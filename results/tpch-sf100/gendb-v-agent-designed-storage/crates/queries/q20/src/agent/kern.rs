//! The worker task (`PartTask`): one list of matching part rows, in batches of up to `bcap` parts.
//! 1. Their part keys; then where their partsupp rows are: exactly `[lo, hi)` by the run layout of suppliers_psrun
//!    (`run_range`, touching the first supplier key), or from a searched start (`ps_lower`) otherwise.
//! 2. Each part (`do_part_run` / `do_part`): its partsupp rows whose supplier has a nation named `$3` (`ps_target`:
//!    an optional supplier filter `tb`, then the supplier row of the key, dense keys without a read), in batches of
//!    up to four; for a batch, the lineitem sums of the four suppliers in one pass (`kacc::li_acc`), the available
//!    quantities read first so their misses overlap; a qualifying row's supplier row is emitted (`Emit`: the list of
//!    flagged rows, or a bit set when the list overflowed and the task runs again).
//! The postcondition: every flagged supplier row is in the result (`Emit::sound`), and every partsupp row whose part
//! key some listed part row has is decided (`jdone`): when it qualifies, its supplier row (if it has a nation named
//! `$3`) is flagged.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::WorkerTask;
use crate::stores::part_nameidx::interface as pi;
use super::typed::p15;
use super::nf::*;
use super::bind_sp::*;
use super::bind_pl::*;
use super::sl::*;
use super::pfind::*;
use super::kctx::*;
use super::kacc::*;
use super::bits::*;
use super::hits::{fast_src, pos_of};
use crate::stores::suppliers::interface::common::read::lemma_div_lt;

verus! {

/// Some matching part row of `[lo, hi)` has key `k`.
pub open spec fn hitk(pp: Seq<PartView>, pat: Seq<u8>, lo: int, hi: int, k: int) -> bool {
    exists|r: int| lo <= r < hi && pi::pkey_at(pp, r) == k && #[trigger] hit_row(pp, pat, r)
}

/// Supplier row `x` is among the rows found so far.
pub open spec fn has(e: Emit, x: int) -> bool {
    if e.fm { bit(e.sf@, x) } else { exists|i: int| 0 <= i < e.cnt && #[trigger] e.out@[i] == x }
}

/// The list of a list-mode emitter overflowed: its rows are incomplete (the task is run again in bit-set mode).
pub open spec fn lost(e: Emit) -> bool {
    !e.fm && e.ovf
}

/// Partsupp row `j` is decided in the rows found `e`.
pub open spec fn jdone(sv: StoresView, ps: Seq<Literal>, d1: int, e: Emit, j: int) -> bool {
    let sp = sv.suppliers;
    lost(e) || (sl_ps_qual(sv, pat_of(ps), d0_of(ps), d1, j) ==>
        forall|x: int| 0 <= x < tn(sp, 13) && #[trigger] suk(sp, x) == pss(sp, j) && sl_nat_ok(sp, nname_of(ps), sunk(sp, x))
            ==> has(e, x))
}

/// Rows found stay found; an overflow stays.
pub open spec fn mono(a: Emit, b: Emit, ns: int) -> bool {
    &&& a.fm == b.fm
    &&& lost(a) ==> lost(b)
    &&& forall|x: int| 0 <= x < ns && #[trigger] has(a, x) ==> has(b, x)
}

pub proof fn lemma_jdone_mono(sv: StoresView, ps: Seq<Literal>, d1: int, a: Emit, b: Emit, j: int)
    requires jdone(sv, ps, d1, a, j), mono(a, b, tn(sv.suppliers, 13)),
    ensures jdone(sv, ps, d1, b, j),
{
    let sp = sv.suppliers;
    if !lost(a) && sl_ps_qual(sv, pat_of(ps), d0_of(ps), d1, j) {
        assert forall|x: int| 0 <= x < tn(sp, 13) && #[trigger] suk(sp, x) == pss(sp, j) && sl_nat_ok(sp, nname_of(ps), sunk(sp, x))
            implies has(b, x) by {
            assert(has(a, x));
        }
    }
}

/// Supplier rows found so far. Bit-set mode (`fm`): a bit set, and the list of its rows unless the list overflowed.
/// List mode: the list of rows found (with repeats), complete unless it overflowed.
pub struct Emit {
    pub fm: bool,
    pub sf: Vec<u64>,
    pub out: Vec<usize>,
    pub cnt: usize,
    pub cap: usize,
    pub ovf: bool,
    /// A value derived from touch loads (kept so the loads are not removed).
    pub junk: u64,
}

impl Emit {
    pub open spec fn wf(&self, ns: int) -> bool {
        &&& self.out@.len() == self.cap
        &&& self.cnt <= self.cap
        &&& forall|i: int| 0 <= i < self.cnt ==> #[trigger] self.out@[i] < ns
        &&& self.fm ==> {
            &&& holds(self.sf@, ns)
            &&& forall|i: int| 0 <= i < self.cnt ==> bit(self.sf@, #[trigger] self.out@[i] as int)
            &&& !self.ovf ==> forall|x: int| 0 <= x < ns && #[trigger] bit(self.sf@, x)
                ==> exists|i: int| 0 <= i < self.cnt && self.out@[i] == x
        }
    }

    pub open spec fn sound(&self, sv: StoresView, ps: Seq<Literal>, d1: int, ns: int) -> bool {
        forall|x: int| 0 <= x < ns && #[trigger] has(*self, x) ==> sl_s_qual(sv, ps, d1, x)
    }

    pub fn emit(&mut self, x: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(d1): Ghost<int>,
        Ghost(ns): Ghost<int>)
        requires old(self).wf(ns), old(self).sound(sv, ps, d1, ns), x < ns, sl_s_qual(sv, ps, d1, x as int),
        ensures
            final(self).wf(ns), final(self).sound(sv, ps, d1, ns),
            lost(*final(self)) || has(*final(self), x as int),
            mono(*old(self), *final(self), ns),
        no_unwind
    {
        let ghost e0 = *self;
        if self.fm {
            if !get_bit(&self.sf, x) {
                let ghost old_sf = self.sf@;
                let ghost old_out = self.out@;
                let ghost old_cnt = self.cnt;
                set_bit(&mut self.sf, x);
                if self.cnt < self.cap {
                    let c = self.cnt;
                    self.out[c] = x;
                    self.cnt = c + 1;
                    proof {
                        assert forall|y: int| 0 <= y < ns && #[trigger] bit(self.sf@, y) && !self.ovf
                            implies exists|i: int| 0 <= i < self.cnt && self.out@[i] == y by {
                            if y == x {
                                assert(self.out@[c as int] == y);
                            } else {
                                assert(bit(old_sf, y));
                                let i = choose|i: int| 0 <= i < old_cnt && old_out[i] == y;
                                assert(self.out@[i] == y);
                            }
                        }
                        assert forall|i: int| 0 <= i < self.cnt implies bit(self.sf@, #[trigger] self.out@[i] as int) by {
                            if i < c {
                                assert(self.out@[i] == old_out[i]);
                                assert(bit(old_sf, old_out[i] as int));
                            }
                        }
                        assert forall|i: int| 0 <= i < self.cnt implies #[trigger] self.out@[i] < ns by {
                            if i < c {
                                assert(self.out@[i] == old_out[i]);
                            }
                        }
                    }
                } else {
                    self.ovf = true;
                    proof {
                        assert forall|i: int| 0 <= i < self.cnt implies bit(self.sf@, #[trigger] self.out@[i] as int) by {
                            assert(bit(old_sf, old_out[i] as int));
                        }
                    }
                }
                proof {
                    assert forall|y: int| 0 <= y < ns && #[trigger] has(e0, y) implies has(*self, y) by {
                        assert(bit(old_sf, y));
                    }
                    assert forall|y: int| 0 <= y < ns && #[trigger] has(*self, y) implies sl_s_qual(sv, ps, d1, y) by {
                        if y != x {
                            assert(bit(old_sf, y));
                            assert(has(e0, y));
                        }
                    }
                }
            }
        } else {
            if self.cnt < self.cap {
                let ghost old_out = self.out@;
                let c = self.cnt;
                self.out[c] = x;
                self.cnt = c + 1;
                proof {
                    assert(self.out@[c as int] == x);
                    assert forall|i: int| 0 <= i < self.cnt implies #[trigger] self.out@[i] < ns by {
                        if i < c {
                            assert(self.out@[i] == old_out[i]);
                        }
                    }
                    assert forall|y: int| 0 <= y < ns && #[trigger] has(e0, y) implies has(*self, y) by {
                        let i = choose|i: int| 0 <= i < e0.cnt && #[trigger] e0.out@[i] == y;
                        assert(self.out@[i] == old_out[i]);
                    }
                    assert forall|y: int| 0 <= y < ns && #[trigger] has(*self, y) implies sl_s_qual(sv, ps, d1, y) by {
                        let i = choose|i: int| 0 <= i < self.cnt && #[trigger] self.out@[i] == y;
                        if i < c {
                            assert(self.out@[i] == old_out[i]);
                            assert(has(e0, y));
                        }
                    }
                }
            } else {
                self.ovf = true;
                proof {
                    assert forall|y: int| 0 <= y < ns && #[trigger] has(e0, y) implies has(*self, y) by {
                        let i = choose|i: int| 0 <= i < e0.cnt && #[trigger] e0.out@[i] == y;
                        assert(self.out@[i] == e0.out@[i]);
                    }
                    assert forall|y: int| 0 <= y < ns && #[trigger] has(*self, y) implies sl_s_qual(sv, ps, d1, y) by {
                        let i = choose|i: int| 0 <= i < self.cnt && #[trigger] self.out@[i] == y;
                        assert(self.out@[i] == e0.out@[i]);
                        assert(has(e0, y));
                    }
                }
            }
        }
    }
}

/// Emitters that differ only in `junk` hold the same rows.
proof fn lemma_junk(a: Emit, b: Emit, ns: int, sv: StoresView, ps: Seq<Literal>, d1: int)
    requires a.fm == b.fm, a.sf@ == b.sf@, a.out@ == b.out@, a.cnt == b.cnt, a.cap == b.cap, a.ovf == b.ovf,
    ensures
        mono(a, b, ns),
        a.wf(ns) ==> b.wf(ns),
        a.sound(sv, ps, d1, ns) ==> b.sound(sv, ps, d1, ns),
{
    assert forall|x: int| 0 <= x < ns && #[trigger] has(b, x) implies has(a, x) by {
        if !a.fm {
            let i = choose|i: int| 0 <= i < b.cnt && #[trigger] b.out@[i] == x;
            assert(a.out@[i] == x);
        }
    }
    assert forall|x: int| 0 <= x < ns && #[trigger] has(a, x) implies has(b, x) by {
        if !a.fm {
            let i = choose|i: int| 0 <= i < a.cnt && #[trigger] a.out@[i] == x;
            assert(b.out@[i] == x);
        }
    }
    if a.wf(ns) && a.fm && !a.ovf {
        assert forall|x: int| 0 <= x < ns && #[trigger] bit(b.sf@, x) implies exists|i: int| 0 <= i < b.cnt && b.out@[i] == x by {
            let i = choose|i: int| 0 <= i < a.cnt && a.out@[i] == x;
            assert(b.out@[i] == x);
        }
    }
}

/// Partsupp keys never decrease (sorted partsupp).
pub proof fn lemma_ps_sorted(sp: Seq<PartView>, a: int, b: int)
    requires sp_ok(sp), ps_kind(sp) == 1, 0 <= a <= b < tn(sp, 0),
    ensures psk(sp, a) <= psk(sp, b),
    decreases b - a,
{
    if a < b {
        lemma_ps_sorted(sp, a, b - 1);
        assert(ps_le(sp, b - 1));
    }
}

/// The ghost parameters of a context.
pub open spec fn cg(ctx: &Ctx, sv: StoresView, ps: Seq<Literal>, d1: int) -> bool {
    ctx.sv@ == sv && ctx.ps@ == ps && ctx.d1g@ == d1
}

/// Supplier row `x` (key `s`) has a nation named `$3`.
pub open spec fn target(ctx: &Ctx, s: int, x: int) -> bool {
    &&& 0 <= x < ctx.ns
    &&& suk(ctx.sp(), x) == s
    &&& sl_nat_ok(ctx.sp(), ctx.nname(), sunk(ctx.sp(), x))
}

/// A partsupp row whose supplier has no row with a nation named `$3` is decided whatever its sums.
proof fn lemma_no_target(ctx: &Ctx, j: int, sf: Emit, x: Option<usize>)
    requires
        ctx.wf(), 0 <= j < ctx.nps,
        x matches Some(x0) ==> x0 < ctx.ns && suk(ctx.sp(), x0 as int) == pss(ctx.sp(), j)
            && !sl_nat_ok(ctx.sp(), ctx.nname(), sunk(ctx.sp(), x0 as int)),
        x is None ==> forall|y: int| 0 <= y < ctx.ns ==> #[trigger] suk(ctx.sp(), y) != pss(ctx.sp(), j),
    ensures jdone(ctx.sv@, ctx.ps@, ctx.d1g@, sf, j),
{
    let sp = ctx.sp();
    let ps = ctx.ps@;
    assert forall|y: int| 0 <= y < tn(sp, 13) && #[trigger] suk(sp, y) == pss(sp, j)
        && sl_nat_ok(sp, nname_of(ps), sunk(sp, y)) implies has(sf, y) by {
        if let Some(x0) = x {
            if y != x0 {
                assert(suk(sp, y) != suk(sp, x0 as int));
            }
        }
    }
}

/// The supplier filter `tb` (bit `y`: key `sbase + y`, for `y < nb`): every supplier row with a nation named `$3`
/// and a key in that range has its bit set (a clear bit rules the key out without a supplier lookup).
pub open spec fn tb_ok(ctx: &Ctx, tb: Seq<u64>, nb: int) -> bool {
    &&& nb <= tb.len() * 64
    &&& forall|x: int| 0 <= x < ctx.ns && ctx.sbase <= #[trigger] suk(ctx.sp(), x) < ctx.sbase + nb
        && sl_nat_ok(ctx.sp(), ctx.nname(), sunk(ctx.sp(), x)) ==> bit(tb, suk(ctx.sp(), x) - ctx.sbase)
}

/// A partsupp row whose supplier key has a clear filter bit is decided whatever its sums.
proof fn lemma_tb_skip(ctx: &Ctx, tb: Seq<u64>, nb: int, j: int, sf: Emit)
    requires
        ctx.wf(), 0 <= j < ctx.nps, tb_ok(ctx, tb, nb),
        ctx.sbase <= pss(ctx.sp(), j) < ctx.sbase + nb,
        !bit(tb, pss(ctx.sp(), j) - ctx.sbase),
    ensures jdone(ctx.sv@, ctx.ps@, ctx.d1g@, sf, j),
{
    let sp = ctx.sp();
    let ps = ctx.ps@;
    assert forall|y: int| 0 <= y < tn(sp, 13) && #[trigger] suk(sp, y) == pss(sp, j)
        && sl_nat_ok(sp, nname_of(ps), sunk(sp, y)) implies has(sf, y) by {
        assert(bit(tb, suk(sp, y) - ctx.sbase));
    }
}

/// Fill the supplier filter (`tb` all clear on entry; bits for keys `sbase .. sbase + nb`).
fn build_tb(ctx: &Ctx, tb: &mut Vec<u64>, nb: usize)
    requires
        ctx.wf(), nb as int <= old(tb)@.len() * 64,
        forall|y: int| 0 <= y < old(tb)@.len() * 64 ==> !#[trigger] bit(old(tb)@, y),
    ensures
        final(tb)@.len() == old(tb)@.len(),
        tb_ok(ctx, final(tb)@, nb as int),
    no_unwind
{
    let ghost sp = ctx.sp();
    let ns = ctx.ns;
    let base = ctx.sbase;
    let ghost tl = tb@.len();
    let mut x: usize = 0;
    if nb == 0 {
        return;
    }
    if ctx.dense && ns <= nb {
        // row x has key sbase + x: its bit is x (no key read)
        while x < ns
            invariant
                ctx.wf(), ctx.dense, ns == ctx.ns, base == ctx.sbase, sp == ctx.sp(),
                tb@.len() == tl, nb as int <= tl * 64, ns <= nb,
                x <= ns,
                forall|z: int| 0 <= z < x && ctx.sbase <= #[trigger] suk(ctx.sp(), z) < ctx.sbase + nb
                    && sl_nat_ok(ctx.sp(), ctx.nname(), sunk(ctx.sp(), z)) ==> bit(tb@, suk(ctx.sp(), z) - ctx.sbase),
            decreases ns - x,
        {
            let nk = ctx.get_sunk(x);
            if ctx.nat_has(nk) {
                proof {
                    lemma_div_lt(x as int, 64, tl as int);
                }
                let ghost t0 = tb@;
                set_bit(tb, x);
                proof {
                    assert forall|z: int| 0 <= z < x + 1 && ctx.sbase <= #[trigger] suk(ctx.sp(), z) < ctx.sbase + nb
                        && sl_nat_ok(ctx.sp(), ctx.nname(), sunk(ctx.sp(), z)) implies bit(tb@, suk(ctx.sp(), z) - ctx.sbase) by {
                        if z < x {
                            assert(bit(t0, suk(sp, z) - ctx.sbase));
                        }
                    }
                }
            }
            x = x + 1;
        }
        return;
    }
    while x < ns
        invariant
            ctx.wf(), ns == ctx.ns, base == ctx.sbase, sp == ctx.sp(),
            tb@.len() == tl, nb as int <= tl * 64,
            x <= ns,
            forall|z: int| 0 <= z < x && ctx.sbase <= #[trigger] suk(ctx.sp(), z) < ctx.sbase + nb
                && sl_nat_ok(ctx.sp(), ctx.nname(), sunk(ctx.sp(), z)) ==> bit(tb@, suk(ctx.sp(), z) - ctx.sbase),
        decreases ns - x,
    {
        let k = ctx.get_suk(x);
        let d = k as i128 - base as i128;
        if d >= 0 && d < nb as i128 {
            let nk = ctx.get_sunk(x);
            if ctx.nat_has(nk) {
                let y = d as usize;
                proof {
                    lemma_div_lt(y as int, 64, tl as int);
                }
                let ghost t0 = tb@;
                set_bit(tb, y);
                proof {
                    assert forall|z: int| 0 <= z < x + 1 && ctx.sbase <= #[trigger] suk(ctx.sp(), z) < ctx.sbase + nb
                        && sl_nat_ok(ctx.sp(), ctx.nname(), sunk(ctx.sp(), z)) implies bit(tb@, suk(ctx.sp(), z) - ctx.sbase) by {
                        if z < x {
                            assert(bit(t0, suk(sp, z) - ctx.sbase));
                        }
                    }
                }
            }
        }
        x = x + 1;
    }
}

/// Decide partsupp row `j` (key `k`, supplier `s` whose row `x` has a nation named `$3`) from its lineitem sums
/// `a` and `c`.
fn decide(ctx: &Ctx, j: usize, s: i64, x: usize, a: i128, c: u64, av: i64, em: &mut Emit, Ghost(k): Ghost<int>)
    requires
        ctx.wf(), j < ctx.nps, av == psa(ctx.sp(), j as int),
        psk(ctx.sp(), j as int) == k, pss(ctx.sp(), j as int) == s,
        target(ctx, s as int, x as int),
        sl_part_hit(ctx.pp(), ctx.pat(), k),
        a == sl_lsum(ctx.lp(), k, s as int, ctx.d0 as int, ctx.d1 as int),
        c == sl_lcnt(ctx.lp(), k, s as int, ctx.d0 as int, ctx.d1 as int),
        old(em).wf(ctx.ns as int), old(em).sound(ctx.sv@, ctx.ps@, ctx.d1g@, ctx.ns as int),
    ensures
        final(em).wf(ctx.ns as int), final(em).sound(ctx.sv@, ctx.ps@, ctx.d1g@, ctx.ns as int),
        mono(*old(em), *final(em), ctx.ns as int),
        jdone(ctx.sv@, ctx.ps@, ctx.d1g@, *final(em), j as int),
    no_unwind
{
    let ghost sv = ctx.sv@;
    let ghost sp = ctx.sp();
    let ghost ps = ctx.ps@;
    let ghost d1 = ctx.d1g@;
    if c > 0 {
        if 200 * (av as i128) > a {
            proof {
                assert(sl_ps_qual(sv, pat_of(ps), d0_of(ps), d1, j as int));
                assert(sl_sk_ok(sv, pat_of(ps), d0_of(ps), d1, suk(sp, x as int)));
            }
            em.emit(x, Ghost(sv), Ghost(ps), Ghost(d1), Ghost(ctx.ns as int));
            proof {
                if !lost(*em) {
                    assert forall|y: int| 0 <= y < tn(sp, 13) && #[trigger] suk(sp, y) == pss(sp, j as int)
                        && sl_nat_ok(sp, nname_of(ps), sunk(sp, y)) implies has(*em, y) by {
                        if y != x {
                            assert(suk(sp, y) != suk(sp, x as int));
                        }
                    }
                }
            }
        }
    }
}

/// Decide the partsupp rows `j0 .. j(m-1)` (all of key `k`; their suppliers' rows `x0 ..` have a nation named `$3`).
fn do_batch(ctx: &Ctx, k: i64, m: usize, j0: usize, j1: usize, j2: usize, j3: usize, x0: usize, x1: usize, x2: usize,
    x3: usize, em: &mut Emit) -> (junk: u64)
    requires
        ctx.wf(),
        1 <= m <= 4,
        j0 < ctx.nps && j1 < ctx.nps && j2 < ctx.nps && j3 < ctx.nps,
        psk(ctx.sp(), j0 as int) == k && target(ctx, pss(ctx.sp(), j0 as int), x0 as int),
        m > 1 ==> psk(ctx.sp(), j1 as int) == k && target(ctx, pss(ctx.sp(), j1 as int), x1 as int),
        m > 2 ==> psk(ctx.sp(), j2 as int) == k && target(ctx, pss(ctx.sp(), j2 as int), x2 as int),
        m > 3 ==> psk(ctx.sp(), j3 as int) == k && target(ctx, pss(ctx.sp(), j3 as int), x3 as int),
        sl_part_hit(ctx.pp(), ctx.pat(), k as int),
        old(em).wf(ctx.ns as int), old(em).sound(ctx.sv@, ctx.ps@, ctx.d1g@, ctx.ns as int),
    ensures
        final(em).wf(ctx.ns as int), final(em).sound(ctx.sv@, ctx.ps@, ctx.d1g@, ctx.ns as int),
        mono(*old(em), *final(em), ctx.ns as int),
        jdone(ctx.sv@, ctx.ps@, ctx.d1g@, *final(em), j0 as int),
        m > 1 ==> jdone(ctx.sv@, ctx.ps@, ctx.d1g@, *final(em), j1 as int),
        m > 2 ==> jdone(ctx.sv@, ctx.ps@, ctx.d1g@, *final(em), j2 as int),
        m > 3 ==> jdone(ctx.sv@, ctx.ps@, ctx.d1g@, *final(em), j3 as int),
    no_unwind
{
    let ghost (sv, ps, d1, ns) = (ctx.sv@, ctx.ps@, ctx.d1g@, ctx.ns as int);
    // the available quantities first: their misses overlap the lineitem reads
    let av0 = ctx.get_psa(j0);
    let av1 = if m > 1 { ctx.get_psa(j1) } else { av0 };
    let av2 = if m > 2 { ctx.get_psa(j2) } else { av0 };
    let av3 = if m > 3 { ctx.get_psa(j3) } else { av0 };
    let s0 = ctx.get_pss(j0);
    let s1 = if m > 1 { ctx.get_pss(j1) } else { s0 };
    let s2 = if m > 2 { ctx.get_pss(j2) } else { s0 };
    let s3 = if m > 3 { ctx.get_pss(j3) } else { s0 };
    let acc = li_acc(ctx, k, s0, s1, s2, s3);
    decide(ctx, j0, s0, x0, acc.a0, acc.c0, av0, em, Ghost(k as int));
    let ghost sf1 = *em;
    if m > 1 {
        decide(ctx, j1, s1, x1, acc.a1, acc.c1, av1, em, Ghost(k as int));
        proof {
            lemma_jdone_mono(sv, ps, d1, sf1, *em, j0 as int);
        }
    }
    let ghost sf2 = *em;
    if m > 2 {
        decide(ctx, j2, s2, x2, acc.a2, acc.c2, av2, em, Ghost(k as int));
        proof {
            lemma_jdone_mono(sv, ps, d1, sf2, *em, j0 as int);
            lemma_jdone_mono(sv, ps, d1, sf2, *em, j1 as int);
        }
    }
    let ghost sf3 = *em;
    if m > 3 {
        decide(ctx, j3, s3, x3, acc.a3, acc.c3, av3, em, Ghost(k as int));
        proof {
            lemma_jdone_mono(sv, ps, d1, sf3, *em, j0 as int);
            lemma_jdone_mono(sv, ps, d1, sf3, *em, j1 as int);
            lemma_jdone_mono(sv, ps, d1, sf3, *em, j2 as int);
        }
    }
    acc.junk
}

/// Sorted partsupp: the first row at or after `cur` whose key is not below `k` (rows before `cur` are below `k`).
fn ps_lower(ctx: &Ctx, cur: usize, k: i64) -> (r: usize)
    requires
        ctx.wf_ps(), ctx.sorted, cur <= ctx.nps,
        forall|j: int| 0 <= j < cur ==> #[trigger] psk(ctx.sp(), j) < k,
    ensures
        r <= ctx.nps,
        forall|j: int| 0 <= j < r ==> #[trigger] psk(ctx.sp(), j) < k,
        r < ctx.nps ==> psk(ctx.sp(), r as int) >= k,
    no_unwind
{
    let ghost sp = ctx.sp();
    let n = ctx.nps;
    let g = ctx.guess(k);
    if g > 0 && g < n {
        if ctx.get_psk(g - 1) < k && ctx.get_psk(g) >= k {
            proof {
                assert forall|j: int| 0 <= j < g implies #[trigger] psk(sp, j) < k by {
                    lemma_ps_sorted(sp, j, g - 1);
                }
            }
            return g;
        }
    }
    if cur >= n {
        return n;
    }
    if ctx.get_psk(cur) >= k {
        return cur;
    }
    proof {
        assert forall|j: int| 0 <= j <= cur implies #[trigger] psk(sp, j) < k by {
            lemma_ps_sorted(sp, j, cur as int);
        }
    }
    // gallop: lo has a key below k, hi is n or has a key not below k
    let mut lo = cur;
    let mut step: usize = 1;
    let mut hi: usize = n;
    let mut done = false;
    while !done
        invariant
            ctx.wf_ps(), ctx.sorted, n == ctx.nps, sp == ctx.sp(),
            lo < n, lo < hi <= n, step >= 1,
            forall|j: int| 0 <= j <= lo ==> #[trigger] psk(sp, j) < k,
            done ==> (hi == n || psk(sp, hi as int) >= k),
            !done ==> hi == n,
        decreases n - lo, (if done { 0int } else { 1int }),
    {
        let h = if n - lo > step { lo + step } else { n };
        if h == n {
            hi = n;
            done = true;
        } else if ctx.get_psk(h) >= k {
            hi = h;
            done = true;
        } else {
            proof {
                assert forall|j: int| 0 <= j <= h implies #[trigger] psk(sp, j) < k by {
                    lemma_ps_sorted(sp, j, h as int);
                }
            }
            lo = h;
            if step < 0x4000_0000 {
                step = step * 2;
            }
        }
    }
    while lo + 1 < hi
        invariant
            ctx.wf_ps(), ctx.sorted, n == ctx.nps, sp == ctx.sp(),
            lo < hi <= n,
            forall|j: int| 0 <= j <= lo ==> #[trigger] psk(sp, j) < k,
            hi == n || psk(sp, hi as int) >= k,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        if ctx.get_psk(mid) < k {
            proof {
                assert forall|j: int| 0 <= j <= mid implies #[trigger] psk(sp, j) < k by {
                    lemma_ps_sorted(sp, j, mid as int);
                }
            }
            lo = mid;
        } else {
            hi = mid;
        }
    }
    hi
}

/// Decide every partsupp row of key `k`: rows from `start` (sorted partsupp: the first row whose key is not below
/// `k`; otherwise 0).
fn do_part(ctx: &Ctx, k: i64, start: usize, tb: &Vec<u64>, nb: usize, em: &mut Emit)
    requires
        ctx.wf(), tb_ok(ctx, tb@, nb as int),
        sl_part_hit(ctx.pp(), ctx.pat(), k as int),
        start <= ctx.nps,
        forall|j: int| 0 <= j < start ==> #[trigger] psk(ctx.sp(), j) < k,
        ctx.sorted ==> (start < ctx.nps ==> psk(ctx.sp(), start as int) >= k),
        old(em).wf(ctx.ns as int), old(em).sound(ctx.sv@, ctx.ps@, ctx.d1g@, ctx.ns as int),
    ensures
        final(em).wf(ctx.ns as int), final(em).sound(ctx.sv@, ctx.ps@, ctx.d1g@, ctx.ns as int),
        mono(*old(em), *final(em), ctx.ns as int),
        forall|j: int| 0 <= j < ctx.nps && #[trigger] psk(ctx.sp(), j) == k ==> jdone(ctx.sv@, ctx.ps@, ctx.d1g@, *final(em), j),
    no_unwind
{
    let ghost (sv, ps, d1, ns) = (ctx.sv@, ctx.ps@, ctx.d1g@, ctx.ns as int);
    let ghost sp = ctx.sp();
    let ghost sf0 = *em;
    let n = ctx.nps;
    let mut j = start;
    while j < n
        invariant
            ctx.wf(), n == ctx.nps, sp == ctx.sp(), sv == ctx.sv@, ps == ctx.ps@, d1 == ctx.d1g@, ns == ctx.ns,
            tb_ok(ctx, tb@, nb as int),
            sl_part_hit(ctx.pp(), ctx.pat(), k as int),
            start <= j <= n,
            ctx.sorted ==> (start < n ==> psk(sp, start as int) >= k),
            forall|t: int| 0 <= t < start ==> #[trigger] psk(sp, t) < k,
            em.wf(ns), em.sound(sv, ps, d1, ns),
            mono(sf0, *em, ns),
            forall|t: int| start <= t < j && #[trigger] psk(sp, t) == k ==> jdone(sv, ps, d1, *em, t),
        decreases n - j,
    {
        let j_in = j;
        let mut m: usize = 0;
        let mut j0: usize = 0;
        let mut j1: usize = 0;
        let mut j2: usize = 0;
        let mut j3: usize = 0;
        let mut x0: usize = 0;
        let mut x1: usize = 0;
        let mut x2: usize = 0;
        let mut x3: usize = 0;
        while m < 4 && j < n
            invariant
                ctx.wf(), n == ctx.nps, sp == ctx.sp(), sv == ctx.sv@, ps == ctx.ps@, d1 == ctx.d1g@, ns == ctx.ns,
                tb_ok(ctx, tb@, nb as int),
                start <= j_in <= j <= n, m <= 4,
                ctx.sorted ==> (start < n ==> psk(sp, start as int) >= k),
                j0 < n && j1 < n && j2 < n && j3 < n,
                m > 0 ==> psk(sp, j0 as int) == k && j_in <= j0 < j && target(ctx, pss(sp, j0 as int), x0 as int),
                m > 1 ==> psk(sp, j1 as int) == k && j_in <= j1 < j && target(ctx, pss(sp, j1 as int), x1 as int),
                m > 2 ==> psk(sp, j2 as int) == k && j_in <= j2 < j && target(ctx, pss(sp, j2 as int), x2 as int),
                m > 3 ==> psk(sp, j3 as int) == k && j_in <= j3 < j && target(ctx, pss(sp, j3 as int), x3 as int),
                forall|t: int| j_in <= t < j && #[trigger] psk(sp, t) == k
                    ==> (m > 0 && t == j0) || (m > 1 && t == j1) || (m > 2 && t == j2) || (m > 3 && t == j3)
                        || jdone(sv, ps, d1, *em, t),
            decreases n - j,
        {
            let kj = ctx.get_psk(j);
            if kj == k {
                let s = ctx.get_pss(j);
                let d = s as i128 - ctx.sbase as i128;
                let skip = if d >= 0 && d < nb as i128 {
                    proof {
                        lemma_div_lt(d as int, 64, tb@.len() as int);
                    }
                    !get_bit(tb, d as usize)
                } else {
                    false
                };
                let fx = if skip { None } else { ctx.find_su(s) };
                let mut tgt = false;
                let mut xx: usize = 0;
                if skip {
                    proof {
                        lemma_tb_skip(ctx, tb@, nb as int, j as int, *em);
                    }
                } else if let Some(x) = fx {
                    let nk = ctx.get_sunk(x);
                    if ctx.nat_has(nk) {
                        tgt = true;
                        xx = x;
                    } else {
                        proof {
                            lemma_no_target(ctx, j as int, *em, fx);
                        }
                    }
                } else {
                    proof {
                        lemma_no_target(ctx, j as int, *em, fx);
                    }
                }
                if tgt {
                    if m == 0 { j0 = j; x0 = xx; } else if m == 1 { j1 = j; x1 = xx; } else if m == 2 { j2 = j; x2 = xx; } else { j3 = j; x3 = xx; }
                    m = m + 1;
                }
                j = j + 1;
            } else if ctx.sorted {
                proof {
                    assert forall|t: int| j <= t < n implies #[trigger] psk(sp, t) != k by {
                        lemma_ps_sorted(sp, start as int, j as int);
                        lemma_ps_sorted(sp, j as int, t);
                    }
                }
                j = n;
            } else {
                j = j + 1;
            }
        }
        let ghost sfb = *em;
        if m > 0 {
            do_batch(ctx, k, m, j0, j1, j2, j3, x0, x1, x2, x3, em);
            proof {
                assert forall|t: int| start <= t < j && #[trigger] psk(sp, t) == k implies jdone(sv, ps, d1, *em, t) by {
                    if t < j_in || !((m > 0 && t == j0) || (m > 1 && t == j1) || (m > 2 && t == j2) || (m > 3 && t == j3)) {
                        lemma_jdone_mono(sv, ps, d1, sfb, *em, t);
                    }
                }
            }
        }
    }
}

/// Supplier row of partsupp row `j`'s supplier when it may have a nation named `$3` (`None`: the row is decided
/// whatever its sums). The filter `tb` rules out most suppliers without a supplier lookup.
fn ps_target(ctx: &Ctx, j: usize, tb: &Vec<u64>, nb: usize, Ghost(em): Ghost<Emit>) -> (r: Option<usize>)
    requires ctx.wf(), j < ctx.nps, tb_ok(ctx, tb@, nb as int),
    ensures
        r matches Some(x) ==> target(ctx, pss(ctx.sp(), j as int), x as int),
        r is None ==> jdone(ctx.sv@, ctx.ps@, ctx.d1g@, em, j as int),
    no_unwind
{
    let s = ctx.get_pss(j);
    let d = s as i128 - ctx.sbase as i128;
    if d >= 0 && d < nb as i128 {
        proof {
            lemma_div_lt(d as int, 64, tb@.len() as int);
        }
        if !get_bit(tb, d as usize) {
            proof {
                lemma_tb_skip(ctx, tb@, nb as int, j as int, em);
            }
            return None;
        }
    }
    let fx = ctx.find_su(s);
    if let Some(x) = fx {
        let nk = ctx.get_sunk(x);
        if ctx.nat_has(nk) {
            return Some(x);
        }
    }
    proof {
        lemma_no_target(ctx, j as int, em, fx);
    }
    None
}

/// Decide every partsupp row of key `k`: the rows `[lo, hi)` (run layout: exactly the rows of `k`).
fn do_part_run(ctx: &Ctx, k: i64, lo: usize, hi: usize, tb: &Vec<u64>, nb: usize, em: &mut Emit) -> (junk: u64)
    requires
        ctx.wf(), tb_ok(ctx, tb@, nb as int),
        sl_part_hit(ctx.pp(), ctx.pat(), k as int),
        run_rows(ctx, k as int, lo as int, hi as int),
        old(em).wf(ctx.ns as int), old(em).sound(ctx.sv@, ctx.ps@, ctx.d1g@, ctx.ns as int),
    ensures
        final(em).wf(ctx.ns as int), final(em).sound(ctx.sv@, ctx.ps@, ctx.d1g@, ctx.ns as int),
        mono(*old(em), *final(em), ctx.ns as int),
        forall|j: int| 0 <= j < ctx.nps && #[trigger] psk(ctx.sp(), j) == k ==> jdone(ctx.sv@, ctx.ps@, ctx.d1g@, *final(em), j),
    no_unwind
{
    let ghost (sv, ps, d1, ns) = (ctx.sv@, ctx.ps@, ctx.d1g@, ctx.ns as int);
    let ghost sp = ctx.sp();
    let ghost sf0 = *em;
    let mut junk: u64 = 0;
    let mut j = lo;
    while j < hi
        invariant
            ctx.wf(), sp == ctx.sp(), sv == ctx.sv@, ps == ctx.ps@, d1 == ctx.d1g@, ns == ctx.ns,
            tb_ok(ctx, tb@, nb as int),
            sl_part_hit(ctx.pp(), ctx.pat(), k as int),
            run_rows(ctx, k as int, lo as int, hi as int),
            lo <= j <= hi,
            em.wf(ns), em.sound(sv, ps, d1, ns),
            mono(sf0, *em, ns),
            forall|t: int| lo <= t < j ==> jdone(sv, ps, d1, *em, t),
        decreases hi - j,
    {
        let j_in = j;
        let mut m: usize = 0;
        let mut j0: usize = 0;
        let mut j1: usize = 0;
        let mut j2: usize = 0;
        let mut j3: usize = 0;
        let mut x0: usize = 0;
        let mut x1: usize = 0;
        let mut x2: usize = 0;
        let mut x3: usize = 0;
        while m < 4 && j < hi
            invariant
                ctx.wf(), sp == ctx.sp(), sv == ctx.sv@, ps == ctx.ps@, d1 == ctx.d1g@, ns == ctx.ns,
                tb_ok(ctx, tb@, nb as int),
                run_rows(ctx, k as int, lo as int, hi as int),
                lo <= j_in <= j <= hi, m <= 4,
                j0 < hi && j1 < hi && j2 < hi && j3 < hi,
                m > 0 ==> j_in <= j0 < j && target(ctx, pss(sp, j0 as int), x0 as int),
                m > 1 ==> j_in <= j1 < j && target(ctx, pss(sp, j1 as int), x1 as int),
                m > 2 ==> j_in <= j2 < j && target(ctx, pss(sp, j2 as int), x2 as int),
                m > 3 ==> j_in <= j3 < j && target(ctx, pss(sp, j3 as int), x3 as int),
                forall|t: int| j_in <= t < j
                    ==> (m > 0 && t == j0) || (m > 1 && t == j1) || (m > 2 && t == j2) || (m > 3 && t == j3)
                        || jdone(sv, ps, d1, *em, t),
            decreases hi - j,
        {
            let fx = ps_target(ctx, j, tb, nb, Ghost(*em));
            if let Some(xx) = fx {
                if m == 0 { j0 = j; x0 = xx; } else if m == 1 { j1 = j; x1 = xx; } else if m == 2 { j2 = j; x2 = xx; } else { j3 = j; x3 = xx; }
                m = m + 1;
            }
            j = j + 1;
        }
        let ghost sfb = *em;
        if m > 0 {
            proof {
                assert(psk(sp, j0 as int) == k);
                assert(m > 1 ==> psk(sp, j1 as int) == k);
                assert(m > 2 ==> psk(sp, j2 as int) == k);
                assert(m > 3 ==> psk(sp, j3 as int) == k);
            }
            let jk = do_batch(ctx, k, m, j0, j1, j2, j3, x0, x1, x2, x3, em);
            junk = junk ^ jk;
            proof {
                assert forall|t: int| lo <= t < j implies jdone(sv, ps, d1, *em, t) by {
                    if t < j_in || !((m > 0 && t == j0) || (m > 1 && t == j1) || (m > 2 && t == j2) || (m > 3 && t == j3)) {
                        lemma_jdone_mono(sv, ps, d1, sfb, *em, t);
                    }
                }
            }
        }
    }
    proof {
        assert forall|j: int| 0 <= j < ctx.nps && #[trigger] psk(ctx.sp(), j) == k implies jdone(sv, ps, d1, *em, j) by {
            assert(lo <= j < hi);
        }
    }
    junk
}

/// Some row of the list `l` has part key `k`.
pub open spec fn hitl(pp: Seq<PartView>, l: Seq<usize>, k: int) -> bool {
    exists|i: int| 0 <= i < l.len() && #[trigger] pi::pkey_at(pp, l[i] as int) == k
}

/// `st` is where the partsupp rows of key `k` start (none before it; in sorted partsupp, none below `k` from it).
pub open spec fn start_ok(ctx: &Ctx, k: int, st: int) -> bool {
    &&& 0 <= st <= ctx.nps
    &&& forall|j: int| 0 <= j < st ==> #[trigger] psk(ctx.sp(), j) < k
    &&& ctx.sorted ==> (st < ctx.nps ==> psk(ctx.sp(), st) >= k)
}

/// Where the partsupp rows of key `k` are: exactly `[lo, hi)` (run layout) or from `lo` on (`start_ok`).
pub open spec fn rows_at(ctx: &Ctx, k: int, lo: int, hi: int) -> bool {
    if ctx.runok && ctx.ratio <= 0x1_0000 { run_rows(ctx, k, lo, hi) } else { start_ok(ctx, k, lo) }
}

/// A task's list of part rows: entries `[q0, q0 + n)` of the two name-order ranges (fast mode, read in place), or
/// its own list `rl`.
pub open spec fn vlist(fast: bool, perm: Seq<u32>, rl: Seq<usize>, a1: int, b1: int, a2: int, b2: int, q0: int, n: int)
    -> Seq<usize> {
    if fast { fast_src(perm, a1, b1, a2, b2).subrange(q0, q0 + n) } else { rl }
}

pub open spec fn vok(fast: bool, perm: Seq<u32>, rl: Seq<usize>, a1: int, b1: int, a2: int, b2: int, q0: int, n: int)
    -> bool {
    &&& fast ==> 0 <= a1 <= b1 <= perm.len() && 0 <= a2 <= b2 <= perm.len() && 0 <= q0 && q0 + n <= (b1 - a1) + (b2 - a2)
        && (b1 - a1) + (b2 - a2) <= usize::MAX
    &&& !fast ==> rl.len() == n
}

/// Entry `i` of the list (`no_unwind`).
fn vrow(fast: bool, perm: &[u32], rl: &Vec<usize>, a1: usize, b1: usize, a2: usize, b2: usize, q0: usize, n: usize,
    i: usize) -> (r: usize)
    requires
        vok(fast, perm@, rl@, a1 as int, b1 as int, a2 as int, b2 as int, q0 as int, n as int),
        i < n,
    ensures
        vlist(fast, perm@, rl@, a1 as int, b1 as int, a2 as int, b2 as int, q0 as int, n as int).len() == n,
        r == vlist(fast, perm@, rl@, a1 as int, b1 as int, a2 as int, b2 as int, q0 as int, n as int)[i as int],
    no_unwind
{
    if fast {
        let p = q0 + i;
        let l1 = b1 - a1;
        proof {
            assert(fast_src(perm@, a1 as int, b1 as int, a2 as int, b2 as int)[p as int]
                == perm@[pos_of(a1 as int, b1 as int, a2 as int, p as int)] as usize);
        }
        if p < l1 {
            perm[a1 + p] as usize
        } else {
            perm[a2 + (p - l1)] as usize
        }
    } else {
        rl[i]
    }
}

/// The worker task over a list of matching part rows, processed in batches of up to `bcap` rows: first their part
/// keys, then where their partsupp rows start (touching their supplier keys and index entries), then each part.
pub struct PartTask {
    pub ctx: Ctx,
    pub rl: Vec<usize>,
    pub fast: bool,
    pub perm: &'static [u32],
    pub a1: usize,
    pub b1: usize,
    pub a2: usize,
    pub b2: usize,
    pub q0: usize,
    pub n: usize,
    pub em: Emit,
    pub ks: Vec<i64>,
    pub sts: Vec<usize>,
    pub tch: Vec<u64>,
    pub bcap: usize,
    /// The supplier filter (all clear until `run` fills it) over keys `sbase .. sbase + nb`.
    pub tb: Vec<u64>,
    pub nb: usize,
    /// Per batch part: its lineitem index entry, then its date window (touch stages only).
    pub w0: Vec<usize>,
    pub w1: Vec<usize>,
}

impl PartTask {
    /// The task's part rows.
    pub open spec fn lst(&self) -> Seq<usize> {
        vlist(self.fast, self.perm@, self.rl@, self.a1 as int, self.b1 as int, self.a2 as int, self.b2 as int,
            self.q0 as int, self.n as int)
    }
}

impl WorkerTask for PartTask {
    type Output = Emit;

    open spec fn pre(&self) -> bool {
        let pp = self.ctx.pp();
        &&& self.ctx.wf()
        &&& vok(self.fast, self.perm@, self.rl@, self.a1 as int, self.b1 as int, self.a2 as int, self.b2 as int,
            self.q0 as int, self.n as int)
        &&& forall|i: int| 0 <= i < self.n ==> (#[trigger] self.lst()[i]) < self.ctx.np
            && hit_row(pp, self.ctx.pat(), self.lst()[i] as int)
        &&& self.em.wf(self.ctx.ns as int)
        &&& self.em.sound(self.ctx.sv@, self.ctx.ps@, self.ctx.d1g@, self.ctx.ns as int)
        &&& self.bcap >= 1
        &&& self.ks@.len() == self.bcap && self.sts@.len() == self.bcap && self.tch@.len() == self.bcap
        &&& self.w0@.len() == self.bcap && self.w1@.len() == self.bcap
        &&& self.nb as int <= self.tb@.len() * 64
        &&& forall|y: int| 0 <= y < self.tb@.len() * 64 ==> !#[trigger] bit(self.tb@, y)
    }

    open spec fn post(&self, out: Emit) -> bool {
        let sp = self.ctx.sp();
        &&& out.wf(self.ctx.ns as int)
        &&& out.sound(self.ctx.sv@, self.ctx.ps@, self.ctx.d1g@, self.ctx.ns as int)
        &&& out.fm == self.em.fm
        &&& forall|j: int| 0 <= j < self.ctx.nps && #[trigger] hitl(self.ctx.pp(), self.lst(), psk(sp, j))
            ==> jdone(self.ctx.sv@, self.ctx.ps@, self.ctx.d1g@, out, j)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (0, self.n as u64)
    }

    fn run(self) -> (out: Emit) {
        let ghost rl = self.lst();
        let PartTask { ctx, rl: rv, fast, perm, a1, b1, a2, b2, q0, n, em, ks, sts, tch, bcap, tb, nb, w0, w1 } = self;
        let mut tb = tb;
        build_tb(&ctx, &mut tb, nb);
        let run_mode = ctx.runok && ctx.ratio <= 0x1_0000;
        let mut junk: u64 = 0;
        let mut w0 = w0;
        let mut w1 = w1;
        let mut em = em;
        let ghost fm0 = em.fm;
        let mut ks = ks;
        let mut sts = sts;
        let mut tch = tch;
        let ghost pp = ctx.pp();
        let ghost pat = ctx.pat();
        let ghost (sv, ps, d1, ns) = (ctx.sv@, ctx.ps@, ctx.d1g@, ctx.ns as int);
        let ghost sp = ctx.sp();
        let mut i: usize = 0;
        while i < n
            invariant
                ctx.wf(), i <= n, rl.len() == n,
                vok(fast, perm@, rv@, a1 as int, b1 as int, a2 as int, b2 as int, q0 as int, n as int),
                rl == vlist(fast, perm@, rv@, a1 as int, b1 as int, a2 as int, b2 as int, q0 as int, n as int),
                pp == ctx.pp(), pat == ctx.pat(), sp == ctx.sp(),
                sv == ctx.sv@, ps == ctx.ps@, d1 == ctx.d1g@, ns == ctx.ns,
                forall|t: int| 0 <= t < n ==> (#[trigger] rl[t]) < ctx.np && hit_row(pp, pat, rl[t] as int),
                em.wf(ns), em.sound(sv, ps, d1, ns), em.fm == fm0,
                bcap >= 1, ks@.len() == bcap, sts@.len() == bcap, tch@.len() == bcap,
                w0@.len() == bcap, w1@.len() == bcap, tb_ok(&ctx, tb@, nb as int),
                run_mode == (ctx.runok && ctx.ratio <= 0x1_0000),
                forall|j: int| 0 <= j < ctx.nps && #[trigger] hitl(pp, rl.take(i as int), psk(sp, j))
                    ==> jdone(sv, ps, d1, em, j),
            decreases n - i,
        {
            let m = if n - i < bcap { n - i } else { bcap };
            // part keys
            let mut b: usize = 0;
            while b < m
                invariant
                    ctx.wf(), i + m <= n, m <= bcap, b <= m, rl.len() == n, pp == ctx.pp(),
                    vok(fast, perm@, rv@, a1 as int, b1 as int, a2 as int, b2 as int, q0 as int, n as int),
                    rl == vlist(fast, perm@, rv@, a1 as int, b1 as int, a2 as int, b2 as int, q0 as int, n as int),
                    forall|t: int| 0 <= t < n ==> (#[trigger] rl[t]) < ctx.np && hit_row(pp, pat, rl[t] as int),
                    ks@.len() == bcap,
                    forall|c: int| 0 <= c < b ==> #[trigger] ks@[c] == pi::pkey_at(pp, rl[i + c] as int),
                decreases m - b,
            {
                let r = vrow(fast, perm, &rv, a1, b1, a2, b2, q0, n, i + b);
                let k = ctx.get_pk(r);
                ks[b] = k;
                b = b + 1;
            }
            // where their partsupp rows start; touch their first supplier keys and index entries
            b = 0;
            while b < m
                invariant
                    ctx.wf(), i + m <= n, m <= bcap, b <= m, rl.len() == n, pp == ctx.pp(),
                    ks@.len() == bcap, sts@.len() == bcap, tch@.len() == bcap,
                    w0@.len() == bcap, w1@.len() == bcap, run_mode == (ctx.runok && ctx.ratio <= 0x1_0000),
                    forall|c: int| 0 <= c < m ==> #[trigger] ks@[c] == pi::pkey_at(pp, rl[i + c] as int),
                    forall|c: int| 0 <= c < b ==> #[trigger] rows_at(&ctx, ks@[c] as int, w0@[c] as int, w1@[c] as int),
                decreases m - b,
            {
                let k = ks[b];
                let mut t: u64 = 0;
                if run_mode {
                    // rows by arithmetic; touch the first supplier key
                    let (lo, hi) = run_range(&ctx, k);
                    w0[b] = lo;
                    w1[b] = hi;
                    if lo < hi {
                        t = ctx.ssk[lo] as u64;
                    }
                } else {
                    let st = if ctx.sorted { ps_lower(&ctx, 0, k) } else { 0 };
                    w0[b] = st;
                    w1[b] = st;
                    if st < ctx.nps {
                        t = ctx.get_pss(st) as u64;
                    }
                }
                tch[b] = t;
                b = b + 1;
            }
            // each part
            b = 0;
            while b < m
                invariant
                    ctx.wf(), i + m <= n, m <= bcap, b <= m, rl.len() == n,
                    pp == ctx.pp(), pat == ctx.pat(), sp == ctx.sp(),
                    sv == ctx.sv@, ps == ctx.ps@, d1 == ctx.d1g@, ns == ctx.ns,
                    forall|t: int| 0 <= t < n ==> (#[trigger] rl[t]) < ctx.np && hit_row(pp, pat, rl[t] as int),
                    ks@.len() == bcap, w0@.len() == bcap, w1@.len() == bcap, run_mode == (ctx.runok && ctx.ratio <= 0x1_0000),
                    forall|c: int| 0 <= c < m ==> #[trigger] ks@[c] == pi::pkey_at(pp, rl[i + c] as int),
                    forall|c: int| 0 <= c < m ==> #[trigger] rows_at(&ctx, ks@[c] as int, w0@[c] as int, w1@[c] as int),
                    em.wf(ns), em.sound(sv, ps, d1, ns), em.fm == fm0,
                    tb_ok(&ctx, tb@, nb as int),
                    forall|j: int| 0 <= j < ctx.nps && #[trigger] hitl(pp, rl.take(i + b), psk(sp, j))
                        ==> jdone(sv, ps, d1, em, j),
                decreases m - b,
            {
                let ghost sfb = em;
                let k = ks[b];
                let lo = w0[b];
                let hi = w1[b];
                proof {
                    assert(ks@[b as int] == pi::pkey_at(pp, rl[i + b] as int));
                    assert(hit_row(pp, pat, rl[i + b] as int));
                    assert(sl_part_hit(pp, pat, k as int));
                    assert(rows_at(&ctx, k as int, lo as int, hi as int));
                }
                if run_mode {
                    let jk = do_part_run(&ctx, k, lo, hi, &tb, nb, &mut em);
                    junk = junk ^ jk;
                } else {
                    do_part(&ctx, k, lo, &tb, nb, &mut em);
                }
                proof {
                    assert forall|j: int| 0 <= j < ctx.nps && #[trigger] hitl(pp, rl.take(i + b + 1), psk(sp, j))
                        implies jdone(sv, ps, d1, em, j) by {
                        if psk(sp, j) != k {
                            let w = choose|w: int| 0 <= w < rl.take(i + b + 1).len() && #[trigger] pi::pkey_at(pp, rl.take(i + b + 1)[w] as int) == psk(sp, j);
                            assert(w != i + b);
                            assert(rl.take(i + b + 1)[w] == rl.take(i + b)[w]);
                            assert(hitl(pp, rl.take(i + b), psk(sp, j)));
                            lemma_jdone_mono(sv, ps, d1, sfb, em, j);
                        }
                    }
                }
                b = b + 1;
            }
            i = i + m;
        }
        proof {
            assert(rl.take(n as int) =~= rl);
        }
        // keep the touch loads: their values go out with the emitter
        let ghost e0 = em;
        em.junk = junk ^ tch[0];
        proof {
            lemma_junk(e0, em, ns, sv, ps, d1);
            assert forall|j: int| 0 <= j < ctx.nps && #[trigger] hitl(pp, rl, psk(sp, j)) implies jdone(sv, ps, d1, em, j) by {
                lemma_jdone_mono(sv, ps, d1, e0, em, j);
            }
        }
        em
    }
}

} // verus!
