//! Index plan: the part rows of each arm come from the (p_brand, p_container, p_size) index of storage `part_bcs`
//! (one contiguous range of index positions per brand and container: the sizes `1 ..= smax(a)` are consecutive
//! entries), their lineitem rows from the (l_partkey, l_shipinstruct, l_shipmode) index of storage `li_pkship` (a
//! directory entry per part key; the ship key byte of each position decides instruction and mode before any row
//! is read).
//!
//! Plan (`index_plan`):
//! 1. tables on the calling thread: the ship qualification table over the 256 ship keys (`ship_table`), the arm
//!    of each container entry and the brand matches of each arm (`part_tables`);
//! 2. `make_pieces`: one pass over the (brand, container) groups of the part index; a group whose container is in
//!    arm `a`'s list and whose brand is `a`'s yields the positions of sizes `1 ..= smax(a)`, cut into pieces of at
//!    most `CHUNK` positions; every other position's part has no arm (it contributes nothing);
//! 3. the pieces are split into at most `workers` tasks (`IxTask`), each adding its pieces with the staged batch
//!    kernel (`add_range`: stage A reads the key and directory range of up to `BATCH` parts, stage B collects the
//!    positions whose ship key qualifies, stage C reads quantity, price and discount of those rows; the loads of
//!    one stage are independent, so they overlap in memory);
//! 4. the calling thread adds the tasks' accumulators.
//! Any mass beyond `i128::MAX` (or a full match buffer, which only falls back to a per-part loop) makes the plan
//! give up (`None`): the caller then runs the incumbent plan, which handles capacity.
//!
//! Proof: accumulator `k` of a part row `z` with arm `a` and key `pk` is the sum of `mterm(k, a, q)` over the
//! directory range of `pk` (`lemma_part_sum`); stage B keeps, per part, the sum over its collected positions equal
//! to the sum over its range (non-qualifying positions have a zero term); stage C sums the collected positions,
//! which regroup into the parts' sums (`lemma_isum_regroup`). The pieces cover every position whose part has an
//! arm (`lemma_zone`), so the pieces' sums add up to the sums over all part index positions (`ixmodel::rsum`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::numeric::abs;
use crate::link::expr::{ival, tval};
use crate::link::join::{sum_of, lemma_sum_of_zero};
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::parallel::{Dispatch, fork_join, WorkerTask, MAX_WORKERS};
use crate::stores::part_bcs::interface as pbi;
use crate::stores::li_pkship::interface as lsi;
use super::common::fastdiv::{Divisor, divisor_ok};
use super::common::isum::*;
use super::kernel::{Acc, mmax};
use super::terms::*;
use super::model::{p15, abs_lt};
use super::ixmodel::*;
use super::tables::cont_bytes;

verus! {

/// Parts per batch of the staged kernel.
pub const BATCH: usize = 64;
/// Collected positions per batch (stage B).
pub const MCAP: usize = 8192;
/// Part index positions per piece.
pub const CHUNK: usize = 256;
/// Most worker tasks of one call.
pub const MAX_TASKS: usize = 32;

// ------------------------------------------------------------------------------------------------ handles

/// The lineitem index of li_pkship and the columns read at its rows.
#[derive(Clone, Copy)]
pub struct LIdx {
    pub kmin: i64,
    pub nk: usize,
    pub offs: &'static [u32],
    pub rows: &'static [u32],
    pub ship: &'static [u8],
    pub qc: &'static [u16],
    pub qb: &'static [i64],
    pub pc: &'static [u32],
    pub pb: &'static [i64],
    pub dc: &'static [u8],
    pub db: &'static [i64],
    pub dv: Divisor,
}

/// `l` holds the whole index and columns of `lp`, whose index is present.
pub open spec fn lidx_ok(l: LIdx, lp: Seq<PartView>) -> bool {
    &&& lp_ok(lp)
    &&& lsi::has_idx(lp)
    &&& l.kmin as int == lsi::idx_kmin(lp)
    &&& l.nk as int == lsi::idx_nkeys(lp)
    &&& l.offs@ == lsi::idx_offs(lp)
    &&& l.rows@ == lsi::idx_rows(lp)
    &&& l.ship@ == lsi::idx_ship(lp)
    &&& l.qc@ == lsi::u16s(lp[lsi::LI_QUANTITY_CODES as int])
    &&& l.qb@ == lsi::i64s(lp[lsi::LI_QUANTITY_BASE as int])
    &&& l.pc@ == lsi::u32s(lp[lsi::LI_PRICE_CODES as int])
    &&& l.pb@ == lsi::i64s(lp[lsi::LI_PRICE_BASE as int])
    &&& l.dc@ == lsi::u8s(lp[lsi::LI_DISCOUNT_CODES as int])
    &&& l.db@ == lsi::i64s(lp[lsi::LI_DISCOUNT_BASE as int])
    &&& divisor_ok(l.dv, lsi::bsize(lp))
}

/// The part index of part_bcs and its p_partkey column.
#[derive(Clone, Copy)]
pub struct PIdx {
    pub smin: i64,
    pub ns: usize,
    pub nb: usize,
    pub nc: usize,
    pub offs: &'static [u32],
    pub perm: &'static [u32],
    pub kc: &'static [u32],
    pub kb: &'static [i64],
    pub dv: Divisor,
}

/// `p` holds the whole index and p_partkey column of `pp`, whose index is present.
pub open spec fn pidx_ok(p: PIdx, pp: Seq<PartView>) -> bool {
    &&& pp_ok(pp)
    &&& pbi::has_idx(pp)
    &&& p.smin as int == pbi::idx_smin(pp)
    &&& p.ns as int == pbi::idx_ns(pp)
    &&& p.nb as int == pbi::n_brands(pp)
    &&& p.nc as int == pbi::n_conts(pp)
    &&& p.offs@ == pbi::idx_offs(pp)
    &&& p.perm@ == pbi::idx_perm(pp)
    &&& p.kc@ == pbi::u32s(pp[pbi::PA_PARTKEY_CODES as int])
    &&& p.kb@ == pbi::i64s(pp[pbi::PA_PARTKEY_BASE as int])
    &&& divisor_ok(p.dv, pbi::bsize(pp))
}

/// Positions `p0 .. p1` of the part index, every one holding a part row of arm `a`.
#[derive(Clone, Copy)]
pub struct Piece {
    pub p0: usize,
    pub p1: usize,
    pub a: usize,
}

/// The part row at index position `q` has no arm.
pub open spec fn no_arm(pp: Seq<PartView>, ps: Seq<Literal>, q: int) -> bool {
    zarm(ps, prows(pp)[q]) == 3 && prows(pp)[q].len() == 4
}

/// The part row at index position `q` has arm `a`.
pub open spec fn arm_is(pp: Seq<PartView>, ps: Seq<Literal>, q: int, a: int) -> bool {
    zarm(ps, prows(pp)[q]) == a
}

pub open spec fn piece_ok(pc: Piece, pp: Seq<PartView>, ps: Seq<Literal>) -> bool {
    &&& pc.p0 <= pc.p1 <= n_p(pp)
    &&& pc.a < 3
    &&& forall|p: int| pc.p0 <= p < pc.p1 ==> #[trigger] arm_is(pp, ps, p, pc.a as int)
}

// ------------------------------------------------------------------------------------------------ terms

/// The ship instruction and mode of the row at lineitem index position `q` qualify.
pub open spec fn qual_at(lp: Seq<PartView>, q: int) -> bool {
    let s = lsi::irow(lp, q);
    lsi::si_text(lp, lsi::si_at(lp, s)) == dip() && mode_in(lsi::sm_text(lp, lsi::sm_at(lp, s)))
}

/// The lineitem side of arm `a` at index position `q`.
pub open spec fn lq(lp: Seq<PartView>, ps: Seq<Literal>, a: int, q: int) -> bool {
    let s = lsi::irow(lp, q);
    li_arm(ps, a, lsi::qty_at(lp, s), lsi::si_text(lp, lsi::si_at(lp, s)), lsi::sm_text(lp, lsi::sm_at(lp, s)))
}

/// `l_extendedprice * (1 - l_discount)` (scale 4) at index position `q`.
pub open spec fn lv(lp: Seq<PartView>, q: int) -> int {
    let s = lsi::irow(lp, q);
    lsi::price_at(lp, s) * (100 - lsi::disc_at(lp, s))
}

/// Accumulator `k`'s term of index position `q` under arm `a` (the key condition aside).
pub open spec fn mterm(lp: Seq<PartView>, ps: Seq<Literal>, k: int, a: int, q: int) -> int {
    contrib(k, lq(lp, ps, a, q), lv(lp, q))
}

pub open spec fn mt(lp: Seq<PartView>, ps: Seq<Literal>, k: int, a: int) -> spec_fn(int) -> int {
    |q: int| mterm(lp, ps, k, a, q)
}

/// The terms of the collected positions `mq`.
pub open spec fn mf(lp: Seq<PartView>, ps: Seq<Literal>, k: int, a: int, mq: Seq<u32>) -> spec_fn(int) -> int {
    |t: int| mterm(lp, ps, k, a, mq[t] as int)
}

/// Accumulator `k` of the part row at part index position `p`.
pub open spec fn pt(lp: Seq<PartView>, pp: Seq<PartView>, ps: Seq<Literal>, k: int) -> spec_fn(int) -> int {
    |p: int| pin_l(lp, ps, k)(prows(pp)[p])
}

/// Accumulator `k` of piece `i` of `pcs`.
pub open spec fn pv(lp: Seq<PartView>, pp: Seq<PartView>, ps: Seq<Literal>, k: int, pcs: Seq<Piece>) -> spec_fn(int) -> int {
    |i: int| isum(pt(lp, pp, ps, k), pcs[i].p0 as int, pcs[i].p1 as int)
}

/// The p_partkey of the part row at part index position `p`.
pub open spec fn part_key(pp: Seq<PartView>, p: int) -> int {
    pbi::pkey_at(pp, pbi::prow(pp, p))
}

/// `o0 .. o1` is the directory range of key `pk` (empty for a key outside the directory).
pub open spec fn dir_range(lp: Seq<PartView>, pk: int, o0: int, o1: int) -> bool {
    let e = pk - lsi::idx_kmin(lp);
    if 0 <= e < lsi::idx_nkeys(lp) {
        o0 == lsi::idx_offs(lp)[e] && o1 == lsi::idx_offs(lp)[e + 1]
    } else {
        o0 == 0 && o1 == 0
    }
}

/// The accumulators hold the totals `c0` (count), `c1` (sum) and `c2` (mass), within the capacity.
pub open spec fn acc_rel(acc: Acc, c0: int, c1: int, c2: int) -> bool {
    &&& acc.sum == c1
    &&& acc.mass == c2
    &&& acc.any == (c0 > 0)
    &&& c0 >= 0
    &&& 0 <= c2 <= mmax()
    &&& -c2 <= c1 <= c2
}

/// The quantity window of each arm.
pub open spec fn arms_ok(qlo: Seq<i64>, qhi: Seq<i64>, ps: Seq<Literal>) -> bool {
    &&& qlo.len() == 3 && qhi.len() == 3
    &&& forall|a: int| 0 <= a < 3 ==> #[trigger] qlo[a] == 100 * qty_p(ps, a) && qhi[a] == 100 * (qty_p(ps, a) + 10)
}

/// The ship key table: entry `c` qualifies exactly when instruction `c / 16` and mode `c % 16` exist and qualify.
pub open spec fn qual_ok(qual: Seq<bool>, lp: Seq<PartView>) -> bool {
    &&& qual.len() == 256
    &&& forall|c: int| 0 <= c < 256 ==> #[trigger] qual[c] == (
            c / 16 < lsi::si_offs(lp).len() - 1 && c % 16 < lsi::sm_offs(lp).len() - 1
            && lsi::si_text(lp, c / 16) == dip() && mode_in(lsi::sm_text(lp, c % 16)))
}

// ------------------------------------------------------------------------------------------------ lemmas

/// `j < m * b` implies `j / b < m`.
pub proof fn lemma_div_lt(j: int, b: int, m: int)
    requires 0 <= j < m * b, b >= 1,
    ensures 0 <= j / b < m,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, b);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(j, b);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(j, b);
    assert(b * (j / b) == (j / b) * b) by (nonlinear_arith);
    assert(j / b < m) by (nonlinear_arith) requires (j / b) * b <= j, j < m * b, b >= 1;
}

/// Adding one term to the accumulators.
pub proof fn lemma_acc_add(acc: Acc, c0: int, c1: int, c2: int, pass: bool, v: int, acc2: Acc)
    requires
        acc_rel(acc, c0, c1, c2),
        acc2.sum == acc.sum + (if pass { v } else { 0 }),
        acc2.mass == acc.mass + (if pass { abs(v) } else { 0 }),
        acc2.any == (acc.any || pass),
        acc2.mass <= mmax(),
    ensures acc_rel(acc2, c0 + contrib(0, pass, v), c1 + contrib(1, pass, v), c2 + contrib(2, pass, v)),
{
}

/// The term of lineitem index position `q` for part row `z` of arm `a`: `mterm` when the keys are equal.
pub proof fn lemma_jt_pos(lp: Seq<PartView>, ps: Seq<Literal>, k: int, z: Row, a: int, q: int)
    requires
        lp_ok(lp),
        0 <= q < n_l(lp),
        z.len() == 4,
        0 <= a < 3,
        zarm(ps, z) == a,
    ensures
        jt(ps, k, z)(lrows(lp)[q]) == if lsi::key_at(lp, lsi::irow(lp, q)) == ival(z[0]) { mterm(lp, ps, k, a, q) } else { 0 },
{
    let y = lrows(lp)[q];
    assert(y == lrow(lp, q));
    assert(y.len() == 6);
    lemma_wq_arm(ps, y, z);
    lemma_joined(y, z);
}

/// A part row without an arm contributes nothing.
pub proof fn lemma_pin_l_none(lp: Seq<PartView>, ps: Seq<Literal>, k: int, z: Row)
    requires z.len() == 4, zarm(ps, z) == 3,
    ensures pin_l(lp, ps, k)(z) == 0,
{
    let rows = lrows(lp);
    assert forall|i: int| 0 <= i < rows.len() implies jt(ps, k, z)(#[trigger] rows[i]) == 0 by {
        assert(rows[i].len() == 6);
        lemma_wq_arm(ps, rows[i], z);
    }
    lemma_sum_of_zero(rows, jt(ps, k, z));
}

/// The row at a part index position: four values, its key and its arm's inputs.
pub proof fn lemma_prow(pp: Seq<PartView>, p: int)
    ensures
        prows(pp).len() == if n_p(pp) >= 0 { n_p(pp) } else { 0 },
        0 <= p < n_p(pp) ==> prows(pp)[p] == prow_val(pp, p),
        prow_val(pp, p).len() == 4,
        ival(prow_val(pp, p)[0]) == part_key(pp, p),
{
}

/// Accumulator `k` of a part row of arm `a` is the sum of the terms over the directory range of its key.
pub proof fn lemma_part_sum(lp: Seq<PartView>, ps: Seq<Literal>, k: int, z: Row, a: int, o0: int, o1: int)
    requires
        lp_ok(lp),
        lsi::has_idx(lp),
        z.len() == 4,
        0 <= a < 3,
        zarm(ps, z) == a,
        dir_range(lp, ival(z[0]), o0, o1),
    ensures
        pin_l(lp, ps, k)(z) == isum(mt(lp, ps, k, a), o0, o1),
        0 <= o0 <= o1 <= n_l(lp),
{
    let n = n_l(lp);
    let rows = lrows(lp);
    let pk = ival(z[0]);
    let g = |q: int| jt(ps, k, z)(rows[q]);
    lemma_sum_of_isum(rows, jt(ps, k, z), 0, n);
    assert(rows.subrange(0, n) =~= rows);
    let e = pk - lsi::idx_kmin(lp);
    if 0 <= e < lsi::idx_nkeys(lp) {
        assert forall|q: int| 0 <= q < n implies #[trigger] g(q) == (if o0 <= q < o1 { mterm(lp, ps, k, a, q) } else { 0 }) by {
            lsi::lemma_entry_exact(lp, n, e, q);
            lemma_jt_pos(lp, ps, k, z, a, q);
        }
        lsi::lemma_offs_mono(lp, n, e, e + 1);
        lsi::lemma_offs_mono(lp, n, e + 1, lsi::idx_nkeys(lp));
        lemma_isum_split(g, 0, o0, n);
        lemma_isum_split(g, o0, o1, n);
        lemma_isum_zero(g, 0, o0);
        lemma_isum_zero(g, o1, n);
        lemma_isum_ext(g, mt(lp, ps, k, a), o0, o1);
    } else {
        assert forall|q: int| 0 <= q < n implies #[trigger] g(q) == 0 by {
            lsi::lemma_outside_none(lp, n, pk, q);
            lemma_jt_pos(lp, ps, k, z, a, q);
        }
        lemma_isum_zero(g, 0, n);
    }
}

/// The ship key of position `q` decides `qual_at` through the table.
pub proof fn lemma_qual(lp: Seq<PartView>, qual: Seq<bool>, q: int)
    requires lp_ok(lp), lsi::has_idx(lp), qual_ok(qual, lp), 0 <= q < n_l(lp),
    ensures
        lsi::idx_ship(lp)[q] < 256,
        qual[lsi::idx_ship(lp)[q] as int] == qual_at(lp, q),
{
    let n = n_l(lp);
    assert(lsi::ship_key_ok(lp, q));
    let s = lsi::irow(lp, q);
    assert(0 <= s < n);
    assert(lsi::dict_idx_ok(lp, s));
    let (si, sm) = (lsi::si_at(lp, s), lsi::sm_at(lp, s));
    let c = lsi::idx_ship(lp)[q] as int;
    assert(c == 16 * si + sm);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(c, 16, si, sm);
}

/// The lineitem side of arm `a` is the qualifying ship key and the quantity window.
pub proof fn lemma_lq(lp: Seq<PartView>, ps: Seq<Literal>, a: int, q: int)
    ensures lq(lp, ps, a, q) == (qual_at(lp, q) && 100 * qty_p(ps, a) <= lsi::qty_at(lp, lsi::irow(lp, q))
        && lsi::qty_at(lp, lsi::irow(lp, q)) <= 100 * (qty_p(ps, a) + 10)),
{
}

/// The arm of a part row from the tables of its container (`ca`: the arm whose list holds it, 3 for none) and of
/// its brand (`bmatch`: it is arm `ca`'s brand).
pub proof fn lemma_arm_of(ps: Seq<Literal>, bt: Seq<u8>, sz: int, ct: Seq<u8>, ca: int, bmatch: bool)
    requires
        0 <= ca <= 3,
        ca < 3 ==> cont_in(ca, ct),
        ca == 3 ==> forall|a: int| 0 <= a < 3 ==> !#[trigger] cont_in(a, ct),
        ca < 3 ==> (bmatch == (bt == brand_p(ps, ca))),
    ensures
        arm_of(ps, bt, sz, ct) == if ca < 3 && bmatch && 1 <= sz <= smax(ca) { ca } else { 3 },
{
    if ca < 3 {
        assert forall|a: int| 0 <= a < 3 && a != ca implies !part_arm(ps, a, bt, sz, ct) by {
            if part_arm(ps, a, bt, sz, ct) {
                lemma_cont_first(a, ct);
                lemma_cont_first(ca, ct);
            }
        }
    }
}

/// Mixed radix: a key `h * ns + t` (`0 <= t < ns`) inside `g * ns + t0 .. g * ns + t1` has `h == g`.
pub proof fn lemma_radix(h: int, t: int, g: int, ns: int, t0: int, t1: int)
    requires 0 <= t < ns, 0 <= h, 0 <= g, 0 <= t0 <= t1 <= ns, g * ns + t0 <= h * ns + t < g * ns + t1,
    ensures h == g, t0 <= t < t1,
{
    if h < g {
        assert(h * ns + ns <= g * ns) by (nonlinear_arith) requires h + 1 <= g, ns >= 0;
    } else if h > g {
        assert(g * ns + ns <= h * ns) by (nonlinear_arith) requires g + 1 <= h, ns >= 0;
    }
}

/// A position of entries `g * ns + t0 .. g * ns + t1` of the part index: its row is in (brand, container) group
/// `g` with `p_size - smin` in `t0 .. t1`.
pub proof fn lemma_zone(pp: Seq<PartView>, g: int, t0: int, t1: int, p: int)
    requires
        pp_ok(pp),
        pbi::has_idx(pp),
        0 <= g < pbi::n_brands(pp) * pbi::n_conts(pp),
        0 <= t0 <= t1 <= pbi::idx_ns(pp),
        0 <= p < n_p(pp),
        pbi::idx_offs(pp)[g * pbi::idx_ns(pp) + t0] <= p < pbi::idx_offs(pp)[g * pbi::idx_ns(pp) + t1],
    ensures ({
        let r = pbi::prow(pp, p);
        &&& 0 <= r < n_p(pp)
        &&& pbi::bi_at(pp, r) == g / pbi::n_conts(pp)
        &&& pbi::ci_at(pp, r) == g % pbi::n_conts(pp)
        &&& t0 <= pbi::size_at(pp, r) - pbi::idx_smin(pp) < t1
    }),
{
    let n = n_p(pp);
    let (nb, nc, ns) = (pbi::n_brands(pp), pbi::n_conts(pp), pbi::idx_ns(pp));
    assert((g + 1) * ns <= nb * nc * ns) by (nonlinear_arith) requires g + 1 <= nb * nc, ns >= 1;
    assert(g * ns + t1 <= (g + 1) * ns) by (nonlinear_arith) requires t1 <= ns;
    assert(0 <= g * ns) by (nonlinear_arith) requires g >= 0, ns >= 1;
    pbi::lemma_entries_exact(pp, n, g * ns + t0, g * ns + t1, p);
    let r = pbi::prow(pp, p);
    assert(0 <= r < n);
    assert(pbi::dict_idx_ok(pp, r));
    assert(pbi::size_in(pp, r));
    let (bi, ci) = (pbi::bi_at(pp, r), pbi::ci_at(pp, r));
    let h = bi * nc + ci;
    assert(0 <= bi * nc) by (nonlinear_arith) requires bi >= 0, nc >= 0;
    let t = pbi::size_at(pp, r) - pbi::idx_smin(pp);
    assert(pbi::comp_at(pp, r) == h * ns + t);
    lemma_radix(h, t, g, ns, t0, t1);
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(g, nc, bi, ci);
}

/// Parts without an arm on a span of positions sum to 0.
pub proof fn lemma_span_zero(lp: Seq<PartView>, pp: Seq<PartView>, ps: Seq<Literal>, k: int, x0: int, x1: int)
    requires forall|p: int| x0 <= p < x1 ==> #[trigger] no_arm(pp, ps, p),
    ensures isum(pt(lp, pp, ps, k), x0, x1) == 0,
{
    assert forall|p: int| x0 <= p < x1 implies #[trigger] pt(lp, pp, ps, k)(p) == 0 by {
        assert(no_arm(pp, ps, p));
        lemma_pin_l_none(lp, ps, k, prows(pp)[p]);
    }
    lemma_isum_zero(pt(lp, pp, ps, k), x0, x1);
}

// ------------------------------------------------------------------------------------------------ text and tables

/// `bytes[lo .. hi] == needle`.
pub fn slice_eq(bytes: &[u8], lo: usize, hi: usize, needle: &[u8]) -> (r: bool)
    requires lo <= hi <= bytes@.len(),
    ensures r == (bytes@.subrange(lo as int, hi as int) == needle@),
{
    if hi - lo != needle.len() {
        proof {
            assert(bytes@.subrange(lo as int, hi as int).len() != needle@.len());
        }
        return false;
    }
    let mut i: usize = 0;
    while i < needle.len()
        invariant
            lo <= hi <= bytes@.len(), hi - lo == needle@.len(), i <= needle@.len(),
            forall|j: int| 0 <= j < i ==> bytes@[lo + j] == needle@[j],
        decreases needle@.len() - i,
    {
        if bytes[lo + i] != needle[i] {
            proof {
                assert(bytes@.subrange(lo as int, hi as int)[i as int] != needle@[i as int]);
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(bytes@.subrange(lo as int, hi as int) =~= needle@);
    }
    true
}

/// Entry `i` of a dictionary (offsets `offs`, bytes `bytes`) equals `needle` (false for an absent entry).
fn entry_eq(offs: &[u64], bytes: &[u8], i: usize, needle: &[u8]) -> (r: bool)
    requires
        offs@.len() >= 1,
        i < offs@.len() - 1 ==> offs@[i as int] <= offs@[i + 1] <= bytes@.len(),
    ensures r == (i < offs@.len() - 1 && bytes@.subrange(offs@[i as int] as int, offs@[i + 1] as int) == needle@),
{
    if i >= offs.len() - 1 {
        return false;
    }
    let nb = bytes.len();
    let lo = offs[i];
    let hi = offs[i + 1];
    proof {
        assert(hi as int <= nb as int);
    }
    slice_eq(bytes, lo as usize, hi as usize, needle)
}

/// The ship key table of `lp`.
pub fn ship_table(so: &[u64], sy: &[u8], mo: &[u64], my: &[u8], Ghost(lp): Ghost<Seq<PartView>>) -> (qual: Vec<bool>)
    requires
        lp_ok(lp),
        so@ == lsi::si_offs(lp), sy@ == lsi::si_bytes(lp), mo@ == lsi::sm_offs(lp), my@ == lsi::sm_bytes(lp),
    ensures qual_ok(qual@, lp),
{
    let vd: Vec<u8> = vec![68u8, 69u8, 76u8, 73u8, 86u8, 69u8, 82u8, 32u8, 73u8, 78u8, 32u8, 80u8, 69u8, 82u8, 83u8, 79u8, 78u8];
    let va: Vec<u8> = vec![65u8, 73u8, 82u8];
    let vr: Vec<u8> = vec![65u8, 73u8, 82u8, 32u8, 82u8, 69u8, 71u8];
    proof {
        assert(vd@ =~= dip());
        assert(va@ =~= air());
        assert(vr@ =~= air_reg());
    }
    let mut sq: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < 16
        invariant
            lp_ok(lp), so@ == lsi::si_offs(lp), sy@ == lsi::si_bytes(lp), vd@ == dip(),
            i <= 16, sq@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] sq@[j] == (j < lsi::si_offs(lp).len() - 1 && lsi::si_text(lp, j) == dip()),
        decreases 16 - i,
    {
        proof {
            if i < lsi::si_offs(lp).len() - 1 {
                assert(lsi::dict_range_ok(so@, sy@, i as int));
            }
        }
        let ok = entry_eq(so, sy, i, vd.as_slice());
        sq.push(ok);
        i = i + 1;
    }
    let mut mq: Vec<bool> = Vec::new();
    let mut j: usize = 0;
    while j < 16
        invariant
            lp_ok(lp), mo@ == lsi::sm_offs(lp), my@ == lsi::sm_bytes(lp), va@ == air(), vr@ == air_reg(),
            j <= 16, mq@.len() == j,
            forall|x: int| 0 <= x < j ==> #[trigger] mq@[x] == (x < lsi::sm_offs(lp).len() - 1 && mode_in(lsi::sm_text(lp, x))),
        decreases 16 - j,
    {
        proof {
            if j < lsi::sm_offs(lp).len() - 1 {
                assert(lsi::dict_range_ok(mo@, my@, j as int));
            }
        }
        let ok = entry_eq(mo, my, j, va.as_slice()) || entry_eq(mo, my, j, vr.as_slice());
        mq.push(ok);
        j = j + 1;
    }
    let mut qual: Vec<bool> = Vec::new();
    let mut c: usize = 0;
    while c < 256
        invariant
            sq@.len() == 16, mq@.len() == 16,
            forall|j: int| 0 <= j < 16 ==> #[trigger] sq@[j] == (j < lsi::si_offs(lp).len() - 1 && lsi::si_text(lp, j) == dip()),
            forall|x: int| 0 <= x < 16 ==> #[trigger] mq@[x] == (x < lsi::sm_offs(lp).len() - 1 && mode_in(lsi::sm_text(lp, x))),
            c <= 256, qual@.len() == c,
            forall|d: int| 0 <= d < c ==> #[trigger] qual@[d] == (
                d / 16 < lsi::si_offs(lp).len() - 1 && d % 16 < lsi::sm_offs(lp).len() - 1
                && lsi::si_text(lp, d / 16) == dip() && mode_in(lsi::sm_text(lp, d % 16))),
        decreases 256 - c,
    {
        let x = sq[c / 16] && mq[c % 16];
        qual.push(x);
        c = c + 1;
    }
    qual
}

/// The container arm table: `carm[c] < 3` is the arm whose list holds container entry `c`, 3 when none does.
pub open spec fn carm_ok(carm: Seq<u8>, pp: Seq<PartView>) -> bool {
    &&& carm.len() == pbi::n_conts(pp)
    &&& forall|c: int| 0 <= c < carm.len() ==> {
        &&& #[trigger] carm[c] <= 3
        &&& carm[c] < 3 ==> cont_in(carm[c] as int, pbi::c_text(pp, c))
        &&& carm[c] == 3 ==> forall|a: int| 0 <= a < 3 ==> !#[trigger] cont_in(a, pbi::c_text(pp, c))
    }
}

/// The brand table of arm `a`: entry `b` is arm `a`'s brand parameter.
pub open spec fn bm_ok(bm: Seq<bool>, pp: Seq<PartView>, ps: Seq<Literal>, a: int) -> bool {
    &&& bm.len() == pbi::n_brands(pp)
    &&& forall|b: int| 0 <= b < bm.len() ==> #[trigger] bm[b] == (pbi::b_text(pp, b) == brand_p(ps, a))
}

/// The arm of one container entry.
fn cont_arm(co: &[u64], cy: &[u8], c: usize, Ghost(pp): Ghost<Seq<PartView>>) -> (arm: u8)
    requires
        pp_ok(pp), co@ == pbi::c_offs(pp), cy@ == pbi::c_bytes(pp),
        c < pbi::n_conts(pp),
    ensures
        arm <= 3,
        arm < 3 ==> cont_in(arm as int, pbi::c_text(pp, c as int)),
        arm == 3 ==> forall|a: int| 0 <= a < 3 ==> !#[trigger] cont_in(a, pbi::c_text(pp, c as int)),
{
    let ghost ct = pbi::c_text(pp, c as int);
    let mut arm: u8 = 3;
    let mut a: u8 = 0;
    while a < 3
        invariant
            pp_ok(pp), co@ == pbi::c_offs(pp), cy@ == pbi::c_bytes(pp), c < pbi::n_conts(pp),
            ct == pbi::c_text(pp, c as int),
            a <= 3, arm <= 3,
            arm < 3 ==> cont_in(arm as int, ct),
            arm == 3 ==> forall|a2: int| 0 <= a2 < a ==> !#[trigger] cont_in(a2, ct),
        decreases 3 - a,
    {
        let mut i: u8 = 0;
        let mut hit = false;
        while i < 4
            invariant
                pp_ok(pp), co@ == pbi::c_offs(pp), cy@ == pbi::c_bytes(pp), c < pbi::n_conts(pp),
                ct == pbi::c_text(pp, c as int),
                a < 3, i <= 4,
                hit == exists|i2: int| 0 <= i2 < i && ct == #[trigger] cont_lit(a as int, i2),
            decreases 4 - i,
        {
            let v = cont_bytes(a, i);
            proof {
                assert(pbi::dict_range_ok(co@, cy@, c as int));
            }
            let e = entry_eq(co, cy, c, v.as_slice());
            proof {
                assert(e == (ct == cont_lit(a as int, i as int)));
            }
            hit = hit || e;
            i = i + 1;
        }
        proof {
            if hit {
                let i2 = choose|i2: int| 0 <= i2 < 4 && ct == #[trigger] cont_lit(a as int, i2);
                assert(cont_in(a as int, ct));
            } else {
                assert(ct != cont_lit(a as int, 0));
                assert(ct != cont_lit(a as int, 1));
                assert(ct != cont_lit(a as int, 2));
                assert(ct != cont_lit(a as int, 3));
            }
        }
        if hit {
            arm = a;
        }
        a = a + 1;
    }
    arm
}

/// The container arm table of `pp`.
pub fn cont_table(co: &[u64], cy: &[u8], Ghost(pp): Ghost<Seq<PartView>>) -> (carm: Vec<u8>)
    requires pp_ok(pp), co@ == pbi::c_offs(pp), cy@ == pbi::c_bytes(pp),
    ensures carm_ok(carm@, pp),
{
    let nc = co.len() - 1;
    let mut carm: Vec<u8> = Vec::new();
    let mut c: usize = 0;
    while c < nc
        invariant
            pp_ok(pp), co@ == pbi::c_offs(pp), cy@ == pbi::c_bytes(pp), nc == pbi::n_conts(pp),
            c <= nc, carm@.len() == c,
            forall|c2: int| 0 <= c2 < c ==> {
                &&& #[trigger] carm@[c2] <= 3
                &&& carm@[c2] < 3 ==> cont_in(carm@[c2] as int, pbi::c_text(pp, c2))
                &&& carm@[c2] == 3 ==> forall|a: int| 0 <= a < 3 ==> !#[trigger] cont_in(a, pbi::c_text(pp, c2))
            },
        decreases nc - c,
    {
        let x = cont_arm(co, cy, c, Ghost(pp));
        carm.push(x);
        c = c + 1;
    }
    carm
}

/// The brand table of arm `a` (brand parameter `brand`).
pub fn brand_table(bo: &[u64], by: &[u8], brand: &[u8], Ghost(pp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>,
    Ghost(a): Ghost<int>) -> (bm: Vec<bool>)
    requires pp_ok(pp), bo@ == pbi::b_offs(pp), by@ == pbi::b_bytes(pp), brand@ == brand_p(ps, a),
    ensures bm_ok(bm@, pp, ps, a),
{
    let nb = bo.len() - 1;
    let mut bm: Vec<bool> = Vec::new();
    let mut b: usize = 0;
    while b < nb
        invariant
            pp_ok(pp), bo@ == pbi::b_offs(pp), by@ == pbi::b_bytes(pp), nb == pbi::n_brands(pp), brand@ == brand_p(ps, a),
            b <= nb, bm@.len() == b,
            forall|b2: int| 0 <= b2 < b ==> #[trigger] bm@[b2] == (pbi::b_text(pp, b2) == brand_p(ps, a)),
        decreases nb - b,
    {
        proof {
            assert(pbi::dict_range_ok(bo@, by@, b as int));
        }
        let x = entry_eq(bo, by, b, brand);
        bm.push(x);
        b = b + 1;
    }
    bm
}

// ------------------------------------------------------------------------------------------------ row reads

/// The quantity, price and discount of the row at lineitem index position `q`.
#[inline(always)]
fn row_vals(l: &LIdx, q: usize, Ghost(lp): Ghost<Seq<PartView>>) -> (r: (i64, i64, i64))
    requires lidx_ok(*l, lp), q < n_l(lp),
    ensures ({
        let s = lsi::irow(lp, q as int);
        &&& r.0 == lsi::qty_at(lp, s) && r.1 == lsi::price_at(lp, s) && r.2 == lsi::disc_at(lp, s)
        &&& abs_lt(r.1 as int, p15()) && abs_lt(r.2 as int, p15())
    }),
    no_unwind
{
    let ghost n = n_l(lp);
    let ghost bs = lsi::bsize(lp);
    proof {
        assert(0 <= lsi::irow(lp, q as int) < n);
    }
    let s = l.rows[q] as usize;
    proof {
        assert(s as int == lsi::irow(lp, q as int));
        assert(l_vals_ok(lp, s as int));
        lemma_div_lt(s as int, bs, l.qb@.len() as int);
        lemma_div_lt(s as int, bs, l.pb@.len() as int);
        lemma_div_lt(s as int, bs, l.db@.len() as int);
    }
    let g = l.dv.div(s as u64) as usize;
    let qv = l.qb[g] + l.qc[s] as i64;
    let pr = l.pb[g] + l.pc[s] as i64;
    let d = l.db[g] + l.dc[s] as i64;
    (qv, pr, d)
}

/// `price * (100 - disc)`, exact, with its absolute value.
#[inline(always)]
fn row_value(pr: i64, d: i64) -> (r: (i128, i128))
    requires abs_lt(pr as int, p15()), abs_lt(d as int, p15()),
    ensures r.0 == pr * (100 - d), r.1 == abs(pr * (100 - d)), 0 <= r.1 <= 0x10_0000_0000_0000_0000_0000_0000,
    no_unwind
{
    let f = 100 - (d as i128);
    proof {
        let (x, y) = (pr as int, f as int);
        assert(-1_000_000_000_000_000 < x < 1_000_000_000_000_000);
        assert(-1_000_000_000_000_000 < y < 1_000_000_000_000_101);
        assert(-0x10_0000_0000_0000_0000_0000_0000 <= x * y <= 0x10_0000_0000_0000_0000_0000_0000) by (nonlinear_arith)
            requires -1_000_000_000_000_000 < x < 1_000_000_000_000_000, -1_000_000_000_000_000 < y < 1_000_000_000_000_101;
    }
    let v = (pr as i128) * f;
    let av = if v < 0 { -v } else { v };
    (v, av)
}

// ------------------------------------------------------------------------------------------------ the staged kernel

/// The directory range of key `pk`.
#[inline(always)]
fn dir_lookup(l: &LIdx, pk: i64, Ghost(lp): Ghost<Seq<PartView>>) -> (r: (u32, u32))
    requires lidx_ok(*l, lp),
    ensures dir_range(lp, pk as int, r.0 as int, r.1 as int), r.0 <= r.1 <= n_l(lp),
    no_unwind
{
    let e128 = (pk as i128) - (l.kmin as i128);
    if e128 >= 0 && e128 < l.nk as i128 {
        let e = e128 as usize;
        proof {
            lsi::lemma_offs_mono(lp, n_l(lp), e as int, e as int + 1);
            lsi::lemma_offs_mono(lp, n_l(lp), e as int + 1, lsi::idx_nkeys(lp));
        }
        (l.offs[e], l.offs[e + 1])
    } else {
        (0, 0)
    }
}

/// The key of the part row at part index position `i`.
#[inline(always)]
fn part_key_at(p: &PIdx, i: usize, Ghost(pp): Ghost<Seq<PartView>>) -> (pk: i64)
    requires pidx_ok(*p, pp), i < n_p(pp),
    ensures pk as int == part_key(pp, i as int),
    no_unwind
{
    let ghost n = n_p(pp);
    proof {
        assert(0 <= pbi::prow(pp, i as int) < n);
    }
    let r = p.perm[i] as usize;
    proof {
        assert(p_vals_ok(pp, r as int));
        lemma_div_lt(r as int, pbi::bsize(pp), p.kb@.len() as int);
    }
    p.kb[p.dv.div(r as u64) as usize] + p.kc[r] as i64
}

/// Adds the terms of lineitem index positions `o0 .. o1` under arm `a` (window `qlo ..= qhi`); `false` when the
/// mass would exceed `i128::MAX`.
fn add_span(l: &LIdx, qual: &Vec<bool>, o0: usize, o1: usize, a: usize, qlo: i64, qhi: i64, acc: &mut Acc,
    Ghost(lp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(c): Ghost<(int, int, int)>) -> (ok: bool)
    requires
        lidx_ok(*l, lp), qual_ok(qual@, lp),
        o0 <= o1 <= n_l(lp), a < 3,
        qlo == 100 * qty_p(ps, a as int), qhi == 100 * (qty_p(ps, a as int) + 10),
        acc_rel(*old(acc), c.0, c.1, c.2),
    ensures
        ok ==> acc_rel(*final(acc), c.0 + isum(mt(lp, ps, 0, a as int), o0 as int, o1 as int),
            c.1 + isum(mt(lp, ps, 1, a as int), o0 as int, o1 as int),
            c.2 + isum(mt(lp, ps, 2, a as int), o0 as int, o1 as int)),
    no_unwind
{
    let ghost ai = a as int;
    let mut q = o0;
    while q < o1
        invariant
            lidx_ok(*l, lp), qual_ok(qual@, lp),
            o0 <= q <= o1 <= n_l(lp), a < 3, ai == a,
            qlo == 100 * qty_p(ps, ai), qhi == 100 * (qty_p(ps, ai) + 10),
            acc_rel(*acc, c.0 + isum(mt(lp, ps, 0, ai), o0 as int, q as int),
                c.1 + isum(mt(lp, ps, 1, ai), o0 as int, q as int),
                c.2 + isum(mt(lp, ps, 2, ai), o0 as int, q as int)),
        decreases o1 - q,
    {
        let ghost c0 = c.0 + isum(mt(lp, ps, 0, ai), o0 as int, q as int);
        let ghost c1 = c.1 + isum(mt(lp, ps, 1, ai), o0 as int, q as int);
        let ghost c2 = c.2 + isum(mt(lp, ps, 2, ai), o0 as int, q as int);
        proof {
            lemma_qual(lp, qual@, q as int);
            lemma_lq(lp, ps, ai, q as int);
            lemma_isum_step(mt(lp, ps, 0, ai), o0 as int, q as int);
            lemma_isum_step(mt(lp, ps, 1, ai), o0 as int, q as int);
            lemma_isum_step(mt(lp, ps, 2, ai), o0 as int, q as int);
        }
        if qual[l.ship[q] as usize] {
            let (qv, pr, d) = row_vals(l, q, Ghost(lp));
            let pass = qlo <= qv && qv <= qhi;
            let (v0, av0) = row_value(pr, d);
            let v: i128 = if pass { v0 } else { 0 };
            let av: i128 = if pass { av0 } else { 0 };
            if acc.mass > i128::MAX - av {
                return false;
            }
            let ghost old_acc = *acc;
            acc.sum = acc.sum + v;
            acc.mass = acc.mass + av;
            acc.any = acc.any || pass;
            proof {
                assert(lq(lp, ps, ai, q as int) == pass);
                assert(lv(lp, q as int) == v0);
                lemma_acc_add(old_acc, c0, c1, c2, pass, v0 as int, *acc);
            }
        } else {
            proof {
                assert(!lq(lp, ps, ai, q as int));
            }
        }
        q = q + 1;
    }
    true
}

/// Part `b + i` of a batch: `lo[i] .. hi[i]` is the directory range of its key.
pub open spec fn range_at(lp: Seq<PartView>, pp: Seq<PartView>, b: int, lo: Seq<u32>, hi: Seq<u32>, i: int) -> bool {
    &&& dir_range(lp, part_key(pp, b + i), lo[i] as int, hi[i] as int)
    &&& lo[i] <= hi[i] <= n_l(lp)
}

/// Stage A: the directory range of each part of the batch `b .. b + cnt`.
fn stage_a(p: &PIdx, l: &LIdx, b: usize, cnt: usize, lo: &mut Vec<u32>, hi: &mut Vec<u32>,
    Ghost(pp): Ghost<Seq<PartView>>, Ghost(lp): Ghost<Seq<PartView>>)
    requires
        pidx_ok(*p, pp), lidx_ok(*l, lp),
        b + cnt <= n_p(pp), b + cnt <= usize::MAX, cnt <= BATCH,
        old(lo)@.len() == BATCH, old(hi)@.len() == BATCH,
    ensures
        final(lo)@.len() == BATCH, final(hi)@.len() == BATCH,
        forall|i: int| 0 <= i < cnt ==> #[trigger] range_at(lp, pp, b as int, final(lo)@, final(hi)@, i),
    no_unwind
{
    let mut i: usize = 0;
    while i < cnt
        invariant
            pidx_ok(*p, pp), lidx_ok(*l, lp),
            b + cnt <= n_p(pp), b + cnt <= usize::MAX, cnt <= BATCH, i <= cnt,
            lo@.len() == BATCH, hi@.len() == BATCH,
            forall|i2: int| 0 <= i2 < i ==> #[trigger] range_at(lp, pp, b as int, lo@, hi@, i2),
        decreases cnt - i,
    {
        let pk = part_key_at(p, b + i, Ghost(pp));
        let (o0, o1) = dir_lookup(l, pk, Ghost(lp));
        let ghost (lo0, hi0) = (lo@, hi@);
        lo[i] = o0;
        hi[i] = o1;
        proof {
            assert(pk as int == part_key(pp, b + i));
            assert(dir_range(lp, pk as int, o0 as int, o1 as int));
            assert forall|i2: int| 0 <= i2 < i + 1 implies #[trigger] range_at(lp, pp, b as int, lo@, hi@, i2) by {
                if i2 < i {
                    assert(range_at(lp, pp, b as int, lo0, hi0, i2));
                    assert(lo@[i2] == lo0[i2] && hi@[i2] == hi0[i2]);
                } else {
                    assert(lo@[i2] == o0 && hi@[i2] == o1);
                }
            }
        }
        i = i + 1;
    }
}

/// Per part `i` of a batch: the terms of its collected positions sum like the terms of its directory range.
pub open spec fn part_done(lp: Seq<PartView>, ps: Seq<Literal>, a: int, mq: Seq<u32>, starts: Seq<u32>, lo: Seq<u32>,
    hi: Seq<u32>, i: int) -> bool
{
    &&& starts[i] <= starts[i + 1]
    &&& isum(mf(lp, ps, 0, a, mq), starts[i] as int, starts[i + 1] as int) == isum(mt(lp, ps, 0, a), lo[i] as int, hi[i] as int)
    &&& isum(mf(lp, ps, 1, a, mq), starts[i] as int, starts[i + 1] as int) == isum(mt(lp, ps, 1, a), lo[i] as int, hi[i] as int)
    &&& isum(mf(lp, ps, 2, a, mq), starts[i] as int, starts[i + 1] as int) == isum(mt(lp, ps, 2, a), lo[i] as int, hi[i] as int)
}

/// Collected positions agreeing below `bound` keep their sums below it.
proof fn lemma_mf_frame(lp: Seq<PartView>, ps: Seq<Literal>, a: int, mq0: Seq<u32>, mq1: Seq<u32>, t0: int, t1: int, bound: int)
    requires 0 <= t0, t1 <= bound, forall|t: int| 0 <= t < bound ==> #[trigger] mq0[t] == mq1[t],
    ensures
        isum(mf(lp, ps, 0, a, mq0), t0, t1) == isum(mf(lp, ps, 0, a, mq1), t0, t1),
        isum(mf(lp, ps, 1, a, mq0), t0, t1) == isum(mf(lp, ps, 1, a, mq1), t0, t1),
        isum(mf(lp, ps, 2, a, mq0), t0, t1) == isum(mf(lp, ps, 2, a, mq1), t0, t1),
{
    assert forall|t: int| t0 <= t < t1 implies #[trigger] mf(lp, ps, 0, a, mq0)(t) == mf(lp, ps, 0, a, mq1)(t) by {
        assert(mq0[t] == mq1[t]);
    }
    assert forall|t: int| t0 <= t < t1 implies #[trigger] mf(lp, ps, 1, a, mq0)(t) == mf(lp, ps, 1, a, mq1)(t) by {
        assert(mq0[t] == mq1[t]);
    }
    assert forall|t: int| t0 <= t < t1 implies #[trigger] mf(lp, ps, 2, a, mq0)(t) == mf(lp, ps, 2, a, mq1)(t) by {
        assert(mq0[t] == mq1[t]);
    }
    lemma_isum_ext(mf(lp, ps, 0, a, mq0), mf(lp, ps, 0, a, mq1), t0, t1);
    lemma_isum_ext(mf(lp, ps, 1, a, mq0), mf(lp, ps, 1, a, mq1), t0, t1);
    lemma_isum_ext(mf(lp, ps, 2, a, mq0), mf(lp, ps, 2, a, mq1), t0, t1);
}

/// Stage B for one part: the qualifying positions of `o0 .. o1` appended at `mq[m0 ..]`; `None` when the buffer
/// is full.
fn collect(l: &LIdx, qual: &Vec<bool>, o0: usize, o1: usize, m0: usize, mq: &mut Vec<u32>,
    Ghost(lp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(a): Ghost<int>) -> (r: Option<usize>)
    requires
        lidx_ok(*l, lp), qual_ok(qual@, lp),
        o0 <= o1 <= n_l(lp), o1 <= u32::MAX, m0 <= MCAP, old(mq)@.len() == MCAP + 1,
        forall|t: int| 0 <= t < m0 ==> (#[trigger] old(mq)@[t]) < n_l(lp) && qual_at(lp, old(mq)@[t] as int),
    ensures
        final(mq)@.len() == MCAP + 1,
        r matches Some(m) ==> {
            &&& m0 <= m <= MCAP
            &&& forall|t: int| 0 <= t < m0 ==> #[trigger] final(mq)@[t] == old(mq)@[t]
            &&& forall|t: int| 0 <= t < m ==> (#[trigger] final(mq)@[t]) < n_l(lp) && qual_at(lp, final(mq)@[t] as int)
            &&& isum(mf(lp, ps, 0, a, final(mq)@), m0 as int, m as int) == isum(mt(lp, ps, 0, a), o0 as int, o1 as int)
            &&& isum(mf(lp, ps, 1, a, final(mq)@), m0 as int, m as int) == isum(mt(lp, ps, 1, a), o0 as int, o1 as int)
            &&& isum(mf(lp, ps, 2, a, final(mq)@), m0 as int, m as int) == isum(mt(lp, ps, 2, a), o0 as int, o1 as int)
        },
    no_unwind
{
    let ghost mq_in = mq@;
    let mut m = m0;
    let mut q = o0;
    while q < o1
        invariant
            lidx_ok(*l, lp), qual_ok(qual@, lp),
            o0 <= q <= o1 <= n_l(lp), o1 <= u32::MAX, m0 <= m <= MCAP, mq@.len() == MCAP + 1,
            forall|t: int| 0 <= t < m0 ==> #[trigger] mq@[t] == mq_in[t],
            forall|t: int| 0 <= t < m ==> (#[trigger] mq@[t]) < n_l(lp) && qual_at(lp, mq@[t] as int),
            isum(mf(lp, ps, 0, a, mq@), m0 as int, m as int) == isum(mt(lp, ps, 0, a), o0 as int, q as int),
            isum(mf(lp, ps, 1, a, mq@), m0 as int, m as int) == isum(mt(lp, ps, 1, a), o0 as int, q as int),
            isum(mf(lp, ps, 2, a, mq@), m0 as int, m as int) == isum(mt(lp, ps, 2, a), o0 as int, q as int),
        decreases o1 - q,
    {
        if m == MCAP {
            return None;
        }
        let ghost mq_old = mq@;
        mq[m] = q as u32;
        proof {
            lemma_qual(lp, qual@, q as int);
            lemma_lq(lp, ps, a, q as int);
            lemma_isum_step(mt(lp, ps, 0, a), o0 as int, q as int);
            lemma_isum_step(mt(lp, ps, 1, a), o0 as int, q as int);
            lemma_isum_step(mt(lp, ps, 2, a), o0 as int, q as int);
            assert forall|t: int| 0 <= t < m implies #[trigger] mq_old[t] == mq@[t] by {}
            lemma_mf_frame(lp, ps, a, mq_old, mq@, m0 as int, m as int, m as int);
        }
        if qual[l.ship[q] as usize] {
            proof {
                lemma_isum_step(mf(lp, ps, 0, a, mq@), m0 as int, m as int);
                lemma_isum_step(mf(lp, ps, 1, a, mq@), m0 as int, m as int);
                lemma_isum_step(mf(lp, ps, 2, a, mq@), m0 as int, m as int);
            }
            m = m + 1;
        } else {
            proof {
                assert(!lq(lp, ps, a, q as int));
            }
        }
        q = q + 1;
    }
    Some(m)
}

/// Stage B: the qualifying positions of every part of the batch, part `i`'s at `mq[starts[i] .. starts[i + 1]]`;
/// `None` when the buffer is full.
fn stage_b(l: &LIdx, qual: &Vec<bool>, cnt: usize, lo: &Vec<u32>, hi: &Vec<u32>, starts: &mut Vec<u32>, mq: &mut Vec<u32>,
    Ghost(lp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(a): Ghost<int>) -> (r: Option<usize>)
    requires
        lidx_ok(*l, lp), qual_ok(qual@, lp),
        cnt <= BATCH, lo@.len() == BATCH, hi@.len() == BATCH,
        forall|i: int| 0 <= i < cnt ==> #[trigger] lo@[i] <= hi@[i] <= n_l(lp),
        old(starts)@.len() == BATCH + 1, old(mq)@.len() == MCAP + 1,
    ensures
        final(starts)@.len() == BATCH + 1, final(mq)@.len() == MCAP + 1,
        r matches Some(m) ==> {
            &&& m <= MCAP
            &&& final(starts)@[0] == 0
            &&& final(starts)@[cnt as int] == m
            &&& forall|t: int| 0 <= t < m ==> (#[trigger] final(mq)@[t]) < n_l(lp) && qual_at(lp, final(mq)@[t] as int)
            &&& forall|i: int| 0 <= i < cnt ==> #[trigger] part_done(lp, ps, a, final(mq)@, final(starts)@, lo@, hi@, i)
        },
    no_unwind
{
    let mut m: usize = 0;
    let mut i: usize = 0;
    starts[0] = 0;
    while i < cnt
        invariant
            lidx_ok(*l, lp), qual_ok(qual@, lp),
            cnt <= BATCH, lo@.len() == BATCH, hi@.len() == BATCH,
            forall|i2: int| 0 <= i2 < cnt ==> #[trigger] lo@[i2] <= hi@[i2] <= n_l(lp),
            starts@.len() == BATCH + 1, mq@.len() == MCAP + 1,
            i <= cnt, m <= MCAP,
            starts@[0] == 0,
            starts@[i as int] == m,
            forall|t: int| 0 <= t < m ==> (#[trigger] mq@[t]) < n_l(lp) && qual_at(lp, mq@[t] as int),
            forall|i2: int| 0 <= i2 < i ==> #[trigger] part_done(lp, ps, a, mq@, starts@, lo@, hi@, i2) && starts@[i2 + 1] <= m,
        decreases cnt - i,
    {
        let ghost mq0 = mq@;
        let ghost st0 = starts@;
        match collect(l, qual, lo[i] as usize, hi[i] as usize, m, mq, Ghost(lp), Ghost(ps), Ghost(a)) {
            None => {
                return None;
            },
            Some(m2) => {
                starts[i + 1] = m2 as u32;
                proof {
                    assert forall|i2: int| 0 <= i2 < i + 1 implies #[trigger] part_done(lp, ps, a, mq@, starts@, lo@, hi@, i2)
                        && starts@[i2 + 1] <= m2 by {
                        if i2 < i {
                            assert(part_done(lp, ps, a, mq0, st0, lo@, hi@, i2));
                            assert(starts@[i2] == st0[i2] && starts@[i2 + 1] == st0[i2 + 1]);
                            lemma_mf_frame(lp, ps, a, mq0, mq@, st0[i2] as int, st0[i2 + 1] as int, m as int);
                        } else {
                            assert(starts@[i2] == m && starts@[i2 + 1] == m2);
                        }
                    }
                }
                m = m2;
            },
        }
        i = i + 1;
    }
    Some(m)
}

/// Stage C: adds the terms of the collected positions `mq[0 .. m]` (all qualifying) under arm `a`.
fn stage_c(l: &LIdx, mq: &Vec<u32>, m: usize, a: usize, qlo: i64, qhi: i64, acc: &mut Acc,
    Ghost(lp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(c): Ghost<(int, int, int)>) -> (ok: bool)
    requires
        lidx_ok(*l, lp), a < 3,
        m <= mq@.len(),
        forall|t: int| 0 <= t < m ==> (#[trigger] mq@[t]) < n_l(lp) && qual_at(lp, mq@[t] as int),
        qlo == 100 * qty_p(ps, a as int), qhi == 100 * (qty_p(ps, a as int) + 10),
        acc_rel(*old(acc), c.0, c.1, c.2),
    ensures
        ok ==> acc_rel(*final(acc), c.0 + isum(mf(lp, ps, 0, a as int, mq@), 0, m as int),
            c.1 + isum(mf(lp, ps, 1, a as int, mq@), 0, m as int),
            c.2 + isum(mf(lp, ps, 2, a as int, mq@), 0, m as int)),
    no_unwind
{
    let ghost ai = a as int;
    let mut t: usize = 0;
    while t < m
        invariant
            lidx_ok(*l, lp), a < 3, ai == a,
            m <= mq@.len(),
            forall|t2: int| 0 <= t2 < m ==> (#[trigger] mq@[t2]) < n_l(lp) && qual_at(lp, mq@[t2] as int),
            qlo == 100 * qty_p(ps, ai), qhi == 100 * (qty_p(ps, ai) + 10),
            t <= m,
            acc_rel(*acc, c.0 + isum(mf(lp, ps, 0, ai, mq@), 0, t as int),
                c.1 + isum(mf(lp, ps, 1, ai, mq@), 0, t as int),
                c.2 + isum(mf(lp, ps, 2, ai, mq@), 0, t as int)),
        decreases m - t,
    {
        let ghost c0 = c.0 + isum(mf(lp, ps, 0, ai, mq@), 0, t as int);
        let ghost c1 = c.1 + isum(mf(lp, ps, 1, ai, mq@), 0, t as int);
        let ghost c2 = c.2 + isum(mf(lp, ps, 2, ai, mq@), 0, t as int);
        let q = mq[t] as usize;
        let (qv, pr, d) = row_vals(l, q, Ghost(lp));
        let pass = qlo <= qv && qv <= qhi;
        let (v0, av0) = row_value(pr, d);
        let v: i128 = if pass { v0 } else { 0 };
        let av: i128 = if pass { av0 } else { 0 };
        if acc.mass > i128::MAX - av {
            return false;
        }
        let ghost old_acc = *acc;
        acc.sum = acc.sum + v;
        acc.mass = acc.mass + av;
        acc.any = acc.any || pass;
        proof {
            lemma_lq(lp, ps, ai, q as int);
            assert(lq(lp, ps, ai, q as int) == pass);
            assert(lv(lp, q as int) == v0);
            lemma_isum_step(mf(lp, ps, 0, ai, mq@), 0, t as int);
            lemma_isum_step(mf(lp, ps, 1, ai, mq@), 0, t as int);
            lemma_isum_step(mf(lp, ps, 2, ai, mq@), 0, t as int);
            lemma_acc_add(old_acc, c0, c1, c2, pass, v0 as int, *acc);
        }
        t = t + 1;
    }
    true
}

/// Part `b + i` of a batch: its accumulators are the sums over its directory range.
proof fn lemma_batch_part(lp: Seq<PartView>, pp: Seq<PartView>, ps: Seq<Literal>, pc: Piece, b: int, i: int, o0: int, o1: int)
    requires
        lp_ok(lp), lsi::has_idx(lp),
        piece_ok(pc, pp, ps),
        pc.p0 <= b + i < pc.p1,
        dir_range(lp, part_key(pp, b + i), o0, o1),
    ensures
        pt(lp, pp, ps, 0)(b + i) == isum(mt(lp, ps, 0, pc.a as int), o0, o1),
        pt(lp, pp, ps, 1)(b + i) == isum(mt(lp, ps, 1, pc.a as int), o0, o1),
        pt(lp, pp, ps, 2)(b + i) == isum(mt(lp, ps, 2, pc.a as int), o0, o1),
{
    let p = b + i;
    lemma_prow(pp, p);
    let z = prows(pp)[p];
    assert(arm_is(pp, ps, p, pc.a as int));
    lemma_part_sum(lp, ps, 0, z, pc.a as int, o0, o1);
    lemma_part_sum(lp, ps, 1, z, pc.a as int, o0, o1);
    lemma_part_sum(lp, ps, 2, z, pc.a as int, o0, o1);
}

/// Adds the parts at positions `pc.p0 .. pc.p1` of the part index in batches; `false` when the mass would exceed
/// `i128::MAX`.
fn add_range(p: &PIdx, l: &LIdx, qual: &Vec<bool>, pc: Piece, qlo: i64, qhi: i64, acc: &mut Acc,
    lo: &mut Vec<u32>, hi: &mut Vec<u32>, starts: &mut Vec<u32>, mq: &mut Vec<u32>,
    Ghost(pp): Ghost<Seq<PartView>>, Ghost(lp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>,
    Ghost(c): Ghost<(int, int, int)>) -> (ok: bool)
    requires
        pidx_ok(*p, pp), lidx_ok(*l, lp), qual_ok(qual@, lp),
        piece_ok(pc, pp, ps),
        qlo == 100 * qty_p(ps, pc.a as int), qhi == 100 * (qty_p(ps, pc.a as int) + 10),
        old(lo)@.len() == BATCH, old(hi)@.len() == BATCH, old(starts)@.len() == BATCH + 1, old(mq)@.len() == MCAP + 1,
        acc_rel(*old(acc), c.0, c.1, c.2),
    ensures
        final(lo)@.len() == BATCH, final(hi)@.len() == BATCH, final(starts)@.len() == BATCH + 1, final(mq)@.len() == MCAP + 1,
        ok ==> acc_rel(*final(acc), c.0 + isum(pt(lp, pp, ps, 0), pc.p0 as int, pc.p1 as int),
            c.1 + isum(pt(lp, pp, ps, 1), pc.p0 as int, pc.p1 as int),
            c.2 + isum(pt(lp, pp, ps, 2), pc.p0 as int, pc.p1 as int)),
    no_unwind
{
    let ghost ai = pc.a as int;
    let a = pc.a;
    let p1 = pc.p1;
    let mut b = pc.p0;
    while b < p1
        invariant
            pidx_ok(*p, pp), lidx_ok(*l, lp), qual_ok(qual@, lp),
            piece_ok(pc, pp, ps), a == pc.a, ai == a, p1 == pc.p1,
            qlo == 100 * qty_p(ps, ai), qhi == 100 * (qty_p(ps, ai) + 10),
            lo@.len() == BATCH, hi@.len() == BATCH, starts@.len() == BATCH + 1, mq@.len() == MCAP + 1,
            pc.p0 <= b <= p1,
            acc_rel(*acc, c.0 + isum(pt(lp, pp, ps, 0), pc.p0 as int, b as int),
                c.1 + isum(pt(lp, pp, ps, 1), pc.p0 as int, b as int),
                c.2 + isum(pt(lp, pp, ps, 2), pc.p0 as int, b as int)),
        decreases p1 - b,
    {
        let be = if p1 - b > BATCH { b + BATCH } else { p1 };
        let cnt = be - b;
        let ghost c0 = c.0 + isum(pt(lp, pp, ps, 0), pc.p0 as int, b as int);
        let ghost c1 = c.1 + isum(pt(lp, pp, ps, 1), pc.p0 as int, b as int);
        let ghost c2 = c.2 + isum(pt(lp, pp, ps, 2), pc.p0 as int, b as int);
        stage_a(p, l, b, cnt, lo, hi, Ghost(pp), Ghost(lp));
        proof {
            assert forall|i: int| 0 <= i < cnt implies #[trigger] lo@[i] <= hi@[i] <= n_l(lp) by {
                assert(range_at(lp, pp, b as int, lo@, hi@, i));
            }
            assert forall|i: int| 0 <= i < cnt implies
                #[trigger] pt(lp, pp, ps, 0)(b + i) == isum(mt(lp, ps, 0, ai), lo@[i] as int, hi@[i] as int)
                && pt(lp, pp, ps, 1)(b + i) == isum(mt(lp, ps, 1, ai), lo@[i] as int, hi@[i] as int)
                && pt(lp, pp, ps, 2)(b + i) == isum(mt(lp, ps, 2, ai), lo@[i] as int, hi@[i] as int) by {
                assert(range_at(lp, pp, b as int, lo@, hi@, i));
                lemma_batch_part(lp, pp, ps, pc, b as int, i, lo@[i] as int, hi@[i] as int);
            }
            lemma_isum_split(pt(lp, pp, ps, 0), pc.p0 as int, b as int, be as int);
            lemma_isum_split(pt(lp, pp, ps, 1), pc.p0 as int, b as int, be as int);
            lemma_isum_split(pt(lp, pp, ps, 2), pc.p0 as int, b as int, be as int);
        }
        match stage_b(l, qual, cnt, lo, hi, starts, mq, Ghost(lp), Ghost(ps), Ghost(ai)) {
            Some(m) => {
                proof {
                    let st = starts@;
                    assert forall|i: int| 0 <= i < cnt implies #[trigger] st[i] <= st[i + 1] by {
                        assert(part_done(lp, ps, ai, mq@, st, lo@, hi@, i));
                    }
                    assert forall|i: int| 0 <= i < cnt implies
                        #[trigger] isum(mf(lp, ps, 0, ai, mq@), st[i] as int, st[i + 1] as int) == pt(lp, pp, ps, 0)(b + i) by {
                        assert(part_done(lp, ps, ai, mq@, st, lo@, hi@, i));
                        assert(pt(lp, pp, ps, 0)(b + i) == isum(mt(lp, ps, 0, ai), lo@[i] as int, hi@[i] as int));
                    }
                    assert forall|i: int| 0 <= i < cnt implies
                        #[trigger] isum(mf(lp, ps, 1, ai, mq@), st[i] as int, st[i + 1] as int) == pt(lp, pp, ps, 1)(b + i) by {
                        assert(part_done(lp, ps, ai, mq@, st, lo@, hi@, i));
                        assert(pt(lp, pp, ps, 1)(b + i) == isum(mt(lp, ps, 1, ai), lo@[i] as int, hi@[i] as int));
                    }
                    assert forall|i: int| 0 <= i < cnt implies
                        #[trigger] isum(mf(lp, ps, 2, ai, mq@), st[i] as int, st[i + 1] as int) == pt(lp, pp, ps, 2)(b + i) by {
                        assert(part_done(lp, ps, ai, mq@, st, lo@, hi@, i));
                        assert(pt(lp, pp, ps, 2)(b + i) == isum(mt(lp, ps, 2, ai), lo@[i] as int, hi@[i] as int));
                    }
                    lemma_isum_regroup(mf(lp, ps, 0, ai, mq@), pt(lp, pp, ps, 0), st, b as int, cnt as int);
                    lemma_isum_regroup(mf(lp, ps, 1, ai, mq@), pt(lp, pp, ps, 1), st, b as int, cnt as int);
                    lemma_isum_regroup(mf(lp, ps, 2, ai, mq@), pt(lp, pp, ps, 2), st, b as int, cnt as int);
                }
                if !stage_c(l, mq, m, a, qlo, qhi, acc, Ghost(lp), Ghost(ps), Ghost((c0, c1, c2))) {
                    return false;
                }
            },
            None => {
                // a full buffer: the batch part by part
                let mut i: usize = 0;
                while i < cnt
                    invariant
                        lidx_ok(*l, lp), qual_ok(qual@, lp), a < 3, ai == a,
                        qlo == 100 * qty_p(ps, ai), qhi == 100 * (qty_p(ps, ai) + 10),
                        lo@.len() == BATCH, hi@.len() == BATCH, starts@.len() == BATCH + 1, mq@.len() == MCAP + 1,
                        cnt <= BATCH, i <= cnt,
                        forall|i2: int| 0 <= i2 < cnt ==> #[trigger] lo@[i2] <= hi@[i2] <= n_l(lp),
                        forall|i2: int| 0 <= i2 < cnt ==>
                            #[trigger] pt(lp, pp, ps, 0)(b + i2) == isum(mt(lp, ps, 0, ai), lo@[i2] as int, hi@[i2] as int)
                            && pt(lp, pp, ps, 1)(b + i2) == isum(mt(lp, ps, 1, ai), lo@[i2] as int, hi@[i2] as int)
                            && pt(lp, pp, ps, 2)(b + i2) == isum(mt(lp, ps, 2, ai), lo@[i2] as int, hi@[i2] as int),
                        acc_rel(*acc, c0 + isum(pt(lp, pp, ps, 0), b as int, b + i), c1 + isum(pt(lp, pp, ps, 1), b as int, b + i),
                            c2 + isum(pt(lp, pp, ps, 2), b as int, b + i)),
                    decreases cnt - i,
                {
                    let ghost d0 = c0 + isum(pt(lp, pp, ps, 0), b as int, b + i);
                    let ghost d1 = c1 + isum(pt(lp, pp, ps, 1), b as int, b + i);
                    let ghost d2 = c2 + isum(pt(lp, pp, ps, 2), b as int, b + i);
                    proof {
                        assert(lo@[i as int] <= hi@[i as int] <= n_l(lp));
                        assert(pt(lp, pp, ps, 0)(b + i) == isum(mt(lp, ps, 0, ai), lo@[i as int] as int, hi@[i as int] as int));
                        lemma_isum_step(pt(lp, pp, ps, 0), b as int, b + i);
                        lemma_isum_step(pt(lp, pp, ps, 1), b as int, b + i);
                        lemma_isum_step(pt(lp, pp, ps, 2), b as int, b + i);
                    }
                    if !add_span(l, qual, lo[i] as usize, hi[i] as usize, a, qlo, qhi, acc, Ghost(lp), Ghost(ps), Ghost((d0, d1, d2))) {
                        return false;
                    }
                    i = i + 1;
                }
            },
        }
        b = be;
    }
    true
}

// ------------------------------------------------------------------------------------------------ tasks

/// One worker's run of pieces.
pub struct IxTask {
    pub p: PIdx,
    pub l: LIdx,
    pub qual: Vec<bool>,
    pub pieces: Vec<Piece>,
    pub qlo: Vec<i64>,
    pub qhi: Vec<i64>,
    pub lo: Vec<u32>,
    pub hi: Vec<u32>,
    pub starts: Vec<u32>,
    pub mq: Vec<u32>,
    pub pp: Ghost<Seq<PartView>>,
    pub lp: Ghost<Seq<PartView>>,
    pub ps: Ghost<Seq<Literal>>,
}

/// Accumulator `k` of the pieces `i0 .. i1`.
pub open spec fn psum(lp: Seq<PartView>, pp: Seq<PartView>, ps: Seq<Literal>, k: int, pcs: Seq<Piece>, i0: int, i1: int) -> int {
    isum(pv(lp, pp, ps, k, pcs), i0, i1)
}

pub open spec fn ix_pre(t: IxTask) -> bool {
    let (pp, lp, ps) = (t.pp@, t.lp@, t.ps@);
    &&& pidx_ok(t.p, pp)
    &&& lidx_ok(t.l, lp)
    &&& qual_ok(t.qual@, lp)
    &&& arms_ok(t.qlo@, t.qhi@, ps)
    &&& t.lo@.len() == BATCH && t.hi@.len() == BATCH && t.starts@.len() == BATCH + 1 && t.mq@.len() == MCAP + 1
    &&& forall|i: int| 0 <= i < t.pieces@.len() ==> #[trigger] piece_ok(t.pieces@[i], pp, ps)
}

pub open spec fn ix_post(t: IxTask, out: Option<Acc>) -> bool {
    out matches Some(acc) ==> acc_rel(acc, psum(t.lp@, t.pp@, t.ps@, 0, t.pieces@, 0, t.pieces@.len() as int),
        psum(t.lp@, t.pp@, t.ps@, 1, t.pieces@, 0, t.pieces@.len() as int),
        psum(t.lp@, t.pp@, t.ps@, 2, t.pieces@, 0, t.pieces@.len() as int))
}

impl WorkerTask for IxTask {
    type Output = Option<Acc>;

    open spec fn pre(&self) -> bool {
        ix_pre(*self)
    }

    open spec fn post(&self, out: Option<Acc>) -> bool {
        ix_post(*self, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        if self.pieces.len() == 0 {
            (0, 0)
        } else {
            (self.pieces[0].p0 as u64, self.pieces[self.pieces.len() - 1].p1 as u64)
        }
    }

    fn run(self) -> (out: Option<Acc>) {
        let ghost (pp, lp, ps) = (self.pp@, self.lp@, self.ps@);
        let ghost pcs = self.pieces@;
        let mut lo = self.lo;
        let mut hi = self.hi;
        let mut starts = self.starts;
        let mut mq = self.mq;
        let mut acc = Acc { sum: 0, mass: 0, any: false };
        let np = self.pieces.len();
        let mut i: usize = 0;
        while i < np
            invariant
                pidx_ok(self.p, pp), lidx_ok(self.l, lp), qual_ok(self.qual@, lp), arms_ok(self.qlo@, self.qhi@, ps),
                pcs == self.pieces@, np == pcs.len(),
                forall|j: int| 0 <= j < np ==> #[trigger] piece_ok(pcs[j], pp, ps),
                lo@.len() == BATCH, hi@.len() == BATCH, starts@.len() == BATCH + 1, mq@.len() == MCAP + 1,
                i <= np,
                acc_rel(acc, psum(lp, pp, ps, 0, pcs, 0, i as int), psum(lp, pp, ps, 1, pcs, 0, i as int),
                    psum(lp, pp, ps, 2, pcs, 0, i as int)),
            decreases np - i,
        {
            let pc = self.pieces[i];
            proof {
                assert(piece_ok(pc, pp, ps));
                assert(self.qlo@[pc.a as int] == 100 * qty_p(ps, pc.a as int));
                lemma_isum_step(pv(lp, pp, ps, 0, pcs), 0, i as int);
                lemma_isum_step(pv(lp, pp, ps, 1, pcs), 0, i as int);
                lemma_isum_step(pv(lp, pp, ps, 2, pcs), 0, i as int);
            }
            if !add_range(&self.p, &self.l, &self.qual, pc, self.qlo[pc.a], self.qhi[pc.a], &mut acc,
                &mut lo, &mut hi, &mut starts, &mut mq, Ghost(pp), Ghost(lp), Ghost(ps),
                Ghost((psum(lp, pp, ps, 0, pcs, 0, i as int), psum(lp, pp, ps, 1, pcs, 0, i as int), psum(lp, pp, ps, 2, pcs, 0, i as int)))) {
                return None;
            }
            i = i + 1;
        }
        Some(acc)
    }
}

// ------------------------------------------------------------------------------------------------ pieces

/// Appends the pieces of positions `x0 .. x1` (arm `a`), each at most `CHUNK` positions.
fn push_pieces(pieces: &mut Vec<Piece>, x0: usize, x1: usize, a: usize,
    Ghost(lp): Ghost<Seq<PartView>>, Ghost(pp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>)
    requires
        x0 <= x1 <= n_p(pp), a < 3,
        forall|p: int| x0 <= p < x1 ==> #[trigger] arm_is(pp, ps, p, a as int),
        forall|i: int| 0 <= i < old(pieces)@.len() ==> #[trigger] piece_ok(old(pieces)@[i], pp, ps),
    ensures
        forall|i: int| 0 <= i < final(pieces)@.len() ==> #[trigger] piece_ok(final(pieces)@[i], pp, ps),
        psum(lp, pp, ps, 0, final(pieces)@, 0, final(pieces)@.len() as int)
            == psum(lp, pp, ps, 0, old(pieces)@, 0, old(pieces)@.len() as int) + isum(pt(lp, pp, ps, 0), x0 as int, x1 as int),
        psum(lp, pp, ps, 1, final(pieces)@, 0, final(pieces)@.len() as int)
            == psum(lp, pp, ps, 1, old(pieces)@, 0, old(pieces)@.len() as int) + isum(pt(lp, pp, ps, 1), x0 as int, x1 as int),
        psum(lp, pp, ps, 2, final(pieces)@, 0, final(pieces)@.len() as int)
            == psum(lp, pp, ps, 2, old(pieces)@, 0, old(pieces)@.len() as int) + isum(pt(lp, pp, ps, 2), x0 as int, x1 as int),
{
    let ghost pc0 = pieces@;
    let mut cur = x0;
    while cur < x1
        invariant
            x0 <= cur <= x1 <= n_p(pp), a < 3,
            forall|p: int| x0 <= p < x1 ==> #[trigger] arm_is(pp, ps, p, a as int),
            forall|i: int| 0 <= i < pieces@.len() ==> #[trigger] piece_ok(pieces@[i], pp, ps),
            psum(lp, pp, ps, 0, pieces@, 0, pieces@.len() as int) == psum(lp, pp, ps, 0, pc0, 0, pc0.len() as int) + isum(pt(lp, pp, ps, 0), x0 as int, cur as int),
            psum(lp, pp, ps, 1, pieces@, 0, pieces@.len() as int) == psum(lp, pp, ps, 1, pc0, 0, pc0.len() as int) + isum(pt(lp, pp, ps, 1), x0 as int, cur as int),
            psum(lp, pp, ps, 2, pieces@, 0, pieces@.len() as int) == psum(lp, pp, ps, 2, pc0, 0, pc0.len() as int) + isum(pt(lp, pp, ps, 2), x0 as int, cur as int),
        decreases x1 - cur,
    {
        let nx = if x1 - cur > CHUNK { cur + CHUNK } else { x1 };
        let pc = Piece { p0: cur, p1: nx, a };
        let ghost old_p = pieces@;
        pieces.push(pc);
        proof {
            let np = old_p.len() as int;
            assert(pieces@ == old_p.push(pc));
            assert(piece_ok(pc, pp, ps));
            assert forall|i: int| 0 <= i < pieces@.len() implies #[trigger] piece_ok(pieces@[i], pp, ps) by {
                if i < np {
                    assert(pieces@[i] == old_p[i]);
                }
            }
            assert forall|i: int| 0 <= i < np implies #[trigger] pv(lp, pp, ps, 0, old_p)(i) == pv(lp, pp, ps, 0, pieces@)(i) by {
                assert(pieces@[i] == old_p[i]);
            }
            assert forall|i: int| 0 <= i < np implies #[trigger] pv(lp, pp, ps, 1, old_p)(i) == pv(lp, pp, ps, 1, pieces@)(i) by {
                assert(pieces@[i] == old_p[i]);
            }
            assert forall|i: int| 0 <= i < np implies #[trigger] pv(lp, pp, ps, 2, old_p)(i) == pv(lp, pp, ps, 2, pieces@)(i) by {
                assert(pieces@[i] == old_p[i]);
            }
            lemma_isum_ext(pv(lp, pp, ps, 0, old_p), pv(lp, pp, ps, 0, pieces@), 0, np);
            lemma_isum_ext(pv(lp, pp, ps, 1, old_p), pv(lp, pp, ps, 1, pieces@), 0, np);
            lemma_isum_ext(pv(lp, pp, ps, 2, old_p), pv(lp, pp, ps, 2, pieces@), 0, np);
            lemma_isum_step(pv(lp, pp, ps, 0, pieces@), 0, np);
            lemma_isum_step(pv(lp, pp, ps, 1, pieces@), 0, np);
            lemma_isum_step(pv(lp, pp, ps, 2, pieces@), 0, np);
            assert(pieces@[np] == pc);
            lemma_isum_split(pt(lp, pp, ps, 0), x0 as int, cur as int, nx as int);
            lemma_isum_split(pt(lp, pp, ps, 1), x0 as int, cur as int, nx as int);
            lemma_isum_split(pt(lp, pp, ps, 2), x0 as int, cur as int, nx as int);
        }
        cur = nx;
    }
}

/// The arm tables of the part side.
pub struct PartTabs {
    pub carm: Vec<u8>,
    pub bm0: Vec<bool>,
    pub bm1: Vec<bool>,
    pub bm2: Vec<bool>,
}

pub open spec fn tabs_ok(t: PartTabs, pp: Seq<PartView>, ps: Seq<Literal>) -> bool {
    &&& carm_ok(t.carm@, pp)
    &&& bm_ok(t.bm0@, pp, ps, 0)
    &&& bm_ok(t.bm1@, pp, ps, 1)
    &&& bm_ok(t.bm2@, pp, ps, 2)
}

/// The arm of every part row in (brand, container) group `g` with `p_size - smin` in `t0 .. t1`.
proof fn lemma_group_arm(pp: Seq<PartView>, ps: Seq<Literal>, tabs: PartTabs, g: int, t0: int, t1: int, p: int, ca: int, bmatch: bool)
    requires
        pp_ok(pp), pbi::has_idx(pp), tabs_ok(tabs, pp, ps),
        0 <= g < pbi::n_brands(pp) * pbi::n_conts(pp),
        0 <= t0 <= t1 <= pbi::idx_ns(pp),
        0 <= p < n_p(pp),
        pbi::idx_offs(pp)[g * pbi::idx_ns(pp) + t0] <= p < pbi::idx_offs(pp)[g * pbi::idx_ns(pp) + t1],
        ca == tabs.carm@[g % pbi::n_conts(pp)] as int,
        ca < 3 ==> bmatch == (if ca == 0 { tabs.bm0@[g / pbi::n_conts(pp)] } else if ca == 1 { tabs.bm1@[g / pbi::n_conts(pp)] }
            else { tabs.bm2@[g / pbi::n_conts(pp)] }),
    ensures ({
        let sz = pbi::size_at(pp, pbi::prow(pp, p));
        &&& t0 <= sz - pbi::idx_smin(pp) < t1
        &&& prows(pp)[p].len() == 4
        &&& zarm(ps, prows(pp)[p]) == if ca < 3 && bmatch && 1 <= sz <= smax(ca) { ca } else { 3 }
    }),
{
    lemma_zone(pp, g, t0, t1, p);
    let r = pbi::prow(pp, p);
    let nc = pbi::n_conts(pp);
    let (b, c) = (g / nc, g % nc);
    lemma_prow(pp, p);
    assert(pbi::dict_idx_ok(pp, r));
    assert(0 <= c < nc && 0 <= b < pbi::n_brands(pp));
    assert(tabs.carm@[c] <= 3);
    let bt = pbi::b_text(pp, b);
    let ct = pbi::c_text(pp, c);
    if ca < 3 {
        if ca == 0 { assert(tabs.bm0@[b] == (bt == brand_p(ps, 0))); }
        else if ca == 1 { assert(tabs.bm1@[b] == (bt == brand_p(ps, 1))); }
        else { assert(tabs.bm2@[b] == (bt == brand_p(ps, 2))); }
    }
    lemma_arm_of(ps, bt, pbi::size_at(pp, r), ct, ca, bmatch);
}

/// The pieces cover the part index positions `0 .. x`: each is well formed and their accumulators are the sums over
/// those positions.
pub open spec fn pieces_cover(lp: Seq<PartView>, pp: Seq<PartView>, ps: Seq<Literal>, pcs: Seq<Piece>, x: int) -> bool {
    &&& forall|i: int| 0 <= i < pcs.len() ==> #[trigger] piece_ok(pcs[i], pp, ps)
    &&& psum(lp, pp, ps, 0, pcs, 0, pcs.len() as int) == isum(pt(lp, pp, ps, 0), 0, x)
    &&& psum(lp, pp, ps, 1, pcs, 0, pcs.len() as int) == isum(pt(lp, pp, ps, 1), 0, x)
    &&& psum(lp, pp, ps, 2, pcs, 0, pcs.len() as int) == isum(pt(lp, pp, ps, 2), 0, x)
}

/// Parts without an arm on positions `x .. y` extend a cover of `0 .. x` to `0 .. y`.
proof fn lemma_cover_skip(lp: Seq<PartView>, pp: Seq<PartView>, ps: Seq<Literal>, pcs: Seq<Piece>, x: int, y: int)
    requires
        pieces_cover(lp, pp, ps, pcs, x),
        0 <= x <= y,
        forall|q: int| x <= q < y ==> #[trigger] no_arm(pp, ps, q),
    ensures pieces_cover(lp, pp, ps, pcs, y),
{
    lemma_span_zero(lp, pp, ps, 0, x, y);
    lemma_span_zero(lp, pp, ps, 1, x, y);
    lemma_span_zero(lp, pp, ps, 2, x, y);
    lemma_isum_split(pt(lp, pp, ps, 0), 0, x, y);
    lemma_isum_split(pt(lp, pp, ps, 1), 0, x, y);
    lemma_isum_split(pt(lp, pp, ps, 2), 0, x, y);
}

/// The part row at position `q` has `p_size - smin` in `t0 .. t1` and the arm the tables give.
pub open spec fn zone_arm_ok(pp: Seq<PartView>, ps: Seq<Literal>, t0: int, t1: int, ca: int, bmatch: bool, q: int) -> bool {
    let sz = pbi::size_at(pp, pbi::prow(pp, q));
    &&& t0 <= sz - pbi::idx_smin(pp) < t1
    &&& prows(pp)[q].len() == 4
    &&& zarm(ps, prows(pp)[q]) == if ca < 3 && bmatch && 1 <= sz <= smax(ca) { ca } else { 3 }
}

/// The arms of every part row of group `g` whose `p_size - smin` lies in `t0 .. t1` (positions
/// `offs[g * ns + t0] .. offs[g * ns + t1]`).
proof fn lemma_zone_arms(pp: Seq<PartView>, ps: Seq<Literal>, tabs: PartTabs, g: int, t0: int, t1: int, ca: int, bmatch: bool)
    requires
        pp_ok(pp), pbi::has_idx(pp), tabs_ok(tabs, pp, ps),
        0 <= g < pbi::n_brands(pp) * pbi::n_conts(pp),
        0 <= t0 <= t1 <= pbi::idx_ns(pp),
        ca == tabs.carm@[g % pbi::n_conts(pp)] as int,
        ca < 3 ==> bmatch == (if ca == 0 { tabs.bm0@[g / pbi::n_conts(pp)] } else if ca == 1 { tabs.bm1@[g / pbi::n_conts(pp)] }
            else { tabs.bm2@[g / pbi::n_conts(pp)] }),
    ensures
        forall|q: int| pbi::idx_offs(pp)[g * pbi::idx_ns(pp) + t0] <= q < pbi::idx_offs(pp)[g * pbi::idx_ns(pp) + t1]
            ==> #[trigger] zone_arm_ok(pp, ps, t0, t1, ca, bmatch, q),
{
    let ns = pbi::idx_ns(pp);
    let n = n_p(pp);
    assert forall|q: int| pbi::idx_offs(pp)[g * ns + t0] <= q < pbi::idx_offs(pp)[g * ns + t1]
        implies #[trigger] zone_arm_ok(pp, ps, t0, t1, ca, bmatch, q) by {
        assert((g + 1) * ns <= pbi::n_brands(pp) * pbi::n_conts(pp) * ns) by (nonlinear_arith)
            requires g + 1 <= pbi::n_brands(pp) * pbi::n_conts(pp), ns >= 1;
        assert(g * ns + t1 <= (g + 1) * ns) by (nonlinear_arith) requires t1 <= ns;
        assert(0 <= g * ns) by (nonlinear_arith) requires g >= 0, ns >= 1;
        pbi::lemma_offs_mono(pp, n, g * ns + t1, pbi::idx_nkeys(pp));
        assert(pbi::idx_offs(pp)[pbi::idx_nkeys(pp)] <= n);
        assert(0 <= q < n);
        lemma_group_arm(pp, ps, tabs, g, t0, t1, q, ca, bmatch);
        let sz = pbi::size_at(pp, pbi::prow(pp, q));
        assert(t0 <= sz - pbi::idx_smin(pp) < t1);
        assert(prows(pp)[q].len() == 4);
        assert(zarm(ps, prows(pp)[q]) == if ca < 3 && bmatch && 1 <= sz <= smax(ca) { ca } else { 3 });
    }
}

/// The pieces of (brand, container) group `g`: appended to a cover of the positions before the group, they cover
/// the positions through the group.
#[verifier::spinoff_prover]
fn add_group(p: &PIdx, tabs: &PartTabs, pieces: &mut Vec<Piece>, g: usize, Ghost(lp): Ghost<Seq<PartView>>,
    Ghost(pp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>)
    requires
        pidx_ok(*p, pp), tabs_ok(*tabs, pp, ps),
        g < pbi::n_brands(pp) * pbi::n_conts(pp),
        (g + 1) * pbi::idx_ns(pp) <= pbi::idx_nkeys(pp),
        pieces_cover(lp, pp, ps, old(pieces)@, pbi::idx_offs(pp)[g * pbi::idx_ns(pp)] as int),
    ensures
        pieces_cover(lp, pp, ps, final(pieces)@, pbi::idx_offs(pp)[(g + 1) * pbi::idx_ns(pp)] as int),
{
    let ghost n = n_p(pp);
    let ghost (nbi, nci, nsi) = (pbi::n_brands(pp), pbi::n_conts(pp), pbi::idx_ns(pp));
    let ghost offs = pbi::idx_offs(pp);
    let ns = p.ns;
    let nk = p.offs.len() - 1;
    proof {
        assert((g + 1) * nsi == g * nsi + nsi) by (nonlinear_arith);
        assert(0 <= g * nsi) by (nonlinear_arith) requires g >= 0, nsi >= 1;
        assert(nci > 0) by (nonlinear_arith) requires g < nbi * nci, nbi >= 0, nci >= 0;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(g as int, nci);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(g as int, nci);
        vstd::arithmetic::div_mod::lemma_div_pos_is_pos(g as int, nci);
        lemma_div_lt(g as int, nci, nbi);
        assert(offs.len() == pbi::idx_nkeys(pp) + 1);
        assert(p.offs@.len() == offs.len());
    }
    let b = g / p.nc;
    let c = g % p.nc;
    let e0 = g * ns;
    let ca = tabs.carm[c];
    let bmatch = if ca == 0 { tabs.bm0[b] } else if ca == 1 { tabs.bm1[b] } else if ca == 2 { tabs.bm2[b] } else { false };
    let ghost x = offs[e0 as int] as int;
    let ghost y = offs[e0 + nsi] as int;
    proof {
        pbi::lemma_offs_mono(pp, n, e0 as int, e0 + nsi);
        pbi::lemma_offs_mono(pp, n, e0 + nsi, pbi::idx_nkeys(pp));
        assert((g + 1) * nsi == e0 + nsi);
    }
    let smax: i128 = if ca == 0 { 5 } else if ca == 1 { 10 } else { 15 };
    let lo_t: i128 = if 1 - (p.smin as i128) > 0 { 1 - (p.smin as i128) } else { 0 };
    let hi_t: i128 = if smax - (p.smin as i128) < (ns as i128) - 1 { smax - (p.smin as i128) } else { (ns as i128) - 1 };
    if ca < 3 && bmatch && lo_t <= hi_t {
        let x0 = p.offs[e0 + lo_t as usize] as usize;
        let x1 = p.offs[e0 + hi_t as usize + 1] as usize;
        proof {
            let (t0, t1) = (lo_t as int, hi_t as int + 1);
            pbi::lemma_offs_mono(pp, n, e0 as int, e0 + t0);
            pbi::lemma_offs_mono(pp, n, e0 + t0, e0 + t1);
            pbi::lemma_offs_mono(pp, n, e0 + t1, e0 + nsi);
            lemma_zone_arms(pp, ps, *tabs, g as int, 0, t0, ca as int, bmatch);
            lemma_zone_arms(pp, ps, *tabs, g as int, t0, t1, ca as int, bmatch);
            assert forall|q: int| x <= q < x0 implies #[trigger] no_arm(pp, ps, q) by {
                assert(zone_arm_ok(pp, ps, 0, t0, ca as int, bmatch, q));
            }
            assert forall|q: int| x0 <= q < x1 implies #[trigger] arm_is(pp, ps, q, ca as int) by {
                assert(zone_arm_ok(pp, ps, t0, t1, ca as int, bmatch, q));
            }
            lemma_cover_skip(lp, pp, ps, pieces@, x, x0 as int);
        }
        push_pieces(pieces, x0, x1, ca as usize, Ghost(lp), Ghost(pp), Ghost(ps));
        proof {
            let (t1) = (hi_t as int + 1);
            lemma_isum_split(pt(lp, pp, ps, 0), 0, x0 as int, x1 as int);
            lemma_isum_split(pt(lp, pp, ps, 1), 0, x0 as int, x1 as int);
            lemma_isum_split(pt(lp, pp, ps, 2), 0, x0 as int, x1 as int);
            assert(pieces_cover(lp, pp, ps, pieces@, x1 as int));
            lemma_zone_arms(pp, ps, *tabs, g as int, t1, nsi, ca as int, bmatch);
            assert forall|q: int| x1 <= q < y implies #[trigger] no_arm(pp, ps, q) by {
                assert(zone_arm_ok(pp, ps, t1, nsi, ca as int, bmatch, q));
            }
            lemma_cover_skip(lp, pp, ps, pieces@, x1 as int, y);
        }
    } else {
        proof {
            lemma_zone_arms(pp, ps, *tabs, g as int, 0, nsi, ca as int, bmatch);
            assert forall|q: int| x <= q < y implies #[trigger] no_arm(pp, ps, q) by {
                assert(zone_arm_ok(pp, ps, 0, nsi, ca as int, bmatch, q));
            }
            lemma_cover_skip(lp, pp, ps, pieces@, x, y);
        }
    }
}

/// The pieces of every part index position whose part row has an arm; their accumulators are the totals over all
/// positions.
fn make_pieces(p: &PIdx, tabs: &PartTabs, Ghost(lp): Ghost<Seq<PartView>>, Ghost(pp): Ghost<Seq<PartView>>,
    Ghost(ps): Ghost<Seq<Literal>>) -> (pieces: Vec<Piece>)
    requires pidx_ok(*p, pp), tabs_ok(*tabs, pp, ps),
    ensures pieces_cover(lp, pp, ps, pieces@, n_p(pp)),
{
    let ghost n = n_p(pp);
    let ghost (nbi, nci, nsi) = (pbi::n_brands(pp), pbi::n_conts(pp), pbi::idx_ns(pp));
    let ghost offs = pbi::idx_offs(pp);
    let nk = p.offs.len() - 1;
    proof {
        assert(nbi * nci <= nbi * nci * nsi) by (nonlinear_arith) requires nbi >= 0, nci >= 0, nsi >= 1;
        assert(nk as int == nbi * nci * nsi);
    }
    let ng = p.nb * p.nc;
    let mut pieces: Vec<Piece> = Vec::new();
    let mut g: usize = 0;
    proof {
        assert(0 * nsi == 0);
        // offs[0] == 0: position 0 lies at or after its entry's start
        pbi::lemma_offs_mono(pp, n, 0, pbi::idx_nkeys(pp));
        if n > 0 {
            assert(pbi::in_entry(pp, 0));
            pbi::lemma_offs_mono(pp, n, 0, pbi::comp_at(pp, pbi::prow(pp, 0)));
        }
        assert(offs[0] == 0);
        lemma_isum_empty(pt(lp, pp, ps, 0), 0);
        lemma_isum_empty(pt(lp, pp, ps, 1), 0);
        lemma_isum_empty(pt(lp, pp, ps, 2), 0);
    }
    while g < ng
        invariant
            pidx_ok(*p, pp), tabs_ok(*tabs, pp, ps),
            n == n_p(pp), nbi == pbi::n_brands(pp), nci == pbi::n_conts(pp), nsi == pbi::idx_ns(pp), offs == pbi::idx_offs(pp),
            ng == nbi * nci, nk == nbi * nci * nsi, nk == pbi::idx_nkeys(pp),
            g <= ng,
            pieces_cover(lp, pp, ps, pieces@, offs[g * nsi] as int),
        decreases ng - g,
    {
        proof {
            assert((g + 1) * nsi <= nbi * nci * nsi) by (nonlinear_arith) requires g + 1 <= nbi * nci, nsi >= 1;
        }
        add_group(p, tabs, &mut pieces, g, Ghost(lp), Ghost(pp), Ghost(ps));
        g = g + 1;
    }
    proof {
        assert(g == nbi * nci);
        assert(g * nsi == nk);
        // every position lies before the last offset
        if n > 0 {
            assert(pbi::in_entry(pp, n - 1));
            pbi::lemma_offs_mono(pp, n, pbi::comp_at(pp, pbi::prow(pp, n - 1)) + 1, nk as int);
        }
        assert(offs[nk as int] == n);
    }
    pieces
}

// ------------------------------------------------------------------------------------------------ the plan

/// Task `tk` (number `t`) adds the pieces `cut[t] .. cut[t + 1]` of `pcs` over the given parts and binding.
pub open spec fn task_cut(tk: IxTask, lp: Seq<PartView>, pp: Seq<PartView>, ps: Seq<Literal>, cut: Seq<int>, pcs: Seq<Piece>, t: int) -> bool {
    &&& tk.lp@ == lp && tk.pp@ == pp && tk.ps@ == ps
    &&& 0 <= cut[t] <= cut[t + 1] <= pcs.len()
    &&& tk.pieces@ == pcs.subrange(cut[t], cut[t + 1])
}

/// Task `tk` is ready to run and adds the pieces `cut[t] .. cut[t + 1]`.
pub open spec fn task_ok(tk: IxTask, lp: Seq<PartView>, pp: Seq<PartView>, ps: Seq<Literal>, cut: Seq<int>, pcs: Seq<Piece>, t: int) -> bool {
    tk.pre() && task_cut(tk, lp, pp, ps, cut, pcs, t)
}

/// The pieces `lo_c .. hi_c` as a sequence of their own: the same sums.
proof fn lemma_cut_sum(lp: Seq<PartView>, pp: Seq<PartView>, ps: Seq<Literal>, pcs: Seq<Piece>, lo_c: int, hi_c: int)
    requires 0 <= lo_c <= hi_c <= pcs.len(),
    ensures
        psum(lp, pp, ps, 0, pcs.subrange(lo_c, hi_c), 0, hi_c - lo_c) == isum(pv(lp, pp, ps, 0, pcs), lo_c, hi_c),
        psum(lp, pp, ps, 1, pcs.subrange(lo_c, hi_c), 0, hi_c - lo_c) == isum(pv(lp, pp, ps, 1, pcs), lo_c, hi_c),
        psum(lp, pp, ps, 2, pcs.subrange(lo_c, hi_c), 0, hi_c - lo_c) == isum(pv(lp, pp, ps, 2, pcs), lo_c, hi_c),
{
    let sub = pcs.subrange(lo_c, hi_c);
    let len = hi_c - lo_c;
    assert forall|i: int| 0 <= i < len implies #[trigger] pv(lp, pp, ps, 0, sub)(i) == pv(lp, pp, ps, 0, pcs)(lo_c + i) by {
        assert(sub[i] == pcs[lo_c + i]);
    }
    assert forall|i: int| 0 <= i < len implies #[trigger] pv(lp, pp, ps, 1, sub)(i) == pv(lp, pp, ps, 1, pcs)(lo_c + i) by {
        assert(sub[i] == pcs[lo_c + i]);
    }
    assert forall|i: int| 0 <= i < len implies #[trigger] pv(lp, pp, ps, 2, sub)(i) == pv(lp, pp, ps, 2, pcs)(lo_c + i) by {
        assert(sub[i] == pcs[lo_c + i]);
    }
    lemma_isum_shift(pv(lp, pp, ps, 0, sub), pv(lp, pp, ps, 0, pcs), lo_c, len);
    lemma_isum_shift(pv(lp, pp, ps, 1, sub), pv(lp, pp, ps, 1, pcs), lo_c, len);
    lemma_isum_shift(pv(lp, pp, ps, 2, sub), pv(lp, pp, ps, 2, pcs), lo_c, len);
}

/// A copy of a vector of flags.
fn copy_flags(v: &Vec<bool>) -> (r: Vec<bool>)
    ensures r@ == v@,
{
    let mut r: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v@.len(), r@ == v@.subrange(0, i as int),
        decreases v@.len() - i,
    {
        r.push(v[i]);
        proof {
            assert(r@ =~= v@.subrange(0, i + 1));
        }
        i = i + 1;
    }
    proof {
        assert(r@ =~= v@);
    }
    r
}

/// The tasks' accumulators added in task order: `None` when the mass would exceed `i128::MAX` or a task gave up.
fn merge_tasks(outs: &Vec<Option<Acc>>, Ghost(tv): Ghost<Seq<IxTask>>, Ghost(cut): Ghost<Seq<int>>,
    Ghost(lp): Ghost<Seq<PartView>>, Ghost(pp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(pcs): Ghost<Seq<Piece>>)
    -> (r: Option<Acc>)
    requires
        outs@.len() == tv.len(), cut.len() == tv.len() + 1, cut[0] == 0,
        forall|t: int| 0 <= t < tv.len() ==> #[trigger] ix_post(tv[t], outs@[t]),
        forall|t: int| 0 <= t < tv.len() ==> #[trigger] task_cut(tv[t], lp, pp, ps, cut, pcs, t),
    ensures
        r matches Some(acc) ==> acc_rel(acc, psum(lp, pp, ps, 0, pcs, 0, cut[tv.len() as int]),
            psum(lp, pp, ps, 1, pcs, 0, cut[tv.len() as int]), psum(lp, pp, ps, 2, pcs, 0, cut[tv.len() as int])),
{
    let mut acc = Acc { sum: 0, mass: 0, any: false };
    let nt = outs.len();
    let mut t: usize = 0;
    while t < nt
        invariant
            nt == outs@.len(), outs@.len() == tv.len(), cut.len() == tv.len() + 1, cut[0] == 0,
            forall|t2: int| 0 <= t2 < tv.len() ==> #[trigger] ix_post(tv[t2], outs@[t2]),
            forall|t2: int| 0 <= t2 < tv.len() ==> #[trigger] task_cut(tv[t2], lp, pp, ps, cut, pcs, t2),
            t <= nt,
            acc_rel(acc, psum(lp, pp, ps, 0, pcs, 0, cut[t as int]), psum(lp, pp, ps, 1, pcs, 0, cut[t as int]),
                psum(lp, pp, ps, 2, pcs, 0, cut[t as int])),
        decreases nt - t,
    {
        let o = outs[t];
        match o {
            None => {
                return None;
            },
            Some(x) => {
                let ghost tk = tv[t as int];
                let ghost (lo_c, hi_c) = (cut[t as int], cut[t + 1]);
                proof {
                    assert(ix_post(tk, outs@[t as int]));
                    let sub = pcs.subrange(lo_c, hi_c);
                    assert(task_cut(tk, lp, pp, ps, cut, pcs, t as int));
                    assert(tk.pieces@ == sub);
                    lemma_cut_sum(lp, pp, ps, pcs, lo_c, hi_c);
                    lemma_isum_split(pv(lp, pp, ps, 0, pcs), 0, lo_c, hi_c);
                    lemma_isum_split(pv(lp, pp, ps, 1, pcs), 0, lo_c, hi_c);
                    lemma_isum_split(pv(lp, pp, ps, 2, pcs), 0, lo_c, hi_c);
                }
                if acc.mass > i128::MAX - x.mass {
                    return None;
                }
                acc = Acc { sum: acc.sum + x.sum, mass: acc.mass + x.mass, any: acc.any || x.any };
            },
        }
        t = t + 1;
    }
    Some(acc)
}

/// The index plan when both indexes are present: `Some(acc)` with the accumulators over every part index
/// position, or `None` (absent index, or a mass beyond `i128::MAX`): the caller then runs the incumbent plan.
pub fn index_plan(pst: &mut StoredParts, lst: &mut StoredParts, b0: &[u8], q0: i64, b1: &[u8], q1: i64, b2: &[u8], q2: i64,
    workers: usize, dispatch: &mut Dispatch,
    Ghost(pp): Ghost<Seq<PartView>>, Ghost(lp): Ghost<Seq<PartView>>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Option<Acc>)
    requires
        old(pst)@ == pp, old(lst)@ == lp,
        pp_ok(pp), lp_ok(lp),
        b0@ == brand_p(ps, 0), b1@ == brand_p(ps, 1), b2@ == brand_p(ps, 2),
        q0 as int == qty_p(ps, 0), q1 as int == qty_p(ps, 1), q2 as int == qty_p(ps, 2),
        -2147483648 <= q0 <= 2147483637, -2147483648 <= q1 <= 2147483637, -2147483648 <= q2 <= 2147483637,
        1 <= workers <= MAX_WORKERS,
    ensures
        final(pst)@ == pp, final(lst)@ == lp,
        r matches Some(acc) ==> pbi::has_idx(pp) && lsi::has_idx(lp) && acc_rel(acc, rsum(lp, pp, ps, 0, 0, n_p(pp)),
            rsum(lp, pp, ps, 1, 0, n_p(pp)), rsum(lp, pp, ps, 2, 0, n_p(pp))),
{
    let pmeta = pst.extent_i64(pbi::IDX_META, 0, 3);
    let lmeta = lst.extent_i64(lsi::IDX_META, 0, 2);
    if pmeta[0] != pbi::MODE_INDEX || lmeta[0] != lsi::MODE_INDEX {
        return None;
    }
    proof {
        assert(pbi::has_idx(pp));
        assert(lsi::has_idx(lp));
    }
    // part side
    let nbo0 = pst.part_len(pbi::PA_BRAND_DOFFS);
    let nco0 = pst.part_len(pbi::PA_CONT_DOFFS);
    if nbo0 < 2 || nco0 < 2 {
        return None;
    }
    let pn = pst.part_len(pbi::PA_PARTKEY_CODES);
    let play = pst.extent_u64(pbi::PA_LAYOUT, 0, 2);
    let nbo = pst.part_len(pbi::PA_BRAND_DOFFS);
    let nco = pst.part_len(pbi::PA_CONT_DOFFS);
    let bo = pst.extent_u64(pbi::PA_BRAND_DOFFS, 0, nbo);
    let nby = pst.part_len(pbi::PA_BRAND_DBYTES);
    let by = pst.extent_u8(pbi::PA_BRAND_DBYTES, 0, nby);
    let co = pst.extent_u64(pbi::PA_CONT_DOFFS, 0, nco);
    let ncy = pst.part_len(pbi::PA_CONT_DBYTES);
    let cy = pst.extent_u8(pbi::PA_CONT_DBYTES, 0, ncy);
    let nkb = pst.part_len(pbi::PA_PARTKEY_BASE);
    let npo = pst.part_len(pbi::IDX_OFFS);
    let poffs = pst.extent_u32(pbi::IDX_OFFS, 0, npo);
    let pperm = pst.extent_u32(pbi::IDX_PERM, 0, pn);
    let kc = pst.extent_u32(pbi::PA_PARTKEY_CODES, 0, pn);
    let kb = pst.extent_i64(pbi::PA_PARTKEY_BASE, 0, nkb);
    proof {
        assert(pn as int == n_p(pp));
        assert(bo@ =~= pbi::b_offs(pp));
        assert(by@ =~= pbi::b_bytes(pp));
        assert(co@ =~= pbi::c_offs(pp));
        assert(cy@ =~= pbi::c_bytes(pp));
        assert(poffs@ =~= pbi::idx_offs(pp));
        assert(pperm@ =~= pbi::idx_perm(pp));
        assert(kc@ =~= pbi::u32s(pp[pbi::PA_PARTKEY_CODES as int]));
        assert(kb@ =~= pbi::i64s(pp[pbi::PA_PARTKEY_BASE as int]));
        assert(pmeta@[1] == pbi::idx_smin(pp) && pmeta@[2] == pbi::idx_ns(pp));
        let (nbi, nci, nsi) = (pbi::n_brands(pp), pbi::n_conts(pp), pbi::idx_ns(pp));
        assert(nbi >= 1 && nci >= 1);
        assert(nsi <= nbi * nci * nsi) by (nonlinear_arith) requires nsi >= 1, nbi >= 1, nci >= 1;
        assert(npo as int == nbi * nci * nsi + 1);
        assert(pmeta@[2] as int <= npo);
    }
    let p = PIdx {
        smin: pmeta[1],
        ns: pmeta[2] as usize,
        nb: nbo - 1,
        nc: nco - 1,
        offs: poffs,
        perm: pperm,
        kc,
        kb,
        dv: Divisor::new(play[1]),
    };
    // lineitem side
    let ln = lst.part_len(lsi::LI_QUANTITY_CODES);
    let llay = lst.extent_u64(lsi::LI_LAYOUT, 0, 2);
    let nlo = lst.part_len(lsi::IDX_OFFS);
    let loffs = lst.extent_u32(lsi::IDX_OFFS, 0, nlo);
    let lrows_ = lst.extent_u32(lsi::IDX_ROWS, 0, ln);
    let lship = lst.extent_u8(lsi::IDX_SHIP, 0, ln);
    let qc = lst.extent_u16(lsi::LI_QUANTITY_CODES, 0, ln);
    let nqb = lst.part_len(lsi::LI_QUANTITY_BASE);
    let qb = lst.extent_i64(lsi::LI_QUANTITY_BASE, 0, nqb);
    let pc = lst.extent_u32(lsi::LI_PRICE_CODES, 0, ln);
    let npb = lst.part_len(lsi::LI_PRICE_BASE);
    let pb = lst.extent_i64(lsi::LI_PRICE_BASE, 0, npb);
    let dc = lst.extent_u8(lsi::LI_DISCOUNT_CODES, 0, ln);
    let ndb = lst.part_len(lsi::LI_DISCOUNT_BASE);
    let db = lst.extent_i64(lsi::LI_DISCOUNT_BASE, 0, ndb);
    let nso = lst.part_len(lsi::LI_SI_DOFFS);
    let so = lst.extent_u64(lsi::LI_SI_DOFFS, 0, nso);
    let nsy = lst.part_len(lsi::LI_SI_DBYTES);
    let sy = lst.extent_u8(lsi::LI_SI_DBYTES, 0, nsy);
    let nmo = lst.part_len(lsi::LI_SM_DOFFS);
    let mo = lst.extent_u64(lsi::LI_SM_DOFFS, 0, nmo);
    let nmy = lst.part_len(lsi::LI_SM_DBYTES);
    let my = lst.extent_u8(lsi::LI_SM_DBYTES, 0, nmy);
    proof {
        assert(ln as int == n_l(lp));
        assert(loffs@ =~= lsi::idx_offs(lp));
        assert(lrows_@ =~= lsi::idx_rows(lp));
        assert(lship@ =~= lsi::idx_ship(lp));
        assert(qc@ =~= lsi::u16s(lp[lsi::LI_QUANTITY_CODES as int]));
        assert(qb@ =~= lsi::i64s(lp[lsi::LI_QUANTITY_BASE as int]));
        assert(pc@ =~= lsi::u32s(lp[lsi::LI_PRICE_CODES as int]));
        assert(pb@ =~= lsi::i64s(lp[lsi::LI_PRICE_BASE as int]));
        assert(dc@ =~= lsi::u8s(lp[lsi::LI_DISCOUNT_CODES as int]));
        assert(db@ =~= lsi::i64s(lp[lsi::LI_DISCOUNT_BASE as int]));
        assert(so@ =~= lsi::si_offs(lp));
        assert(sy@ =~= lsi::si_bytes(lp));
        assert(mo@ =~= lsi::sm_offs(lp));
        assert(my@ =~= lsi::sm_bytes(lp));
    }
    let l = LIdx {
        kmin: lmeta[1],
        nk: nlo - 1,
        offs: loffs,
        rows: lrows_,
        ship: lship,
        qc,
        qb,
        pc,
        pb,
        dc,
        db,
        dv: Divisor::new(llay[1]),
    };
    proof {
        assert(pidx_ok(p, pp));
        assert(lidx_ok(l, lp));
    }
    let qual = ship_table(so, sy, mo, my, Ghost(lp));
    let tabs = PartTabs {
        carm: cont_table(co, cy, Ghost(pp)),
        bm0: brand_table(bo, by, b0, Ghost(pp), Ghost(ps), Ghost(0)),
        bm1: brand_table(bo, by, b1, Ghost(pp), Ghost(ps), Ghost(1)),
        bm2: brand_table(bo, by, b2, Ghost(pp), Ghost(ps), Ghost(2)),
    };
    let pieces = make_pieces(&p, &tabs, Ghost(lp), Ghost(pp), Ghost(ps));
    let ghost pcs = pieces@;
    let qlo: Vec<i64> = vec![100 * q0, 100 * q1, 100 * q2];
    let qhi: Vec<i64> = vec![100 * (q0 + 10), 100 * (q1 + 10), 100 * (q2 + 10)];
    proof {
        assert(arms_ok(qlo@, qhi@, ps)) by {
            assert forall|a: int| 0 <= a < 3 implies #[trigger] qlo@[a] == 100 * qty_p(ps, a) && qhi@[a] == 100 * (qty_p(ps, a) + 10) by {
                if a == 0 {} else if a == 1 {} else {}
            }
        }
    }
    // tasks: contiguous runs of pieces
    let np = pieces.len();
    // at most MAX_TASKS tasks: beyond that, thread start-up outweighs the work of a task
    let wk = if workers < MAX_TASKS { workers } else { MAX_TASKS };
    let nt = if np < wk { if np == 0 { 1 } else { np } } else { wk };
    let pq = np / nt;
    let per = if pq < np { pq + 1 } else { pq };
    let mut tasks: Vec<IxTask> = Vec::new();
    let ghost mut cut: Seq<int> = seq![0int];
    let mut i0: usize = 0;
    let mut t: usize = 0;
    while t < nt
        invariant
            pidx_ok(p, pp), lidx_ok(l, lp), qual_ok(qual@, lp), arms_ok(qlo@, qhi@, ps),
            pcs == pieces@, np == pcs.len(),
            forall|i: int| 0 <= i < np ==> #[trigger] piece_ok(pcs[i], pp, ps),
            q0 as int == qty_p(ps, 0), q1 as int == qty_p(ps, 1), q2 as int == qty_p(ps, 2),
            -2147483648 <= q0 <= 2147483637, -2147483648 <= q1 <= 2147483637, -2147483648 <= q2 <= 2147483637,
            1 <= nt <= MAX_WORKERS, t <= nt, i0 <= np,
            tasks@.len() == t, cut.len() == t + 1, cut[0] == 0, cut[t as int] == i0,
            t == nt ==> i0 == np,
            forall|t2: int| 0 <= t2 < t ==> #[trigger] task_ok(tasks@[t2], lp, pp, ps, cut, pcs, t2),
        decreases nt - t,
    {
        let i1 = if t + 1 == nt || per > np - i0 { np } else { i0 + per };
        let mut sub: Vec<Piece> = Vec::new();
        let mut j = i0;
        while j < i1
            invariant
                i0 <= j <= i1 <= np, np == pieces@.len(),
                sub@ == pieces@.subrange(i0 as int, j as int),
            decreases i1 - j,
        {
            sub.push(pieces[j]);
            proof {
                assert(sub@ =~= pieces@.subrange(i0 as int, j + 1));
            }
            j = j + 1;
        }
        let task = IxTask {
            p, l,
            qual: copy_flags(&qual),
            pieces: sub,
            qlo: vec![100 * q0, 100 * q1, 100 * q2],
            qhi: vec![100 * (q0 + 10), 100 * (q1 + 10), 100 * (q2 + 10)],
            lo: vec![0u32; BATCH],
            hi: vec![0u32; BATCH],
            starts: vec![0u32; BATCH + 1],
            mq: vec![0u32; MCAP + 1],
            pp: Ghost(pp),
            lp: Ghost(lp),
            ps: Ghost(ps),
        };
        proof {
            assert(task.qual@ == qual@);
            assert(arms_ok(task.qlo@, task.qhi@, ps)) by {
                assert forall|a: int| 0 <= a < 3 implies #[trigger] task.qlo@[a] == 100 * qty_p(ps, a)
                    && task.qhi@[a] == 100 * (qty_p(ps, a) + 10) by {
                    if a == 0 {} else if a == 1 {} else {}
                }
            }
            assert forall|i: int| 0 <= i < task.pieces@.len() implies #[trigger] piece_ok(task.pieces@[i], pp, ps) by {
                assert(task.pieces@[i] == pcs[i0 + i]);
            }
            assert(task.pre());
        }
        let ghost old_tasks = tasks@;
        let ghost old_cut = cut;
        tasks.push(task);
        proof {
            cut = cut.push(i1 as int);
            assert forall|t2: int| 0 <= t2 < t + 1 implies #[trigger] task_ok(tasks@[t2], lp, pp, ps, cut, pcs, t2) by {
                if t2 < t {
                    assert(tasks@[t2] == old_tasks[t2]);
                    assert(task_ok(old_tasks[t2], lp, pp, ps, old_cut, pcs, t2));
                    assert(cut[t2] == old_cut[t2] && cut[t2 + 1] == old_cut[t2 + 1]);
                } else {
                    assert(tasks@[t2] == task);
                    assert(cut[t2] == i0 && cut[t2 + 1] == i1);
                }
            }
        }
        i0 = i1;
        t = t + 1;
    }
    let ghost tv = tasks@;
    proof {
        assert forall|t2: int| 0 <= t2 < tv.len() implies #[trigger] task_cut(tv[t2], lp, pp, ps, cut, pcs, t2) by {
            assert(task_ok(tasks@[t2], lp, pp, ps, cut, pcs, t2));
        }
    }
    let outs: Vec<Option<Acc>> = if nt == 1 {
        let task = tasks.pop().unwrap();
        proof {
            assert(task == tv[0]);
            assert(task_ok(tv[0], lp, pp, ps, cut, pcs, 0));
        }
        let o = task.run();
        let mut v: Vec<Option<Acc>> = Vec::new();
        v.push(o);
        proof {
            assert(v@[0] == o);
            assert(ix_post(tv[0], v@[0]));
            assert forall|t2: int| 0 <= t2 < tv.len() implies #[trigger] ix_post(tv[t2], v@[t2]) by {}
        }
        v
    } else {
        proof {
            assert forall|i: int| 0 <= i < tasks@.len() implies #[trigger] tasks@[i].pre() by {
                assert(task_ok(tasks@[i], lp, pp, ps, cut, pcs, i));
            }
        }
        match fork_join(dispatch, tasks) {
            Ok(o) => {
                proof {
                    assert forall|t2: int| 0 <= t2 < tv.len() implies #[trigger] ix_post(tv[t2], o@[t2]) by {
                        assert(tv[t2].post(o@[t2]));
                    }
                }
                o
            },
            Err(_) => {
                return None;
            },
        }
    };
    let r = merge_tasks(&outs, Ghost(tv), Ghost(cut), Ghost(lp), Ghost(pp), Ghost(ps), Ghost(pcs));
    proof {
        assert(cut[tv.len() as int] == np);
        lemma_prow(pp, 0);
        let n = n_p(pp);
        assert forall|k: int| 0 <= k < 3 implies #[trigger] rsum(lp, pp, ps, k, 0, n) == isum(pt(lp, pp, ps, k), 0, n) by {
            lemma_sum_of_isum(prows(pp), pin_l(lp, ps, k), 0, n);
            assert forall|j: int| 0 <= j < n implies #[trigger] pt(lp, pp, ps, k)(j) == (|i: int| pin_l(lp, ps, k)(prows(pp)[i]))(j) by {}
            lemma_isum_ext(pt(lp, pp, ps, k), |i: int| pin_l(lp, ps, k)(prows(pp)[i]), 0, n);
        }
        assert(rsum(lp, pp, ps, 0, 0, n) == isum(pt(lp, pp, ps, 0), 0, n));
        assert(rsum(lp, pp, ps, 1, 0, n) == isum(pt(lp, pp, ps, 1), 0, n));
        assert(rsum(lp, pp, ps, 2, 0, n) == isum(pt(lp, pp, ps, 2), 0, n));
    }
    r
}

} // verus!
