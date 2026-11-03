//! Per-lineitem contributions computed by the scan, and the buffer of pending rows.
//!
//! `Shared` is the read-only state every scan task reads (columns, codes, nation tables, the date range);
//! `shared_ok` ties it to the stored data and the statement's parameters (`Ctx`). A lineitem row's contribution
//! (`contrib_ok`: `Some((group, revenue))` exactly for candidates) is computed either from scratch (`slow_contrib`,
//! correct for any data) or from the code of its order and its supplier's slot (`fast_from_slot`, for an *entry*
//! whose order has a non-`NONE` code, `entry_ok`).
//!
//! The scan records every row it does not skip as an entry (row, code) — `SLOW` for rows computed from scratch —
//! in a fixed-capacity buffer, and flushes the buffer into the group accumulators (`flush`). Ghost bookkeeping:
//! `ent` lists every entry so far; the accumulators hold the group sums of the flushed prefix (`accs_rel`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::work::put;
use crate::agent::model::*;
use crate::agent::sem_from::*;
use crate::agent::sem_pred::*;
use crate::agent::plan::*;
use crate::agent::contrib::*;
use crate::agent::cols::*;
use crate::agent::common::key_lookup::find_key;
use crate::agent::common::lookup::*;
use crate::agent::common::exact_sum::*;
use crate::agent::common::bitmap::*;

verus! {

/// Code of an entry computed from scratch.
pub const SLOW: u8 = 254;

/// Pending entries per flush (1024: the entry buffers stay in the L1 cache; measured ~1% faster than 4096 and
/// faster than 512).
pub const CAP: usize = 1024;

/// The statement's parameters and the slots, as the proofs use them.
pub struct Ctx {
    pub sv: StoresView,
    pub rp: Seq<u8>,
    pub pd: int,
    pub t: int,
    pub slots: Seq<u8>,
}

/// The read-only state of the scan tasks.
pub struct Shared {
    pub c: Cols,
    pub ccode: Vec<u8>,
    pub scode: Vec<u8>,
    pub bits: Vec<u64>,
    pub cdense: bool,
    pub sdense: bool,
    /// The fast (plain `i64`) forms of the dense customer and supplier key columns.
    pub ck: DenseKeys,
    pub sk: DenseKeys,
    pub inreg: Vec<bool>,
    pub gids: Vec<usize>,
    pub gos: Vec<usize>,
    pub ng: usize,
    pub dlo: i32,
    pub dhi: i32,
    pub fast: bool,
}

pub open spec fn shared_ok(sh: Shared, x: Ctx) -> bool {
    &&& cols_ok(sh.c, x.sv)
    &&& stores_wf(x.sv)
    &&& keys_ok(x.sv)
    &&& vals_ok(x.sv)
    &&& forall|od: i32| #[trigger] date_in(od, x.pd, x.t) == (sh.dlo <= od < sh.dhi)
    &&& sh.inreg@.len() == nn(x.sv)
    &&& sh.gids@.len() == nn(x.sv)
    &&& forall|e: int| 0 <= e < nn(x.sv) ==> #[trigger] sh.inreg@[e] == inreg(x.sv, x.rp, e)
    &&& forall|e: int| 0 <= e < nn(x.sv) && inreg(x.sv, x.rp, e) ==> #[trigger] sh.gids@[e] < sh.ng
    &&& sh.cdense ==> is_dense(c_ck(x.sv))
    &&& sh.sdense ==> is_dense(s_sk(x.sv))
    &&& dense_keys_ok(sh.ck, c_ck(x.sv))
    &&& dense_keys_ok(sh.sk, s_sk(x.sv))
    &&& sh.fast ==> {
        &&& slots_ok(x.sv, x.rp, sh.gids@, x.slots, sh.gos@)
        &&& forall|s: int| 0 <= s < sh.gos@.len() ==> #[trigger] sh.gos@[s] < sh.ng
        &&& sh.ccode@.len() == nc(x.sv)
        &&& sh.scode@.len() == ns(x.sv)
        &&& forall|i: int| 0 <= i < nc(x.sv) ==> #[trigger] sh.ccode@[i] == nslot(x.sv, x.slots, c_nk(x.sv)[i])
        &&& forall|d: int| 0 <= d < ns(x.sv) ==> #[trigger] sh.scode@[d] == nslot(x.sv, x.slots, s_nk(x.sv)[d])
        &&& 64 * sh.bits@.len() >= nc(x.sv)
        &&& forall|i: int| 0 <= i < nc(x.sv) ==> #[trigger] bit_at(sh.bits@, i) == (sh.ccode@[i] != NONE)
    }
}

/// `r` is lineitem row `c`'s contribution: `Some((group, revenue))` exactly for candidates.
pub open spec fn contrib_ok(x: Ctx, gids: Seq<usize>, ng: usize, c: int, r: Option<(usize, i128)>) -> bool {
    &&& (r is Some) == cand(x.sv, x.rp, x.pd, x.t, c)
    &&& r matches Some((g, v)) ==> g < ng && g as int == gids[cnation(x.sv, x.rp, x.pd, x.t, c)] as int && v as int == crev(x.sv, c)
        && v > i128::MIN
}

/// The revenue coefficient of lineitem row `row`.
pub fn rev(c: &Cols, row: usize, Ghost(sv): Ghost<StoresView>) -> (v: i128)
    requires cols_ok(*c, sv), vals_ok(sv), row < c.nl,
    ensures v as int == crev(sv, row as int), v > i128::MIN,
    no_unwind
{
    let e = c.lext[row];
    let d = c.ldisc[row];
    assert(abs(e as int) < coeff_bound() && abs(d as int) < coeff_bound());
    let f = 100 - d;
    assert(-0x1_0000_0000_0000_0000_0000_0000_0000 < e * f < 0x1_0000_0000_0000_0000_0000_0000_0000) by (nonlinear_arith)
        requires -1_000_000_000_000_000 < e < 1_000_000_000_000_000, -1_000_000_000_000_100 < f < 1_000_000_000_000_100;
    e * f
}

/// The contribution of lineitem row `row`, from scratch.
pub fn slow_contrib(sh: &Shared, row: usize, Ghost(x): Ghost<Ctx>) -> (r: Option<(usize, i128)>)
    requires shared_ok(*sh, x), row < sh.c.nl,
    ensures contrib_ok(x, sh.gids@, sh.ng, row as int, r),
    no_unwind
{
    let ghost sv = x.sv;
    let ghost (rp, pd, t) = (x.rp, x.pd, x.t);
    let c = &sh.c;
    let ghost cr = row as int;
    let j = match find_sorted(c.ook, c.no, c.lok[row]) {
        Some(j) => j,
        None => {
            proof { if cand(sv, rp, pd, t, cr) { lemma_cand_facts(sv, rp, pd, t, cr); } }
            return None;
        },
    };
    let od = c.odate[j];
    if !(sh.dlo <= od && od < sh.dhi) {
        proof {
            if cand(sv, rp, pd, t, cr) {
                lemma_cand_facts(sv, rp, pd, t, cr);
                let u = ctuple(sv, rp, pd, t, cr);
                assert(o_ok(sv)[u.1] == o_ok(sv)[j as int]);
            }
        }
        return None;
    }
    let i = match find_dense(c.ckeys, c.nc, sh.cdense, c.ock[j]) {
        Some(i) => i,
        None => {
            proof {
                if cand(sv, rp, pd, t, cr) {
                    lemma_cand_facts(sv, rp, pd, t, cr);
                    let u = ctuple(sv, rp, pd, t, cr);
                    assert(o_ok(sv)[u.1] == o_ok(sv)[j as int]);
                    assert(c_ck(sv)[u.0] == o_ck(sv)[j as int]);
                }
            }
            return None;
        },
    };
    let d = match find_dense(c.skeys, c.ns, sh.sdense, c.lsk[row]) {
        Some(d) => d,
        None => {
            proof {
                if cand(sv, rp, pd, t, cr) {
                    lemma_cand_facts(sv, rp, pd, t, cr);
                    let u = ctuple(sv, rp, pd, t, cr);
                    assert(s_sk(sv)[u.2] == l_sk(sv)[cr]);
                }
            }
            return None;
        },
    };
    if c.cnk[i] != c.snk[d] {
        proof {
            if cand(sv, rp, pd, t, cr) {
                lemma_cand_facts(sv, rp, pd, t, cr);
                let u = ctuple(sv, rp, pd, t, cr);
                assert(o_ok(sv)[u.1] == o_ok(sv)[j as int]);
                assert(c_ck(sv)[u.0] == c_ck(sv)[i as int]);
                assert(s_sk(sv)[u.2] == s_sk(sv)[d as int]);
            }
        }
        return None;
    }
    let e = match find_key(c.nkeys, c.nn, c.snk[d]) {
        Some(e) => e,
        None => {
            proof {
                if cand(sv, rp, pd, t, cr) {
                    lemma_cand_facts(sv, rp, pd, t, cr);
                    let u = ctuple(sv, rp, pd, t, cr);
                    assert(s_sk(sv)[u.2] == s_sk(sv)[d as int]);
                    assert(n_nk(sv)[u.3] == s_nk(sv)[d as int]);
                }
            }
            return None;
        },
    };
    if !sh.inreg[e] {
        proof {
            if cand(sv, rp, pd, t, cr) {
                lemma_cand_facts(sv, rp, pd, t, cr);
                let u = ctuple(sv, rp, pd, t, cr);
                assert(s_sk(sv)[u.2] == s_sk(sv)[d as int]);
                assert(n_nk(sv)[u.3] == n_nk(sv)[e as int]);
            }
        }
        return None;
    }
    let v = rev(c, row, Ghost(sv));
    proof {
        let f = choose|f: int| 0 <= f < nr(sv) && #[trigger] r_rk(sv)[f] == n_rk(sv)[e as int] && r_name(sv, f) == rp;
        assert(date_in(od, pd, t));
        assert(in6(sv, i as int, j as int, cr, d as int, e as int, f));
        assert(qual6(sv, rp, pd, t, i as int, j as int, cr, d as int, e as int, f));
        assert(cand(sv, rp, pd, t, cr));
        lemma_ctuple(sv, rp, pd, t, cr);
    }
    Some((sh.gids[e], v))
}

/// Lineitem row `c` is an entry with order code `code`: some order with its order key has that non-`NONE` code.
pub open spec fn entry_ok(x: Ctx, c: int, code: u8) -> bool {
    &&& code != NONE
    &&& exists|j: int| 0 <= j < no(x.sv) && #[trigger] o_ok(x.sv)[j] == l_ok(x.sv)[c] && ord_code(x.sv, x.slots, x.pd, x.t, j) == code
}

// ------------------------------------------------------------------------------------------ entries and accumulators

/// Sums of the group terms of the first `n` entries of `ent`.
pub open spec fn esum(x: Ctx, gids: Seq<usize>, g: int, ent: Seq<usize>, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else { esum(x, gids, g, ent, n - 1) + gterm(x.sv, x.rp, x.pd, x.t, gids, g, ent[n - 1] as int) }
}

pub open spec fn ecnt(x: Ctx, gids: Seq<usize>, g: int, ent: Seq<usize>, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else {
        ecnt(x, gids, g, ent, n - 1)
            + if cand(x.sv, x.rp, x.pd, x.t, ent[n - 1] as int) && gids[cnation(x.sv, x.rp, x.pd, x.t, ent[n - 1] as int)] == g { 1int } else { 0int }
    }
}

pub open spec fn eabs(x: Ctx, gids: Seq<usize>, g: int, ent: Seq<usize>, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else { eabs(x, gids, g, ent, n - 1) + abs(gterm(x.sv, x.rp, x.pd, x.t, gids, g, ent[n - 1] as int)) }
}

/// Every group accumulator holds the sums of the first `n` entries.
pub open spec fn accs_rel(accs: Seq<Acc>, x: Ctx, gids: Seq<usize>, ng: usize, ent: Seq<usize>, n: int) -> bool {
    &&& accs.len() == ng
    &&& forall|g: int| 0 <= g < ng ==> acc_ok(#[trigger] accs[g], esum(x, gids, g, ent, n), eabs(x, gids, g, ent, n), ecnt(x, gids, g, ent, n))
}

/// Entry sums over a prefix do not depend on later entries.
pub proof fn lemma_esum_prefix(x: Ctx, gids: Seq<usize>, g: int, a: Seq<usize>, b: Seq<usize>, n: int)
    requires 0 <= n <= a.len(), n <= b.len(), forall|p: int| 0 <= p < n ==> #[trigger] a[p] == b[p],
    ensures esum(x, gids, g, a, n) == esum(x, gids, g, b, n), ecnt(x, gids, g, a, n) == ecnt(x, gids, g, b, n),
        eabs(x, gids, g, a, n) == eabs(x, gids, g, b, n),
    decreases n,
{
    if n > 0 {
        lemma_esum_prefix(x, gids, g, a, b, n - 1);
    }
}

/// Adds the contribution `r` of entry `ent[n]` to the accumulators.
pub fn add_contrib(accs: &mut Vec<Acc>, r: Option<(usize, i128)>, Ghost(x): Ghost<Ctx>, Ghost(gids): Ghost<Seq<usize>>, ng: usize,
    Ghost(ent): Ghost<Seq<usize>>, Ghost(n): Ghost<int>)
    requires
        accs_rel(old(accs)@, x, gids, ng, ent, n), 0 <= n < ent.len(),
        contrib_ok(x, gids, ng, ent[n] as int, r),
    ensures accs_rel(final(accs)@, x, gids, ng, ent, n + 1),
    no_unwind
{
    let ghost a0 = accs@;
    let ghost c = ent[n] as int;
    match r {
        Some((g, v)) => {
            let ghost (s, m, k) = (esum(x, gids, g as int, ent, n), eabs(x, gids, g as int, ent, n), ecnt(x, gids, g as int, ent, n));
            assert(acc_ok(a0[g as int], s, m, k));
            let mut a = Acc { sum: accs[g].sum, mass: accs[g].mass, cnt: accs[g].cnt, over: accs[g].over };
            acc_add(&mut a, v, Ghost(s), Ghost(m), Ghost(k));
            put(accs, g, a);
            proof {
                assert forall|h: int| 0 <= h < ng implies acc_ok(#[trigger] accs@[h], esum(x, gids, h, ent, n + 1),
                    eabs(x, gids, h, ent, n + 1), ecnt(x, gids, h, ent, n + 1)) by {
                    if h != g as int {
                        assert(accs@[h] == a0[h]);
                    }
                }
            }
        },
        None => {
            proof {
                assert forall|h: int| 0 <= h < ng implies acc_ok(#[trigger] accs@[h], esum(x, gids, h, ent, n + 1),
                    eabs(x, gids, h, ent, n + 1), ecnt(x, gids, h, ent, n + 1)) by {
                    assert(gterm(x.sv, x.rp, x.pd, x.t, gids, h, c) == 0);
                }
            }
        },
    }
}

/// A pending entry: computed from scratch, or (fast mode) an entry with its order's code.
pub open spec fn entry_valid(sh: Shared, x: Ctx, row: usize, code: u8) -> bool {
    &&& row < sh.c.nl
    &&& code == SLOW || (sh.fast && entry_ok(x, row as int, code))
}

/// The pending buffer: `nr` entries `(rrow[p], rcode[p])`, the last `nr` of `ent`.
pub struct Buf {
    pub rrow: Vec<usize>,
    pub rcode: Vec<u8>,
    pub rsc: Vec<u8>,
    pub rsk: Vec<i64>,
    pub nr: usize,
}

pub open spec fn buf_ok(b: Buf, sh: Shared, x: Ctx, ent: Seq<usize>) -> bool {
    &&& b.rrow@.len() == CAP
    &&& b.rcode@.len() == CAP
    &&& b.rsc@.len() == CAP
    &&& b.rsk@.len() == CAP
    &&& b.nr < CAP
    &&& b.nr <= ent.len()
    &&& forall|p: int| 0 <= p < b.nr ==> #[trigger] b.rrow@[p] == ent[ent.len() - b.nr + p] && entry_valid(sh, x, b.rrow@[p], b.rcode@[p])
}

/// The slot of the supplier with key `k` (`NONE` if there is none).
pub open spec fn supp_slot(sv: StoresView, scode: Seq<u8>, k: i64) -> u8 {
    if exists|d: int| 0 <= d < ns(sv) && #[trigger] s_sk(sv)[d] == k {
        scode[choose|d: int| 0 <= d < ns(sv) && #[trigger] s_sk(sv)[d] == k]
    } else {
        NONE
    }
}

/// The slot of the supplier of lineitem row `row` (fast mode).
fn key_supp_slot(sh: &Shared, k: i64, Ghost(x): Ghost<Ctx>) -> (r: u8)
    requires shared_ok(*sh, x), sh.fast,
    ensures r == supp_slot(x.sv, sh.scode@, k),
    no_unwind
{
    let ghost sv = x.sv;
    let c = &sh.c;
    match find_dense(c.skeys, c.ns, sh.sdense, k) {
        Some(d) => {
            proof {
                let d2 = choose|d2: int| 0 <= d2 < ns(sv) && #[trigger] s_sk(sv)[d2] == k;
                assert(s_sk(sv)[d2] == s_sk(sv)[d as int]);
            }
            sh.scode[d]
        },
        None => NONE,
    }
}

/// The contribution of entry `(row, code)` from its supplier's slot `slot`.
fn fast_from_slot(sh: &Shared, row: usize, code: u8, slot: u8, Ghost(x): Ghost<Ctx>) -> (r: Option<(usize, i128)>)
    requires
        shared_ok(*sh, x), sh.fast, row < sh.c.nl, entry_ok(x, row as int, code),
        slot == supp_slot(x.sv, sh.scode@, l_sk(x.sv)[row as int]),
    ensures contrib_ok(x, sh.gids@, sh.ng, row as int, r),
    no_unwind
{
    let ghost sv = x.sv;
    let ghost (rp, pd, t) = (x.rp, x.pd, x.t);
    let ghost j = choose|j: int| 0 <= j < no(sv) && #[trigger] o_ok(sv)[j] == l_ok(sv)[row as int] && ord_code(sv, x.slots, pd, t, j) == code;
    proof { lemma_fast_entry(sv, rp, pd, t, sh.gids@, x.slots, sh.gos@, row as int, j, code); }
    if slot == code {
        let v = rev(&sh.c, row, Ghost(sv));
        proof {
            let d = choose|d: int| 0 <= d < ns(sv) && #[trigger] s_sk(sv)[d] == l_sk(sv)[row as int];
            assert(sh.scode@[d] == nslot(sv, x.slots, s_nk(sv)[d]));
            lemma_ord_code(sv, rp, pd, t, sh.gids@, x.slots, sh.gos@, j);
            assert((code as int) < sh.gos@.len()) by {
                let (i, e) = choose|i: int, e: int| 0 <= i < nc(sv) && 0 <= e < nn(sv) && #[trigger] c_ck(sv)[i] == o_ck(sv)[j]
                    && #[trigger] n_nk(sv)[e] == c_nk(sv)[i] && inreg(sv, rp, e) && x.slots[e] == ord_code(sv, x.slots, pd, t, j)
                    && date_in(o_date(sv)[j], pd, t);
            }
        }
        Some((sh.gos[code as usize], v))
    } else {
        proof {
            if cand(sv, rp, pd, t, row as int) {
                let d2 = choose|d2: int| 0 <= d2 < ns(sv) && #[trigger] s_sk(sv)[d2] == l_sk(sv)[row as int]
                    && nslot(sv, x.slots, s_nk(sv)[d2]) == code;
                let d = choose|d: int| 0 <= d < ns(sv) && #[trigger] s_sk(sv)[d] == l_sk(sv)[row as int];
                assert(s_sk(sv)[d2] == s_sk(sv)[d]);
            }
        }
        None
    }
}

/// Flushes the pending entries into the accumulators.
pub fn flush(sh: &Shared, b: &mut Buf, accs: &mut Vec<Acc>, Ghost(x): Ghost<Ctx>, Ghost(ent): Ghost<Seq<usize>>)
    requires
        shared_ok(*sh, x),
        old(b).rrow@.len() == CAP, old(b).rcode@.len() == CAP, old(b).rsc@.len() == CAP, old(b).rsk@.len() == CAP, old(b).nr <= CAP, old(b).nr <= ent.len(),
        forall|p: int| 0 <= p < old(b).nr ==> #[trigger] old(b).rrow@[p] == ent[ent.len() - old(b).nr + p]
            && entry_valid(*sh, x, old(b).rrow@[p], old(b).rcode@[p]),
        accs_rel(old(accs)@, x, sh.gids@, sh.ng, ent, ent.len() - old(b).nr),
    ensures
        buf_ok(*final(b), *sh, x, ent), final(b).nr == 0,
        accs_rel(final(accs)@, x, sh.gids@, sh.ng, ent, ent.len() as int),
    no_unwind
{
    let nr = b.nr;
    let ghost base = ent.len() - nr;
    // Pass 1: the supplier keys of the entries (a tight loop of independent reads, so their cache misses overlap).
    let lsk = sh.c.lsk;
    let mut i: usize = 0;
    while i < nr
        invariant
            shared_ok(*sh, x), lsk@ == l_sk(x.sv), lsk@.len() == sh.c.nl,
            b.rrow@.len() == CAP, b.rcode@.len() == CAP, b.rsc@.len() == CAP, b.rsk@.len() == CAP, nr == b.nr, nr <= CAP, nr <= ent.len(),
            base == ent.len() - nr, i <= nr,
            forall|p: int| 0 <= p < nr ==> #[trigger] b.rrow@[p] == ent[base + p] && entry_valid(*sh, x, b.rrow@[p], b.rcode@[p]),
            forall|p: int| 0 <= p < i ==> #[trigger] b.rsk@[p] == l_sk(x.sv)[b.rrow@[p] as int],
        decreases nr - i,
    {
        assert(entry_valid(*sh, x, b.rrow@[i as int], b.rcode@[i as int]));
        let k = lsk[b.rrow[i]];
        put(&mut b.rsk, i, k);
        i = i + 1;
    }
    // Pass 2: the supplier slots of the fast entries.
    i = 0;
    while i < nr
        invariant
            shared_ok(*sh, x),
            b.rrow@.len() == CAP, b.rcode@.len() == CAP, b.rsc@.len() == CAP, b.rsk@.len() == CAP, nr == b.nr, nr <= CAP, nr <= ent.len(),
            base == ent.len() - nr, i <= nr,
            forall|p: int| 0 <= p < nr ==> #[trigger] b.rrow@[p] == ent[base + p] && entry_valid(*sh, x, b.rrow@[p], b.rcode@[p]),
            forall|p: int| 0 <= p < nr ==> #[trigger] b.rsk@[p] == l_sk(x.sv)[b.rrow@[p] as int],
            forall|p: int| 0 <= p < i && b.rcode@[p] != SLOW ==>
                #[trigger] b.rsc@[p] == supp_slot(x.sv, sh.scode@, l_sk(x.sv)[b.rrow@[p] as int]),
        decreases nr - i,
    {
        let code = b.rcode[i];
        if code != SLOW {
            assert(entry_valid(*sh, x, b.rrow@[i as int], b.rcode@[i as int]));
            let s = key_supp_slot(sh, b.rsk[i], Ghost(x));
            put(&mut b.rsc, i, s);
        }
        i = i + 1;
    }
    // Pass 3: the contributions.
    i = 0;
    while i < nr
        invariant
            shared_ok(*sh, x),
            b.rrow@.len() == CAP, b.rcode@.len() == CAP, b.rsc@.len() == CAP, b.rsk@.len() == CAP, nr == b.nr, nr <= CAP, nr <= ent.len(),
            base == ent.len() - nr, i <= nr,
            forall|p: int| 0 <= p < nr ==> #[trigger] b.rrow@[p] == ent[base + p] && entry_valid(*sh, x, b.rrow@[p], b.rcode@[p]),
            forall|p: int| 0 <= p < nr && b.rcode@[p] != SLOW ==>
                #[trigger] b.rsc@[p] == supp_slot(x.sv, sh.scode@, l_sk(x.sv)[b.rrow@[p] as int]),
            accs_rel(accs@, x, sh.gids@, sh.ng, ent, base + i),
        decreases nr - i,
    {
        let row = b.rrow[i];
        let code = b.rcode[i];
        assert(entry_valid(*sh, x, b.rrow@[i as int], b.rcode@[i as int]));
        let r = if code == SLOW { slow_contrib(sh, row, Ghost(x)) } else { fast_from_slot(sh, row, code, b.rsc[i], Ghost(x)) };
        add_contrib(accs, r, Ghost(x), Ghost(sh.gids@), sh.ng, Ghost(ent), Ghost(base + i));
        i = i + 1;
    }
    b.nr = 0;
}

/// Appends entry `(row, code)` (flushing a full buffer).
pub fn push_entry(sh: &Shared, b: &mut Buf, accs: &mut Vec<Acc>, row: usize, code: u8, Ghost(x): Ghost<Ctx>, Ghost(ent): Ghost<Seq<usize>>)
    requires
        shared_ok(*sh, x), buf_ok(*old(b), *sh, x, ent),
        accs_rel(old(accs)@, x, sh.gids@, sh.ng, ent, ent.len() - old(b).nr),
        entry_valid(*sh, x, row, code),
    ensures
        buf_ok(*final(b), *sh, x, ent.push(row)),
        accs_rel(final(accs)@, x, sh.gids@, sh.ng, ent.push(row), ent.len() + 1 - final(b).nr),
    no_unwind
{
    let ghost e2 = ent.push(row);
    let ghost n0 = ent.len() - b.nr;
    let nr = b.nr;
    put(&mut b.rrow, nr, row);
    put(&mut b.rcode, nr, code);
    b.nr = nr + 1;
    proof {
        assert forall|g: int| 0 <= g < sh.ng implies acc_ok(#[trigger] accs@[g], esum(x, sh.gids@, g, e2, n0),
            eabs(x, sh.gids@, g, e2, n0), ecnt(x, sh.gids@, g, e2, n0)) by {
            lemma_esum_prefix(x, sh.gids@, g, ent, e2, n0);
        }
        assert forall|p: int| 0 <= p < b.nr implies #[trigger] b.rrow@[p] == e2[e2.len() - b.nr + p]
            && entry_valid(*sh, x, b.rrow@[p], b.rcode@[p]) by {
            if p < nr {
                assert(b.rrow@[p] == old(b).rrow@[p]);
                assert(b.rcode@[p] == old(b).rcode@[p]);
            }
        }
    }
    if b.nr == CAP {
        flush(sh, b, accs, Ghost(x), Ghost(e2));
    }
}

} // verus!
