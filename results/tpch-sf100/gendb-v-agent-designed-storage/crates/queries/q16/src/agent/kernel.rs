//! The pair tasks of one round (`model`): the (local group, supplier row) pairs of a range of part rows, grouped
//! by local group.
//!
//! `PairTask` (part rows `[lo, hi)`, whole part blocks): per part block, three 256-entry tables turn the brand, type
//! and size codes of a row into its brand term, type term and size slot (`block_tabs`); a row whose three entries
//! exist has the code `bterm + tterm + slot`. For such a row with key `k`, the partsupp rows of `k`
//! (`ps_rows_of`: the guess `[j * ratio, (j + 1) * ratio)` checked at its ends and neighbours on sorted partsupp,
//! else a binary search, or every row checked when partsupp is not sorted) each give the supplier row of their
//! suppkey (`supp_of`: by position when the supplier keys are dense, else a key search) and one pair (code, supplier
//! row). The pairs are then sorted by code (`common::scatter`): the task's segment of group `g` holds exactly the
//! supplier rows of its pairs of `g` (`pairs_out`). A task whose scratch is too small says so (`done == false`); a
//! scratch of the partsupp row count always suffices (every partsupp row gives at most one pair, since part keys
//! are unique). Supplier rows are stored as `S` (`sidx`: `u32` when they fit). Each task also runs the subquery's
//! byte test over a range of supplier rows (`supp::SuppTask`), so no separate fork-join is needed for it.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::WorkerTask;
use crate::stores::suppliers::interface::common::keyidx as sk;
use crate::stores::psrun::interface as pri;
use super::tables::*;
use super::model::*;
use super::common::scatter::*;
use super::sidx::SIdx;
use super::supp::{SuppTask, SuppOut};

verus! {

broadcast use vstd::array::group_array_axioms;

/// The bit that marks "no entry" in the per-block code tables (every term, slot and code is below it).
pub const NONE_BIT: u32 = 0x8000_0000;

/// What every pair task reads: the column handles, the key layouts and the round's lookup tables.
pub struct PairEnv {
    pub c: Cols,
    /// Partsupp rows per part: the guess of part row `j`'s partsupp range is `[j * ratio, (j + 1) * ratio)` for
    /// `j < jmax`.
    pub ratio: usize,
    pub jmax: usize,
    /// `ps.bs == 2^ps_shift` when `ps_shift < 32` (a row's group is then a shift).
    pub ps_shift: u32,
    /// The supplier keys are `sfirst + r` at row `r`.
    pub sdense: bool,
    pub sfirst: i64,
    /// The part keys are `pfirst + j` at row `j`.
    pub pdense: bool,
    pub pfirst: i64,
    pub tabs: Arc<QualTabs>,
    pub nb: usize,
    pub nt: usize,
    pub ns: usize,
    /// `RUN_ROWS / ratio` when psrun's key runs apply to the guess (`runs[0] == ratio`, `ratio` divides `RUN_ROWS`),
    /// else 0.
    pub rper: usize,
}

/// The environment's facts: shapes, key layouts and unique keys, and the tables of a round of `ng` local groups.
pub open spec fn env_ok(e: PairEnv, ng: int) -> bool {
    &&& shape_ok(e.c)
    &&& tabs_shape(*e.tabs, e.nb as int, e.nt as int, ng)
    &&& e.ns == e.tabs.sizes@.len()
    &&& e.ratio > 0 ==> e.jmax * e.ratio <= e.c.ps.n
    &&& e.rper > 0 ==> e.ratio > 0 && e.rper * e.ratio == pri::RUN_ROWS && e.c.ps.runs@[0] == e.ratio as int
    &&& e.ps_shift < 32 ==> e.c.ps.bs == vstd::arithmetic::power2::pow2(e.ps_shift as nat)
    &&& e.sdense ==> forall|r: int| 0 <= r < e.c.s.n ==> #[trigger] skey(e.c.s, r) == e.sfirst + r
    &&& e.pdense ==> forall|j: int| 0 <= j < e.c.p.n ==> #[trigger] pkey(e.c.p, j) == e.pfirst + j
    &&& forall|j1: int, j2: int| 0 <= j1 < e.c.p.n && 0 <= j2 < e.c.p.n && #[trigger] pkey(e.c.p, j1) == #[trigger] pkey(e.c.p, j2)
        ==> j1 == j2
    &&& forall|r1: int, r2: int| 0 <= r1 < e.c.s.n && 0 <= r2 < e.c.s.n && #[trigger] skey(e.c.s, r1) == #[trigger] skey(e.c.s, r2)
        ==> r1 == r2
}

/// The group of partsupp row `i`.
#[inline(always)]
pub fn ps_grp(e: &PairEnv, i: usize) -> (r: usize)
    requires e.ps_shift < 32 ==> e.c.ps.bs == vstd::arithmetic::power2::pow2(e.ps_shift as nat), e.c.ps.bs >= 1,
    ensures r == (i as int) / (e.c.ps.bs as int),
    no_unwind
{
    if e.ps_shift < 32 {
        proof {
            vstd::bits::lemma_usize_shr_is_div(i, e.ps_shift as usize);
        }
        i >> (e.ps_shift as usize)
    } else {
        i / e.c.ps.bs
    }
}

/// Key of partsupp row `i`.
#[inline(always)]
pub fn ps_key(e: &PairEnv, i: usize, Ghost(ng): Ghost<int>) -> (r: i64)
    requires env_ok(*e, ng), i < e.c.ps.n,
    ensures r == pskey(e.c.ps, i as int),
    no_unwind
{
    proof {
        lemma_grp_bound(e.c.ps.n as int, e.c.ps.bs as int, e.c.ps.ng as int, i as int);
        assert(i64r(pskey(e.c.ps, i as int)));
    }
    let g = ps_grp(e, i);
    e.c.ps.key_b[g] + e.c.ps.key_c[i] as i64
}

/// Suppkey of partsupp row `i`.
#[inline(always)]
pub fn ps_supp(e: &PairEnv, i: usize, Ghost(ng): Ghost<int>) -> (r: i64)
    requires env_ok(*e, ng), i < e.c.ps.n,
    ensures r == pssupp(e.c.ps, i as int),
    no_unwind
{
    proof {
        lemma_grp_bound(e.c.ps.n as int, e.c.ps.bs as int, e.c.ps.ng as int, i as int);
        assert(i64r(pssupp(e.c.ps, i as int)));
    }
    let g = ps_grp(e, i);
    e.c.ps.supp_b[g] + e.c.ps.supp_c[i] as i64
}

/// Keys are nondecreasing along sorted partsupp.
proof fn lemma_ps_sorted(e: PairEnv, ng: int, a: int, b: int)
    requires env_ok(e, ng), e.c.ps.kind == 1, 0 <= a <= b < e.c.ps.n,
    ensures pskey(e.c.ps, a) <= pskey(e.c.ps, b),
{
    let c = e.c;
    sk::lemma_sorted_le(c.ps.key_c@, c.ps.key_b@, c.e32@, c.e64@, c.ps.bs as int, c.ps.kind, c.ps.n as int, a, b);
}

/// Every partsupp row of key `k` lies in `[a, b)`; when `exact`, every row there has key `k`.
pub open spec fn rows_of(e: PairEnv, k: int, a: int, b: int, exact: bool) -> bool {
    &&& 0 <= a <= b <= e.c.ps.n
    &&& forall|i: int| 0 <= i < e.c.ps.n && #[trigger] pskey(e.c.ps, i) == k ==> a <= i < b
    &&& exact ==> forall|i: int| a <= i < b ==> #[trigger] pskey(e.c.ps, i) == k
}

/// The guess `[a, b)` of key `k`'s partsupp rows: both ends hold `k`, and the neighbours (if any) do not.
pub open spec fn guess_ok(e: PairEnv, k: int, a: int, b: int) -> bool {
    &&& 0 <= a < b <= e.c.ps.n
    &&& pskey(e.c.ps, a) == k
    &&& pskey(e.c.ps, b - 1) == k
    &&& (a == 0 || pskey(e.c.ps, a - 1) != k)
    &&& (b == e.c.ps.n || pskey(e.c.ps, b) != k)
}

/// Row `x = J * R + d` of block `B` (rows from `B * RUN_ROWS`, `P * R == RUN_ROWS`) is run step `(x - B * RUN_ROWS) / R`.
pub proof fn lemma_run_step(r: int, p: int, bk: int, j: int, d: int)
    requires r >= 1, p * r == 65536, bk >= 0, j * r >= bk * 65536, -1 <= d <= r,
        d == -1 ==> j * r > bk * 65536,
    ensures
        0 <= d < r ==> (j * r + d - bk * 65536) / r == j - bk * p,
        d == -1 ==> (j * r + d - bk * 65536) / r == j - bk * p - 1,
        d == r ==> (j * r + d - bk * 65536) / r == j - bk * p + 1,
{
    assert(bk * 65536 == (bk * p) * r) by (nonlinear_arith) requires p * r == 65536;
    let q = j - bk * p;
    assert(j * r - bk * 65536 == q * r) by (nonlinear_arith) requires bk * 65536 == (bk * p) * r, q == j - bk * p;
    if 0 <= d < r {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(j * r + d - bk * 65536, r, q, d);
    }
    if d == -1 {
        assert(q >= 1) by (nonlinear_arith) requires q * r > 0, r >= 1;
        assert(j * r + d - bk * 65536 == (q - 1) * r + (r - 1)) by (nonlinear_arith) requires j * r - bk * 65536 == q * r, d == -1;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(j * r + d - bk * 65536, r, q - 1, r - 1);
    }
    if d == r {
        assert(j * r + d - bk * 65536 == (q + 1) * r + 0) by (nonlinear_arith) requires j * r - bk * 65536 == q * r, d == r;
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(j * r + d - bk * 65536, r, q + 1, 0);
    }
}

/// The guess of part row `j` (rows `[j * ratio, (j + 1) * ratio)`) from psrun's key runs: inside a block with a run
/// entry, every row's key is arithmetic, so only a neighbour across the block's edge is read.
#[inline(always)]
pub fn run_guess(e: &PairEnv, j: usize, k: i64, Ghost(ng): Ghost<int>) -> (ok: bool)
    requires env_ok(*e, ng), e.ratio > 0, j < e.jmax,
    ensures ok ==> guess_ok(*e, k as int, j * e.ratio, j * e.ratio + e.ratio),
    no_unwind
{
    let rper = e.rper;
    if rper == 0 {
        return false;
    }
    let n = e.c.ps.n;
    let r = e.ratio;
    proof {
        assert(j * r + r <= e.jmax * r) by (nonlinear_arith) requires j < e.jmax, r > 0;
    }
    let a = j * r;
    let b = a + r;
    let blk = a / 65536;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, 65536);
        let nb = pri::run_blocks(n as int);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n + 65535, 65536);
        assert(blk < nb) by (nonlinear_arith)
            requires a == 65536 * blk + a % 65536, 0 <= a % 65536 < 65536, a < n,
                n + 65535 == 65536 * nb + (n + 65535) % 65536, 0 <= (n + 65535) % 65536 < 65536, blk >= 0;
        assert(blk * rper <= j) by (nonlinear_arith)
            requires blk * 65536 <= a, a == j * r, rper * r == 65536, r >= 1, blk >= 0, rper >= 1;
    }
    let kk = e.c.ps.runs[blk + 1];
    if kk == pri::NO_RUN {
        return false;
    }
    let s = blk * 65536;
    let off = j - blk * rper;
    if kk as i128 + off as i128 != k as i128 || b - s > 65536 {
        return false;
    }
    let ghost ri = r as int;
    let ghost bi = blk as int;
    proof {
        assert(e.c.ps.runs@[0] == r as int);
        assert(s == bi * pri::RUN_ROWS);
        // Rows `[a, b)` lie in block `blk`, each at run step `off`.
        assert forall|i: int| a <= i < b implies #[trigger] pskey(e.c.ps, i) == k by {
            lemma_run_step(ri, rper as int, bi, j as int, i - a);
            assert(fv32(e.c.ps.key_c@, e.c.ps.key_b@, e.c.ps.bs as int, i) == kk + (i - bi * pri::RUN_ROWS) / ri);
        }
        assert(pskey(e.c.ps, a as int) == k);
        assert(pskey(e.c.ps, b - 1) == k);
    }
    // The neighbour before `a`: inside the block it is one run step lower; at the block's start it is read.
    let lo_ok = if a > s {
        proof {
            lemma_run_step(ri, rper as int, bi, j as int, -1);
            assert(fv32(e.c.ps.key_c@, e.c.ps.key_b@, e.c.ps.bs as int, a - 1) == kk + (a - 1 - bi * pri::RUN_ROWS) / ri);
        }
        true
    } else {
        a == 0 || ps_key(e, a - 1, Ghost(ng)) != k
    };
    // The neighbour at `b`: inside the block it is one run step higher; at the block's end it is read.
    let hi_ok = if b == n {
        true
    } else if b - s < 65536 {
        proof {
            lemma_run_step(ri, rper as int, bi, j as int, ri);
            assert(fv32(e.c.ps.key_c@, e.c.ps.key_b@, e.c.ps.bs as int, b as int) == kk + (b - bi * pri::RUN_ROWS) / ri);
        }
        true
    } else {
        ps_key(e, b, Ghost(ng)) != k
    };
    lo_ok && hi_ok
}

/// A checked guess on sorted partsupp holds exactly the rows of key `k`.
pub proof fn lemma_guess_rows(e: PairEnv, ng: int, k: int, a: int, b: int)
    requires env_ok(e, ng), e.c.ps.kind == 1, guess_ok(e, k, a, b),
    ensures rows_of(e, k, a, b, true),
{
    assert forall|i: int| 0 <= i < e.c.ps.n && #[trigger] pskey(e.c.ps, i) == k implies a <= i < b by {
        if i < a {
            lemma_ps_sorted(e, ng, i, a - 1);
            lemma_ps_sorted(e, ng, a - 1, a);
        }
        if i >= b {
            lemma_ps_sorted(e, ng, b - 1, b);
            lemma_ps_sorted(e, ng, b, i);
        }
    }
    assert forall|i: int| a <= i < b implies #[trigger] pskey(e.c.ps, i) == k by {
        lemma_ps_sorted(e, ng, a, i);
        lemma_ps_sorted(e, ng, i, b - 1);
    }
}

/// The partsupp rows of key `k` of part row `j`.
#[inline(always)]
pub fn ps_rows_of(e: &PairEnv, j: usize, k: i64, Ghost(ng): Ghost<int>) -> (r: (usize, usize, bool))
    requires env_ok(*e, ng),
    ensures rows_of(*e, k as int, r.0 as int, r.1 as int, r.2),
    no_unwind
{
    let n = e.c.ps.n;
    if e.c.ps.kind != 1 {
        return (0, n, false);
    }
    let r = e.ratio;
    if r > 0 && j < e.jmax {
        proof {
            assert(j * r + r <= e.jmax * r) by (nonlinear_arith) requires j < e.jmax, r > 0;
        }
        let a = j * r;
        let b = a + r;
        if run_guess(e, j, k, Ghost(ng)) || (ps_key(e, a, Ghost(ng)) == k && ps_key(e, b - 1, Ghost(ng)) == k
            && (a == 0 || ps_key(e, a - 1, Ghost(ng)) != k) && (b == n || ps_key(e, b, Ghost(ng)) != k)) {
            proof {
                assert(guess_ok(*e, k as int, a as int, b as int));
                assert forall|i: int| 0 <= i < e.c.ps.n && #[trigger] pskey(e.c.ps, i) == k implies a <= i < b by {
                    if i < a {
                        lemma_ps_sorted(*e, ng, i, a - 1);
                        lemma_ps_sorted(*e, ng, a - 1, a as int);
                    }
                    if i >= b {
                        lemma_ps_sorted(*e, ng, b - 1, b as int);
                        lemma_ps_sorted(*e, ng, b as int, i);
                    }
                }
                assert forall|i: int| a <= i < b implies #[trigger] pskey(e.c.ps, i) == k by {
                    lemma_ps_sorted(*e, ng, a as int, i);
                    lemma_ps_sorted(*e, ng, i, b - 1);
                }
            }
            return (a, b, true);
        }
    }
    let (a, b) = sk::key_range(e.c.ps.key_c, e.c.ps.key_b, e.c.e32, e.c.e64, e.c.ps.bs, e.c.ps.kind, n, k as i128);
    proof {
        assert forall|i: int| 0 <= i < e.c.ps.n && #[trigger] pskey(e.c.ps, i) == k implies a <= i < b by {
            assert(sk::irow(e.c.ps.kind, e.c.e32@, e.c.e64@, e.c.ps.bs as int, i) == i);
            assert(sk::fkey(e.c.ps.key_c@, e.c.ps.key_b@, e.c.ps.bs as int, i) == pskey(e.c.ps, i));
        }
        assert forall|i: int| a <= i < b implies #[trigger] pskey(e.c.ps, i) == k by {
            assert(sk::irow(e.c.ps.kind, e.c.e32@, e.c.e64@, e.c.ps.bs as int, i) == i);
            assert(sk::fkey(e.c.ps.key_c@, e.c.ps.key_b@, e.c.ps.bs as int, i) == pskey(e.c.ps, i));
        }
    }
    (a, b, true)
}

/// The supplier row of key `key`, if any.
#[inline(always)]
pub fn supp_of(e: &PairEnv, key: i64, Ghost(ng): Ghost<int>) -> (r: Option<usize>)
    requires env_ok(*e, ng),
    ensures
        r matches Some(s) ==> s < e.c.s.n && skey(e.c.s, s as int) == key,
        r is None ==> forall|s: int| 0 <= s < e.c.s.n ==> #[trigger] skey(e.c.s, s) != key,
    no_unwind
{
    if e.sdense {
        let d: i128 = key as i128 - e.sfirst as i128;
        if 0 <= d && d < e.c.s.n as i128 {
            Some(d as usize)
        } else {
            None
        }
    } else {
        let r = sk::key_find(e.c.s.key_c, e.c.s.key_b, e.c.e32, e.c.e64, e.c.s.bs, e.c.s.kind, e.c.s.n, key as i128);
        proof {
            assert forall|s: int| 0 <= s < e.c.s.n implies sk::fkey(e.c.s.key_c@, e.c.s.key_b@, e.c.s.bs as int, s)
                == #[trigger] skey(e.c.s, s) by {}
        }
        r
    }
}

// ------------------------------------------------------------------------------------------------ block tables

/// The brand table entry of dictionary index `b`: its term, or `NONE_BIT`.
pub open spec fn bt_of(q: QualTabs, b: int) -> u32 {
    if 0 <= b < q.bterm@.len() && q.bterm@[b] != NONE32 { q.bterm@[b] } else { NONE_BIT }
}

pub open spec fn tt_of(q: QualTabs, t: int) -> u32 {
    if 0 <= t < q.tterm@.len() && q.tterm@[t] != NONE32 { q.tterm@[t] } else { NONE_BIT }
}

/// The size table entry of value `v`: its slot, or `NONE_BIT`.
pub open spec fn st_of(q: QualTabs, v: int) -> u32 {
    if listed(q.sizes@, v) { slot_of(q.sizes@, v) as u32 } else { NONE_BIT }
}

/// The tables of the part block with bases `bb`, `tb`, `sb`.
pub open spec fn block_ok(q: QualTabs, bb: u64, tb: u64, sb: i64, btab: [u32; 256], ttab: [u32; 256], stab: [u32; 256]) -> bool {
    &&& forall|c: int| 0 <= c < 256 ==> #[trigger] btab@[c] == bt_of(q, bb + c)
    &&& forall|c: int| 0 <= c < 256 ==> #[trigger] ttab@[c] == tt_of(q, tb + c)
    &&& forall|c: int| 0 <= c < 256 ==> #[trigger] stab@[c] == st_of(q, sb + c)
}

/// The listed slot is the one found by scanning (the sizes are distinct).
proof fn lemma_slot_unique(sizes: Seq<i64>, v: int, z: int)
    requires sizes.no_duplicates(), 0 <= z < sizes.len(), sizes[z] == v,
    ensures listed(sizes, v), slot_of(sizes, v) == z,
{
    let w = slot_of(sizes, v);
    assert(sizes[w] == v);
}

pub fn block_tabs(q: &QualTabs, nb: usize, nt: usize, ns: usize, bb: u64, tb: u64, sb: i64, btab: &mut [u32; 256],
    ttab: &mut [u32; 256], stab: &mut [u32; 256], Ghost(ng): Ghost<int>)
    requires
        tabs_shape(*q, nb as int, nt as int, ng),
        ns == q.sizes@.len(),
    ensures block_ok(*q, bb, tb, sb, *final(btab), *final(ttab), *final(stab)),
    no_unwind
{
    let mut c: usize = 0;
    while c < 256
        invariant
            c <= 256,
            tabs_shape(*q, nb as int, nt as int, ng),
            ns == q.sizes@.len(),
            forall|d: int| 0 <= d < c ==> #[trigger] btab@[d] == bt_of(*q, bb + d),
            forall|d: int| 0 <= d < c ==> #[trigger] ttab@[d] == tt_of(*q, tb + d),
            forall|d: int| 0 <= d < c ==> #[trigger] stab@[d] == st_of(*q, sb + d),
        decreases 256 - c,
    {
        let b: u128 = bb as u128 + c as u128;
        let bt = if b < nb as u128 { q.bterm[b as usize] } else { NONE32 };
        btab[c] = if bt == NONE32 { NONE_BIT } else { bt };
        let t: u128 = tb as u128 + c as u128;
        let tt = if t < nt as u128 { q.tterm[t as usize] } else { NONE32 };
        ttab[c] = if tt == NONE32 { NONE_BIT } else { tt };
        let v: i128 = sb as i128 + c as i128;
        let mut z: usize = 0;
        let mut slot: u32 = NONE_BIT;
        while z < ns
            invariant
                z <= ns, ns == q.sizes@.len(), ns <= 8,
                q.sizes@.no_duplicates(),
                slot == NONE_BIT ==> forall|y: int| 0 <= y < z ==> #[trigger] q.sizes@[y] != v,
                slot != NONE_BIT ==> slot < z && q.sizes@[slot as int] == v,
            decreases ns - z,
        {
            if q.sizes[z] as i128 == v {
                slot = z as u32;
            }
            z = z + 1;
        }
        proof {
            if slot != NONE_BIT {
                lemma_slot_unique(q.sizes@, v as int, slot as int);
            } else {
                if listed(q.sizes@, v as int) {
                    let y = choose|y: int| 0 <= y < q.sizes@.len() && q.sizes@[y] == v as int;
                    assert(q.sizes@[y] != v);
                }
            }
        }
        stab[c] = slot;
        c = c + 1;
    }
}

/// The bit test of the three table entries: all exist exactly when the row is coded, and then their sum is its code.
pub proof fn lemma_code_bits(q: QualTabs, p: PCols, j: int, nb: int, nt: int, ng: int, x: u32, y: u32, z: u32)
    requires
        tabs_shape(q, nb, nt, ng),
        x == bt_of(q, bidx(p, j)),
        y == tt_of(q, tidx(p, j)),
        z == st_of(q, sval(p, j)),
    ensures
        ((x | y | z) & NONE_BIT == 0) == coded(q, p, j),
        coded(q, p, j) ==> x + y + z == code_of(q, p, j) && code_of(q, p, j) < ng,
{
    let (b, t, v) = (bidx(p, j), tidx(p, j), sval(p, j));
    lemma_or3(x, y, z);
    if listed(q.sizes@, v) {
        let w = slot_of(q.sizes@, v);
        assert(0 <= w < q.sizes@.len() <= 8);
    }
    let bok = 0 <= b < q.bterm@.len() && q.bterm@[b] != NONE32;
    let tok = 0 <= t < q.tterm@.len() && q.tterm@[t] != NONE32;
    if bok && tok {
        assert(q.bterm@[b] + q.tterm@[t] + q.sizes@.len() <= ng);
    }
    // An existing term with no partner of the other kind can still be large; then the row is not coded and the
    // missing entry alone sets the bit.
}

/// `(x | y | z) & 2^31` is zero exactly when all three are below `2^31`.
proof fn lemma_or3(x: u32, y: u32, z: u32)
    by (bit_vector)
    ensures ((x | y | z) & 0x8000_0000u32 == 0u32) == (x < 0x8000_0000u32 && y < 0x8000_0000u32 && z < 0x8000_0000u32),
{
}

// ------------------------------------------------------------------------------------------------ pair tasks

/// Part rows `[lo, hi)`: the pairs of their partsupp rows, grouped by local group.
pub struct PairTask<S: SIdx> {
    pub env: Arc<PairEnv>,
    pub ng: usize,
    pub lo: usize,
    pub hi: usize,
    /// Scratch: the pairs (local group, supplier row) in scan order (`cap` entries each).
    pub tmp_g: Vec<u32>,
    pub tmp_s: Vec<S>,
    pub cap: usize,
    /// Scratch: the code tables of the current part block.
    pub btab: [u32; 256],
    pub ttab: [u32; 256],
    pub stab: [u32; 256],
    /// Output: supplier rows grouped by local group (`cap` entries), and the group offsets (`ng + 1`, all zero).
    pub out: Vec<S>,
    pub offs: Vec<usize>,
    /// The supplier rows this task decides for the subquery.
    pub supp: SuppTask,
}

pub struct PairOut<S: SIdx> {
    pub out: Vec<S>,
    pub offs: Vec<usize>,
    pub supp: SuppOut,
    /// False when the scratch was too small (the task stopped; run it again with more room).
    pub done: bool,
}

/// Group `g`'s segment of a pair task's output holds `x`.
pub open spec fn seg_has<S: SIdx>(po: PairOut<S>, g: int, x: int) -> bool {
    exists|p: int| po.offs@[g] <= p < po.offs@[g + 1] && #[trigger] po.out@[p].sx() == x
}

/// A finished pair task's output over part rows `[lo, hi)`: segment `g` holds exactly the supplier rows of the
/// pairs of `g`.
pub open spec fn pairs_out<S: SIdx>(q: QualTabs, c: Cols, lo: int, hi: int, ng: int, po: PairOut<S>) -> bool {
    &&& po.offs@.len() == ng + 1
    &&& po.offs@[0] == 0
    &&& po.offs@[ng] <= po.out@.len()
    &&& forall|g: int| 0 <= g < ng ==> #[trigger] po.offs@[g] <= po.offs@[g + 1]
    &&& forall|g: int, x: int| 0 <= g < ng ==> (#[trigger] seg_has(po, g, x) <==> pair_in(q, c, lo, hi, g, x))
}

/// The pairs in the scratch so far.
pub open spec fn tmp_has<S: SIdx>(tg: Seq<u32>, ts: Seq<S>, cnt: int, g: int, x: int) -> bool {
    exists|k: int| 0 <= k < cnt && tg[k] as int == g && #[trigger] ts[k].sx() == x
}

/// Partsupp row `i` has the key of a part row of `[lo, hi)`.
pub open spec fn row_of_parts(c: Cols, lo: int, hi: int, i: int) -> bool {
    exists|j: int| lo <= j < hi && #[trigger] pkey(c.p, j) == pskey(c.ps, i)
}

/// The scan state after the parts `[lo, j)`: the scratch holds exactly their pairs; the set `emitted` of partsupp
/// rows that gave a pair has one row per pair.
pub open spec fn scan_ok<S: SIdx>(q: QualTabs, c: Cols, ng: int, lo: int, j: int, tg: Seq<u32>, ts: Seq<S>, cnt: int,
    emitted: Set<int>) -> bool {
    &&& 0 <= cnt <= tg.len() && cnt <= ts.len()
    &&& forall|k: int| 0 <= k < cnt ==> (#[trigger] tg[k]) < ng
    &&& forall|g: int, x: int| #[trigger] tmp_has(tg, ts, cnt, g, x) <==> pair_in(q, c, lo, j, g, x)
    &&& cnt == emitted.len()
    &&& forall|i: int| #[trigger] emitted.contains(i) ==> 0 <= i < c.ps.n && row_of_parts(c, lo, j, i)
}

/// The scan state inside part row `j` after its partsupp rows below `i` (of `[a, b)`).
pub open spec fn inner_ok<S: SIdx>(q: QualTabs, c: Cols, ng: int, lo: int, j: int, a: int, i: int, k: int, tg: Seq<u32>,
    ts: Seq<S>, cnt: int, emitted: Set<int>) -> bool {
    &&& 0 <= cnt <= tg.len() && cnt <= ts.len()
    &&& forall|q2: int| 0 <= q2 < cnt ==> (#[trigger] tg[q2]) < ng
    &&& forall|g2: int, x2: int| #[trigger] tmp_has(tg, ts, cnt, g2, x2) <==>
        (pair_in(q, c, lo, j, g2, x2) || exists|i2: int| a <= i2 < i && #[trigger] pair_at(q, c, j, i2, g2, x2))
    &&& cnt == emitted.len()
    &&& forall|i2: int| #[trigger] emitted.contains(i2) ==> 0 <= i2 < c.ps.n
        && (row_of_parts(c, lo, j, i2) || (i2 < i && pskey(c.ps, i2) == k))
}

impl<S: SIdx> WorkerTask for PairTask<S> {
    type Output = PairOut<S>;

    open spec fn pre(&self) -> bool {
        &&& env_ok(*self.env, self.ng as int)
        &&& self.lo <= self.hi <= self.env.c.p.n
        &&& self.ng + 1 < usize::MAX
        &&& self.tmp_g@.len() == self.cap && self.tmp_s@.len() == self.cap && self.out@.len() == self.cap
        &&& self.offs@.len() == self.ng + 1
        &&& forall|g: int| 0 <= g <= self.ng ==> #[trigger] self.offs@[g] == 0
        &&& self.env.c.s.n as int <= S::lim()
        &&& self.supp.pre()
    }

    open spec fn post(&self, out: PairOut<S>) -> bool {
        &&& out.done ==> pairs_out(*self.env.tabs, self.env.c, self.lo as int, self.hi as int, self.ng as int, out)
        &&& self.cap >= self.env.c.ps.n ==> out.done
        &&& self.supp.post(out.supp)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: PairOut<S>) {
        let PairTask { env, ng, lo, hi, tmp_g, tmp_s, cap, btab, ttab, stab, out, offs, supp } = self;
        let so = supp.run();
        let mut tmp_g = tmp_g;
        let mut tmp_s = tmp_s;
        let mut btab = btab;
        let mut ttab = ttab;
        let mut stab = stab;
        let mut out = out;
        let mut offs = offs;
        let e: &PairEnv = &*env;
        let q: &QualTabs = &*e.tabs;
        let ghost c = e.c;
        let ghost ngi = ng as int;
        let pbs = e.c.p.bs;
        let mut cnt: usize = 0;
        let ghost mut emitted: Set<int> = Set::empty();
        let mut j = lo;
        proof {
            assert forall|g: int, x: int| #[trigger] tmp_has(tmp_g@, tmp_s@, 0, g, x) <==> pair_in(*q, c, lo as int, lo as int, g, x) by {}
        }
        while j < hi
            invariant
                env_ok(*e, ngi), ngi == ng,
                c == e.c, *q == *e.tabs,
                self.cap == cap, self.env.c == c, c.s.n as int <= S::lim(), self.supp.post(so),
                lo <= j <= hi <= c.p.n,
                pbs == c.p.bs,
                tmp_g@.len() == cap && tmp_s@.len() == cap,
                scan_ok(*q, c, ngi, lo as int, j as int, tmp_g@, tmp_s@, cnt as int, emitted),
                cap >= c.ps.n ==> cnt <= c.ps.n,
            decreases hi - j,
        {
            let g = j / pbs;
            proof {
                lemma_grp_bound(c.p.n as int, pbs as int, c.p.ng as int, j as int);
                lemma_block_start(j as int, pbs as int);
            }
            let gs = g * pbs;
            let seg_end = if hi - gs > pbs { gs + pbs } else { hi };
            proof {
                assert((g + 1) * pbs == g * pbs + pbs) by (nonlinear_arith);
            }
            let bb = e.c.p.brand_b[g];
            let tb = e.c.p.type_b[g];
            let sb = e.c.p.size_b[g];
            block_tabs(q, e.nb, e.nt, e.ns, bb, tb, sb, &mut btab, &mut ttab, &mut stab, Ghost(ngi));
            let kb = e.c.p.key_b[g];
            let bcodes = e.c.p.brand_c;
            let tcodes = e.c.p.type_c;
            let scodes = e.c.p.size_c;
            let kcodes = e.c.p.key_c;
            while j < seg_end
                invariant
                    env_ok(*e, ngi), ngi == ng,
                    c == e.c, *q == *e.tabs,
                    self.cap == cap, self.env.c == c, c.s.n as int <= S::lim(), self.supp.post(so),
                    lo <= j <= seg_end <= hi <= c.p.n,
                    seg_end <= (g + 1) * pbs,
                    g * pbs <= j,
                    g < c.p.ng,
                    pbs == c.p.bs,
                    bb == c.p.brand_b@[g as int], tb == c.p.type_b@[g as int], sb == c.p.size_b@[g as int],
                    kb == c.p.key_b@[g as int],
                    bcodes@ == c.p.brand_c@, tcodes@ == c.p.type_c@, scodes@ == c.p.size_c@, kcodes@ == c.p.key_c@,
                    block_ok(*q, bb, tb, sb, btab, ttab, stab),
                    tmp_g@.len() == cap && tmp_s@.len() == cap,
                    scan_ok(*q, c, ngi, lo as int, j as int, tmp_g@, tmp_s@, cnt as int, emitted),
                    cap >= c.ps.n ==> cnt <= c.ps.n,
                decreases seg_end - j,
            {
                proof {
                    assert((g + 1) * pbs == g * pbs + pbs) by (nonlinear_arith);
                    lemma_in_group(pbs as int, g as int, j as int);
                }
                let x = btab[bcodes[j] as usize];
                let y = ttab[tcodes[j] as usize];
                let z = stab[scodes[j] as usize];
                proof {
                    lemma_code_bits(*q, c.p, j as int, e.nb as int, e.nt as int, ngi, x, y, z);
                }
                if (x | y | z) & NONE_BIT == 0 {
                    let code: u32 = x + y + z;
                    proof {
                        assert(i64r(pkey(c.p, j as int)));
                    }
                    let k = kb + kcodes[j] as i64;
                    let (a, b, exact) = ps_rows_of(e, j, k, Ghost(ngi));
                    let mut i = a;
                    proof {
                        lemma_inner_start(*q, c, ngi, lo as int, j as int, a as int, k as int, tmp_g@, tmp_s@, cnt as int,
                            emitted);
                    }
                    while i < b
                        invariant
                            env_ok(*e, ngi), ngi == ng,
                            c == e.c, *q == *e.tabs,
                            self.cap == cap, self.env.c == c, c.s.n as int <= S::lim(), self.supp.post(so),
                            lo <= j < hi <= c.p.n,
                            coded(*q, c.p, j as int), code_of(*q, c.p, j as int) == code as int, (code as int) < ngi,
                            k as int == pkey(c.p, j as int),
                            rows_of(*e, k as int, a as int, b as int, exact),
                            a <= i <= b,
                            tmp_g@.len() == cap && tmp_s@.len() == cap,
                            inner_ok(*q, c, ngi, lo as int, j as int, a as int, i as int, k as int, tmp_g@, tmp_s@,
                                cnt as int, emitted),
                            cap >= c.ps.n ==> cnt <= c.ps.n,
                        decreases b - i,
                    {
                        let ghost i0 = i as int;
                        if exact || ps_key(e, i, Ghost(ngi)) == k {
                            proof {
                                if exact { assert(pskey(c.ps, i as int) == k); }
                            }
                            let skv = ps_supp(e, i, Ghost(ngi));
                            match supp_of(e, skv, Ghost(ngi)) {
                                Some(sj) => {
                                    proof {
                                        lemma_fresh(*e, ngi, lo as int, j as int, i as int, k as int, emitted);
                                        vstd::set::lemma_set_insert_len(emitted, i as int);
                                        if cap >= c.ps.n {
                                            lemma_emitted_bound(emitted.insert(i as int), c.ps.n as int);
                                        }
                                    }
                                    if cnt >= cap {
                                        proof {
                                            assert(cap < c.ps.n);
                                        }
                                        return PairOut { out, offs, done: false, supp: so };
                                    }
                                    let ghost tg0 = tmp_g@;
                                    let ghost ts0 = tmp_s@;
                                    tmp_g[cnt] = code;
                                    let sv = S::of_usize(sj);
                                    tmp_s[cnt] = sv;
                                    proof {
                                        lemma_inner_emit(*q, *e, c, ngi, lo as int, j as int, a as int, i as int, k as int,
                                            code as int, sj as int, sv, tg0, ts0, tmp_g@, tmp_s@, cnt as int, emitted);
                                        emitted = emitted.insert(i as int);
                                    }
                                    cnt = cnt + 1;
                                },
                                None => {
                                    proof {
                                        lemma_inner_skip(*q, c, ngi, lo as int, j as int, a as int, i as int, k as int,
                                            tmp_g@, tmp_s@, cnt as int, emitted);
                                    }
                                },
                            }
                        } else {
                            proof {
                                lemma_inner_skip(*q, c, ngi, lo as int, j as int, a as int, i as int, k as int,
                                    tmp_g@, tmp_s@, cnt as int, emitted);
                            }
                        }
                        i = i + 1;
                    }
                    proof {
                        lemma_part_done(*q, c, *e, ngi, lo as int, j as int, a as int, b as int, exact, tmp_g@, tmp_s@,
                            cnt as int, emitted, k as int);
                    }
                } else {
                    proof {
                        lemma_part_skip(*q, c, ngi, lo as int, j as int, tmp_g@, tmp_s@, cnt as int, emitted);
                    }
                }
                j = j + 1;
            }
        }
        // Group the pairs by local group.
        scatter(&tmp_g, &tmp_s, cnt, ng, &mut offs, &mut out);
        let r = PairOut { out, offs, done: true, supp: so };
        proof {
            lemma_pairs_out(*q, c, lo as int, hi as int, ngi, tmp_g@, tmp_s@, cnt as int, r);
        }
        r
    }
}

/// Row `j` of blocks of `bs` rows lies in block `j / bs`: `g * bs <= j < (g + 1) * bs`.
pub proof fn lemma_block_start(j: int, bs: int)
    requires j >= 0, bs >= 1,
    ensures (j / bs) * bs <= j < (j / bs + 1) * bs, j / bs >= 0,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, bs);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(j, bs);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(j, bs);
    assert(bs * (j / bs) == (j / bs) * bs) by (nonlinear_arith);
    assert((j / bs + 1) * bs == (j / bs) * bs + bs) by (nonlinear_arith);
}

/// The emitted rows are rows of partsupp, so at most its row count.
proof fn lemma_emitted_bound(s: Set<int>, n: int)
    requires n >= 0, forall|i: int| #[trigger] s.contains(i) ==> 0 <= i < n,
    ensures s.len() <= n,
{
    vstd::set_lib::lemma_int_range(0, n);
    assert(s.subset_of(Set::range(0int, n)));
    vstd::set_lib::lemma_len_subset(s, Set::range(0int, n));
}

/// A partsupp row of part row `j`'s key is not yet emitted: emitted rows have earlier parts' keys (other keys, part
/// keys being unique) or are earlier rows of this part.
proof fn lemma_fresh(e: PairEnv, ng: int, lo: int, j: int, i: int, k: int, emitted: Set<int>)
    requires
        env_ok(e, ng),
        0 <= lo <= j < e.c.p.n,
        k == pkey(e.c.p, j),
        pskey(e.c.ps, i) == k,
        forall|i2: int| #[trigger] emitted.contains(i2) ==> 0 <= i2 < e.c.ps.n
            && (row_of_parts(e.c, lo, j, i2) || (i2 < i && pskey(e.c.ps, i2) == k)),
    ensures !emitted.contains(i),
{
    if emitted.contains(i) {
        if row_of_parts(e.c, lo, j, i) {
            let j2 = choose|j2: int| lo <= j2 < j && #[trigger] pkey(e.c.p, j2) == pskey(e.c.ps, i);
            assert(pkey(e.c.p, j2) == pkey(e.c.p, j));
        }
    }
}

/// Appending one pair to the scratch.
pub proof fn lemma_tmp_push<S: SIdx>(tg: Seq<u32>, ts: Seq<S>, cnt: int, g: int, x: int)
    requires 0 <= cnt < tg.len(), cnt < ts.len(),
    ensures tmp_has(tg, ts, cnt + 1, g, x) <==> (tmp_has(tg, ts, cnt, g, x) || (tg[cnt] as int == g && ts[cnt].sx() == x)),
{
    if tmp_has(tg, ts, cnt + 1, g, x) {
        let k = choose|k: int| 0 <= k < cnt + 1 && tg[k] as int == g && #[trigger] ts[k].sx() == x;
        if k < cnt {
            assert(tmp_has(tg, ts, cnt, g, x));
        }
    }
}

/// Writing slot `cnt` keeps the pairs below it.
pub proof fn lemma_tmp_write<S: SIdx>(tg0: Seq<u32>, ts0: Seq<S>, tg: Seq<u32>, ts: Seq<S>, cnt: int, g: int, x: int)
    requires
        0 <= cnt < tg0.len(), cnt < ts0.len(),
        tg == tg0.update(cnt, tg[cnt]), ts == ts0.update(cnt, ts[cnt]),
    ensures tmp_has(tg, ts, cnt, g, x) == tmp_has(tg0, ts0, cnt, g, x),
{
    if tmp_has(tg, ts, cnt, g, x) {
        let k = choose|k: int| 0 <= k < cnt && tg[k] as int == g && #[trigger] ts[k].sx() == x;
        assert(tg0[k] == tg[k] && ts0[k] == ts[k]);
    }
    if tmp_has(tg0, ts0, cnt, g, x) {
        let k = choose|k: int| 0 <= k < cnt && tg0[k] as int == g && #[trigger] ts0[k].sx() == x;
        assert(tg0[k] == tg[k] && ts0[k] == ts[k]);
    }
}

/// The inner scan starts with the parts `[lo, j)`'s pairs.
proof fn lemma_inner_start<S: SIdx>(q: QualTabs, c: Cols, ng: int, lo: int, j: int, a: int, k: int, tg: Seq<u32>, ts: Seq<S>,
    cnt: int, emitted: Set<int>)
    requires scan_ok(q, c, ng, lo, j, tg, ts, cnt, emitted),
    ensures inner_ok(q, c, ng, lo, j, a, a, k, tg, ts, cnt, emitted),
{
}

/// Emitting the pair (`code`, `sj`) of partsupp row `i`.
proof fn lemma_inner_emit<S: SIdx>(q: QualTabs, e: PairEnv, c: Cols, ng: int, lo: int, j: int, a: int, i: int, k: int,
    code: int, sj: int, sv: S, tg0: Seq<u32>, ts0: Seq<S>, tg: Seq<u32>, ts: Seq<S>, cnt: int, emitted: Set<int>)
    requires
        env_ok(e, ng), e.c == c, q == *e.tabs,
        0 <= lo <= j < c.p.n,
        coded(q, c.p, j), code_of(q, c.p, j) == code, 0 <= code < ng,
        k == pkey(c.p, j),
        0 <= a <= i < c.ps.n,
        pskey(c.ps, i) == k,
        0 <= sj < c.s.n, skey(c.s, sj) == pssupp(c.ps, i),
        inner_ok(q, c, ng, lo, j, a, i, k, tg0, ts0, cnt, emitted),
        !emitted.contains(i),
        0 <= cnt < tg0.len(), tg0.len() == tg.len(), ts0.len() == ts.len(), cnt < ts0.len(),
        tg == tg0.update(cnt, code as u32), ts == ts0.update(cnt, sv), sv.sx() == sj,
    ensures inner_ok(q, c, ng, lo, j, a, i + 1, k, tg, ts, cnt + 1, emitted.insert(i)),
{
    assert(pair_at(q, c, j, i, code, sj));
    assert forall|g2: int, x2: int| #[trigger] tmp_has(tg, ts, cnt + 1, g2, x2) <==>
        (pair_in(q, c, lo, j, g2, x2) || exists|i2: int| a <= i2 < i + 1 && #[trigger] pair_at(q, c, j, i2, g2, x2)) by {
        lemma_tmp_push(tg, ts, cnt, g2, x2);
        lemma_tmp_write(tg0, ts0, tg, ts, cnt, g2, x2);
        if exists|i2: int| a <= i2 < i + 1 && #[trigger] pair_at(q, c, j, i2, g2, x2) {
            let i2 = choose|i2: int| a <= i2 < i + 1 && #[trigger] pair_at(q, c, j, i2, g2, x2);
            if i2 == i {
                assert(skey(c.s, x2) == skey(c.s, sj));
            } else {
                assert(exists|i3: int| a <= i3 < i && #[trigger] pair_at(q, c, j, i3, g2, x2));
            }
        }
        if exists|i2: int| a <= i2 < i && #[trigger] pair_at(q, c, j, i2, g2, x2) {
            let i2 = choose|i2: int| a <= i2 < i && #[trigger] pair_at(q, c, j, i2, g2, x2);
            assert(a <= i2 < i + 1);
        }
    }
    assert forall|q2: int| 0 <= q2 < cnt + 1 implies (#[trigger] tg[q2]) < ng by {
        if q2 < cnt { assert(tg[q2] == tg0[q2]); }
    }
    vstd::set::lemma_set_insert_len(emitted, i);
}

/// Partsupp row `i` adds no pair (another key, or no supplier row of its suppkey).
proof fn lemma_inner_skip<S: SIdx>(q: QualTabs, c: Cols, ng: int, lo: int, j: int, a: int, i: int, k: int, tg: Seq<u32>,
    ts: Seq<S>, cnt: int, emitted: Set<int>)
    requires
        inner_ok(q, c, ng, lo, j, a, i, k, tg, ts, cnt, emitted),
        k == pkey(c.p, j),
        pskey(c.ps, i) != k || forall|s: int| 0 <= s < c.s.n ==> #[trigger] skey(c.s, s) != pssupp(c.ps, i),
    ensures inner_ok(q, c, ng, lo, j, a, i + 1, k, tg, ts, cnt, emitted),
{
    assert forall|g2: int, x2: int| #[trigger] tmp_has(tg, ts, cnt, g2, x2) <==>
        (pair_in(q, c, lo, j, g2, x2) || exists|i2: int| a <= i2 < i + 1 && #[trigger] pair_at(q, c, j, i2, g2, x2)) by {
        if exists|i2: int| a <= i2 < i + 1 && #[trigger] pair_at(q, c, j, i2, g2, x2) {
            let i2 = choose|i2: int| a <= i2 < i + 1 && #[trigger] pair_at(q, c, j, i2, g2, x2);
            if i2 == i {
                assert(skey(c.s, x2) == pssupp(c.ps, i));
            } else {
                assert(exists|i3: int| a <= i3 < i && #[trigger] pair_at(q, c, j, i3, g2, x2));
            }
        }
    }
}

/// A part row that is not coded adds no pair.
proof fn lemma_part_skip<S: SIdx>(q: QualTabs, c: Cols, ng: int, lo: int, j: int, tg: Seq<u32>, ts: Seq<S>, cnt: int,
    emitted: Set<int>)
    requires
        lo <= j,
        !coded(q, c.p, j),
        scan_ok(q, c, ng, lo, j, tg, ts, cnt, emitted),
    ensures scan_ok(q, c, ng, lo, j + 1, tg, ts, cnt, emitted),
{
    assert forall|g: int, x: int| #[trigger] tmp_has(tg, ts, cnt, g, x) <==> pair_in(q, c, lo, j + 1, g, x) by {
        if pair_in(q, c, lo, j + 1, g, x) {
            let (j2, i2) = choose|j2: int, i2: int| lo <= j2 < j + 1 && #[trigger] pair_at(q, c, j2, i2, g, x);
            assert(j2 != j);
            assert(pair_in(q, c, lo, j, g, x));
        }
        if pair_in(q, c, lo, j, g, x) {
            let (j2, i2) = choose|j2: int, i2: int| lo <= j2 < j && #[trigger] pair_at(q, c, j2, i2, g, x);
            assert(lo <= j2 < j + 1);
        }
    }
    assert forall|i: int| #[trigger] emitted.contains(i) implies 0 <= i < c.ps.n && row_of_parts(c, lo, j + 1, i) by {
        let j2 = choose|j2: int| lo <= j2 < j && #[trigger] pkey(c.p, j2) == pskey(c.ps, i);
        assert(lo <= j2 < j + 1);
    }
}

/// After all partsupp rows of a coded part row: the scratch holds the pairs of the parts `[lo, j + 1)`.
proof fn lemma_part_done<S: SIdx>(q: QualTabs, c: Cols, e: PairEnv, ng: int, lo: int, j: int, a: int, b: int, exact: bool,
    tg: Seq<u32>, ts: Seq<S>, cnt: int, emitted: Set<int>, k: int)
    requires
        e.c == c, q == *e.tabs,
        lo <= j,
        coded(q, c.p, j),
        k == pkey(c.p, j),
        rows_of(e, k, a, b, exact),
        inner_ok(q, c, ng, lo, j, a, b, k, tg, ts, cnt, emitted),
    ensures scan_ok(q, c, ng, lo, j + 1, tg, ts, cnt, emitted),
{
    assert forall|g: int, x: int| #[trigger] tmp_has(tg, ts, cnt, g, x) <==> pair_in(q, c, lo, j + 1, g, x) by {
        if pair_in(q, c, lo, j + 1, g, x) {
            let (j2, i2) = choose|j2: int, i2: int| lo <= j2 < j + 1 && #[trigger] pair_at(q, c, j2, i2, g, x);
            if j2 == j {
                assert(pskey(c.ps, i2) == k);
                assert(a <= i2 < b);
            } else {
                assert(pair_in(q, c, lo, j, g, x));
            }
        }
        if tmp_has(tg, ts, cnt, g, x) {
            if pair_in(q, c, lo, j, g, x) {
                let (j2, i2) = choose|j2: int, i2: int| lo <= j2 < j && #[trigger] pair_at(q, c, j2, i2, g, x);
                assert(lo <= j2 < j + 1);
            } else {
                let i2 = choose|i2: int| a <= i2 < b && #[trigger] pair_at(q, c, j, i2, g, x);
                assert(lo <= j < j + 1);
            }
        }
    }
    assert forall|i: int| #[trigger] emitted.contains(i) implies 0 <= i < c.ps.n && row_of_parts(c, lo, j + 1, i) by {
        if row_of_parts(c, lo, j, i) {
            let j2 = choose|j2: int| lo <= j2 < j && #[trigger] pkey(c.p, j2) == pskey(c.ps, i);
            assert(lo <= j2 < j + 1);
        } else {
            assert(pkey(c.p, j) == pskey(c.ps, i));
        }
    }
}

/// A value lies in `s[a .. b]` exactly when it lies in the subrange as a sequence.
pub proof fn lemma_sub_has<S: SIdx>(s: Seq<S>, a: int, b: int, x: int)
    requires 0 <= a <= b <= s.len(),
    ensures
        (exists|p: int| a <= p < b && #[trigger] s[p].sx() == x)
            <==> (exists|w: int| 0 <= w < s.subrange(a, b).len() && s.subrange(a, b)[w].sx() == x),
{
    let t = s.subrange(a, b);
    if exists|p: int| a <= p < b && #[trigger] s[p].sx() == x {
        let p = choose|p: int| a <= p < b && #[trigger] s[p].sx() == x;
        assert(t[p - a] == s[p]);
    }
    if exists|w: int| 0 <= w < t.len() && t[w].sx() == x {
        let w = choose|w: int| 0 <= w < t.len() && t[w].sx() == x;
        assert(s[a + w] == t[w]);
    }
}

/// One group's segment holds exactly the scratch's pairs of that group.
proof fn lemma_seg_group<S: SIdx>(tg: Seq<u32>, ts: Seq<S>, cnt: int, po: PairOut<S>, g: int, x: int)
    requires
        0 <= cnt <= tg.len(), cnt <= ts.len(),
        0 <= po.offs@[g] <= po.offs@[g + 1] <= po.out@.len(),
        po.out@.subrange(po.offs@[g] as int, po.offs@[g + 1] as int) == sel(tg, ts, cnt, g),
    ensures seg_has(po, g, x) <==> tmp_has(tg, ts, cnt, g, x),
{
    lemma_sub_has(po.out@, po.offs@[g] as int, po.offs@[g + 1] as int, x);
    lemma_sel_has(tg, ts, cnt, g, x);
}

/// Offsets of a sorted scratch are nondecreasing up to the pair count.
pub proof fn lemma_offs_bound<S: SIdx>(tg: Seq<u32>, ts: Seq<S>, cnt: int, ng: int, offs: Seq<usize>, out: Seq<S>, g: int)
    requires scattered(tg, ts, cnt, ng, offs, out), 0 <= g <= ng,
    ensures 0 <= offs[g] <= cnt,
    decreases ng - g,
{
    if g < ng {
        lemma_offs_bound(tg, ts, cnt, ng, offs, out, g + 1);
        assert(offs[g] <= offs[g + 1]);
    }
}

/// The scatter's segments hold the scratch's pairs by group.
proof fn lemma_pairs_out<S: SIdx>(q: QualTabs, c: Cols, lo: int, hi: int, ng: int, tg: Seq<u32>, ts: Seq<S>, cnt: int,
    po: PairOut<S>)
    requires
        scattered(tg, ts, cnt, ng, po.offs@, po.out@),
        forall|g: int, x: int| #[trigger] tmp_has(tg, ts, cnt, g, x) <==> pair_in(q, c, lo, hi, g, x),
        0 <= cnt <= tg.len(), cnt <= ts.len(),
    ensures pairs_out(q, c, lo, hi, ng, po),
{
    assert forall|g: int, x: int| 0 <= g < ng implies (#[trigger] seg_has(po, g, x) <==> pair_in(q, c, lo, hi, g, x)) by {
        lemma_offs_bound(tg, ts, cnt, ng, po.offs@, po.out@, g);
        lemma_offs_bound(tg, ts, cnt, ng, po.offs@, po.out@, g + 1);
        assert(po.offs@[g] <= po.offs@[g + 1]);
        lemma_seg_group(tg, ts, cnt, po, g, x);
    }
}

/// `sel` holds a value exactly when some pair of that key has it.
pub proof fn lemma_sel_has<S: SIdx>(tg: Seq<u32>, ts: Seq<S>, n: int, g: int, x: int)
    requires 0 <= n <= tg.len(), n <= ts.len(),
    ensures
        (exists|w: int| 0 <= w < sel(tg, ts, n, g).len() && sel(tg, ts, n, g)[w].sx() == x) <==> tmp_has(tg, ts, n, g, x),
    decreases n,
{
    if n > 0 {
        lemma_sel_has(tg, ts, n - 1, g, x);
        lemma_tmp_push(tg, ts, n - 1, g, x);
        let s0 = sel(tg, ts, n - 1, g);
        let s1 = sel(tg, ts, n, g);
        if (tg[n - 1] as int) == g {
            assert(s1 == s0.push(ts[n - 1]));
            if exists|w: int| 0 <= w < s1.len() && s1[w].sx() == x {
                let w = choose|w: int| 0 <= w < s1.len() && s1[w].sx() == x;
                if w < s0.len() {
                    assert(s0[w] == s1[w]);
                }
            }
            if exists|w: int| 0 <= w < s0.len() && s0[w].sx() == x {
                let w = choose|w: int| 0 <= w < s0.len() && s0[w].sx() == x;
                assert(s1[w] == s0[w]);
            }
            if ts[n - 1].sx() == x {
                assert(s1[s0.len() as int] == ts[n - 1]);
            }
        } else {
            assert(s1 == s0);
        }
    } else {
        assert(sel(tg, ts, 0, g).len() == 0);
    }
}

} // verus!
