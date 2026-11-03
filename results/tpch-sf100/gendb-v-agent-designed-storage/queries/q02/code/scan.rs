//! The Q2 candidate scan (`q2spec::chunk_ok`): part rows passing `p_size = $1 AND p_type LIKE $2`, their partsupp
//! rows (the key range of the part's partkey; partsupp is stored sorted by ps_partkey), whose supplier lies in
//! region `$3`, and among those the rows of minimal ps_supplycost. One candidate per qualifying (part, partsupp)
//! pair, in increasing (part, partsupp) order.
//!
//! A worker scans whole part groups; per group it first collects a batch of selected part rows (64 rows at a time
//! from a byte-compare mask of the p_size codes, `collect_block`, then the LIKE outcome per matching row), touches the
//! partsupp lines they need (independent loads that overlap their memory latency), then processes the batch in row
//! order. Its output buffer is preallocated; when the next part's candidates might not fit, the worker stops and
//! reports the row it stopped at, and the calling thread continues serially (`scan_rows_serial`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::work::put;
use crate::stores::suppliers::interface::common::keyidx::{key_find_guess, key_range, fkey, irow, lemma_sorted_le};
use super::tables::*;
use super::q2spec::*;
use super::common::bits::{bit, match_mask, lowest_bit, clear_bit, lemma_no_bit_of_zero};

verus! {

// ------------------------------------------------------------------------------------------------ state

/// A preallocated candidate buffer: `v[0 .. len]` are the candidates written so far; writes and resets never
/// allocate (usable in worker bodies).
pub struct CandBuf {
    pub v: Vec<Cand>,
    pub len: usize,
}

pub open spec fn buf_wf(b: CandBuf) -> bool {
    b.len <= b.v@.len()
}

pub open spec fn buf_view(b: CandBuf) -> Seq<Cand> {
    b.v@.subrange(0, b.len as int)
}

/// Per-call lookup tables built on the calling thread: LIKE outcome per p_type dictionary entry, nation row by
/// nationkey value (`nat_tab[v] = row + 1`, 0 for none, for values below 256), nation keys, and the region row
/// (`row + 1`, 0 for none) named `$3` of each nation.
pub struct Lookups {
    pub like_ok: Vec<bool>,
    pub nat_tab: Vec<usize>,
    pub nkeys: Vec<i64>,
    pub nreg: Vec<usize>,
}

pub open spec fn nat_tab_ok(x: usize, t: Tabs, v: int) -> bool {
    if x == 0 {
        forall|q: int| 0 <= q < t.n.len() ==> t.n[q][0] != Val::Int(v)
    } else {
        x - 1 < t.n.len() && t.n[x - 1][0] == Val::Int(v)
    }
}

pub open spec fn nreg_ok(x: usize, t: Tabs, m: Prm, q: int) -> bool {
    if x == 0 {
        forall|r: int| !rmatch(t, m, q, r)
    } else {
        rmatch(t, m, q, x - 1)
    }
}

pub open spec fn lookups_ok(lk: Lookups, c: Cols, t: Tabs, m: Prm) -> bool {
    &&& lk.like_ok@.len() == c.p.type_o@.len() - 1
    &&& forall|e: int| 0 <= e < lk.like_ok@.len()
        ==> #[trigger] lk.like_ok@[e] == like_true(Val::Text(txt(c.p.type_o@, c.p.type_y@, e)), m.pat)
    &&& lk.nat_tab@.len() == 256
    &&& forall|v: int| 0 <= v < 256 ==> #[trigger] nat_tab_ok(lk.nat_tab@[v], t, v)
    &&& lk.nkeys@.len() == t.n.len()
    &&& forall|q: int| 0 <= q < t.n.len() ==> t.n[q][0] == Val::Int(#[trigger] lk.nkeys@[q] as int)
    &&& lk.nreg@.len() == t.n.len()
    &&& forall|q: int| 0 <= q < t.n.len() ==> #[trigger] nreg_ok(lk.nreg@[q], t, m, q)
}

/// Scan parameters shared by every task: `$1`, the first supplier key and part key with their density flags
/// (`key[j] == first + j` for every row), and the guess for partsupp ranges (first partkey, rows per part).
#[derive(Clone, Copy)]
pub struct ScanArgs {
    pub size: i64,
    pub s_first: i64,
    pub s_dense: bool,
    pub p_first: i64,
    pub p_dense: bool,
    pub ps_first: i64,
    pub ratio: usize,
    pub psrun: bool,
}

/// With `psrun`, partsupp row `k` has ps_partkey `p_first + k / ratio` (storage `suppliers_psrun`'s run layout):
/// the rows of a partkey are found without reading the key column.
pub open spec fn run_fact(a: ScanArgs, t: Tabs) -> bool {
    a.psrun ==> a.ratio >= 1 && forall|k: int| 0 <= k < t.ps.len() ==> #[trigger] t.ps[k][0] == Val::Int(a.p_first + k / (a.ratio as int))
}

pub open spec fn args_ok(a: ScanArgs, t: Tabs, m: Prm) -> bool {
    &&& a.size as int == m.size
    &&& a.s_dense ==> forall|j: int| 0 <= j < t.s.len() ==> #[trigger] t.s[j][0] == Val::Int(a.s_first + j)
    &&& a.p_dense ==> forall|i: int| 0 <= i < t.p.len() ==> #[trigger] t.p[i][0] == Val::Int(a.p_first + i)
    &&& run_fact(a, t)
}

/// Everything a scan relies on.
pub open spec fn scan_env(c: Cols, lk: Lookups, a: ScanArgs, t: Tabs, m: Prm) -> bool {
    &&& cols_ok(c, t)
    &&& keys_unique(t)
    &&& lookups_ok(lk, c, t, m)
    &&& args_ok(a, t, m)
}

/// First row of part group `g` (the row count past the last group).
pub open spec fn row_start(c: Cols, g: int) -> int {
    if g < c.p.ng { g * c.p.bs } else { c.p.n as int }
}

// ------------------------------------------------------------------------------------------------ chunk lemmas

/// Rows without a selected part add no candidates.
pub proof fn lemma_chunk_extend(t: Tabs, m: Prm, cs: Seq<Cand>, a: int, b: int, b2: int)
    requires chunk_ok(t, m, cs, a, b), b <= b2, forall|i: int| b <= i < b2 ==> !#[trigger] part_sel(t, m, i),
    ensures chunk_ok(t, m, cs, a, b2),
{
}

/// The candidates of one more part row.
pub proof fn lemma_chunk_part(t: Tabs, m: Prm, cs: Seq<Cand>, seg: Seq<Cand>, a: int, r: int)
    requires
        chunk_ok(t, m, cs, a, r),
        forall|x: int| 0 <= x < seg.len() ==> #[trigger] cand_ok(t, m, seg[x]),
        forall|x: int| 0 <= x < seg.len() ==> #[trigger] seg[x].part == r,
        forall|x: int, y: int| 0 <= x < y < seg.len() ==> #[trigger] seg[x].ps < #[trigger] seg[y].ps,
        forall|k: int| #[trigger] is_min(t, m, t.p[r][0], k) ==> has_pair(seg, r, k),
    ensures chunk_ok(t, m, cs + seg, a, r + 1),
{
    assert forall|x: int, y: int| 0 <= x < y < seg.len() implies #[trigger] cand_lt(seg[x], seg[y]) by {
        assert(seg[x].ps < seg[y].ps);
        assert(seg[x].part == r && seg[y].part == r);
    }
    assert forall|x: int| 0 <= x < seg.len() implies r <= #[trigger] seg[x].part < r + 1 by {
        assert(seg[x].part == r);
    }
    assert(chunk_ok(t, m, seg, r, r + 1));
    lemma_chunk_append(t, m, cs, seg, a, r, r + 1);
}

// ------------------------------------------------------------------------------------------------ lookups

/// Group of row `j` under blocks of `bs` rows (the common block size divides by a shift).
#[inline]
pub fn grp(j: usize, bs: usize) -> (g: usize)
    requires bs >= 1,
    ensures g == j / bs,
    no_unwind
{
    if bs == 65536 { j / 65536 } else { j / bs }
}

/// Nation row of nationkey `v` (unique by the primary key).
pub fn nation_of(lk: &Lookups, v: i64, Ghost(c): Ghost<Cols>, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>) -> (r: Option<usize>)
    requires lookups_ok(*lk, c, t, m),
    ensures
        r matches Some(q) ==> q < t.n.len() && t.n[q as int][0] == Val::Int(v as int),
        r is None ==> forall|q: int| 0 <= q < t.n.len() ==> t.n[q][0] != Val::Int(v as int),
    no_unwind
{
    if 0 <= v && v < 256 {
        let x = lk.nat_tab[v as usize];
        assert(nat_tab_ok(lk.nat_tab@[v as int], t, v as int));
        if x > 0 { Some(x - 1) } else { None }
    } else {
        let nn = lk.nkeys.len();
        let mut q: usize = 0;
        while q < nn
            invariant
                lookups_ok(*lk, c, t, m),
                nn == t.n.len(),
                q <= nn,
                forall|q2: int| 0 <= q2 < q ==> t.n[q2][0] != Val::Int(v as int),
            decreases nn - q,
        {
            assert(t.n[q as int][0] == Val::Int(lk.nkeys@[q as int] as int));
            if lk.nkeys[q] == v {
                return Some(q);
            }
            q = q + 1;
        }
        None
    }
}

/// Supplier, nation and region rows of partsupp row `k` when its supplier lies in region `$3`.
pub fn supp_region(c: &Cols, lk: &Lookups, a: ScanArgs, k: usize, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>)
    -> (r: Option<(usize, usize, usize)>)
    requires scan_env(*c, *lk, a, t, m), k < c.ps.n,
    ensures
        r matches Some((j, n, rg)) ==> smatch(t, k as int, j as int) && nmatch(t, j as int, n as int) && rmatch(t, m, n as int, rg as int),
        r is None ==> !inreg(t, m, k as int),
    no_unwind
{
    assert(ps_row_ok(c.ps, t.ps[k as int], k as int));
    proof { lemma_grp_bound(c.ps.n as int, c.ps.bs as int, c.ps.ng as int, k as int); }
    let sk: i64 = c.ps.supp_b[grp(k, c.ps.bs)] + c.ps.supp_c[k] as i64;
    let found: Option<usize> = if a.s_dense {
        if sk as i128 >= a.s_first as i128 && (sk as i128) - (a.s_first as i128) < c.s.n as i128 {
            let j = (sk as i128 - a.s_first as i128) as usize;
            assert(t.s[j as int][0] == Val::Int(a.s_first + j));
            Some(j)
        } else {
            proof {
                assert forall|j: int| 0 <= j < t.s.len() implies t.s[j][0] != Val::Int(sk as int) by {
                    assert(t.s[j][0] == Val::Int(a.s_first + j));
                }
            }
            None
        }
    } else {
        let guess: usize = if sk as i128 >= a.s_first as i128 && (sk as i128) - (a.s_first as i128) < c.s.n as i128 {
            (sk as i128 - a.s_first as i128) as usize
        } else {
            c.s.n
        };
        let f = key_find_guess(c.s.key_c, c.s.key_b, c.e32, c.e64, c.s.bs, c.s.kind, c.s.n, sk as i128, guess);
        proof {
            match f {
                Some(j) => {
                    assert(supp_row_ok(c.s, t.s[j as int], j as int));
                    assert(fkey(c.s.key_c@, c.s.key_b@, c.s.bs as int, j as int) == fv32(c.s.key_c@, c.s.key_b@, c.s.bs as int, j as int));
                },
                None => {
                    assert forall|j: int| 0 <= j < t.s.len() implies t.s[j][0] != Val::Int(sk as int) by {
                        assert(supp_row_ok(c.s, t.s[j], j));
                        assert(fkey(c.s.key_c@, c.s.key_b@, c.s.bs as int, j) != sk as int);
                    }
                },
            }
        }
        f
    };
    match found {
        None => {
            proof {
                assert forall|j: int, n: int, r: int| #![trigger smatch(t, k as int, j), nmatch(t, j, n), rmatch(t, m, n, r)]
                    smatch(t, k as int, j) && nmatch(t, j, n) implies !rmatch(t, m, n, r) by {
                    assert(t.s[j][0] == t.ps[k as int][1]);
                }
            }
            None
        },
        Some(j) => {
            assert(supp_row_ok(c.s, t.s[j as int], j as int));
            proof { lemma_grp_bound(c.s.n as int, c.s.bs as int, c.s.ng as int, j as int); }
            let nv: i64 = c.s.nat_b[grp(j, c.s.bs)] + c.s.nat_c[j] as i64;
            match nation_of(lk, nv, Ghost(*c), Ghost(t), Ghost(m)) {
                None => {
                    proof {
                        assert forall|j2: int, n: int, r: int| #![trigger smatch(t, k as int, j2), nmatch(t, j2, n), rmatch(t, m, n, r)]
                            smatch(t, k as int, j2) && nmatch(t, j2, n) implies !rmatch(t, m, n, r) by {
                            assert(t.s[j2][0] == t.s[j as int][0]);
                            assert(j2 == j);
                        }
                    }
                    None
                },
                Some(n) => {
                    let rr = lk.nreg[n];
                    assert(nreg_ok(lk.nreg@[n as int], t, m, n as int));
                    if rr > 0 {
                        Some((j, n, rr - 1))
                    } else {
                        proof {
                            assert forall|j2: int, n2: int, r: int| #![trigger smatch(t, k as int, j2), nmatch(t, j2, n2), rmatch(t, m, n2, r)]
                                smatch(t, k as int, j2) && nmatch(t, j2, n2) implies !rmatch(t, m, n2, r) by {
                                assert(t.s[j2][0] == t.s[j as int][0]);
                                assert(j2 == j);
                                assert(t.n[n2][0] == t.n[n as int][0]);
                                assert(n2 == n);
                            }
                        }
                        None
                    }
                },
            }
        },
    }
}

/// Key of partsupp row `k`.
#[inline]
pub fn ps_key(c: &Cols, k: usize, Ghost(t): Ghost<Tabs>) -> (v: i64)
    requires cols_ok(*c, t), k < c.ps.n,
    ensures v as int == fv32(c.ps.key_c@, c.ps.key_b@, c.ps.bs as int, k as int), t.ps[k as int][0] == Val::Int(v as int),
    no_unwind
{
    assert(ps_row_ok(c.ps, t.ps[k as int], k as int));
    proof { lemma_grp_bound(c.ps.n as int, c.ps.bs as int, c.ps.ng as int, k as int); }
    c.ps.key_b[grp(k, c.ps.bs)] + c.ps.key_c[k] as i64
}

/// `du < n / ratio` keeps `du * ratio` below `n`.
proof fn lemma_mul_below(du: int, ratio: int, n: int)
    requires 0 <= du, ratio > 0, n >= 0, du < n / ratio,
    ensures du * ratio < n, du * ratio >= 0,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(n, ratio);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(n, ratio);
    let q = n / ratio;
    assert(ratio * q == q * ratio) by (nonlinear_arith);
    assert(du * ratio <= (q - 1) * ratio) by (nonlinear_arith) requires du <= q - 1, ratio > 0;
    assert((q - 1) * ratio == q * ratio - ratio) by (nonlinear_arith);
    assert(du * ratio >= 0) by (nonlinear_arith) requires du >= 0, ratio > 0;
}

/// Sorted partsupp keys are nondecreasing between any two rows.
proof fn lemma_ps_sorted(c: Cols, t: Tabs, x: int, y: int)
    requires cols_ok(c, t), c.ps.kind == 1, 0 <= x <= y < c.ps.n,
    ensures fv32(c.ps.key_c@, c.ps.key_b@, c.ps.bs as int, x) <= fv32(c.ps.key_c@, c.ps.key_b@, c.ps.bs as int, y),
{
    lemma_sorted_le(c.ps.key_c@, c.ps.key_b@, c.e32@, c.e64@, c.ps.bs as int, c.ps.kind, c.ps.n as int, x, y);
}

/// `du <= nk / nt` keeps `du * nt` at most `nk`.
pub proof fn lemma_mul_le_div(du: int, nt: int, nk: int)
    requires 0 <= du, nt >= 1, nk >= 0, du <= nk / nt,
    ensures 0 <= du * nt <= nk,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(nk, nt);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(nk, nt);
    assert(du * nt <= (nk / nt) * nt) by (nonlinear_arith) requires du <= nk / nt, nt >= 1;
    assert((nk / nt) * nt == nt * (nk / nt)) by (nonlinear_arith);
    assert(du * nt >= 0) by (nonlinear_arith) requires du >= 0, nt >= 1;
}

/// Under the run layout, the partsupp rows of key `pk` are exactly `[d * ratio, d * ratio + ratio)` (within the
/// table), `d = pk - p_first`; no key is read.
fn run_range(c: &Cols, a: ScanArgs, pk: i64, Ghost(t): Ghost<Tabs>) -> (r: (usize, usize))
    requires cols_ok(*c, t), run_fact(a, t), a.psrun,
    ensures
        r.0 <= r.1 <= c.ps.n,
        forall|k: int| 0 <= k < c.ps.n && #[trigger] t.ps[k][0] == Val::Int(pk as int) ==> r.0 <= k < r.1,
        forall|k: int| r.0 <= k < r.1 ==> #[trigger] t.ps[k][0] == Val::Int(pk as int),
    no_unwind
{
    let n = c.ps.n;
    let ratio = a.ratio;
    let d: i128 = pk as i128 - a.p_first as i128;
    if d < 0 || d > (n / ratio) as i128 {
        proof {
            assert forall|k: int| 0 <= k < c.ps.n && #[trigger] t.ps[k][0] == Val::Int(pk as int) implies 0 <= k < 0 by {
                assert(t.ps[k][0] == Val::Int(a.p_first + k / (ratio as int)));
                vstd::arithmetic::div_mod::lemma_div_pos_is_pos(k, ratio as int);
                vstd::arithmetic::div_mod::lemma_div_is_ordered(k, n as int, ratio as int);
            }
        }
        return (0, 0);
    }
    let du = d as usize;
    proof { lemma_mul_le_div(du as int, ratio as int, n as int); }
    let lo = du * ratio;
    let hi = if n - lo > ratio { lo + ratio } else { n };
    proof {
        assert forall|k: int| 0 <= k < c.ps.n && #[trigger] t.ps[k][0] == Val::Int(pk as int) implies lo <= k < hi by {
            assert(t.ps[k][0] == Val::Int(a.p_first + k / (ratio as int)));
            crate::stores::part_sztyidx::interface::lemma_key_split(k, ratio as int, du as int);
        }
        assert forall|k: int| lo <= k < hi implies #[trigger] t.ps[k][0] == Val::Int(pk as int) by {
            assert(t.ps[k][0] == Val::Int(a.p_first + k / (ratio as int)));
            crate::stores::part_sztyidx::interface::lemma_key_split(k, ratio as int, du as int);
        }
    }
    (lo, hi)
}

/// The partsupp positions `[lo, hi)` that hold every row of key `pk` (sorted table: a guessed start first).
pub fn ps_range(c: &Cols, a: ScanArgs, pk: i64, Ghost(t): Ghost<Tabs>) -> (r: (usize, usize))
    requires cols_ok(*c, t), run_fact(a, t),
    ensures
        r.0 <= r.1 <= c.ps.n,
        forall|k: int| 0 <= k < c.ps.n && #[trigger] t.ps[k][0] == Val::Int(pk as int) ==> r.0 <= k < r.1,
        a.psrun ==> forall|k: int| r.0 <= k < r.1 ==> #[trigger] t.ps[k][0] == Val::Int(pk as int),
    no_unwind
{
    let n = c.ps.n;
    if a.psrun {
        return run_range(c, a, pk, Ghost(t));
    }
    if c.ps.kind == 1 {
        let ratio = a.ratio;
        let d: i128 = pk as i128 - a.ps_first as i128;
        if ratio > 0 && d >= 0 && d < (n / ratio) as i128 {
            let du = d as usize;
            proof { lemma_mul_below(du as int, ratio as int, n as int); }
            let g = du * ratio;
            let before_ok = if g == 0 { true } else { ps_key(c, g - 1, Ghost(t)) < pk };
            if ps_key(c, g, Ghost(t)) == pk && before_ok {
                let mut h = g + 1;
                while h < n && ps_key(c, h, Ghost(t)) == pk
                    invariant
                        cols_ok(*c, t), c.ps.kind == 1, n == c.ps.n,
                        g < h <= n,
                        forall|k: int| g <= k < h ==> #[trigger] fv32(c.ps.key_c@, c.ps.key_b@, c.ps.bs as int, k) == pk,
                    decreases n - h,
                {
                    h = h + 1;
                }
                proof {
                    let b = c.ps.bs as int;
                    assert forall|k: int| 0 <= k < n && #[trigger] t.ps[k][0] == Val::Int(pk as int) implies g <= k < h by {
                        assert(ps_row_ok(c.ps, t.ps[k], k));
                        if k < g {
                            lemma_ps_sorted(*c, t, k, (g - 1) as int);
                        }
                        if k >= h {
                            assert(h < n);
                            lemma_ps_sorted(*c, t, (h - 1) as int, h as int);
                            lemma_ps_sorted(*c, t, h as int, k);
                            assert(fv32(c.ps.key_c@, c.ps.key_b@, b, h as int) != pk);
                        }
                    }
                }
                return (g, h);
            }
        }
        let r = key_range(c.ps.key_c, c.ps.key_b, c.e32, c.e64, c.ps.bs, c.ps.kind, n, pk as i128);
        proof {
            assert forall|k: int| 0 <= k < c.ps.n && #[trigger] t.ps[k][0] == Val::Int(pk as int) implies r.0 <= k < r.1 by {
                assert(ps_row_ok(c.ps, t.ps[k], k));
                assert(irow(c.ps.kind, c.e32@, c.e64@, c.ps.bs as int, k) == k);
                assert(fkey(c.ps.key_c@, c.ps.key_b@, c.ps.bs as int, k) == pk);
            }
        }
        r
    } else {
        (0, n)
    }
}

// ------------------------------------------------------------------------------------------------ one part

/// The supplier, nation and region facts of a candidate (`cand_ok` without its part and minimality).
pub open spec fn cand_rows_ok(t: Tabs, m: Prm, c: Cand) -> bool {
    &&& smatch(t, c.ps as int, c.supp as int)
    &&& nmatch(t, c.supp as int, c.nation as int)
    &&& (exists|r: int| #[trigger] rmatch(t, m, c.nation as int, r))
    &&& t.s[c.supp as int][5] == (Val::Num { coeff: c.acct as int, scale: 2 })
}

/// Appends `x` to the buffer (room is required).
#[inline]
fn push_cand(buf: &mut CandBuf, x: Cand)
    requires buf_wf(*old(buf)), old(buf).len < old(buf).v@.len(),
    ensures
        buf_wf(*final(buf)),
        final(buf).v@.len() == old(buf).v@.len(),
        final(buf).len == old(buf).len + 1,
        buf_view(*final(buf)) == buf_view(*old(buf)).push(x),
    no_unwind
{
    let at = buf.len;
    let vl = buf.v.len();
    let ghost before = buf.v@;
    put(&mut buf.v, at, x);
    buf.len = at + 1;
    proof {
        assert(buf_view(*buf) =~= before.subrange(0, at as int).push(x));
    }
}

/// The candidates of part row `i` so far (`seg`): partsupp rows of `[lo, k)` qualifying for `pkv` at cost
/// `best`, in increasing order, with their supplier, nation and region facts.
pub open spec fn seg_ok(t: Tabs, m: Prm, seg: Seq<Cand>, i: usize, pkv: Val, lo: int, k: int, best: int) -> bool {
    &&& forall|x: int| 0 <= x < seg.len() ==> #[trigger] seg[x].part == i && lo <= seg[x].ps < k
    &&& forall|x: int| 0 <= x < seg.len() ==> qual(t, m, pkv, #[trigger] seg[x].ps as int)
    &&& forall|x: int| 0 <= x < seg.len() ==> cost(t, #[trigger] seg[x].ps as int) == best
    &&& forall|x: int| 0 <= x < seg.len() ==> #[trigger] cand_rows_ok(t, m, seg[x])
    &&& forall|x: int, y: int| 0 <= x < y < seg.len() ==> #[trigger] seg[x].ps < #[trigger] seg[y].ps
    &&& forall|k2: int| lo <= k2 < k && #[trigger] qual(t, m, pkv, k2) && cost(t, k2) == best
        ==> exists|x: int| 0 <= x < seg.len() && #[trigger] seg[x].ps == k2
}

/// One more partsupp row `k` that is a candidate at cost `best`.
#[verifier::spinoff_prover]
proof fn lemma_seg_push(t: Tabs, m: Prm, seg: Seq<Cand>, x: Cand, i: usize, pkv: Val, lo: int, k: int, best: int)
    requires
        seg_ok(t, m, seg, i, pkv, lo, k, best),
        lo <= k,
        x.part == i, x.ps == k, qual(t, m, pkv, k), cost(t, k) == best, cand_rows_ok(t, m, x),
    ensures seg_ok(t, m, seg.push(x), i, pkv, lo, k + 1, best),
{
    let s1 = seg.push(x);
    assert forall|y: int| 0 <= y < s1.len() implies #[trigger] s1[y].part == i && lo <= s1[y].ps < k + 1 by {
        if y < seg.len() { assert(s1[y] == seg[y]); assert(seg[y].part == i); }
    }
    assert forall|y: int| 0 <= y < s1.len() implies qual(t, m, pkv, #[trigger] s1[y].ps as int) by {
        if y < seg.len() { assert(s1[y] == seg[y]); }
    }
    assert forall|y: int| 0 <= y < s1.len() implies cost(t, #[trigger] s1[y].ps as int) == best by {
        if y < seg.len() { assert(s1[y] == seg[y]); }
    }
    assert forall|y: int| 0 <= y < s1.len() implies #[trigger] cand_rows_ok(t, m, s1[y]) by {
        if y < seg.len() { assert(s1[y] == seg[y]); }
    }
    assert forall|y: int, z: int| 0 <= y < z < s1.len() implies #[trigger] s1[y].ps < #[trigger] s1[z].ps by {
        assert(s1[y] == seg[y]);
        assert(seg[y].part == i);
        if z < seg.len() { assert(s1[z] == seg[z]); }
    }
    assert forall|k2: int| lo <= k2 < k + 1 && #[trigger] qual(t, m, pkv, k2) && cost(t, k2) == best
        implies exists|y: int| 0 <= y < s1.len() && #[trigger] s1[y].ps == k2 by {
        if k2 == k {
            assert(s1[seg.len() as int].ps == k2);
        } else {
            let y = choose|y: int| 0 <= y < seg.len() && #[trigger] seg[y].ps == k2;
            assert(s1[y] == seg[y]);
        }
    }
}

/// One more partsupp row `k` that is not a candidate at cost `best`.
#[verifier::spinoff_prover]
proof fn lemma_seg_skip(t: Tabs, m: Prm, seg: Seq<Cand>, i: usize, pkv: Val, lo: int, k: int, best: int)
    requires seg_ok(t, m, seg, i, pkv, lo, k, best), lo <= k, !(qual(t, m, pkv, k) && cost(t, k) == best),
    ensures seg_ok(t, m, seg, i, pkv, lo, k + 1, best),
{
    assert forall|y: int| 0 <= y < seg.len() implies #[trigger] seg[y].part == i && lo <= seg[y].ps < k + 1 by {
        assert(seg[y].part == i);
    }
    assert forall|k2: int| lo <= k2 < k + 1 && #[trigger] qual(t, m, pkv, k2) && cost(t, k2) == best
        implies exists|y: int| 0 <= y < seg.len() && #[trigger] seg[y].ps == k2 by {
        assert(k2 < k);
        let y = choose|y: int| 0 <= y < seg.len() && #[trigger] seg[y].ps == k2;
        assert(seg[y].ps == k2);
    }
    assert(forall|x: int| 0 <= x < seg.len() ==> qual(t, m, pkv, #[trigger] seg[x].ps as int));
    assert(forall|x: int| 0 <= x < seg.len() ==> cost(t, #[trigger] seg[x].ps as int) == best);
    assert(forall|x: int| 0 <= x < seg.len() ==> #[trigger] cand_rows_ok(t, m, seg[x]));
    assert(forall|x: int, y: int| 0 <= x < y < seg.len() ==> #[trigger] seg[x].ps < #[trigger] seg[y].ps);
    assert(forall|x: int| 0 <= x < seg.len() ==> #[trigger] seg[x].part == i && lo <= seg[x].ps < k + 1);
    assert(forall|k2: int| lo <= k2 < k + 1 && #[trigger] qual(t, m, pkv, k2) && cost(t, k2) == best
        ==> exists|x: int| 0 <= x < seg.len() && #[trigger] seg[x].ps == k2);
    assert(seg_ok(t, m, seg, i, pkv, lo, k + 1, best));
}

/// Appends the candidates of part row `i` (partkey `pk`, partsupp positions `[lo, hi)` holding every row of `pk`)
/// to `buf`: one pass that restarts the part's candidates whenever a strictly cheaper supplier appears.
pub fn emit_part(c: &Cols, lk: &Lookups, a: ScanArgs, i: usize, pk: i64, lo: usize, hi: usize, buf: &mut CandBuf,
    Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>)
    requires
        scan_env(*c, *lk, a, t, m),
        part_sel(t, m, i as int),
        t.p[i as int][0] == Val::Int(pk as int),
        lo <= hi <= c.ps.n,
        forall|k: int| 0 <= k < c.ps.n && #[trigger] t.ps[k][0] == Val::Int(pk as int) ==> lo <= k < hi,
        a.psrun ==> forall|k: int| lo <= k < hi ==> #[trigger] t.ps[k][0] == Val::Int(pk as int),
        buf_wf(*old(buf)),
        old(buf).len + (hi - lo) <= old(buf).v@.len(),
    ensures
        buf_wf(*final(buf)),
        final(buf).v@.len() == old(buf).v@.len(),
        old(buf).len <= final(buf).len <= old(buf).len + (hi - lo),
        ({
            let seg = buf_view(*final(buf)).subrange(old(buf).len as int, final(buf).len as int);
            &&& buf_view(*final(buf)) == buf_view(*old(buf)) + seg
            &&& forall|x: int| 0 <= x < seg.len() ==> #[trigger] cand_ok(t, m, seg[x])
            &&& forall|x: int| 0 <= x < seg.len() ==> #[trigger] seg[x].part == i
            &&& forall|x: int, y: int| 0 <= x < y < seg.len() ==> #[trigger] seg[x].ps < #[trigger] seg[y].ps
            &&& forall|k: int| #[trigger] is_min(t, m, t.p[i as int][0], k) ==> has_pair(seg, i as int, k)
        }),
    no_unwind
{
    let ghost pkv = Val::Int(pk as int);
    let ghost pre = buf_view(*buf);
    let ghost mut seg = Seq::<Cand>::empty();
    let start = buf.len;
    let mut best: i64 = 0;
    let mut found = false;
    let mut k = lo;
    while k < hi
        invariant
            scan_env(*c, *lk, a, t, m),
            part_sel(t, m, i as int),
            t.p[i as int][0] == pkv,
            pkv == Val::Int(pk as int),
            lo <= k <= hi <= c.ps.n,
            a.psrun ==> forall|k2: int| lo <= k2 < hi ==> #[trigger] t.ps[k2][0] == Val::Int(pk as int),
            buf_wf(*buf),
            buf.v@.len() == old(buf).v@.len(),
            start == old(buf).len,
            pre == buf_view(*old(buf)),
            buf.len == start + seg.len(),
            seg.len() <= k - lo,
            start + (hi - lo) <= buf.v@.len(),
            buf_view(*buf) == pre + seg,
            found ==> exists|k0: int| lo <= k0 < k && qual(t, m, pkv, k0) && cost(t, k0) == best,
            found ==> forall|k2: int| lo <= k2 < k && #[trigger] qual(t, m, pkv, k2) ==> best <= cost(t, k2),
            !found ==> forall|k2: int| lo <= k2 < k ==> !#[trigger] qual(t, m, pkv, k2),
            !found ==> seg.len() == 0,
            seg_ok(t, m, seg, i, pkv, lo as int, k as int, best as int),
        decreases hi - k,
    {
        // Under the run layout every row of `[lo, hi)` has key `pk`; otherwise compare the stored key.
        let key_ok: bool = if a.psrun { true } else { ps_key(c, k, Ghost(t)) == pk };
        assert(key_ok <==> t.ps[k as int][0] == Val::Int(pk as int));
        if key_ok {
            match supp_region(c, lk, a, k, Ghost(t), Ghost(m)) {
                Some((j, n, r)) => {
                    assert(ps_row_ok(c.ps, t.ps[k as int], k as int));
                    proof { lemma_grp_bound(c.ps.n as int, c.ps.bs as int, c.ps.ng as int, k as int); }
                    let cst = c.ps.cost_b[grp(k, c.ps.bs)] + c.ps.cost_c[k] as i64;
                    assert(qual(t, m, pkv, k as int));
                    assert(cost(t, k as int) == cst as int);
                    if !found || cst <= best {
                        if !found || cst < best {
                            best = cst;
                            found = true;
                            buf.len = start;
                            proof {
                                seg = Seq::<Cand>::empty();
                                assert(buf_view(*buf) =~= pre + seg);
                                assert forall|k2: int| lo <= k2 < k && #[trigger] qual(t, m, pkv, k2) implies cost(t, k2) != best by {
                                }
                            }
                        }
                        assert(supp_row_ok(c.s, t.s[j as int], j as int));
                        proof { lemma_grp_bound(c.s.n as int, c.s.bs as int, c.s.ng as int, j as int); }
                        let acct = c.s.acct_b[grp(j, c.s.bs)] + c.s.acct_c[j] as i64;
                        let x = Cand { part: i, ps: k, supp: j, nation: n, acct };
                        push_cand(buf, x);
                        proof {
                            assert(rmatch(t, m, n as int, r as int));
                            assert(cand_rows_ok(t, m, x));
                            lemma_seg_push(t, m, seg, x, i, pkv, lo as int, k as int, best as int);
                            seg = seg.push(x);
                            assert(buf_view(*buf) =~= pre + seg);
                        }
                    } else {
                        proof { lemma_seg_skip(t, m, seg, i, pkv, lo as int, k as int, best as int); }
                    }
                },
                None => {
                    assert(!qual(t, m, pkv, k as int));
                    proof { lemma_seg_skip(t, m, seg, i, pkv, lo as int, k as int, best as int); }
                },
            }
        } else {
            assert(t.ps[k as int][0] != pkv);
            proof { lemma_seg_skip(t, m, seg, i, pkv, lo as int, k as int, best as int); }
        }
        k = k + 1;
    }
    proof {
        assert(buf_view(*buf).subrange(start as int, buf.len as int) =~= seg);
        // Every qualifying row of `pk` lies in `[lo, hi)`, so `best` is the minimum over all of them.
        assert forall|k2: int| #[trigger] qual(t, m, pkv, k2) implies lo <= k2 < hi by {
            assert(t.ps[k2][0] == Val::Int(pk as int));
        }
        assert forall|x: int| 0 <= x < seg.len() implies #[trigger] cand_ok(t, m, seg[x]) by {
            let kx = seg[x].ps as int;
            assert(cand_rows_ok(t, m, seg[x]));
            assert forall|k2: int| #[trigger] qual(t, m, pkv, k2) implies cost(t, kx) <= cost(t, k2) by {
                assert(lo <= k2 < hi);
            }
            assert(is_min(t, m, pkv, kx));
        }
        assert forall|k2: int| #[trigger] is_min(t, m, t.p[i as int][0], k2) implies has_pair(seg, i as int, k2) by {
            assert(qual(t, m, pkv, k2));
            assert(found);
            let k0 = choose|k0: int| lo <= k0 < hi && qual(t, m, pkv, k0) && cost(t, k0) == best;
            assert(cost(t, k2) <= cost(t, k0));
            assert(lo <= k2 < hi);
            let x = choose|x: int| 0 <= x < seg.len() && #[trigger] seg[x].ps == k2;
            assert(seg[x].part == i);
        }
    }
}

// ------------------------------------------------------------------------------------------------ batches

/// The mutable state of one scan: the candidate buffer, a preallocated list of pending part rows (a batch), and a
/// sink for the prefetching loads of a batch (so they are not removed).
pub struct ScanState {
    pub buf: CandBuf,
    pub pend: Vec<usize>,
    pub sink: u64,
}

/// Partkey of part row `r` (the dense key without a load).
#[inline]
pub fn part_key(c: &Cols, a: ScanArgs, r: usize, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>) -> (pk: i64)
    requires cols_ok(*c, t), args_ok(a, t, m), r < c.p.n,
    ensures t.p[r as int][0] == Val::Int(pk as int),
    no_unwind
{
    assert(part_row_ok(c.p, t.p[r as int], r as int));
    if a.p_dense {
        assert(t.p[r as int][0] == Val::Int(a.p_first + r));
        (a.p_first as i128 + r as i128) as i64
    } else {
        proof { lemma_grp_bound(c.p.n as int, c.p.bs as int, c.p.ng as int, r as int); }
        c.p.key_b[grp(r, c.p.bs)] + c.p.key_c[r] as i64
    }
}

/// Loads the partsupp lines a batch of part rows will need (independent loads that overlap their memory latency);
/// reads only, the result goes to `sink`. With dense part keys numbered like the partsupp keys, part row `r`'s
/// partsupp rows are guessed at `r * ratio` (no division per part); the neighbour keys `ps_range` checks are loaded too.
pub fn touch_batch(c: &Cols, a: ScanArgs, pend: &Vec<usize>, np: usize, sink: &mut u64, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>)
    requires
        cols_ok(*c, t), args_ok(a, t, m),
        np <= pend@.len(),
        forall|x: int| 0 <= x < np ==> #[trigger] pend@[x] < c.p.n,
    no_unwind
{
    let mut x: u64 = *sink;
    let ratio = a.ratio;
    let n = c.ps.n;
    if !(a.p_dense && a.p_first == a.ps_first && ratio > 0) {
        return;
    }
    let pmax = n / ratio;
    let kc = c.ps.key_c;
    let sc = c.ps.supp_c;
    let cc = c.ps.cost_c;
    let mut q: usize = 0;
    while q < np
        invariant
            cols_ok(*c, t), np <= pend@.len(), n == c.ps.n, ratio > 0, pmax == n / ratio,
            kc@ == c.ps.key_c@, sc@ == c.ps.supp_c@, cc@ == c.ps.cost_c@,
        decreases np - q,
    {
        let r = pend[q];
        if r < pmax {
            proof { lemma_mul_below(r as int, ratio as int, n as int); }
            let gs = r * ratio;
            let ge = if n - gs > ratio { gs + ratio } else { gs };
            let gp = if gs > 0 { gs - 1 } else { gs };
            x = if a.psrun {
                x ^ (sc[gs] as u64) ^ (cc[gs] as u64)
            } else {
                x ^ (kc[gp] as u64) ^ (kc[ge] as u64) ^ (sc[gs] as u64) ^ (cc[gs] as u64)
            };
        }
        q = q + 1;
    }
    *sink = x;
}

/// Loads the supplier lines (nation code, account balance) of the guessed partsupp rows of a batch of part rows,
/// after `touch_batch` brought their partsupp lines in (independent loads that overlap their latency); reads only,
/// the result goes to `sink`. Dense supplier keys only (supplier row = suppkey - first key).
pub fn touch_suppliers(c: &Cols, a: ScanArgs, pend: &Vec<usize>, np: usize, sink: &mut u64, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>)
    requires
        cols_ok(*c, t), args_ok(a, t, m),
        np <= pend@.len(),
        forall|x: int| 0 <= x < np ==> #[trigger] pend@[x] < c.p.n,
    no_unwind
{
    let mut x: u64 = *sink;
    let ratio = a.ratio;
    let n = c.ps.n;
    let ns = c.s.n;
    if !(a.s_dense && a.p_dense && a.p_first == a.ps_first && ratio > 0) {
        return;
    }
    let pmax = n / ratio;
    let bs = c.ps.bs;
    let sc = c.ps.supp_c;
    let sb = c.ps.supp_b;
    let natc = c.s.nat_c;
    let acct = c.s.acct_c;
    let s_first = a.s_first;
    let mut q: usize = 0;
    while q < np
        invariant
            cols_ok(*c, t), np <= pend@.len(), n == c.ps.n, ns == c.s.n, ratio > 0, pmax == n / ratio, bs == c.ps.bs,
            sc@ == c.ps.supp_c@, sb@ == c.ps.supp_b@, natc@ == c.s.nat_c@, acct@ == c.s.acct_c@,
        decreases np - q,
    {
        let r = pend[q];
        if r < pmax {
            proof { lemma_mul_below(r as int, ratio as int, n as int); }
            let gs = r * ratio;
            let ge = if n - gs > ratio { gs + ratio } else { n };
            let mut k = gs;
            while k < ge
                invariant
                    cols_ok(*c, t), n == c.ps.n, ns == c.s.n, gs <= k <= ge, ge <= n, bs == c.ps.bs,
                    sc@ == c.ps.supp_c@, sb@ == c.ps.supp_b@, natc@ == c.s.nat_c@, acct@ == c.s.acct_c@,
                decreases ge - k,
            {
                proof { lemma_grp_bound(c.ps.n as int, c.ps.bs as int, c.ps.ng as int, k as int); }
                let sk: i128 = sb[grp(k, bs)] as i128 + sc[k] as i128 - s_first as i128;
                if 0 <= sk && sk < ns as i128 {
                    let j = sk as usize;
                    x = x ^ (natc[j] as u64) ^ (acct[j] as u64);
                }
                k = k + 1;
            }
        }
        q = q + 1;
    }
    *sink = x;
}

/// Part row `r` of group `g` passes `p_size = $1 AND p_type LIKE $2` iff its size code is `tc` and the LIKE
/// outcome of its p_type dictionary entry is true.
proof fn lemma_block_row(c: Cols, lk: Lookups, t: Tabs, m: Prm, tc: u8, g: int, r: int)
    requires
        cols_ok(c, t), lookups_ok(lk, c, t, m),
        0 <= g < c.p.ng, g * c.p.bs <= r < g * c.p.bs + c.p.bs, r < c.p.n,
        tc as int == m.size - c.p.size_b@[g],
    ensures
        0 <= c.p.type_b@[g] + c.p.type_c@[r] < lk.like_ok@.len(),
        part_sel(t, m, r) <==> (c.p.size_c@[r] == tc && lk.like_ok@[c.p.type_b@[g] + c.p.type_c@[r]]),
{
    assert(part_row_ok(c.p, t.p[r], r));
    lemma_in_group(c.p.bs as int, g, r);
    let e = c.p.type_b@[g] + c.p.type_c@[r];
    assert(lk.like_ok@[e] == like_true(Val::Text(txt(c.p.type_o@, c.p.type_y@, e)), m.pat));
}

/// Writes to `pend[np ..]` the selected part rows among the 64 rows `[i, i + 64)` of group `g`, in increasing
/// order: one byte-compare mask of the p_size codes, then the LIKE outcome of each row whose code matches.
fn collect_block(c: &Cols, lk: &Lookups, tc: u8, tb: u64, g: usize, i: usize, pend: &mut Vec<usize>, np: usize,
    Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>) -> (np2: usize)
    requires
        cols_ok(*c, t), lookups_ok(*lk, *c, t, m),
        g < c.p.ng, g * c.p.bs <= i, i + 64 <= c.p.n, i + 64 <= g * c.p.bs + c.p.bs,
        tc as int == m.size - c.p.size_b@[g as int], tb == c.p.type_b@[g as int],
        np + 64 <= old(pend)@.len() <= usize::MAX,
    ensures
        final(pend)@.len() == old(pend)@.len(),
        np <= np2 <= np + 64,
        forall|x: int| 0 <= x < np ==> #[trigger] final(pend)@[x] == old(pend)@[x],
        forall|x: int| np <= x < np2 ==> i <= #[trigger] final(pend)@[x] < i + 64 && part_sel(t, m, final(pend)@[x] as int),
        forall|x: int, y: int| np <= x < y < np2 ==> #[trigger] final(pend)@[x] < #[trigger] final(pend)@[y],
        forall|r: int| i <= r < i + 64 && #[trigger] part_sel(t, m, r) ==> exists|x: int| np <= x < np2 && final(pend)@[x] == r,
    no_unwind
{
    let mut mm = match_mask(c.p.size_c, i, tc);
    let mut k = np;
    // `cur`: block offset of the first row not yet considered; the set bits of `mm` are the matching rows from it.
    let mut cur: u64 = 0;
    while mm != 0
        invariant
            cols_ok(*c, t), lookups_ok(*lk, *c, t, m),
            g < c.p.ng, g * c.p.bs <= i, i + 64 <= c.p.n, i + 64 <= g * c.p.bs + c.p.bs,
            tc as int == m.size - c.p.size_b@[g as int], tb == c.p.type_b@[g as int],
            np + 64 <= old(pend)@.len() <= usize::MAX,
            pend@.len() == old(pend)@.len(),
            cur <= 64, np <= k, k <= np + cur,
            forall|b: int| 0 <= b < 64 ==> (#[trigger] bit(mm, b) <==> (cur <= b && c.p.size_c@[i + b] == tc)),
            forall|x: int| 0 <= x < np ==> #[trigger] pend@[x] == old(pend)@[x],
            forall|x: int| np <= x < k ==> i <= #[trigger] pend@[x] < i + cur && part_sel(t, m, pend@[x] as int),
            forall|x: int, y: int| np <= x < y < k ==> #[trigger] pend@[x] < #[trigger] pend@[y],
            forall|r: int| i <= r < i + cur && #[trigger] part_sel(t, m, r) ==> exists|x: int| np <= x < k && pend@[x] == r,
        decreases 64 - cur,
    {
        let p = lowest_bit(mm);
        assert(bit(mm, p as int));
        assert(cur <= p);
        let r = i + p as usize;
        proof {
            lemma_block_row(*c, *lk, t, m, tc, g as int, r as int);
            // Rows between `cur` and `p` have another size code.
            assert forall|r2: int| i + cur <= r2 < r implies !#[trigger] part_sel(t, m, r2) by {
                lemma_block_row(*c, *lk, t, m, tc, g as int, r2);
                assert(!bit(mm, r2 - i));
            }
        }
        let e = (tb + c.p.type_c[r] as u64) as usize;
        let ghost p0 = pend@;
        let ghost k0 = k;
        if lk.like_ok[e] {
            put(pend, k, r);
            k = k + 1;
        }
        proof {
            assert forall|r2: int| i <= r2 < i + p + 1 && #[trigger] part_sel(t, m, r2)
                implies exists|x: int| np <= x < k && pend@[x] == r2 by {
                if r2 < i + cur {
                    let x = choose|x: int| np <= x < k0 && p0[x] == r2;
                    assert(pend@[x] == p0[x]);
                } else {
                    assert(r2 == r);
                    assert(pend@[k0 as int] == r2);
                }
            }
            assert forall|x: int, y: int| np <= x < y < k implies #[trigger] pend@[x] < #[trigger] pend@[y] by {
                if y < k0 {
                    assert(pend@[x] == p0[x] && pend@[y] == p0[y]);
                } else {
                    assert(pend@[x] == p0[x]);
                }
            }
        }
        let ghost mm0 = mm;
        let ghost cur0 = cur;
        mm = clear_bit(mm, p);
        cur = p + 1;
        proof {
            // Bits below `p` were already clear (lowest bit), bit `p` is cleared, the rest are kept.
            assert forall|b: int| 0 <= b < 64 implies (#[trigger] bit(mm, b) <==> (cur <= b && c.p.size_c@[i + b] == tc)) by {
                assert(bit(mm0, b) <==> (cur0 <= b && c.p.size_c@[i + b] == tc));
                if b < p {
                    assert(!bit(mm0, b));
                }
            }
        }
    }
    proof {
        assert forall|r: int| i <= r < i + 64 && #[trigger] part_sel(t, m, r) implies exists|x: int| np <= x < k && pend@[x] == r by {
            if r >= i + cur {
                lemma_block_row(*c, *lk, t, m, tc, g as int, r);
                lemma_no_bit_of_zero(r - i);
                assert(!bit(mm, r - i));
            }
        }
    }
    k
}

/// Scans the part groups `[g_lo, g_hi)` into `st.buf` (empty on entry), a batch of selected part rows at a time;
/// stops early, returning the part row it stopped at, when that part's candidates might not fit. Returns the next
/// part row to scan (`row_start(g_hi)` when complete).
pub fn scan_groups(c: &Cols, lk: &Lookups, a: ScanArgs, g_lo: usize, g_hi: usize, st: &mut ScanState,
    Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>) -> (next: usize)
    requires
        scan_env(*c, *lk, a, t, m),
        g_lo <= g_hi <= c.p.ng,
        buf_wf(old(st).buf),
        old(st).buf.len == 0,
    ensures
        buf_wf(final(st).buf),
        row_start(*c, g_lo as int) <= next <= row_start(*c, g_hi as int),
        chunk_ok(t, m, buf_view(final(st).buf), row_start(*c, g_lo as int), next as int),
    no_unwind
{
    let bs = c.p.bs;
    let n = c.p.n;
    let pcap = st.pend.len();
    let ghost a0 = row_start(*c, g_lo as int);
    proof {
        lemma_chunk_empty(t, m, a0);
        assert(buf_view(st.buf) =~= Seq::<Cand>::empty());
    }
    let mut g = g_lo;
    while g < g_hi
        invariant
            scan_env(*c, *lk, a, t, m),
            bs == c.p.bs, n == c.p.n, pcap == st.pend@.len(),
            g_lo <= g <= g_hi <= c.p.ng,
            a0 == row_start(*c, g_lo as int),
            a0 <= row_start(*c, g as int),
            buf_wf(st.buf),
            chunk_ok(t, m, buf_view(st.buf), a0, row_start(*c, g as int)),
        decreases g_hi - g,
    {
        proof { lemma_group_rows(*c, t, g as int); }
        let row_lo = g * bs;
        let row_hi = if n - row_lo > bs { row_lo + bs } else { n };
        let sb = c.p.size_b[g];
        let d: i128 = a.size as i128 - sb as i128;
        if 0 <= d && d < 256 && pcap > 0 {
            let tc = d as u8;
            let tb = c.p.type_b[g];
            let mut i = row_lo;
            while i < row_hi
                invariant
                    scan_env(*c, *lk, a, t, m),
                    bs == c.p.bs, n == c.p.n, pcap == st.pend@.len(), pcap > 0,
                    g < c.p.ng, g_lo <= g < g_hi <= c.p.ng,
                    row_lo == g * bs, row_lo <= i <= row_hi, row_hi <= n, row_hi <= row_lo + bs,
                    row_lo as int == row_start(*c, g as int),
                    row_hi as int == row_start(*c, (g + 1) as int),
                    sb == c.p.size_b@[g as int], tb == c.p.type_b@[g as int],
                    d == a.size as int - sb as int, 0 <= d < 256, tc as int == d,
                    a0 == row_start(*c, g_lo as int),
                    a0 <= row_start(*c, g as int),
                    buf_wf(st.buf),
                    chunk_ok(t, m, buf_view(st.buf), a0, i as int),
                decreases row_hi - i,
            {
                // Collect a batch of selected part rows.
                let i0 = i;
                let mut np: usize = 0;
                while i < row_hi && np < pcap
                    invariant
                        scan_env(*c, *lk, a, t, m),
                        bs == c.p.bs, n == c.p.n, pcap == st.pend@.len(),
                        g < c.p.ng, row_lo == g * bs, row_lo <= i0 <= i <= row_hi, row_hi <= n, row_hi <= row_lo + bs,
                        row_hi as int == row_start(*c, (g + 1) as int),
                        sb == c.p.size_b@[g as int], tb == c.p.type_b@[g as int],
                        d == a.size as int - sb as int, 0 <= d < 256, tc as int == d,
                        np <= pcap, np <= i - i0,
                        forall|x: int| 0 <= x < np ==> i0 <= #[trigger] st.pend@[x] < i && part_sel(t, m, st.pend@[x] as int),
                        forall|x: int, y: int| 0 <= x < y < np ==> #[trigger] st.pend@[x] < #[trigger] st.pend@[y],
                        forall|r: int| i0 <= r < i && #[trigger] part_sel(t, m, r) ==> exists|x: int| 0 <= x < np && st.pend@[x] == r,
                        buf_wf(st.buf),
                        chunk_ok(t, m, buf_view(st.buf), a0, i0 as int),
                        a0 == row_start(*c, g_lo as int),
                    decreases row_hi - i,
                {
                    if row_hi - i >= 64 && pcap - np >= 64 {
                        // 64 rows at once (byte-compare mask of the size codes).
                        let ghost p0 = st.pend@;
                        let ghost np0 = np;
                        np = collect_block(c, lk, tc, tb, g, i, &mut st.pend, np, Ghost(t), Ghost(m));
                        proof {
                            assert forall|x: int| 0 <= x < np implies i0 <= #[trigger] st.pend@[x] < i + 64 && part_sel(t, m, st.pend@[x] as int) by {
                                if x < np0 { assert(st.pend@[x] == p0[x]); }
                            }
                            assert forall|x: int, y: int| 0 <= x < y < np implies #[trigger] st.pend@[x] < #[trigger] st.pend@[y] by {
                                if y < np0 {
                                    assert(st.pend@[x] == p0[x] && st.pend@[y] == p0[y]);
                                } else if x < np0 {
                                    assert(st.pend@[x] == p0[x]);
                                }
                            }
                            assert forall|r: int| i0 <= r < i + 64 && #[trigger] part_sel(t, m, r) implies exists|x: int| 0 <= x < np && st.pend@[x] == r by {
                                if r < i {
                                    let x = choose|x: int| 0 <= x < np0 && p0[x] == r;
                                    assert(st.pend@[x] == p0[x]);
                                }
                            }
                        }
                        i = i + 64;
                    } else {
                        assert(part_row_ok(c.p, t.p[i as int], i as int));
                        proof { lemma_in_group(bs as int, g as int, i as int); }
                        let ghost sel = part_sel(t, m, i as int);
                        if c.p.size_c[i] == tc {
                            let e = (tb + c.p.type_c[i] as u64) as usize;
                            assert(lk.like_ok@[e as int] == like_true(Val::Text(txt(c.p.type_o@, c.p.type_y@, e as int)), m.pat));
                            if lk.like_ok[e] {
                                assert(sel);
                                let ghost p0 = st.pend@;
                                put(&mut st.pend, np, i);
                                proof {
                                    assert forall|r: int| i0 <= r < i + 1 && #[trigger] part_sel(t, m, r)
                                        implies exists|x: int| 0 <= x < np + 1 && st.pend@[x] == r by {
                                        if r < i {
                                            let x = choose|x: int| 0 <= x < np && p0[x] == r;
                                            assert(st.pend@[x] == p0[x]);
                                        } else {
                                            assert(st.pend@[np as int] == r);
                                        }
                                    }
                                }
                                np = np + 1;
                            } else {
                                assert(!sel);
                            }
                        } else {
                            assert(!sel);
                        }
                        i = i + 1;
                    }
                }
                touch_batch(c, a, &st.pend, np, &mut st.sink, Ghost(t), Ghost(m));
                // Process the batch in row order.
                let mut q: usize = 0;
                while q < np
                    invariant
                        scan_env(*c, *lk, a, t, m),
                        bs == c.p.bs, n == c.p.n, pcap == st.pend@.len(),
                        g < c.p.ng, g_lo <= g < g_hi <= c.p.ng,
                        row_lo <= i0 <= i <= row_hi, row_hi <= n,
                        row_hi as int == row_start(*c, (g + 1) as int),
                        row_lo as int == row_start(*c, g as int),
                        q <= np, np <= pcap,
                        forall|x: int| 0 <= x < np ==> i0 <= #[trigger] st.pend@[x] < i && part_sel(t, m, st.pend@[x] as int),
                        forall|x: int, y: int| 0 <= x < y < np ==> #[trigger] st.pend@[x] < #[trigger] st.pend@[y],
                        forall|r: int| i0 <= r < i && #[trigger] part_sel(t, m, r) ==> exists|x: int| 0 <= x < np && st.pend@[x] == r,
                        buf_wf(st.buf),
                        a0 == row_start(*c, g_lo as int),
                        a0 <= row_start(*c, g as int),
                        chunk_ok(t, m, buf_view(st.buf), a0, (if q == 0 { i0 as int } else { st.pend@[q - 1] + 1 })),
                    decreases np - q,
                {
                    let r = st.pend[q];
                    let ghost cur = if q == 0 { i0 as int } else { st.pend@[q - 1] + 1 };
                    proof {
                        assert forall|x: int| cur <= x < r implies !#[trigger] part_sel(t, m, x) by {
                            if part_sel(t, m, x) {
                                let y = choose|y: int| 0 <= y < np && st.pend@[y] == x;
                                if y < q {
                                    if y < q - 1 {
                                        assert(st.pend@[y] < st.pend@[q - 1]);
                                    }
                                } else if y > q {
                                    assert(st.pend@[q as int] < st.pend@[y]);
                                }
                            }
                        }
                        if q > 0 {
                            assert(st.pend@[q - 1] < st.pend@[q as int]);
                        }
                        lemma_chunk_extend(t, m, buf_view(st.buf), a0, cur, r as int);
                    }
                    let pk = part_key(c, a, r, Ghost(t), Ghost(m));
                    let (lo, hi) = ps_range(c, a, pk, Ghost(t));
                    if st.buf.v.len() - st.buf.len < hi - lo {
                        proof { lemma_row_start_mono(*c, t, (g + 1) as int, g_hi as int); }
                        return r;
                    }
                    let ghost before = buf_view(st.buf);
                    let ghost blen = st.buf.len;
                    emit_part(c, lk, a, r, pk, lo, hi, &mut st.buf, Ghost(t), Ghost(m));
                    proof {
                        let seg = buf_view(st.buf).subrange(blen as int, st.buf.len as int);
                        lemma_chunk_part(t, m, before, seg, a0, r as int);
                    }
                    q = q + 1;
                }
                proof {
                    let cur = if np == 0 { i0 as int } else { st.pend@[np - 1] + 1 };
                    assert forall|x: int| cur <= x < i implies !#[trigger] part_sel(t, m, x) by {
                        if part_sel(t, m, x) {
                            let y = choose|y: int| 0 <= y < np && st.pend@[y] == x;
                            if y < np - 1 {
                                assert(st.pend@[y] < st.pend@[np - 1]);
                            }
                        }
                    }
                    lemma_chunk_extend(t, m, buf_view(st.buf), a0, cur, i as int);
                }
            }
        } else {
            if pcap == 0 {
                proof { lemma_row_start_mono(*c, t, g as int, g_hi as int); }
                return row_lo;
            }
            proof {
                assert forall|x: int| row_lo <= x < row_hi implies !#[trigger] part_sel(t, m, x) by {
                    assert(part_row_ok(c.p, t.p[x], x));
                    lemma_in_group(bs as int, g as int, x);
                }
                lemma_chunk_extend(t, m, buf_view(st.buf), a0, row_lo as int, row_hi as int);
            }
        }
        proof { lemma_row_start_mono(*c, t, g as int, (g + 1) as int); }
        g = g + 1;
    }
    if g_hi < c.p.ng {
        proof { lemma_group_rows(*c, t, g_hi as int); }
        g_hi * bs
    } else {
        n
    }
}

/// The rows of part group `g < ng`: `g * bs` up to `row_start(g + 1)`, and `row_start(g + 1) - g * bs <= bs`.
proof fn lemma_group_rows(c: Cols, t: Tabs, g: int)
    requires cols_ok(c, t), 0 <= g < c.p.ng,
    ensures
        g * c.p.bs < c.p.n,
        row_start(c, g) == g * c.p.bs,
        row_start(c, g + 1) == if c.p.n - g * c.p.bs > c.p.bs { g * c.p.bs + c.p.bs } else { c.p.n as int },
{
    let bs = c.p.bs as int;
    let ng = c.p.ng as int;
    assert(g * bs <= (ng - 1) * bs) by (nonlinear_arith) requires g <= ng - 1, bs >= 1;
    assert((g + 1) * bs == g * bs + bs) by (nonlinear_arith);
    if g + 1 < ng {
        assert((g + 1) * bs <= (ng - 1) * bs) by (nonlinear_arith) requires g + 1 <= ng - 1, bs >= 1;
    } else {
        assert((g + 1) * bs >= c.p.n);
    }
}

/// Group starts are nondecreasing.
proof fn lemma_row_start_mono(c: Cols, t: Tabs, g1: int, g2: int)
    requires cols_ok(c, t), 0 <= g1 <= g2 <= c.p.ng,
    ensures row_start(c, g1) <= row_start(c, g2),
{
    let bs = c.p.bs as int;
    let ng = c.p.ng as int;
    if g2 < ng {
        assert(g1 * bs <= g2 * bs) by (nonlinear_arith) requires g1 <= g2, bs >= 1;
    } else if g1 < ng {
        assert(g1 * bs <= (ng - 1) * bs) by (nonlinear_arith) requires g1 <= ng - 1, bs >= 1;
    }
}

// ------------------------------------------------------------------------------------------------ tasks

/// One worker: the part groups `[g_lo, g_hi)`, into its preallocated state.
pub struct ScanTask {
    pub c: Cols,
    pub lk: Lookups,
    pub a: ScanArgs,
    pub g_lo: usize,
    pub g_hi: usize,
    pub st: ScanState,
    pub t: Ghost<Tabs>,
    pub m: Ghost<Prm>,
}

impl WorkerTask for ScanTask {
    type Output = (ScanState, usize);

    open spec fn pre(&self) -> bool {
        &&& scan_env(self.c, self.lk, self.a, self.t@, self.m@)
        &&& self.g_lo <= self.g_hi <= self.c.p.ng
        &&& buf_wf(self.st.buf)
        &&& self.st.buf.len == 0
    }

    open spec fn post(&self, out: (ScanState, usize)) -> bool {
        &&& buf_wf(out.0.buf)
        &&& row_start(self.c, self.g_lo as int) <= out.1 <= row_start(self.c, self.g_hi as int)
        &&& chunk_ok(self.t@, self.m@, buf_view(out.0.buf), row_start(self.c, self.g_lo as int), out.1 as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.g_lo as u64, self.g_hi as u64)
    }

    fn run(self) -> (out: (ScanState, usize)) {
        let ScanTask { c, lk, a, g_lo, g_hi, st, t, m } = self;
        let mut st = st;
        let next = scan_groups(&c, &lk, a, g_lo, g_hi, &mut st, t, m);
        (st, next)
    }
}

/// Serial continuation from part row `from` to `to`: one part at a time, each with a buffer of its own; appends
/// the candidates of the rows `[from, to)` to `out`.
pub fn scan_rows_serial(c: &Cols, lk: &Lookups, a: ScanArgs, from: usize, to: usize, out: &mut Vec<Cand>,
    Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>)
    requires scan_env(*c, *lk, a, t, m), from <= to <= c.p.n,
    ensures exists|seg: Seq<Cand>| final(out)@ == old(out)@ + seg && chunk_ok(t, m, seg, from as int, to as int),
{
    let bs = c.p.bs;
    let ghost o0 = out@;
    let ghost mut seg = Seq::<Cand>::empty();
    proof {
        lemma_chunk_empty(t, m, from as int);
        assert(out@ =~= o0 + seg);
    }
    let mut i = from;
    while i < to
        invariant
            scan_env(*c, *lk, a, t, m), bs == c.p.bs, from <= i <= to <= c.p.n,
            out@ == o0 + seg,
            chunk_ok(t, m, seg, from as int, i as int),
        decreases to - i,
    {
        assert(part_row_ok(c.p, t.p[i as int], i as int));
        proof { lemma_grp_bound(c.p.n as int, c.p.bs as int, c.p.ng as int, i as int); }
        let g = grp(i, bs);
        let sz: i64 = c.p.size_b[g] + c.p.size_c[i] as i64;
        let ghost sel = part_sel(t, m, i as int);
        if sz == a.size {
            let e = (c.p.type_b[g] + c.p.type_c[i] as u64) as usize;
            assert(lk.like_ok@[e as int] == like_true(Val::Text(txt(c.p.type_o@, c.p.type_y@, e as int)), m.pat));
            if lk.like_ok[e] {
                assert(sel);
                let pk = part_key(c, a, i, Ghost(t), Ghost(m));
                let (lo, hi) = ps_range(c, a, pk, Ghost(t));
                let mut buf = CandBuf { v: vec![Cand { part: 0, ps: 0, supp: 0, nation: 0, acct: 0 }; hi - lo], len: 0 };
                proof { assert(buf_view(buf) =~= Seq::<Cand>::empty()); }
                emit_part(c, lk, a, i, pk, lo, hi, &mut buf, Ghost(t), Ghost(m));
                let ghost part = buf_view(buf);
                proof {
                    assert(part =~= buf_view(buf).subrange(0, buf.len as int));
                    lemma_chunk_part(t, m, seg, part, from as int, i as int);
                }
                let blen = buf.len;
                let mut v = buf.v;
                v.truncate(blen);
                out.append(&mut v);
                proof {
                    seg = seg + part;
                    assert(out@ =~= o0 + seg);
                }
            } else {
                proof { lemma_chunk_extend(t, m, seg, from as int, i as int, i + 1); }
            }
        } else {
            proof { lemma_chunk_extend(t, m, seg, from as int, i as int, i + 1); }
        }
        i = i + 1;
    }
}

} // verus!
