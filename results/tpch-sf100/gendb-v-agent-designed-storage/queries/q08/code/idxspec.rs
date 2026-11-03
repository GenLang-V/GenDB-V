//! Meaning of the index-driven Q8 kernel (`idx`): the per-year accumulators over positions of lineitem's l_partkey
//! key index (`acc_idx`: position `p` contributes what stored row `drow(p)` contributes, `model::lc`), over a batch of
//! buffered rows (`acc_rows`), and the reindexing lemma: since the key index is a bijection of the stored rows,
//! the accumulators over all its positions are those over all stored rows (`lemma_idx_all`).
use vstd::prelude::*;
use crate::stores::factsdir::interface::common::colfmt::{is_perm, covered};
use super::model::*;
use super::join::LHit;
use super::idx::Dirs;

verus! {

// ------------------------------------------------------------------------------------------------ key index

/// Stored lineitem row at position `p` of the l_partkey key index.
pub open spec fn drow(c: Cols, d: Dirs, p: int) -> int {
    d.ib@[p / c.bs_l as int] + d.ic@[p]
}

/// The key index as a row map over the `n_l` positions.
pub open spec fn dmap(c: Cols, d: Dirs) -> Seq<int> {
    Seq::new(c.n_l as nat, |p: int| drow(c, d, p))
}

/// The contribution of key index position `p`.
pub open spec fn gl(c: Cols, pm: spec_fn(int) -> bool, ns: NStat, d: Dirs, p: int) -> Option<LHit> {
    lc(c, pm, ns, drow(c, d, p))
}

/// The accumulators of key index positions `[a, b)`.
pub open spec fn acc_idx(c: Cols, pm: spec_fn(int) -> bool, ns: NStat, d: Dirs, a: int, b: int) -> AccS
    decreases b - a,
{
    if b <= a { acc_zero() } else { acc_add(acc_idx(c, pm, ns, d, a, b - 1), acc_of(gl(c, pm, ns, d, b - 1))) }
}

/// Adjacent position ranges add.
pub proof fn lemma_idx_split(c: Cols, pm: spec_fn(int) -> bool, ns: NStat, d: Dirs, a: int, b: int, e: int)
    requires a <= b <= e,
    ensures acc_idx(c, pm, ns, d, a, e) == acc_add(acc_idx(c, pm, ns, d, a, b), acc_idx(c, pm, ns, d, b, e)),
    decreases e - b,
{
    if b < e {
        lemma_idx_split(c, pm, ns, d, a, b, e - 1);
        lemma_acc_add_assoc(acc_idx(c, pm, ns, d, a, b), acc_idx(c, pm, ns, d, b, e - 1), acc_of(gl(c, pm, ns, d, e - 1)));
    } else {
        lemma_acc_add_zero(acc_idx(c, pm, ns, d, a, b));
    }
}

/// Positions without a contribution add nothing.
pub proof fn lemma_idx_none(c: Cols, pm: spec_fn(int) -> bool, ns: NStat, d: Dirs, a: int, b: int)
    requires forall|p: int| a <= p < b ==> #[trigger] gl(c, pm, ns, d, p) is None,
    ensures acc_idx(c, pm, ns, d, a, b) == acc_zero(),
    decreases b - a,
{
    if a < b {
        lemma_idx_none(c, pm, ns, d, a, b - 1);
    }
}

/// Counts and sums of a position range are bounded by its length and masses.
pub proof fn lemma_idx_sane(c: Cols, pm: spec_fn(int) -> bool, ns: NStat, d: Dirs, a: int, b: int)
    requires a <= b,
    ensures acc_sane(acc_idx(c, pm, ns, d, a, b), b - a),
    decreases b - a,
{
    if a < b {
        lemma_idx_sane(c, pm, ns, d, a, b - 1);
    }
}

/// Masses never decrease as a position range grows.
pub proof fn lemma_idx_mass_mono(c: Cols, pm: spec_fn(int) -> bool, ns: NStat, d: Dirs, a: int, b: int, e: int)
    requires a <= b <= e,
    ensures
        acc_idx(c, pm, ns, d, a, b).m0 <= acc_idx(c, pm, ns, d, a, e).m0,
        acc_idx(c, pm, ns, d, a, b).m1 <= acc_idx(c, pm, ns, d, a, e).m1,
{
    lemma_idx_split(c, pm, ns, d, a, b, e);
    lemma_idx_sane(c, pm, ns, d, b, e);
}

// ------------------------------------------------------------------------------------------------ batches

/// The accumulators of the first `n` buffered rows.
pub open spec fn acc_rows(c: Cols, pm: spec_fn(int) -> bool, ns: NStat, rows: Seq<usize>, n: int) -> AccS
    decreases n,
{
    if n <= 0 { acc_zero() } else { acc_add(acc_rows(c, pm, ns, rows, n - 1), acc_of(lc(c, pm, ns, rows[n - 1] as int))) }
}

/// Only the first `n` rows matter.
pub proof fn lemma_rows_ext(c: Cols, pm: spec_fn(int) -> bool, ns: NStat, r1: Seq<usize>, r2: Seq<usize>, n: int)
    requires forall|q: int| 0 <= q < n ==> r1[q] == r2[q],
    ensures acc_rows(c, pm, ns, r1, n) == acc_rows(c, pm, ns, r2, n),
    decreases n,
{
    if n > 0 {
        lemma_rows_ext(c, pm, ns, r1, r2, n - 1);
    }
}

/// Writing row `s` at slot `m` extends the first `m` rows by `s`.
pub proof fn lemma_rows_put(c: Cols, pm: spec_fn(int) -> bool, ns: NStat, r: Seq<usize>, m: int, s: usize)
    requires 0 <= m < r.len(),
    ensures
        acc_rows(c, pm, ns, r.update(m, s), m + 1) == acc_add(acc_rows(c, pm, ns, r, m), acc_of(lc(c, pm, ns, s as int))),
        acc_rows(c, pm, ns, r.update(m, s), m) == acc_rows(c, pm, ns, r, m),
{
    lemma_rows_ext(c, pm, ns, r.update(m, s), r, m);
}

/// Counts and sums of a batch are bounded by its length and masses.
pub proof fn lemma_rows_sane(c: Cols, pm: spec_fn(int) -> bool, ns: NStat, r: Seq<usize>, n: int)
    requires n >= 0,
    ensures acc_sane(acc_rows(c, pm, ns, r, n), n),
    decreases n,
{
    if n > 0 {
        lemma_rows_sane(c, pm, ns, r, n - 1);
    }
}

/// Masses never decrease along a batch.
pub proof fn lemma_rows_mass_mono(c: Cols, pm: spec_fn(int) -> bool, ns: NStat, r: Seq<usize>, a: int, b: int)
    requires 0 <= a <= b,
    ensures
        acc_rows(c, pm, ns, r, a).m0 <= acc_rows(c, pm, ns, r, b).m0,
        acc_rows(c, pm, ns, r, a).m1 <= acc_rows(c, pm, ns, r, b).m1,
    decreases b - a,
{
    if a < b {
        lemma_rows_mass_mono(c, pm, ns, r, a, b - 1);
    }
}

/// Sanity of a sum: counts add, sums stay within masses.
pub proof fn lemma_sane_add(x: AccS, y: AccS, k: int, n: int)
    requires acc_sane(x, k), acc_sane(y, n),
    ensures acc_sane(acc_add(x, y), k + n),
{
}

/// A sanity bound holds for any larger count.
pub proof fn lemma_sane_wider(x: AccS, k: int, n: int)
    requires acc_sane(x, k), k <= n,
    ensures acc_sane(x, n),
{
}

// ------------------------------------------------------------------------------------------------ reindexing

/// The accumulators of `h` over the rows a map `m` names at `[0, k)`.
pub open spec fn acc_over(m: Seq<int>, h: spec_fn(int) -> AccS, k: int) -> AccS
    decreases k,
{
    if k <= 0 { acc_zero() } else { acc_add(acc_over(m, h, k - 1), h(m[k - 1])) }
}

/// The accumulators of `h` over `[0, k)`.
pub open spec fn acc_upto(h: spec_fn(int) -> AccS, k: int) -> AccS
    decreases k,
{
    if k <= 0 { acc_zero() } else { acc_add(acc_upto(h, k - 1), h(k - 1)) }
}

proof fn lemma_over_ext(a: Seq<int>, b: Seq<int>, h: spec_fn(int) -> AccS, k: int)
    requires 0 <= k, k <= a.len(), k <= b.len(), forall|q: int| 0 <= q < k ==> a[q] == b[q],
    ensures acc_over(a, h, k) == acc_over(b, h, k),
    decreases k,
{
    if k > 0 {
        lemma_over_ext(a, b, h, k - 1);
    }
}

proof fn lemma_over_remove(m: Seq<int>, h: spec_fn(int) -> AccS, k: int, j0: int)
    requires 0 <= j0 < k <= m.len(),
    ensures acc_over(m, h, k) == acc_add(acc_over(m.remove(j0), h, k - 1), h(m[j0])),
    decreases k,
{
    if k - 1 == j0 {
        assert forall|q: int| 0 <= q < k - 1 implies m.remove(j0)[q] == m[q] by {}
        lemma_over_ext(m, m.remove(j0), h, k - 1);
    } else {
        lemma_over_remove(m, h, k - 1, j0);
        assert(m.remove(j0)[k - 2] == m[k - 1]);
    }
}

proof fn lemma_perm_remove(rmap: Seq<int>, n: int, j0: int)
    requires is_perm(rmap, n), 0 <= j0 < n, rmap[j0] == n - 1,
    ensures is_perm(rmap.remove(j0), n - 1),
{
    let r = rmap.remove(j0);
    assert forall|j: int| 0 <= j < n - 1 implies 0 <= #[trigger] r[j] < n - 1 by {
        let k = if j < j0 { j } else { j + 1 };
        assert(r[j] == rmap[k]);
        assert(rmap[k] != rmap[j0]);
    }
    assert forall|a: int, b: int| 0 <= a < n - 1 && 0 <= b < n - 1 && a != b implies #[trigger] r[a] != #[trigger] r[b] by {
        let ka = if a < j0 { a } else { a + 1 };
        let kb = if b < j0 { b } else { b + 1 };
        assert(r[a] == rmap[ka] && r[b] == rmap[kb]);
    }
    assert forall|i: int| 0 <= i < n - 1 implies #[trigger] covered(r, i) by {
        assert(covered(rmap, i));
        let k = choose|k: int| 0 <= k < rmap.len() && rmap[k] == i;
        assert(k != j0);
        let j = if k < j0 { k } else { k - 1 };
        assert(r[j] == i);
    }
}

/// Over a bijection of `[0, n)`, the accumulators are those over `[0, n)`.
pub proof fn lemma_over_perm(m: Seq<int>, n: int, h: spec_fn(int) -> AccS)
    requires is_perm(m, n),
    ensures acc_over(m, h, n) == acc_upto(h, n),
    decreases n,
{
    if n > 0 {
        assert(covered(m, n - 1));
        let j0 = choose|j: int| 0 <= j < m.len() && m[j] == n - 1;
        lemma_over_remove(m, h, n, j0);
        lemma_perm_remove(m, n, j0);
        lemma_over_perm(m.remove(j0), n - 1, h);
    }
}

/// One row's accumulators as a function of the stored row.
pub open spec fn row_acc(c: Cols, pm: spec_fn(int) -> bool, ns: NStat) -> spec_fn(int) -> AccS {
    |s: int| acc_of(lc(c, pm, ns, s))
}

proof fn lemma_idx_over(c: Cols, pm: spec_fn(int) -> bool, ns: NStat, d: Dirs, k: int)
    requires 0 <= k <= c.n_l,
    ensures acc_idx(c, pm, ns, d, 0, k) == acc_over(dmap(c, d), row_acc(c, pm, ns), k),
    decreases k,
{
    if k > 0 {
        lemma_idx_over(c, pm, ns, d, k - 1);
        assert(dmap(c, d)[k - 1] == drow(c, d, k - 1));
    }
}

proof fn lemma_range_upto(c: Cols, pm: spec_fn(int) -> bool, ns: NStat, k: int)
    requires 0 <= k,
    ensures acc_range(c, pm, ns, 0, k) == acc_upto(row_acc(c, pm, ns), k),
    decreases k,
{
    if k > 0 {
        lemma_range_upto(c, pm, ns, k - 1);
    }
}

/// All positions of a bijective key index accumulate as all stored rows.
pub proof fn lemma_idx_all(c: Cols, pm: spec_fn(int) -> bool, ns: NStat, d: Dirs)
    requires is_perm(dmap(c, d), c.n_l as int),
    ensures acc_idx(c, pm, ns, d, 0, c.n_l as int) == acc_range(c, pm, ns, 0, c.n_l as int),
{
    lemma_idx_over(c, pm, ns, d, c.n_l as int);
    lemma_over_perm(dmap(c, d), c.n_l as int, row_acc(c, pm, ns));
    lemma_range_upto(c, pm, ns, c.n_l as int);
}

} // verus!
