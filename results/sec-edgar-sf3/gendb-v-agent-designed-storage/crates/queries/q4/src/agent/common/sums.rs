//! Sums of an integer function over an index range (`rsum`), with split, extensionality, zero, single-term,
//! reindexing by a duplicate-free index list, and the bridge to `link::join::sum_of` over a sequence.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::link::join::{sum_of, lemma_sum_of_perm};

verus! {

/// `h(lo) + .. + h(hi - 1)`.
pub open spec fn rsum(lo: int, hi: int, h: spec_fn(int) -> int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { rsum(lo, hi - 1, h) + h(hi - 1) }
}

pub proof fn lemma_rsum_split(lo: int, mid: int, hi: int, h: spec_fn(int) -> int)
    requires lo <= mid <= hi,
    ensures rsum(lo, hi, h) == rsum(lo, mid, h) + rsum(mid, hi, h),
    decreases hi - mid,
{
    if hi > mid {
        lemma_rsum_split(lo, mid, hi - 1, h);
    }
}

pub proof fn lemma_rsum_ext(lo: int, hi: int, h1: spec_fn(int) -> int, h2: spec_fn(int) -> int)
    requires forall|i: int| lo <= i < hi ==> #[trigger] h1(i) == h2(i),
    ensures rsum(lo, hi, h1) == rsum(lo, hi, h2),
    decreases hi - lo,
{
    if hi > lo {
        lemma_rsum_ext(lo, hi - 1, h1, h2);
        assert(h1(hi - 1) == h2(hi - 1));
    }
}

pub proof fn lemma_rsum_zero(lo: int, hi: int, h: spec_fn(int) -> int)
    requires forall|i: int| lo <= i < hi ==> #[trigger] h(i) == 0,
    ensures rsum(lo, hi, h) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_rsum_zero(lo, hi - 1, h);
        assert(h(hi - 1) == 0);
    }
}

pub proof fn lemma_rsum_nonneg(lo: int, hi: int, h: spec_fn(int) -> int)
    requires forall|i: int| lo <= i < hi ==> #[trigger] h(i) >= 0,
    ensures rsum(lo, hi, h) >= 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_rsum_nonneg(lo, hi - 1, h);
        assert(h(hi - 1) >= 0);
    }
}

/// Nonnegative terms summing to zero are all zero.
pub proof fn lemma_rsum_nonneg_zero(lo: int, hi: int, h: spec_fn(int) -> int, i: int)
    requires forall|k: int| lo <= k < hi ==> #[trigger] h(k) >= 0, rsum(lo, hi, h) == 0, lo <= i < hi,
    ensures h(i) == 0,
{
    lemma_rsum_remove(lo, hi, h, i);
    assert forall|k: int| lo <= k < hi implies #[trigger] zero_at(h, i)(k) >= 0 by {}
    lemma_rsum_nonneg(lo, hi, zero_at(h, i));
}

/// Pointwise `h1 <= h2` gives `rsum h1 <= rsum h2`.
pub proof fn lemma_rsum_le(lo: int, hi: int, h1: spec_fn(int) -> int, h2: spec_fn(int) -> int)
    requires forall|i: int| lo <= i < hi ==> #[trigger] h1(i) <= h2(i),
    ensures rsum(lo, hi, h1) <= rsum(lo, hi, h2),
    decreases hi - lo,
{
    if hi > lo {
        lemma_rsum_le(lo, hi - 1, h1, h2);
        assert(h1(hi - 1) <= h2(hi - 1));
    }
}

/// Only index `k` contributes.
pub proof fn lemma_rsum_single(lo: int, hi: int, h: spec_fn(int) -> int, k: int)
    requires lo <= k < hi, forall|i: int| lo <= i < hi && i != k ==> #[trigger] h(i) == 0,
    ensures rsum(lo, hi, h) == h(k),
{
    lemma_rsum_split(lo, k, hi, h);
    lemma_rsum_split(k, k + 1, hi, h);
    lemma_rsum_zero(lo, k, h);
    lemma_rsum_zero(k + 1, hi, h);
    assert(rsum(k, k + 1, h) == rsum(k, k, h) + h(k));
}

/// Only the indices of `[a, b)` contribute.
pub proof fn lemma_rsum_window(lo: int, a: int, b: int, hi: int, h: spec_fn(int) -> int)
    requires lo <= a <= b <= hi, forall|i: int| lo <= i < hi && !(a <= i < b) ==> #[trigger] h(i) == 0,
    ensures rsum(lo, hi, h) == rsum(a, b, h),
{
    lemma_rsum_split(lo, a, hi, h);
    lemma_rsum_split(a, b, hi, h);
    lemma_rsum_zero(lo, a, h);
    lemma_rsum_zero(b, hi, h);
}

/// Adding a function pointwise.
pub proof fn lemma_rsum_add(lo: int, hi: int, h1: spec_fn(int) -> int, h2: spec_fn(int) -> int)
    ensures rsum(lo, hi, |i: int| h1(i) + h2(i)) == rsum(lo, hi, h1) + rsum(lo, hi, h2),
    decreases hi - lo,
{
    if hi > lo {
        lemma_rsum_add(lo, hi - 1, h1, h2);
    }
}

/// `h` with index `k` zeroed.
pub open spec fn zero_at(h: spec_fn(int) -> int, k: int) -> spec_fn(int) -> int {
    |i: int| if i == k { 0 } else { h(i) }
}

pub proof fn lemma_rsum_remove(lo: int, hi: int, h: spec_fn(int) -> int, k: int)
    requires lo <= k < hi,
    ensures rsum(lo, hi, h) == rsum(lo, hi, zero_at(h, k)) + h(k),
{
    let z = zero_at(h, k);
    lemma_rsum_split(lo, k, hi, h);
    lemma_rsum_split(k, k + 1, hi, h);
    lemma_rsum_split(lo, k, hi, z);
    lemma_rsum_split(k, k + 1, hi, z);
    lemma_rsum_ext(lo, k, h, z);
    lemma_rsum_ext(k + 1, hi, h, z);
    assert(rsum(k, k, h) == 0 && rsum(k, k, z) == 0);
    assert(rsum(k, k + 1, h) == rsum(k, k, h) + h(k));
    assert(rsum(k, k + 1, z) == rsum(k, k, z) + z(k));
    assert(z(k) == 0);
}

/// Reindexing: when every index with a nonzero term is listed exactly once in `idx`, the sum over `[0, n)` is the
/// sum over the list.
pub proof fn lemma_rsum_reindex(n: int, h: spec_fn(int) -> int, idx: Seq<int>)
    requires
        idx.no_duplicates(),
        forall|k: int| 0 <= k < idx.len() ==> 0 <= #[trigger] idx[k] < n,
        forall|i: int| 0 <= i < n && h(i) != 0 ==> #[trigger] idx.contains(i),
    ensures rsum(0, n, h) == rsum(0, idx.len() as int, |k: int| h(idx[k])),
    decreases idx.len(),
{
    if idx.len() == 0 {
        assert forall|i: int| 0 <= i < n implies #[trigger] h(i) == 0 by {
            if h(i) != 0 { assert(idx.contains(i)); }
        }
        lemma_rsum_zero(0, n, h);
    } else {
        let k = idx.last();
        let ii = idx.drop_last();
        let z = zero_at(h, k);
        assert(idx[idx.len() - 1] == k);
        lemma_rsum_remove(0, n, h, k);
        assert forall|i: int| 0 <= i < n && z(i) != 0 implies #[trigger] ii.contains(i) by {
            assert(i != k && h(i) != 0);
            assert(idx.contains(i));
            let m = choose|m: int| 0 <= m < idx.len() && idx[m] == i;
            assert(m != idx.len() - 1);
            assert(ii[m] == i);
        }
        assert forall|m: int| 0 <= m < ii.len() implies 0 <= #[trigger] ii[m] < n by { assert(ii[m] == idx[m]); }
        lemma_rsum_reindex(n, z, ii);
        // The listed terms: none of the earlier indices is `k`.
        assert forall|m: int| 0 <= m < ii.len() implies #[trigger] z(ii[m]) == h(ii[m]) by {
            assert(ii[m] == idx[m]);
            assert(idx[m] != idx[idx.len() - 1]);
        }
        let hz = |m: int| z(ii[m]);
        let hh = |m: int| h(idx[m]);
        lemma_rsum_ext(0, ii.len() as int, hz, hh);
        assert(rsum(0, idx.len() as int, hh) == rsum(0, ii.len() as int, hh) + hh(ii.len() as int));
    }
}

/// `sum_of` over a sequence is `rsum` over its positions.
pub proof fn lemma_sum_of_rsum(rows: Seq<Row>, f: spec_fn(Row) -> int)
    ensures sum_of(rows, f) == rsum(0, rows.len() as int, |i: int| f(rows[i])),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        lemma_sum_of_rsum(ri, f);
        lemma_rsum_ext(0, ri.len() as int, |i: int| f(ri[i]), |i: int| f(rows[i]));
        assert(rows.last() == rows[rows.len() - 1]);
    }
}

/// A sequence with the multiset of another: the same sums.
pub proof fn lemma_sum_of_permuted(rows: Seq<Row>, p: Seq<u64>, f: spec_fn(Row) -> int)
    requires Seq::new(rows.len(), |i: int| rows[p[i] as int]).to_multiset() == rows.to_multiset(),
    ensures sum_of(rows, f) == rsum(0, rows.len() as int, |i: int| f(rows[p[i] as int])),
{
    let s = Seq::new(rows.len(), |i: int| rows[p[i] as int]);
    lemma_sum_of_perm(s, rows, f);
    lemma_sum_of_rsum(s, f);
    lemma_rsum_ext(0, rows.len() as int, |i: int| f(s[i]), |i: int| f(rows[p[i] as int]));
}

} // verus!
