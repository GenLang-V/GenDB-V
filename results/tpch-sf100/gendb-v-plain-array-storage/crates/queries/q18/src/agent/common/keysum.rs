//! Per-key sums over a key column and a value column (`ksum`, `kcount`): the sum and number of the values of the
//! rows `lo..hi` whose key is `v`, with their range laws. General: no query, table or column is named.
use vstd::prelude::*;

verus! {

/// Sum of `vals[i]` over the rows `i` in `lo..hi` with `keys[i] == v`.
pub open spec fn ksum(keys: Seq<i64>, vals: Seq<i128>, v: i64, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { ksum(keys, vals, v, lo, hi - 1) + if keys[hi - 1] == v { vals[hi - 1] as int } else { 0 } }
}

/// Number of rows `i` in `lo..hi` with `keys[i] == v`.
pub open spec fn kcount(keys: Seq<i64>, v: i64, lo: int, hi: int) -> nat
    decreases hi - lo,
{
    if hi <= lo { 0 } else { kcount(keys, v, lo, hi - 1) + if keys[hi - 1] == v { 1nat } else { 0nat } }
}

/// One more row at the end of the range.
pub proof fn lemma_k_step(keys: Seq<i64>, vals: Seq<i128>, v: i64, lo: int, hi: int)
    requires lo <= hi,
    ensures
        ksum(keys, vals, v, lo, hi + 1) == ksum(keys, vals, v, lo, hi) + if keys[hi] == v { vals[hi] as int } else { 0 },
        kcount(keys, v, lo, hi + 1) == kcount(keys, v, lo, hi) + if keys[hi] == v { 1nat } else { 0nat },
{
}

/// The empty range.
pub proof fn lemma_k_empty(keys: Seq<i64>, vals: Seq<i128>, v: i64, lo: int)
    ensures ksum(keys, vals, v, lo, lo) == 0, kcount(keys, v, lo, lo) == 0,
{
}

/// Adjacent ranges add.
pub proof fn lemma_k_split(keys: Seq<i64>, vals: Seq<i128>, v: i64, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures
        ksum(keys, vals, v, lo, hi) == ksum(keys, vals, v, lo, mid) + ksum(keys, vals, v, mid, hi),
        kcount(keys, v, lo, hi) == kcount(keys, v, lo, mid) + kcount(keys, v, mid, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_k_split(keys, vals, v, lo, mid, hi - 1);
    }
}

/// A range without a row of key `v` has zero count and sum.
pub proof fn lemma_k_absent(keys: Seq<i64>, vals: Seq<i128>, v: i64, lo: int, hi: int)
    requires forall|j: int| lo <= j < hi ==> keys[j] != v,
    ensures ksum(keys, vals, v, lo, hi) == 0, kcount(keys, v, lo, hi) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_k_absent(keys, vals, v, lo, hi - 1);
    }
}

/// A range with a row of key `v` has a positive count; a positive count has a witness row.
pub proof fn lemma_k_witness(keys: Seq<i64>, v: i64, lo: int, hi: int)
    ensures (kcount(keys, v, lo, hi) > 0) == (exists|j: int| lo <= j < hi && keys[j] == v),
    decreases hi - lo,
{
    if hi > lo {
        lemma_k_witness(keys, v, lo, hi - 1);
        if keys[hi - 1] == v {
            assert(lo <= hi - 1 < hi && keys[hi - 1] == v);
        }
        if exists|j: int| lo <= j < hi && keys[j] == v {
            let j = choose|j: int| lo <= j < hi && keys[j] == v;
            if j < hi - 1 {
                assert(lo <= j < hi - 1 && keys[j] == v);
            }
        }
    }
}

/// `|ksum| <= kcount * b` when every value of a row of key `v` is within `b` in absolute value.
pub proof fn lemma_k_bound(keys: Seq<i64>, vals: Seq<i128>, v: i64, lo: int, hi: int, b: int)
    requires 0 <= b, forall|j: int| lo <= j < hi ==> -b <= #[trigger] vals[j] <= b,
    ensures
        -(kcount(keys, v, lo, hi) as int) * b <= ksum(keys, vals, v, lo, hi) <= (kcount(keys, v, lo, hi) as int) * b,
        lo <= hi ==> kcount(keys, v, lo, hi) <= hi - lo,
    decreases hi - lo,
{
    if hi > lo {
        lemma_k_bound(keys, vals, v, lo, hi - 1, b);
        let c = kcount(keys, v, lo, hi - 1) as int;
        let s = ksum(keys, vals, v, lo, hi - 1);
        let x = vals[hi - 1] as int;
        assert(-b <= x <= b);
        assert(-c * b <= s <= c * b);
        if keys[hi - 1] == v {
            assert(kcount(keys, v, lo, hi) as int == c + 1);
            assert(ksum(keys, vals, v, lo, hi) == s + x);
            assert((c + 1) * b == c * b + b) by (nonlinear_arith);
            assert(-(c + 1) * b == -c * b - b) by (nonlinear_arith);
        }
    }
}

} // verus!
