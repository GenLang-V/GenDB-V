//! Sums of integer terms over index ranges `[lo, hi)` (`range_sum`, recursive on the last index), with the laws a
//! partitioned loop needs: splitting a range, pointwise-equal terms, and term bounds.
use vstd::prelude::*;

verus! {

/// `f(lo) + .. + f(hi - 1)` (0 for an empty range).
pub open spec fn range_sum(lo: int, hi: int, f: spec_fn(int) -> int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { range_sum(lo, hi - 1, f) + f(hi - 1) }
}

/// A range sum is the sum over its two halves.
pub proof fn lemma_range_sum_split(lo: int, mid: int, hi: int, f: spec_fn(int) -> int)
    requires lo <= mid <= hi,
    ensures range_sum(lo, hi, f) == range_sum(lo, mid, f) + range_sum(mid, hi, f),
    decreases hi - mid,
{
    if hi > mid {
        lemma_range_sum_split(lo, mid, hi - 1, f);
    }
}

/// One more index at the end.
pub proof fn lemma_range_sum_step(lo: int, hi: int, f: spec_fn(int) -> int)
    requires lo <= hi,
    ensures range_sum(lo, hi + 1, f) == range_sum(lo, hi, f) + f(hi),
{
}

/// Range sums of pointwise equal terms are equal.
pub proof fn lemma_range_sum_ext(lo: int, hi: int, f: spec_fn(int) -> int, g: spec_fn(int) -> int)
    requires forall|r: int| lo <= r < hi ==> #[trigger] f(r) == g(r),
    ensures range_sum(lo, hi, f) == range_sum(lo, hi, g),
    decreases hi - lo,
{
    if hi > lo {
        lemma_range_sum_ext(lo, hi - 1, f, g);
    }
}

/// Terms in `[a, b]` give a sum in `[a * (hi - lo), b * (hi - lo)]`.
pub proof fn lemma_range_sum_bounds(lo: int, hi: int, f: spec_fn(int) -> int, a: int, b: int)
    requires lo <= hi, forall|r: int| lo <= r < hi ==> a <= #[trigger] f(r) <= b,
    ensures a * (hi - lo) <= range_sum(lo, hi, f) <= b * (hi - lo),
    decreases hi - lo,
{
    if hi > lo {
        lemma_range_sum_bounds(lo, hi - 1, f, a, b);
        assert(a * (hi - lo) == a * (hi - 1 - lo) + a) by (nonlinear_arith);
        assert(b * (hi - lo) == b * (hi - 1 - lo) + b) by (nonlinear_arith);
    } else {
        assert(a * (hi - lo) == 0 && b * (hi - lo) == 0) by (nonlinear_arith) requires hi - lo == 0;
    }
}

} // verus!
