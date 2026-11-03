//! Sums over relations (`link::join::sum_of`): guarded and scaled terms, a term that vanishes off one row,
//! index ranges (`subrange`) with their one-step, split and all-zero laws, and nonnegative sums.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::link::join::*;

verus! {

/// A guard `p` that does not depend on the row, and a factor `a`, move out of the sum.
pub proof fn lemma_sum_guard(rows: Seq<Row>, p: bool, a: int, q: spec_fn(Row) -> bool, f: spec_fn(Row) -> int)
    ensures
        sum_of(rows, |x: Row| if p && q(x) { a * f(x) } else { 0int })
            == if p { a * sum_of(rows, |x: Row| if q(x) { f(x) } else { 0int }) } else { 0int },
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        lemma_sum_guard(ri, p, a, q, f);
        let x = rows.last();
        let s = sum_of(ri, |x: Row| if q(x) { f(x) } else { 0int });
        let t = if q(x) { f(x) } else { 0int };
        assert(a * (s + t) == a * s + a * t) by (nonlinear_arith);
    }
}

/// A constant factor moves out of the sum.
pub proof fn lemma_sum_scale(rows: Seq<Row>, a: int, f: spec_fn(Row) -> int)
    ensures sum_of(rows, |x: Row| a * f(x)) == a * sum_of(rows, f),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        lemma_sum_scale(ri, a, f);
        let s = sum_of(ri, f);
        let t = f(rows.last());
        assert(a * (s + t) == a * s + a * t) by (nonlinear_arith);
    }
}

/// A term that vanishes on every row but row `i`: the sum is that row's term.
pub proof fn lemma_sum_single(rows: Seq<Row>, f: spec_fn(Row) -> int, i: int)
    requires
        0 <= i < rows.len(),
        forall|j: int| 0 <= j < rows.len() && j != i ==> f(#[trigger] rows[j]) == 0,
    ensures sum_of(rows, f) == f(rows[i]),
{
    lemma_sum_of_remove(rows, i, f);
    let r = rows.remove(i);
    assert forall|j: int| 0 <= j < r.len() implies f(#[trigger] r[j]) == 0 by {
        if j < i {
            assert(r[j] == rows[j]);
        } else {
            assert(r[j] == rows[j + 1]);
        }
    }
    lemma_sum_of_zero(r, f);
}

/// The range `lo..hi + 1` is the range `lo..hi` and row `hi`.
pub proof fn lemma_sum_range_step(rows: Seq<Row>, f: spec_fn(Row) -> int, lo: int, hi: int)
    requires 0 <= lo <= hi < rows.len(),
    ensures sum_of(rows.subrange(lo, hi + 1), f) == sum_of(rows.subrange(lo, hi), f) + f(rows[hi]),
{
    assert(rows.subrange(lo, hi + 1).drop_last() =~= rows.subrange(lo, hi));
    assert(rows.subrange(lo, hi + 1).last() == rows[hi]);
}

/// The empty range sums to zero.
pub proof fn lemma_sum_range_empty(rows: Seq<Row>, f: spec_fn(Row) -> int, lo: int)
    requires 0 <= lo <= rows.len(),
    ensures sum_of(rows.subrange(lo, lo), f) == 0,
{
    assert(rows.subrange(lo, lo).len() == 0);
}

/// Adjacent ranges add.
pub proof fn lemma_sum_range_split(rows: Seq<Row>, f: spec_fn(Row) -> int, lo: int, mid: int, hi: int)
    requires 0 <= lo <= mid <= hi <= rows.len(),
    ensures sum_of(rows.subrange(lo, hi), f) == sum_of(rows.subrange(lo, mid), f) + sum_of(rows.subrange(mid, hi), f),
{
    assert(rows.subrange(lo, hi) =~= rows.subrange(lo, mid) + rows.subrange(mid, hi));
    lemma_sum_of_append(rows.subrange(lo, mid), rows.subrange(mid, hi), f);
}

/// A range whose terms all vanish sums to zero.
pub proof fn lemma_sum_range_zero(rows: Seq<Row>, f: spec_fn(Row) -> int, lo: int, hi: int)
    requires
        0 <= lo <= hi <= rows.len(),
        forall|j: int| lo <= j < hi ==> f(#[trigger] rows[j]) == 0,
    ensures sum_of(rows.subrange(lo, hi), f) == 0,
{
    let r = rows.subrange(lo, hi);
    assert forall|j: int| 0 <= j < r.len() implies f(#[trigger] r[j]) == 0 by {
        assert(r[j] == rows[lo + j]);
    }
    lemma_sum_of_zero(r, f);
}

/// The whole relation is its range `0..len`.
pub proof fn lemma_sum_range_all(rows: Seq<Row>, f: spec_fn(Row) -> int)
    ensures sum_of(rows.subrange(0, rows.len() as int), f) == sum_of(rows, f),
{
    assert(rows.subrange(0, rows.len() as int) =~= rows);
}

/// Nonnegative terms: the sum of a range is at most the sum of any range containing it.
pub proof fn lemma_sum_range_mono(rows: Seq<Row>, f: spec_fn(Row) -> int, lo: int, hi: int, lo2: int, hi2: int)
    requires
        0 <= lo2 <= lo <= hi <= hi2 <= rows.len(),
        forall|j: int| 0 <= j < rows.len() ==> f(#[trigger] rows[j]) >= 0,
    ensures
        0 <= sum_of(rows.subrange(lo, hi), f) <= sum_of(rows.subrange(lo2, hi2), f),
{
    lemma_sum_range_split(rows, f, lo2, lo, hi2);
    lemma_sum_range_split(rows, f, lo, hi, hi2);
    lemma_sum_range_nonneg(rows, f, lo2, lo);
    lemma_sum_range_nonneg(rows, f, lo, hi);
    lemma_sum_range_nonneg(rows, f, hi, hi2);
}

/// Nonnegative terms have a nonnegative range sum.
pub proof fn lemma_sum_range_nonneg(rows: Seq<Row>, f: spec_fn(Row) -> int, lo: int, hi: int)
    requires
        0 <= lo <= hi <= rows.len(),
        forall|j: int| 0 <= j < rows.len() ==> f(#[trigger] rows[j]) >= 0,
    ensures sum_of(rows.subrange(lo, hi), f) >= 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_sum_range_nonneg(rows, f, lo, hi - 1);
        lemma_sum_range_step(rows, f, lo, hi - 1);
    } else {
        lemma_sum_range_empty(rows, f, lo);
    }
}

} // verus!
