//! Sums of an integer function over a half-open range of integers (`isum(f, a, b) = f(a) + .. + f(b - 1)`), with
//! the step, split, zero, extensionality and nonnegativity lemmas, and the bridge to `link::join::sum_of` over a
//! subrange of rows.
use vstd::prelude::*;
use crate::spec::value::Row;
use crate::link::join::sum_of;

verus! {

/// `f(a) + f(a + 1) + .. + f(b - 1)` (0 when `b <= a`).
pub open spec fn isum(f: spec_fn(int) -> int, a: int, b: int) -> int
    decreases b - a,
{
    if b <= a { 0 } else { isum(f, a, b - 1) + f(b - 1) }
}

/// One more term at the top.
pub proof fn lemma_isum_step(f: spec_fn(int) -> int, a: int, b: int)
    requires a <= b,
    ensures isum(f, a, b + 1) == isum(f, a, b) + f(b),
{
}

/// The empty range.
pub proof fn lemma_isum_empty(f: spec_fn(int) -> int, a: int)
    ensures isum(f, a, a) == 0,
{
}

/// A range splits at any point inside it.
pub proof fn lemma_isum_split(f: spec_fn(int) -> int, a: int, m: int, b: int)
    requires a <= m <= b,
    ensures isum(f, a, b) == isum(f, a, m) + isum(f, m, b),
    decreases b - m,
{
    if m < b {
        lemma_isum_split(f, a, m, b - 1);
    }
}

/// Functions equal on the range have equal sums.
pub proof fn lemma_isum_ext(f: spec_fn(int) -> int, g: spec_fn(int) -> int, a: int, b: int)
    requires forall|i: int| a <= i < b ==> #[trigger] f(i) == g(i),
    ensures isum(f, a, b) == isum(g, a, b),
    decreases b - a,
{
    if a < b {
        lemma_isum_ext(f, g, a, b - 1);
    }
}

/// A range of zero terms sums to 0.
pub proof fn lemma_isum_zero(f: spec_fn(int) -> int, a: int, b: int)
    requires forall|i: int| a <= i < b ==> #[trigger] f(i) == 0,
    ensures isum(f, a, b) == 0,
    decreases b - a,
{
    if a < b {
        lemma_isum_zero(f, a, b - 1);
    }
}

/// A range of nonnegative terms has a nonnegative sum.
pub proof fn lemma_isum_nonneg(f: spec_fn(int) -> int, a: int, b: int)
    requires forall|i: int| a <= i < b ==> #[trigger] f(i) >= 0,
    ensures isum(f, a, b) >= 0,
    decreases b - a,
{
    if a < b {
        lemma_isum_nonneg(f, a, b - 1);
    }
}

/// A sum over a subrange of rows is the integer sum of the terms of its positions.
pub proof fn lemma_sum_of_isum(rows: Seq<Row>, g: spec_fn(Row) -> int, a: int, b: int)
    requires 0 <= a <= b <= rows.len(),
    ensures sum_of(rows.subrange(a, b), g) == isum(|i: int| g(rows[i]), a, b),
    decreases b - a,
{
    let f = |i: int| g(rows[i]);
    if a == b {
        assert(rows.subrange(a, b).len() == 0);
    } else {
        lemma_sum_of_isum(rows, g, a, b - 1);
        let s = rows.subrange(a, b);
        assert(s.drop_last() =~= rows.subrange(a, b - 1));
        assert(s.last() == rows[b - 1]);
        assert(isum(f, a, b) == isum(f, a, b - 1) + f(b - 1));
    }
}

/// A sum cut at nondecreasing boundaries `starts[0] == 0 <= starts[1] <= ..`: when segment `i` sums to `v(b + i)`,
/// the whole prefix up to `starts[cnt]` sums to `v(b) + .. + v(b + cnt - 1)`.
pub proof fn lemma_isum_regroup(f: spec_fn(int) -> int, v: spec_fn(int) -> int, starts: Seq<u32>, b: int, cnt: int)
    requires
        0 <= cnt < starts.len(),
        starts[0] == 0,
        forall|i: int| 0 <= i < cnt ==> #[trigger] starts[i] <= starts[i + 1],
        forall|i: int| 0 <= i < cnt ==> #[trigger] isum(f, starts[i] as int, starts[i + 1] as int) == v(b + i),
    ensures isum(f, 0, starts[cnt] as int) == isum(v, b, b + cnt),
    decreases cnt,
{
    if cnt > 0 {
        lemma_isum_regroup(f, v, starts, b, cnt - 1);
        assert(starts[cnt - 1] <= starts[cnt]);
        lemma_isum_split(f, 0, starts[cnt - 1] as int, starts[cnt] as int);
        assert(isum(f, starts[cnt - 1] as int, starts[cnt] as int) == v(b + (cnt - 1)));
    }
}

/// A range sum shifted by `d`: `f(i) == g(d + i)` on `0 .. len`.
pub proof fn lemma_isum_shift(f: spec_fn(int) -> int, g: spec_fn(int) -> int, d: int, len: int)
    requires len >= 0, forall|i: int| 0 <= i < len ==> #[trigger] f(i) == g(d + i),
    ensures isum(f, 0, len) == isum(g, d, d + len),
    decreases len,
{
    if len > 0 {
        lemma_isum_shift(f, g, d, len - 1);
        assert(f(len - 1) == g(d + (len - 1)));
    }
}

} // verus!
