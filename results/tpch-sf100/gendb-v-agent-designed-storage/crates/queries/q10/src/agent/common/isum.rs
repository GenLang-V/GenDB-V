//! Finite integer sums over an index range: `isum(n, f)` is `f(0) + .. + f(n - 1)` (0 for `n <= 0`), with the laws
//! a loop, a partition or a join proof needs (step, extensionality, zero terms, sign and monotonicity, a single
//! nonzero term, a constant factor, exchange of two sums, a sum over a relation built by index).
use vstd::prelude::*;
use crate::spec::value::Row;
use crate::link::join::{sum_of, lemma_sum_of_ext};

verus! {

/// `f(0) + f(1) + .. + f(n - 1)`; empty (0) for `n <= 0`.
pub open spec fn isum(n: int, f: spec_fn(int) -> int) -> int
    decreases n,
{
    if n <= 0 { 0 } else { isum(n - 1, f) + f(n - 1) }
}

/// One more term.
pub proof fn lemma_isum_step(n: int, f: spec_fn(int) -> int)
    requires n >= 0,
    ensures isum(n + 1, f) == isum(n, f) + f(n),
{
}

/// Functions that agree on `[0, n)` have the same sum.
pub proof fn lemma_isum_ext(n: int, f: spec_fn(int) -> int, g: spec_fn(int) -> int)
    requires forall|i: int| 0 <= i < n ==> #[trigger] f(i) == g(i),
    ensures isum(n, f) == isum(n, g),
    decreases n,
{
    if n > 0 {
        lemma_isum_ext(n - 1, f, g);
    }
}

/// Zero terms: zero sum.
pub proof fn lemma_isum_zero(n: int, f: spec_fn(int) -> int)
    requires forall|i: int| 0 <= i < n ==> #[trigger] f(i) == 0,
    ensures isum(n, f) == 0,
    decreases n,
{
    if n > 0 {
        lemma_isum_zero(n - 1, f);
    }
}

/// Termwise `f <= g`: `isum f <= isum g`.
pub proof fn lemma_isum_mono(n: int, f: spec_fn(int) -> int, g: spec_fn(int) -> int)
    requires forall|i: int| 0 <= i < n ==> #[trigger] f(i) <= g(i),
    ensures isum(n, f) <= isum(n, g),
    decreases n,
{
    if n > 0 {
        lemma_isum_mono(n - 1, f, g);
    }
}

/// Nonnegative terms: the partial sums are nonnegative and nondecreasing in the bound.
pub proof fn lemma_isum_nonneg(a: int, b: int, f: spec_fn(int) -> int)
    requires
        a <= b,
        forall|i: int| 0 <= i < b ==> #[trigger] f(i) >= 0,
    ensures 0 <= isum(a, f) <= isum(b, f),
    decreases b,
{
    if b > 0 && a < b {
        lemma_isum_nonneg(a, b - 1, f);
        assert(f(b - 1) >= 0);
    } else if b > 0 {
        lemma_isum_nonneg(a - 1, b - 1, f);
        assert(f(b - 1) >= 0);
    }
}

/// Nonnegative terms: the sum is at least each term.
pub proof fn lemma_isum_ge_term(n: int, f: spec_fn(int) -> int, i: int)
    requires
        0 <= i < n,
        forall|t: int| 0 <= t < n ==> #[trigger] f(t) >= 0,
    ensures isum(n, f) >= f(i),
{
    lemma_isum_nonneg(i, i + 1, f);
    lemma_isum_nonneg(i + 1, n, f);
}

/// Terms zero on `[0, a)`: the prefix sum up to `a` is zero.
pub proof fn lemma_isum_prefix_zero(a: int, f: spec_fn(int) -> int)
    requires forall|i: int| 0 <= i < a ==> #[trigger] f(i) == 0,
    ensures isum(a, f) == 0,
{
    lemma_isum_zero(a, f);
}

/// Terms zero on `[b, n)`: the sum up to `n` is the sum up to `b`.
pub proof fn lemma_isum_suffix_zero(b: int, n: int, f: spec_fn(int) -> int)
    requires
        0 <= b <= n,
        forall|i: int| b <= i < n ==> #[trigger] f(i) == 0,
    ensures isum(n, f) == isum(b, f),
    decreases n - b,
{
    if b < n {
        lemma_isum_suffix_zero(b, n - 1, f);
        assert(f(n - 1) == 0);
    }
}

/// One possibly nonzero term at `k`: the sum is that term (or 0 when `k` lies outside `[0, n)`).
pub proof fn lemma_isum_single(n: int, f: spec_fn(int) -> int, k: int)
    requires forall|i: int| 0 <= i < n && i != k ==> #[trigger] f(i) == 0,
    ensures isum(n, f) == if 0 <= k < n { f(k) } else { 0 },
    decreases n,
{
    if n > 0 {
        lemma_isum_single(n - 1, f, k);
        if n - 1 != k {
            assert(f(n - 1) == 0);
        } else {
            lemma_isum_zero(n - 1, f);
        }
    }
}

/// A constant factor moves out of the sum.
pub proof fn lemma_isum_scale(n: int, f: spec_fn(int) -> int, c: int)
    ensures isum(n, |i: int| c * f(i)) == c * isum(n, f),
    decreases n,
{
    if n > 0 {
        lemma_isum_scale(n - 1, f, c);
        assert(c * isum(n - 1, f) + c * f(n - 1) == c * (isum(n - 1, f) + f(n - 1))) by (nonlinear_arith);
    }
}

/// Termwise sum.
pub proof fn lemma_isum_add(n: int, f: spec_fn(int) -> int, g: spec_fn(int) -> int)
    ensures isum(n, |i: int| f(i) + g(i)) == isum(n, f) + isum(n, g),
    decreases n,
{
    if n > 0 {
        lemma_isum_add(n - 1, f, g);
    }
}

/// Exchange of two finite sums.
pub proof fn lemma_isum_swap(n: int, m: int, h: spec_fn(int, int) -> int)
    ensures
        isum(n, |i: int| isum(m, |j: int| h(i, j))) == isum(m, |j: int| isum(n, |i: int| h(i, j))),
    decreases n,
{
    let lhs = |i: int| isum(m, |j: int| h(i, j));
    let rhs = |j: int| isum(n, |i: int| h(i, j));
    if n <= 0 {
        assert forall|j: int| 0 <= j < m implies #[trigger] rhs(j) == 0 by {}
        lemma_isum_zero(m, rhs);
    } else {
        lemma_isum_swap(n - 1, m, h);
        let prev = |j: int| isum(n - 1, |i: int| h(i, j));
        let last = |j: int| h(n - 1, j);
        // isum(n, lhs) = isum(n - 1, lhs) + lhs(n - 1) = isum(m, prev) + isum(m, last)
        lemma_isum_ext(m, |j: int| h(n - 1, j), last);
        lemma_isum_add(m, prev, last);
        assert forall|j: int| 0 <= j < m implies #[trigger] rhs(j) == (|j: int| prev(j) + last(j))(j) by {}
        lemma_isum_ext(m, rhs, |j: int| prev(j) + last(j));
    }
}

/// The sum over a relation built row by row from an index is the index sum.
pub proof fn lemma_sum_of_seq(n: int, rowf: spec_fn(int) -> Row, h: spec_fn(Row) -> int)
    requires n >= 0,
    ensures sum_of(Seq::new(n as nat, rowf), h) == isum(n, |i: int| h(rowf(i))),
    decreases n,
{
    let s = Seq::new(n as nat, rowf);
    if n > 0 {
        lemma_sum_of_seq(n - 1, rowf, h);
        assert(s.drop_last() =~= Seq::new((n - 1) as nat, rowf));
        assert(s.last() == rowf(n - 1));
    } else {
        assert(s.len() == 0);
    }
}

} // verus!
