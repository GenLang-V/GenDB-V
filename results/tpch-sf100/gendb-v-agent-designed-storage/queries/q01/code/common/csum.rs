//! Conditional sums over an index range `0..n`: `csum(sel, val, n)` is the sum of `val(i)` over the indices
//! `i < n` with `sel(i)`, defined by recursion on the last index (so a loop over `i` proves one step per
//! iteration). Laws: one step, pointwise agreement, an affine value (`c + f(i)`), an empty selection, bounds.
use vstd::prelude::*;

verus! {

/// Sum of `val(i)` over `0 <= i < n` with `sel(i)`.
pub open spec fn csum(sel: spec_fn(int) -> bool, val: spec_fn(int) -> int, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else { csum(sel, val, n - 1) + if sel(n - 1) { val(n - 1) } else { 0 } }
}

/// The constant 1 (counts are sums of it).
pub open spec fn one() -> spec_fn(int) -> int {
    |i: int| 1int
}

/// One more index.
pub proof fn lemma_csum_step(sel: spec_fn(int) -> bool, val: spec_fn(int) -> int, n: int)
    requires n >= 0,
    ensures csum(sel, val, n + 1) == csum(sel, val, n) + if sel(n) { val(n) } else { 0 },
{
}

/// Sums of selections and values that agree on every selected index are equal.
pub proof fn lemma_csum_ext(s1: spec_fn(int) -> bool, v1: spec_fn(int) -> int, s2: spec_fn(int) -> bool,
    v2: spec_fn(int) -> int, n: int)
    requires
        forall|i: int| 0 <= i < n ==> #[trigger] s1(i) == s2(i),
        forall|i: int| 0 <= i < n && s1(i) ==> #[trigger] v1(i) == v2(i),
    ensures csum(s1, v1, n) == csum(s2, v2, n),
    decreases n,
{
    if n > 0 {
        lemma_csum_ext(s1, v1, s2, v2, n - 1);
        assert(s1(n - 1) == s2(n - 1));
    }
}

/// An empty selection sums to 0.
pub proof fn lemma_csum_none(sel: spec_fn(int) -> bool, val: spec_fn(int) -> int, n: int)
    requires forall|i: int| 0 <= i < n ==> !#[trigger] sel(i),
    ensures csum(sel, val, n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_csum_none(sel, val, n - 1);
        assert(!sel(n - 1));
    }
}

/// An affine value: the constant times the count plus the sum of the varying part.
pub proof fn lemma_csum_affine(sel: spec_fn(int) -> bool, f: spec_fn(int) -> int, g: spec_fn(int) -> int, c: int, n: int)
    requires forall|i: int| 0 <= i < n ==> #[trigger] g(i) == c + f(i),
    ensures csum(sel, g, n) == c * csum(sel, one(), n) + csum(sel, f, n),
    decreases n,
{
    if n > 0 {
        lemma_csum_affine(sel, f, g, c, n - 1);
        assert(g(n - 1) == c + f(n - 1));
        assert(c * (csum(sel, one(), n - 1) + 1) == c * csum(sel, one(), n - 1) + c) by (nonlinear_arith);
    }
}

/// Selecting every index.
pub open spec fn sel_all() -> spec_fn(int) -> bool {
    |i: int| true
}

/// A count is between 0 and the number of indices.
pub proof fn lemma_count_bounds(sel: spec_fn(int) -> bool, n: int)
    requires n >= 0,
    ensures 0 <= csum(sel, one(), n) <= n,
    decreases n,
{
    if n > 0 {
        lemma_count_bounds(sel, n - 1);
    }
}

/// Selecting every index counts every index.
pub proof fn lemma_count_all(n: int)
    requires n >= 0,
    ensures csum(sel_all(), one(), n) == n,
    decreases n,
{
    if n > 0 {
        lemma_count_all(n - 1);
    }
}

/// Complementary selections split a sum.
pub proof fn lemma_csum_complement(s1: spec_fn(int) -> bool, s2: spec_fn(int) -> bool, val: spec_fn(int) -> int, n: int)
    requires forall|i: int| 0 <= i < n ==> #[trigger] s2(i) == !s1(i),
    ensures csum(s2, val, n) == csum(sel_all(), val, n) - csum(s1, val, n),
    decreases n,
{
    if n > 0 {
        lemma_csum_complement(s1, s2, val, n - 1);
        assert(s2(n - 1) == !s1(n - 1));
    }
}

} // verus!
