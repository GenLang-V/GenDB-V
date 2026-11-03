//! Even splits of `0..n` into `k` consecutive ranges: range `i` is `split(n, k, i) .. split(n, k, i + 1)` with
//! `split(n, k, i) = floor(n * i / k)`; the ranges are ordered, start at 0, end at `n` and cover every position once.
use vstd::prelude::*;

verus! {

/// The start of range `i` of `k` even ranges of `0..n`.
pub open spec fn split(n: int, k: int, i: int) -> int { n * i / k }

/// The splits start at 0, end at `n`, and do not decrease.
pub proof fn lemma_split(n: int, k: int, i: int, j: int)
    requires n >= 0, k > 0, 0 <= i <= j <= k,
    ensures
        split(n, k, 0) == 0, split(n, k, k) == n,
        0 <= split(n, k, i) <= split(n, k, j) <= n,
{
    assert(n * 0 / k == 0) by (nonlinear_arith) requires k > 0;
    assert(n * k / k == n) by (nonlinear_arith) requires k > 0;
    assert(n * i <= n * j) by (nonlinear_arith) requires n >= 0, i <= j;
    assert(n * i / k <= n * j / k) by (nonlinear_arith) requires n * i <= n * j, k > 0;
    assert(0 <= n * i) by (nonlinear_arith) requires n >= 0, i >= 0;
    assert(0 <= n * i / k) by (nonlinear_arith) requires 0 <= n * i, k > 0;
    assert(n * j <= n * k) by (nonlinear_arith) requires n >= 0, j <= k;
    assert(n * j / k <= n * k / k) by (nonlinear_arith) requires n * j <= n * k, k > 0;
}

/// `split(n, k, i)`.
pub fn split_exec(n: usize, k: usize, i: usize) -> (r: usize)
    requires k > 0, i <= k,
    ensures r as int == split(n as int, k as int, i as int),
{
    proof {
        lemma_split(n as int, k as int, i as int, k as int);
        assert(n as int * i as int <= u128::MAX) by (nonlinear_arith)
            requires 0 <= n <= usize::MAX, 0 <= i <= usize::MAX, usize::MAX < 0x1_0000_0000_0000_0000;
    }
    let x: u128 = (n as u128) * (i as u128) / (k as u128);
    x as usize
}

} // verus!
