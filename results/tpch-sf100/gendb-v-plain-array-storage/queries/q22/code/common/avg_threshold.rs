//! `x > AVG(..)` in integer form. PostgreSQL's AVG of numeric values with exact sum coefficient `s >= 0` at scale
//! `sc` over `n >= 1` values is `numeric_div(s, n)` (`spec::fns::div::num_div`): the quotient rounded half away
//! from zero at the result scale `r = div_scale(s, sc, n, 0) >= sc`. With `P = 10^(r - sc)` (`avg_shift`), a value
//! of coefficient `c` at scale `sc` exceeds that AVG exactly when `c > (s + floor(n / (2P))) / n` (`avg_thr`,
//! floor division; `lemma_gt_avg`). When `P > n` the correction term is 0 and the test is `c > floor(s / n)`.
use vstd::prelude::*;
use crate::spec::numeric::*;
use crate::spec::fns::div::*;
use crate::bridge::fns::div::{lemma_div_scale_range, lemma_div_round_bounds, lemma_num_div_coeff_scaled};
use crate::bridge::order::lemma_num_cmp_at;

verus! {

/// `r - sc` for the AVG result scale `r` (`r >= sc` for `sc <= 1000`).
pub open spec fn avg_shift(s: int, sc: nat, n: int) -> nat {
    (div_scale(s, sc, n, 0) - sc) as nat
}

/// The integer threshold: `(s + floor(n / (2 * 10^shift))) / n`.
pub open spec fn avg_thr(s: int, sc: nat, n: int) -> int {
    (s + n / (2 * pow10(avg_shift(s, sc, n)))) / n
}

/// The AVG coefficient is `div_round(s * P, n)`.
proof fn lemma_avg_coeff(s: int, sc: nat, n: int)
    requires s >= 0, n >= 1, sc <= 1000,
    ensures
        sc <= div_scale(s, sc, n, 0),
        num_div_coeff(s, sc, n, 0) == div_round(s * pow10(avg_shift(s, sc, n)), n),
{
    lemma_div_scale_range(s, sc, n, 0);
    lemma_num_div_coeff_scaled(s, sc, n, 0);
    let r = div_scale(s, sc, n, 0);
    let k = avg_shift(s, sc, n);
    assert(r + 0 - sc == k);
    let p = pow10(k);
    lemma_pow10_positive(k);
    let q = div_round(abs(s) * p, abs(n));
    assert(abs(s) == s && abs(n) == n && sign(n) == 1);
    if s == 0 {
        assert(s * p == 0);
        assert(div_round(0, n) == 0) by {
            assert((2 * 0 + n) / (2 * n) == 0) by (nonlinear_arith) requires n >= 1;
        }
        assert(sign(s) == 0);
        assert(sign(s) * sign(n) * q == 0) by (nonlinear_arith) requires sign(s) == 0;
    } else {
        assert(sign(s) == 1);
        assert(sign(s) * sign(n) * q == q) by (nonlinear_arith) requires sign(s) == 1, sign(n) == 1;
    }
}

/// `c * P > div_round(s * P, n)` exactly when `2 n c P > 2 s P + n`.
proof fn lemma_gt_round(c: int, s: int, n: int, p: int)
    requires s >= 0, n >= 1, p >= 1,
    ensures (c * p > div_round(s * p, n)) == (2 * n * (c * p) > 2 * (s * p) + n),
{
    let m = s * p;
    assert(m >= 0) by (nonlinear_arith) requires s >= 0, p >= 1, m == s * p;
    lemma_div_round_bounds(m, n);
    let rr = div_round(m, n);
    let x = c * p;
    if x > rr {
        assert(2 * n * x >= 2 * n * rr + 2 * n) by (nonlinear_arith) requires x >= rr + 1, n >= 1;
    } else {
        assert(2 * n * x <= 2 * n * rr) by (nonlinear_arith) requires x <= rr, n >= 1;
    }
}

/// `2 n c P > 2 s P + n` exactly when `c > (s + floor(n / (2P))) / n`.
proof fn lemma_gt_floor(c: int, s: int, n: int, p: int)
    requires s >= 0, n >= 1, p >= 1,
    ensures (2 * n * (c * p) > 2 * (s * p) + n) == (c > (s + n / (2 * p)) / n),
{
    let d = n * c - s;
    let f = n / (2 * p);
    assert(2 * n * (c * p) - 2 * (s * p) == 2 * p * d) by (nonlinear_arith) requires d == n * c - s;
    // 2 P d > n  <=>  d > f
    assert(f >= 0 && 2 * p * f <= n && n < 2 * p * (f + 1)) by (nonlinear_arith)
        requires f == n / (2 * p), n >= 1, p >= 1;
    if d > f {
        assert(2 * p * d >= 2 * p * (f + 1)) by (nonlinear_arith) requires d >= f + 1, p >= 1;
    } else {
        assert(2 * p * d <= 2 * p * f) by (nonlinear_arith) requires d <= f, p >= 1;
    }
    // d > f  <=>  n c > s + f  <=>  c > (s + f) / n
    let q = (s + f) / n;
    assert(n * q <= s + f && s + f < n * (q + 1)) by (nonlinear_arith) requires q == (s + f) / n, n >= 1, s + f >= 0;
    if c > q {
        assert(n * c >= n * (q + 1)) by (nonlinear_arith) requires c >= q + 1, n >= 1;
    } else {
        assert(n * c <= n * q) by (nonlinear_arith) requires c <= q, n >= 1;
    }
}

/// A value of coefficient `c` at scale `sc` exceeds the AVG of sum `s >= 0` (scale `sc`) over `n >= 1` values
/// exactly when `c > avg_thr(s, sc, n)`.
pub proof fn lemma_gt_avg(c: int, s: int, sc: nat, n: int)
    requires s >= 0, n >= 1, sc <= 1000,
    ensures
        (num_cmp(c, sc, num_div_coeff(s, sc, n, 0), div_scale(s, sc, n, 0)) > 0) == (c > avg_thr(s, sc, n)),
        sc <= div_scale(s, sc, n, 0),
{
    lemma_avg_coeff(s, sc, n);
    let r = div_scale(s, sc, n, 0);
    let k = avg_shift(s, sc, n);
    let p = pow10(k);
    lemma_pow10_positive(k);
    let a = num_div_coeff(s, sc, n, 0);
    lemma_num_cmp_at(c, sc, a, r, r);
    assert(align(c, sc, r) == c * p);
    assert(pow10(0) == 1);
    assert(align(a, r, r) == a);
    assert((sign(c * p - a) > 0) == (c * p > a));
    lemma_gt_round(c, s, n, p);
    lemma_gt_floor(c, s, n, p);
}

/// With a shift of at least 20 digits and `n < 10^20`, the correction term vanishes.
pub proof fn lemma_thr_large_shift(n: int, k: nat)
    requires k >= 20, 1 <= n < 100_000_000_000_000_000_000,
    ensures n / (2 * pow10(k)) == 0,
{
    lemma_pow10_monotone(20, k);
    assert(pow10(20) == 100_000_000_000_000_000_000) by (compute);
    let p = pow10(k);
    assert(n / (2 * p) == 0) by (nonlinear_arith) requires 0 <= n < 2 * p;
}

} // verus!
