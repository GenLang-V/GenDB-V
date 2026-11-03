//! The comparison `l_quantity < 0.2 * AVG(l_quantity)` of a quantity coefficient `q` (scale 2) with the subquery's
//! value of a key with `n >= 1` rows and quantity sum `s` (scale 2), in integer form.
//!
//! The subquery's value is `2 * A` at scale `r + 1`, where `A` is PostgreSQL's AVG `s / n` rounded half away from
//! zero at the result scale `r = div_scale(s, 2, n, 0) >= 2` (`spec::fns::div`). With `P = 10^(r - 2)`:
//! - always: `q < 0.2 * AVG` exactly when `5 * q * P < A` (`lemma_below_scaled`; the slow path's `cmp_scaled`);
//! - fast form: when `|s| < 10^6` (so `r >= 16`) and `n < 2 * 10^14` (so `2 * P > n`), the rounding of `A` cannot
//!   cross the comparison, and `q < 0.2 * AVG` exactly when `5 * q * n < s` (`lemma_below_fast`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::fns::div::*;
use crate::bridge::fns::div::{lemma_div_scale_range, lemma_div_round_bounds, lemma_num_div_coeff_scaled};
use crate::bridge::order::lemma_pow10_add;

verus! {

/// The comparison of `q` (scale 2) with `0.2 * AVG`: the value `2 * A` at scale `r + 1`.
pub open spec fn below_avg(q: int, s: int, n: int) -> bool {
    num_cmp(q, 2, 2 * num_div_coeff(s, 2, n, 0), div_scale(s, 2, n, 0) + 1) < 0
}

/// Exact form: `q < 0.2 * AVG` exactly when `5 q 10^(r-2) < A`.
pub proof fn lemma_below_scaled(q: int, s: int, n: int)
    requires n >= 1,
    ensures ({
        let r = div_scale(s, 2, n, 0);
        &&& 2 <= r <= 1000
        &&& below_avg(q, s, n) == (5 * q * pow10((r - 2) as nat) < num_div_coeff(s, 2, n, 0))
    }),
{
    lemma_div_scale_range(s, 2, n, 0);
    let r = div_scale(s, 2, n, 0);
    let a = num_div_coeff(s, 2, n, 0);
    let p = pow10((r - 2) as nat);
    // align(q, 2, r + 1) = q * 10^(r - 1) = 10 * q * P, and align(2a, r + 1, r + 1) = 2a
    assert(max_nat(2, r + 1) == r + 1);
    lemma_pow10_add(1, (r - 2) as nat);
    assert(pow10(1) == 10) by (compute);
    assert((r + 1 - 2) as nat == (1 + (r - 2)) as nat);
    assert(align(q, 2, r + 1) == q * (10 * p));
    crate::link::expr::lemma_align_same(2 * a, r + 1);
    assert(num_cmp(q, 2, 2 * a, r + 1) == sign(q * (10 * p) - 2 * a));
    assert(q * (10 * p) == 2 * (5 * q * p)) by (nonlinear_arith);
    assert((q * (10 * p) - 2 * a < 0) == (5 * q * p < a)) by (nonlinear_arith)
        requires q * (10 * p) == 2 * (5 * q * p);
}

/// The rounded quotient bounds: `2 s P - n <= 2 n A <= 2 s P + n`.
pub proof fn lemma_avg_bounds(s: int, n: int)
    requires n >= 1,
    ensures ({
        let r = div_scale(s, 2, n, 0);
        let p = pow10((r - 2) as nat);
        let a = num_div_coeff(s, 2, n, 0);
        &&& p >= 1
        &&& 2 * s * p - n <= 2 * n * a <= 2 * s * p + n
    }),
{
    lemma_div_scale_range(s, 2, n, 0);
    lemma_num_div_coeff_scaled(s, 2, n, 0);
    let r = div_scale(s, 2, n, 0);
    let kk = (r - 2) as nat;
    let p = pow10(kk);
    lemma_pow10_positive(kk);
    let a = num_div_coeff(s, 2, n, 0);
    assert((r + 0 - 2) as nat == kk);
    assert(abs(n) == n);
    assert(sign(n) == 1);
    let m = abs(s) * p;
    assert(m >= 0) by (nonlinear_arith) requires abs(s) >= 0, p >= 1, m == abs(s) * p;
    let x = div_round(m, n);
    lemma_div_round_bounds(m, n);
    let sg = sign(s);
    assert(a == sg * 1 * x);
    if s >= 0 {
        assert(abs(s) == s);
        if s == 0 {
            assert(sg == 0);
            assert(a == 0) by (nonlinear_arith) requires a == sg * 1 * x, sg == 0;
            assert(m == 0) by (nonlinear_arith) requires m == abs(s) * p, abs(s) == 0;
        } else {
            assert(sg == 1);
            assert(a == x) by (nonlinear_arith) requires a == sg * 1 * x, sg == 1;
        }
        assert(2 * s * p - n <= 2 * n * a <= 2 * s * p + n) by (nonlinear_arith)
            requires 2 * m - n < 2 * n * x <= 2 * m + n, m == s * p, (a == x || (a == 0 && m == 0 && s == 0)), n >= 1;
    } else {
        assert(abs(s) == -s);
        assert(sg == -1);
        assert(a == -x) by (nonlinear_arith) requires a == sg * 1 * x, sg == -1;
        assert(2 * s * p - n <= 2 * n * a <= 2 * s * p + n) by (nonlinear_arith)
            requires 2 * m - n < 2 * n * x <= 2 * m + n, m == (-s) * p, a == -x;
    }
}

/// A non-zero dividend below `10^6` (scale 2) and a positive count: the result scale is at least 16.
pub proof fn lemma_scale_16(s: int, n: int)
    requires n >= 1, -1_000_000 < s < 1_000_000,
    ensures div_scale(s, 2, n, 0) >= 16,
{
    let w1 = nbase_weight(s, 2);
    let w2 = nbase_weight(n, 0);
    if s != 0 {
        lemma_decimal_digits_bound(abs(s), 6);
        assert(pow10(6) == 1_000_000) by (compute);
        assert(decimal_digits(abs(s)) <= 6);
        assert(w1 == (decimal_digits(abs(s)) - 1 - 2) / 4);
        assert(w1 <= 0);
    } else {
        assert(w1 == 0);
    }
    assert(decimal_digits(n) >= 1);
    assert(abs(n) == n);
    assert(w2 == (decimal_digits(n) - 1 - 0) / 4);
    assert(w2 >= 0);
    let qw0 = w1 - w2;
    assert(qw0 <= 0);
}

/// Fast form: under the bounds, `q < 0.2 * AVG` exactly when `5 q n < s`.
pub proof fn lemma_below_fast(q: int, s: int, n: int)
    requires 1 <= n < 200_000_000_000_000, -1_000_000 < s < 1_000_000,
    ensures below_avg(q, s, n) == (5 * q * n < s),
{
    lemma_below_scaled(q, s, n);
    lemma_avg_bounds(s, n);
    lemma_scale_16(s, n);
    let r = div_scale(s, 2, n, 0);
    let p = pow10((r - 2) as nat);
    let a = num_div_coeff(s, 2, n, 0);
    // P = 10^(r-2) >= 10^14, so 2 P > n
    crate::spec::numeric::lemma_pow10_monotone(14, (r - 2) as nat);
    assert(pow10(14) == 100_000_000_000_000) by (compute);
    assert(2 * p > n);
    let t = 5 * q;
    if s >= t * n + 1 {
        assert(2 * n * a > 2 * n * (t * p)) by (nonlinear_arith)
            requires 2 * s * p - n <= 2 * n * a, s >= t * n + 1, 2 * p > n, p >= 1;
        assert(a > t * p) by (nonlinear_arith) requires 2 * n * a > 2 * n * (t * p), n >= 1;
        assert(t * n < s);
    } else if s <= t * n - 1 {
        assert(2 * n * a < 2 * n * (t * p)) by (nonlinear_arith)
            requires 2 * n * a <= 2 * s * p + n, s <= t * n - 1, 2 * p > n, p >= 1;
        assert(a < t * p) by (nonlinear_arith) requires 2 * n * a < 2 * n * (t * p), n >= 1;
    } else {
        assert(s == t * n);
        assert(-n <= 2 * n * (a - t * p) <= n) by (nonlinear_arith)
            requires 2 * s * p - n <= 2 * n * a <= 2 * s * p + n, s == t * n;
        assert(a == t * p) by (nonlinear_arith) requires -n <= 2 * n * (a - t * p) <= n, n >= 1;
    }
    assert(5 * q * p == t * p);
    assert(5 * q * n == t * n);
}

} // verus!
