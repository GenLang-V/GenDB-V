//! Proofs about `spec::fns::div`: type soundness (dispatched from `bridge::fns::lemma_fn_family`), and the
//! arithmetic facts that characterize the definitions (the truncating integer quotient, the leading base-10000
//! digit, the result-scale range, half-away-from-zero rounding). The executable evaluator (`exec::fns::div`)
//! relies on `lemma_div_round_split` and `lemma_num_div_coeff_scaled` for the quotient it computes. Powers of
//! ten are combined with `bridge::order::lemma_pow10_add`.
use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::numeric::*;
use crate::spec::fns::div::*;
use crate::bridge::typing::*;
use crate::bridge::order::lemma_pow10_add;

verus! {

/// Type soundness of `div` (`bridge::fns::lemma_fn_family`): integer division gives an integer, numeric
/// division a numeric (or NULL).
pub proof fn lemma_div_family(f: ScalarFn, tys: Seq<ColTy>, vs: Seq<Val>)
    requires
        row_typed(vs, tys),
        type_div(f, tys) is Some,
        apply_div(f, vs) is Ok,
    ensures
        val_has_family(apply_div(f, vs)->Ok_0, type_div(f, tys)->0.ty),
{
    assert(val_has_family(vs[0], tys[0].ty));
    assert(val_has_family(vs[1], tys[1].ty));
}

// ------------------------------------------------------------------ integer division

/// `trunc_div` is C's truncating quotient: `a = q·b + rem` with `|rem| < |b|` and `rem` zero or of the sign of `a`.
pub proof fn lemma_trunc_div(a: int, b: int)
    requires b != 0,
    ensures ({
        let q = trunc_div(a, b);
        let rem = a - q * b;
        abs(rem) < abs(b) && (rem == 0 || sign(rem) == sign(a))
    }),
{
    let x = abs(a);
    let y = abs(b);
    let u = x / y;
    let m = x % y;
    lemma_fundamental_div_mod(x, y);
    lemma_mod_pos_bound(x, y);
    let q = trunc_div(a, b);
    if a == 0 {
        lemma_fundamental_div_mod_converse(0int, y, 0int, 0int);
        assert(q == 0) by (nonlinear_arith) requires q == sign(a) * sign(b) * u, sign(a) == 0;
    } else if a > 0 && b > 0 {
        assert(q == u) by (nonlinear_arith) requires q == sign(a) * sign(b) * u, sign(a) == 1, sign(b) == 1;
        assert(a - q * b == m) by (nonlinear_arith) requires q == u, x == y * u + m, x == a, y == b;
    } else if a > 0 && b < 0 {
        assert(q == -u) by (nonlinear_arith) requires q == sign(a) * sign(b) * u, sign(a) == 1, sign(b) == -1;
        assert(a - q * b == m) by (nonlinear_arith) requires q == -u, x == y * u + m, x == a, y == -b;
    } else if a < 0 && b > 0 {
        assert(q == -u) by (nonlinear_arith) requires q == sign(a) * sign(b) * u, sign(a) == -1, sign(b) == 1;
        assert(a - q * b == -m) by (nonlinear_arith) requires q == -u, x == y * u + m, x == -a, y == b;
    } else {
        assert(q == u) by (nonlinear_arith) requires q == sign(a) * sign(b) * u, sign(a) == -1, sign(b) == -1;
        assert(a - q * b == -m) by (nonlinear_arith) requires q == u, x == y * u + m, x == -a, y == -b;
    }
}

// ------------------------------------------------------------------ result scale

/// The quotient's display scale lies in `[0, 1000]` and, when both operand scales are at most 1000, is at
/// least each of them.
pub proof fn lemma_div_scale_range(c1: int, s1: nat, c2: int, s2: nat)
    ensures
        div_scale(c1, s1, c2, s2) <= 1000,
        s1 <= 1000 ==> s1 <= div_scale(c1, s1, c2, s2),
        s2 <= 1000 ==> s2 <= div_scale(c1, s1, c2, s2),
{
}

/// The leading base-10000 digit of a nonzero value is a base-10000 digit in `[1, 9999]`, i.e.
/// `10000^w <= |v| < 10000^(w+1)` for `w = nbase_weight`: the weight is the normalized one.
///
/// With `n` decimal digits of `m = |c|` (`10^(n-1) <= m < 10^n`) and `em = (n - 1 - s) mod 4`, the digit is
/// `m·10^t` with `t = 1 - n + em`. Scaling the bounds of `m` by `10^t` (`t >= 0`), or dividing them by `10^-t`
/// (`t < 0`), gives `10^em <= digit < 10^(em+1)`, and `0 <= em < 4` bounds that by `[1, 9999]`.
pub proof fn lemma_nbase_first_digit_range(c: int, s: nat)
    requires c != 0,
    ensures 1 <= nbase_first_digit(c, s) <= 9999,
{
    let m = abs(c);
    let n = decimal_digits(m);
    let e = n - 1 - s;
    let w = nbase_weight(c, s);
    lemma_fundamental_div_mod(e, 4);
    lemma_mod_bound(e, 4);
    let em = e % 4;
    let t = 0 - s - 4 * w;
    assert(t == 1 - n + em) by (nonlinear_arith) requires w == e / 4, e == 4 * (e / 4) + em, e == n - 1 - s, t == 0 - s - 4 * w;
    // 10^(n-1) <= m < 10^n
    lemma_decimal_digits_bound(m, n);
    assert(n >= 1) by {
        if n == 0 { lemma_decimal_digits_bound(m, 0); assert(pow10(0) == 1); }
    }
    let n1 = (n - 1) as nat;
    lemma_decimal_digits_bound(m, n1);
    let em_n = em as nat;
    assert(pow10(4) == 10000) by (compute);
    lemma_pow10_monotone((em_n + 1) as nat, 4);
    lemma_pow10_positive(em_n);
    if t >= 0 {
        let tn = t as nat;
        lemma_pow10_add(n1, tn);
        lemma_pow10_add(n, tn);
        assert(n1 + tn == em_n);
        assert(n + tn == em_n + 1);
        let pt = pow10(tn);
        lemma_pow10_positive(tn);
        assert(pow10(n1) * pt <= m * pt) by (nonlinear_arith) requires pow10(n1) <= m, pt >= 1;
        assert(m * pt < pow10(n) * pt) by (nonlinear_arith) requires m < pow10(n), pt >= 1;
        assert(nbase_first_digit(c, s) == m * pt);
    } else {
        let u = (0 - t) as nat;
        assert(u + em_n == n1);
        assert(u + em_n + 1 == n);
        lemma_pow10_add(u, em_n);
        lemma_pow10_add(u, (em_n + 1) as nat);
        let pu = pow10(u);
        lemma_pow10_positive(u);
        let d = m / pu;
        assert(nbase_first_digit(c, s) == d);
        lemma_fundamental_div_mod(m, pu);
        lemma_mod_pos_bound(m, pu);
        let r = m % pu;
        // pu·10^em <= m = pu·d + r < pu·(d+1) ==> 10^em <= d; m < pu·10^(em+1) ==> d < 10^(em+1)
        let a = pow10(em_n);
        let b = pow10((em_n + 1) as nat);
        assert(a <= d) by (nonlinear_arith) requires pu * a <= m, m == pu * d + r, 0 <= r < pu, pu >= 1;
        assert(d < b) by (nonlinear_arith) requires m < pu * b, m == pu * d + r, 0 <= r, pu >= 1;
    }
}

// ------------------------------------------------------------------ rounding

/// `div_round(n, d)` is `n / d` rounded half away from zero: `2n - d < 2d·q <= 2n + d` (a tie `2d·q = 2n + d`
/// rounds up in magnitude).
pub proof fn lemma_div_round_bounds(n: int, d: int)
    requires n >= 0, d > 0,
    ensures
        2 * n - d < 2 * d * div_round(n, d) <= 2 * n + d,
        div_round(n, d) >= 0,
{
    let q = div_round(n, d);
    lemma_fundamental_div_mod(2 * n + d, 2 * d);
    lemma_mod_pos_bound(2 * n + d, 2 * d);
    let r = (2 * n + d) % (2 * d);
    assert(2 * n + d == 2 * d * q + r);
    assert(q >= 0) by (nonlinear_arith) requires 2 * n + d == 2 * d * q + r, r < 2 * d, n >= 0, d > 0;
}

/// A common positive factor does not change the rounded quotient.
pub proof fn lemma_div_round_factor(n: int, d: int, a: int)
    requires n >= 0, d > 0, a > 0,
    ensures div_round(n * a, d * a) == div_round(n, d),
{
    let x = 2 * n + d;
    assert(2 * (n * a) + d * a == x * a) by (nonlinear_arith) requires x == 2 * n + d;
    assert(2 * (d * a) == a * (2 * d)) by (nonlinear_arith);
    lemma_div_denominator(x * a, a, 2 * d);
    assert(x * a == a * x) by (nonlinear_arith);
    lemma_div_multiples_vanish(x, a);
}

/// The rounded quotient from the truncated quotient and the remainder (no intermediate above `n` or `d`).
pub proof fn lemma_div_round_split(n: int, d: int)
    requires n >= 0, d > 0,
    ensures div_round(n, d) == n / d + if n % d >= d - n % d { 1int } else { 0int },
{
    lemma_fundamental_div_mod(n, d);
    lemma_mod_pos_bound(n, d);
    let q = n / d;
    let m = n % d;
    if m >= d - m {
        assert(2 * n + d == (q + 1) * (2 * d) + (2 * m - d)) by (nonlinear_arith) requires n == d * q + m;
        lemma_fundamental_div_mod_converse(2 * n + d, 2 * d, q + 1, 2 * m - d);
    } else {
        assert(2 * n + d == q * (2 * d) + (2 * m + d)) by (nonlinear_arith) requires n == d * q + m;
        lemma_fundamental_div_mod_converse(2 * n + d, 2 * d, q, 2 * m + d);
    }
}

/// The exact quotient `c1·10^(r+s2) / (c2·10^s1)` in the form the evaluator computes: with
/// `k = r + s2 - s1`, the rounded magnitude is `div_round(|c1|·10^k, |c2|)` (`k >= 0`) or
/// `div_round(|c1|, |c2|·10^-k)` (`k < 0`).
pub proof fn lemma_num_div_coeff_scaled(c1: int, s1: nat, c2: int, s2: nat)
    requires c2 != 0,
    ensures ({
        let r = div_scale(c1, s1, c2, s2);
        let k = r + s2 - s1;
        let q = if k >= 0 { div_round(abs(c1) * pow10(k as nat), abs(c2)) }
            else { div_round(abs(c1), abs(c2) * pow10((0 - k) as nat)) };
        num_div_coeff(c1, s1, c2, s2) == sign(c1) * sign(c2) * q && q >= 0
    }),
{
    let r = div_scale(c1, s1, c2, s2);
    let k = r + s2 - s1;
    let m1 = abs(c1);
    let m2 = abs(c2);
    if k >= 0 {
        let kn = k as nat;
        lemma_pow10_add(kn, s1);
        assert(kn + s1 == r + s2);
        lemma_pow10_positive(s1);
        lemma_pow10_positive(kn);
        let a = pow10(s1);
        let p = pow10(kn);
        assert(m1 * pow10(r + s2) == (m1 * p) * a) by (nonlinear_arith) requires pow10(r + s2) == p * a;
        assert(m1 * p >= 0) by (nonlinear_arith) requires m1 >= 0, p >= 1;
        lemma_div_round_factor(m1 * p, m2, a);
        lemma_div_round_bounds(m1 * p, m2);
    } else {
        let u = (0 - k) as nat;
        let b = r + s2;
        lemma_pow10_add(u, b);
        assert(u + b == s1);
        lemma_pow10_positive(b);
        lemma_pow10_positive(u);
        let a = pow10(b);
        let p = pow10(u);
        assert(m2 * pow10(s1) == (m2 * p) * a) by (nonlinear_arith) requires pow10(s1) == p * a;
        assert(m2 * p > 0) by (nonlinear_arith) requires m2 > 0, p >= 1;
        lemma_div_round_factor(m1, m2 * p, a);
        lemma_div_round_bounds(m1, m2 * p);
    }
}

} // verus!
