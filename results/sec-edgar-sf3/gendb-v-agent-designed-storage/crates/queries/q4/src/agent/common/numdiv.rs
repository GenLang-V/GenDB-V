//! `no_unwind` copies of the framework's numeric division (`exec::fns::div::num_div_exec` and the helpers it calls:
//! `exec::numeric::pow10_exec`, `exec::datetime::floor_divmod`), unchanged except for the `no_unwind` marks, so that
//! worker bodies (which may only call `no_unwind` code) can evaluate AVG. Numeric division is PostgreSQL
//! `numeric_div` on `i128` coefficients, `Capacity` exactly outside `spec::fns::div::num_div_fits`.
use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::fns::div::*;
use crate::exec::value::*;
use crate::exec::domain::*;
use crate::bridge::fns::div::*;

verus! {

/// `10^k` if it fits `i128`.
pub fn pow10_exec(k: u32) -> (r: Option<i128>)
    ensures
        match r {
            Some(p) => p as int == pow10(k as nat),
            None => !fits_i128(pow10(k as nat)),
        },
    no_unwind
{
    let mut acc: i128 = 1;
    let mut i: u32 = 0;
    while i < k
        invariant
            i <= k,
            acc as int == pow10(i as nat),
        decreases k - i,
    {
        match acc.checked_mul(10) {
            Some(n) => {
                acc = n;
            },
            None => {
                proof {
                    lemma_pow10_positive(i as nat);
                    assert(pow10((i + 1) as nat) == 10 * pow10(i as nat));
                    lemma_pow10_monotone((i + 1) as nat, k as nat);
                }
                return None;
            },
        }
        i = i + 1;
    }
    Some(acc)
}

/// Floor division and modulus by a positive divisor (Rust `/` truncates toward zero; the spec's `/` and `%`
/// are floor division and the non-negative remainder).
pub fn floor_divmod(x: i64, d: i64) -> (r: (i64, i64))
    requires
        0 < d,
    ensures
        r.0 as int == x as int / d as int,
        r.1 as int == x as int % d as int,
        r.0 * d + r.1 == x,
        0 <= r.1 < d,
        x >= 0 ==> 0 <= r.0 <= x,
        x < 0 ==> x <= r.0 < 0,
    no_unwind
{
    if x >= 0 {
        // Unsigned division (d > 0, x >= 0): the same quotient and remainder, and it cannot overflow.
        let q = ((x as u64) / (d as u64)) as i64;
        let m = ((x as u64) % (d as u64)) as i64;
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(x as int, d as int);
            assert(q * d + m == x) by (nonlinear_arith) requires d * q + m == x;
            assert(q <= x) by (nonlinear_arith) requires q * d + m == x, m >= 0, d >= 1, q >= 0;
        }
        (q, m)
    } else {
        let u = -(x + 1);
        let a = ((u as u64) / (d as u64)) as i64;
        let b = ((u as u64) % (d as u64)) as i64;
        let q = -a - 1;
        let m = d - b - 1;
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(u as int, d as int);
            assert(q * d + m == x) by (nonlinear_arith)
                requires d * a + b == u, q == -a - 1, m == d - b - 1, u == -(x + 1);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod_converse(x as int, d as int, q as int, m as int);
            assert(a <= u) by (nonlinear_arith) requires d * a + b == u, b >= 0, d >= 1, a >= 0;
        }
        (q, m)
    }
}

/// `|c|` (every `i128` magnitude fits `u128`).
pub fn magnitude(c: i128) -> (m: u128)
    ensures m as int == abs(c as int),
    no_unwind
{
    if c >= 0 { c as u128 } else { ((-(c + 1)) as u128) + 1 }
}

/// Number of decimal digits of `m` (at most 39).
fn decimal_digits_exec(m: u128) -> (n: u32)
    ensures n as nat == decimal_digits(m as int), n <= 39,
    no_unwind
{
    proof {
        lemma_pow10_i128_boundary();
        lemma_decimal_digits_bound(m as int, 39);
    }
    let mut x = m;
    let mut n: u32 = 0;
    while x > 0
        invariant
            n as nat + decimal_digits(x as int) == decimal_digits(m as int),
            decimal_digits(m as int) <= 39,
        decreases x,
    {
        assert(decimal_digits(x as int) == 1 + decimal_digits((x / 10) as int));
        x = x / 10;
        n = n + 1;
    }
    n
}

/// `10^k` for `k <= 38` (it fits `i128`).
fn pow10_small(k: u32) -> (p: u128)
    requires k <= 38,
    ensures p as int == pow10(k as nat), p >= 1,
    no_unwind
{
    proof {
        lemma_pow10_i128_boundary();
        lemma_pow10_monotone(k as nat, 38);
        lemma_pow10_positive(k as nat);
    }
    match pow10_exec(k) {
        Some(p) => p as u128,
        None => unreached(),
    }
}

/// Base-10000 weight and leading base-10000 digit of `c·10^-s`, `c != 0` (`nbase_weight`, `nbase_first_digit`).
fn nbase_weight_first_digit_exec(c: i128, s: u32) -> (r: (i64, u128))
    requires c != 0,
    ensures
        r.0 as int == nbase_weight(c as int, s as nat),
        r.1 as int == nbase_first_digit(c as int, s as nat),
        -0x1_0000_0000 <= r.0 <= 38,
    no_unwind
{
    let m = magnitude(c);
    let n = decimal_digits_exec(m);
    proof {
        lemma_decimal_digits_bound(m as int, n as nat);
        if n == 0 {
            assert(pow10(0) == 1);
        }
    }
    let e: i64 = n as i64 - 1 - s as i64;
    let (w, em) = floor_divmod(e, 4);
    // t = -s - 4w = 1 - n + (e mod 4)
    let t: i64 = 1 - n as i64 + em;
    let ghost ts = 0 - s as int - 4 * (w as int);
    assert(ts == t as int);
    if t >= 0 {
        // n <= 4 here, so |c| < 10^4 and 10^t <= 10^3.
        proof {
            lemma_pow10_monotone(n as nat, 4);
            assert(pow10(4) == 10000) by (compute);
            lemma_pow10_monotone(t as nat, 3);
            assert(pow10(3) == 1000) by (compute);
        }
        let p = pow10_small(t as u32);
        assert(m * p <= 10000 * 1000) by (nonlinear_arith) requires m < 10000, p <= 1000;
        (w, m * p)
    } else {
        let p = pow10_small((0 - t) as u32);
        (w, m / p)
    }
}

/// `div_scale` (PostgreSQL `select_div_scale`).
pub fn div_scale_exec(c1: i128, s1: u32, c2: i128, s2: u32) -> (r: u32)
    ensures r as nat == div_scale(c1 as int, s1 as nat, c2 as int, s2 as nat), r <= 1000,
    no_unwind
{
    let (w1, d1) = if c1 == 0 { (0i64, 0u128) } else { nbase_weight_first_digit_exec(c1, s1) };
    let (w2, d2) = if c2 == 0 { (0i64, 0u128) } else { nbase_weight_first_digit_exec(c2, s2) };
    let qw0: i64 = w1 - w2;
    let qweight: i64 = if d1 <= d2 { qw0 - 1 } else { qw0 };
    // NUMERIC_MIN_SIG_DIGITS = 16, DEC_DIGITS = 4, NUMERIC_MAX_DISPLAY_SCALE = 1000 (`spec::fns::div`).
    let r0: i64 = 16 - qweight * 4;
    let r1: i64 = if r0 >= s1 as i64 { r0 } else { s1 as i64 };
    let r2: i64 = if r1 >= s2 as i64 { r1 } else { s2 as i64 };
    let r3: i64 = if r2 >= 0 { r2 } else { 0 };
    let r4: i64 = if r3 <= 1000 { r3 } else { 1000 };
    r4 as u32
}

/// `num_div` on `i128` coefficients, with `Capacity` exactly outside `num_div_fits`.
pub fn num_div_exec(c1: i128, s1: u32, c2: i128, s2: u32) -> (r: Outcome<EVal>)
    ensures
        match r {
            Ok(res) => num_div_fits(c1 as int, s1 as nat, c2 as int, s2 as nat)
                && view_result(res) == num_div(c1 as int, s1 as nat, c2 as int, s2 as nat),
            Err(_) => !num_div_fits(c1 as int, s1 as nat, c2 as int, s2 as nat),
        },
    no_unwind
{
    let ghost (gc1, gs1, gc2, gs2) = (c1 as int, s1 as nat, c2 as int, s2 as nat);
    if c2 == 0 {
        return Ok(Err(SqlError::DivisionByZero));
    }
    let r = div_scale_exec(c1, s1, c2, s2);
    if c1 == 0 {
        proof {
            let x = div_round(abs(gc1) * pow10(r as nat + gs2), abs(gc2) * pow10(gs1));
            assert(num_div_coeff(gc1, gs1, gc2, gs2) == sign(gc1) * sign(gc2) * x);
            assert(num_div_coeff(gc1, gs1, gc2, gs2) == 0) by (nonlinear_arith)
                requires num_div_coeff(gc1, gs1, gc2, gs2) == sign(gc1) * sign(gc2) * x, sign(gc1) == 0;
            lemma_num_in_range_small(0, r as nat);
        }
        return Ok(Ok(EVal::Num { coeff: 0, scale: r }));
    }
    let m1 = magnitude(c1);
    let m2 = magnitude(c2);
    let k: i64 = r as i64 + s2 as i64 - s1 as i64;
    proof {
        lemma_num_div_coeff_scaled(gc1, gs1, gc2, gs2);
        lemma_pow10_i128_boundary();
    }
    let (numerator, denominator): (u128, u128) = if k >= 0 {
        if k > 38 {
            proof {
                lemma_pow10_monotone(39, k as nat);
                assert(m1 * pow10(k as nat) >= pow10(k as nat)) by (nonlinear_arith)
                    requires m1 >= 1, pow10(k as nat) >= 1;
            }
            return Err(Capacity);
        }
        let p = pow10_small(k as u32);
        match m1.checked_mul(p) {
            Some(x) => (x, m2),
            None => return Err(Capacity),
        }
    } else {
        if k < -38 {
            proof {
                lemma_pow10_monotone(39, (0 - k) as nat);
                assert(m2 * pow10((0 - k) as nat) >= pow10((0 - k) as nat)) by (nonlinear_arith)
                    requires m2 >= 1, pow10((0 - k) as nat) >= 1;
            }
            return Err(Capacity);
        }
        let p = pow10_small((0 - k) as u32);
        match m2.checked_mul(p) {
            Some(y) => {
                assert(y >= 1) by (nonlinear_arith) requires y == m2 * p, m2 >= 1, p >= 1;
                (m1, y)
            },
            None => return Err(Capacity),
        }
    };
    let truncated = numerator / denominator;
    let remainder = numerator % denominator;
    proof {
        lemma_div_round_split(numerator as int, denominator as int);
        lemma_fundamental_div_mod(numerator as int, denominator as int);
        lemma_mod_pos_bound(numerator as int, denominator as int);
        if remainder >= denominator - remainder {
            assert(truncated < u128::MAX) by (nonlinear_arith)
                requires numerator == denominator * truncated + remainder, remainder >= 1, remainder < denominator,
                    numerator <= u128::MAX, truncated >= 0;
        }
    }
    let rounded: u128 = if remainder >= denominator - remainder { truncated + 1 } else { truncated };
    let ghost qs = div_round(numerator as int, denominator as int);
    assert(rounded as int == qs);
    // Apply the sign; the coefficient must fit `i128` (a magnitude of 2^127 only for a negative quotient).
    let negative = (c1 < 0) != (c2 < 0);
    let coeff: i128 = if negative {
        if rounded > 0x8000_0000_0000_0000_0000_0000_0000_0000u128 {
            proof {
                assert(num_div_coeff(gc1, gs1, gc2, gs2) == -qs) by (nonlinear_arith)
                    requires num_div_coeff(gc1, gs1, gc2, gs2) == sign(gc1) * sign(gc2) * qs, sign(gc1) * sign(gc2) == -1;
            }
            return Err(Capacity);
        }
        proof {
            assert(num_div_coeff(gc1, gs1, gc2, gs2) == -qs) by (nonlinear_arith)
                requires num_div_coeff(gc1, gs1, gc2, gs2) == sign(gc1) * sign(gc2) * qs, sign(gc1) * sign(gc2) == -1;
        }
        if rounded == 0x8000_0000_0000_0000_0000_0000_0000_0000u128 { i128::MIN } else { -(rounded as i128) }
    } else {
        if rounded > 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128 {
            proof {
                assert(num_div_coeff(gc1, gs1, gc2, gs2) == qs) by (nonlinear_arith)
                    requires num_div_coeff(gc1, gs1, gc2, gs2) == sign(gc1) * sign(gc2) * qs, sign(gc1) * sign(gc2) == 1;
            }
            return Err(Capacity);
        }
        proof {
            assert(num_div_coeff(gc1, gs1, gc2, gs2) == qs) by (nonlinear_arith)
                requires num_div_coeff(gc1, gs1, gc2, gs2) == sign(gc1) * sign(gc2) * qs, sign(gc1) * sign(gc2) == 1;
        }
        rounded as i128
    };
    proof {
        lemma_num_in_range_small(coeff as int, r as nat);
    }
    Ok(Ok(EVal::Num { coeff, scale: r }))
}

} // verus!
