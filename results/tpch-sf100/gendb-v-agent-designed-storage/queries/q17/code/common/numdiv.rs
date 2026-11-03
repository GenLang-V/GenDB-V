//! Exact numeric division (`spec::fns::div::num_div`, PostgreSQL `numeric_div`) on `i128` coefficients as `no_unwind`
//! code, so worker tasks can compute quotients such as AVG (`sum / count`): the result scale `div_scale` from the
//! decimal digit counts of the operands, then the quotient rounded half away from zero. `None` exactly where the
//! framework's `exec::fns::div::num_div_exec` reports `Capacity` (outside `num_div_fits`) or for a zero divisor.
use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::fns::div::*;
use crate::bridge::fns::div::*;

verus! {

/// `|c|` (every `i128` magnitude fits `u128`).
pub fn magnitude_nu(c: i128) -> (m: u128)
    ensures m as int == abs(c as int),
    no_unwind
{
    if c >= 0 { c as u128 } else { ((-(c + 1)) as u128) + 1 }
}

/// Number of decimal digits of `m` (at most 39).
pub fn decimal_digits_nu(m: u128) -> (n: u32)
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

/// `10^k` for `k <= 38` (it fits `u128`).
pub fn pow10_nu(k: u32) -> (p: u128)
    requires k <= 38,
    ensures p as int == pow10(k as nat), p >= 1,
    no_unwind
{
    proof {
        lemma_pow10_i128_boundary();
        lemma_pow10_monotone(k as nat, 38);
    }
    let mut acc: u128 = 1;
    let mut i: u32 = 0;
    while i < k
        invariant
            i <= k <= 38,
            acc as int == pow10(i as nat),
            pow10(38) < 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff,
        decreases k - i,
    {
        proof {
            lemma_pow10_monotone((i + 1) as nat, 38);
            assert(pow10((i + 1) as nat) == 10 * pow10(i as nat));
        }
        acc = acc * 10;
        i = i + 1;
    }
    proof {
        lemma_pow10_positive(k as nat);
    }
    acc
}

/// Floor division and (nonnegative) modulus by 4 of a small integer.
fn floor_div4(x: i64) -> (r: (i64, i64))
    requires -0x1_0000_0000 <= x <= 0x1_0000_0000,
    ensures
        r.0 as int == x as int / 4,
        r.1 as int == x as int % 4,
        0 <= r.1 < 4,
        r.0 * 4 + r.1 == x,
    no_unwind
{
    if x >= 0 {
        let u = x as u64;
        proof {
            lemma_fundamental_div_mod(u as int, 4);
            lemma_mod_pos_bound(u as int, 4);
        }
        ((u / 4) as i64, (u % 4) as i64)
    } else {
        let u = (0 - x) as u64;
        let c = (u + 3) / 4;
        let q: i64 = 0 - (c as i64);
        let m: i64 = x - 4 * q;
        proof {
            let (xi, ui, ci) = (x as int, u as int, c as int);
            lemma_fundamental_div_mod(ui + 3, 4);
            lemma_mod_pos_bound(ui + 3, 4);
            // 4c <= u + 3 < 4c + 4, so 0 <= x + 4c = m <= 3, and x = 4(-c) + m pins the Euclidean quotient.
            assert(4 * ci <= ui + 3 < 4 * ci + 4);
            assert(0 <= m < 4);
            assert(xi == 4 * (q as int) + (m as int));
            lemma_fundamental_div_mod_converse(xi, 4, q as int, m as int);
        }
        (q, m)
    }
}

/// Base-10000 weight and leading base-10000 digit of `c·10^-s`, `c != 0` (`nbase_weight`, `nbase_first_digit`).
fn nbase_weight_first_digit_nu(c: i128, s: u32) -> (r: (i64, u128))
    requires c != 0, s <= 0x1000_0000,
    ensures
        r.0 as int == nbase_weight(c as int, s as nat),
        r.1 as int == nbase_first_digit(c as int, s as nat),
        -0x1000_0000 <= r.0 <= 38,
    no_unwind
{
    let m = magnitude_nu(c);
    let n = decimal_digits_nu(m);
    proof {
        lemma_decimal_digits_bound(m as int, n as nat);
        if n == 0 {
            assert(pow10(0) == 1);
        }
    }
    let e: i64 = n as i64 - 1 - s as i64;
    let (w, em) = floor_div4(e);
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
        let p = pow10_nu(t as u32);
        assert(m * p <= 10000 * 1000) by (nonlinear_arith) requires m < 10000, p <= 1000;
        (w, m * p)
    } else {
        let p = pow10_nu((0 - t) as u32);
        (w, m / p)
    }
}

/// `div_scale` (PostgreSQL `select_div_scale`).
pub fn div_scale_nu(c1: i128, s1: u32, c2: i128, s2: u32) -> (r: u32)
    requires s1 <= 0x1000_0000, s2 <= 0x1000_0000,
    ensures r as nat == div_scale(c1 as int, s1 as nat, c2 as int, s2 as nat), r <= 1000,
    no_unwind
{
    let (w1, d1) = if c1 == 0 { (0i64, 0u128) } else { nbase_weight_first_digit_nu(c1, s1) };
    let (w2, d2) = if c2 == 0 { (0i64, 0u128) } else { nbase_weight_first_digit_nu(c2, s2) };
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

/// `m > MAX / p` means `m * p > MAX` (`MAX = u128::MAX`, `p >= 1`).
proof fn lemma_mul_over(m: int, p: int)
    requires p >= 1, m > (u128::MAX as int) / p,
    ensures m * p > u128::MAX as int,
{
    let mx = u128::MAX as int;
    lemma_fundamental_div_mod(mx, p);
    lemma_mod_pos_bound(mx, p);
    let q = mx / p;
    let rr = mx % p;
    assert(m * p >= (q + 1) * p) by (nonlinear_arith) requires m >= q + 1, p >= 1;
    assert((q + 1) * p == p * q + p) by (nonlinear_arith);
}

/// `m <= MAX / p` means `m * p <= MAX` (`MAX = u128::MAX`, `p >= 1`, `m >= 0`).
proof fn lemma_mul_under(m: int, p: int)
    requires p >= 1, 0 <= m <= (u128::MAX as int) / p,
    ensures m * p <= u128::MAX as int,
{
    let mx = u128::MAX as int;
    lemma_fundamental_div_mod(mx, p);
    lemma_mod_pos_bound(mx, p);
    let q = mx / p;
    assert(m * p <= q * p) by (nonlinear_arith) requires m <= q, p >= 1;
    assert(q * p == p * q) by (nonlinear_arith);
}

/// `num_div` on `i128` coefficients: `Some((coeff, scale))` with `num_div(..) == Ok(Num { coeff, scale })` inside
/// `num_div_fits`, `None` for a zero divisor or outside `num_div_fits`.
pub fn num_div_nu(c1: i128, s1: u32, c2: i128, s2: u32) -> (r: Option<(i128, u32)>)
    requires s1 <= 1000, s2 <= 1000,
    ensures
        r matches Some((q, sc)) ==> c2 != 0 && num_div_fits(c1 as int, s1 as nat, c2 as int, s2 as nat)
            && num_div(c1 as int, s1 as nat, c2 as int, s2 as nat) == Ok::<Val, SqlError>(Val::Num { coeff: q as int, scale: sc as nat }),
        r is None ==> c2 == 0 || !num_div_fits(c1 as int, s1 as nat, c2 as int, s2 as nat),
    no_unwind
{
    let ghost (gc1, gs1, gc2, gs2) = (c1 as int, s1 as nat, c2 as int, s2 as nat);
    if c2 == 0 {
        return None;
    }
    let r = div_scale_nu(c1, s1, c2, s2);
    if c1 == 0 {
        proof {
            let x = div_round(abs(gc1) * pow10(r as nat + gs2), abs(gc2) * pow10(gs1));
            assert(num_div_coeff(gc1, gs1, gc2, gs2) == sign(gc1) * sign(gc2) * x);
            assert(num_div_coeff(gc1, gs1, gc2, gs2) == 0) by (nonlinear_arith)
                requires num_div_coeff(gc1, gs1, gc2, gs2) == sign(gc1) * sign(gc2) * x, sign(gc1) == 0;
            lemma_num_in_range_small(0, r as nat);
        }
        return Some((0, r));
    }
    let m1 = magnitude_nu(c1);
    let m2 = magnitude_nu(c2);
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
            return None;
        }
        let p = pow10_nu(k as u32);
        if m1 > u128::MAX / p {
            proof {
                lemma_mul_over(m1 as int, p as int);
            }
            return None;
        }
        proof {
            lemma_mul_under(m1 as int, p as int);
        }
        (m1 * p, m2)
    } else {
        if k < -38 {
            proof {
                lemma_pow10_monotone(39, (0 - k) as nat);
                assert(m2 * pow10((0 - k) as nat) >= pow10((0 - k) as nat)) by (nonlinear_arith)
                    requires m2 >= 1, pow10((0 - k) as nat) >= 1;
            }
            return None;
        }
        let p = pow10_nu((0 - k) as u32);
        if m2 > u128::MAX / p {
            proof {
                lemma_mul_over(m2 as int, p as int);
            }
            return None;
        }
        proof {
            lemma_mul_under(m2 as int, p as int);
            assert(m2 * p >= 1) by (nonlinear_arith) requires m2 >= 1, p >= 1;
        }
        (m1, m2 * p)
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
        proof {
            assert(num_div_coeff(gc1, gs1, gc2, gs2) == -qs) by (nonlinear_arith)
                requires num_div_coeff(gc1, gs1, gc2, gs2) == sign(gc1) * sign(gc2) * qs, sign(gc1) * sign(gc2) == -1;
        }
        if rounded > 0x8000_0000_0000_0000_0000_0000_0000_0000u128 {
            return None;
        }
        if rounded == 0x8000_0000_0000_0000_0000_0000_0000_0000u128 { i128::MIN } else { -(rounded as i128) }
    } else {
        proof {
            assert(num_div_coeff(gc1, gs1, gc2, gs2) == qs) by (nonlinear_arith)
                requires num_div_coeff(gc1, gs1, gc2, gs2) == sign(gc1) * sign(gc2) * qs, sign(gc1) * sign(gc2) == 1;
        }
        if rounded > 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128 {
            return None;
        }
        rounded as i128
    };
    proof {
        lemma_num_in_range_small(coeff as int, r as nat);
    }
    Some((coeff, r))
}

} // verus!
