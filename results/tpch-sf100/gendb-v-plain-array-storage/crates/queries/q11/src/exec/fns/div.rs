//! Executable `spec::fns::div`: integer division in `i128`/`u128` (never `Capacity`), numeric division over
//! `i128` coefficients with `Capacity` exactly outside `spec::fns::div::num_div_fits`.
//!
//! Numeric division (PostgreSQL `numeric_div`): the result scale `r` is computed exactly (decimal digit count of
//! each magnitude, at most 39, then the base-10000 weight by floor division and the leading base-10000 digit with
//! one power of ten of at most 38). With `k = r + s2 - s1` the quotient magnitude is `numerator / denominator`
//! rounded half away from zero, where `numerator = |c1|·10^k, denominator = |c2|` (`k >= 0`) or
//! `numerator = |c1|, denominator = |c2|·10^-k` (`k < 0`): the truncated quotient, plus one when the remainder is
//! at least half of the denominator (`bridge::fns::div::lemma_div_round_split`), so no intermediate exceeds the
//! numerator or the denominator.
//!
//! The proofs use lemmas of `bridge::fns::div` (the only `exec` dependency on `bridge`).
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
use crate::exec::numeric::*;
use crate::exec::scalar::*;
use crate::exec::datetime::floor_divmod;
use crate::bridge::fns::div::*;

verus! {

/// `|c|` (every `i128` magnitude fits `u128`).
pub fn magnitude(c: i128) -> (m: u128)
    ensures m as int == abs(c as int),
{
    if c >= 0 { c as u128 } else { ((-(c + 1)) as u128) + 1 }
}

/// Number of decimal digits of `m` (at most 39).
fn decimal_digits_exec(m: u128) -> (n: u32)
    ensures n as nat == decimal_digits(m as int), n <= 39,
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

/// `int_div` on `i64` operands (int4 values are `i64` in range); never `Capacity`.
pub fn int_div_exec(k: IntKind, a: i64, b: i64) -> (r: Result<EVal, SqlError>)
    ensures view_result(r) == int_div(k, a as int, b as int),
{
    if b == 0 {
        return Err(SqlError::DivisionByZero);
    }
    let ua = magnitude(a as i128);
    let ub = magnitude(b as i128);
    let q = ua / ub;
    proof {
        lemma_fundamental_div_mod(ua as int, ub as int);
        lemma_mod_pos_bound(ua as int, ub as int);
        assert(q <= ua) by (nonlinear_arith) requires ua == ub * q + (ua % ub), ua % ub >= 0, ub >= 1, q >= 0;
        if a == 0 {
            lemma_fundamental_div_mod_converse(0int, ub as int, 0int, 0int);
        }
    }
    let ghost qa = abs(a as int) / abs(b as int);
    assert(q as int == qa);
    let v: i128 = if (a < 0) != (b < 0) { -(q as i128) } else { q as i128 };
    proof {
        let (ga, gb) = (a as int, b as int);
        if a == 0 {
            assert(trunc_div(ga, gb) == 0) by (nonlinear_arith) requires trunc_div(ga, gb) == sign(ga) * sign(gb) * qa, sign(ga) == 0;
            assert(v == 0);
        } else if (a < 0) != (b < 0) {
            assert(trunc_div(ga, gb) == -qa) by (nonlinear_arith)
                requires trunc_div(ga, gb) == sign(ga) * sign(gb) * qa, sign(ga) * sign(gb) == -1;
        } else {
            assert(trunc_div(ga, gb) == qa) by (nonlinear_arith)
                requires trunc_div(ga, gb) == sign(ga) * sign(gb) * qa, sign(ga) * sign(gb) == 1;
        }
    }
    int_result_exec(k, v)
}

/// `spec::fns::div::apply_div`: `/` on two int4, two int8 or two numeric values (NULL if either is NULL).
pub fn exec_div(f: ScalarFn, args: &Vec<EVal>) -> (r: Outcome<EVal>)
    requires row_ts_ok(view_row(args@)),
    ensures
        match r {
            Ok(res) => fits_div(f, view_row(args@)) && view_result(res) == apply_div(f, view_row(args@))
                && (res matches Ok(v) ==> val_ts_ok(v@)),
            Err(_) => !fits_div(f, view_row(args@)),
        },
{
    if args.len() != 2 {
        return Ok(Err(SqlError::TypeError));
    }
    let ghost g = view_row(args@);
    assert(g[0] == args@[0]@ && g[1] == args@[1]@);
    match (&args[0], &args[1]) {
        (EVal::Null, _) => Ok(Ok(EVal::Null)),
        (_, EVal::Null) => Ok(Ok(EVal::Null)),
        (EVal::Int(a), EVal::Int(b)) => match f {
            ScalarFn::DivInt4 => Ok(int_div_exec(IntKind::Int4, *a, *b)),
            ScalarFn::DivInt8 => Ok(int_div_exec(IntKind::Int8, *a, *b)),
            _ => Ok(Err(SqlError::TypeError)),
        },
        (EVal::Num { coeff: c1, scale: s1 }, EVal::Num { coeff: c2, scale: s2 }) => match f {
            ScalarFn::DivNumeric => num_div_exec(*c1, *s1, *c2, *s2),
            _ => Ok(Err(SqlError::TypeError)),
        },
        _ => Ok(Err(SqlError::TypeError)),
    }
}

/// `spec::fns::div::type_div`: int4, int8 or numeric at the maximum display scale 1000.
pub fn type_div_exec(f: ScalarFn, args: &Vec<ColTy>) -> (r: Option<ColTy>)
    ensures r == type_div(f, args@),
{
    if args.len() != 2 {
        return None;
    }
    let nullable = args[0].nullable || args[1].nullable;
    match (f, args[0].ty, args[1].ty) {
        (ScalarFn::DivInt4, ScalarTy::Int4, ScalarTy::Int4) => Some(ColTy { ty: ScalarTy::Int4, nullable }),
        (ScalarFn::DivInt8, ScalarTy::Int8, ScalarTy::Int8) => Some(ColTy { ty: ScalarTy::Int8, nullable }),
        (ScalarFn::DivNumeric, ScalarTy::Numeric { .. }, ScalarTy::Numeric { .. }) =>
            Some(ColTy { ty: ScalarTy::Numeric { scale: 1000 }, nullable }),
        _ => None,
    }
}

} // verus!
