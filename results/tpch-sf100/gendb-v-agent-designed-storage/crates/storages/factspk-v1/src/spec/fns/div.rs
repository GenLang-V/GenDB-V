//! Integer and numeric division (`Expr::Call` with `DivInt4`, `DivInt8`, `DivNumeric`), as PostgreSQL 18
//! (REL_18_3: int.c `int4div`, int8.c `int8div`, numeric.c `numeric_div_opt_error`, `select_div_scale`,
//! `div_var` with exact rounding).
//!
//! - `DivInt4` (`int4 / int4 -> int4`), `DivInt8` (`int8 / int8 -> int8`; the resolver casts an int4 operand
//!   to int8 first): a NULL operand gives NULL; a zero divisor is 22012 (checked first, also for `0 / 0`);
//!   otherwise the quotient truncated toward zero (C `/`), range-checked by `int_result` (so `MIN / -1` is
//!   22003).
//! - `DivNumeric` (`numeric / numeric -> numeric`; an integer operand is cast by `IntToNumeric`): a NULL operand
//!   gives NULL; a zero divisor is 22012; otherwise the exact quotient rounded half away from zero at the
//!   value-dependent result scale `div_scale` (PostgreSQL's `select_div_scale`: at least 16 significant digits
//!   estimated from the base-10000 weights and leading base-10000 digits of the operands, at least either
//!   operand's display scale, clamped to `[0, 1000]`), then PostgreSQL's format limit (`num_result`, 22003).
//!   The static type is `numeric` with display-scale bound 1000 (`NUMERIC_MAX_DISPLAY_SCALE`, a PostgreSQL
//!   fact, see `spec::types::ScalarTy`).
//!
//! The executable domain (`fits_div`) is `num_div_fits`: integer division never needs `Capacity`; numeric
//! division needs the scaled dividend `|c1|·10^k` (when `k >= 0`) or the scaled divisor `|c2|·10^-k` (when
//! `k < 0`), `k = rscale + s2 - s1`, to fit `u128` and the result coefficient to fit `i128`.
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::int::*;
use crate::spec::numeric::*;

verus! {

// ------------------------------------------------------------------ integer division

/// C `/` on integers (truncation toward zero), `b != 0`. Written out because the spec's `/` is Euclidean.
pub open spec fn trunc_div(a: int, b: int) -> int {
    sign(a) * sign(b) * (abs(a) / abs(b))
}

/// `a / b` at integer type `k` (`int4div` / `int8div`): 22012 for a zero divisor, then the range check.
pub open spec fn int_div(k: IntKind, a: int, b: int) -> Result<Val, SqlError> {
    if b == 0 { Err(SqlError::DivisionByZero) } else { int_result(k, trunc_div(a, b)) }
}

// ------------------------------------------------------------------ numeric division

/// `NUMERIC_MIN_SIG_DIGITS`.
pub open spec fn numeric_min_sig_digits() -> int { 16 }
/// `NUMERIC_MAX_DISPLAY_SCALE` (= `NUMERIC_MAX_PRECISION`); also the static display-scale bound of a quotient.
pub open spec fn numeric_max_display_scale() -> int { 1000 }
/// `DEC_DIGITS`: decimal digits per base-10000 (`NBASE`) digit.
pub open spec fn dec_digits() -> int { 4 }

/// Base-10000 weight of the leading nonzero digit of `coeff·10^-scale` (0 for zero): `floor(e / 4)` where
/// `e = digits(|coeff|) - 1 - scale` is the decimal exponent of the leading decimal digit (the spec's `/` by a
/// positive divisor is floor division). PostgreSQL's digits are aligned at the decimal point, so this is the
/// normalized `weight` that `select_div_scale` reads.
pub open spec fn nbase_weight(coeff: int, scale: nat) -> int {
    if coeff == 0 { 0 } else { (decimal_digits(abs(coeff)) - 1 - scale) / dec_digits() }
}

/// Leading nonzero base-10000 digit of `coeff·10^-scale` (0 for zero): `floor(|coeff|·10^t)` with
/// `t = -scale - 4·weight` (in `[1, 9999]` for nonzero values, `bridge::fns::div::lemma_nbase_first_digit_range`).
pub open spec fn nbase_first_digit(coeff: int, scale: nat) -> int {
    if coeff == 0 {
        0
    } else {
        let t = 0 - scale - dec_digits() * nbase_weight(coeff, scale);
        if t >= 0 { abs(coeff) * pow10(t as nat) } else { abs(coeff) / pow10((0 - t) as nat) }
    }
}

/// `select_div_scale`: the estimated base-10000 weight of the quotient (one less when the leading digits do not
/// show that the dividend's leading digit is larger), then
/// `min(1000, max(max(max(16 - 4·qweight, s1), s2), 0))` in PostgreSQL's order.
pub open spec fn div_scale(c1: int, s1: nat, c2: int, s2: nat) -> nat {
    let qw0 = nbase_weight(c1, s1) - nbase_weight(c2, s2);
    let qweight = if nbase_first_digit(c1, s1) <= nbase_first_digit(c2, s2) { qw0 - 1 } else { qw0 };
    let r0 = numeric_min_sig_digits() - qweight * dec_digits();
    let r1 = if r0 >= s1 { r0 } else { s1 as int };
    let r2 = if r1 >= s2 { r1 } else { s2 as int };
    let r3 = if r2 >= 0 { r2 } else { 0 };
    let r4 = if r3 <= numeric_max_display_scale() { r3 } else { numeric_max_display_scale() };
    r4 as nat
}

/// `n / d` rounded half away from zero, for `n >= 0` and `d > 0`: `floor((2n + d) / (2d))`.
pub open spec fn div_round(n: int, d: int) -> int {
    (2 * n + d) / (2 * d)
}

/// Coefficient of `(c1·10^-s1) / (c2·10^-s2)` at scale `r = div_scale(..)`, rounded half away from zero:
/// the exact scaled quotient is `c1·10^(r+s2) / (c2·10^s1)`.
pub open spec fn num_div_coeff(c1: int, s1: nat, c2: int, s2: nat) -> int {
    let r = div_scale(c1, s1, c2, s2);
    sign(c1) * sign(c2) * div_round(abs(c1) * pow10(r + s2), abs(c2) * pow10(s1))
}

/// `numeric_div`: 22012 for a zero divisor, otherwise the rounded quotient at scale `div_scale`, then
/// PostgreSQL's format limit (22003).
pub open spec fn num_div(c1: int, s1: nat, c2: int, s2: nat) -> Result<Val, SqlError> {
    if c2 == 0 {
        Err(SqlError::DivisionByZero)
    } else {
        num_result(num_div_coeff(c1, s1, c2, s2), div_scale(c1, s1, c2, s2))
    }
}

pub open spec fn in_u128(x: int) -> bool {
    0 <= x <= u128::MAX as int
}

pub open spec fn in_i128(x: int) -> bool {
    i128::MIN as int <= x <= i128::MAX as int
}

/// Executable domain of `num_div` on `i128` coefficients: the intermediates the evaluator computes. A zero
/// divisor (22012) or dividend (quotient 0) computes none; otherwise, with `k = rscale + s2 - s1`, the scaled
/// dividend `|c1|·10^k` (`k >= 0`) or scaled divisor `|c2|·10^-k` (`k < 0`) must fit `u128` (the rounded quotient
/// is computed from it and the other unscaled magnitude) and the result coefficient must fit `i128`.
pub open spec fn num_div_fits(c1: int, s1: nat, c2: int, s2: nat) -> bool {
    c2 == 0 || c1 == 0 || {
        let k = div_scale(c1, s1, c2, s2) + s2 - s1;
        &&& if k >= 0 { in_u128(abs(c1) * pow10(k as nat)) } else { in_u128(abs(c2) * pow10((0 - k) as nat)) }
        &&& in_i128(num_div_coeff(c1, s1, c2, s2))
    }
}

// ------------------------------------------------------------------ the `Call` interface (`spec::fns`)

/// Result type: `int4 / int4 -> int4`, `int8 / int8 -> int8`, `numeric / numeric -> numeric` with display-scale
/// bound 1000; nullable if an operand is.
pub open spec fn type_div(f: ScalarFn, args: Seq<ColTy>) -> Option<ColTy> {
    if args.len() != 2 {
        None
    } else {
        let nullable = args[0].nullable || args[1].nullable;
        match (f, args[0].ty, args[1].ty) {
            (ScalarFn::DivInt4, ScalarTy::Int4, ScalarTy::Int4) => Some(ColTy { ty: ScalarTy::Int4, nullable }),
            (ScalarFn::DivInt8, ScalarTy::Int8, ScalarTy::Int8) => Some(ColTy { ty: ScalarTy::Int8, nullable }),
            (ScalarFn::DivNumeric, ScalarTy::Numeric { .. }, ScalarTy::Numeric { .. }) =>
                Some(ColTy { ty: ScalarTy::Numeric { scale: 1000 }, nullable }),
            _ => None,
        }
    }
}

/// Value of a division on its evaluated operands (strict: a NULL operand gives NULL).
pub open spec fn apply_div(f: ScalarFn, args: Seq<Val>) -> Result<Val, SqlError> {
    if args.len() != 2 {
        Err(SqlError::TypeError)
    } else {
        match (args[0], args[1]) {
            (Val::Null, _) => Ok(Val::Null),
            (_, Val::Null) => Ok(Val::Null),
            (Val::Int(a), Val::Int(b)) => match f {
                ScalarFn::DivInt4 => int_div(IntKind::Int4, a, b),
                ScalarFn::DivInt8 => int_div(IntKind::Int8, a, b),
                _ => Err(SqlError::TypeError),
            },
            (Val::Num { coeff: c1, scale: s1 }, Val::Num { coeff: c2, scale: s2 }) => match f {
                ScalarFn::DivNumeric => num_div(c1, s1, c2, s2),
                _ => Err(SqlError::TypeError),
            },
            _ => Err(SqlError::TypeError),
        }
    }
}

/// Executable domain of `apply_div` (only numeric division can leave it).
pub open spec fn fits_div(f: ScalarFn, args: Seq<Val>) -> bool {
    args.len() == 2 ==> match (f, args[0], args[1]) {
        (ScalarFn::DivNumeric, Val::Num { coeff: c1, scale: s1 }, Val::Num { coeff: c2, scale: s2 }) =>
            num_div_fits(c1, s1, c2, s2),
        _ => true,
    }
}

} // verus!
