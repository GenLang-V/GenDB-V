//! Checked examples of division and AVG on concrete values, each an actual PostgreSQL 18.3 result recorded by the
//! numeric review (reference fixture `cov_n`). They pin
//! the leaf functions only (no AST evaluation), so `by (compute)` stays cheap.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::scalar::*;
use crate::spec::fns::div::*;
use crate::spec::aggs::avg::*;

verus! {

/// `7/2, (-7)/2, 7/(-2), (-7)/(-2)` = `3, -3, -3, 3`; `1/0` and `0/0` are 22012 (checked before the range);
/// `(-2147483648)::int4 / (-1)` and `(-9223372036854775808)::int8 / (-1)` are 22003.
pub proof fn pin_int_div() {
    assert(int_div(IntKind::Int4, 7, 2) == Ok::<Val, SqlError>(Val::Int(3))) by (compute);
    assert(int_div(IntKind::Int4, -7, 2) == Ok::<Val, SqlError>(Val::Int(-3))) by (compute);
    assert(int_div(IntKind::Int4, 7, -2) == Ok::<Val, SqlError>(Val::Int(-3))) by (compute);
    assert(int_div(IntKind::Int4, -7, -2) == Ok::<Val, SqlError>(Val::Int(3))) by (compute);
    assert(int_div(IntKind::Int4, 1, 0) == Err::<Val, SqlError>(SqlError::DivisionByZero)) by (compute);
    assert(int_div(IntKind::Int8, 0, 0) == Err::<Val, SqlError>(SqlError::DivisionByZero)) by (compute);
    assert(int_div(IntKind::Int4, -2147483648, -1) == Err::<Val, SqlError>(SqlError::NumericValueOutOfRange))
        by (compute);
    assert(int_div(IntKind::Int8, -9223372036854775808, -1) == Err::<Val, SqlError>(SqlError::NumericValueOutOfRange))
        by (compute);
}

/// Value-dependent result scale and half-away-from-zero rounding:
/// `1/3 = 0.33333333333333333333` (scale 20), `2/3 = 0.66666666666666666667`, `(-2)/3 = -0.66666666666666666667`,
/// `5/2 = 2.5000000000000000` (16), `10000/3 = 3333.3333333333333333` (16), `1/10000 = 0.000100000000000000000000`
/// (24), `0.5/1000000000000000000000` = 5e-22 at scale 40, `0/3` = 0 at scale 20, `1/0` = 22012;
/// `3/2` (scale 16) and `15000/10000` (scale 20) are the same value at different display scales.
pub proof fn pin_num_div() {
    assert(num_div(1, 0, 3, 0) == Ok::<Val, SqlError>(Val::Num { coeff: 33333333333333333333, scale: 20 }))
        by (compute);
    assert(num_div(2, 0, 3, 0) == Ok::<Val, SqlError>(Val::Num { coeff: 66666666666666666667, scale: 20 }))
        by (compute);
    assert(num_div(-2, 0, 3, 0) == Ok::<Val, SqlError>(Val::Num { coeff: -66666666666666666667, scale: 20 }))
        by (compute);
    assert(num_div(5, 0, 2, 0) == Ok::<Val, SqlError>(Val::Num { coeff: 25000000000000000, scale: 16 }))
        by (compute);
    assert(num_div(10000, 0, 3, 0) == Ok::<Val, SqlError>(Val::Num { coeff: 33333333333333333333, scale: 16 }))
        by (compute);
    assert(num_div(1, 0, 10000, 0) == Ok::<Val, SqlError>(Val::Num { coeff: 100000000000000000000, scale: 24 }))
        by (compute);
    assert(num_div(5, 1, 1000000000000000000000, 0) == Ok::<Val, SqlError>(Val::Num { coeff: 5000000000000000000, scale: 40 }))
        by (compute);
    assert(num_div(0, 0, 3, 0) == Ok::<Val, SqlError>(Val::Num { coeff: 0, scale: 20 })) by (compute);
    assert(num_div(1, 0, 0, 0) == Err::<Val, SqlError>(SqlError::DivisionByZero)) by (compute);
    assert(num_div(3, 0, 2, 0) == Ok::<Val, SqlError>(Val::Num { coeff: 15000000000000000, scale: 16 }))
        by (compute);
    assert(num_div(15000, 0, 10000, 0) == Ok::<Val, SqlError>(Val::Num { coeff: 150000000000000000000, scale: 20 }))
        by (compute);
}

/// Scale clamp at `NUMERIC_MAX_DISPLAY_SCALE`: `5e-1001/1` rounds its tie away from zero to `1e-1000` (scale
/// 1000), `-5e-1001/1` to `-1e-1000`, `4e-1001/1` to 0 at scale 1000.
pub proof fn pin_num_div_scale_clamp() {
    assert(num_div(5, 1001, 1, 0) == Ok::<Val, SqlError>(Val::Num { coeff: 1, scale: 1000 })) by (compute);
    assert(num_div(-5, 1001, 1, 0) == Ok::<Val, SqlError>(Val::Num { coeff: -1, scale: 1000 })) by (compute);
    assert(num_div(4, 1001, 1, 0) == Ok::<Val, SqlError>(Val::Num { coeff: 0, scale: 1000 })) by (compute);
}

/// AVG: int `{1, 2, 2}` = `1.6666666666666667`; numeric `{1.5, 2.25, NULL}` = `1.8750000000000000`;
/// numeric `{1.000, 2}` = `1.5000000000000000`; int `{-1, -2}` = `-1.5000000000000000`; int `{NULL}` and `{}` are
/// NULL; int `{2147483647, 2147483647}` = `2147483647.00000000` (no int8/int4 range check on the sum).
pub proof fn pin_avg() {
    assert(avg_value(NumKind::Int4, seq![Val::Int(1), Val::Int(2), Val::Int(2)])
        == Ok::<Val, SqlError>(Val::Num { coeff: 16666666666666667, scale: 16 })) by (compute);
    assert(avg_value(NumKind::Numeric, seq![Val::Num { coeff: 15, scale: 1 }, Val::Num { coeff: 225, scale: 2 }, Val::Null])
        == Ok::<Val, SqlError>(Val::Num { coeff: 18750000000000000, scale: 16 })) by (compute);
    assert(avg_value(NumKind::Numeric, seq![Val::Num { coeff: 1000, scale: 3 }, Val::Num { coeff: 2, scale: 0 }])
        == Ok::<Val, SqlError>(Val::Num { coeff: 15000000000000000, scale: 16 })) by (compute);
    assert(avg_value(NumKind::Int4, seq![Val::Int(-1), Val::Int(-2)])
        == Ok::<Val, SqlError>(Val::Num { coeff: -15000000000000000, scale: 16 })) by (compute);
    assert(avg_value(NumKind::Int4, seq![Val::Null]) == Ok::<Val, SqlError>(Val::Null)) by (compute);
    assert(avg_value(NumKind::Int8, Seq::<Val>::empty()) == Ok::<Val, SqlError>(Val::Null)) by (compute);
    assert(avg_value(NumKind::Int4, seq![Val::Int(2147483647), Val::Int(2147483647)])
        == Ok::<Val, SqlError>(Val::Num { coeff: 214748364700000000, scale: 8 })) by (compute);
}

} // verus!
