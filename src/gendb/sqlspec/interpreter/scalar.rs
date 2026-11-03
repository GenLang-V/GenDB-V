//! Executable value-level SQL operators (`spec::int`, `spec::scalar`, three-valued logic of `spec::value`):
//! integer range checks, arithmetic, unary minus, casts, interval addition, comparison and truth values. Each
//! postcondition states the bridge to the spec operator (and, for operators that can leave the executable
//! domain, `Capacity` exactly outside the `exec::domain` predicate).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::datetime::*;
use crate::spec::scalar::*;
use crate::exec::value::*;
use crate::exec::domain::*;
use crate::exec::numeric::*;
use crate::exec::datetime::*;
use crate::exec::text::*;

verus! {

/// `spec::int::int_in_range`.
pub fn int_in_range_exec(k: IntKind, v: i128) -> (r: bool)
    ensures r == int_in_range(k, v as int),
{
    match k {
        IntKind::Int4 => -0x8000_0000i128 <= v && v <= 0x7fff_ffffi128,
        IntKind::Int8 => -0x8000_0000_0000_0000i128 <= v && v <= 0x7fff_ffff_ffff_ffffi128,
    }
}

/// `spec::int::int_result` for an exact result that fits `i128`.
pub fn int_result_exec(k: IntKind, v: i128) -> (r: Result<EVal, SqlError>)
    ensures view_result(r) == int_result(k, v as int),
{
    if int_in_range_exec(k, v) { Ok(EVal::Int(v as i64)) } else { Err(SqlError::NumericValueOutOfRange) }
}

/// `spec::scalar::int_kind_of`.
pub fn int_kind_of_exec(k: NumKind) -> (r: IntKind)
    ensures r == int_kind_of(k),
{
    match k {
        NumKind::Int8 => IntKind::Int8,
        _ => IntKind::Int4,
    }
}

/// `spec::scalar::arith`.
pub fn arith_exec(op: ArithOp, kind: NumKind, a: &EVal, b: &EVal) -> (r: Outcome<EVal>)
    ensures
        match r {
            Ok(res) => arith_fits(op, kind, a@, b@) && view_result(res) == arith(op, kind, a@, b@),
            Err(_) => !arith_fits(op, kind, a@, b@),
        },
{
    match (a, b) {
        (EVal::Null, EVal::Null) | (EVal::Null, EVal::Int(_)) | (EVal::Int(_), EVal::Null)
        | (EVal::Null, EVal::Num { .. }) | (EVal::Num { .. }, EVal::Null) => Ok(Ok(EVal::Null)),
        (EVal::Int(x), EVal::Int(y)) => match kind {
            NumKind::Numeric => Ok(Err(SqlError::TypeError)),
            _ => {
                let v: i128 = match op {
                    ArithOp::Add => *x as i128 + *y as i128,
                    ArithOp::Sub => *x as i128 - *y as i128,
                    ArithOp::Mul => {
                        let (xi, yi) = (*x as i128, *y as i128);
                        proof {
                            // |x|, |y| <= 2^63, so |x * y| <= 2^126.
                            assert(-0x4000_0000_0000_0000_0000_0000_0000_0000 <= xi * yi
                                <= 0x4000_0000_0000_0000_0000_0000_0000_0000) by (nonlinear_arith)
                                requires -0x8000_0000_0000_0000 <= xi <= 0x8000_0000_0000_0000,
                                    -0x8000_0000_0000_0000 <= yi <= 0x8000_0000_0000_0000;
                        }
                        xi * yi
                    },
                };
                Ok(int_result_exec(int_kind_of_exec(kind), v))
            },
        },
        (EVal::Num { coeff: c1, scale: s1 }, EVal::Num { coeff: c2, scale: s2 }) => match kind {
            NumKind::Numeric => match num_arith_exec(op, *c1, *s1, *c2, *s2) {
                Ok((c, s)) => {
                    proof {
                        lemma_num_in_range_small(c as int, s as nat);
                    }
                    Ok(Ok(EVal::Num { coeff: c, scale: s }))
                },
                Err(cap) => Err(cap),
            },
            _ => Ok(Err(SqlError::TypeError)),
        },
        _ => Ok(Err(SqlError::TypeError)),
    }
}

/// `spec::scalar::neg`.
pub fn neg_exec(kind: NumKind, a: &EVal) -> (r: Outcome<EVal>)
    ensures
        match r {
            Ok(res) => neg_fits(kind, a@) && view_result(res) == neg(kind, a@),
            Err(_) => !neg_fits(kind, a@),
        },
{
    match a {
        EVal::Null => Ok(Ok(EVal::Null)),
        EVal::Int(x) => match kind {
            NumKind::Numeric => Ok(Err(SqlError::TypeError)),
            _ => Ok(int_result_exec(int_kind_of_exec(kind), -(*x as i128))),
        },
        EVal::Num { coeff, scale } => match kind {
            NumKind::Numeric => if *coeff == i128::MIN {
                Err(Capacity)
            } else {
                let c = -*coeff;
                proof {
                    lemma_num_in_range_small(c as int, *scale as nat);
                }
                Ok(Ok(EVal::Num { coeff: c, scale: *scale }))
            },
            _ => Ok(Err(SqlError::TypeError)),
        },
        _ => Ok(Err(SqlError::TypeError)),
    }
}

/// `spec::scalar::cast` (never leaves the executable domain).
pub fn cast_exec(op: CastOp, a: &EVal) -> (r: Result<EVal, SqlError>)
    ensures view_result(r) == cast(op, a@),
{
    match (op, a) {
        (_, EVal::Null) => Ok(EVal::Null),
        (CastOp::Int4ToInt8, EVal::Int(x)) => Ok(EVal::Int(*x)),
        (CastOp::IntToNumeric, EVal::Int(x)) => Ok(EVal::Num { coeff: *x as i128, scale: 0 }),
        (CastOp::DateToTimestamp, EVal::Date(d)) => match date_to_ts_exec(*d) {
            Ok(t) => Ok(EVal::Ts(t)),
            Err(e) => Err(e),
        },
        _ => Err(SqlError::TypeError),
    }
}

/// `spec::scalar::add_interval` on a timestamp value of PostgreSQL's range (every `EVal::Ts` produced by the
/// evaluator is; input timestamps are checked by `db_wf`).
pub fn add_interval_exec(a: &EVal, months: i32, days: i32, micros: i64) -> (r: Result<EVal, SqlError>)
    requires a@ matches Val::Ts(t) ==> ts_valid(t),
    ensures view_result(r) == add_interval(a@, months, days, micros),
{
    match a {
        EVal::Null => Ok(EVal::Null),
        EVal::Ts(t) => match ts_add_interval_exec(*t, months, days, micros) {
            Ok(x) => Ok(EVal::Ts(x)),
            Err(e) => Err(e),
        },
        _ => Err(SqlError::TypeError),
    }
}

/// `spec::scalar::compare` (exact, never leaves the executable domain). A date compares with a timestamp as its
/// midnight in microseconds, computed in `i128` (`spec::datetime::date_as_usecs`; `86_400_000_000` is
/// `USECS_PER_DAY` as a literal, see `exec::datetime`).
pub fn compare_exec(a: &EVal, b: &EVal) -> (r: Option<i8>)
    ensures
        match r {
            Some(c) => compare(a@, b@) == Some(c as int),
            None => compare(a@, b@) is None,
        },
{
    match (a, b) {
        (EVal::Bool(x), EVal::Bool(y)) => Some(if *x == *y { 0 } else if !*x { -1 } else { 1 }),
        (EVal::Int(x), EVal::Int(y)) => Some(three_way_cmp(*x as i128, *y as i128)),
        (EVal::Int(x), EVal::Num { coeff, scale }) => Some(num_cmp_exec(*x as i128, 0, *coeff, *scale)),
        (EVal::Num { coeff, scale }, EVal::Int(y)) => Some(num_cmp_exec(*coeff, *scale, *y as i128, 0)),
        (EVal::Num { coeff: c1, scale: s1 }, EVal::Num { coeff: c2, scale: s2 }) => Some(num_cmp_exec(*c1, *s1, *c2, *s2)),
        (EVal::Date(x), EVal::Date(y)) => Some(three_way_cmp(*x as i128, *y as i128)),
        (EVal::Date(x), EVal::Ts(t)) => Some(three_way_cmp(*x as i128 * 86_400_000_000i128, *t as i128)),
        (EVal::Ts(t), EVal::Date(y)) => Some(three_way_cmp(*t as i128, *y as i128 * 86_400_000_000i128)),
        (EVal::Ts(t), EVal::Ts(u)) => Some(three_way_cmp(*t as i128, *u as i128)),
        (EVal::Text(x), EVal::Text(y)) => Some(lex_cmp_exec(x, y)),
        _ => None,
    }
}

/// `spec::scalar::cmp_holds`.
pub fn cmp_holds_exec(op: CmpOp, c: i8) -> (r: bool)
    ensures r == cmp_holds(op, c as int),
{
    match op {
        CmpOp::Eq => c == 0,
        CmpOp::Ne => c != 0,
        CmpOp::Lt => c < 0,
        CmpOp::Le => c <= 0,
        CmpOp::Gt => c > 0,
        CmpOp::Ge => c >= 0,
    }
}

/// `spec::value::truth_of`.
pub fn truth_of_exec(b: bool) -> (r: Truth)
    ensures r == truth_of(b),
{
    if b { Truth::True } else { Truth::False }
}

/// `spec::scalar::cmp_truth`.
pub fn cmp_truth_exec(op: CmpOp, a: &EVal, b: &EVal) -> (r: Result<Truth, SqlError>)
    ensures r == cmp_truth(op, a@, b@),
{
    if matches!(a, EVal::Null) || matches!(b, EVal::Null) {
        Ok(Truth::Unknown)
    } else {
        match compare_exec(a, b) {
            Some(c) => Ok(truth_of_exec(cmp_holds_exec(op, c))),
            None => Err(SqlError::TypeError),
        }
    }
}

/// `spec::scalar::truth_of_val`.
pub fn truth_of_val_exec(a: &EVal) -> (r: Result<Truth, SqlError>)
    ensures r == truth_of_val(a@),
{
    match a {
        EVal::Null => Ok(Truth::Unknown),
        EVal::Bool(b) => Ok(truth_of_exec(*b)),
        _ => Err(SqlError::TypeError),
    }
}

/// `spec::value::truth_and` (three-valued AND).
pub fn truth_and_exec(a: Truth, b: Truth) -> (r: Truth)
    ensures r == truth_and(a, b),
{
    match (a, b) {
        (Truth::False, _) | (_, Truth::False) => Truth::False,
        (Truth::True, Truth::True) => Truth::True,
        _ => Truth::Unknown,
    }
}

/// `spec::value::truth_or` (three-valued OR).
pub fn truth_or_exec(a: Truth, b: Truth) -> (r: Truth)
    ensures r == truth_or(a, b),
{
    match (a, b) {
        (Truth::True, _) | (_, Truth::True) => Truth::True,
        (Truth::False, Truth::False) => Truth::False,
        _ => Truth::Unknown,
    }
}

/// `spec::value::truth_not` (three-valued NOT).
pub fn truth_not_exec(a: Truth) -> (r: Truth)
    ensures r == truth_not(a),
{
    match a {
        Truth::True => Truth::False,
        Truth::False => Truth::True,
        Truth::Unknown => Truth::Unknown,
    }
}

} // verus!
