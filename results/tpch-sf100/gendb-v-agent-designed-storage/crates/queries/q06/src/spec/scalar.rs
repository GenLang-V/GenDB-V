//! Value-level SQL operators of the fragment. Every operator is monomorphic after resolution (the AST node
//! names its operand type); NULL operands give NULL (strict operators) or `Unknown` (comparisons).
//! Ill-typed operand values give `SqlError::TypeError` (unreachable for checked ASTs).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::datetime::*;
use crate::spec::text::*;

verus! {

/// Binary arithmetic operators (division is the scalar function `spec::fns::div`).
#[derive(Clone, Copy)]
pub enum ArithOp {
    Add,
    Sub,
    Mul,
}

/// Operand/result type of an arithmetic operator: `int4 op int4 -> int4`, `int8 op int8 -> int8`,
/// `numeric op numeric -> numeric` (PostgreSQL `int4pl`, `int8mul`, `numeric_add`, ...).
#[derive(Clone, Copy)]
pub enum NumKind {
    Int4,
    Int8,
    Numeric,
}

/// Comparison operators (`=`, `<>`, `<`, `<=`, `>`, `>=`).
#[derive(Clone, Copy)]
pub enum CmpOp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

/// Casts of the core fragment (inserted by the resolver where PostgreSQL applies them implicitly).
#[derive(Clone, Copy)]
pub enum CastOp {
    /// `int4 -> int8` (value unchanged).
    Int4ToInt8,
    /// `int4/int8 -> numeric` (exact, scale 0).
    IntToNumeric,
    /// `date -> timestamp` (midnight; 22008 past the timestamp range).
    DateToTimestamp,
}

/// Integer type of an integer operator kind (`arith` and `neg` refuse `Numeric` integer operands before
/// asking).
pub open spec fn int_kind_of(k: NumKind) -> IntKind {
    match k {
        NumKind::Int8 => IntKind::Int8,
        _ => IntKind::Int4,
    }
}

/// Exact integer `a op b` (the range check is `int_result`).
pub open spec fn int_arith(op: ArithOp, a: int, b: int) -> int {
    match op {
        ArithOp::Add => a + b,
        ArithOp::Sub => a - b,
        ArithOp::Mul => a * b,
    }
}

/// Exact numeric operator: result coefficient and scale.
pub open spec fn num_arith(op: ArithOp, c1: int, s1: nat, c2: int, s2: nat) -> (int, nat) {
    match op {
        ArithOp::Add => (num_add_coeff(c1, s1, c2, s2), max_nat(s1, s2)),
        ArithOp::Sub => (num_sub_coeff(c1, s1, c2, s2), max_nat(s1, s2)),
        ArithOp::Mul => (c1 * c2, s1 + s2),
    }
}

/// `a op b` at operand type `kind`.
pub open spec fn arith(op: ArithOp, kind: NumKind, a: Val, b: Val) -> Result<Val, SqlError> {
    match (a, b) {
        (Val::Null, Val::Null) => Ok(Val::Null),
        (Val::Null, Val::Int(_)) => Ok(Val::Null),
        (Val::Int(_), Val::Null) => Ok(Val::Null),
        (Val::Null, Val::Num { .. }) => Ok(Val::Null),
        (Val::Num { .. }, Val::Null) => Ok(Val::Null),
        (Val::Int(x), Val::Int(y)) => match kind {
            NumKind::Numeric => Err(SqlError::TypeError),
            _ => int_result(int_kind_of(kind), int_arith(op, x, y)),
        },
        (Val::Num { coeff: c1, scale: s1 }, Val::Num { coeff: c2, scale: s2 }) => match kind {
            NumKind::Numeric => {
                let r = num_arith(op, c1, s1, c2, s2);
                num_result(r.0, r.1)
            },
            _ => Err(SqlError::TypeError),
        },
        _ => Err(SqlError::TypeError),
    }
}

/// Unary minus at type `kind` (`-int4min` is 22003).
pub open spec fn neg(kind: NumKind, a: Val) -> Result<Val, SqlError> {
    match a {
        Val::Null => Ok(Val::Null),
        Val::Int(x) => match kind {
            NumKind::Numeric => Err(SqlError::TypeError),
            _ => int_result(int_kind_of(kind), -x),
        },
        Val::Num { coeff, scale } => match kind {
            NumKind::Numeric => num_result(-coeff, scale),
            _ => Err(SqlError::TypeError),
        },
        _ => Err(SqlError::TypeError),
    }
}

/// Value of a cast (strict: NULL stays NULL).
pub open spec fn cast(op: CastOp, a: Val) -> Result<Val, SqlError> {
    match (op, a) {
        (_, Val::Null) => Ok(Val::Null),
        (CastOp::Int4ToInt8, Val::Int(x)) => Ok(Val::Int(x)),
        (CastOp::IntToNumeric, Val::Int(x)) => Ok(Val::Num { coeff: x, scale: 0 }),
        (CastOp::DateToTimestamp, Val::Date(d)) => match date_to_ts(d) {
            Ok(t) => Ok(Val::Ts(t)),
            Err(e) => Err(e),
        },
        _ => Err(SqlError::TypeError),
    }
}

/// `timestamp + interval` (the resolver casts a `date` operand to `timestamp` and negates for `-`).
pub open spec fn add_interval(a: Val, months: i32, days: i32, micros: i64) -> Result<Val, SqlError> {
    match a {
        Val::Null => Ok(Val::Null),
        Val::Ts(t) => match ts_add_interval(t, months as int, days as int, micros as int) {
            Ok(r) => Ok(Val::Ts(r)),
            Err(e) => Err(e),
        },
        _ => Err(SqlError::TypeError),
    }
}

/// Exact order of two non-NULL values of one comparison family: `Some(-1 | 0 | 1)`, or `None` across
/// families. Families: boolean; `int4/int8/numeric` (exact value order, as PostgreSQL's cross-type operators);
/// `date/timestamp` (exact, dates at midnight); text (bytes).
pub open spec fn compare(a: Val, b: Val) -> Option<int> {
    match (a, b) {
        (Val::Bool(x), Val::Bool(y)) => Some(if x == y { 0 } else if !x { -1 } else { 1 }),
        (Val::Int(x), Val::Int(y)) => Some(sign(x - y)),
        (Val::Int(x), Val::Num { coeff, scale }) => Some(num_cmp(x, 0, coeff, scale)),
        (Val::Num { coeff, scale }, Val::Int(y)) => Some(num_cmp(coeff, scale, y, 0)),
        (Val::Num { coeff: c1, scale: s1 }, Val::Num { coeff: c2, scale: s2 }) => Some(num_cmp(c1, s1, c2, s2)),
        (Val::Date(x), Val::Date(y)) => Some(sign(x - y)),
        (Val::Date(x), Val::Ts(t)) => Some(sign(date_as_usecs(x) - t)),
        (Val::Ts(t), Val::Date(y)) => Some(sign(t - date_as_usecs(y))),
        (Val::Ts(t), Val::Ts(u)) => Some(sign(t - u)),
        (Val::Text(x), Val::Text(y)) => Some(lex_cmp(x, y)),
        _ => None,
    }
}

/// The order `c` of two values (from `compare`) satisfies `op`.
pub open spec fn cmp_holds(op: CmpOp, c: int) -> bool {
    match op {
        CmpOp::Eq => c == 0,
        CmpOp::Ne => c != 0,
        CmpOp::Lt => c < 0,
        CmpOp::Le => c <= 0,
        CmpOp::Gt => c > 0,
        CmpOp::Ge => c >= 0,
    }
}

/// SQL comparison: `Unknown` if an operand is NULL.
pub open spec fn cmp_truth(op: CmpOp, a: Val, b: Val) -> Result<Truth, SqlError> {
    if a is Null || b is Null {
        Ok(Truth::Unknown)
    } else {
        match compare(a, b) {
            Some(c) => Ok(truth_of(cmp_holds(op, c))),
            None => Err(SqlError::TypeError),
        }
    }
}

/// A boolean value used as a condition (`WHERE flag`): NULL is `Unknown`.
pub open spec fn truth_of_val(a: Val) -> Result<Truth, SqlError> {
    match a {
        Val::Null => Ok(Truth::Unknown),
        Val::Bool(b) => Ok(truth_of(b)),
        _ => Err(SqlError::TypeError),
    }
}

} // verus!
