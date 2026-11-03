//! Machine values with their view onto `spec::value::Val`, rows, and the outcome type of executable operators
//! (value, SQL error or `Capacity`).
use vstd::prelude::*;
use crate::spec::value::*;

verus! {

/// Machine representation of a SQL value. `Int` holds int4/int8 values; `Num` a decimal whose coefficient
/// and scale fit `i128`/`u32` (the executable domain, `exec::domain`); `Date`/`Ts` are PostgreSQL's
/// `DateADT`/`Timestamp` (days / microseconds since 2000-01-01), which fit `i32`/`i64` over their whole range.
pub enum EVal {
    Null,
    Bool(bool),
    Int(i64),
    Num { coeff: i128, scale: u32 },
    Date(i32),
    Ts(i64),
    Text(Vec<u8>),
}

impl View for EVal {
    type V = Val;

    open spec fn view(&self) -> Val {
        match self {
            EVal::Null => Val::Null,
            EVal::Bool(b) => Val::Bool(*b),
            EVal::Int(x) => Val::Int(*x as int),
            EVal::Num { coeff, scale } => Val::Num { coeff: *coeff as int, scale: *scale as nat },
            EVal::Date(d) => Val::Date(*d as int),
            EVal::Ts(t) => Val::Ts(*t as int),
            EVal::Text(b) => Val::Text(b@),
        }
    }
}

/// A row: values in column order.
pub type ERow = Vec<EVal>;

pub open spec fn view_row(r: Seq<EVal>) -> Row {
    r.map_values(|v: EVal| v@)
}

/// Refusal of the finite executable domain. Every function returning it proves that a concrete exact
/// intermediate of the evaluation lies outside the machine representation (its `exec::domain` predicate is
/// false), and returns a result whenever that predicate holds. It is never a SQL outcome.
pub struct Capacity;

/// SQL result of an executable operator: `Ok(Ok(v))` value, `Ok(Err(e))` SQL error, `Err(Capacity)`.
pub type Outcome<T> = Result<Result<T, SqlError>, Capacity>;

pub open spec fn view_result(r: Result<EVal, SqlError>) -> Result<Val, SqlError> {
    match r {
        Ok(v) => Ok(v@),
        Err(e) => Err(e),
    }
}

/// A copy of `v` with the same view (`Text` bytes are copied).
pub fn clone_val(v: &EVal) -> (r: EVal)
    ensures r@ == v@,
{
    match v {
        EVal::Null => EVal::Null,
        EVal::Bool(b) => EVal::Bool(*b),
        EVal::Int(x) => EVal::Int(*x),
        EVal::Num { coeff, scale } => EVal::Num { coeff: *coeff, scale: *scale },
        EVal::Date(d) => EVal::Date(*d),
        EVal::Ts(t) => EVal::Ts(*t),
        EVal::Text(b) => EVal::Text(b.clone()),
    }
}

} // verus!
