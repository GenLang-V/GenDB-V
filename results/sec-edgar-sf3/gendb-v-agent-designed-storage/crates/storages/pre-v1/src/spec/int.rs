//! `integer` / `bigint` semantics: exact arithmetic, then the result type's range check.
use vstd::prelude::*;
use crate::spec::limits::*;
use crate::spec::value::*;

verus! {

/// Monomorphic integer type of an integer operator (the resolver inserts `int4 -> int8` casts first).
#[derive(Clone, Copy)]
pub enum IntKind {
    Int4,
    Int8,
}

/// `v` is a value of integer type `k`.
pub open spec fn int_in_range(k: IntKind, v: int) -> bool {
    match k {
        IntKind::Int4 => int4_min() <= v <= int4_max(),
        IntKind::Int8 => int8_min() <= v <= int8_max(),
    }
}

/// An exact integer result of type `k`, or 22003 when it is outside the type.
pub open spec fn int_result(k: IntKind, v: int) -> Result<Val, SqlError> {
    if int_in_range(k, v) { Ok(Val::Int(v)) } else { Err(SqlError::NumericValueOutOfRange) }
}

} // verus!
