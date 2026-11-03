//! MIN / MAX over the argument values of a group, as PostgreSQL 18 (`pg_aggregate.dat`: `int4smaller`,
//! `int8smaller`, `numeric_smaller`, `date_smaller`, `timestamp_smaller`, `text_smaller`, `bpchar_smaller` and the
//! `larger` counterparts).
//!
//! NULLs are ignored; no non-NULL value gives NULL. Otherwise the extreme value in `compare` order (numerics by
//! value, text bytewise in C collation, dates and timestamps on one time line). The result is one of the
//! argument values, so it keeps its own numeric display scale; among equal extreme values the first occurrence
//! is kept (reference choice R1, VERUS_SQL_COVERAGE design §3.4: PostgreSQL's transition keeps the later of two
//! equal values and its row order depends on the plan, so it may show another equal-valued numeric scale;
//! deviation D2). There is no boolean MIN/MAX (PostgreSQL has none): the type is refused and a boolean argument
//! value is ill-typed.
//! No executable-domain predicate is needed: the result is an argument value (never `Capacity`).
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::scalar::*;

verus! {

/// Result type of `MIN`/`MAX` over an argument of type `t`: the argument type (numerics keep their scale
/// bound), nullable; boolean is refused.
pub open spec fn minmax_ty(t: ColTy) -> Option<ColTy> {
    match t.ty {
        ScalarTy::Bool => None,
        _ => Some(ColTy { ty: t.ty, nullable: true }),
    }
}

/// `c` (the order of a new value against the running extremum) makes the new value the extremum: strictly
/// larger for MAX, strictly smaller for MIN (so the first of equal values stays).
pub open spec fn extremum_better(max: bool, c: int) -> bool {
    if max { c > 0 } else { c < 0 }
}

/// One step of the running extremum `acc` (NULL while no non-NULL value was seen) with the next value `v`.
pub open spec fn extremum_step(max: bool, acc: Val, v: Val) -> Result<Val, SqlError> {
    if v is Null {
        Ok(acc)
    } else if v is Bool {
        Err(SqlError::TypeError)
    } else if acc is Null {
        Ok(v)
    } else {
        match compare(v, acc) {
            Some(c) => if extremum_better(max, c) { Ok(v) } else { Ok(acc) },
            None => Err(SqlError::TypeError),
        }
    }
}

/// The extremum of `vs` in row order (`max`: MAX, otherwise MIN); an ill-typed value stops it.
pub open spec fn extremum(max: bool, vs: Seq<Val>) -> Result<Val, SqlError>
    decreases vs.len(),
{
    if vs.len() == 0 {
        Ok(Val::Null)
    } else {
        match extremum(max, vs.drop_last()) {
            Ok(acc) => extremum_step(max, acc, vs.last()),
            Err(e) => Err(e),
        }
    }
}

/// Values of `MIN` and `MAX` over the argument values of a group.
pub open spec fn min_value(vs: Seq<Val>) -> Result<Val, SqlError> {
    extremum(false, vs)
}

pub open spec fn max_value(vs: Seq<Val>) -> Result<Val, SqlError> {
    extremum(true, vs)
}

} // verus!
