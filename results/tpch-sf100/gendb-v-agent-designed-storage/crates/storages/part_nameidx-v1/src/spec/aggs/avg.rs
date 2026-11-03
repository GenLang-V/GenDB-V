//! AVG over the argument values of a group, as PostgreSQL 18 (`pg_aggregate.dat`: `int4_avg_accum`/`int8_avg`,
//! `int8_avg_accum`/`numeric_poly_avg`, `numeric_avg_accum`/`numeric_avg`).
//!
//! NULLs are ignored; no non-NULL value gives NULL. Otherwise the exact sum of the non-NULL values (integers:
//! `int_sum` at scale 0; numeric: `num_sum` at the largest input display scale, then PostgreSQL's format limit
//! 22003 on the sum) divided by the count with `numeric_div` (`spec::fns::div::num_div`, divisor at scale 0).
//! The result is `numeric` with display-scale bound 1000; its display scale depends on the magnitudes of the
//! sum and the count. The sum is exact, so the value does not depend on the row order.
//!
//! Deviation D3 of the VERUS_SQL_COVERAGE design (recorded, not tested): PostgreSQL's int4 transition adds in
//! int64 without an overflow check, so it wraps only for at least 2^32 rows; this meaning is exact. No int8 range
//! check applies to the int4 sum (that is SUM(int4)'s final type, not AVG's).
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::numeric::*;
use crate::spec::relation::*;
use crate::spec::typing::*;
use crate::spec::fns::div::*;

verus! {

/// Result type of `AVG` at operand kind `kind` over an argument of type `t`: `numeric` (bound 1000), nullable.
pub open spec fn avg_ty(kind: NumKind, t: ColTy) -> Option<ColTy> {
    if kind_accepts(kind, t.ty) {
        Some(ColTy { ty: ScalarTy::Numeric { scale: 1000 }, nullable: true })
    } else {
        None
    }
}

/// Exact sum `(coefficient, scale)` of the non-NULL values of kind `kind` (integers at scale 0).
pub open spec fn avg_sum(kind: NumKind, vs: Seq<Val>) -> (int, nat) {
    match kind {
        NumKind::Numeric => num_sum(vs),
        _ => (int_sum(vs), 0nat),
    }
}

/// Value of `AVG` over the argument values of a group.
pub open spec fn avg_value(kind: NumKind, vs: Seq<Val>) -> Result<Val, SqlError> {
    if !all_of_kind(kind, vs) {
        Err(SqlError::TypeError)
    } else if count_non_null(vs) == 0 {
        Ok(Val::Null)
    } else {
        let s = avg_sum(kind, vs);
        // `numeric_avg` makes the sum a numeric first (`make_result`); integer sums convert exactly.
        if kind is Numeric && !num_in_range(s.0, s.1) {
            Err(SqlError::NumericValueOutOfRange)
        } else {
            num_div(s.0, s.1, count_non_null(vs) as int, 0)
        }
    }
}

/// Division part of the executable domain of `avg_value` (the sum's own domain is the SUM capacity condition,
/// `exec::relational::domain::sum_mass_fits`, combined in `exec::aggs::avg::fits_avg_value`).
pub open spec fn fits_avg(kind: NumKind, vs: Seq<Val>) -> bool {
    (all_of_kind(kind, vs) && count_non_null(vs) > 0) ==> {
        let s = avg_sum(kind, vs);
        num_div_fits(s.0, s.1, count_non_null(vs) as int, 0)
    }
}

} // verus!
