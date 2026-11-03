//! `agg(DISTINCT x)` (`Agg::DistinctAgg`): the inner aggregate over `spec::equality::distinct_vals` (the value
//! arm in `spec::relation::agg_value` is final): the non-NULL values, one per not-distinct class (SQL value
//! equality: `1.0` and `1.00` are one value; the first occurrence represents it, reference choice R1 of the
//! VERUS_SQL_COVERAGE design).
//!
//! The inner aggregate is `COUNT`, `SUM` or `AVG`. `MIN/MAX(DISTINCT x)` is `MIN/MAX(x)` (normalized by the
//! frontend), and `COUNT(DISTINCT *)` is not SQL, so every other inner aggregate is refused. The result type is
//! the inner aggregate's type (removing duplicates changes neither the argument type nor the result type).
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::ast::*;

verus! {

/// Result type of `DistinctAgg(inner)` given the inner aggregate's type `t`.
pub open spec fn distinct_agg_ty(inner: Agg, t: ColTy) -> Option<ColTy> {
    match inner {
        Agg::Count(_) | Agg::Sum { .. } | Agg::Avg { .. } => Some(t),
        _ => None,
    }
}

} // verus!
