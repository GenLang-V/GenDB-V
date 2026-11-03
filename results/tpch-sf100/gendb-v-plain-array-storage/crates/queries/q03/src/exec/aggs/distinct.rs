//! Executable `spec::aggs::distinct` (typing of `DistinctAgg`; its values use `exec::equality::distinct_vals_exec`).
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::aggs::distinct::*;
use crate::exec::ast::*;

verus! {

/// `spec::aggs::distinct::distinct_agg_ty`: DISTINCT is allowed on COUNT, SUM and AVG and keeps their type.
pub fn distinct_agg_ty_exec(inner: &EAgg, t: ColTy) -> (r: Option<ColTy>)
    ensures r == distinct_agg_ty(view_agg(*inner), t),
{
    match inner {
        EAgg::Count(_) | EAgg::Sum { .. } | EAgg::Avg { .. } => Some(t),
        _ => None,
    }
}

} // verus!
