//! Type soundness of `spec::aggs::distinct` (dispatched from `bridge::typing::lemma_agg_family`). The value arm
//! `agg_value(inner, distinct_vals(vs))` is covered by the dispatcher (the distinct values are argument values,
//! `bridge::relation::lemma_distinct_vals_sub`); this module relates the result type to the inner aggregate's type.
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::ast::*;
use crate::spec::typing::*;
use crate::spec::aggs::distinct::*;

verus! {

/// `DistinctAgg(inner)` has the inner aggregate's type `t`, so it keeps its comparison family.
pub proof fn lemma_distinct_agg_ty_family(inner: Agg, t: ColTy)
    requires distinct_agg_ty(inner, t) is Some,
    ensures family(distinct_agg_ty(inner, t)->0.ty) == family(t.ty),
{
}

} // verus!
