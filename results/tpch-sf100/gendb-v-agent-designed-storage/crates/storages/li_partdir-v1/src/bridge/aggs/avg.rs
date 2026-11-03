//! Type soundness of `spec::aggs::avg` (dispatched from `bridge::typing::lemma_agg_family`).
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::aggs::avg::*;
use crate::bridge::typing::*;

verus! {

/// AVG over argument values of static type `t` is NULL or a numeric, the family of its result type
/// (`numeric`, bound 1000), whatever the argument values.
pub proof fn lemma_avg_family(kind: NumKind, t: ColTy, vs: Seq<Val>)
    requires
        avg_ty(kind, t) is Some,
        avg_value(kind, vs) is Ok,
    ensures
        val_has_family(avg_value(kind, vs)->Ok_0, avg_ty(kind, t)->0.ty),
{
    let v = avg_value(kind, vs)->Ok_0;
    assert(v is Null || v is Num);
}

} // verus!
