//! Type soundness of `spec::aggs::minmax` (dispatched from `bridge::typing::lemma_agg_family`):
//! the extremum is NULL or one of the argument values, and the result type is the argument type.
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::aggs::minmax::*;
use crate::bridge::typing::*;

verus! {

/// The extremum is NULL or an argument value.
pub proof fn lemma_extremum_member(max: bool, vs: Seq<Val>)
    requires extremum(max, vs) is Ok,
    ensures ({
        let r = extremum(max, vs)->Ok_0;
        r is Null || exists|i: int| 0 <= i < vs.len() && vs[i] == r
    }),
    decreases vs.len(),
{
    // `extremum` folds from the left: the extremum of the prefix is NULL or a prefix value, and one step keeps
    // it or takes the last value.
    if vs.len() > 0 {
        let init = vs.drop_last();
        lemma_extremum_member(max, init);
        let acc = extremum(max, init)->Ok_0;
        if !(acc is Null) {
            let i = choose|i: int| 0 <= i < init.len() && init[i] == acc;
            assert(vs[i] == acc);
        }
        assert(vs[vs.len() - 1] == vs.last());
    }
}

/// MIN and MAX share `extremum`; the result is NULL or the argument value that `lemma_extremum_member` names.
pub proof fn lemma_extremum_family(max: bool, t: ColTy, vs: Seq<Val>)
    requires
        minmax_ty(t) is Some,
        extremum(max, vs) is Ok,
        forall|i: int| 0 <= i < vs.len() ==> val_has_family(#[trigger] vs[i], t.ty),
    ensures
        val_has_family(extremum(max, vs)->Ok_0, minmax_ty(t)->0.ty),
{
    lemma_extremum_member(max, vs);
    let r = extremum(max, vs)->Ok_0;
    if !(r is Null) {
        let i = choose|i: int| 0 <= i < vs.len() && vs[i] == r;
        assert(val_has_family(vs[i], t.ty));
    }
}

/// MIN over argument values of static type `t`.
pub proof fn lemma_min_family(t: ColTy, vs: Seq<Val>)
    requires
        minmax_ty(t) is Some,
        min_value(vs) is Ok,
        forall|i: int| 0 <= i < vs.len() ==> val_has_family(#[trigger] vs[i], t.ty),
    ensures
        val_has_family(min_value(vs)->Ok_0, minmax_ty(t)->0.ty),
{
    lemma_extremum_family(false, t, vs);
}

/// MAX over argument values of static type `t`.
pub proof fn lemma_max_family(t: ColTy, vs: Seq<Val>)
    requires
        minmax_ty(t) is Some,
        max_value(vs) is Ok,
        forall|i: int| 0 <= i < vs.len() ==> val_has_family(#[trigger] vs[i], t.ty),
    ensures
        val_has_family(max_value(vs)->Ok_0, minmax_ty(t)->0.ty),
{
    lemma_extremum_family(true, t, vs);
}

} // verus!
