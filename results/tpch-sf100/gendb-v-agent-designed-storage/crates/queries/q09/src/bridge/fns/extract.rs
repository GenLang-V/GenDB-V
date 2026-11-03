//! Proofs about `spec::fns::extract`: type soundness (dispatched from `bridge::fns::lemma_fn_family`).
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::fns::extract::*;
use crate::bridge::typing::*;

verus! {

/// Type soundness of `extract`: a value is NULL or a number (numeric, scale 0).
pub proof fn lemma_extract_family(f: ScalarFn, tys: Seq<ColTy>, vs: Seq<Val>)
    requires
        row_typed(vs, tys),
        type_extract(f, tys) is Some,
        apply_extract(f, vs) is Ok,
    ensures
        val_has_family(apply_extract(f, vs)->Ok_0, type_extract(f, tys)->0.ty),
{
    let v = apply_extract(f, vs)->Ok_0;
    assert(v is Null || v is Num);
}

} // verus!
