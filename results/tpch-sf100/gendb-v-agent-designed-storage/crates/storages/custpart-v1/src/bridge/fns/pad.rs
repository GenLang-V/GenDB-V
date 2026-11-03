//! Proofs about `spec::fns::pad`: type soundness (dispatched from `bridge::fns::lemma_fn_family`).
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::fns::pad::*;
use crate::bridge::typing::*;

verus! {

/// Type soundness of `pad`: a value is NULL or text.
pub proof fn lemma_pad_family(f: ScalarFn, tys: Seq<ColTy>, vs: Seq<Val>)
    requires
        row_typed(vs, tys),
        type_pad(f, tys) is Some,
        apply_pad(f, vs) is Ok,
    ensures
        val_has_family(apply_pad(f, vs)->Ok_0, type_pad(f, tys)->0.ty),
{
    let v = apply_pad(f, vs)->Ok_0;
    assert(v is Null || v is Text);
}

} // verus!
