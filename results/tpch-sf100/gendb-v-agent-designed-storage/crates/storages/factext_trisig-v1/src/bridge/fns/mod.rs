//! Proofs about the leaf scalar functions (`spec::fns`), one module per feature as in `spec::fns`. The
//! dispatcher `lemma_fn_family` (type soundness: a typed call's value lies in the comparison family of its static
//! type) is called by `bridge::typing::lemma_expr_family` for `Expr::Call`; each feature module proves its arm
//! and any facts the executable evaluator needs about its definition (`div`, `like`, `substring`).
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::fns::*;
use crate::bridge::typing::*;

pub mod div;
pub mod like;
pub mod substring;
pub mod extract;
pub mod pad;

verus! {

pub proof fn lemma_fn_family(f: ScalarFn, tys: Seq<ColTy>, vs: Seq<Val>)
    requires
        row_typed(vs, tys),
        type_fn(f, tys) is Some,
        apply_fn(f, vs) is Ok,
    ensures
        val_has_family(apply_fn(f, vs)->Ok_0, type_fn(f, tys)->0.ty),
{
    match f {
        ScalarFn::DivInt4 | ScalarFn::DivInt8 | ScalarFn::DivNumeric => div::lemma_div_family(f, tys, vs),
        ScalarFn::Like => like::lemma_like_family(f, tys, vs),
        ScalarFn::Substring2 | ScalarFn::Substring3 => substring::lemma_substring_family(f, tys, vs),
        ScalarFn::ExtractYear | ScalarFn::ExtractMonth | ScalarFn::ExtractDay => extract::lemma_extract_family(f, tys, vs),
        ScalarFn::PadBpchar => pad::lemma_pad_family(f, tys, vs),
    }
}

} // verus!
