//! Proofs about `spec::fns::substring`: type soundness (dispatched from `bridge::fns::lemma_fn_family`) and the
//! meaning of the character range on well-behaved arguments.
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::chars::*;
use crate::spec::fns::substring::*;
use crate::bridge::typing::*;

verus! {

/// Type soundness of `substring`: a value is NULL or text.
pub proof fn lemma_substring_family(f: ScalarFn, tys: Seq<ColTy>, vs: Seq<Val>)
    requires
        row_typed(vs, tys),
        type_substring(f, tys) is Some,
        apply_substring(f, vs) is Ok,
    ensures
        val_has_family(apply_substring(f, vs)->Ok_0, type_substring(f, tys)->0.ty),
{
    let v = apply_substring(f, vs)->Ok_0;
    assert(v is Null || v is Text);
}

/// `SUBSTRING(s FROM 1)` is `s`, and so is `SUBSTRING(s FROM start FOR len)` whenever `start <= 1` and the end
/// reaches past the last character.
pub proof fn lemma_substring_whole(b: Seq<u8>, start: int, end: Option<int>)
    requires
        start <= 1,
        end matches Some(e) ==> e - 1 >= chars(b).len(),
    ensures
        char_range(chars(b), start, end) == b,
{
    let cs = chars(b);
    assert(cs.subrange(0, cs.len() as int) =~= cs);
    lemma_concat_chars(b);
}

} // verus!
