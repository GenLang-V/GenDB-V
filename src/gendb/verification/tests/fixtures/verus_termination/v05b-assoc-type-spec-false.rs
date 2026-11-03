// Soundness probe v05b (pinned Verus, rust_verify --no-cheating with the admission flags): verified (1 verified, 0 errors): spec code proves S.f() == S.f() + 1 through a bound on an associated type.
// Input of the author-source scan tests (tests/verus_author_freeze.rs); never compiled here.
use vstd::prelude::*;
verus! {
// Spec-mode analogue of v05 (i6 shape without dyn): if admitted, S.f() == S.f() + 1.
pub trait T {
    spec fn f(&self) -> int;
}
pub trait Fam {
    type A: T;
    spec fn get() -> Self::A;
}
pub struct S;
pub struct X;
impl Fam for X {
    type A = S;
    open spec fn get() -> S {
        S
    }
}
pub open spec fn call<F: Fam>() -> int {
    F::get().f() + 1
}
impl T for S {
    open spec fn f(&self) -> int {
        call::<X>()
    }
}
pub proof fn test()
    ensures false,
{
    let s = S;
    assert(s.f() == call::<X>());
    assert(call::<X>() == X::get().f() + 1);
    assert(X::get() == s);
}
} // verus!
