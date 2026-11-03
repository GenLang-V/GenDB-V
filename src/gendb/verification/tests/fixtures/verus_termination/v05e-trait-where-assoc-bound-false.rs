// Soundness probe v05e (pinned Verus, rust_verify --no-cheating with the admission flags): verified (4 verified, 0 errors): proof code proves false through a trait-level where bound on an associated type.
// Input of the author-source scan tests (tests/verus_author_freeze.rs); never compiled here.
use vstd::prelude::*;
verus! {
// Bound on an associated type through a supertrait-style trait-level where clause.
pub trait T {
    proof fn m(tracked &self)
        ensures false;
}
pub trait Fam where Self::A: T {
    type A;
    proof fn get() -> (tracked a: Self::A);
}
pub struct S;
pub struct X;
impl Fam for X {
    type A = S;
    proof fn get() -> (tracked a: S) {
        S
    }
}
pub proof fn call<F: Fam>()
    ensures false,
{
    let tracked a = F::get();
    a.m();
}
impl T for S {
    proof fn m(tracked &self) {
        call::<X>();
    }
}
pub proof fn test()
    ensures false,
{
    call::<X>();
}
} // verus!
