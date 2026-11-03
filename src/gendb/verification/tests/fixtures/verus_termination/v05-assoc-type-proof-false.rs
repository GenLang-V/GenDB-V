// Soundness probe v05 (pinned Verus, rust_verify --no-cheating with the admission flags): verified (4 verified, 0 errors): proof code proves false through a bound on an associated type (Verus PR #3063); its runtime form r1 returned add_one(5) == 0.
// Input of the author-source scan tests (tests/verus_author_freeze.rs); never compiled here.
use vstd::prelude::*;
verus! {
// Recursion through an associated type bound: S: T is needed by X: Fam, used by call::<X>() inside S::m.
pub trait T {
    proof fn m(tracked &self)
        ensures false;
}
pub trait Fam {
    type A: T;
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
