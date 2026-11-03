// Soundness probe v05d (pinned Verus, rust_verify --no-cheating with the admission flags): verified (4 verified, 0 errors): exec recursion through a bound on an associated type, with an ensures no returning call can meet.
// Input of the author-source scan tests (tests/verus_author_freeze.rs); never compiled here.
use vstd::prelude::*;
verus! {
// Exec-mode analogue of v05 (h5b shape without dyn): verifies only if the cycle is missed; would never return.
pub trait T {
    fn m(&self, n: u64) -> (r: u64)
        ensures r == n + 1 && r == n + 2;
}
pub trait Fam {
    type A: T;
    fn get() -> Self::A;
}
pub struct S;
pub struct X;
impl Fam for X {
    type A = S;
    fn get() -> S {
        S
    }
}
pub fn call<F: Fam>(n: u64) -> (r: u64)
    ensures r == n + 1 && r == n + 2,
{
    let a = F::get();
    a.m(n)
}
impl T for S {
    fn m(&self, n: u64) -> (r: u64) {
        call::<X>(n)
    }
}
pub fn entry(n: u64) -> (r: u64)
    ensures false,
{
    call::<X>(n)
}
} // verus!
