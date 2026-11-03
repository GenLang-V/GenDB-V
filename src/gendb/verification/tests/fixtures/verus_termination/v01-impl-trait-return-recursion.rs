// Soundness probe v01 (pinned Verus, rust_verify --no-cheating with the admission flags): verified (3 verified, 0 errors): exec recursion through an `impl Trait` return type; its runtime form r2 ran until killed.
// Input of the author-source scan tests (tests/verus_author_freeze.rs); never compiled here.
use vstd::prelude::*;
verus! {
// Recursion through an `impl Trait` return type (opaque type) instead of `&dyn T`.
pub trait T {
    fn m(&self, n: u64) -> (r: u64)
        ensures r == n + 1 && r == n + 2;
}
pub struct S;
pub fn mk() -> impl T {
    S
}
impl T for S {
    fn m(&self, n: u64) -> (r: u64) {
        let x = mk();
        x.m(n)
    }
}
pub fn entry(n: u64) -> (r: u64)
    ensures false,
{
    let s = S;
    s.m(n)
}
} // verus!
