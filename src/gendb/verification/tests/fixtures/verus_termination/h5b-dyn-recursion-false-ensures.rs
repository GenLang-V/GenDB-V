// Termination probe h5b (pinned Verus, rust_verify --no-cheating with the admission flags): verified (3 verified, 0 errors); entry() ran until killed.
// Input of the author-source scan tests (verification/src/verus/refusal.rs, tests/verus_toolchain.rs, tests/verus_author_freeze.rs); never compiled here.
use vstd::prelude::*;
verus! {
// Recursion through a trait object, with a postcondition no returning call could meet.
pub trait T {
    fn m(&self, n: u64) -> (r: u64)
        ensures r == n + 1 && r == n + 2;
}
pub struct S;
pub fn call_dyn(a: &dyn T, n: u64) -> (r: u64)
    ensures r == n + 1 && r == n + 2,
{
    a.m(n)
}
impl T for S {
    fn m(&self, n: u64) -> (r: u64) {
        call_dyn(self, n)
    }
}
pub fn entry(n: u64) -> (r: u64)
    ensures false,
{
    let s = S;
    call_dyn(&s, n)
}
} // verus!
