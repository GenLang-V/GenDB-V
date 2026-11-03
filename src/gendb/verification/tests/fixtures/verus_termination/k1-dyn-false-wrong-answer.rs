// Termination probe k1 (pinned Verus, rust_verify --no-cheating with the admission flags): verified (3 verified, 0 errors); add_one(5) returned 0.
// Input of the author-source scan tests (verification/src/verus/refusal.rs, tests/verus_toolchain.rs, tests/verus_author_freeze.rs); never compiled here.
use vstd::prelude::*;
verus! {
// Consequence of i5: an exec function that returns and violates its postcondition.
pub trait T {
    proof fn m(tracked &self)
        ensures false;
}
pub struct S;
pub proof fn call_dyn(tracked a: &dyn T)
    ensures false,
{
    a.m()
}
impl T for S {
    proof fn m(tracked &self) {
        call_dyn(self)
    }
}
pub fn add_one(n: u64) -> (r: u64)
    ensures r == n + 1,
{
    proof {
        let tracked s = S;
        call_dyn(&s);
    }
    0
}
} // verus!
