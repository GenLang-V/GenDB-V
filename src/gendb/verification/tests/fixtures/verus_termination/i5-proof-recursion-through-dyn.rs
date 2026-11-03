// Termination probe i5 (pinned Verus, rust_verify --no-cheating with the admission flags): verified (3 verified, 0 errors): proof code proves false.
// Input of the author-source scan tests (verification/src/verus/refusal.rs, tests/verus_toolchain.rs, tests/verus_author_freeze.rs); never compiled here.
use vstd::prelude::*;
verus! {
// Proof-mode analogue of h5: if admitted, `false` is proved in ghost code.
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
pub proof fn test()
    ensures false,
{
    let tracked s = S;
    call_dyn(&s);
}
} // verus!
