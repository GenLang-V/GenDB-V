// Soundness probe v11 (pinned Verus, rust_verify --no-cheating with the admission flags): verified (2 verified, 0 errors): a Drop impl that drops a value of its own type; its runtime form r3 ran until killed.
// Input of the author-source scan tests (tests/verus_author_freeze.rs); never compiled here.
use vstd::prelude::*;
verus! {
// Implicit calls: a Drop impl whose body drops another value of the same type.
pub struct S {
    pub x: u64,
}
impl Drop for S {
    fn drop(&mut self)
        opens_invariants none
        no_unwind
    {
        let t = S { x: 0 };
    }
}
pub fn entry(n: u64) -> (r: u64)
    ensures r == n,
{
    let s = S { x: n };
    n
}
} // verus!
