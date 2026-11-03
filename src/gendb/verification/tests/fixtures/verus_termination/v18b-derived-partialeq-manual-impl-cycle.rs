// Soundness probe v18b (pinned Verus, rust_verify --no-cheating with the admission flags): verified (2 verified, 0 errors): a derived PartialEq calls a manual PartialEq impl that compares two values of the outer type; its runtime form r4 ran until killed.
// Input of the author-source scan tests (tests/verus_author_freeze.rs); never compiled here.
use vstd::prelude::*;
verus! {
// v18 with T2 declaring that it does not obey the eq spec, so its `eq` has no postcondition to meet.
#[derive(PartialEq, Eq)]
pub struct S {
    pub t: T2,
}
pub struct T2 {
    pub v: u64,
}
impl vstd::std_specs::cmp::PartialEqSpecImpl for T2 {
    open spec fn obeys_eq_spec() -> bool { false }
    open spec fn eq_spec(&self, other: &T2) -> bool { true }
}
impl PartialEq for T2 {
    fn eq(&self, other: &T2) -> bool {
        let a = S { t: T2 { v: self.v } };
        let b = S { t: T2 { v: other.v } };
        a == b
    }
}
impl Eq for T2 {}
pub fn entry(x: u64) -> bool {
    let p = T2 { v: x };
    let q = T2 { v: x };
    p == q
}
} // verus!
