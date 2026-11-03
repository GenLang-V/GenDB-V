// Soundness probe v22 (pinned Verus, rust_verify --no-cheating with the admission flags): verified (3 verified, 0 errors): proof code proves false through std's IntoIterator::IntoIter: Iterator bound, no author trait (Verus PR #3063); its runtime form r5 returned add_one(5) == 0.
// Input of the author-source scan tests (tests/verus_author_freeze.rs); never compiled here.
use vstd::prelude::*;
use vstd::std_specs::iter::IteratorSpec;
verus! {
// v05b through a std trait with a bounded associated type (IntoIterator::IntoIter: Iterator), no author trait.
pub struct S {
    pub x: u64,
}
pub struct X {
    pub x: u64,
}
impl Iterator for S {
    type Item = u64;
    fn next(&mut self) -> (r: Option<u64>) {
        None
    }
}
pub open spec fn g<Y: IntoIterator>(it: Y::IntoIter) -> int {
    match it.decrease() {
        Some(n) => n as int,
        None => 0,
    }
}
impl vstd::std_specs::iter::IteratorSpecImpl for S {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool { false }
    open spec fn remaining(&self) -> Seq<u64> { Seq::empty() }
    open spec fn will_return_none(&self) -> bool { true }
    open spec fn decrease(&self) -> Option<nat> {
        Some((if g::<X>(*self) >= 0 { g::<X>(*self) + 1 } else { 0 }) as nat)
    }
    open spec fn peek(&self, index: int) -> Option<u64> { None }
}
impl IntoIterator for X {
    type Item = u64;
    type IntoIter = S;
    fn into_iter(self) -> S {
        S { x: self.x }
    }
}
pub proof fn test(s: S)
    ensures false,
{
    assert(g::<X>(s) >= 0);
    assert(s.decrease() == Some((g::<X>(s) + 1) as nat));
    assert(g::<X>(s) == g::<X>(s) + 1);
}
} // verus!
