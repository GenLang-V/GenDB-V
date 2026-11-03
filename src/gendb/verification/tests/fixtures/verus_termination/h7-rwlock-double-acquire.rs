// Termination probe h7 (pinned Verus, rust_verify --no-cheating with the admission flags): verified (1 verified, 0 errors); deadlock() spun until killed.
// Input of the author-source scan tests (verification/src/verus/refusal.rs, tests/verus_toolchain.rs, tests/verus_author_freeze.rs); never compiled here.
use vstd::prelude::*;
use vstd::rwlock::{RwLock, RwLockPredicate};
verus! {
pub struct AnyU64;
impl RwLockPredicate<u64> for AnyU64 {
    open spec fn inv(self, v: u64) -> bool { true }
}
// The second acquire_write spins forever: vstd marks acquire_write exec_allows_no_decreases_clause.
pub fn deadlock(n: u64) -> (r: u64)
{
    let lock = RwLock::<u64, AnyU64>::new(n, Ghost(AnyU64));
    let (v1, h1) = lock.acquire_write();
    let (v2, h2) = lock.acquire_write();
    h2.release_write(v2);
    h1.release_write(v1);
    0
}
} // verus!
