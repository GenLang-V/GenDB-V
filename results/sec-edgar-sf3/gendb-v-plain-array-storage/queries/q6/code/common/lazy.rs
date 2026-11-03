//! Lazily zeroed buffers: a vector of zeroable elements (integers, `bool`, tuples of them) allocated with more than
//! glibc's largest mmap threshold is mapped fresh, so the kernel zeroes each page at its first touch, by the worker
//! that fills it, instead of the calling thread writing every element. `fill` sets every element on that worker.
use vstd::prelude::*;

verus! {

/// Bytes above glibc's largest dynamic mmap threshold (32 MiB on 64-bit hosts).
pub const LAZY_BYTES: usize = 33554432;

/// At least `need` elements of `elem_bytes` bytes, and enough that the allocation is mapped (lazily zeroed); `need`
/// itself when it is larger than that floor.
pub fn lazy_cap(need: usize, elem_bytes: usize) -> (r: usize)
    requires 1 <= elem_bytes <= 64,
    ensures r >= need, r == need || r <= LAZY_BYTES + 4096,
{
    let floor = LAZY_BYTES / elem_bytes + 4096;
    if need > floor { need } else { floor }
}

/// Every element of `v` set to `x` (`no_unwind`: usable in worker bodies).
pub fn fill<T: Copy>(v: &mut Vec<T>, x: T)
    ensures final(v)@.len() == old(v)@.len(), forall|i: int| 0 <= i < final(v)@.len() ==> #[trigger] final(v)@[i] == x,
    no_unwind
{
    let n = v.len();
    let mut i: usize = 0;
    while i < n
        invariant n == v@.len(), i <= n, forall|j: int| 0 <= j < i ==> #[trigger] v@[j] == x,
        decreases n - i,
    {
        v[i] = x;
        i = i + 1;
    }
}

} // verus!
