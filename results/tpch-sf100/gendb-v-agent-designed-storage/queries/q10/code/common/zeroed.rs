//! Zero-filled vectors on fresh pages: a request is rounded up to more than 32 MiB, glibc's largest dynamic mmap
//! threshold, so the allocator maps fresh zero pages (no clearing on the calling thread; each page is touched first
//! by the thread that writes it) instead of clearing recycled heap memory.
use vstd::prelude::*;

verus! {

/// Elements of 8 bytes in a request above 32 MiB.
pub const MIN_8: usize = 4_194_305;
/// Elements of 4 bytes in a request above 32 MiB.
pub const MIN_4: usize = 8_388_609;
/// Elements of 1 byte in a request above 32 MiB.
pub const MIN_1: usize = 33_554_433;

/// At least `n` zero `i64`s.
pub fn zeroed_i64(n: usize) -> (v: Vec<i64>)
    ensures v@.len() >= n, forall|i: int| 0 <= i < v@.len() ==> #[trigger] v@[i] == 0,
{
    let len = if n < MIN_8 { MIN_8 } else { n };
    let v = vec![0i64; len];
    v
}

/// At least `n` zero `u64`s.
pub fn zeroed_u64(n: usize) -> (v: Vec<u64>)
    ensures v@.len() >= n, forall|i: int| 0 <= i < v@.len() ==> #[trigger] v@[i] == 0,
{
    let len = if n < MIN_8 { MIN_8 } else { n };
    let v = vec![0u64; len];
    v
}

/// At least `n` zero `u32`s.
pub fn zeroed_u32(n: usize) -> (v: Vec<u32>)
    ensures v@.len() >= n, forall|i: int| 0 <= i < v@.len() ==> #[trigger] v@[i] == 0,
{
    let len = if n < MIN_4 { MIN_4 } else { n };
    let v = vec![0u32; len];
    v
}

/// At least `n` zero `u8`s.
pub fn zeroed_u8(n: usize) -> (v: Vec<u8>)
    ensures v@.len() >= n, forall|i: int| 0 <= i < v@.len() ==> #[trigger] v@[i] == 0,
{
    let len = if n < MIN_1 { MIN_1 } else { n };
    let v = vec![0u8; len];
    v
}

} // verus!
