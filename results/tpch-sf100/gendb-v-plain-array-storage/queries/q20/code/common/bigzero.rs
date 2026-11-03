//! Zeroed worker output buffers that the allocator always maps fresh: each holds more than 32 MiB (the largest
//! threshold of glibc's dynamic mmap threshold), so it is never carved out of recycled heap memory, `calloc` needs no
//! clearing, and only the pages a worker writes cost anything. A buffer is at least the requested length.
use vstd::prelude::*;

verus! {

/// Elements of 8 bytes in a buffer of just over 32 MiB.
pub const BIG8: usize = 4_200_000;
/// Elements of 4 bytes in a buffer of just over 32 MiB.
pub const BIG4: usize = 8_400_000;
/// Elements of 16 bytes in a buffer of just over 32 MiB.
pub const BIG16: usize = 2_100_000;
/// Elements of 1 byte in a buffer of just over 32 MiB.
pub const BIG1: usize = 33_600_000;

/// At least `n` zero `i64`s (at least `BIG8`).
pub fn zeroed_i64(n: usize) -> (v: Vec<i64>)
    ensures v@.len() >= n,
{
    let len = if n > BIG8 { n } else { BIG8 };
    vec![0i64; len]
}

/// At least `n` zero `u32`s (at least `BIG4`).
pub fn zeroed_u32(n: usize) -> (v: Vec<u32>)
    ensures v@.len() >= n,
{
    let len = if n > BIG4 { n } else { BIG4 };
    vec![0u32; len]
}

/// At least `n` zero `u64`s (at least `BIG8`).
pub fn zeroed_u64(n: usize) -> (v: Vec<u64>)
    ensures v@.len() >= n,
{
    let len = if n > BIG8 { n } else { BIG8 };
    vec![0u64; len]
}

/// At least `n` zero `usize`s (at least `BIG8`).
pub fn zeroed_usize(n: usize) -> (v: Vec<usize>)
    ensures v@.len() >= n,
{
    let len = if n > BIG8 { n } else { BIG8 };
    vec![0usize; len]
}

/// At least `n` zero `i128`s (at least `BIG16`).
pub fn zeroed_i128(n: usize) -> (v: Vec<i128>)
    ensures v@.len() >= n,
{
    let len = if n > BIG16 { n } else { BIG16 };
    vec![0i128; len]
}

/// At least `n` `false`s (at least `BIG1`).
pub fn zeroed_bool(n: usize) -> (v: Vec<bool>)
    ensures v@.len() >= n,
{
    let len = if n > BIG1 { n } else { BIG1 };
    vec![false; len]
}

} // verus!
