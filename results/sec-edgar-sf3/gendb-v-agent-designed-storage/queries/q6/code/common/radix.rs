//! Radix sort of `u64` keys by their low `RADIX_BITS` bits: two stable counting passes of `RADIX_DIGIT` bits each,
//! with caller-supplied scratch (no allocation, `no_unwind`, usable in worker bodies). Keys below `2^RADIX_BITS` end
//! up in increasing order. Only the lengths are specified: callers must use the order for speed only (for example a
//! cache whose every entry is checked when read), never for correctness.
use vstd::prelude::*;
use crate::gendb_entry::work::put;

verus! {

/// Bits per counting pass, and the number of buckets per pass.
pub const RADIX_DIGIT: u64 = 11;
pub const RADIX_BUCKETS: usize = 2048;
/// Bits ordered by the two passes.
pub const RADIX_BITS: u64 = 22;

/// The bucket of key `x` in the pass that orders bits `[shift, shift + RADIX_DIGIT)`.
fn digit(x: u64, shift: u64) -> (b: usize)
    requires shift < 64,
    ensures b < RADIX_BUCKETS,
    no_unwind
{
    let d = (x >> shift) & 2047u64;
    assert(d <= 2047) by (bit_vector)
        requires d == (x >> shift) & 2047u64;
    d as usize
}

/// One stable counting pass: `src[0..n)` ordered by bits `[shift, shift + RADIX_DIGIT)` into `dst[0..n)`
/// (`counts` is scratch). Positions are bounds-checked, so the pass is safe for any input.
fn radix_pass(src: &Vec<u64>, dst: &mut Vec<u64>, counts: &mut Vec<usize>, n: usize, shift: u64)
    requires n <= src@.len(), n <= old(dst)@.len(), old(counts)@.len() == RADIX_BUCKETS, shift < 64,
    ensures final(dst)@.len() == old(dst)@.len(), final(counts)@.len() == RADIX_BUCKETS,
    no_unwind
{
    let mut b: usize = 0;
    while b < RADIX_BUCKETS
        invariant b <= RADIX_BUCKETS, counts@.len() == RADIX_BUCKETS,
        decreases RADIX_BUCKETS - b,
    {
        put(counts, b, 0);
        b = b + 1;
    }
    // bucket sizes
    let mut i: usize = 0;
    while i < n
        invariant i <= n, n <= src@.len(), counts@.len() == RADIX_BUCKETS, shift < 64,
        decreases n - i,
    {
        let d = digit(src[i], shift);
        let c = counts[d];
        if c < n {
            put(counts, d, c + 1);
        }
        i = i + 1;
    }
    // first position of each bucket
    let mut acc: usize = 0;
    let mut b: usize = 0;
    while b < RADIX_BUCKETS
        invariant b <= RADIX_BUCKETS, counts@.len() == RADIX_BUCKETS, acc <= n,
        decreases RADIX_BUCKETS - b,
    {
        let c = counts[b];
        put(counts, b, acc);
        acc = if c <= n - acc { acc + c } else { n };
        b = b + 1;
    }
    // stable scatter
    let m = dst.len();
    let mut i: usize = 0;
    while i < n
        invariant i <= n, n <= src@.len(), n <= m, dst@.len() == m, counts@.len() == RADIX_BUCKETS, shift < 64,
        decreases n - i,
    {
        let x = src[i];
        let d = digit(x, shift);
        let p = counts[d];
        if p < n {
            put(dst, p, x);
            put(counts, d, p + 1);
        }
        i = i + 1;
    }
}

/// `v[0..n)` reordered by the low `RADIX_BITS` bits of its keys (`tmp` and `counts` are scratch).
pub fn radix_sort_low(v: &mut Vec<u64>, tmp: &mut Vec<u64>, counts: &mut Vec<usize>, n: usize)
    requires n <= old(v)@.len(), n <= old(tmp)@.len(), old(counts)@.len() == RADIX_BUCKETS,
    ensures final(v)@.len() == old(v)@.len(), final(tmp)@.len() == old(tmp)@.len(), final(counts)@.len() == RADIX_BUCKETS,
    no_unwind
{
    radix_pass(&*v, tmp, counts, n, 0);
    radix_pass(&*tmp, v, counts, n, RADIX_DIGIT);
}

} // verus!
