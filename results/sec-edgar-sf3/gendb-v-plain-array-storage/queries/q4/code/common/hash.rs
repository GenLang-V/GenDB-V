//! Cheap 64-bit hashes of byte strings and integers with exact specifications: multiplicative mixing
//! (`mix(h, x) = (h ^ x) * K1 mod 2^64`) of the length and of three little-endian 8-byte words of the text (its
//! first, middle and last 8 bytes; shorter texts are packed into one word). A hash computed when an index is
//! built and one computed when it is probed are the same function of the key bytes, so equal keys always meet
//! in one bucket. Nothing here depends on the quality of the hash; only speed does.
use vstd::prelude::*;

verus! {

/// The multiplier of `mix` (2^64 / golden ratio, odd).
pub const K1: u64 = 0x9E37_79B9_7F4A_7C15;

/// One mixing step: `(h ^ x) * K1` modulo 2^64.
pub open spec fn mix_spec(h: u64, x: u64) -> u64 {
    (h ^ x).wrapping_mul(K1)
}

pub fn mix(h: u64, x: u64) -> (r: u64)
    ensures r == mix_spec(h, x),
    no_unwind
{
    (h ^ x).wrapping_mul(K1)
}

/// The little-endian word of bytes `at .. at + 8` of `t`.
pub open spec fn word8_spec(t: Seq<u8>, at: int) -> u64 {
    (t[at] as u64) | ((t[at + 1] as u64) << 8u64) | ((t[at + 2] as u64) << 16u64) | ((t[at + 3] as u64) << 24u64)
        | ((t[at + 4] as u64) << 32u64) | ((t[at + 5] as u64) << 40u64) | ((t[at + 6] as u64) << 48u64)
        | ((t[at + 7] as u64) << 56u64)
}

pub fn word8(t: &[u8], at: usize, n: usize) -> (r: u64)
    requires n == t@.len(), at + 8 <= n,
    ensures r == word8_spec(t@, at as int),
    no_unwind
{
    // A subslice of exactly 8 bytes: constant indexes need no bounds checks, so the 8 loads merge into one.
    let (_, tail) = t.split_at(at);
    let (w, _) = tail.split_at(8);
    proof {
        assert(w@ =~= t@.subrange(at as int, at + 8));
    }
    (w[0] as u64) | ((w[1] as u64) << 8u64) | ((w[2] as u64) << 16u64) | ((w[3] as u64) << 24u64)
        | ((w[4] as u64) << 32u64) | ((w[5] as u64) << 40u64) | ((w[6] as u64) << 48u64)
        | ((w[7] as u64) << 56u64)
}

/// The first `k` bytes of `t` packed big-endian into one word (meant for `k < 8`).
pub open spec fn small_word_spec(t: Seq<u8>, k: int) -> u64
    decreases k,
{
    if k <= 0 { 0 } else { (small_word_spec(t, k - 1) << 8u64) | (t[k - 1] as u64) }
}

pub fn small_word(t: &[u8], n: usize) -> (r: u64)
    requires n == t@.len(),
    ensures r == small_word_spec(t@, n as int),
    no_unwind
{
    let mut w: u64 = 0;
    let mut q: usize = 0;
    while q < n
        invariant q <= n, n == t@.len(), w == small_word_spec(t@, q as int),
        decreases n - q,
    {
        w = (w << 8u64) | (t[q] as u64);
        q = q + 1;
    }
    w
}

/// Hash of the text `t` under `seed`.
pub open spec fn text_hash_spec(seed: u64, t: Seq<u8>) -> u64 {
    let n = t.len() as int;
    if n >= 8 {
        mix_spec(mix_spec(mix_spec(seed ^ (n as u64), word8_spec(t, 0)), word8_spec(t, (n - 8) / 2)), word8_spec(t, n - 8))
    } else {
        mix_spec(seed ^ (n as u64), small_word_spec(t, n))
    }
}

/// Hash of the `n` bytes `t` (the length is passed: slice `len` is not `no_unwind`).
pub fn text_hash(seed: u64, t: &[u8], n: usize) -> (r: u64)
    requires n == t@.len(),
    ensures r == text_hash_spec(seed, t@),
    no_unwind
{
    if n >= 8 {
        let w0 = word8(t, 0, n);
        let w1 = word8(t, (n - 8) / 2, n);
        let w2 = word8(t, n - 8, n);
        mix(mix(mix(seed ^ (n as u64), w0), w1), w2)
    } else {
        let w = small_word(t, n);
        mix(seed ^ (n as u64), w)
    }
}

/// Hash of a pair of texts (for example a tag and its version).
pub open spec fn pair_hash_spec(seed: u64, a: Seq<u8>, b: Seq<u8>) -> u64 {
    text_hash_spec(text_hash_spec(seed, a), b)
}

pub fn pair_hash(seed: u64, a: &[u8], na: usize, b: &[u8], nb: usize) -> (r: u64)
    requires na == a@.len(), nb == b@.len(),
    ensures r == pair_hash_spec(seed, a@, b@),
    no_unwind
{
    let h = text_hash(seed, a, na);
    text_hash(h, b, nb)
}

} // verus!
