//! A 64-bit hash of a byte string over its full content, stated as a spec function (`hash_text`) that the
//! `no_unwind` executable `hash_bytes` computes exactly. Layout of the computation: the length is mixed into the
//! seed, then every full 8-byte little-endian word in order, then the last 8 bytes (overlapping the last full word)
//! when the length is not a multiple of 8; a string shorter than 8 bytes is mixed as one partial word. Only
//! determinism matters for correctness (equal bytes, equal hash); the mixing quality only affects speed.
//! A word is read through an 8-byte subslice (`split_at`), so the compiler emits one unchecked 8-byte load.
use vstd::prelude::*;

verus! {

pub const MIX_MUL: u64 = 0x9E3779B97F4A7C15;
pub const SEED_TAG: u64 = 0xC2B2AE3D27D4EB4F;
pub const SEED_ADSH: u64 = 0x165667B19E3779F9;

/// One mixing step: multiply-xorshift of `h ^ w`.
pub open spec fn mix(h: u64, w: u64) -> u64 {
    let x = vstd::wrapping::u64_specs::wrapping_mul(h ^ w, MIX_MUL);
    x ^ (x >> 29u64)
}

/// Eight bytes of `b` from byte `s` as a little-endian word.
pub open spec fn word8(b: Seq<u8>, s: int) -> u64 {
    (b[s] as u64) | ((b[s + 1] as u64) << 8u64) | ((b[s + 2] as u64) << 16u64) | ((b[s + 3] as u64) << 24u64)
        | ((b[s + 4] as u64) << 32u64) | ((b[s + 5] as u64) << 40u64) | ((b[s + 6] as u64) << 48u64)
        | ((b[s + 7] as u64) << 56u64)
}

/// The first `k` (at most 8) bytes of `b` as a little-endian word.
pub open spec fn word_part(b: Seq<u8>, k: nat) -> u64
    decreases k,
{
    if k == 0 { 0u64 } else { word_part(b, (k - 1) as nat) | ((b[k - 1] as u64) << ((8 * (k - 1)) as u64)) }
}

/// `h` after mixing the first `k` full words of `b`.
pub open spec fn hash_words(b: Seq<u8>, h: u64, k: nat) -> u64
    decreases k,
{
    if k == 0 { h } else { mix(hash_words(b, h, (k - 1) as nat), word8(b, 8 * (k - 1))) }
}

/// The hash of `b` under `seed`.
pub open spec fn hash_text(b: Seq<u8>, seed: u64) -> u64 {
    let n = b.len();
    let h0 = mix(seed, n as u64);
    if n < 8 {
        mix(h0, word_part(b, n))
    } else {
        let h1 = hash_words(b, h0, n / 8);
        if n % 8 == 0 { h1 } else { mix(h1, word8(b, n - 8)) }
    }
}

#[inline(always)]
pub fn mix_exec(h: u64, w: u64) -> (r: u64)
    ensures r == mix(h, w),
    no_unwind
{
    let x = (h ^ w).wrapping_mul(MIX_MUL);
    x ^ (x >> 29u64)
}

/// The word at byte `s`, read from an 8-byte subslice (bounds known to the compiler: one load).
#[inline(always)]
pub fn word8_at(b: &[u8], s: usize) -> (w: u64)
    requires s + 8 <= b@.len(),
    ensures w == word8(b@, s as int),
    no_unwind
{
    let (_, t) = b.split_at(s);
    let (x, _) = t.split_at(8);
    proof {
        assert forall|k: int| 0 <= k < 8 implies x@[k] == b@[s + k] by {
            assert(x@[k] == t@[k]);
        }
    }
    (x[0] as u64) | ((x[1] as u64) << 8u64) | ((x[2] as u64) << 16u64) | ((x[3] as u64) << 24u64)
        | ((x[4] as u64) << 32u64) | ((x[5] as u64) << 40u64) | ((x[6] as u64) << 48u64)
        | ((x[7] as u64) << 56u64)
}

/// `hash_text(b@, seed)`; `n` is the length of `b` (slice `len` is not `no_unwind`).
pub fn hash_bytes(b: &[u8], n: usize, seed: u64) -> (h: u64)
    requires n == b@.len(),
    ensures h == hash_text(b@, seed),
    no_unwind
{
    let h0 = mix_exec(seed, n as u64);
    if n < 8 {
        let mut w: u64 = 0;
        let mut k: usize = 0;
        while k < n
            invariant k <= n, n == b@.len(), n < 8, w == word_part(b@, k as nat),
            decreases n - k,
        {
            w = w | ((b[k] as u64) << ((8 * k) as u64));
            k = k + 1;
        }
        mix_exec(h0, w)
    } else {
        let words = n / 8;
        let mut h = h0;
        let mut k: usize = 0;
        while k < words
            invariant k <= words, words == n / 8, n == b@.len(), h == hash_words(b@, h0, k as nat),
            decreases words - k,
        {
            proof {
                assert(8 * k + 8 <= n) by (nonlinear_arith) requires k < words, words == n / 8;
            }
            h = mix_exec(h, word8_at(b, 8 * k));
            k = k + 1;
        }
        if n % 8 == 0 { h } else { mix_exec(h, word8_at(b, n - 8)) }
    }
}

} // verus!
