//! Per-row byte-trigram signatures of a text column (the scheme of storage `factext_trisig`): a 128-bit Bloom
//! filter with one hashed bit per trigram, stored as two 64-bit words (word 0: bits 0..64, word 1: bits 64..128).
//!
//! A text value `t` has the trigram start positions `0 .. t.len() - 2`; the trigram at `p` is the bytes
//! `t[p], t[p + 1], t[p + 2]`, hashed to a bit position `tri_hash` in `0 .. 128` (Knuth's multiplicative hash of the
//! 24-bit trigram value: the top 7 bits of its 32-bit product with 2654435761). Word `w` of the signature,
//! `sig_of(t, w)`, is the OR of the word-`w` bits (`tri_bit(.., w)`) of every trigram of `t`. Every trigram's bit is
//! set in the signature (`lemma_sig_has`), so a byte string whose trigram bits are not all in a row's signature
//! does not occur in that row's text: a filter that skips rows soundly (it never skips a row that contains the
//! string). Pure metadata: no text is recoverable.
use vstd::prelude::*;

verus! {

/// Bit position (0..128) of the trigram `a, b, c`.
pub open spec fn tri_hash(a: u8, b: u8, c: u8) -> int {
    let x = (a as int) * 65536 + (b as int) * 256 + (c as int);
    ((x * 2654435761) % 4294967296) / 33554432
}

/// The bit of the trigram `a, b, c` in signature word `w` (0 when its bit lies in the other word).
pub open spec fn tri_bit(a: u8, b: u8, c: u8, w: int) -> u64 {
    if tri_hash(a, b, c) / 64 == w { 1u64 << ((tri_hash(a, b, c) % 64) as u64) } else { 0u64 }
}

/// Number of trigram start positions of `t`.
pub open spec fn tri_count(t: Seq<u8>) -> int {
    if t.len() >= 3 { t.len() - 2 } else { 0 }
}

/// Word `w` of the OR of the bits of the trigrams starting at `0 .. k`.
pub open spec fn sig_upto(t: Seq<u8>, k: int, w: int) -> u64
    decreases k,
{
    if k <= 0 { 0u64 } else { sig_upto(t, k - 1, w) | tri_bit(t[k - 1], t[k], t[k + 1], w) }
}

/// Word `w` of the signature of `t`: OR of the word-`w` bits of all its trigrams.
pub open spec fn sig_of(t: Seq<u8>, w: int) -> u64 {
    sig_upto(t, tri_count(t), w)
}

/// The hash is a bit position.
pub proof fn lemma_tri_hash_range(a: u8, b: u8, c: u8)
    ensures 0 <= tri_hash(a, b, c) < 128,
{
    let x = (a as int) * 65536 + (b as int) * 256 + (c as int);
    let m = (x * 2654435761) % 4294967296;
    assert(0 <= m < 4294967296);
    assert(m / 33554432 < 128) by (nonlinear_arith) requires 0 <= m < 4294967296;
    assert(m / 33554432 >= 0) by (nonlinear_arith) requires 0 <= m;
}

/// The bits of the trigram `a, b, c` in words 0 and 1, computed (usable in worker bodies).
pub fn tri_bits_exec(a: u8, b: u8, c: u8) -> (r: (u64, u64))
    ensures r.0 == tri_bit(a, b, c, 0), r.1 == tri_bit(a, b, c, 1),
    no_unwind
{
    proof { lemma_tri_hash_range(a, b, c); }
    let x: u64 = (a as u64) * 65536 + (b as u64) * 256 + (c as u64);
    assert(x < 16777216);
    assert(x * 2654435761 < 0x1_0000_0000_0000_0000) by (nonlinear_arith) requires x < 16777216;
    let h: u64 = ((x * 2654435761) % 4294967296) / 33554432;
    assert(h as int == tri_hash(a, b, c));
    if h < 64 {
        (1u64 << h, 0)
    } else {
        (0, 1u64 << (h - 64))
    }
}

/// OR keeps a bit that is set.
pub proof fn lemma_or_keeps(x: u64, y: u64, b: u64)
    requires x & b == b,
    ensures (x | y) & b == b,
{
    assert((x & b == b) ==> ((x | y) & b == b)) by (bit_vector);
}

/// OR sets the bits it adds.
pub proof fn lemma_or_sets(x: u64, b: u64)
    ensures (x | b) & b == b,
{
    assert((x | b) & b == b) by (bit_vector);
}

/// The bits of the trigrams before `k` stay set in every later prefix signature.
pub proof fn lemma_sig_upto_mono(t: Seq<u8>, p: int, k: int, w: int)
    requires
        0 <= p < k,
    ensures
        sig_upto(t, k, w) & tri_bit(t[p], t[p + 1], t[p + 2], w) == tri_bit(t[p], t[p + 1], t[p + 2], w),
    decreases k,
{
    let b = tri_bit(t[p], t[p + 1], t[p + 2], w);
    if k - 1 == p {
        lemma_or_sets(sig_upto(t, k - 1, w), b);
    } else {
        lemma_sig_upto_mono(t, p, k - 1, w);
        lemma_or_keeps(sig_upto(t, k - 1, w), tri_bit(t[k - 1], t[k], t[k + 1], w), b);
    }
}

/// Every trigram of `t` has its bit set in `sig_of(t, w)`.
pub proof fn lemma_sig_has(t: Seq<u8>, p: int, w: int)
    requires
        0 <= p,
        p + 2 < t.len(),
    ensures
        sig_of(t, w) & tri_bit(t[p], t[p + 1], t[p + 2], w) == tri_bit(t[p], t[p + 1], t[p + 2], w),
{
    lemma_sig_upto_mono(t, p, tri_count(t), w);
}

} // verus!
