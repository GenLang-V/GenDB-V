//! Bit-level facts about 64-bit masks (one bit per row of a 64-row block): setting a bit, clearing the lowest set
//! bit, and the first set bit (`trailing_zeros`); 2-bit fields of a word (`field2`); bitmaps of 64-bit words
//! (`word_bit`).
//! Each fact is one small `bit_vector` lemma, stated for a single bit position; `lemma_bit_or_set` and
//! `lemma_bit_or3` cover setting a bit with OR and the union of three masks.
use vstd::prelude::*;
use vstd::std_specs::bits::{u64_trailing_zeros, axiom_u64_trailing_zeros};

verus! {

/// Bit `u` of `m` (positions `0..64`).
pub open spec fn bit(m: u64, u: u64) -> bool { (m >> u) & 1u64 == 1u64 }

/// `m` with bit `t` set to `x` (`m` has bit `t` clear).
pub proof fn lemma_bit_set(m: u64, x: u64, t: u64, u: u64)
    requires t < 64, u < 64, x <= 1, !bit(m, t),
    ensures bit(m | (x << t), u) == if u == t { x == 1 } else { bit(m, u) },
{
    assert(((m >> t) & 1u64 != 1u64 && t < 64 && u < 64 && x <= 1) ==>
        ((((m | (x << t)) >> u) & 1u64 == 1u64) == if u == t { x == 1 } else { (m >> u) & 1u64 == 1u64 })) by (bit_vector);
}

/// `m` with bit `t` set (whether or not it was set before).
pub proof fn lemma_bit_or_set(m: u64, t: u64, u: u64)
    requires t < 64, u < 64,
    ensures bit(m | (1u64 << t), u) == (u == t || bit(m, u)),
{
    assert((t < 64 && u < 64) ==> ((((m | (1u64 << t)) >> u) & 1u64 == 1u64) == (u == t || (m >> u) & 1u64 == 1u64)))
        by (bit_vector);
}

/// A bit of the union of three masks.
pub proof fn lemma_bit_or3(a: u64, b: u64, c: u64, u: u64)
    requires u < 64,
    ensures bit(a | b | c, u) == (bit(a, u) || bit(b, u) || bit(c, u)),
{
    assert(u < 64 ==> ((((a | b | c) >> u) & 1u64 == 1u64)
        == ((a >> u) & 1u64 == 1u64 || (b >> u) & 1u64 == 1u64 || (c >> u) & 1u64 == 1u64))) by (bit_vector);
}

/// The empty mask.
pub proof fn lemma_bit_zero(u: u64)
    ensures !bit(0, u),
{
    assert((0u64 >> u) & 1u64 != 1u64) by (bit_vector);
}

/// The first set bit of a non-zero mask: set, and every bit below it clear.
pub proof fn lemma_first_bit(c: u64)
    requires c != 0,
    ensures
        c.trailing_zeros() < 64,
        bit(c, c.trailing_zeros() as u64),
        forall|u: u64| u < c.trailing_zeros() ==> !#[trigger] bit(c, u),
{
    axiom_u64_trailing_zeros(c);
}

/// Clearing the lowest set bit `s` of `c` keeps every other bit.
pub proof fn lemma_clear_lowest(c: u64, s: u64, u: u64)
    requires
        c != 0, s < 64, u < 64, bit(c, s),
        forall|v: u64| v < s ==> !#[trigger] bit(c, v),
    ensures bit(c & sub(c, 1), u) == (bit(c, u) && u != s),
{
    if u < s {
        assert(!bit(c, u));
        assert(((c >> u) & 1u64 != 1u64 && u < s && s < 64) ==> (((c & sub(c, 1)) >> u) & 1u64 != 1u64)) by (bit_vector);
    } else if u == s {
        assert(!bit(c, 0) || s == 0);
        // the bits below s are zero, so c - 1 clears bit s and sets the bits below it
        lemma_low_bits_zero(c, s);
        assert((c & sub(sub(1u64 << s, 1), 0) == 0u64 && ((c >> s) & 1u64 == 1u64) && s < 64) ==>
            (((c & sub(c, 1)) >> s) & 1u64 != 1u64)) by (bit_vector);
    } else {
        lemma_low_bits_zero(c, s);
        assert((c & sub(sub(1u64 << s, 1), 0) == 0u64 && ((c >> s) & 1u64 == 1u64) && s < u && u < 64) ==>
            ((((c & sub(c, 1)) >> u) & 1u64 == 1u64) == ((c >> u) & 1u64 == 1u64))) by (bit_vector);
    }
}

/// The bits of `c` below `s` are clear exactly when `c & (2^s - 1) == 0`.
pub proof fn lemma_low_bits_zero(c: u64, s: u64)
    requires s < 64, forall|v: u64| v < s ==> !#[trigger] bit(c, v),
    ensures c & sub(sub(1u64 << s, 1), 0) == 0u64,
    decreases s,
{
    if s > 0 {
        assert(!bit(c, (s - 1) as u64));
        lemma_low_bits_zero(c, (s - 1) as u64);
        let t = (s - 1) as u64;
        assert((c & sub(sub(1u64 << t, 1), 0) == 0u64 && ((c >> t) & 1u64 != 1u64) && t < 63 && s == t + 1) ==>
            c & sub(sub(1u64 << s, 1), 0) == 0u64) by (bit_vector);
    } else {
        assert(c & sub(sub(1u64 << 0u64, 1), 0) == 0u64) by (bit_vector);
    }
}

/// The 2-bit field `j` (bits `2j`, `2j + 1`) of `m`, for `j < 32`.
pub open spec fn field2(m: u64, j: u64) -> u64 { (m >> (2 * j)) & 3u64 }

/// Every field of the empty word is 0.
pub proof fn lemma_field2_zero(j: u64)
    requires j < 32,
    ensures field2(0u64, j) == 0,
{
    assert(j < 32 ==> (0u64 >> (2 * j)) & 3u64 == 0u64) by (bit_vector);
}

/// A field is at most 3.
pub proof fn lemma_field2_max(m: u64, j: u64)
    ensures field2(m, j) <= 3,
{
    assert((m >> (2 * j)) & 3u64 <= 3u64) by (bit_vector);
}

/// `m` with the empty field `k` set to `t`.
pub proof fn lemma_field2_set(m: u64, t: u64, k: u64, j: u64)
    requires k < 32, j < 32, t <= 3, field2(m, k) == 0,
    ensures field2(m | (t << (2 * k)), j) == if j == k { t } else { field2(m, j) },
{
    assert((k < 32 && j < 32 && t <= 3 && (m >> (2 * k)) & 3u64 == 0u64) ==>
        ((m | (t << (2 * k))) >> (2 * j)) & 3u64 == if j == k { t } else { (m >> (2 * j)) & 3u64 }) by (bit_vector);
}

/// Bit `u % 64` of word `u / 64`, for row `u` of a bitmap stored as 64-bit words.
pub open spec fn word_bit(words: Seq<u64>, u: int) -> bool {
    0 <= u && u / 64 < words.len() && bit(words[u / 64], (u % 64) as u64)
}

} // verus!
