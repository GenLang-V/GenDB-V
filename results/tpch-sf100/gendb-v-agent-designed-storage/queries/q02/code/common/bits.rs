//! 64-element byte match masks (bit `b` set iff `x[base + b] == v`) and the lowest set bit of a mask, for
//! vectorizable equality filters over byte codes. Every helper is `no_unwind` (usable in worker bodies).
//!
//! `match_mask` compiles to byte compares and a move-mask; `lowest_bit` takes a de Bruijn table guess, checks it at
//! run time (set, and nothing set below it) and falls back to a linear search, so the table needs no proof.
use vstd::prelude::*;

verus! {

/// Bit `b` (0 <= b < 64) of `m` is set.
pub open spec fn bit(m: u64, b: int) -> bool {
    (m >> (b as u64)) & 1u64 == 1u64
}

/// Setting bit `j` to `v` (0 or 1) leaves the other bits.
proof fn lemma_or_bit(m: u64, v: u64, j: u64, b: u64)
    by (bit_vector)
    requires v <= 1, j < 64, b < 64,
    ensures
        (((m | (v << j)) >> b) & 1u64 == 1u64)
            == (if b == j { ((m >> b) & 1u64 == 1u64) || v == 1u64 } else { (m >> b) & 1u64 == 1u64 }),
{
}

/// Clearing bit `p` leaves the other bits.
proof fn lemma_clear_bit(m: u64, p: u64, b: u64)
    by (bit_vector)
    requires p < 64, b < 64,
    ensures (((m & !(1u64 << p)) >> b) & 1u64 == 1u64) == (b != p && (m >> b) & 1u64 == 1u64),
{
}

/// No bit of zero is set.
proof fn lemma_zero_bit(b: u64)
    by (bit_vector)
    requires b < 64,
    ensures (0u64 >> b) & 1u64 != 1u64,
{
}

/// `m` has no set bit below `p` when it has none under the mask `2^p - 1`.
proof fn lemma_below_mask(m: u64, p: u64, b: u64)
    by (bit_vector)
    requires p < 64, b < p, m & sub(1u64 << p, 1u64) == 0u64,
    ensures (m >> b) & 1u64 != 1u64,
{
}

/// `2^p` is at least 1.
proof fn lemma_pow_pos(p: u64)
    by (bit_vector)
    requires p < 64,
    ensures 1u64 << p >= 1u64,
{
}

/// The top 6 bits of a word index a 64-entry table.
proof fn lemma_top6(x: u64)
    by (bit_vector)
    ensures x >> 58u64 < 64u64,
{
}

/// No bit of zero is set.
pub proof fn lemma_no_bit_of_zero(b: int)
    requires 0 <= b < 64,
    ensures !bit(0u64, b),
{
    lemma_zero_bit(b as u64);
}

/// A nonzero word has a set bit.
proof fn lemma_nonzero_has_bit(m: u64)
    requires m != 0,
    ensures exists|b: int| 0 <= b < 64 && #[trigger] bit(m, b),
{
    broadcast use vstd::std_specs::bits::axiom_u64_trailing_zeros;
    let z = vstd::std_specs::bits::u64_trailing_zeros(m);
    assert(bit(m, z as int));
}

/// Mask of the 64 bytes `x[base .. base + 64]` equal to `v`: bit `b` is set iff `x[base + b] == v`.
pub fn match_mask(x: &[u8], base: usize, v: u8) -> (m: u64)
    requires base + 64 <= x@.len(),
    ensures forall|b: int| 0 <= b < 64 ==> (#[trigger] bit(m, b) <==> x@[base + b] == v),
    no_unwind
{
    let mut m: u64 = 0;
    proof {
        assert forall|b: int| 0 <= b < 64 implies !#[trigger] bit(m, b) by { lemma_zero_bit(b as u64); }
    }
    let mut j: usize = 0;
    while j < 64
        invariant
            base + 64 <= x@.len(),
            j <= 64,
            forall|b: int| 0 <= b < 64 ==> (#[trigger] bit(m, b) <==> (b < j && x@[base + b] == v)),
        decreases 64 - j,
    {
        let one: u64 = if x[base + j] == v { 1 } else { 0 };
        let ghost m0 = m;
        m = m | (one << (j as u64));
        proof {
            assert forall|b: int| 0 <= b < 64 implies (#[trigger] bit(m, b) <==> (b < j + 1 && x@[base + b] == v)) by {
                lemma_or_bit(m0, one, j as u64, b as u64);
                assert(bit(m0, b) <==> (b < j && x@[base + b] == v));
            }
        }
        j = j + 1;
    }
    m
}

/// The lowest set bit of a nonzero `m`.
pub fn lowest_bit(m: u64) -> (p: u64)
    requires m != 0,
    ensures p < 64, bit(m, p as int), forall|b: int| 0 <= b < p ==> !#[trigger] bit(m, b),
    no_unwind
{
    let db: [u8; 64] = [
        0, 1, 48, 2, 57, 49, 28, 3, 61, 58, 50, 42, 38, 29, 17, 4, 62, 55, 59, 36, 53, 51, 43, 22, 45, 39, 33, 30,
        24, 18, 12, 5, 63, 47, 56, 27, 60, 41, 37, 16, 54, 35, 52, 21, 44, 32, 23, 11, 46, 26, 40, 15, 34, 20, 31, 10,
        25, 14, 19, 9, 13, 8, 7, 6,
    ];
    // The isolated lowest bit times the de Bruijn constant has the bit's position in its top 6 bits.
    let low = m ^ (m & (m - 1));
    let h = low.wrapping_mul(0x03f79d71b4cb0a89u64);
    proof { lemma_top6(h); }
    let guess = db[(h >> 58u64) as usize] as u64;
    if guess < 64 {
        proof { lemma_pow_pos(guess); }
        if (m >> guess) & 1u64 == 1u64 && m & ((1u64 << guess) - 1u64) == 0u64 {
            proof {
                assert forall|b: int| 0 <= b < guess implies !#[trigger] bit(m, b) by {
                    lemma_below_mask(m, guess, b as u64);
                }
            }
            return guess;
        }
    }
    let mut q: u64 = 0;
    while q < 64 && (m >> q) & 1u64 != 1u64
        invariant q <= 64, forall|b: int| 0 <= b < q ==> !#[trigger] bit(m, b),
        decreases 64 - q,
    {
        q = q + 1;
    }
    if q == 64 {
        proof { lemma_nonzero_has_bit(m); }
        assert(false);
    }
    q
}

/// The bits of `m` without bit `p`.
pub fn clear_bit(m: u64, p: u64) -> (r: u64)
    requires p < 64,
    ensures forall|b: int| 0 <= b < 64 ==> (#[trigger] bit(r, b) <==> (b != p && bit(m, b))),
    no_unwind
{
    let r = m & !(1u64 << p);
    proof {
        assert forall|b: int| 0 <= b < 64 implies (#[trigger] bit(r, b) <==> (b != p && bit(m, b))) by {
            lemma_clear_bit(m, p, b as u64);
        }
    }
    r
}

} // verus!
