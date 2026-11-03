//! 64-element match masks for vectorizable filters over codes: byte equality (`match_mask`: bit `b` set iff
//! `x[base + b] == v`) and a half-open range over 16-bit codes (`range_mask16`: bit `b` set iff
//! `lo <= x[base + b] < hi`), and the lowest set bit of a mask (`lowest_bit`, `clear_bit`). Every helper is
//! `no_unwind` (usable in worker bodies).
//!
//! `match_mask` compiles to byte compares and a move-mask; `lowest_bit` takes a de Bruijn table guess, checks it at
//! run time (set, and nothing set below it) and falls back to a linear search, so the table needs no proof.
//! `pop_lowest` returns the lowest set bit and the mask without it (`m & (m - 1)`), checking the table guess with
//! one compare against the isolated bit. The isolated bit is written `m & -m` (`m & (!m + 1)`), the form LLVM
//! recognizes as a table-based count of trailing zeros: the lookup compiles to one `tzcnt`.
//! `lemma_set_bit` and `lemma_and_zero_bit` are the facts a loop needs that builds a mask bit by bit and tests two
//! masks for common bits.
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

/// Setting bit `j` to `v` (0 or 1): bit `b` of the result as an `int`-indexed `bit`.
pub proof fn lemma_set_bit(m: u64, v: u64, j: u64, b: int)
    requires v <= 1, j < 64, 0 <= b < 64,
    ensures bit(m | (v << j), b) == (if b == j { bit(m, b) || v == 1 } else { bit(m, b) }),
{
    lemma_or_bit(m, v, j, b as u64);
}

proof fn lemma_and_zero_bv(x: u64, m: u64, b: u64)
    by (bit_vector)
    requires b < 64, x & m == 0u64, (m >> b) & 1u64 == 1u64,
    ensures (x >> b) & 1u64 != 1u64,
{
}

/// Two masks without common bits: a bit set in `m` is clear in `x`.
pub proof fn lemma_and_zero_bit(x: u64, m: u64, b: int)
    requires 0 <= b < 64, x & m == 0, bit(m, b),
    ensures !bit(x, b),
{
    lemma_and_zero_bv(x, m, b as u64);
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

/// Mask of the 64 codes `x[base .. base + 64]` in `[lo, hi)`: bit `b` is set iff `lo <= x[base + b] < hi`.
pub fn range_mask16(x: &[u16], base: usize, lo: u32, hi: u32) -> (m: u64)
    requires base + 64 <= x@.len(),
    ensures forall|b: int| 0 <= b < 64 ==> (#[trigger] bit(m, b) <==> (lo <= x@[base + b] && x@[base + b] < hi)),
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
            forall|b: int| 0 <= b < 64 ==> (#[trigger] bit(m, b) <==> (b < j && lo <= x@[base + b] && x@[base + b] < hi)),
        decreases 64 - j,
    {
        let c = x[base + j] as u32;
        let inr = lo <= c && c < hi;
        let one: u64 = if inr { 1 } else { 0 };
        let ghost m0 = m;
        m = m | (one << (j as u64));
        proof {
            assert forall|b: int| 0 <= b < 64 implies (#[trigger] bit(m, b) <==> (b < j + 1 && lo <= x@[base + b] && x@[base + b] < hi)) by {
                lemma_or_bit(m0, one, j as u64, b as u64);
                assert(bit(m0, b) <==> (b < j && lo <= x@[base + b] && x@[base + b] < hi));
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

/// The isolated lowest bit `m ^ (m & (m - 1))` equal to `2^g` means bit `g` is set and none below it.
proof fn lemma_isolated(m: u64, g: u64)
    by (bit_vector)
    requires m != 0u64, g < 64u64, (m ^ (m & sub(m, 1u64))) == (1u64 << g),
    ensures (m >> g) & 1u64 == 1u64, m & sub(1u64 << g, 1u64) == 0u64,
{
}

/// With bit `g` the lowest set bit, `m & (m - 1)` is `m` without bit `g`.
proof fn lemma_drop_lowest(m: u64, g: u64, b: u64)
    by (bit_vector)
    requires g < 64u64, b < 64u64, (m >> g) & 1u64 == 1u64, m & sub(1u64 << g, 1u64) == 0u64,
    ensures (((m & sub(m, 1u64)) >> b) & 1u64 == 1u64) == (b != g && (m >> b) & 1u64 == 1u64),
{
}

/// No bit below `q` is set: `m` has no bit under the mask `2^q - 1`.
proof fn lemma_mask_below(m: u64, q: u64)
    requires q < 64, forall|b: int| 0 <= b < q ==> !#[trigger] bit(m, b),
    ensures m & sub(1u64 << q, 1u64) == 0u64,
    decreases q,
{
    if q > 0 {
        lemma_mask_below(m, (q - 1) as u64);
        assert(!bit(m, q - 1));
        lemma_mask_step(m, (q - 1) as u64);
    } else {
        lemma_mask_zero(m);
    }
}

proof fn lemma_mask_step(m: u64, q: u64)
    by (bit_vector)
    requires q < 63u64, m & sub(1u64 << q, 1u64) == 0u64, (m >> q) & 1u64 != 1u64,
    ensures m & sub(1u64 << add(q, 1u64), 1u64) == 0u64,
{
}

proof fn lemma_mask_zero(m: u64)
    by (bit_vector)
    ensures m & sub(1u64 << 0u64, 1u64) == 0u64,
{
}

/// Bit positions by the top 6 bits of `2^p * 0x03f79d71b4cb0a89` (a read-only table; every use checks its entry).
pub const DEBRUIJN: [u8; 64] = [
    0, 1, 48, 2, 57, 49, 28, 3, 61, 58, 50, 42, 38, 29, 17, 4, 62, 55, 59, 36, 53, 51, 43, 22, 45, 39, 33, 30,
    24, 18, 12, 5, 63, 47, 56, 27, 60, 41, 37, 16, 54, 35, 52, 21, 44, 32, 23, 11, 46, 26, 40, 15, 34, 20, 31, 10,
    25, 14, 19, 9, 13, 8, 7, 6,
];

proof fn lemma_neg_ok(m: u64)
    by (bit_vector)
    requires m != 0u64,
    ensures !m < 0xFFFF_FFFF_FFFF_FFFFu64,
{
}

/// `m & -m` (as LLVM's table-based count-trailing-zeros pattern expects it) is `m ^ (m & (m - 1))`.
proof fn lemma_low_iso(m: u64)
    by (bit_vector)
    requires m != 0u64,
    ensures m & add(!m, 1u64) == m ^ (m & sub(m, 1u64)),
{
}

/// The lowest set bit `p` of a nonzero `m` and `m` without it.
#[inline(always)]
pub fn pop_lowest(m: u64) -> (r: (u64, u64))
    requires m != 0,
    ensures
        r.0 < 64, bit(m, r.0 as int), forall|b: int| 0 <= b < r.0 ==> !#[trigger] bit(m, b),
        forall|b: int| 0 <= b < 64 ==> (#[trigger] bit(r.1, b) <==> (b != r.0 && bit(m, b))),
    no_unwind
{
    let rest = m & (m - 1);
    proof { lemma_neg_ok(m); }
    let low = m & ((!m) + 1);
    proof { lemma_low_iso(m); }
    // The isolated lowest bit times the de Bruijn constant has the bit's position in its top 6 bits.
    let h = low.wrapping_mul(0x03f79d71b4cb0a89u64);
    proof { lemma_top6(h); }
    let guess = DEBRUIJN[(h >> 58u64) as usize] as u64;
    let mut q: u64 = 0;
    if guess < 64 && low == (1u64 << guess) {
        proof { lemma_isolated(m, guess); }
        q = guess;
    } else {
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
        proof { lemma_mask_below(m, q); }
    }
    proof {
        assert forall|b: int| 0 <= b < q implies !#[trigger] bit(m, b) by {
            lemma_below_mask(m, q, b as u64);
        }
        assert forall|b: int| 0 <= b < 64 implies (#[trigger] bit(rest, b) <==> (b != q && bit(m, b))) by {
            lemma_drop_lowest(m, q, b as u64);
        }
    }
    (q, rest)
}

/// Packing a 24-bit value and an 8-bit value into one word and reading them back.
pub proof fn lemma_pack24(t: u32, q: u32)
    by (bit_vector)
    requires t < 0x100_0000u32, q < 256u32,
    ensures ((t | (q << 24u32)) & 0xFF_FFFFu32) == t, ((t | (q << 24u32)) >> 24u32) == q,
{
}

/// The top 8 bits of a word are below 256.
pub proof fn lemma_top8(e: u32)
    by (bit_vector)
    ensures e >> 24u32 < 256u32, e & 0xFF_FFFFu32 < 0x100_0000u32,
{
}

/// A right shift does not grow a value.
pub proof fn lemma_shr_le(x: u64, s: u64)
    by (bit_vector)
    ensures x >> s <= x,
{
}

/// Right shifts are monotone.
pub proof fn lemma_shr_mono(a: u32, b: u32, s: u32)
    by (bit_vector)
    requires a <= b,
    ensures a >> s <= b >> s,
{
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
