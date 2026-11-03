//! Bit masks in a `u64` (bit `u` of `x` is `bit(x, u)`): setting one bit, clearing bit 0, the lowest set bit
//! (`x & (x - 1)` clears it, `x - (x & (x - 1))` isolates it), the mask of the bits `[a, e)`, intersections, and the
//! index of the lowest set bit (`low_bit`: a de Bruijn multiplication and a table lookup whose answer is checked at
//! run time, so the table needs no proof; usable where `u64::trailing_zeros`, which may unwind, is not) and of the
//! highest one (`high_bit`).
//!
//! Each lemma states one fact per bit position `u < 64` and is proved by the bit-vector solver; callers quantify
//! over `u` themselves (`assert forall|u: u64| u < 64 implies ... by { lemma_...(.., u) }`).
use vstd::prelude::*;
use vstd::std_specs::bits::{u64_trailing_zeros, axiom_u64_trailing_zeros};

verus! {

/// Bit `u` of `x` is set.
pub open spec fn bit(x: u64, u: u64) -> bool { (x >> u) & 1u64 == 1u64 }

/// Setting bit `t` to `b` (0 or 1) by `x | (b << t)`.
pub proof fn lemma_bit_or(x: u64, b: u64, t: u64, u: u64)
    requires b <= 1, t < 64, u < 64,
    ensures bit(x | (b << t), u) == (bit(x, u) || (u == t && b == 1)),
{
    assert(((x | (b << t)) >> u) & 1u64 == 1u64 <==> (((x >> u) & 1u64 == 1u64) || (u == t && b == 1)))
        by (bit_vector) requires b <= 1, t < 64, u < 64;
}

/// No bit of 0 is set.
pub proof fn lemma_bit_zero(u: u64)
    ensures !bit(0u64, u),
{
    assert(!((0u64 >> u) & 1u64 == 1u64)) by (bit_vector);
}

/// Clearing bit 0 by `x & !1`.
pub proof fn lemma_bit_clear0(x: u64, u: u64)
    requires u < 64,
    ensures bit(x & !1u64, u) == (u != 0 && bit(x, u)),
{
    assert(((x & !1u64) >> u) & 1u64 == 1u64 <==> (u != 0 && (x >> u) & 1u64 == 1u64)) by (bit_vector) requires u < 64;
}

/// The bit `e` of a nonzero `x` returned by `trailing_zeros` is set and every bit below it is clear (in closed form:
/// `x << (64 - e) == 0`).
pub proof fn lemma_tz(x: u64)
    requires x != 0,
    ensures
        u64_trailing_zeros(x) < 64,
        bit(x, u64_trailing_zeros(x) as u64),
        x << sub(64u64, u64_trailing_zeros(x) as u64) == 0,
        forall|u: u64| u < u64_trailing_zeros(x) ==> !#[trigger] bit(x, u),
{
    axiom_u64_trailing_zeros(x);
}

/// Clearing the lowest set bit `e` of `x` by `x & (x - 1)`.
pub proof fn lemma_clear_lowest(x: u64, e: u64, u: u64)
    requires e < 64, u < 64, bit(x, e), x << sub(64u64, e) == 0,
    ensures
        x >= 1,
        bit(x & sub(x, 1u64), u) == (u > e && bit(x, u)),
{
    assert(x >= 1 && ((((x & sub(x, 1u64)) >> u) & 1u64 == 1u64) <==> (u > e && (x >> u) & 1u64 == 1u64))) by (bit_vector)
        requires e < 64, u < 64, (x >> e) & 1u64 == 1u64, x << sub(64u64, e) == 0;
}

/// The bits `[a, a + k)` of `x` moved to bit 0: `(x >> a) & (2^k - 1)`.
pub proof fn lemma_bits_range(x: u64, a: u64, k: u64, u: u64)
    requires a < 64, 1 <= k < 64, u < 64,
    ensures bit((x >> a) & sub(1u64 << k, 1u64), u) == (u < k && add(a, u) < 64 && bit(x, add(a, u))),
{
    assert((((x >> a) & sub(1u64 << k, 1u64)) >> u) & 1u64 == 1u64
        <==> (u < k && add(a, u) < 64 && (x >> add(a, u)) & 1u64 == 1u64)) by (bit_vector)
        requires a < 64, 1 <= k, k < 64, u < 64;
}

/// Bit `u` of an intersection.
pub proof fn lemma_bit_and(x: u64, y: u64, u: u64)
    requires u < 64,
    ensures bit(x & y, u) == (bit(x, u) && bit(y, u)),
{
    assert((((x & y) >> u) & 1u64 == 1u64) <==> ((x >> u) & 1u64 == 1u64 && (y >> u) & 1u64 == 1u64)) by (bit_vector)
        requires u < 64;
}

/// The single bit `1 << a`.
pub proof fn lemma_bit_single(a: u64, u: u64)
    requires a < 64, u < 64,
    ensures bit(1u64 << a, u) == (u == a),
{
    assert((((1u64 << a) >> u) & 1u64 == 1u64) <==> (u == a)) by (bit_vector) requires a < 64, u < 64;
}

/// The lowest set bit `e` of `x` (bits below `e` clear) isolated: `x - (x & (x - 1)) == 1 << e`.
pub proof fn lemma_low_mask(x: u64, e: u64)
    requires e < 64, bit(x, e), x << sub(64u64, e) == 0,
    ensures x >= 1, x & sub(x, 1u64) <= x, sub(x, x & sub(x, 1u64)) == 1u64 << e,
{
    assert(x >= 1 && x & sub(x, 1u64) <= x && sub(x, x & sub(x, 1u64)) == 1u64 << e) by (bit_vector)
        requires e < 64, (x >> e) & 1u64 == 1u64, x << sub(64u64, e) == 0;
}

/// The mask of the bits `[a, e)`: `(1 << e) - (1 << a)`.
pub proof fn lemma_span(a: u64, e: u64, u: u64)
    requires a < e < 64, u < 64,
    ensures 1u64 << a <= 1u64 << e, bit(sub(1u64 << e, 1u64 << a), u) == (a <= u && u < e),
{
    assert(1u64 << a <= 1u64 << e && ((((sub(1u64 << e, 1u64 << a)) >> u) & 1u64 == 1u64) <==> (a <= u && u < e)))
        by (bit_vector) requires a < e, e < 64, u < 64;
}

/// `x << (64 - r) == 0` clears every bit below `r`.
pub proof fn lemma_shl_low_zero(x: u64, r: u64, u: u64)
    requires 0 < r < 64, x << sub(64u64, r) == 0, u < r,
    ensures !bit(x, u),
{
    assert(!((x >> u) & 1u64 == 1u64)) by (bit_vector) requires 0 < r, r < 64, x << sub(64u64, r) == 0, u < r;
}

/// The de Bruijn constant of `low_bit` (every 6-bit window of it is distinct).
pub const DEBRUIJN64: u64 = 0x03f7_9d71_b4cb_0a89;

/// The lookup table of `low_bit`: entry `(2^i * DEBRUIJN64) >> 58` is `i`. Its contents are not part of any proof
/// (`low_bit` checks every answer), only its length.
pub fn low_bit_table() -> (tab: Vec<u8>)
    ensures tab@.len() == 64,
{
    let mut tab: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < 64
        invariant i <= 64, tab@.len() == i,
        decreases 64 - i,
    {
        tab.push(0u8);
        i = i + 1;
    }
    let mut b: u64 = 0;
    while b < 64
        invariant b <= 64, tab@.len() == 64,
        decreases 64 - b,
    {
        let h = (1u64 << b).wrapping_mul(DEBRUIJN64) >> 58u64;
        proof { lemma_shr58((1u64 << b).wrapping_mul(DEBRUIJN64)); }
        tab.set(h as usize, b as u8);
        b = b + 1;
    }
    tab
}

/// The top 6 bits of a word are below 64.
pub proof fn lemma_shr58(y: u64)
    ensures y >> 58u64 < 64,
{
    assert(y >> 58u64 < 64) by (bit_vector);
}

/// The index of the lowest set bit of `x != 0`.
#[inline(always)]
pub fn low_bit(x: u64, tab: &Vec<u8>) -> (r: u64)
    requires x != 0, tab@.len() == 64,
    ensures r < 64, bit(x, r), forall|u: u64| u < r ==> !#[trigger] bit(x, u),
    no_unwind
{
    proof {
        assert(x & sub(x, 1u64) <= x && sub(x, 1u64) == x - 1) by (bit_vector) requires x != 0;
    }
    let rest = x & (x - 1);
    let low = x - rest;
    let h = low.wrapping_mul(DEBRUIJN64) >> 58u64;
    proof { lemma_shr58(low.wrapping_mul(DEBRUIJN64)); }
    let r = tab[h as usize] as u64;
    if r < 64 && (x >> r) & 1u64 == 1u64 && (r == 0 || x << (64 - r) == 0) {
        proof {
            assert forall|u: u64| u < r implies !#[trigger] bit(x, u) by {
                assert(sub(64u64, r) == 64 - r);
                lemma_shl_low_zero(x, r, u);
            }
        }
        return r;
    }
    // not reached for a de Bruijn table: scan the bits
    let mut i: u64 = 0;
    while i < 64
        invariant x != 0, i <= 64, forall|u: u64| u < i ==> !#[trigger] bit(x, u),
        decreases 64 - i,
    {
        if (x >> i) & 1u64 == 1u64 {
            return i;
        }
        i = i + 1;
    }
    proof {
        lemma_tz(x);
        assert(bit(x, u64_trailing_zeros(x) as u64));
    }
    0
}

/// The highest set bit `r` of `x`, located by the smeared mask `sm` (every bit at or below it set): `sm ^ (sm >> 1)`
/// is the single bit `r`, and no bit of `x` lies above it.
pub proof fn lemma_high(x: u64, s1: u64, s2: u64, s3: u64, s4: u64, s5: u64, sm: u64, r: u64)
    requires
        r < 64,
        s1 == x | (x >> 1u64), s2 == s1 | (s1 >> 2u64), s3 == s2 | (s2 >> 4u64), s4 == s3 | (s3 >> 8u64),
        s5 == s4 | (s4 >> 16u64), sm == s5 | (s5 >> 32u64),
        bit(sm ^ (sm >> 1u64), r),
    ensures bit(x, r), forall|u: u64| r < u < 64 ==> !#[trigger] bit(x, u),
{
    assert((x >> r) & 1u64 == 1u64 && (x >> r) >> 1u64 == 0) by (bit_vector)
        requires
            r < 64,
            s1 == x | (x >> 1u64), s2 == s1 | (s1 >> 2u64), s3 == s2 | (s2 >> 4u64), s4 == s3 | (s3 >> 8u64),
            s5 == s4 | (s4 >> 16u64), sm == s5 | (s5 >> 32u64),
            ((sm ^ (sm >> 1u64)) >> r) & 1u64 == 1u64;
    assert forall|u: u64| r < u < 64 implies !#[trigger] bit(x, u) by {
        assert(!((x >> u) & 1u64 == 1u64)) by (bit_vector) requires r < u, u < 64, (x >> r) >> 1u64 == 0;
    }
}

/// The index of the highest set bit of `x != 0` (smear the bits down, isolate the top one, then `low_bit`).
#[inline(always)]
pub fn high_bit(x: u64, tab: &Vec<u8>) -> (r: u64)
    requires x != 0, tab@.len() == 64,
    ensures r < 64, bit(x, r), forall|u: u64| r < u < 64 ==> !#[trigger] bit(x, u),
    no_unwind
{
    let s1 = x | (x >> 1u64);
    let s2 = s1 | (s1 >> 2u64);
    let s3 = s2 | (s2 >> 4u64);
    let s4 = s3 | (s3 >> 8u64);
    let s5 = s4 | (s4 >> 16u64);
    let sm = s5 | (s5 >> 32u64);
    let top = sm ^ (sm >> 1u64);
    proof {
        assert(top != 0) by (bit_vector)
            requires
                x != 0,
                s1 == x | (x >> 1u64), s2 == s1 | (s1 >> 2u64), s3 == s2 | (s2 >> 4u64), s4 == s3 | (s3 >> 8u64),
                s5 == s4 | (s4 >> 16u64), sm == s5 | (s5 >> 32u64), top == sm ^ (sm >> 1u64);
    }
    let r = low_bit(top, tab);
    proof { lemma_high(x, s1, s2, s3, s4, s5, sm, r); }
    r
}

} // verus!
