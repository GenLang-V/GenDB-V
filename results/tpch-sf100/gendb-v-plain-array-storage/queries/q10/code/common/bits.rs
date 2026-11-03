//! Bit-level facts about 64-bit masks (one bit per row of a 64-row block): setting a bit, clearing the lowest set
//! bit and the first set bit (`trailing_zeros`).
//! Each fact is one small `bit_vector` lemma, stated for a single bit position.
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

} // verus!
