//! Small bit sets in `u16` and `u64` words: membership (`bit16`, `bit64`), union by `|`, singletons `1 << c`, the
//! empty set 0.
use vstd::prelude::*;

verus! {

/// `b` is in the set `x` (`b < 16`).
pub open spec fn bit16(x: u16, b: u16) -> bool {
    (x >> b) & 1u16 == 1u16
}

/// `b` is in the set `x` (`b < 64`).
pub open spec fn bit64(x: u64, b: u64) -> bool {
    (x >> b) & 1u64 == 1u64
}

pub proof fn lemma_or16(x: u16, y: u16, b: u16)
    requires b < 16,
    ensures bit16(x | y, b) == (bit16(x, b) || bit16(y, b)),
{
    assert(((x | y) >> b) & 1u16 == 1u16 <==> ((x >> b) & 1u16 == 1u16 || (y >> b) & 1u16 == 1u16)) by (bit_vector)
        requires b < 16u16;
}

pub proof fn lemma_one16(c: u16, b: u16)
    requires c < 16, b < 16,
    ensures bit16(1u16 << c, b) == (b == c),
{
    assert(((1u16 << c) >> b) & 1u16 == 1u16 <==> b == c) by (bit_vector)
        requires c < 16u16, b < 16u16;
}

pub proof fn lemma_zero16(b: u16)
    requires b < 16,
    ensures !bit16(0u16, b),
{
    assert(!((0u16 >> b) & 1u16 == 1u16)) by (bit_vector)
        requires b < 16u16;
}

pub proof fn lemma_or64(x: u64, y: u64, b: u64)
    requires b < 64,
    ensures bit64(x | y, b) == (bit64(x, b) || bit64(y, b)),
{
    assert(((x | y) >> b) & 1u64 == 1u64 <==> ((x >> b) & 1u64 == 1u64 || (y >> b) & 1u64 == 1u64)) by (bit_vector)
        requires b < 64u64;
}

pub proof fn lemma_one64(c: u64, b: u64)
    requires c < 64, b < 64,
    ensures bit64(1u64 << c, b) == (b == c),
{
    assert(((1u64 << c) >> b) & 1u64 == 1u64 <==> b == c) by (bit_vector)
        requires c < 64u64, b < 64u64;
}

pub proof fn lemma_zero64(b: u64)
    requires b < 64,
    ensures !bit64(0u64, b),
{
    assert(!((0u64 >> b) & 1u64 == 1u64)) by (bit_vector)
        requires b < 64u64;
}

/// A `u16` set with no member at or above 16 is its members below 16 (stated for its zero test).
pub proof fn lemma_nonzero16(x: u16)
    requires x != 0,
    ensures exists|b: u16| b < 16 && #[trigger] bit16(x, b),
{
    if !(exists|b: u16| b < 16 && #[trigger] bit16(x, b)) {
        assert(bit16(x, 0) == false);
        assert(bit16(x, 1) == false);
        assert(bit16(x, 2) == false);
        assert(bit16(x, 3) == false);
        assert(bit16(x, 4) == false);
        assert(bit16(x, 5) == false);
        assert(bit16(x, 6) == false);
        assert(bit16(x, 7) == false);
        assert(bit16(x, 8) == false);
        assert(bit16(x, 9) == false);
        assert(bit16(x, 10) == false);
        assert(bit16(x, 11) == false);
        assert(bit16(x, 12) == false);
        assert(bit16(x, 13) == false);
        assert(bit16(x, 14) == false);
        assert(bit16(x, 15) == false);
        assert(x == 0u16) by (bit_vector)
            requires
                (x >> 0u16) & 1u16 != 1u16, (x >> 1u16) & 1u16 != 1u16, (x >> 2u16) & 1u16 != 1u16,
                (x >> 3u16) & 1u16 != 1u16, (x >> 4u16) & 1u16 != 1u16, (x >> 5u16) & 1u16 != 1u16,
                (x >> 6u16) & 1u16 != 1u16, (x >> 7u16) & 1u16 != 1u16, (x >> 8u16) & 1u16 != 1u16,
                (x >> 9u16) & 1u16 != 1u16, (x >> 10u16) & 1u16 != 1u16, (x >> 11u16) & 1u16 != 1u16,
                (x >> 12u16) & 1u16 != 1u16, (x >> 13u16) & 1u16 != 1u16, (x >> 14u16) & 1u16 != 1u16,
                (x >> 15u16) & 1u16 != 1u16;
    }
}

} // verus!
