//! Index of the lowest set bit of a nonzero `u64`, branch-free and `no_unwind` (the bit-count intrinsics such as
//! `trailing_zeros` are not `no_unwind` in the pinned vstd, so worker tasks cannot call them): isolate the bit with
//! `m ^ (m & (m - 1))`, then read its index off six masks (binary decomposition).
use vstd::prelude::*;

verus! {

/// Bit `i` of `m` (`0 <= i < 64`).
pub open spec fn bit_at(m: u64, i: int) -> bool {
    ((m >> (i as u64)) & 1u64) == 1u64
}

/// The index read off the isolated lowest bit `low`.
pub open spec fn index_of(low: u64) -> u64 {
    (if low & 0xFFFF_FFFF_0000_0000u64 != 0 { 32u64 } else { 0u64 })
    | (if low & 0xFFFF_0000_FFFF_0000u64 != 0 { 16u64 } else { 0u64 })
    | (if low & 0xFF00_FF00_FF00_FF00u64 != 0 { 8u64 } else { 0u64 })
    | (if low & 0xF0F0_F0F0_F0F0_F0F0u64 != 0 { 4u64 } else { 0u64 })
    | (if low & 0xCCCC_CCCC_CCCC_CCCCu64 != 0 { 2u64 } else { 0u64 })
    | (if low & 0xAAAA_AAAA_AAAA_AAAAu64 != 0 { 1u64 } else { 0u64 })
}

/// The decomposition finds the lowest set bit: it is set, and every bit below it is clear.
proof fn lemma_index_of(m: u64)
    requires m != 0,
    ensures
        index_of(m ^ (m & sub(m, 1u64))) < 64,
        (m >> index_of(m ^ (m & sub(m, 1u64)))) & 1u64 == 1u64,
        m & sub(1u64 << index_of(m ^ (m & sub(m, 1u64))), 1u64) == 0u64,
{
    assert(index_of(m ^ (m & sub(m, 1u64))) < 64) by (bit_vector) requires m != 0;
    assert((m >> index_of(m ^ (m & sub(m, 1u64)))) & 1u64 == 1u64) by (bit_vector) requires m != 0;
    assert(m & sub(1u64 << index_of(m ^ (m & sub(m, 1u64))), 1u64) == 0u64) by (bit_vector) requires m != 0;
}

/// Bits below `t` of a word whose low `t` bits are clear are clear.
proof fn lemma_low_clear(m: u64, t: u64, j: u64)
    requires t < 64, j < t, m & sub(1u64 << t, 1u64) == 0u64,
    ensures (m >> j) & 1u64 == 0u64,
{
    assert((m >> j) & 1u64 == 0u64) by (bit_vector) requires t < 64, j < t, m & sub(1u64 << t, 1u64) == 0u64;
}

/// The index of the lowest set bit of `m`.
#[inline(always)]
pub fn low_bit(m: u64) -> (t: u64)
    requires m != 0,
    ensures
        t < 64,
        bit_at(m, t as int),
        forall|j: int| 0 <= j < t ==> !#[trigger] bit_at(m, j),
    no_unwind
{
    let low = m ^ (m & (m - 1));
    let t: u64 = (if low & 0xFFFF_FFFF_0000_0000u64 != 0 { 32u64 } else { 0u64 })
        | (if low & 0xFFFF_0000_FFFF_0000u64 != 0 { 16u64 } else { 0u64 })
        | (if low & 0xFF00_FF00_FF00_FF00u64 != 0 { 8u64 } else { 0u64 })
        | (if low & 0xF0F0_F0F0_F0F0_F0F0u64 != 0 { 4u64 } else { 0u64 })
        | (if low & 0xCCCC_CCCC_CCCC_CCCCu64 != 0 { 2u64 } else { 0u64 })
        | (if low & 0xAAAA_AAAA_AAAA_AAAAu64 != 0 { 1u64 } else { 0u64 });
    proof {
        assert(m - 1 == sub(m, 1u64));
        assert(t == index_of(m ^ (m & sub(m, 1u64))));
        lemma_index_of(m);
        assert forall|j: int| 0 <= j < t implies !#[trigger] bit_at(m, j) by {
            lemma_low_clear(m, t, j as u64);
        }
    }
    t
}

} // verus!
