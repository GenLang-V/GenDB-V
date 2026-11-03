//! `trailing_zeros` of a non-zero `u64` without the intrinsic (whose pinned vstd specification may unwind, so worker
//! bodies cannot call it): isolate the lowest set bit, multiply by the de Bruijn constant `0x03f79d71b4cb0a89`, and
//! map the top 6 bits to the bit position (`TZ_TABLE`, a constant table, which LLVM compiles to `tzcnt`). The map is proved
//! for each of the 64 single-bit words (`lemma_debruijn`, one `bit_vector` fact per position), so nothing is checked
//! at run time.
use vstd::prelude::*;
use vstd::std_specs::bits::{u64_trailing_zeros, axiom_u64_trailing_zeros};
use crate::agent::common::bitset::*;

verus! {

pub const DEBRUIJN: u64 = 0x03f7_9d71_b4cb_0a89;

/// The bit position of de Bruijn index `h` (the top 6 bits of `(1 << k) * DEBRUIJN` for `k < 64`).
pub open spec fn tz_index(h: u64) -> u64 {
    match h {
        0 => 0,
        1 => 1,
        2 => 48,
        3 => 2,
        4 => 57,
        5 => 49,
        6 => 28,
        7 => 3,
        8 => 61,
        9 => 58,
        10 => 50,
        11 => 42,
        12 => 38,
        13 => 29,
        14 => 17,
        15 => 4,
        16 => 62,
        17 => 55,
        18 => 59,
        19 => 36,
        20 => 53,
        21 => 51,
        22 => 43,
        23 => 22,
        24 => 45,
        25 => 39,
        26 => 33,
        27 => 30,
        28 => 24,
        29 => 18,
        30 => 12,
        31 => 5,
        32 => 63,
        33 => 47,
        34 => 56,
        35 => 27,
        36 => 60,
        37 => 41,
        38 => 37,
        39 => 16,
        40 => 54,
        41 => 35,
        42 => 52,
        43 => 21,
        44 => 44,
        45 => 32,
        46 => 23,
        47 => 11,
        48 => 46,
        49 => 26,
        50 => 40,
        51 => 15,
        52 => 34,
        53 => 20,
        54 => 31,
        55 => 10,
        56 => 25,
        57 => 14,
        58 => 19,
        59 => 9,
        60 => 13,
        61 => 8,
        62 => 7,
        63 => 6,
        _ => 0,
    }
}

/// `tz_index` as a constant table (`TZ_TABLE[h] == tz_index(h)` for `h < 64`, `lemma_tz_table`). A lookup into a
/// constant table indexed by the de Bruijn product is what LLVM recognizes and compiles to one `tzcnt`.
pub const TZ_TABLE: [u8; 64] = [0, 1, 48, 2, 57, 49, 28, 3, 61, 58, 50, 42, 38, 29, 17, 4, 62, 55, 59, 36, 53, 51, 43, 22, 45, 39, 33, 30, 24, 18, 12, 5, 63, 47, 56, 27, 60, 41, 37, 16, 54, 35, 52, 21, 44, 32, 23, 11, 46, 26, 40, 15, 34, 20, 31, 10, 25, 14, 19, 9, 13, 8, 7, 6];

/// The table entry of every de Bruijn index is `tz_index`.
pub proof fn lemma_tz_table(h: u64)
    requires h < 64,
    ensures TZ_TABLE@[h as int] as u64 == tz_index(h),
{
    if h == 0u64 {
        assert(TZ_TABLE@[0] as u64 == tz_index(0u64));
    } else if h == 1u64 {
        assert(TZ_TABLE@[1] as u64 == tz_index(1u64));
    } else if h == 2u64 {
        assert(TZ_TABLE@[2] as u64 == tz_index(2u64));
    } else if h == 3u64 {
        assert(TZ_TABLE@[3] as u64 == tz_index(3u64));
    } else if h == 4u64 {
        assert(TZ_TABLE@[4] as u64 == tz_index(4u64));
    } else if h == 5u64 {
        assert(TZ_TABLE@[5] as u64 == tz_index(5u64));
    } else if h == 6u64 {
        assert(TZ_TABLE@[6] as u64 == tz_index(6u64));
    } else if h == 7u64 {
        assert(TZ_TABLE@[7] as u64 == tz_index(7u64));
    } else if h == 8u64 {
        assert(TZ_TABLE@[8] as u64 == tz_index(8u64));
    } else if h == 9u64 {
        assert(TZ_TABLE@[9] as u64 == tz_index(9u64));
    } else if h == 10u64 {
        assert(TZ_TABLE@[10] as u64 == tz_index(10u64));
    } else if h == 11u64 {
        assert(TZ_TABLE@[11] as u64 == tz_index(11u64));
    } else if h == 12u64 {
        assert(TZ_TABLE@[12] as u64 == tz_index(12u64));
    } else if h == 13u64 {
        assert(TZ_TABLE@[13] as u64 == tz_index(13u64));
    } else if h == 14u64 {
        assert(TZ_TABLE@[14] as u64 == tz_index(14u64));
    } else if h == 15u64 {
        assert(TZ_TABLE@[15] as u64 == tz_index(15u64));
    } else if h == 16u64 {
        assert(TZ_TABLE@[16] as u64 == tz_index(16u64));
    } else if h == 17u64 {
        assert(TZ_TABLE@[17] as u64 == tz_index(17u64));
    } else if h == 18u64 {
        assert(TZ_TABLE@[18] as u64 == tz_index(18u64));
    } else if h == 19u64 {
        assert(TZ_TABLE@[19] as u64 == tz_index(19u64));
    } else if h == 20u64 {
        assert(TZ_TABLE@[20] as u64 == tz_index(20u64));
    } else if h == 21u64 {
        assert(TZ_TABLE@[21] as u64 == tz_index(21u64));
    } else if h == 22u64 {
        assert(TZ_TABLE@[22] as u64 == tz_index(22u64));
    } else if h == 23u64 {
        assert(TZ_TABLE@[23] as u64 == tz_index(23u64));
    } else if h == 24u64 {
        assert(TZ_TABLE@[24] as u64 == tz_index(24u64));
    } else if h == 25u64 {
        assert(TZ_TABLE@[25] as u64 == tz_index(25u64));
    } else if h == 26u64 {
        assert(TZ_TABLE@[26] as u64 == tz_index(26u64));
    } else if h == 27u64 {
        assert(TZ_TABLE@[27] as u64 == tz_index(27u64));
    } else if h == 28u64 {
        assert(TZ_TABLE@[28] as u64 == tz_index(28u64));
    } else if h == 29u64 {
        assert(TZ_TABLE@[29] as u64 == tz_index(29u64));
    } else if h == 30u64 {
        assert(TZ_TABLE@[30] as u64 == tz_index(30u64));
    } else if h == 31u64 {
        assert(TZ_TABLE@[31] as u64 == tz_index(31u64));
    } else if h == 32u64 {
        assert(TZ_TABLE@[32] as u64 == tz_index(32u64));
    } else if h == 33u64 {
        assert(TZ_TABLE@[33] as u64 == tz_index(33u64));
    } else if h == 34u64 {
        assert(TZ_TABLE@[34] as u64 == tz_index(34u64));
    } else if h == 35u64 {
        assert(TZ_TABLE@[35] as u64 == tz_index(35u64));
    } else if h == 36u64 {
        assert(TZ_TABLE@[36] as u64 == tz_index(36u64));
    } else if h == 37u64 {
        assert(TZ_TABLE@[37] as u64 == tz_index(37u64));
    } else if h == 38u64 {
        assert(TZ_TABLE@[38] as u64 == tz_index(38u64));
    } else if h == 39u64 {
        assert(TZ_TABLE@[39] as u64 == tz_index(39u64));
    } else if h == 40u64 {
        assert(TZ_TABLE@[40] as u64 == tz_index(40u64));
    } else if h == 41u64 {
        assert(TZ_TABLE@[41] as u64 == tz_index(41u64));
    } else if h == 42u64 {
        assert(TZ_TABLE@[42] as u64 == tz_index(42u64));
    } else if h == 43u64 {
        assert(TZ_TABLE@[43] as u64 == tz_index(43u64));
    } else if h == 44u64 {
        assert(TZ_TABLE@[44] as u64 == tz_index(44u64));
    } else if h == 45u64 {
        assert(TZ_TABLE@[45] as u64 == tz_index(45u64));
    } else if h == 46u64 {
        assert(TZ_TABLE@[46] as u64 == tz_index(46u64));
    } else if h == 47u64 {
        assert(TZ_TABLE@[47] as u64 == tz_index(47u64));
    } else if h == 48u64 {
        assert(TZ_TABLE@[48] as u64 == tz_index(48u64));
    } else if h == 49u64 {
        assert(TZ_TABLE@[49] as u64 == tz_index(49u64));
    } else if h == 50u64 {
        assert(TZ_TABLE@[50] as u64 == tz_index(50u64));
    } else if h == 51u64 {
        assert(TZ_TABLE@[51] as u64 == tz_index(51u64));
    } else if h == 52u64 {
        assert(TZ_TABLE@[52] as u64 == tz_index(52u64));
    } else if h == 53u64 {
        assert(TZ_TABLE@[53] as u64 == tz_index(53u64));
    } else if h == 54u64 {
        assert(TZ_TABLE@[54] as u64 == tz_index(54u64));
    } else if h == 55u64 {
        assert(TZ_TABLE@[55] as u64 == tz_index(55u64));
    } else if h == 56u64 {
        assert(TZ_TABLE@[56] as u64 == tz_index(56u64));
    } else if h == 57u64 {
        assert(TZ_TABLE@[57] as u64 == tz_index(57u64));
    } else if h == 58u64 {
        assert(TZ_TABLE@[58] as u64 == tz_index(58u64));
    } else if h == 59u64 {
        assert(TZ_TABLE@[59] as u64 == tz_index(59u64));
    } else if h == 60u64 {
        assert(TZ_TABLE@[60] as u64 == tz_index(60u64));
    } else if h == 61u64 {
        assert(TZ_TABLE@[61] as u64 == tz_index(61u64));
    } else if h == 62u64 {
        assert(TZ_TABLE@[62] as u64 == tz_index(62u64));
    } else if h == 63u64 {
        assert(TZ_TABLE@[63] as u64 == tz_index(63u64));
    }
}

/// The de Bruijn index of the single bit `k` maps back to `k`.
pub proof fn lemma_debruijn(k: u64)
    requires k < 64,
    ensures tz_index((1u64 << k).wrapping_mul(DEBRUIJN) >> 58u64) == k,
{
    if k == 0u64 {
        assert((1u64 << 0u64).wrapping_mul(DEBRUIJN) >> 58u64 == 0u64) by (bit_vector);
    } else if k == 1u64 {
        assert((1u64 << 1u64).wrapping_mul(DEBRUIJN) >> 58u64 == 1u64) by (bit_vector);
    } else if k == 2u64 {
        assert((1u64 << 2u64).wrapping_mul(DEBRUIJN) >> 58u64 == 3u64) by (bit_vector);
    } else if k == 3u64 {
        assert((1u64 << 3u64).wrapping_mul(DEBRUIJN) >> 58u64 == 7u64) by (bit_vector);
    } else if k == 4u64 {
        assert((1u64 << 4u64).wrapping_mul(DEBRUIJN) >> 58u64 == 15u64) by (bit_vector);
    } else if k == 5u64 {
        assert((1u64 << 5u64).wrapping_mul(DEBRUIJN) >> 58u64 == 31u64) by (bit_vector);
    } else if k == 6u64 {
        assert((1u64 << 6u64).wrapping_mul(DEBRUIJN) >> 58u64 == 63u64) by (bit_vector);
    } else if k == 7u64 {
        assert((1u64 << 7u64).wrapping_mul(DEBRUIJN) >> 58u64 == 62u64) by (bit_vector);
    } else if k == 8u64 {
        assert((1u64 << 8u64).wrapping_mul(DEBRUIJN) >> 58u64 == 61u64) by (bit_vector);
    } else if k == 9u64 {
        assert((1u64 << 9u64).wrapping_mul(DEBRUIJN) >> 58u64 == 59u64) by (bit_vector);
    } else if k == 10u64 {
        assert((1u64 << 10u64).wrapping_mul(DEBRUIJN) >> 58u64 == 55u64) by (bit_vector);
    } else if k == 11u64 {
        assert((1u64 << 11u64).wrapping_mul(DEBRUIJN) >> 58u64 == 47u64) by (bit_vector);
    } else if k == 12u64 {
        assert((1u64 << 12u64).wrapping_mul(DEBRUIJN) >> 58u64 == 30u64) by (bit_vector);
    } else if k == 13u64 {
        assert((1u64 << 13u64).wrapping_mul(DEBRUIJN) >> 58u64 == 60u64) by (bit_vector);
    } else if k == 14u64 {
        assert((1u64 << 14u64).wrapping_mul(DEBRUIJN) >> 58u64 == 57u64) by (bit_vector);
    } else if k == 15u64 {
        assert((1u64 << 15u64).wrapping_mul(DEBRUIJN) >> 58u64 == 51u64) by (bit_vector);
    } else if k == 16u64 {
        assert((1u64 << 16u64).wrapping_mul(DEBRUIJN) >> 58u64 == 39u64) by (bit_vector);
    } else if k == 17u64 {
        assert((1u64 << 17u64).wrapping_mul(DEBRUIJN) >> 58u64 == 14u64) by (bit_vector);
    } else if k == 18u64 {
        assert((1u64 << 18u64).wrapping_mul(DEBRUIJN) >> 58u64 == 29u64) by (bit_vector);
    } else if k == 19u64 {
        assert((1u64 << 19u64).wrapping_mul(DEBRUIJN) >> 58u64 == 58u64) by (bit_vector);
    } else if k == 20u64 {
        assert((1u64 << 20u64).wrapping_mul(DEBRUIJN) >> 58u64 == 53u64) by (bit_vector);
    } else if k == 21u64 {
        assert((1u64 << 21u64).wrapping_mul(DEBRUIJN) >> 58u64 == 43u64) by (bit_vector);
    } else if k == 22u64 {
        assert((1u64 << 22u64).wrapping_mul(DEBRUIJN) >> 58u64 == 23u64) by (bit_vector);
    } else if k == 23u64 {
        assert((1u64 << 23u64).wrapping_mul(DEBRUIJN) >> 58u64 == 46u64) by (bit_vector);
    } else if k == 24u64 {
        assert((1u64 << 24u64).wrapping_mul(DEBRUIJN) >> 58u64 == 28u64) by (bit_vector);
    } else if k == 25u64 {
        assert((1u64 << 25u64).wrapping_mul(DEBRUIJN) >> 58u64 == 56u64) by (bit_vector);
    } else if k == 26u64 {
        assert((1u64 << 26u64).wrapping_mul(DEBRUIJN) >> 58u64 == 49u64) by (bit_vector);
    } else if k == 27u64 {
        assert((1u64 << 27u64).wrapping_mul(DEBRUIJN) >> 58u64 == 35u64) by (bit_vector);
    } else if k == 28u64 {
        assert((1u64 << 28u64).wrapping_mul(DEBRUIJN) >> 58u64 == 6u64) by (bit_vector);
    } else if k == 29u64 {
        assert((1u64 << 29u64).wrapping_mul(DEBRUIJN) >> 58u64 == 13u64) by (bit_vector);
    } else if k == 30u64 {
        assert((1u64 << 30u64).wrapping_mul(DEBRUIJN) >> 58u64 == 27u64) by (bit_vector);
    } else if k == 31u64 {
        assert((1u64 << 31u64).wrapping_mul(DEBRUIJN) >> 58u64 == 54u64) by (bit_vector);
    } else if k == 32u64 {
        assert((1u64 << 32u64).wrapping_mul(DEBRUIJN) >> 58u64 == 45u64) by (bit_vector);
    } else if k == 33u64 {
        assert((1u64 << 33u64).wrapping_mul(DEBRUIJN) >> 58u64 == 26u64) by (bit_vector);
    } else if k == 34u64 {
        assert((1u64 << 34u64).wrapping_mul(DEBRUIJN) >> 58u64 == 52u64) by (bit_vector);
    } else if k == 35u64 {
        assert((1u64 << 35u64).wrapping_mul(DEBRUIJN) >> 58u64 == 41u64) by (bit_vector);
    } else if k == 36u64 {
        assert((1u64 << 36u64).wrapping_mul(DEBRUIJN) >> 58u64 == 19u64) by (bit_vector);
    } else if k == 37u64 {
        assert((1u64 << 37u64).wrapping_mul(DEBRUIJN) >> 58u64 == 38u64) by (bit_vector);
    } else if k == 38u64 {
        assert((1u64 << 38u64).wrapping_mul(DEBRUIJN) >> 58u64 == 12u64) by (bit_vector);
    } else if k == 39u64 {
        assert((1u64 << 39u64).wrapping_mul(DEBRUIJN) >> 58u64 == 25u64) by (bit_vector);
    } else if k == 40u64 {
        assert((1u64 << 40u64).wrapping_mul(DEBRUIJN) >> 58u64 == 50u64) by (bit_vector);
    } else if k == 41u64 {
        assert((1u64 << 41u64).wrapping_mul(DEBRUIJN) >> 58u64 == 37u64) by (bit_vector);
    } else if k == 42u64 {
        assert((1u64 << 42u64).wrapping_mul(DEBRUIJN) >> 58u64 == 11u64) by (bit_vector);
    } else if k == 43u64 {
        assert((1u64 << 43u64).wrapping_mul(DEBRUIJN) >> 58u64 == 22u64) by (bit_vector);
    } else if k == 44u64 {
        assert((1u64 << 44u64).wrapping_mul(DEBRUIJN) >> 58u64 == 44u64) by (bit_vector);
    } else if k == 45u64 {
        assert((1u64 << 45u64).wrapping_mul(DEBRUIJN) >> 58u64 == 24u64) by (bit_vector);
    } else if k == 46u64 {
        assert((1u64 << 46u64).wrapping_mul(DEBRUIJN) >> 58u64 == 48u64) by (bit_vector);
    } else if k == 47u64 {
        assert((1u64 << 47u64).wrapping_mul(DEBRUIJN) >> 58u64 == 33u64) by (bit_vector);
    } else if k == 48u64 {
        assert((1u64 << 48u64).wrapping_mul(DEBRUIJN) >> 58u64 == 2u64) by (bit_vector);
    } else if k == 49u64 {
        assert((1u64 << 49u64).wrapping_mul(DEBRUIJN) >> 58u64 == 5u64) by (bit_vector);
    } else if k == 50u64 {
        assert((1u64 << 50u64).wrapping_mul(DEBRUIJN) >> 58u64 == 10u64) by (bit_vector);
    } else if k == 51u64 {
        assert((1u64 << 51u64).wrapping_mul(DEBRUIJN) >> 58u64 == 21u64) by (bit_vector);
    } else if k == 52u64 {
        assert((1u64 << 52u64).wrapping_mul(DEBRUIJN) >> 58u64 == 42u64) by (bit_vector);
    } else if k == 53u64 {
        assert((1u64 << 53u64).wrapping_mul(DEBRUIJN) >> 58u64 == 20u64) by (bit_vector);
    } else if k == 54u64 {
        assert((1u64 << 54u64).wrapping_mul(DEBRUIJN) >> 58u64 == 40u64) by (bit_vector);
    } else if k == 55u64 {
        assert((1u64 << 55u64).wrapping_mul(DEBRUIJN) >> 58u64 == 17u64) by (bit_vector);
    } else if k == 56u64 {
        assert((1u64 << 56u64).wrapping_mul(DEBRUIJN) >> 58u64 == 34u64) by (bit_vector);
    } else if k == 57u64 {
        assert((1u64 << 57u64).wrapping_mul(DEBRUIJN) >> 58u64 == 4u64) by (bit_vector);
    } else if k == 58u64 {
        assert((1u64 << 58u64).wrapping_mul(DEBRUIJN) >> 58u64 == 9u64) by (bit_vector);
    } else if k == 59u64 {
        assert((1u64 << 59u64).wrapping_mul(DEBRUIJN) >> 58u64 == 18u64) by (bit_vector);
    } else if k == 60u64 {
        assert((1u64 << 60u64).wrapping_mul(DEBRUIJN) >> 58u64 == 36u64) by (bit_vector);
    } else if k == 61u64 {
        assert((1u64 << 61u64).wrapping_mul(DEBRUIJN) >> 58u64 == 8u64) by (bit_vector);
    } else if k == 62u64 {
        assert((1u64 << 62u64).wrapping_mul(DEBRUIJN) >> 58u64 == 16u64) by (bit_vector);
    } else if k == 63u64 {
        assert((1u64 << 63u64).wrapping_mul(DEBRUIJN) >> 58u64 == 32u64) by (bit_vector);
    }
}

/// The lowest set bit of `c`, isolated, is `1 << tz(c)`.
pub proof fn lemma_isolate(c: u64)
    requires c != 0,
    ensures c & (!c).wrapping_add(1) == (1u64 << (u64_trailing_zeros(c) as u64)),
{
    axiom_u64_trailing_zeros(c);
    let k = u64_trailing_zeros(c) as u64;
    assert(k < 64);
    assert((c >> k) & 1u64 == 1u64);
    lemma_low_bits_zero_tz(c, k);
    assert((c != 0 && k < 64 && (c >> k) & 1u64 == 1u64 && c & sub(sub(1u64 << k, 1), 0) == 0u64) ==>
        c & add(!c, 1) == (1u64 << k)) by (bit_vector);
    assert((!c).wrapping_add(1) == add(!c, 1)) by (bit_vector);
}

proof fn lemma_low_bits_zero_tz(c: u64, k: u64)
    requires c != 0, k == u64_trailing_zeros(c) as u64, k < 64,
    ensures c & sub(sub(1u64 << k, 1), 0) == 0u64,
{
    axiom_u64_trailing_zeros(c);
    assert forall|v: u64| v < k implies !#[trigger] bit(c, v) by {
        assert((c >> v) & 1u64 == 0u64);
    }
    lemma_low_bits_zero(c, k);
}

/// `trailing_zeros` of a non-zero mask, `no_unwind`.
#[inline(always)]
pub fn tz64(c: u64) -> (r: u32)
    requires c != 0,
    ensures r == u64_trailing_zeros(c), r < 64,
    no_unwind
{
    proof {
        lemma_isolate(c);
        axiom_u64_trailing_zeros(c);
        lemma_debruijn(u64_trailing_zeros(c) as u64);
    }
    let low = c & (!c).wrapping_add(1);
    let h = low.wrapping_mul(DEBRUIJN) >> 58u64;
    proof {
        assert(low.wrapping_mul(DEBRUIJN) >> 58u64 < 64u64) by (bit_vector);
        lemma_tz_table(h);
    }
    TZ_TABLE[h as usize] as u32
}

} // verus!
