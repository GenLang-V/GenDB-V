//! Population count of a `u64` word, verified: the SWAR form (byte counts, then one multiply that sums the bytes),
//! which LLVM compiles to one `popcnt`, equals the number of set lanes (`cnt_lanes`); with the low-lane mask
//! `low_mask(t)` (lanes `0..=t`), `popcount(x & low_mask(t))` counts the set lanes of `x` up to lane `t` (a rank).
use vstd::prelude::*;
use super::bits::lane;

verus! {

/// Number of set lanes of `x` below lane `k`.
pub open spec fn cnt_lanes(x: u64, k: int) -> int
    decreases k,
{
    if k <= 0 { 0 } else { cnt_lanes(x, k - 1) + if lane(x, k - 1) { 1int } else { 0int } }
}

/// Bit `i` of `x` as a number (0 or 1).
pub open spec fn b(x: u64, i: u64) -> u64 {
    (x >> i) & 1u64
}

/// The SWAR byte counts of `x`: byte `k` holds the number of set bits of byte `k` of `x`.
pub open spec fn swar_bytes(x: u64) -> u64 {
    let a = (x - ((x >> 1u64) & 0x5555_5555_5555_5555u64)) as u64;
    let bb = ((a & 0x3333_3333_3333_3333u64) + ((a >> 2u64) & 0x3333_3333_3333_3333u64)) as u64;
    ((bb + (bb >> 4u64)) as u64) & 0x0f0f_0f0f_0f0f_0f0fu64
}

/// Byte 0 of the SWAR byte counts is the number of set bits of byte 0 of `x`.
proof fn lemma_byte0(x: u64)
    ensures (swar_bytes(x) >> 0u64) & 0xffu64 == b(x, 0) + b(x, 1) + b(x, 2) + b(x, 3) + b(x, 4) + b(x, 5) + b(x, 6) + b(x, 7),
{
    assert((swar_bytes(x) >> 0u64) & 0xffu64 == ((x >> 0u64) & 1u64) + ((x >> 1u64) & 1u64) + ((x >> 2u64) & 1u64) + ((x >> 3u64) & 1u64) + ((x >> 4u64) & 1u64) + ((x >> 5u64) & 1u64) + ((x >> 6u64) & 1u64) + ((x >> 7u64) & 1u64)) by (bit_vector);
}
/// Byte 1 of the SWAR byte counts is the number of set bits of byte 1 of `x`.
proof fn lemma_byte1(x: u64)
    ensures (swar_bytes(x) >> 8u64) & 0xffu64 == b(x, 8) + b(x, 9) + b(x, 10) + b(x, 11) + b(x, 12) + b(x, 13) + b(x, 14) + b(x, 15),
{
    assert((swar_bytes(x) >> 8u64) & 0xffu64 == ((x >> 8u64) & 1u64) + ((x >> 9u64) & 1u64) + ((x >> 10u64) & 1u64) + ((x >> 11u64) & 1u64) + ((x >> 12u64) & 1u64) + ((x >> 13u64) & 1u64) + ((x >> 14u64) & 1u64) + ((x >> 15u64) & 1u64)) by (bit_vector);
}
/// Byte 2 of the SWAR byte counts is the number of set bits of byte 2 of `x`.
proof fn lemma_byte2(x: u64)
    ensures (swar_bytes(x) >> 16u64) & 0xffu64 == b(x, 16) + b(x, 17) + b(x, 18) + b(x, 19) + b(x, 20) + b(x, 21) + b(x, 22) + b(x, 23),
{
    assert((swar_bytes(x) >> 16u64) & 0xffu64 == ((x >> 16u64) & 1u64) + ((x >> 17u64) & 1u64) + ((x >> 18u64) & 1u64) + ((x >> 19u64) & 1u64) + ((x >> 20u64) & 1u64) + ((x >> 21u64) & 1u64) + ((x >> 22u64) & 1u64) + ((x >> 23u64) & 1u64)) by (bit_vector);
}
/// Byte 3 of the SWAR byte counts is the number of set bits of byte 3 of `x`.
proof fn lemma_byte3(x: u64)
    ensures (swar_bytes(x) >> 24u64) & 0xffu64 == b(x, 24) + b(x, 25) + b(x, 26) + b(x, 27) + b(x, 28) + b(x, 29) + b(x, 30) + b(x, 31),
{
    assert((swar_bytes(x) >> 24u64) & 0xffu64 == ((x >> 24u64) & 1u64) + ((x >> 25u64) & 1u64) + ((x >> 26u64) & 1u64) + ((x >> 27u64) & 1u64) + ((x >> 28u64) & 1u64) + ((x >> 29u64) & 1u64) + ((x >> 30u64) & 1u64) + ((x >> 31u64) & 1u64)) by (bit_vector);
}
/// Byte 4 of the SWAR byte counts is the number of set bits of byte 4 of `x`.
proof fn lemma_byte4(x: u64)
    ensures (swar_bytes(x) >> 32u64) & 0xffu64 == b(x, 32) + b(x, 33) + b(x, 34) + b(x, 35) + b(x, 36) + b(x, 37) + b(x, 38) + b(x, 39),
{
    assert((swar_bytes(x) >> 32u64) & 0xffu64 == ((x >> 32u64) & 1u64) + ((x >> 33u64) & 1u64) + ((x >> 34u64) & 1u64) + ((x >> 35u64) & 1u64) + ((x >> 36u64) & 1u64) + ((x >> 37u64) & 1u64) + ((x >> 38u64) & 1u64) + ((x >> 39u64) & 1u64)) by (bit_vector);
}
/// Byte 5 of the SWAR byte counts is the number of set bits of byte 5 of `x`.
proof fn lemma_byte5(x: u64)
    ensures (swar_bytes(x) >> 40u64) & 0xffu64 == b(x, 40) + b(x, 41) + b(x, 42) + b(x, 43) + b(x, 44) + b(x, 45) + b(x, 46) + b(x, 47),
{
    assert((swar_bytes(x) >> 40u64) & 0xffu64 == ((x >> 40u64) & 1u64) + ((x >> 41u64) & 1u64) + ((x >> 42u64) & 1u64) + ((x >> 43u64) & 1u64) + ((x >> 44u64) & 1u64) + ((x >> 45u64) & 1u64) + ((x >> 46u64) & 1u64) + ((x >> 47u64) & 1u64)) by (bit_vector);
}
/// Byte 6 of the SWAR byte counts is the number of set bits of byte 6 of `x`.
proof fn lemma_byte6(x: u64)
    ensures (swar_bytes(x) >> 48u64) & 0xffu64 == b(x, 48) + b(x, 49) + b(x, 50) + b(x, 51) + b(x, 52) + b(x, 53) + b(x, 54) + b(x, 55),
{
    assert((swar_bytes(x) >> 48u64) & 0xffu64 == ((x >> 48u64) & 1u64) + ((x >> 49u64) & 1u64) + ((x >> 50u64) & 1u64) + ((x >> 51u64) & 1u64) + ((x >> 52u64) & 1u64) + ((x >> 53u64) & 1u64) + ((x >> 54u64) & 1u64) + ((x >> 55u64) & 1u64)) by (bit_vector);
}
/// Byte 7 of the SWAR byte counts is the number of set bits of byte 7 of `x`.
proof fn lemma_byte7(x: u64)
    ensures (swar_bytes(x) >> 56u64) & 0xffu64 == b(x, 56) + b(x, 57) + b(x, 58) + b(x, 59) + b(x, 60) + b(x, 61) + b(x, 62) + b(x, 63),
{
    assert((swar_bytes(x) >> 56u64) & 0xffu64 == ((x >> 56u64) & 1u64) + ((x >> 57u64) & 1u64) + ((x >> 58u64) & 1u64) + ((x >> 59u64) & 1u64) + ((x >> 60u64) & 1u64) + ((x >> 61u64) & 1u64) + ((x >> 62u64) & 1u64) + ((x >> 63u64) & 1u64)) by (bit_vector);
}

/// The multiply by `0x0101..01` sums the bytes into the top byte when each byte is at most 8.
proof fn lemma_byte_sum(c: u64)
    requires (c >> 0u64) & 0xffu64 <= 8, (c >> 8u64) & 0xffu64 <= 8, (c >> 16u64) & 0xffu64 <= 8, (c >> 24u64) & 0xffu64 <= 8, (c >> 32u64) & 0xffu64 <= 8, (c >> 40u64) & 0xffu64 <= 8, (c >> 48u64) & 0xffu64 <= 8, (c >> 56u64) & 0xffu64 <= 8,
    ensures c.wrapping_mul(0x0101_0101_0101_0101u64) >> 56u64 == ((c >> 0u64) & 0xffu64) + ((c >> 8u64) & 0xffu64) + ((c >> 16u64) & 0xffu64) + ((c >> 24u64) & 0xffu64) + ((c >> 32u64) & 0xffu64) + ((c >> 40u64) & 0xffu64) + ((c >> 48u64) & 0xffu64) + ((c >> 56u64) & 0xffu64),
{
    assert(c.wrapping_mul(0x0101_0101_0101_0101u64) >> 56u64 == ((c >> 0u64) & 0xffu64) + ((c >> 8u64) & 0xffu64) + ((c >> 16u64) & 0xffu64) + ((c >> 24u64) & 0xffu64) + ((c >> 32u64) & 0xffu64) + ((c >> 40u64) & 0xffu64) + ((c >> 48u64) & 0xffu64) + ((c >> 56u64) & 0xffu64)) by (bit_vector)
        requires (c >> 0u64) & 0xffu64 <= 8, (c >> 8u64) & 0xffu64 <= 8, (c >> 16u64) & 0xffu64 <= 8, (c >> 24u64) & 0xffu64 <= 8, (c >> 32u64) & 0xffu64 <= 8, (c >> 40u64) & 0xffu64 <= 8, (c >> 48u64) & 0xffu64 <= 8, (c >> 56u64) & 0xffu64 <= 8;
}

/// A bit as a number is 0 or 1, and 1 exactly when its lane is set.
proof fn lemma_b(x: u64, i: u64)
    requires i < 64,
    ensures b(x, i) <= 1, (b(x, i) == 1) == lane(x, i as int),
{
    assert((x >> i) & 1u64 <= 1u64) by (bit_vector);
}

/// One more lane.
proof fn lemma_cnt_step(x: u64, k: int)
    requires 0 <= k < 64,
    ensures cnt_lanes(x, k + 1) == cnt_lanes(x, k) + b(x, k as u64),
{
    lemma_b(x, k as u64);
}

/// Eight more lanes: `cnt_lanes(x, 8 q + 8)` adds the eight bits of byte `q`.
proof fn lemma_cnt_byte(x: u64, q: int)
    requires 0 <= q < 8,
    ensures cnt_lanes(x, 8 * q + 8) == cnt_lanes(x, 8 * q) + b(x, (8 * q) as u64) + b(x, (8 * q + 1) as u64)
        + b(x, (8 * q + 2) as u64) + b(x, (8 * q + 3) as u64) + b(x, (8 * q + 4) as u64) + b(x, (8 * q + 5) as u64)
        + b(x, (8 * q + 6) as u64) + b(x, (8 * q + 7) as u64),
{
    let k = 8 * q;
    lemma_cnt_step(x, k);
    lemma_cnt_step(x, k + 1);
    lemma_cnt_step(x, k + 2);
    lemma_cnt_step(x, k + 3);
    lemma_cnt_step(x, k + 4);
    lemma_cnt_step(x, k + 5);
    lemma_cnt_step(x, k + 6);
    lemma_cnt_step(x, k + 7);
}

/// The number of set lanes of `x` (one `popcnt`).
#[inline(always)]
pub fn popcount(x: u64) -> (r: u64)
    ensures r as int == cnt_lanes(x, 64), r <= 64,
    no_unwind
{
    proof {
        assert(x >= (x >> 1u64) & 0x5555_5555_5555_5555u64) by (bit_vector);
    }
    let a = x - ((x >> 1u64) & 0x5555_5555_5555_5555u64);
    proof {
        assert(((a & 0x3333_3333_3333_3333u64) as int) + (((a >> 2u64) & 0x3333_3333_3333_3333u64) as int) <= u64::MAX)
            by (bit_vector);
    }
    let bb = (a & 0x3333_3333_3333_3333u64) + ((a >> 2u64) & 0x3333_3333_3333_3333u64);
    proof {
        assert((bb as int) + ((bb >> 4u64) as int) <= u64::MAX) by (bit_vector)
            requires bb == (a & 0x3333_3333_3333_3333u64) + ((a >> 2u64) & 0x3333_3333_3333_3333u64);
    }
    let c = (bb + (bb >> 4u64)) & 0x0f0f_0f0f_0f0f_0f0fu64;
    proof {
        assert(c == swar_bytes(x));
        lemma_byte0(x); lemma_byte1(x); lemma_byte2(x); lemma_byte3(x);
        lemma_byte4(x); lemma_byte5(x); lemma_byte6(x); lemma_byte7(x);
        assert forall|i: u64| i < 64 implies #[trigger] b(x, i) <= 1 by { lemma_b(x, i); }
        lemma_byte_sum(c);
        lemma_cnt_byte(x, 0); lemma_cnt_byte(x, 1); lemma_cnt_byte(x, 2); lemma_cnt_byte(x, 3);
        lemma_cnt_byte(x, 4); lemma_cnt_byte(x, 5); lemma_cnt_byte(x, 6); lemma_cnt_byte(x, 7);
        assert(cnt_lanes(x, 0) == 0);
    }
    c.wrapping_mul(0x0101_0101_0101_0101u64) >> 56u64
}

/// The word with lanes `0..=t` set.
#[inline(always)]
pub fn low_mask(t: u64) -> (m: u64)
    requires t < 64,
    ensures forall|i: int| 0 <= i < 64 ==> #[trigger] lane(m, i) == (i <= t),
    no_unwind
{
    let m = 0xffff_ffff_ffff_ffffu64 >> (63 - t);
    proof {
        assert forall|i: int| 0 <= i < 64 implies #[trigger] lane(m, i) == (i <= t) by {
            let ii = i as u64;
            assert((((0xffff_ffff_ffff_ffffu64 >> sub(63u64, t)) >> ii) & 1u64 == 1u64) == (ii <= t)) by (bit_vector)
                requires t < 64, ii < 64;
        }
    }
    m
}

/// A lane of `x & m` is set exactly when it is set in both.
pub proof fn lemma_and_lane(x: u64, m: u64, i: int)
    requires 0 <= i < 64,
    ensures lane(x & m, i) == (lane(x, i) && lane(m, i)),
{
    let ii = i as u64;
    assert((((x & m) >> ii) & 1u64 == 1u64) == (((x >> ii) & 1u64 == 1u64) && ((m >> ii) & 1u64 == 1u64))) by (bit_vector)
        requires ii < 64;
}

/// Words with the same lanes below `k` have the same count below `k`.
proof fn lemma_cnt_same(x: u64, y: u64, k: int)
    requires 0 <= k <= 64, forall|i: int| 0 <= i < k ==> #[trigger] lane(x, i) == lane(y, i),
    ensures cnt_lanes(x, k) == cnt_lanes(y, k),
    decreases k,
{
    if k > 0 {
        lemma_cnt_same(x, y, k - 1);
    }
}

/// Lanes from `k` on that are clear add nothing.
proof fn lemma_cnt_clear(x: u64, k: int, e: int)
    requires 0 <= k <= e <= 64, forall|i: int| k <= i < e ==> !#[trigger] lane(x, i),
    ensures cnt_lanes(x, e) == cnt_lanes(x, k),
    decreases e - k,
{
    if e > k {
        lemma_cnt_clear(x, k, e - 1);
    }
}

/// The rank of lane `t` in `x`: `popcount(x & low_mask(t))` counts the set lanes of `x` in `0..=t`.
pub proof fn lemma_rank(x: u64, m: u64, t: int)
    requires 0 <= t < 64, forall|i: int| 0 <= i < 64 ==> #[trigger] lane(m, i) == (i <= t),
    ensures cnt_lanes(x & m, 64) == cnt_lanes(x, t + 1),
{
    assert forall|i: int| 0 <= i < t + 1 implies #[trigger] lane(x & m, i) == lane(x, i) by {
        lemma_and_lane(x, m, i);
    }
    assert forall|i: int| t + 1 <= i < 64 implies !#[trigger] lane(x & m, i) by {
        lemma_and_lane(x, m, i);
    }
    lemma_cnt_same(x & m, x, t + 1);
    lemma_cnt_clear(x & m, t + 1, 64);
}

/// A count below `k` lies in `[0, k]`.
pub proof fn lemma_cnt_lanes_bound(x: u64, k: int)
    requires 0 <= k,
    ensures 0 <= cnt_lanes(x, k) <= k,
    decreases k,
{
    if k > 0 {
        lemma_cnt_lanes_bound(x, k - 1);
    }
}

} // verus!
