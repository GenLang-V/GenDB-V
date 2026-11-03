//! Rank in a bitset word: the number of set bits of a `u64` below position `b` (`cnt_below`), computed by
//! `count_below` with the clear-lowest-bit loop (one population count instruction on targets that have it; the SWAR
//! sum `swar` is its closed form), `no_unwind`.
use vstd::prelude::*;

verus! {

/// Bit `k` of `x` (0 or 1).
pub open spec fn bit_at(x: u64, k: int) -> nat {
    if 0 <= k < 64 && (x >> (k as u64)) & 1 == 1 { 1 } else { 0 }
}

/// Number of set bits of `x` at positions `0 .. b`.
pub open spec fn cnt_below(x: u64, b: int) -> nat
    decreases b,
{
    if b <= 0 { 0 } else { cnt_below(x, b - 1) + bit_at(x, b - 1) }
}

/// One more position.
pub proof fn lemma_cnt_step(x: u64, b: int)
    requires b >= 0,
    ensures cnt_below(x, b + 1) == cnt_below(x, b) + bit_at(x, b),
{
}

/// The 64 bits of `x` summed in machine arithmetic.
pub open spec fn sum_bits(x: u64) -> u64 {
    (((x >> 0u64) & 1u64) + ((x >> 1u64) & 1u64) + ((x >> 2u64) & 1u64) + ((x >> 3u64) & 1u64) + ((x >> 4u64) & 1u64) + ((x >> 5u64) & 1u64) + ((x >> 6u64) & 1u64) + ((x >> 7u64) & 1u64) + ((x >> 8u64) & 1u64) + ((x >> 9u64) & 1u64) + ((x >> 10u64) & 1u64) + ((x >> 11u64) & 1u64) + ((x >> 12u64) & 1u64) + ((x >> 13u64) & 1u64) + ((x >> 14u64) & 1u64) + ((x >> 15u64) & 1u64) + ((x >> 16u64) & 1u64) + ((x >> 17u64) & 1u64) + ((x >> 18u64) & 1u64) + ((x >> 19u64) & 1u64) + ((x >> 20u64) & 1u64) + ((x >> 21u64) & 1u64) + ((x >> 22u64) & 1u64) + ((x >> 23u64) & 1u64) + ((x >> 24u64) & 1u64) + ((x >> 25u64) & 1u64) + ((x >> 26u64) & 1u64) + ((x >> 27u64) & 1u64) + ((x >> 28u64) & 1u64) + ((x >> 29u64) & 1u64) + ((x >> 30u64) & 1u64) + ((x >> 31u64) & 1u64) + ((x >> 32u64) & 1u64) + ((x >> 33u64) & 1u64) + ((x >> 34u64) & 1u64) + ((x >> 35u64) & 1u64) + ((x >> 36u64) & 1u64) + ((x >> 37u64) & 1u64) + ((x >> 38u64) & 1u64) + ((x >> 39u64) & 1u64) + ((x >> 40u64) & 1u64) + ((x >> 41u64) & 1u64) + ((x >> 42u64) & 1u64) + ((x >> 43u64) & 1u64) + ((x >> 44u64) & 1u64) + ((x >> 45u64) & 1u64) + ((x >> 46u64) & 1u64) + ((x >> 47u64) & 1u64) + ((x >> 48u64) & 1u64) + ((x >> 49u64) & 1u64) + ((x >> 50u64) & 1u64) + ((x >> 51u64) & 1u64) + ((x >> 52u64) & 1u64) + ((x >> 53u64) & 1u64) + ((x >> 54u64) & 1u64) + ((x >> 55u64) & 1u64) + ((x >> 56u64) & 1u64) + ((x >> 57u64) & 1u64) + ((x >> 58u64) & 1u64) + ((x >> 59u64) & 1u64) + ((x >> 60u64) & 1u64) + ((x >> 61u64) & 1u64) + ((x >> 62u64) & 1u64) + ((x >> 63u64) & 1u64)) as u64
}

/// The SWAR population count (2-bit, 4-bit and 8-bit field sums, then the byte sums by shifts).
pub open spec fn swar(x: u64) -> u64 {
    let a = ((x & 0x5555555555555555u64) + ((x >> 1u64) & 0x5555555555555555u64)) as u64;
    let b = ((a & 0x3333333333333333u64) + ((a >> 2u64) & 0x3333333333333333u64)) as u64;
    let c = ((b & 0x0f0f0f0f0f0f0f0fu64) + ((b >> 4u64) & 0x0f0f0f0f0f0f0f0fu64)) as u64;
    let d = ((c & 0x00ff00ff00ff00ffu64) + ((c >> 8u64) & 0x00ff00ff00ff00ffu64)) as u64;
    let e = ((d & 0x0000ffff0000ffffu64) + ((d >> 16u64) & 0x0000ffff0000ffffu64)) as u64;
    ((e & 0x00000000ffffffffu64) + ((e >> 32u64) & 0x00000000ffffffffu64)) as u64
}

proof fn lemma_swar_sum(x: u64)
    ensures swar(x) == sum_bits(x),
{
    assert(swar(x) == sum_bits(x)) by (bit_vector);
}

/// A bit is 0 or 1.
proof fn lemma_bit01(x: u64, k: u64)
    requires k < 64,
    ensures (x >> k) & 1u64 <= 1u64,
{
    assert((x >> k) & 1u64 <= 1u64) by (bit_vector) requires k < 64;
}

/// `bit_at` is the machine bit.
proof fn lemma_bit_at(x: u64, k: int)
    requires 0 <= k < 64,
    ensures bit_at(x, k) as int == ((x >> (k as u64)) & 1u64) as int,
{
    lemma_bit01(x, k as u64);
}

/// Eight more positions.
proof fn lemma_cnt8(x: u64, a: int)
    requires 0 <= a,
    ensures cnt_below(x, a + 8) == cnt_below(x, a) + bit_at(x, a) + bit_at(x, a + 1) + bit_at(x, a + 2) + bit_at(x, a + 3)
        + bit_at(x, a + 4) + bit_at(x, a + 5) + bit_at(x, a + 6) + bit_at(x, a + 7),
{
    lemma_cnt_step(x, a);
    lemma_cnt_step(x, a + 1);
    lemma_cnt_step(x, a + 2);
    lemma_cnt_step(x, a + 3);
    lemma_cnt_step(x, a + 4);
    lemma_cnt_step(x, a + 5);
    lemma_cnt_step(x, a + 6);
    lemma_cnt_step(x, a + 7);
}

/// The flat machine sum of the bits is `cnt_below(x, 64)`.
proof fn lemma_sum_cnt(x: u64)
    ensures sum_bits(x) as int == cnt_below(x, 64),
{
    assert forall|k: int| 0 <= k < 64 implies #[trigger] bit_at(x, k) as int == ((x >> (k as u64)) & 1u64) as int by {
        lemma_bit_at(x, k);
    }
    assert(cnt_below(x, 0) == 0);
    lemma_cnt8(x, 0);
    lemma_cnt8(x, 8);
    lemma_cnt8(x, 16);
    lemma_cnt8(x, 24);
    lemma_cnt8(x, 32);
    lemma_cnt8(x, 40);
    lemma_cnt8(x, 48);
    lemma_cnt8(x, 56);
}

/// The low `b` bits (all bits for `b == 64`).
pub open spec fn low_mask(b: u64) -> u64 {
    if b >= 64 { 0xffff_ffff_ffff_ffffu64 } else { ((1u64 << b) - 1u64) as u64 }
}

/// Bit `k` of `x & low_mask(b)`.
proof fn lemma_masked_bit(x: u64, b: u64, k: u64)
    requires b <= 64, k < 64,
    ensures ((x & low_mask(b)) >> k) & 1u64 == if k < b { (x >> k) & 1u64 } else { 0u64 },
{
    if b == 64 {
        assert(((x & 0xffff_ffff_ffff_ffffu64) >> k) & 1u64 == (x >> k) & 1u64) by (bit_vector);
    } else {
        assert(((x & (((1u64 << b) - 1u64) as u64)) >> k) & 1u64 == if k < b { (x >> k) & 1u64 } else { 0u64 })
            by (bit_vector) requires b < 64, k < 64;
    }
}

/// Counting the masked word over all positions counts the word below `b`.
proof fn lemma_masked_cnt(x: u64, b: u64, k: int)
    requires b <= 64, 0 <= k <= 64,
    ensures cnt_below(x & low_mask(b), k) == cnt_below(x, if k < b { k } else { b as int }),
    decreases k,
{
    if k > 0 {
        lemma_masked_cnt(x, b, k - 1);
        lemma_masked_bit(x, b, (k - 1) as u64);
        lemma_bit_at(x, k - 1);
        lemma_bit_at(x & low_mask(b), k - 1);
    }
}

/// At most `b` set bits below `b`.
proof fn lemma_cnt_le(x: u64, b: int)
    requires 0 <= b,
    ensures cnt_below(x, b) <= b,
    decreases b,
{
    if b > 0 {
        lemma_cnt_le(x, b - 1);
    }
}

/// `y` is `x` without its set bit `t`: one set bit fewer below every `n > t`.
proof fn lemma_cnt_drop(x: u64, y: u64, t: int, n: int)
    requires
        0 <= t < 64, 0 <= n <= 64,
        bit_at(x, t) == 1, bit_at(y, t) == 0,
        forall|k: int| 0 <= k < 64 && k != t ==> #[trigger] bit_at(y, k) == bit_at(x, k),
    ensures cnt_below(y, n) + (if t < n { 1int } else { 0int }) == cnt_below(x, n),
    decreases n,
{
    if n > 0 {
        lemma_cnt_drop(x, y, t, n - 1);
    }
}

/// Clearing the lowest set bit (`x & (x - 1)`) removes one set bit.
proof fn lemma_clear_lowest(x: u64)
    requires x != 0,
    ensures cnt_below(x & ((x - 1) as u64), 64) + 1 == cnt_below(x, 64),
{
    let y = x & ((x - 1) as u64);
    let lsb = (x & ((!x) + 1u64) as u64) as u64;
    let t = swar((lsb - 1u64) as u64);
    assert(swar(((x & ((!x) + 1u64) as u64) - 1u64) as u64) < 64) by (bit_vector) requires x != 0u64;
    assert((x >> swar(((x & ((!x) + 1u64) as u64) - 1u64) as u64)) & 1u64 == 1u64) by (bit_vector) requires x != 0u64;
    assert(x & (((1u64 << swar(((x & ((!x) + 1u64) as u64) - 1u64) as u64)) - 1u64) as u64) == 0u64) by (bit_vector) requires x != 0u64;
    assert(t < 64);
    assert forall|k: int| 0 <= k < 64 implies #[trigger] bit_at(y, k) == (if k == t as int { 0nat } else { bit_at(x, k) }) by {
        let kk = k as u64;
        assert((y >> kk) & 1u64 == (if kk == t { 0u64 } else { (x >> kk) & 1u64 })) by (bit_vector)
            requires y == x & ((x - 1u64) as u64), x != 0u64, t < 64u64, kk < 64u64,
                (x >> t) & 1u64 == 1u64, x & (((1u64 << t) - 1u64) as u64) == 0u64;
        lemma_bit01(x, kk);
        lemma_bit01(y, kk);
    }
    lemma_bit01(x, t);
    lemma_cnt_drop(x, y, t as int, 64);
}

/// `cnt_below(x, b)`: the set bits of `x` below position `b` (the clear-lowest-bit loop, which compiles to one
/// population count instruction where the target has one).
pub fn count_below(x: u64, b: u64) -> (r: u64)
    requires b <= 64,
    ensures r as int == cnt_below(x, b as int), r <= 64, b == 64 ==> r == swar(x),
    no_unwind
{
    proof {
        if b < 64 {
            assert(1u64 << b >= 1u64) by (bit_vector) requires b < 64;
        }
    }
    let mask: u64 = if b >= 64 { 0xffff_ffff_ffff_ffffu64 } else { (1u64 << b) - 1 };
    let y = x & mask;
    proof {
        assert(y == x & low_mask(b));
        lemma_masked_cnt(x, b, 64);
        lemma_cnt_le(y, 64);
    }
    let mut z = y;
    let mut c: u64 = 0;
    while z != 0
        invariant c + cnt_below(z, 64) == cnt_below(y, 64), cnt_below(y, 64) <= 64,
        decreases cnt_below(z, 64),
    {
        proof { lemma_clear_lowest(z); }
        z = z & (z - 1);
        c = c + 1;
    }
    proof {
        assert forall|k: int| 0 <= k < 64 implies #[trigger] bit_at(0u64, k) == 0 by {
            let kk = k as u64;
            assert((0u64 >> kk) & 1u64 == 0u64) by (bit_vector);
        }
        lemma_cnt_zero(64);
        lemma_swar_sum(y);
        lemma_sum_cnt(y);
        if b == 64 {
            assert(x & 0xffff_ffff_ffff_ffffu64 == x) by (bit_vector);
            lemma_swar_sum(x);
            lemma_sum_cnt(x);
        }
    }
    c
}

/// No set bits in the zero word.
proof fn lemma_cnt_zero(n: int)
    requires 0 <= n <= 64, forall|k: int| 0 <= k < 64 ==> #[trigger] bit_at(0u64, k) == 0,
    ensures cnt_below(0u64, n) == 0,
    decreases n,
{
    if n > 0 {
        lemma_cnt_zero(n - 1);
    }
}

} // verus!
