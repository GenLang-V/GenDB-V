//! `trailing_zeros` of a non-zero `u64` without the intrinsic (whose pinned vstd specification may unwind, so worker
//! bodies cannot call it): isolate the lowest set bit, multiply by the de Bruijn constant `0x03f79d71b4cb0a89`, and
//! look the top 6 bits up in a 64-entry table. The answer is checked (`low >> r == 1`), with a bit-by-bit scan as the
//! (never taken) alternative, so the table itself needs no proof.
use vstd::prelude::*;
use vstd::std_specs::bits::{u64_trailing_zeros, axiom_u64_trailing_zeros};
use crate::agent::common::bits::*;

verus! {

pub const DEBRUIJN: u64 = 0x03f7_9d71_b4cb_0a89;

/// Bit position of each table index (any table is sound: `tz64` checks its answer).
pub open spec fn tz_table() -> Seq<u8> {
    seq![0u8, 1, 48, 2, 57, 49, 28, 3, 61, 58, 50, 42, 38, 29, 17, 4, 62, 55, 59, 36, 53, 51, 43, 22, 45, 39, 33, 30,
        24, 18, 12, 5, 63, 47, 56, 27, 60, 41, 37, 16, 54, 35, 52, 21, 44, 32, 23, 11, 46, 26, 40, 15, 34, 20, 31, 10,
        25, 14, 19, 9, 13, 8, 7, 6]
}

/// The 64-entry table as an array.
pub fn tz_table_array() -> (t: [u8; 64])
    ensures t@ == tz_table(),
    no_unwind
{
    let t: [u8; 64] = [0u8, 1, 48, 2, 57, 49, 28, 3, 61, 58, 50, 42, 38, 29, 17, 4, 62, 55, 59, 36, 53, 51, 43, 22, 45, 39,
        33, 30, 24, 18, 12, 5, 63, 47, 56, 27, 60, 41, 37, 16, 54, 35, 52, 21, 44, 32, 23, 11, 46, 26, 40, 15, 34, 20, 31,
        10, 25, 14, 19, 9, 13, 8, 7, 6];
    assert(t@ =~= tz_table());
    t
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

/// `low` is the single bit `k`: shifting it right by `r < 64` gives 1 exactly when `r == k`.
pub proof fn lemma_single_bit_shift(k: u64, r: u64)
    requires k < 64, r < 64, (1u64 << k) >> r == 1u64,
    ensures r == k,
{
    assert((k < 64 && r < 64 && (1u64 << k) >> r == 1u64) ==> r == k) by (bit_vector);
}

/// `trailing_zeros` of a non-zero mask, `no_unwind`.
pub fn tz64(c: u64, table: &[u8; 64]) -> (r: u32)
    requires c != 0, table@.len() == 64,
    ensures r == u64_trailing_zeros(c), r < 64,
    no_unwind
{
    proof {
        lemma_isolate(c);
        axiom_u64_trailing_zeros(c);
    }
    let low = c & (!c).wrapping_add(1);
    let h = low.wrapping_mul(DEBRUIJN) >> 58u64;
    assert(h < 64) by (bit_vector)
        requires h == low.wrapping_mul(DEBRUIJN) >> 58u64;
    let r = table[h as usize] as u64;
    if r < 64 && (low >> r) == 1 {
        proof {
            lemma_single_bit_shift(u64_trailing_zeros(c) as u64, r);
        }
        return r as u32;
    }
    // scan bit by bit
    let mut t: u64 = 0;
    while t < 64
        invariant c != 0, t <= 64, forall|v: u64| v < t ==> #[trigger] ((c >> v) & 1u64) == 0u64,
            u64_trailing_zeros(c) < 64,
            (c >> (u64_trailing_zeros(c) as u64)) & 1u64 == 1u64,
            forall|v: u64| v < u64_trailing_zeros(c) ==> #[trigger] (c >> v) & 1u64 == 0u64,
        decreases 64 - t,
    {
        if (c >> t) & 1 == 1 {
            assert(t >= u64_trailing_zeros(c));
            assert(t == u64_trailing_zeros(c));
            return t as u32;
        }
        t = t + 1;
    }
    assert(false);
    0
}

} // verus!
