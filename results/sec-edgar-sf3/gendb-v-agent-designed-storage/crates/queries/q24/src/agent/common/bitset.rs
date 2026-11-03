//! A fixed-size bit set over `0..64 * words.len()` packed in `u64` words: allocate cleared, set, clear and test one
//! bit (`no_unwind` set/clear/test, usable in worker bodies).
//!
//! Bit `x` is bit `x % 64` (least significant first) of word `x / 64`; `bit_on(w, x)` is its value.
use vstd::prelude::*;
use crate::gendb_entry::work::put;

verus! {

/// Bit `x` of the words `w`.
pub open spec fn bit_on(w: Seq<u64>, x: int) -> bool {
    (w[x / 64] >> ((x % 64) as u64)) & 1u64 == 1u64
}

/// No bit in `0..=hi` is set.
pub open spec fn clear_upto(w: Seq<u64>, hi: int) -> bool {
    forall|x: int| 0 <= x <= hi ==> !#[trigger] bit_on(w, x)
}

/// Setting bit `a` of `v` sets bit `b` exactly when `a == b`, else keeps it.
proof fn lemma_or_bit(v: u64, a: u64, b: u64)
    requires a < 64, b < 64,
    ensures ((v | (1u64 << a)) >> b) & 1u64 == if a == b { 1u64 } else { (v >> b) & 1u64 },
{
    assert(((v | (1u64 << a)) >> b) & 1u64 == if a == b { 1u64 } else { (v >> b) & 1u64 }) by (bit_vector)
        requires a < 64, b < 64;
}

/// Clearing bit `a` of `v` clears bit `b` exactly when `a == b`, else keeps it.
proof fn lemma_andnot_bit(v: u64, a: u64, b: u64)
    requires a < 64, b < 64,
    ensures ((v & !(1u64 << a)) >> b) & 1u64 == if a == b { 0u64 } else { (v >> b) & 1u64 },
{
    assert(((v & !(1u64 << a)) >> b) & 1u64 == if a == b { 0u64 } else { (v >> b) & 1u64 }) by (bit_vector)
        requires a < 64, b < 64;
}

/// A bit of a zero word is clear; a bit is 0 or 1.
proof fn lemma_bit_facts(v: u64, b: u64)
    requires b < 64,
    ensures (0u64 >> b) & 1u64 == 0u64, (v >> b) & 1u64 == 0u64 || (v >> b) & 1u64 == 1u64,
{
    assert((0u64 >> b) & 1u64 == 0u64) by (bit_vector) requires b < 64;
    assert((v >> b) & 1u64 == 0u64 || (v >> b) & 1u64 == 1u64) by (bit_vector);
}

/// Two different bits in the same word differ in their offset.
proof fn lemma_same_word(x: int, y: int)
    requires 0 <= x, 0 <= y, x != y, x / 64 == y / 64,
    ensures x % 64 != y % 64,
{
    assert(x == 64 * (x / 64) + x % 64) by (nonlinear_arith) requires 0 <= x;
    assert(y == 64 * (y / 64) + y % 64) by (nonlinear_arith) requires 0 <= y;
}

/// Words for bits `0..=hi`, all clear.
pub fn new_bits(hi: usize) -> (w: Vec<u64>)
    ensures w@.len() == hi / 64 + 1, clear_upto(w@, hi as int),
{
    let w = vec![0u64; hi / 64 + 1];
    proof {
        assert forall|x: int| 0 <= x <= hi implies !#[trigger] bit_on(w@, x) by {
            assert(cloned(0u64, w@[x / 64]));
            lemma_bit_facts(0u64, (x % 64) as u64);
        }
    }
    w
}

/// Set bit `x`.
pub fn bit_set(w: &mut Vec<u64>, x: usize)
    requires x / 64 < old(w)@.len(),
    ensures
        final(w)@.len() == old(w)@.len(),
        bit_on(final(w)@, x as int),
        forall|y: int| 0 <= y < 64 * old(w)@.len() && y != x ==> #[trigger] bit_on(final(w)@, y) == bit_on(old(w)@, y),
    no_unwind
{
    let q = x / 64;
    let a = (x % 64) as u64;
    let v = w[q];
    put(w, q, v | (1u64 << a));
    proof {
        lemma_or_bit(v, a, a);
        assert forall|y: int| 0 <= y < 64 * old(w)@.len() && y != x implies #[trigger] bit_on(w@, y) == bit_on(old(w)@, y) by {
            if y / 64 == x / 64 {
                lemma_same_word(x as int, y);
                lemma_or_bit(v, a, (y % 64) as u64);
            }
        }
    }
}

/// Clear bit `x`.
pub fn bit_clear(w: &mut Vec<u64>, x: usize)
    requires x / 64 < old(w)@.len(),
    ensures
        final(w)@.len() == old(w)@.len(),
        !bit_on(final(w)@, x as int),
        forall|y: int| 0 <= y < 64 * old(w)@.len() && y != x ==> #[trigger] bit_on(final(w)@, y) == bit_on(old(w)@, y),
    no_unwind
{
    let q = x / 64;
    let a = (x % 64) as u64;
    let v = w[q];
    put(w, q, v & !(1u64 << a));
    proof {
        lemma_andnot_bit(v, a, a);
        assert forall|y: int| 0 <= y < 64 * old(w)@.len() && y != x implies #[trigger] bit_on(w@, y) == bit_on(old(w)@, y) by {
            if y / 64 == x / 64 {
                lemma_same_word(x as int, y);
                lemma_andnot_bit(v, a, (y % 64) as u64);
            }
        }
    }
}

/// Bit `x`.
pub fn bit_test(w: &Vec<u64>, x: usize) -> (b: bool)
    requires x / 64 < w@.len(),
    ensures b == bit_on(w@, x as int),
    no_unwind
{
    let q = x / 64;
    let a = (x % 64) as u64;
    (w[q] >> a) & 1u64 == 1u64
}

} // verus!
