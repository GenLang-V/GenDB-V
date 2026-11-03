//! Bit lemmas for u64 bitmap words: single bits (`bit64`), and / or / not of words, and the set-bit iteration
//! `t = x.trailing_zeros(); ...; x = x & (x - 1)` (lowest set bit, bits below it clear, clearing it).
use vstd::prelude::*;
use vstd::std_specs::bits::{u64_trailing_zeros, axiom_u64_trailing_zeros};

verus! {

/// Bit `i` (`0 <= i < 64`) of word `x`.
pub open spec fn bit64(x: u64, i: int) -> bool {
    (x >> (i as u64)) & 1u64 == 1u64
}

/// Bit `i` of `x` as the integer 0 or 1.
pub open spec fn b01(x: u64, i: int) -> int {
    if bit64(x, i) { 1 } else { 0 }
}

/// `(x >> i) & 1` is bit `i` as 0 or 1.
pub proof fn lemma_bit_value(x: u64, i: u64)
    requires i < 64,
    ensures ((x >> i) & 1u64) as int == b01(x, i as int),
{
    assert((x >> i) & 1u64 == 1u64 || (x >> i) & 1u64 == 0u64) by (bit_vector);
}

/// No bit of 0 is set; every bit of `!0` is set.
pub proof fn lemma_const_words()
    ensures
        forall|i: int| 0 <= i < 64 ==> !#[trigger] bit64(0u64, i),
        forall|i: int| 0 <= i < 64 ==> #[trigger] bit64(!0u64, i),
{
    assert forall|i: int| 0 <= i < 64 implies !#[trigger] bit64(0u64, i) by {
        let k = i as u64;
        assert((0u64 >> k) & 1u64 != 1u64) by (bit_vector);
    }
    assert forall|i: int| 0 <= i < 64 implies #[trigger] bit64(!0u64, i) by {
        let k = i as u64;
        assert(((!0u64) >> k) & 1u64 == 1u64) by (bit_vector) requires k < 64;
    }
}

/// Bits of `a & b`, `a | b` and `!a`.
pub proof fn lemma_bit_ops(a: u64, b: u64, i: int)
    requires 0 <= i < 64,
    ensures
        bit64(a & b, i) == (bit64(a, i) && bit64(b, i)),
        bit64(a | b, i) == (bit64(a, i) || bit64(b, i)),
        bit64(!a, i) == !bit64(a, i),
{
    let k = i as u64;
    assert(((a & b) >> k) & 1u64 == 1u64 <==> ((a >> k) & 1u64 == 1u64 && (b >> k) & 1u64 == 1u64)) by (bit_vector)
        requires k < 64;
    assert(((a | b) >> k) & 1u64 == 1u64 <==> ((a >> k) & 1u64 == 1u64 || (b >> k) & 1u64 == 1u64)) by (bit_vector)
        requires k < 64;
    assert(((!a) >> k) & 1u64 == 1u64 <==> !((a >> k) & 1u64 == 1u64)) by (bit_vector)
        requires k < 64;
}

/// The lowest set bit `t` of a nonzero word: `t < 64`, bit `t` is set, the bits below it are clear, and
/// `x & (x - 1)` clears exactly bit `t`.
pub proof fn lemma_lowest_bit(x: u64)
    requires x != 0,
    ensures ({
        let t = u64_trailing_zeros(x) as int;
        &&& 0 <= t < 64
        &&& bit64(x, t)
        &&& forall|i: int| 0 <= i < t ==> !#[trigger] bit64(x, i)
        &&& forall|i: int| 0 <= i < 64 ==> #[trigger] bit64(x & sub(x, 1u64), i) == (bit64(x, i) && i != t)
    }),
{
    axiom_u64_trailing_zeros(x);
    let t = u64_trailing_zeros(x) as u64;
    assert(t < 64);
    assert forall|i: int| 0 <= i < t implies !#[trigger] bit64(x, i) by {
        let k = i as u64;
        assert((x >> k) & 1u64 == 0u64);
    }
    assert forall|i: int| 0 <= i < 64 implies #[trigger] bit64(x & sub(x, 1u64), i) == (bit64(x, i) && i != t) by {
        let k = i as u64;
        assert(((x & sub(x, 1u64)) >> k) & 1u64 == 1u64 <==> ((x >> k) & 1u64 == 1u64 && k != t)) by (bit_vector)
            requires t < 64, k < 64, (x >> t) & 1u64 == 1u64, x << sub(64u64, t) == 0u64, x != 0u64;
    }
}


// ------------------------------------------------------------------------------------------- lowest set bit index
//
// `u64::trailing_zeros` has no `no_unwind` specification, so worker code finds the index of the lowest set bit
// with a de Bruijn multiplication: `lb = x & !(x - 1)` isolates the bit (`1 << t`), `(lb * DEBRUIJN64) >> 58` is a
// distinct 6-bit slot per `t`, and `DB_TABLE[slot] == t` (checked for all 64 positions by computation).

/// The de Bruijn constant B(2, 6).
pub const DEBRUIJN64: u64 = 0x03f7_9d71_b4cb_0a89;

/// Bit position of each slot.
pub open spec fn db_table() -> Seq<u8> {
    seq![0u8, 1u8, 48u8, 2u8, 57u8, 49u8, 28u8, 3u8, 61u8, 58u8, 50u8, 42u8, 38u8, 29u8, 17u8, 4u8, 62u8, 55u8, 59u8, 36u8, 53u8, 51u8, 43u8, 22u8, 45u8, 39u8, 33u8, 30u8, 24u8, 18u8, 12u8, 5u8, 63u8, 47u8, 56u8, 27u8, 60u8, 41u8, 37u8, 16u8, 54u8, 35u8, 52u8, 21u8, 44u8, 32u8, 23u8, 11u8, 46u8, 26u8, 40u8, 15u8, 34u8, 20u8, 31u8, 10u8, 25u8, 14u8, 19u8, 9u8, 13u8, 8u8, 7u8, 6u8]
}

/// The slot of an isolated bit.
pub open spec fn db_slot(lb: u64) -> u64 {
    lb.wrapping_mul(DEBRUIJN64) >> 58u64
}

/// The table gives position `t` back from the slot of `1 << t`.
pub open spec fn db_ok(t: u64) -> bool {
    db_table()[db_slot(1u64 << t) as int] as u64 == t
}

/// `db_ok` for the positions `t .. 64`.
pub open spec fn db_all(t: nat) -> bool
    decreases 64 - t,
{
    if t >= 64 { true } else { db_ok(t as u64) && db_all(t + 1) }
}

proof fn lemma_db_from(k: nat, t: nat)
    requires db_all(k), k <= t < 64,
    ensures db_ok(t as u64),
    decreases t - k,
{
    if k < t {
        lemma_db_from(k + 1, t);
    }
}

/// The table is right for every position.
pub proof fn lemma_db(t: u64)
    requires t < 64,
    ensures db_ok(t),
{
    assert(db_all(0)) by (compute_only);
    lemma_db_from(0, t as nat);
}

/// `x & !(x - 1)` is the lowest set bit of a nonzero word.
pub proof fn lemma_isolate(x: u64)
    requires x != 0,
    ensures x & !sub(x, 1u64) == 1u64 << (u64_trailing_zeros(x) as u64),
{
    axiom_u64_trailing_zeros(x);
    let t = u64_trailing_zeros(x) as u64;
    assert(x & !sub(x, 1u64) == 1u64 << t) by (bit_vector)
        requires t < 64, (x >> t) & 1u64 == 1u64, x << sub(64u64, t) == 0u64, x != 0u64;
}

/// The index of the lowest set bit of a nonzero word (`trailing_zeros`), without a call that may unwind.
#[inline(always)]
pub fn lowest_bit(x: u64) -> (t: u64)
    requires x != 0,
    ensures t == u64_trailing_zeros(x), t < 64,
    no_unwind
{
    let tab: [u8; 64] = [0, 1, 48, 2, 57, 49, 28, 3, 61, 58, 50, 42, 38, 29, 17, 4, 62, 55, 59, 36, 53, 51, 43, 22, 45, 39, 33, 30, 24, 18, 12, 5, 63, 47, 56, 27, 60, 41, 37, 16, 54, 35, 52, 21, 44, 32, 23, 11, 46, 26, 40, 15, 34, 20, 31, 10, 25, 14, 19, 9, 13, 8, 7, 6];
    proof {
        axiom_u64_trailing_zeros(x);
        lemma_isolate(x);
        lemma_db(u64_trailing_zeros(x) as u64);
        assert(tab@ =~= db_table());
    }
    let lb = x & !(x - 1);
    let slot = lb.wrapping_mul(DEBRUIJN64) >> 58u64;
    proof {
        assert(slot < 64) by (bit_vector) requires slot == lb.wrapping_mul(DEBRUIJN64) >> 58u64;
    }
    tab[slot as usize] as u64
}


/// The de Bruijn slot table (`db_table`), built once by a caller that looks up many words.
#[inline(always)]
pub fn db_tab() -> (tab: [u8; 64])
    ensures tab@ == db_table(),
    no_unwind
{
    let tab: [u8; 64] = [0, 1, 48, 2, 57, 49, 28, 3, 61, 58, 50, 42, 38, 29, 17, 4, 62, 55, 59, 36, 53, 51, 43, 22, 45, 39, 33, 30, 24, 18, 12, 5, 63, 47, 56, 27, 60, 41, 37, 16, 54, 35, 52, 21, 44, 32, 23, 11, 46, 26, 40, 15, 34, 20, 31, 10, 25, 14, 19, 9, 13, 8, 7, 6];
    proof {
        assert(tab@ =~= db_table());
    }
    tab
}

/// `lowest_bit` with the slot table passed in (`db_tab`), so a loop over many words does not rebuild it. The
/// result is masked to 6 bits (a no-op), which tells the compiler it indexes a 64-entry word without a check.
#[inline(always)]
pub fn lowest_bit_tab(tab: &[u8; 64], x: u64) -> (t: u64)
    requires x != 0, tab@ == db_table(),
    ensures t == u64_trailing_zeros(x), t < 64,
    no_unwind
{
    proof {
        axiom_u64_trailing_zeros(x);
        lemma_isolate(x);
        lemma_db(u64_trailing_zeros(x) as u64);
    }
    let lb = x & !(x - 1);
    let slot = lb.wrapping_mul(DEBRUIJN64) >> 58u64;
    proof {
        assert(slot < 64) by (bit_vector) requires slot == lb.wrapping_mul(DEBRUIJN64) >> 58u64;
    }
    let v = tab[slot as usize];
    proof {
        assert(v < 64);
        assert(v & 63u8 == v) by (bit_vector) requires v < 64u8;
    }
    (v & 63u8) as u64
}


/// The index of the lowest set bit of a nonzero word by `u64::trailing_zeros` (one instruction). Its vstd
/// specification has no `no_unwind`, so only code that may unwind (the calling thread, not a worker) uses it.
#[inline(always)]
pub fn lowest_bit_tz(x: u64) -> (t: u64)
    requires x != 0,
    ensures t == u64_trailing_zeros(x), t < 64,
{
    proof {
        axiom_u64_trailing_zeros(x);
    }
    let z = x.trailing_zeros() as u64;
    proof {
        assert(z < 64);
        assert(z & 63u64 == z) by (bit_vector) requires z < 64u64;
    }
    z & 63u64
}

/// The lowest set bit index: `trailing_zeros` when `fast` (may unwind), else the de Bruijn lookup (`no_unwind`).
#[inline(always)]
pub fn lowest_bit_sel(tab: &[u8; 64], x: u64, fast: bool) -> (t: u64)
    requires x != 0, tab@ == db_table(),
    ensures t == u64_trailing_zeros(x), t < 64,
    no_unwind when !fast
{
    if fast { lowest_bit_tz(x) } else { lowest_bit_tab(tab, x) }
}

} // verus!
