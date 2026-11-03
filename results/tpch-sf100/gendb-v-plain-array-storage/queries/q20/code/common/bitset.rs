//! Bitmaps over non-negative integers stored as 64-bit words (bit `v % 64` of word `v / 64`, `wbit`), with a
//! `no_unwind` membership test (`wbit_test`) and an insertion (`wbit_set`), plus the single-word facts used to
//! iterate the set bits of a mask from the lowest (`trailing_zeros`, clearing the lowest set bit). Each fact is
//! one small `bit_vector` lemma.
use vstd::prelude::*;
use vstd::std_specs::bits::axiom_u64_trailing_zeros;

verus! {

/// Bit `u` of `m` (positions `0..64`).
pub open spec fn bit(m: u64, u: u64) -> bool { (m >> u) & 1u64 == 1u64 }

/// Integer `v` is in the bitmap: bit `v % 64` of word `v / 64`.
pub open spec fn wbit(words: Seq<u64>, v: int) -> bool {
    0 <= v && v / 64 < words.len() && bit(words[v / 64], (v % 64) as u64)
}

/// Setting bit `t`: bit `u` is set afterwards exactly when it was or `u == t`.
pub proof fn lemma_bit_or(w: u64, t: u64, u: u64)
    requires t < 64, u < 64,
    ensures bit(w | (1u64 << t), u) == (bit(w, u) || u == t),
{
    assert((t < 64 && u < 64) ==> ((((w | (1u64 << t)) >> u) & 1u64 == 1u64) == (((w >> u) & 1u64 == 1u64) || u == t))) by (bit_vector);
}

/// The empty mask.
pub proof fn lemma_bit_zero(u: u64)
    ensures !bit(0, u),
{
    assert((0u64 >> u) & 1u64 != 1u64) by (bit_vector);
}

/// Word and bit position of an integer: `v >> 6 == v / 64`, `v & 63 == v % 64`.
pub proof fn lemma_word_pos(v: u64)
    ensures (v >> 6u64) as int == v as int / 64, (v & 63u64) as int == v as int % 64, v & 63u64 < 64,
{
    assert(v >> 6u64 == v / 64) by (bit_vector);
    assert(v & 63u64 == v % 64) by (bit_vector);
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
        lemma_low_bits_zero(c, s);
        assert((c & sub(sub(1u64 << s, 1), 0) == 0u64 && ((c >> s) & 1u64 == 1u64) && s < 64) ==>
            (((c & sub(c, 1)) >> s) & 1u64 != 1u64)) by (bit_vector);
    } else {
        lemma_low_bits_zero(c, s);
        assert((c & sub(sub(1u64 << s, 1), 0) == 0u64 && ((c >> s) & 1u64 == 1u64) && s < u && u < 64) ==>
            ((((c & sub(c, 1)) >> u) & 1u64 == 1u64) == ((c >> u) & 1u64 == 1u64))) by (bit_vector);
    }
}

/// A mask with no set bit is zero.
pub proof fn lemma_no_bits_zero(c: u64)
    requires forall|u: u64| u < 64 ==> !#[trigger] bit(c, u),
    ensures c == 0,
{
    lemma_low_bits_zero(c, 63);
    assert(!bit(c, 63));
    assert((c & sub(sub(1u64 << 63u64, 1), 0) == 0u64 && (c >> 63u64) & 1u64 != 1u64) ==> c == 0) by (bit_vector);
}

/// Whether `v` is in the bitmap of `nwords` words (`no_unwind`).
pub fn wbit_test(words: &Vec<u64>, nwords: usize, v: u64) -> (r: bool)
    requires nwords == words@.len(),
    ensures r == wbit(words@, v as int),
    no_unwind
{
    proof { lemma_word_pos(v); }
    let w = v >> 6u64;
    if w < nwords as u64 {
        (words[w as usize] >> (v & 63u64)) & 1u64 == 1u64
    } else {
        false
    }
}

/// Insert `v` into the bitmap.
pub fn wbit_set(words: &mut Vec<u64>, v: u64)
    requires (v as int) / 64 < old(words)@.len(),
    ensures
        final(words)@.len() == old(words)@.len(),
        forall|u: int| #[trigger] wbit(final(words)@, u) == (wbit(old(words)@, u) || u == v as int),
{
    proof {
        lemma_word_pos(v);
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(v as int, 64);
    }
    let n = words.len();
    let w64 = v >> 6u64;
    assert((w64 as int) < n);
    let w = w64 as usize;
    assert(w as int == v as int / 64);
    let b = v & 63u64;
    let old_w = words[w];
    words[w] = old_w | (1u64 << b);
    proof {
        assert forall|u: int| #[trigger] wbit(words@, u) == (wbit(old(words)@, u) || u == v as int) by {
            if 0 <= u && u / 64 < words@.len() {
                vstd::arithmetic::div_mod::lemma_fundamental_div_mod(u, 64);
                let uw = u / 64;
                let ub = (u % 64) as u64;
                assert(0 <= u % 64 < 64);
                assert(ub as int == u % 64);
                assert(w as int == v as int / 64);
                assert(b as int == v as int % 64);
                if uw == w as int {
                    lemma_bit_or(old_w, b, ub);
                    if u == v as int {
                        assert(ub == b);
                    } else {
                        assert(ub != b);
                    }
                } else {
                    assert(words@[uw] == old(words)@[uw]);
                    assert(u != v as int);
                }
            }
        }
    }
}

} // verus!
