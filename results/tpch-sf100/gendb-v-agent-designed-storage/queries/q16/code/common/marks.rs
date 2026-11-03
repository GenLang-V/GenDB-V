//! A bitmap of seen elements (`Vec<u64>`, element `x` is bit `x % 64` of word `x / 64`) with a set view, for
//! counting distinct small integers without allocation (usable in worker bodies).
//!
//! `holds(m, s)`: over every bit position `x < 64 * m.len()`, bit `x` is set exactly when `s` holds `x`.
//! `mark_new` sets an element's bit and tells whether it was clear (so the caller counts first sightings);
//! `clear_word` clears the whole word of an element (so clearing the words of every element seen restores the empty
//! set, whatever else shares their words).
use vstd::prelude::*;

verus! {

/// Bit `x` of the bitmap `m`.
pub open spec fn bit_at(m: Seq<u64>, x: int) -> bool {
    ((m[x / 64] >> ((x % 64) as u64)) & 1u64) == 1u64
}

/// The bitmap `m` represents the set `s` of bit positions.
pub open spec fn holds(m: Seq<u64>, s: Set<int>) -> bool {
    forall|x: int| 0 <= x < 64 * m.len() ==> (#[trigger] bit_at(m, x) <==> s.contains(x))
}

/// Setting bit `b` of a word leaves the other bits.
proof fn lemma_or_bit(w: u64, b: u64, c: u64)
    by (bit_vector)
    requires b < 64, c < 64,
    ensures (((w | (1u64 << b)) >> c) & 1u64 == 1u64) == (c == b || ((w >> c) & 1u64) == 1u64),
{
}

/// A word's bit `b` is clear exactly when its `and` with `2^b` is zero.
proof fn lemma_and_bit(w: u64, b: u64)
    by (bit_vector)
    requires b < 64,
    ensures ((w & (1u64 << b)) == 0u64) == (((w >> b) & 1u64) != 1u64),
{
}

/// No bit of zero is set.
proof fn lemma_zero_bit(c: u64)
    by (bit_vector)
    requires c < 64,
    ensures ((0u64 >> c) & 1u64) != 1u64,
{
}

/// Word and bit of an element by shifts.
proof fn lemma_split(x: u64)
    by (bit_vector)
    ensures x >> 6u64 == x / 64, x & 63u64 == x % 64,
{
}

/// The bit position of an element below 64 words lies in a word of the bitmap.
proof fn lemma_word_in(x: int, len: int)
    requires 0 <= x < 64 * len,
    ensures 0 <= x / 64 < len, 0 <= x % 64 < 64,
{
}

/// Bit `x` of the bitmap.
#[inline(always)]
pub fn get_bit(m: &Vec<u64>, x: usize) -> (r: bool)
    requires (x as int) < 64 * m@.len(),
    ensures r == bit_at(m@, x as int),
    no_unwind
{
    proof {
        lemma_split(x as u64);
        lemma_word_in(x as int, m@.len() as int);
    }
    let w = x >> 6;
    let b = x & 63;
    ((m[w] >> (b as u64)) & 1u64) == 1u64
}

/// An all-zero bitmap represents the empty set.
pub proof fn lemma_zero_holds(m: Seq<u64>)
    requires forall|w: int| 0 <= w < m.len() ==> #[trigger] m[w] == 0u64,
    ensures holds(m, Set::empty()),
{
    assert forall|x: int| 0 <= x < 64 * m.len() implies (#[trigger] bit_at(m, x) <==> Set::<int>::empty().contains(x)) by {
        lemma_word_in(x, m.len() as int);
        lemma_zero_bit((x % 64) as u64);
    }
}

/// Marks `x`: true exactly when `x` was not yet marked.
#[inline(always)]
pub fn mark_new(m: &mut Vec<u64>, x: usize, Ghost(s): Ghost<Set<int>>) -> (fresh: bool)
    requires
        (x as int) < 64 * old(m)@.len(),
        holds(old(m)@, s),
    ensures
        final(m)@.len() == old(m)@.len(),
        fresh == !s.contains(x as int),
        holds(final(m)@, s.insert(x as int)),
    no_unwind
{
    proof {
        lemma_split(x as u64);
        lemma_word_in(x as int, m@.len() as int);
    }
    let w = x >> 6;
    let b = x & 63;
    let bit: u64 = 1u64 << (b as u64);
    let mw = m[w];
    proof {
        lemma_and_bit(mw, b as u64);
        assert(bit_at(old(m)@, x as int) == (((mw >> (b as u64)) & 1u64) == 1u64));
    }
    if mw & bit == 0 {
        m[w] = mw | bit;
        proof {
            let m0 = old(m)@;
            assert forall|y: int| 0 <= y < 64 * m@.len() implies (#[trigger] bit_at(m@, y) <==> s.insert(x as int).contains(y)) by {
                lemma_word_in(y, m@.len() as int);
                if y / 64 == w as int {
                    lemma_or_bit(mw, b as u64, (y % 64) as u64);
                    assert(bit_at(m0, y) == (((mw >> ((y % 64) as u64)) & 1u64) == 1u64));
                    if (y % 64) == b as int {
                        assert(y == x as int);
                    }
                    if y == x as int {
                        assert((y % 64) == b as int);
                    }
                } else {
                    assert(m@[y / 64] == m0[y / 64]);
                    assert(bit_at(m@, y) == bit_at(m0, y));
                    assert(y != x as int);
                }
            }
        }
        true
    } else {
        proof {
            assert(s.insert(x as int) =~= s);
        }
        false
    }
}

/// Clears the word of `x`: every element of that word leaves the set.
#[inline(always)]
pub fn clear_word(m: &mut Vec<u64>, x: usize, Ghost(s): Ghost<Set<int>>)
    requires
        (x as int) < 64 * old(m)@.len(),
        holds(old(m)@, s),
    ensures
        final(m)@.len() == old(m)@.len(),
        holds(final(m)@, s.filter(|y: int| y / 64 != (x as int) / 64)),
    no_unwind
{
    proof {
        lemma_split(x as u64);
        lemma_word_in(x as int, m@.len() as int);
    }
    let w = x >> 6;
    m[w] = 0;
    proof {
        let m0 = old(m)@;
        let s2 = s.filter(|y: int| y / 64 != (x as int) / 64);
        assert forall|y: int| 0 <= y < 64 * m@.len() implies (#[trigger] bit_at(m@, y) <==> s2.contains(y)) by {
            lemma_word_in(y, m@.len() as int);
            if y / 64 == w as int {
                lemma_zero_bit((y % 64) as u64);
            } else {
                assert(m@[y / 64] == m0[y / 64]);
                assert(bit_at(m@, y) == bit_at(m0, y));
            }
        }
    }
}

} // verus!
