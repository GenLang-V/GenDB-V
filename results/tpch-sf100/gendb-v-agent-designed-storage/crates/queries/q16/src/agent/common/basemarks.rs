//! A bitmap of marked elements over a fixed base bitmap (`Vec<u64>`, element `x` is bit `x % 64` of word `x / 64`):
//! the base's bits are pre-set, so one bit test tells both "in the base" and "already marked" (for example a
//! distinct count that skips an excluded set).
//!
//! `holds_over(m, base, s)`: over every bit position `x < 64 * m.len()`, bit `x` of `m` is set exactly when it is set
//! in `base` or `s` holds `x`. `copy_base` starts with `s` empty; `mark_over` sets a clear bit and tells whether it
//! was clear (so the caller counts elements neither in the base nor seen before); `restore_word` resets the whole
//! word of an element to the base's word (so restoring the words of every marked element gives `s` empty again).
use vstd::prelude::*;
use super::marks::bit_at;

verus! {

/// `m` is `base` with the elements of `s` marked as well.
pub open spec fn holds_over(m: Seq<u64>, base: Seq<u64>, s: Set<int>) -> bool {
    &&& m.len() == base.len()
    &&& forall|x: int| 0 <= x < 64 * m.len() ==> (#[trigger] bit_at(m, x) <==> (bit_at(base, x) || s.contains(x)))
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

/// A copy of `base`: no element marked yet.
pub fn copy_base(base: &Vec<u64>) -> (m: Vec<u64>)
    ensures holds_over(m@, base@, Set::empty()),
{
    let n = base.len();
    let mut m: Vec<u64> = Vec::with_capacity(n);
    let mut w: usize = 0;
    while w < n
        invariant n == base@.len(), w <= n, m@.len() == w, forall|w2: int| 0 <= w2 < w ==> #[trigger] m@[w2] == base@[w2],
        decreases n - w,
    {
        m.push(base[w]);
        w = w + 1;
    }
    proof {
        assert(m@ =~= base@);
    }
    m
}

/// Marks `x` unless its bit is already set: true exactly when it was clear (`x` neither in the base nor in `s`).
#[inline(always)]
pub fn mark_over(m: &mut Vec<u64>, x: usize, Ghost(base): Ghost<Seq<u64>>, Ghost(s): Ghost<Set<int>>) -> (fresh: bool)
    requires
        (x as int) < 64 * old(m)@.len(),
        holds_over(old(m)@, base, s),
    ensures
        final(m)@.len() == old(m)@.len(),
        fresh == !(bit_at(base, x as int) || s.contains(x as int)),
        fresh ==> holds_over(final(m)@, base, s.insert(x as int)),
        !fresh ==> final(m)@ == old(m)@,
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
            assert forall|y: int| 0 <= y < 64 * m@.len() implies
                (#[trigger] bit_at(m@, y) <==> (bit_at(base, y) || s.insert(x as int).contains(y))) by {
                lemma_word_in(y, m@.len() as int);
                assert(bit_at(m0, y) <==> (bit_at(base, y) || s.contains(y)));
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
        false
    }
}

/// Resets the word of `x` to the base's word: every element of that word leaves the set.
#[inline(always)]
pub fn restore_word(m: &mut Vec<u64>, base: &Vec<u64>, x: usize, Ghost(s): Ghost<Set<int>>)
    requires
        (x as int) < 64 * old(m)@.len(),
        holds_over(old(m)@, base@, s),
    ensures
        final(m)@.len() == old(m)@.len(),
        holds_over(final(m)@, base@, s.filter(|y: int| y / 64 != (x as int) / 64)),
    no_unwind
{
    proof {
        lemma_split(x as u64);
        lemma_word_in(x as int, m@.len() as int);
    }
    let w = x >> 6;
    m[w] = base[w];
    proof {
        let m0 = old(m)@;
        let s2 = s.filter(|y: int| y / 64 != (x as int) / 64);
        assert forall|y: int| 0 <= y < 64 * m@.len() implies
            (#[trigger] bit_at(m@, y) <==> (bit_at(base@, y) || s2.contains(y))) by {
            lemma_word_in(y, m@.len() as int);
            if y / 64 == w as int {
                assert(m@[y / 64] == base@[y / 64]);
                assert(!s2.contains(y));
            } else {
                assert(m@[y / 64] == m0[y / 64]);
                assert(bit_at(m@, y) == bit_at(m0, y));
                assert(bit_at(m0, y) <==> (bit_at(base@, y) || s.contains(y)));
            }
        }
    }
}

/// Resets every word to the base's: no element marked.
pub fn restore_all(m: &mut Vec<u64>, base: &Vec<u64>)
    requires old(m)@.len() == base@.len(),
    ensures holds_over(final(m)@, base@, Set::empty()),
    no_unwind
{
    let n = m.len();
    let mut w: usize = 0;
    while w < n
        invariant n == m@.len(), n == base@.len(), w <= n, forall|w2: int| 0 <= w2 < w ==> #[trigger] m@[w2] == base@[w2],
        decreases n - w,
    {
        m[w] = base[w];
        w = w + 1;
    }
    proof {
        assert(m@ =~= base@);
    }
}

} // verus!
