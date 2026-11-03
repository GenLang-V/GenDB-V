//! Bit sets of positions `0..64 * words.len()` held in `u64` words: position `o` is bit `o % 64` of word `o / 64`
//! (`bit_at`). Operations for worker tasks (`no_unwind`): test a bit, set a bit (`test_set`, which also says
//! whether it was clear), and copy one word from another bit set (restoring the bits of that word).
use vstd::prelude::*;

verus! {

/// Bit `o` of a word sequence.
pub open spec fn bit_at(words: Seq<u64>, o: int) -> bool {
    (words[o / 64] >> ((o % 64) as u64)) & 1u64 == 1u64
}

/// Position `o` lies in the bit set.
pub open spec fn in_bits(words: Seq<u64>, o: int) -> bool {
    0 <= o && o / 64 < words.len()
}

/// Bit `o` of the bit set.
#[verifier::spinoff_prover]
pub fn test_bit(words: &Vec<u64>, o: u64) -> (r: bool)
    requires in_bits(words@, o as int),
    ensures r == bit_at(words@, o as int),
    no_unwind
{
    let _n = words.len();
    proof {
        assert((o / 64) as int == (o as int) / 64);
        assert((o as int) / 64 < words@.len());
    }
    let wi = (o / 64) as usize;
    let w = words[wi];
    let b = o % 64;
    proof {
        assert(wi as int == (o as int) / 64);
        assert(b as int == (o as int) % 64);
        assert(((o as int) % 64) as u64 == b);
        assert(w == words@[(o as int) / 64]);
    }
    (w >> b) & 1u64 == 1u64
}

/// Set bit `o`; returns whether it was clear. Every other bit is unchanged.
#[verifier::spinoff_prover]
pub fn test_set(words: &mut Vec<u64>, o: u64) -> (was_clear: bool)
    requires in_bits(old(words)@, o as int),
    ensures
        final(words)@.len() == old(words)@.len(),
        was_clear == !bit_at(old(words)@, o as int),
        bit_at(final(words)@, o as int),
        forall|p: int| 0 <= p && p != o && #[trigger] bit_at(final(words)@, p) != bit_at(old(words)@, p) ==> !in_bits(old(words)@, p),
    no_unwind
{
    let _n = words.len();
    proof {
        assert((o / 64) as int == (o as int) / 64);
        assert((o as int) / 64 < words@.len());
    }
    let wi = (o / 64) as usize;
    let b = o % 64;
    proof {
        assert(wi as int == (o as int) / 64);
        assert(b as int == (o as int) % 64);
        assert(((o as int) % 64) as u64 == b);
    }
    let x = words[wi];
    let m = 1u64 << b;
    let was_clear = x & m == 0;
    let y = x | m;
    words[wi] = y;
    proof {
        assert(old(words)@[(o as int) / 64] == x);
        assert(words@[(o as int) / 64] == y);
        assert(was_clear == !((x >> b) & 1u64 == 1u64)) by (bit_vector) requires b < 64, m == 1u64 << b, was_clear == (x & m == 0);
        assert((y >> b) & 1u64 == 1u64) by (bit_vector) requires b < 64, m == 1u64 << b, y == x | m;
        assert forall|p: int| 0 <= p && p != o && #[trigger] bit_at(words@, p) != bit_at(old(words)@, p) implies !in_bits(old(words)@, p) by {
            if in_bits(old(words)@, p) {
                if p / 64 == wi as int {
                    let c = (p % 64) as u64;
                    assert(c != b) by {
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(p, 64);
                        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(o as int, 64);
                        vstd::arithmetic::div_mod::lemma_mod_bound(p, 64);
                        let (qp, qo) = (p / 64, (o as int) / 64);
                        assert(qp == qo);
                        if c == b {
                            assert(p == 64 * qp + (p % 64));
                            assert(o as int == 64 * qo + ((o as int) % 64));
                            assert(p % 64 == (o as int) % 64);
                            assert(p == o as int);
                        }
                    }
                    assert(c < 64);
                    assert(((y >> c) & 1u64 == 1u64) == ((x >> c) & 1u64 == 1u64)) by (bit_vector)
                        requires b < 64, c < 64, c != b, m == 1u64 << b, y == x | m;
                } else {
                    assert(words@[p / 64] == old(words)@[p / 64]);
                }
            }
        }
    }
    was_clear
}

/// Copy the word holding position `o` from `src` (same length): the bits of that word become those of `src`, the
/// others are unchanged.
#[verifier::spinoff_prover]
pub fn copy_word(words: &mut Vec<u64>, src: &Vec<u64>, o: u64)
    requires in_bits(old(words)@, o as int), src@.len() == old(words)@.len(),
    ensures
        final(words)@.len() == old(words)@.len(),
        forall|p: int| 0 <= p && p / 64 == o / 64 ==> #[trigger] bit_at(final(words)@, p) == bit_at(src@, p),
        forall|p: int| 0 <= p && p / 64 != o / 64 ==> #[trigger] bit_at(final(words)@, p) == bit_at(old(words)@, p),
    no_unwind
{
    let _n = words.len();
    proof {
        assert((o / 64) as int == (o as int) / 64);
        assert((o as int) / 64 < words@.len());
    }
    let wi = (o / 64) as usize;
    proof { assert(wi as int == (o as int) / 64); }
    words[wi] = src[wi];
    proof {
        assert forall|p: int| 0 <= p && p / 64 == o / 64 implies #[trigger] bit_at(words@, p) == bit_at(src@, p) by {
            assert(words@[p / 64] == src@[p / 64]);
        }
        assert forall|p: int| 0 <= p && p / 64 != o / 64 implies #[trigger] bit_at(words@, p) == bit_at(old(words)@, p) by {
            if p / 64 < words@.len() { assert(words@[p / 64] == old(words)@[p / 64]); }
        }
    }
}

} // verus!
