//! A bitmap of `64 * words.len()` bits: bit `i` is bit `i % 64` of word `i / 64`. A filter over hashed nodes keeps
//! the bit of every node set (`filter_wf`), so a clear bit proves that no node has that bit.
use vstd::prelude::*;

verus! {

/// Bit `i` of the bitmap is set.
pub open spec fn bit_set(words: Seq<u64>, i: int) -> bool {
    0 <= i < 64 * words.len() && (words[i / 64] >> ((i % 64) as u64)) & 1u64 == 1u64
}

/// Every node `x < len` with `inset(x)` has its bit `fbit(x)` set.
pub open spec fn filter_wf(words: Seq<u64>, inset: spec_fn(int) -> bool, fbit: spec_fn(int) -> int, len: int) -> bool {
    forall|x: int| 0 <= x < len && #[trigger] inset(x) ==> bit_set(words, fbit(x))
}

proof fn lemma_split(i: usize)
    ensures i >> 6usize == i / 64, i & 63usize == i % 64,
{
    assert(i >> 6usize == i / 64) by (bit_vector);
    assert(i & 63usize == i % 64) by (bit_vector);
}

/// Bit `i` of the bitmap.
#[inline(always)]
pub fn test_bit(words: &Vec<u64>, i: usize, Ghost(nw): Ghost<int>) -> (r: bool)
    requires nw == words@.len(), i < 64 * nw,
    ensures r == bit_set(words@, i as int),
    no_unwind
{
    proof {
        lemma_split(i);
    }
    let w = words[i >> 6usize];
    let sh = (i & 63usize) as u64;
    (w >> sh) & 1u64 == 1u64
}

/// The bitmap with bit `i` set as well.
#[inline(always)]
pub fn set_bit(words: &mut Vec<u64>, i: usize, Ghost(nw): Ghost<int>)
    requires nw == old(words)@.len(), i < 64 * nw,
    ensures
        final(words)@.len() == nw,
        bit_set(final(words)@, i as int),
        forall|j: int| #[trigger] bit_set(old(words)@, j) ==> bit_set(final(words)@, j),
    no_unwind
{
    proof {
        lemma_split(i);
    }
    let wi = i >> 6usize;
    let sh = (i & 63usize) as u64;
    let w = words[wi];
    let w2 = w | (1u64 << sh);
    proof {
        assert((w2 >> sh) & 1u64 == 1u64) by (bit_vector) requires w2 == w | (1u64 << sh), sh < 64;
        assert forall|j: int| #[trigger] bit_set(old(words)@, j) implies bit_set(old(words)@.update(wi as int, w2), j) by {
            if j / 64 == wi as int {
                let sj = (j % 64) as u64;
                assert(sj < 64);
                assert((w >> sj) & 1u64 == 1u64 ==> (w2 >> sj) & 1u64 == 1u64) by (bit_vector)
                    requires w2 == w | (1u64 << sh), sh < 64, sj < 64;
            }
        }
    }
    words[wi] = w2;
}

} // verus!
