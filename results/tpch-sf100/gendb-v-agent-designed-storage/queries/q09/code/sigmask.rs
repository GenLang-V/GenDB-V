//! The trigram mask of a word for storage `partsig`'s p_name signatures: the OR of the signature bits of all its
//! trigrams (`word_mask`; 0 for a word shorter than three bytes). A text whose signature covers it and that contains
//! the word has every bit of the mask in its signature (`lemma_skip`), so a row whose signature lacks a mask bit can
//! be skipped without reading its name.
use vstd::prelude::*;
use crate::stores::partsig::interface as gi;
use super::common::like_word::{occurs_at, contains};

verus! {

/// The OR of the bits of the trigrams of `w` starting at `0 .. k`.
pub open spec fn wmask(w: Seq<u8>, k: int) -> u64
    decreases k,
{
    if k <= 0 { 0u64 } else { wmask(w, k - 1) | gi::tri_bit(w[k - 1], w[k], w[k + 1]) }
}

/// The trigram mask of `w`.
pub open spec fn word_mask(w: Seq<u8>) -> u64 {
    if w.len() >= 3 { wmask(w, w.len() - 2) } else { 0u64 }
}

/// Two subsets of `s` make a subset.
proof fn lemma_and_or(s: u64, a: u64, b: u64)
    requires s & a == a, s & b == b,
    ensures s & (a | b) == (a | b),
{
    assert((s & a == a && s & b == b) ==> s & (a | b) == (a | b)) by (bit_vector);
}

/// The empty set is a subset.
proof fn lemma_and_zero(s: u64)
    ensures s & 0u64 == 0u64,
{
    assert(s & 0u64 == 0u64) by (bit_vector);
}

/// A signature with the bits of the trigrams `0 .. k` of `w` has their mask.
proof fn lemma_wmask_in(s: u64, w: Seq<u8>, k: int)
    requires 0 <= k, k + 2 <= w.len(), forall|q: int| 0 <= q < k ==> #[trigger] gi::has_tri(s, w, q),
    ensures s & wmask(w, k) == wmask(w, k),
    decreases k,
{
    if k > 0 {
        lemma_wmask_in(s, w, k - 1);
        assert(gi::has_tri(s, w, k - 1));
        lemma_and_or(s, wmask(w, k - 1), gi::tri_bit(w[k - 1], w[k], w[k + 1]));
    } else {
        lemma_and_zero(s);
    }
}

/// A text containing `w` with a covering signature `s`: `s` has the mask of `w`.
pub proof fn lemma_skip(t: Seq<u8>, s: u64, w: Seq<u8>)
    requires gi::sig_covers(t, s), contains(t, w),
    ensures s & word_mask(w) == word_mask(w),
{
    let i = choose|i: int| #[trigger] occurs_at(t, w, i);
    if w.len() >= 3 {
        assert forall|q: int| 0 <= q < w.len() - 2 implies #[trigger] gi::has_tri(s, w, q) by {
            gi::lemma_sub_tri(t, s, w, i, q);
        }
        lemma_wmask_in(s, w, w.len() - 2);
    } else {
        lemma_and_zero(s);
    }
}

/// The trigram mask of the word `pat[wl .. wl + wn]`.
pub fn word_mask_exec(pat: &[u8], wl: usize, wn: usize) -> (r: u64)
    requires wl + wn <= pat@.len() <= usize::MAX,
    ensures r == word_mask(pat@.subrange(wl as int, wl + wn)),
{
    let ghost w = pat@.subrange(wl as int, wl + wn);
    if wn < 3 {
        return 0;
    }
    let mut r: u64 = 0;
    let mut q: usize = 0;
    while q + 2 < wn
        invariant
            wl + wn <= pat@.len() <= usize::MAX, wn >= 3, w == pat@.subrange(wl as int, wl + wn),
            q + 2 <= wn,
            r == wmask(w, q as int),
        decreases wn - q,
    {
        let b = gi::tri_bit_exec(pat[wl + q], pat[wl + q + 1], pat[wl + q + 2]);
        proof {
            assert(w[q as int] == pat@[wl + q] && w[q + 1] == pat@[wl + q + 1] && w[q + 2] == pat@[wl + q + 2]);
            assert(wmask(w, q + 1) == wmask(w, q as int) | gi::tri_bit(w[q as int], w[q + 1], w[q + 2]));
        }
        r = r | b;
        q = q + 1;
    }
    r
}

} // verus!
