//! 64-bit words of 0/1 flags: bit `j` of a word is `(w >> j) & 1`. `set_bit` adds the next bit of a word built
//! from the low bit up; `mask_word` maps a chunk of 64 u8 codes through a 64-bit mask (bit `j` of the result is
//! bit `chunk[j]` of the mask; every code below 64), a fixed-width loop without branches that the compiler
//! turns into vector shifts (a chunk of constant length, so no bounds checks); `all_below64` tests that
//! precondition.
use vstd::prelude::*;

verus! {

/// Bit `j` of `w` is set.
pub open spec fn wbit(w: u64, j: int) -> bool {
    (w >> (j as u64)) & 1 == 1
}

/// Bit `j` of `w | (f << j)` is `f` and the lower bits are unchanged, when `w` has no bit at `j` or above.
pub proof fn lemma_set_bit(w: u64, f: u64, j: u64)
    requires j < 64, f <= 1, w >> j == 0,
    ensures
        forall|q: u64| q < j ==> #[trigger] (((w | (f << j)) >> q) & 1) == ((w >> q) & 1),
        (((w | (f << j)) >> j) & 1) == f,
        j < 63 ==> ((w | (f << j)) >> ((j + 1) as u64)) == 0,
{
    assert forall|q: u64| q < j implies #[trigger] (((w | (f << j)) >> q) & 1) == ((w >> q) & 1) by {
        assert((((w | (f << j)) >> q) & 1) == ((w >> q) & 1)) by (bit_vector)
            requires j < 64, f <= 1, w >> j == 0, q < j;
    }
    assert((((w | (f << j)) >> j) & 1) == f) by (bit_vector)
        requires j < 64, f <= 1, w >> j == 0;
    if j < 63 {
        let j1: u64 = (j + 1) as u64;
        assert(((w | (f << j)) >> j1) == 0) by (bit_vector)
            requires j < 63, j1 == j + 1, f <= 1, w >> j == 0;
    }
}

/// A bit of a word is 0 or 1.
pub proof fn lemma_bit01(w: u64, q: u64)
    ensures (w >> q) & 1 <= 1,
{
    assert((w >> q) & 1 <= 1) by (bit_vector);
}

/// The empty word has no bit at or above 0.
pub proof fn lemma_zero_word()
    ensures (0u64 >> 0u64) == 0,
{
    assert((0u64 >> 0u64) == 0) by (bit_vector);
}

/// One flag added to the word built so far: `w` holds bits `[0, j)`, the result holds `[0, j]`.
#[inline(always)]
pub fn push_bit(w: u64, f: u64, j: u64) -> (r: u64)
    requires j < 64, f <= 1, w >> j == 0,
    ensures
        forall|q: int| 0 <= q < j ==> #[trigger] wbit(r, q) == wbit(w, q),
        wbit(r, j as int) == (f == 1),
        j < 63 ==> (r >> ((j + 1) as u64)) == 0,
    no_unwind
{
    proof {
        lemma_set_bit(w, f, j);
        assert forall|q: int| 0 <= q < j implies #[trigger] wbit(w | (f << j), q) == wbit(w, q) by {
            assert((((w | (f << j)) >> (q as u64)) & 1) == ((w >> (q as u64)) & 1));
        }
    }
    w | (f << j)
}

/// Every code of the 64-code chunk is below 64.
pub fn all_below64(chunk: &[u8]) -> (r: bool)
    requires chunk@.len() == 64,
    ensures r == forall|j: int| 0 <= j < 64 ==> #[trigger] chunk@[j] < 64,
    no_unwind
{
    let mut any: u32 = 0;
    let mut j: usize = 0;
    while j < 64
        invariant
            chunk@.len() == 64,
            j <= 64, any <= 1,
            (any == 0) == forall|q: int| 0 <= q < j ==> #[trigger] chunk@[q] < 64,
        decreases 64 - j,
    {
        let b: u32 = if chunk[j] >= 64 { 1 } else { 0 };
        proof {
            super::chunk::lemma_or01(any, b);
        }
        any = any | b;
        j = j + 1;
    }
    any == 0
}

/// The word whose bit `j` is bit `chunk[j]` of `m`, for a chunk of 64 codes below 64.
pub fn mask_word(chunk: &[u8], m: u64) -> (w: u64)
    requires
        chunk@.len() == 64,
        forall|j: int| 0 <= j < 64 ==> #[trigger] chunk@[j] < 64,
    ensures forall|j: int| 0 <= j < 64 ==> #[trigger] wbit(w, j) == wbit(m, chunk@[j] as int),
    no_unwind
{
    let mut w: u64 = 0;
    let mut j: usize = 0;
    proof {
        lemma_zero_word();
    }
    while j < 64
        invariant
            chunk@.len() == 64,
            forall|q: int| 0 <= q < 64 ==> #[trigger] chunk@[q] < 64,
            j <= 64,
            j < 64 ==> (w >> (j as u64)) == 0,
            forall|q: int| 0 <= q < j ==> #[trigger] wbit(w, q) == wbit(m, chunk@[q] as int),
        decreases 64 - j,
    {
        let code = chunk[j] as u64;
        proof {
            assert(chunk@[j as int] < 64);
            lemma_bit01(m, code);
        }
        let f = (m >> code) & 1;
        let ghost w0 = w;
        w = push_bit(w, f, j as u64);
        proof {
            assert forall|q: int| 0 <= q < j + 1 implies #[trigger] wbit(w, q) == wbit(m, chunk@[q] as int) by {
                if q < j {
                    assert(wbit(w, q) == wbit(w0, q));
                }
            }
        }
        j = j + 1;
    }
    w
}

} // verus!
