//! Fixed-width chunk tests over code slices: whether a chunk of `W` consecutive codes holds a given code. The test
//! ORs one 0/1 flag per element over a subslice of known length, without an early exit, so the compiler can turn
//! it into a few vector compares; a scan skips a whole chunk when the test is false.
use vstd::prelude::*;

verus! {

/// Codes per chunk of `has_u8`.
pub const W8: usize = 32;

/// Two 0/1 flags OR to a 0/1 flag that is 0 exactly when both are 0.
pub proof fn lemma_or01(a: u32, b: u32)
    requires a <= 1, b <= 1,
    ensures (a | b) <= 1, ((a | b) == 0) == (a == 0 && b == 0),
{
    assert((a | b) <= 1 && (((a | b) == 0) == (a == 0 && b == 0))) by (bit_vector)
        requires a <= 1, b <= 1;
}

/// Some code of `codes[i .. i + W8)` equals `t`.
pub fn has_u8(codes: &[u8], i: usize, t: u8) -> (r: bool)
    requires i + W8 <= codes@.len(),
    ensures r == exists|j: int| i <= j < i + W8 && #[trigger] codes@[j] == t,
    no_unwind
{
    let mut any: u32 = 0;
    let mut j: usize = 0;
    while j < W8
        invariant
            i + W8 <= codes@.len(),
            j <= W8, any <= 1,
            (any == 0) == forall|q: int| i <= q < i + j ==> #[trigger] codes@[q] != t,
        decreases W8 - j,
    {
        let b: u32 = if codes[i + j] == t { 1 } else { 0 };
        proof {
            lemma_or01(any, b);
        }
        any = any | b;
        j = j + 1;
    }
    any != 0
}

} // verus!
