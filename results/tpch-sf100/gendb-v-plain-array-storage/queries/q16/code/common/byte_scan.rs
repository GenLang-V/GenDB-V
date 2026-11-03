//! Word-at-a-time scan of a byte range: whether every byte is ASCII (exact) and whether a given byte may occur
//! (never misses an occurrence), eight bytes per step.
//!
//! Each step reads the little-endian word of eight bytes (`text_dict::word_at`). ASCII: the OR of the words has no
//! high bit set. Byte `c`: a byte of `w` equals `c` exactly when the same byte of `z = w ^ rep(c)` is zero; `fold`
//! ORs the eight bits of every byte of `z` into that byte's lowest bit with shifts and masks that never cross a
//! byte, so `fold(z) != ONES` exactly when some byte of `z` is zero. A range of at least eight bytes is covered by
//! the words at `lo, lo + 8, ...` and one last word ending at `hi` (overlaps are harmless); shorter ranges are
//! scanned byte by byte.
use vstd::prelude::*;
use crate::agent::common::like_two::{ascii, has_two, sub_at};
use crate::agent::common::text_dict::{word_spec, word_at};

verus! {

/// `c` occurs in `s`.
pub open spec fn has_byte(s: Seq<u8>, c: u8) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == c
}

/// A text holding `a` (then `b`) holds the first byte of `a`: a scan that rules that byte out rules out `has_two`.
pub proof fn lemma_has_two_byte(s: Seq<u8>, a: Seq<u8>, b: Seq<u8>)
    requires a.len() >= 1, has_two(s, a, b),
    ensures has_byte(s, a[0]),
{
    let i = choose|i: int| #[trigger] sub_at(s, a, i) && crate::agent::common::like_two::has_sub(s.subrange(i + a.len(), s.len() as int), b);
    assert(s.subrange(i, i + a.len())[0] == s[i]);
}

/// The word whose eight bytes are `c`.
pub open spec fn rep(c: u8) -> u64 {
    let x = c as u64;
    x | (x << 8u64) | (x << 16u64) | (x << 24u64) | (x << 32u64) | (x << 40u64) | (x << 48u64) | (x << 56u64)
}

/// The lowest bit of every byte set.
pub const ONES: u64 = 0x0101_0101_0101_0101u64;

/// The high bit of every byte set.
pub const HIGHS: u64 = 0x8080_8080_8080_8080u64;

/// Every byte of `z` folded into its lowest bit: that bit is 1 exactly when the byte is not zero.
pub open spec fn fold(z: u64) -> u64 {
    let t1 = ((z >> 4u64) & 0x0F0F_0F0F_0F0F_0F0Fu64) | (z & 0x0F0F_0F0F_0F0F_0F0Fu64);
    let t2 = ((t1 >> 2u64) & 0x0303_0303_0303_0303u64) | (t1 & 0x0303_0303_0303_0303u64);
    ((t2 >> 1u64) & ONES) | (t2 & ONES)
}

fn rep_exec(c: u8) -> (r: u64)
    ensures r == rep(c),
    no_unwind
{
    let x = c as u64;
    x | (x << 8u64) | (x << 16u64) | (x << 24u64) | (x << 32u64) | (x << 40u64) | (x << 48u64) | (x << 56u64)
}

fn fold_exec(z: u64) -> (r: u64)
    ensures r == fold(z),
    no_unwind
{
    let t1 = ((z >> 4u64) & 0x0F0F_0F0F_0F0F_0F0Fu64) | (z & 0x0F0F_0F0F_0F0F_0F0Fu64);
    let t2 = ((t1 >> 2u64) & 0x0303_0303_0303_0303u64) | (t1 & 0x0303_0303_0303_0303u64);
    ((t2 >> 1u64) & ONES) | (t2 & ONES)
}

/// The word of bytes `i .. i + 8` has no high bit set exactly when those bytes are ASCII.
pub proof fn lemma_word_ascii(b: Seq<u8>, i: int)
    requires 0 <= i, i + 8 <= b.len(),
    ensures (word_spec(b, i) & HIGHS == 0) <==> (forall|k: int| 0 <= k < 8 ==> #[trigger] b[i + k] < 0x80u8),
{
    let (x0, x1, x2, x3, x4, x5, x6, x7) = (b[i], b[i + 1], b[i + 2], b[i + 3], b[i + 4], b[i + 5], b[i + 6], b[i + 7]);
    assert((((x0 as u64) | ((x1 as u64) << 8u64) | ((x2 as u64) << 16u64) | ((x3 as u64) << 24u64)
        | ((x4 as u64) << 32u64) | ((x5 as u64) << 40u64) | ((x6 as u64) << 48u64) | ((x7 as u64) << 56u64))
        & 0x8080_8080_8080_8080u64 == 0)
        <==> (x0 < 0x80u8 && x1 < 0x80u8 && x2 < 0x80u8 && x3 < 0x80u8 && x4 < 0x80u8 && x5 < 0x80u8 && x6 < 0x80u8
        && x7 < 0x80u8)) by (bit_vector);
    if forall|k: int| 0 <= k < 8 ==> #[trigger] b[i + k] < 0x80u8 {
        assert(b[i + 0] < 0x80u8 && b[i + 1] < 0x80u8 && b[i + 2] < 0x80u8 && b[i + 3] < 0x80u8);
        assert(b[i + 4] < 0x80u8 && b[i + 5] < 0x80u8 && b[i + 6] < 0x80u8 && b[i + 7] < 0x80u8);
    }
    if word_spec(b, i) & HIGHS == 0 {
        assert forall|k: int| 0 <= k < 8 implies #[trigger] b[i + k] < 0x80u8 by {
            if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else if k == 5 {} else if k == 6 {} else {}
        }
    }
}

/// When one of bytes `i .. i + 8` is `c`, the fold of the word xor `rep(c)` is not `ONES`.
pub proof fn lemma_word_byte(b: Seq<u8>, i: int, c: u8)
    requires 0 <= i, i + 8 <= b.len(),
    ensures (exists|k: int| 0 <= k < 8 && #[trigger] b[i + k] == c) ==> fold(word_spec(b, i) ^ rep(c)) != ONES,
{
    let (x0, x1, x2, x3, x4, x5, x6, x7) = (b[i], b[i + 1], b[i + 2], b[i + 3], b[i + 4], b[i + 5], b[i + 6], b[i + 7]);
    let w = word_spec(b, i);
    let z = w ^ rep(c);
    let t1 = ((z >> 4u64) & 0x0F0F_0F0F_0F0F_0F0Fu64) | (z & 0x0F0F_0F0F_0F0F_0F0Fu64);
    let t2 = ((t1 >> 2u64) & 0x0303_0303_0303_0303u64) | (t1 & 0x0303_0303_0303_0303u64);
    let fz = ((t2 >> 1u64) & 0x0101_0101_0101_0101u64) | (t2 & 0x0101_0101_0101_0101u64);
    assert(fz == fold(z));
    assert((x0 == c || x1 == c || x2 == c || x3 == c || x4 == c || x5 == c || x6 == c || x7 == c)
        ==> fz != 0x0101_0101_0101_0101u64)
        by (bit_vector)
        requires
            w == ((x0 as u64) | ((x1 as u64) << 8u64) | ((x2 as u64) << 16u64) | ((x3 as u64) << 24u64)
                | ((x4 as u64) << 32u64) | ((x5 as u64) << 40u64) | ((x6 as u64) << 48u64) | ((x7 as u64) << 56u64)),
            z == w ^ ((c as u64) | ((c as u64) << 8u64) | ((c as u64) << 16u64) | ((c as u64) << 24u64)
                | ((c as u64) << 32u64) | ((c as u64) << 40u64) | ((c as u64) << 48u64) | ((c as u64) << 56u64)),
            t1 == ((z >> 4u64) & 0x0F0F_0F0F_0F0F_0F0Fu64) | (z & 0x0F0F_0F0F_0F0F_0F0Fu64),
            t2 == ((t1 >> 2u64) & 0x0303_0303_0303_0303u64) | (t1 & 0x0303_0303_0303_0303u64),
            fz == ((t2 >> 1u64) & 0x0101_0101_0101_0101u64) | (t2 & 0x0101_0101_0101_0101u64);
    if exists|k: int| 0 <= k < 8 && #[trigger] b[i + k] == c {
        let k = choose|k: int| 0 <= k < 8 && #[trigger] b[i + k] == c;
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else if k == 5 {} else if k == 6 {} else {}
    }
}

/// OR-accumulating a word keeps "no high bit" exactly when both have none.
proof fn lemma_or_highs(a: u64, w: u64)
    ensures ((a | w) & HIGHS == 0) <==> (a & HIGHS == 0 && w & HIGHS == 0),
{
    assert(((a | w) & 0x8080_8080_8080_8080u64 == 0) <==> (a & 0x8080_8080_8080_8080u64 == 0 && w & 0x8080_8080_8080_8080u64 == 0))
        by (bit_vector);
}

/// Whether every byte of `b[lo..hi]` is ASCII (exact), and whether `c` may occur in it (`false` only when it does
/// not).
pub fn scan_ascii_byte(b: &[u8], lo: usize, hi: usize, c: u8) -> (r: (bool, bool))
    requires lo <= hi <= b@.len(),
    ensures
        r.0 == ascii(b@.subrange(lo as int, hi as int)),
        has_byte(b@.subrange(lo as int, hi as int), c) ==> r.1,
    no_unwind
{
    let ghost s = b@.subrange(lo as int, hi as int);
    let n = hi - lo;
    if n < 8 {
        // Byte by byte.
        let mut hb: u8 = 0;
        let mut seen = false;
        let mut i: usize = 0;
        while i < n
            invariant
                n == hi - lo, lo <= hi <= b@.len(), i <= n, s == b@.subrange(lo as int, hi as int),
                hb < 0x80u8 <==> forall|k: int| 0 <= k < i ==> #[trigger] s[k] < 0x80u8,
                !seen ==> forall|k: int| 0 <= k < i ==> #[trigger] s[k] != c,
            decreases n - i,
        {
            let x = b[lo + i];
            proof {
                assert(s[i as int] == x);
                assert((hb | x) < 0x80u8 <==> (hb < 0x80u8 && x < 0x80u8)) by (bit_vector);
            }
            hb = hb | x;
            seen = seen || x == c;
            i = i + 1;
        }
        return (hb < 0x80u8, seen);
    }
    let cc = rep_exec(c);
    let mut orw: u64 = 0;
    let mut any: u64 = 0;
    let mut i: usize = 0;
    proof {
        assert(0u64 & 0x8080_8080_8080_8080u64 == 0) by (bit_vector);
    }
    while i <= n - 8
        invariant
            n == hi - lo, n >= 8, lo <= hi <= b@.len(), i <= n, s == b@.subrange(lo as int, hi as int), cc == rep(c),
            (orw & HIGHS == 0) <==> forall|k: int| 0 <= k < i ==> #[trigger] s[k] < 0x80u8,
            any == 0 ==> forall|k: int| 0 <= k < i ==> #[trigger] s[k] != c,
        decreases n - i,
    {
        let w = word_at(b, lo + i);
        let f = fold_exec(w ^ cc) ^ ONES;
        proof {
            lemma_word_ascii(b@, lo + i);
            lemma_word_byte(b@, lo + i, c);
            lemma_or_highs(orw, w);
            assert forall|k: int| 0 <= k < 8 implies #[trigger] b@[lo + i + k] == s[i + k] by {}
            let na = any | f;
            assert(na == 0u64 ==> any == 0u64 && f == 0u64) by (bit_vector) requires na == any | f;
            if f == 0 {
                let fz = fold(w ^ cc);
                assert(fz == 0x0101_0101_0101_0101u64) by (bit_vector) requires f == fz ^ 0x0101_0101_0101_0101u64, f == 0u64;
                assert forall|k: int| i <= k < i + 8 implies #[trigger] s[k] != c by {
                    assert(b@[lo + i + (k - i)] == s[k]);
                }
            }
            assert forall|k: int| i <= k < i + 8 implies (#[trigger] s[k] < 0x80u8) == (b@[lo + i + (k - i)] < 0x80u8) by {
                assert(b@[lo + i + (k - i)] == s[k]);
            }
            if (orw | w) & HIGHS == 0 {
                assert forall|k: int| 0 <= k < i + 8 implies #[trigger] s[k] < 0x80u8 by {
                    if k >= i { assert(b@[lo + i + (k - i)] < 0x80u8); }
                }
            }
            if forall|k: int| 0 <= k < i + 8 ==> #[trigger] s[k] < 0x80u8 {
                assert forall|k: int| 0 <= k < 8 implies #[trigger] b@[lo + i + k] < 0x80u8 by {
                    assert(s[i + k] < 0x80u8);
                }
            }
        }
        orw = orw | w;
        any = any | f;
        i = i + 8;
    }
    if i < n {
        // The last word ends at `hi`: it covers bytes `n - 8 .. n`, and `n - 8 < i`.
        let j = n - 8;
        let w = word_at(b, hi - 8);
        let f = fold_exec(w ^ cc) ^ ONES;
        proof {
            lemma_word_ascii(b@, lo + j);
            lemma_word_byte(b@, lo + j, c);
            lemma_or_highs(orw, w);
            let na = any | f;
            assert(na == 0u64 ==> any == 0u64 && f == 0u64) by (bit_vector) requires na == any | f;
            if f == 0 {
                let fz = fold(w ^ cc);
                assert(fz == 0x0101_0101_0101_0101u64) by (bit_vector) requires f == fz ^ 0x0101_0101_0101_0101u64, f == 0u64;
                assert forall|k: int| j <= k < j + 8 implies #[trigger] s[k] != c by {
                    assert(b@[lo + j + (k - j)] == s[k]);
                }
            }
            if (orw | w) & HIGHS == 0 {
                assert forall|k: int| 0 <= k < n implies #[trigger] s[k] < 0x80u8 by {
                    if k >= i { assert(b@[lo + j + (k - j)] == s[k]); assert(b@[lo + j + (k - j)] < 0x80u8); }
                }
            }
            if forall|k: int| 0 <= k < n ==> #[trigger] s[k] < 0x80u8 {
                assert forall|k: int| 0 <= k < 8 implies #[trigger] b@[lo + j + k] < 0x80u8 by {
                    assert(s[j + k] < 0x80u8);
                }
            }
        }
        orw = orw | w;
        any = any | f;
    }
    proof {
        if any == 0 {
            assert forall|k: int| 0 <= k < s.len() implies s[k] != c by {}
        }
        assert(ascii(s) == forall|k: int| 0 <= k < n ==> #[trigger] s[k] < 0x80u8);
    }
    (orw & HIGHS == 0, any != 0)
}

} // verus!
