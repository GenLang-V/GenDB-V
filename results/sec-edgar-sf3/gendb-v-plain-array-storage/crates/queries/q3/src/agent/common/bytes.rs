//! Byte strings for worker bodies (`no_unwind`): sub-slices, equality, little-endian 64-bit words, and a three-word
//! fingerprint of a key (`key_words`): for keys of 16 to 24 bytes the words at offsets 0, 8 and `len - 8` cover every
//! byte, so equal words of keys of equal length mean equal keys (`lemma_key_words_eq`). `key_hash` mixes the length
//! and the words into 64 bits (any deterministic function would do; only equal keys must hash equally).
use vstd::prelude::*;

verus! {

/// The little-endian 64-bit word of the 8 bytes of `s` from `a`.
pub open spec fn word_at(s: Seq<u8>, a: int) -> u64 {
    (s[a] as u64) | ((s[a + 1] as u64) << 8u64) | ((s[a + 2] as u64) << 16u64) | ((s[a + 3] as u64) << 24u64)
        | ((s[a + 4] as u64) << 32u64) | ((s[a + 5] as u64) << 40u64) | ((s[a + 6] as u64) << 48u64)
        | ((s[a + 7] as u64) << 56u64)
}

/// Keys whose three words cover them exactly.
pub open spec fn fast_len(n: int) -> bool {
    16 <= n <= 24
}

/// The three words of a key (zero for keys of another length).
pub open spec fn key_words_spec(s: Seq<u8>) -> (u64, u64, u64) {
    if fast_len(s.len() as int) {
        (word_at(s, 0), word_at(s, 8), word_at(s, s.len() - 8))
    } else {
        (0, 0, 0)
    }
}

/// The mix of a length and three words.
pub open spec fn mix(n: u64, w: (u64, u64, u64)) -> u64 {
    ((w.0.wrapping_mul(0x9E37_79B9_7F4A_7C15u64) ^ w.1).wrapping_mul(0xC2B2_AE3D_27D4_EB4Fu64) ^ w.2 ^ n)
        .wrapping_mul(0x1656_67B1_9E37_79F9u64)
}

/// The hash of a key.
pub open spec fn key_hash_spec(s: Seq<u8>) -> u64 {
    mix(s.len() as u64, key_words_spec(s))
}

/// One word determines its 8 bytes.
pub proof fn lemma_word_bytes(a0: u8, a1: u8, a2: u8, a3: u8, a4: u8, a5: u8, a6: u8, a7: u8,
    b0: u8, b1: u8, b2: u8, b3: u8, b4: u8, b5: u8, b6: u8, b7: u8)
    requires
        ((a0 as u64) | ((a1 as u64) << 8u64) | ((a2 as u64) << 16u64) | ((a3 as u64) << 24u64)
            | ((a4 as u64) << 32u64) | ((a5 as u64) << 40u64) | ((a6 as u64) << 48u64) | ((a7 as u64) << 56u64))
        == ((b0 as u64) | ((b1 as u64) << 8u64) | ((b2 as u64) << 16u64) | ((b3 as u64) << 24u64)
            | ((b4 as u64) << 32u64) | ((b5 as u64) << 40u64) | ((b6 as u64) << 48u64) | ((b7 as u64) << 56u64)),
    ensures a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3 && a4 == b4 && a5 == b5 && a6 == b6 && a7 == b7,
{
    assert(a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3 && a4 == b4 && a5 == b5 && a6 == b6 && a7 == b7) by (bit_vector)
        requires
            ((a0 as u64) | ((a1 as u64) << 8u64) | ((a2 as u64) << 16u64) | ((a3 as u64) << 24u64)
                | ((a4 as u64) << 32u64) | ((a5 as u64) << 40u64) | ((a6 as u64) << 48u64) | ((a7 as u64) << 56u64))
            == ((b0 as u64) | ((b1 as u64) << 8u64) | ((b2 as u64) << 16u64) | ((b3 as u64) << 24u64)
                | ((b4 as u64) << 32u64) | ((b5 as u64) << 40u64) | ((b6 as u64) << 48u64) | ((b7 as u64) << 56u64));
}

/// Equal words at `a` mean equal bytes `a..a+8`.
pub proof fn lemma_word_at_eq(s: Seq<u8>, t: Seq<u8>, a: int)
    requires 0 <= a, a + 8 <= s.len(), a + 8 <= t.len(), word_at(s, a) == word_at(t, a),
    ensures forall|k: int| a <= k < a + 8 ==> s[k] == t[k],
{
    lemma_word_bytes(s[a], s[a + 1], s[a + 2], s[a + 3], s[a + 4], s[a + 5], s[a + 6], s[a + 7],
        t[a], t[a + 1], t[a + 2], t[a + 3], t[a + 4], t[a + 5], t[a + 6], t[a + 7]);
}

/// Keys of one covered length with equal words are equal.
pub proof fn lemma_key_words_eq(s: Seq<u8>, t: Seq<u8>)
    requires s.len() == t.len(), fast_len(s.len() as int), key_words_spec(s) == key_words_spec(t),
    ensures s == t,
{
    let n = s.len() as int;
    lemma_word_at_eq(s, t, 0);
    lemma_word_at_eq(s, t, 8);
    lemma_word_at_eq(s, t, n - 8);
    assert forall|k: int| 0 <= k < n implies s[k] == t[k] by {
        if k < 8 {
        } else if k < 16 {
        } else {
            assert(n - 8 <= k);
        }
    }
    assert(s =~= t);
}

/// `bytes[a..b]` as a slice.
#[inline(always)]
pub fn sub_bytes(bytes: &'static [u8], a: usize, b: usize) -> (r: &'static [u8])
    requires a <= b <= bytes@.len(),
    ensures r@ == bytes@.subrange(a as int, b as int),
    no_unwind
{
    let (_, t) = bytes.split_at(a);
    let (m, _) = t.split_at(b - a);
    proof {
        assert(m@ =~= bytes@.subrange(a as int, b as int));
    }
    m
}

/// Equality of two `n`-byte strings.
#[inline(always)]
pub fn eq_n(x: &[u8], y: &[u8], n: usize) -> (r: bool)
    requires x@.len() == n, y@.len() == n,
    ensures r == (x@ == y@),
    no_unwind
{
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n, x@.len() == n, y@.len() == n,
            forall|t: int| 0 <= t < k ==> x@[t] == y@[t],
        decreases n - k,
    {
        if x[k] != y[k] {
            return false;
        }
        k = k + 1;
    }
    proof {
        assert(x@ =~= y@);
    }
    true
}

/// The word of the first 8 bytes of `w`.
#[inline(always)]
pub fn word8(w: &[u8]) -> (v: u64)
    requires w@.len() >= 8,
    ensures v == word_at(w@, 0),
    no_unwind
{
    (w[0] as u64) | ((w[1] as u64) << 8u64) | ((w[2] as u64) << 16u64) | ((w[3] as u64) << 24u64)
        | ((w[4] as u64) << 32u64) | ((w[5] as u64) << 40u64) | ((w[6] as u64) << 48u64) | ((w[7] as u64) << 56u64)
}

/// The word at `a` of `x` is the word of `x[a..]`.
pub proof fn lemma_word_shift(x: Seq<u8>, a: int)
    requires 0 <= a, a + 8 <= x.len(),
    ensures word_at(x.subrange(a, x.len() as int), 0) == word_at(x, a),
{
    let t = x.subrange(a, x.len() as int);
    assert(t[0] == x[a] && t[1] == x[a + 1] && t[2] == x[a + 2] && t[3] == x[a + 3]);
    assert(t[4] == x[a + 4] && t[5] == x[a + 5] && t[6] == x[a + 6] && t[7] == x[a + 7]);
}

/// The three words of the key `x` (`n` bytes).
#[inline(always)]
pub fn key_words(x: &[u8], n: usize) -> (r: (u64, u64, u64))
    requires x@.len() == n,
    ensures r == key_words_spec(x@),
    no_unwind
{
    if 16 <= n && n <= 24 {
        let (a, rest) = x.split_at(8);
        let (b, _) = rest.split_at(8);
        let (_, c) = x.split_at(n - 8);
        let r = (word8(a), word8(b), word8(c));
        proof {
            assert(word_at(a@, 0) == word_at(x@, 0));
            lemma_word_shift(x@, 8);
            assert(rest@ == x@.subrange(8, n as int));
            assert(word_at(b@, 0) == word_at(rest@, 0));
            lemma_word_shift(x@, n - 8);
        }
        r
    } else {
        (0, 0, 0)
    }
}

/// The hash of the key `x` (`n` bytes) from its words.
#[inline(always)]
pub fn key_hash(n: usize, w: (u64, u64, u64)) -> (h: u64)
    requires n <= u64::MAX,
    ensures h == mix(n as u64, w),
    no_unwind
{
    ((w.0.wrapping_mul(0x9E37_79B9_7F4A_7C15u64) ^ w.1).wrapping_mul(0xC2B2_AE3D_27D4_EB4Fu64) ^ w.2 ^ (n as u64))
        .wrapping_mul(0x1656_67B1_9E37_79F9u64)
}

} // verus!
