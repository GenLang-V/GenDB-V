//! Byte strings: 8-byte little-endian word loads, a signature hash of a byte string (length and three words, or the
//! packed bytes of a short string) and word-wise byte equality, each with its spec and `no_unwind`.
//!
//! The hash is only a heuristic for bucketing: every user compares the bytes themselves before relying on a match;
//! what the proofs use is that it is a function of the bytes (`sig_spec`).
use vstd::prelude::*;

verus! {

/// Multiplier of `mix` (64-bit golden ratio).
pub const MIX_K: u64 = 0x9E37_79B9_7F4A_7C15u64;

/// The little-endian word of bytes `b[p..p + 8]`.
pub open spec fn word_spec(b: Seq<u8>, p: int) -> u64 {
    (b[p] as u64) | ((b[p + 1] as u64) << 8u64) | ((b[p + 2] as u64) << 16u64) | ((b[p + 3] as u64) << 24u64)
        | ((b[p + 4] as u64) << 32u64) | ((b[p + 5] as u64) << 40u64) | ((b[p + 6] as u64) << 48u64)
        | ((b[p + 7] as u64) << 56u64)
}

/// One mixing step of the hash.
pub open spec fn mix_spec(h: u64, w: u64) -> u64 {
    let m = (h ^ w).wrapping_mul(MIX_K);
    m ^ (m >> 29u64)
}

/// The bytes of a string shorter than 8 bytes packed into a word (byte `j` at bits `8j..8j + 8`).
pub open spec fn small_word(b: Seq<u8>) -> u64
    decreases b.len(),
{
    if b.len() == 0 || b.len() > 8 {
        0
    } else {
        small_word(b.drop_last()) | ((b.last() as u64) << ((8 * (b.len() - 1)) as u64))
    }
}

/// Signature hash of a byte string: its length mixed with its first, middle and last word, or with its packed bytes
/// when it is shorter than 8 bytes.
pub open spec fn sig_spec(b: Seq<u8>) -> u64 {
    let len = b.len();
    if len >= 8 {
        mix_spec(mix_spec(mix_spec(len as u64, word_spec(b, 0)), word_spec(b, (len - 8) / 2)), word_spec(b, len - 8))
    } else {
        mix_spec(len as u64, small_word(b))
    }
}

/// The word of `b` at byte `p`.
#[inline(always)]
pub fn word_at(b: &[u8], p: usize, Ghost(len): Ghost<int>) -> (w: u64)
    requires len == b@.len(), p + 8 <= len,
    ensures w == word_spec(b@, p as int),
    no_unwind
{
    let (_, t) = b.split_at(p);
    let (x, _) = t.split_at(8);
    proof {
        assert(forall|j: int| 0 <= j < 8 ==> x@[j] == b@[p + j]);
    }
    (x[0] as u64) | ((x[1] as u64) << 8u64) | ((x[2] as u64) << 16u64) | ((x[3] as u64) << 24u64)
        | ((x[4] as u64) << 32u64) | ((x[5] as u64) << 40u64) | ((x[6] as u64) << 48u64)
        | ((x[7] as u64) << 56u64)
}

/// `mix_spec`.
#[inline(always)]
pub fn mix(h: u64, w: u64) -> (r: u64)
    ensures r == mix_spec(h, w),
    no_unwind
{
    let m = (h ^ w).wrapping_mul(MIX_K);
    m ^ (m >> 29u64)
}

/// `sig_spec` of `b` (`len` bytes).
#[inline(always)]
pub fn sig(b: &[u8], len: usize) -> (h: u64)
    requires len == b@.len(),
    ensures h == sig_spec(b@),
    no_unwind
{
    if len >= 8 {
        let w0 = word_at(b, 0, Ghost(len as int));
        let wm = word_at(b, (len - 8) / 2, Ghost(len as int));
        let w1 = word_at(b, len - 8, Ghost(len as int));
        mix(mix(mix(len as u64, w0), wm), w1)
    } else {
        let mut w: u64 = 0;
        let mut j: usize = 0;
        while j < len
            invariant
                len == b@.len(), len < 8, j <= len,
                w == small_word(b@.subrange(0, j as int)),
            decreases len - j,
        {
            proof {
                let s1 = b@.subrange(0, j as int + 1);
                assert(s1.drop_last() =~= b@.subrange(0, j as int));
                assert(s1.last() == b@[j as int]);
            }
            w = w | ((b[j] as u64) << ((8 * j) as u64));
            j = j + 1;
        }
        proof {
            assert(b@.subrange(0, len as int) =~= b@);
        }
        mix(len as u64, w)
    }
}

/// The bytes of a word are recovered by shifting and masking.
proof fn lemma_unpack(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64, a6: u64, a7: u64)
    requires a0 < 256, a1 < 256, a2 < 256, a3 < 256, a4 < 256, a5 < 256, a6 < 256, a7 < 256,
    ensures ({
        let w = a0 | (a1 << 8u64) | (a2 << 16u64) | (a3 << 24u64) | (a4 << 32u64) | (a5 << 40u64) | (a6 << 48u64)
            | (a7 << 56u64);
        &&& w & 0xffu64 == a0
        &&& (w >> 8u64) & 0xffu64 == a1
        &&& (w >> 16u64) & 0xffu64 == a2
        &&& (w >> 24u64) & 0xffu64 == a3
        &&& (w >> 32u64) & 0xffu64 == a4
        &&& (w >> 40u64) & 0xffu64 == a5
        &&& (w >> 48u64) & 0xffu64 == a6
        &&& (w >> 56u64) & 0xffu64 == a7
    }),
{
    assert({
        let w = a0 | (a1 << 8u64) | (a2 << 16u64) | (a3 << 24u64) | (a4 << 32u64) | (a5 << 40u64) | (a6 << 48u64)
            | (a7 << 56u64);
        &&& w & 0xffu64 == a0
        &&& (w >> 8u64) & 0xffu64 == a1
        &&& (w >> 16u64) & 0xffu64 == a2
        &&& (w >> 24u64) & 0xffu64 == a3
        &&& (w >> 32u64) & 0xffu64 == a4
        &&& (w >> 40u64) & 0xffu64 == a5
        &&& (w >> 48u64) & 0xffu64 == a6
        &&& (w >> 56u64) & 0xffu64 == a7
    }) by (bit_vector)
        requires a0 < 256, a1 < 256, a2 < 256, a3 < 256, a4 < 256, a5 < 256, a6 < 256, a7 < 256;
}

/// Equal words at `p` have equal bytes `p..p + 8`.
pub proof fn lemma_word_eq(x: Seq<u8>, y: Seq<u8>, p: int)
    requires 0 <= p, p + 8 <= x.len(), p + 8 <= y.len(), word_spec(x, p) == word_spec(y, p),
    ensures forall|j: int| p <= j < p + 8 ==> x[j] == y[j],
{
    lemma_unpack(x[p] as u64, x[p + 1] as u64, x[p + 2] as u64, x[p + 3] as u64, x[p + 4] as u64, x[p + 5] as u64,
        x[p + 6] as u64, x[p + 7] as u64);
    lemma_unpack(y[p] as u64, y[p + 1] as u64, y[p + 2] as u64, y[p + 3] as u64, y[p + 4] as u64, y[p + 5] as u64,
        y[p + 6] as u64, y[p + 7] as u64);
    assert forall|j: int| p <= j < p + 8 implies x[j] == y[j] by {
        assert((x[j] as u64) == (y[j] as u64));
    }
}

/// Equal words at `x[p..]` and `y[q..]` have equal bytes.
pub proof fn lemma_word_eq_at(x: Seq<u8>, p: int, y: Seq<u8>, q: int)
    requires 0 <= p, p + 8 <= x.len(), 0 <= q, q + 8 <= y.len(), word_spec(x, p) == word_spec(y, q),
    ensures forall|t: int| 0 <= t < 8 ==> #[trigger] x[p + t] == y[q + t],
{
    lemma_unpack(x[p] as u64, x[p + 1] as u64, x[p + 2] as u64, x[p + 3] as u64, x[p + 4] as u64, x[p + 5] as u64,
        x[p + 6] as u64, x[p + 7] as u64);
    lemma_unpack(y[q] as u64, y[q + 1] as u64, y[q + 2] as u64, y[q + 3] as u64, y[q + 4] as u64, y[q + 5] as u64,
        y[q + 6] as u64, y[q + 7] as u64);
    assert forall|t: int| 0 <= t < 8 implies #[trigger] x[p + t] == y[q + t] by {
        assert((x[p + t] as u64) == (y[q + t] as u64));
    }
}

/// Byte equality of `x` and `y` (`n` bytes each), eight bytes at a time.
#[inline(always)]
pub fn bytes_eq(x: &[u8], y: &[u8], n: usize) -> (r: bool)
    requires x@.len() == n, y@.len() == n,
    ensures r == (x@ == y@),
    no_unwind
{
    let mut k: usize = 0;
    while n - k >= 8
        invariant
            x@.len() == n, y@.len() == n, k <= n,
            forall|j: int| 0 <= j < k ==> x@[j] == y@[j],
        decreases n - k,
    {
        if word_at(x, k, Ghost(n as int)) != word_at(y, k, Ghost(n as int)) {
            proof {
                if x@ == y@ {
                    assert(word_spec(x@, k as int) == word_spec(y@, k as int));
                }
            }
            return false;
        }
        proof {
            lemma_word_eq(x@, y@, k as int);
        }
        k = k + 8;
    }
    while k < n
        invariant
            x@.len() == n, y@.len() == n, k <= n,
            forall|j: int| 0 <= j < k ==> x@[j] == y@[j],
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

/// Byte equality of two strings of possibly different lengths.
#[inline(always)]
pub fn text_same(x: &[u8], xn: usize, y: &[u8], yn: usize) -> (r: bool)
    requires x@.len() == xn, y@.len() == yn,
    ensures r == (x@ == y@),
    no_unwind
{
    if xn != yn {
        return false;
    }
    bytes_eq(x, y, xn)
}

} // verus!
