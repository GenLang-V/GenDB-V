//! Byte ranges inside byte arrays, `no_unwind` (usable in worker bodies), with the array lengths carried as
//! arguments: equality of `b[x0..x1]` and `c[y0..y1]`, 8-byte little-endian word loads (`word8`), the three
//! words that cover a value of 8 to 24 bytes (`w3`: equal words of equal-length values mean equal values) and an
//! injective 64-bit code of a value of at most 7 bytes (`scode`).
use vstd::prelude::*;

verus! {

/// `b[x0..x1] == c[y0..y1]`.
pub fn eq_ranges(b: &[u8], blen: usize, x0: usize, x1: usize, c: &[u8], clen: usize, y0: usize, y1: usize) -> (r: bool)
    requires
        blen == b@.len(),
        clen == c@.len(),
        x0 <= x1 <= blen,
        y0 <= y1 <= clen,
    ensures
        r == (b@.subrange(x0 as int, x1 as int) == c@.subrange(y0 as int, y1 as int)),
    no_unwind
{
    let lx = x1 - x0;
    if lx != y1 - y0 {
        proof {
            assert(b@.subrange(x0 as int, x1 as int).len() != c@.subrange(y0 as int, y1 as int).len());
        }
        return false;
    }
    let ghost sb = b@.subrange(x0 as int, x1 as int);
    let ghost sc = c@.subrange(y0 as int, y1 as int);
    let mut k: usize = 0;
    while k < lx
        invariant
            k <= lx, lx == x1 - x0, lx == y1 - y0,
            x0 <= x1 <= blen, y0 <= y1 <= clen, blen == b@.len(), clen == c@.len(),
            sb == b@.subrange(x0 as int, x1 as int), sc == c@.subrange(y0 as int, y1 as int),
            forall|t: int| 0 <= t < k ==> #[trigger] sb[t] == sc[t],
        decreases lx - k,
    {
        if b[x0 + k] != c[y0 + k] {
            proof {
                assert(sb[k as int] != sc[k as int]);
            }
            return false;
        }
        k = k + 1;
    }
    proof {
        assert(sb =~= sc);
    }
    true
}

/// The 8 bytes `s[p..p + 8]` as a little-endian word.
pub open spec fn word8(s: Seq<u8>, p: int) -> u64 {
    (s[p] as u64) | ((s[p + 1] as u64) << 8u64) | ((s[p + 2] as u64) << 16u64) | ((s[p + 3] as u64) << 24u64)
        | ((s[p + 4] as u64) << 32u64) | ((s[p + 5] as u64) << 40u64) | ((s[p + 6] as u64) << 48u64)
        | ((s[p + 7] as u64) << 56u64)
}

/// The word `b[p..p + 8]` (two splits make the length known to the compiler, so the loads combine).
#[inline(always)]
pub fn load8(b: &[u8], blen: usize, p: usize) -> (w: u64)
    requires
        blen == b@.len(),
        p + 8 <= blen,
    ensures
        w == word8(b@, p as int),
    no_unwind
{
    let (_, t) = b.split_at(p);
    let (w, _) = t.split_at(8);
    let x7 = w[7] as u64;
    let x6 = w[6] as u64;
    let x5 = w[5] as u64;
    let x4 = w[4] as u64;
    let x3 = w[3] as u64;
    let x2 = w[2] as u64;
    let x1 = w[1] as u64;
    let x0 = w[0] as u64;
    x0 | (x1 << 8u64) | (x2 << 16u64) | (x3 << 24u64) | (x4 << 32u64) | (x5 << 40u64) | (x6 << 48u64) | (x7 << 56u64)
}

/// Equal little-endian words have equal bytes.
#[verifier::bit_vector]
pub proof fn lemma_word_bytes(x0: u64, x1: u64, x2: u64, x3: u64, x4: u64, x5: u64, x6: u64, x7: u64,
    y0: u64, y1: u64, y2: u64, y3: u64, y4: u64, y5: u64, y6: u64, y7: u64)
    requires
        x0 < 256, x1 < 256, x2 < 256, x3 < 256, x4 < 256, x5 < 256, x6 < 256, x7 < 256,
        y0 < 256, y1 < 256, y2 < 256, y3 < 256, y4 < 256, y5 < 256, y6 < 256, y7 < 256,
        x0 | (x1 << 8u64) | (x2 << 16u64) | (x3 << 24u64) | (x4 << 32u64) | (x5 << 40u64) | (x6 << 48u64) | (x7 << 56u64)
            == y0 | (y1 << 8u64) | (y2 << 16u64) | (y3 << 24u64) | (y4 << 32u64) | (y5 << 40u64) | (y6 << 48u64) | (y7 << 56u64),
    ensures
        x0 == y0, x1 == y1, x2 == y2, x3 == y3, x4 == y4, x5 == y5, x6 == y6, x7 == y7,
{
}

/// Equal words mean equal 8-byte windows.
pub proof fn lemma_word8_eq(s: Seq<u8>, p: int, t: Seq<u8>, q: int)
    requires
        0 <= p, p + 8 <= s.len(),
        0 <= q, q + 8 <= t.len(),
        word8(s, p) == word8(t, q),
    ensures
        forall|k: int| 0 <= k < 8 ==> #[trigger] s[p + k] == t[q + k],
{
    lemma_word_bytes(s[p] as u64, s[p + 1] as u64, s[p + 2] as u64, s[p + 3] as u64, s[p + 4] as u64, s[p + 5] as u64,
        s[p + 6] as u64, s[p + 7] as u64, t[q] as u64, t[q + 1] as u64, t[q + 2] as u64, t[q + 3] as u64,
        t[q + 4] as u64, t[q + 5] as u64, t[q + 6] as u64, t[q + 7] as u64);
    assert forall|k: int| 0 <= k < 8 implies #[trigger] s[p + k] == t[q + k] by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else if k == 5 {} else if k == 6 {} else {}
    }
}

/// The word at position `p` of a subrange is the word at `x0 + p` of the array.
pub proof fn lemma_word8_sub(b: Seq<u8>, x0: int, x1: int, p: int)
    requires
        0 <= x0 <= x1 <= b.len(),
        0 <= p, p + 8 <= x1 - x0,
    ensures
        word8(b.subrange(x0, x1), p) == word8(b, x0 + p),
{
    let s = b.subrange(x0, x1);
    assert(s[p] == b[x0 + p]);
    assert(s[p + 1] == b[x0 + p + 1]);
    assert(s[p + 2] == b[x0 + p + 2]);
    assert(s[p + 3] == b[x0 + p + 3]);
    assert(s[p + 4] == b[x0 + p + 4]);
    assert(s[p + 5] == b[x0 + p + 5]);
    assert(s[p + 6] == b[x0 + p + 6]);
    assert(s[p + 7] == b[x0 + p + 7]);
}

/// Middle word position of a value of `len` bytes (8 to 24).
pub open spec fn wmid(len: int) -> int {
    if 8 < len - 8 { 8 } else { len - 8 }
}

/// The three words covering a value of 8 to 24 bytes: at 0, at `wmid(len)` and at `len - 8`.
pub open spec fn w3(s: Seq<u8>) -> (u64, u64, u64) {
    (word8(s, 0), word8(s, wmid(s.len() as int)), word8(s, s.len() - 8))
}

/// Values of equal length (8 to 24 bytes) with equal covering words are equal.
pub proof fn lemma_w3_eq(s: Seq<u8>, t: Seq<u8>)
    requires
        s.len() == t.len(),
        8 <= s.len() <= 24,
        w3(s) == w3(t),
    ensures
        s == t,
{
    let len = s.len() as int;
    let mid = wmid(len);
    lemma_word8_eq(s, 0, t, 0);
    lemma_word8_eq(s, mid, t, mid);
    lemma_word8_eq(s, len - 8, t, len - 8);
    assert forall|i: int| 0 <= i < len implies s[i] == t[i] by {
        if i < 8 {
            assert(s[0 + i] == t[0 + i]);
        } else if i < mid + 8 {
            assert(s[mid + (i - mid)] == t[mid + (i - mid)]);
        } else {
            assert(s[(len - 8) + (i - (len - 8))] == t[(len - 8) + (i - (len - 8))]);
        }
    }
    assert(s =~= t);
}

/// The covering words of `b[x0..x1]` (length 8 to 24).
#[inline(always)]
pub fn words3(b: &[u8], blen: usize, x0: usize, x1: usize) -> (r: (u64, u64, u64))
    requires
        x0 + 8 <= x1 <= blen,
        x1 - x0 <= 24,
        blen == b@.len(),
    ensures
        r == w3(b@.subrange(x0 as int, x1 as int)),
    no_unwind
{
    let mid = if x0 + 8 < x1 - 8 { x0 + 8 } else { x1 - 8 };
    let r = (load8(b, blen, x0), load8(b, blen, mid), load8(b, blen, x1 - 8));
    proof {
        let (lo, hi) = (x0 as int, x1 as int);
        lemma_word8_sub(b@, lo, hi, 0);
        lemma_word8_sub(b@, lo, hi, mid - lo);
        lemma_word8_sub(b@, lo, hi, hi - 8 - lo);
    }
    r
}

/// The byte `s[k]` as a word when `k < s.len()`, else 0.
pub open spec fn byte_or_zero(s: Seq<u8>, k: int) -> u64 {
    if k < s.len() { s[k] as u64 } else { 0 }
}

/// Injective code of a value of at most 7 bytes: its bytes (little-endian, zero-padded) with `len + 1` in the top
/// byte; 0 for a longer value.
pub open spec fn scode(s: Seq<u8>) -> u64 {
    if s.len() <= 7 {
        byte_or_zero(s, 0) | (byte_or_zero(s, 1) << 8u64) | (byte_or_zero(s, 2) << 16u64) | (byte_or_zero(s, 3) << 24u64)
            | (byte_or_zero(s, 4) << 32u64) | (byte_or_zero(s, 5) << 40u64) | (byte_or_zero(s, 6) << 48u64)
            | (((s.len() + 1) as u64) << 56u64)
    } else {
        0
    }
}

#[verifier::bit_vector]
proof fn lemma_code_parts(x0: u64, x1: u64, x2: u64, x3: u64, x4: u64, x5: u64, x6: u64, lx: u64,
    y0: u64, y1: u64, y2: u64, y3: u64, y4: u64, y5: u64, y6: u64, ly: u64)
    requires
        x0 < 256, x1 < 256, x2 < 256, x3 < 256, x4 < 256, x5 < 256, x6 < 256, lx < 256,
        y0 < 256, y1 < 256, y2 < 256, y3 < 256, y4 < 256, y5 < 256, y6 < 256, ly < 256,
        x0 | (x1 << 8u64) | (x2 << 16u64) | (x3 << 24u64) | (x4 << 32u64) | (x5 << 40u64) | (x6 << 48u64) | (lx << 56u64)
            == y0 | (y1 << 8u64) | (y2 << 16u64) | (y3 << 24u64) | (y4 << 32u64) | (y5 << 40u64) | (y6 << 48u64) | (ly << 56u64),
    ensures
        x0 == y0, x1 == y1, x2 == y2, x3 == y3, x4 == y4, x5 == y5, x6 == y6, lx == ly,
{
}

/// `scode` is injective on values of at most 7 bytes, and never 0 on them.
pub proof fn lemma_scode_inj(s: Seq<u8>, t: Seq<u8>)
    requires
        s.len() <= 7,
        t.len() <= 7,
        scode(s) == scode(t),
    ensures
        s == t,
{
    lemma_code_parts(byte_or_zero(s, 0), byte_or_zero(s, 1), byte_or_zero(s, 2), byte_or_zero(s, 3), byte_or_zero(s, 4),
        byte_or_zero(s, 5), byte_or_zero(s, 6), (s.len() + 1) as u64, byte_or_zero(t, 0), byte_or_zero(t, 1),
        byte_or_zero(t, 2), byte_or_zero(t, 3), byte_or_zero(t, 4), byte_or_zero(t, 5), byte_or_zero(t, 6),
        (t.len() + 1) as u64);
    assert(s.len() == t.len());
    assert forall|k: int| 0 <= k < s.len() implies s[k] == t[k] by {
        assert(byte_or_zero(s, k) == byte_or_zero(t, k)) by {
            if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else if k == 5 {} else {}
        }
    }
    assert(s =~= t);
}

#[verifier::bit_vector]
proof fn lemma_scode_nonzero_bv(a: u64, l: u64)
    requires 1 <= l < 256,
    ensures a | (l << 56u64) != 0,
{
}

/// The code of a short value is not 0.
pub proof fn lemma_scode_nonzero(s: Seq<u8>)
    requires s.len() <= 7,
    ensures scode(s) != 0,
{
    let a = byte_or_zero(s, 0) | (byte_or_zero(s, 1) << 8u64) | (byte_or_zero(s, 2) << 16u64) | (byte_or_zero(s, 3) << 24u64)
        | (byte_or_zero(s, 4) << 32u64) | (byte_or_zero(s, 5) << 40u64) | (byte_or_zero(s, 6) << 48u64);
    lemma_scode_nonzero_bv(a, (s.len() + 1) as u64);
}

/// The code of a 2-byte and of a 1-byte value, as the fast path computes them.
pub proof fn lemma_scode_2_1(s: Seq<u8>, r: Seq<u8>)
    requires s.len() == 2, r.len() == 1,
    ensures
        scode(s) == (s[0] as u64) | ((s[1] as u64) << 8u64) | (3u64 << 56u64),
        scode(r) == (r[0] as u64) | (2u64 << 56u64),
{
    let (a, b, c) = (s[0] as u64, s[1] as u64, r[0] as u64);
    assert(a | (b << 8u64) | (0u64 << 16u64) | (0u64 << 24u64) | (0u64 << 32u64) | (0u64 << 40u64) | (0u64 << 48u64) | (3u64 << 56u64)
        == a | (b << 8u64) | (3u64 << 56u64)) by (bit_vector);
    assert(c | (0u64 << 8u64) | (0u64 << 16u64) | (0u64 << 24u64) | (0u64 << 32u64) | (0u64 << 40u64) | (0u64 << 48u64) | (2u64 << 56u64)
        == c | (2u64 << 56u64)) by (bit_vector);
}

#[verifier::bit_vector]
proof fn lemma_mask_word(x0: u64, x1: u64, x2: u64, x3: u64, x4: u64, x5: u64, x6: u64, x7: u64, len: u64)
    requires
        x0 < 256, x1 < 256, x2 < 256, x3 < 256, x4 < 256, x5 < 256, x6 < 256, x7 < 256,
        len <= 7,
    ensures
        ((x0 | (x1 << 8u64) | (x2 << 16u64) | (x3 << 24u64) | (x4 << 32u64) | (x5 << 40u64) | (x6 << 48u64) | (x7 << 56u64))
            & (((1u64 << (8u64 * len)) - 1u64) as u64))
            == (if len > 0 { x0 } else { 0u64 }) | ((if len > 1 { x1 } else { 0u64 }) << 8u64)
                | ((if len > 2 { x2 } else { 0u64 }) << 16u64) | ((if len > 3 { x3 } else { 0u64 }) << 24u64)
                | ((if len > 4 { x4 } else { 0u64 }) << 32u64) | ((if len > 5 { x5 } else { 0u64 }) << 40u64)
                | ((if len > 6 { x6 } else { 0u64 }) << 48u64),
{
}

/// The code of `b[x0..x1]` when it has at most 7 bytes and a word can be loaded at `x0`; 0 otherwise.
#[inline(always)]
pub fn short_code(b: &[u8], blen: usize, x0: usize, x1: usize) -> (k: u64)
    requires
        x0 <= x1 <= blen,
        blen == b@.len(),
    ensures
        k == 0 || (x1 - x0 <= 7 && k == scode(b@.subrange(x0 as int, x1 as int))),
    no_unwind
{
    let len = x1 - x0;
    if len > 7 || blen - x0 < 8 {
        return 0;
    }
    let w = load8(b, blen, x0);
    let sh = (8 * len) as u64;
    assert(1u64 << sh >= 1u64) by (bit_vector)
        requires sh <= 56u64;
    let m = (1u64 << sh) - 1;
    let k = (w & m) | (((len + 1) as u64) << 56u64);
    proof {
        let s = b@.subrange(x0 as int, x1 as int);
        let p = x0 as int;
        lemma_mask_word(b@[p] as u64, b@[p + 1] as u64, b@[p + 2] as u64, b@[p + 3] as u64, b@[p + 4] as u64,
            b@[p + 5] as u64, b@[p + 6] as u64, b@[p + 7] as u64, len as u64);
        assert forall|j: int| 0 <= j < 7 implies #[trigger] byte_or_zero(s, j)
            == (if (len as int) > j { b@[p + j] as u64 } else { 0u64 }) by {
            if j < len {
                assert(s[j] == b@[p + j]);
            }
        }
        assert(byte_or_zero(s, 0) == (if len > 0 { b@[p] as u64 } else { 0u64 }));
        assert(byte_or_zero(s, 1) == (if len > 1 { b@[p + 1] as u64 } else { 0u64 }));
        assert(byte_or_zero(s, 2) == (if len > 2 { b@[p + 2] as u64 } else { 0u64 }));
        assert(byte_or_zero(s, 3) == (if len > 3 { b@[p + 3] as u64 } else { 0u64 }));
        assert(byte_or_zero(s, 4) == (if len > 4 { b@[p + 4] as u64 } else { 0u64 }));
        assert(byte_or_zero(s, 5) == (if len > 5 { b@[p + 5] as u64 } else { 0u64 }));
        assert(byte_or_zero(s, 6) == (if len > 6 { b@[p + 6] as u64 } else { 0u64 }));
        assert(sh == 8u64 * (len as u64));
    }
    k
}

} // verus!
