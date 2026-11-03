//! Equality of a short byte string (at most 8 bytes) with the bytes at some offset by one masked 64-bit word.
use vstd::prelude::*;
use crate::agent::common::bytes::word_at;

verus! {

// ------------------------------------------------------------------------------------ uom test by one word

/// The little-endian word of the first `n` bytes of `s` (`n <= 8`).
pub open spec fn pword(s: Seq<u8>, n: int) -> u64
    decreases n,
{
    if n <= 0 { 0 } else { pword(s, n - 1) | ((s[n - 1] as u64) << ((8 * (n - 1)) as u64)) }
}

/// The mask of the low `n` bytes.
pub open spec fn bmask(n: int) -> u64 {
    if n >= 8 { 0xffff_ffff_ffff_ffffu64 } else { ((1u64 << ((8 * n) as u64)) - 1) as u64 }
}

proof fn lemma_mask0(x0: u8, x1: u8, x2: u8, x3: u8, x4: u8, x5: u8, x6: u8, x7: u8)
    ensures ((((x0 as u64) | ((x1 as u64) << 8u64) | ((x2 as u64) << 16u64) | ((x3 as u64) << 24u64) | ((x4 as u64) << 32u64) | ((x5 as u64) << 40u64) | ((x6 as u64) << 48u64) | ((x7 as u64) << 56u64)) ^ 0u64) & 0x0u64 == 0) == (true),
{
    assert(((((x0 as u64) | ((x1 as u64) << 8u64) | ((x2 as u64) << 16u64) | ((x3 as u64) << 24u64) | ((x4 as u64) << 32u64) | ((x5 as u64) << 40u64) | ((x6 as u64) << 48u64) | ((x7 as u64) << 56u64)) ^ 0u64) & 0x0u64 == 0) == (true)) by (bit_vector);
}

proof fn lemma_mask1(x0: u8, x1: u8, x2: u8, x3: u8, x4: u8, x5: u8, x6: u8, x7: u8, y0: u8)
    ensures ((((x0 as u64) | ((x1 as u64) << 8u64) | ((x2 as u64) << 16u64) | ((x3 as u64) << 24u64) | ((x4 as u64) << 32u64) | ((x5 as u64) << 40u64) | ((x6 as u64) << 48u64) | ((x7 as u64) << 56u64)) ^ (0u64 | ((y0 as u64) << 0u64))) & 0xffu64 == 0) == (x0 == y0),
{
    assert(((((x0 as u64) | ((x1 as u64) << 8u64) | ((x2 as u64) << 16u64) | ((x3 as u64) << 24u64) | ((x4 as u64) << 32u64) | ((x5 as u64) << 40u64) | ((x6 as u64) << 48u64) | ((x7 as u64) << 56u64)) ^ (0u64 | ((y0 as u64) << 0u64))) & 0xffu64 == 0) == (x0 == y0)) by (bit_vector);
}

proof fn lemma_mask2(x0: u8, x1: u8, x2: u8, x3: u8, x4: u8, x5: u8, x6: u8, x7: u8, y0: u8, y1: u8)
    ensures ((((x0 as u64) | ((x1 as u64) << 8u64) | ((x2 as u64) << 16u64) | ((x3 as u64) << 24u64) | ((x4 as u64) << 32u64) | ((x5 as u64) << 40u64) | ((x6 as u64) << 48u64) | ((x7 as u64) << 56u64)) ^ ((0u64 | ((y0 as u64) << 0u64)) | ((y1 as u64) << 8u64))) & 0xffffu64 == 0) == (x0 == y0 && x1 == y1),
{
    assert(((((x0 as u64) | ((x1 as u64) << 8u64) | ((x2 as u64) << 16u64) | ((x3 as u64) << 24u64) | ((x4 as u64) << 32u64) | ((x5 as u64) << 40u64) | ((x6 as u64) << 48u64) | ((x7 as u64) << 56u64)) ^ ((0u64 | ((y0 as u64) << 0u64)) | ((y1 as u64) << 8u64))) & 0xffffu64 == 0) == (x0 == y0 && x1 == y1)) by (bit_vector);
}

proof fn lemma_mask3(x0: u8, x1: u8, x2: u8, x3: u8, x4: u8, x5: u8, x6: u8, x7: u8, y0: u8, y1: u8, y2: u8)
    ensures ((((x0 as u64) | ((x1 as u64) << 8u64) | ((x2 as u64) << 16u64) | ((x3 as u64) << 24u64) | ((x4 as u64) << 32u64) | ((x5 as u64) << 40u64) | ((x6 as u64) << 48u64) | ((x7 as u64) << 56u64)) ^ (((0u64 | ((y0 as u64) << 0u64)) | ((y1 as u64) << 8u64)) | ((y2 as u64) << 16u64))) & 0xffffffu64 == 0) == (x0 == y0 && x1 == y1 && x2 == y2),
{
    assert(((((x0 as u64) | ((x1 as u64) << 8u64) | ((x2 as u64) << 16u64) | ((x3 as u64) << 24u64) | ((x4 as u64) << 32u64) | ((x5 as u64) << 40u64) | ((x6 as u64) << 48u64) | ((x7 as u64) << 56u64)) ^ (((0u64 | ((y0 as u64) << 0u64)) | ((y1 as u64) << 8u64)) | ((y2 as u64) << 16u64))) & 0xffffffu64 == 0) == (x0 == y0 && x1 == y1 && x2 == y2)) by (bit_vector);
}

proof fn lemma_mask4(x0: u8, x1: u8, x2: u8, x3: u8, x4: u8, x5: u8, x6: u8, x7: u8, y0: u8, y1: u8, y2: u8, y3: u8)
    ensures ((((x0 as u64) | ((x1 as u64) << 8u64) | ((x2 as u64) << 16u64) | ((x3 as u64) << 24u64) | ((x4 as u64) << 32u64) | ((x5 as u64) << 40u64) | ((x6 as u64) << 48u64) | ((x7 as u64) << 56u64)) ^ ((((0u64 | ((y0 as u64) << 0u64)) | ((y1 as u64) << 8u64)) | ((y2 as u64) << 16u64)) | ((y3 as u64) << 24u64))) & 0xffffffffu64 == 0) == (x0 == y0 && x1 == y1 && x2 == y2 && x3 == y3),
{
    assert(((((x0 as u64) | ((x1 as u64) << 8u64) | ((x2 as u64) << 16u64) | ((x3 as u64) << 24u64) | ((x4 as u64) << 32u64) | ((x5 as u64) << 40u64) | ((x6 as u64) << 48u64) | ((x7 as u64) << 56u64)) ^ ((((0u64 | ((y0 as u64) << 0u64)) | ((y1 as u64) << 8u64)) | ((y2 as u64) << 16u64)) | ((y3 as u64) << 24u64))) & 0xffffffffu64 == 0) == (x0 == y0 && x1 == y1 && x2 == y2 && x3 == y3)) by (bit_vector);
}

proof fn lemma_mask5(x0: u8, x1: u8, x2: u8, x3: u8, x4: u8, x5: u8, x6: u8, x7: u8, y0: u8, y1: u8, y2: u8, y3: u8, y4: u8)
    ensures ((((x0 as u64) | ((x1 as u64) << 8u64) | ((x2 as u64) << 16u64) | ((x3 as u64) << 24u64) | ((x4 as u64) << 32u64) | ((x5 as u64) << 40u64) | ((x6 as u64) << 48u64) | ((x7 as u64) << 56u64)) ^ (((((0u64 | ((y0 as u64) << 0u64)) | ((y1 as u64) << 8u64)) | ((y2 as u64) << 16u64)) | ((y3 as u64) << 24u64)) | ((y4 as u64) << 32u64))) & 0xffffffffffu64 == 0) == (x0 == y0 && x1 == y1 && x2 == y2 && x3 == y3 && x4 == y4),
{
    assert(((((x0 as u64) | ((x1 as u64) << 8u64) | ((x2 as u64) << 16u64) | ((x3 as u64) << 24u64) | ((x4 as u64) << 32u64) | ((x5 as u64) << 40u64) | ((x6 as u64) << 48u64) | ((x7 as u64) << 56u64)) ^ (((((0u64 | ((y0 as u64) << 0u64)) | ((y1 as u64) << 8u64)) | ((y2 as u64) << 16u64)) | ((y3 as u64) << 24u64)) | ((y4 as u64) << 32u64))) & 0xffffffffffu64 == 0) == (x0 == y0 && x1 == y1 && x2 == y2 && x3 == y3 && x4 == y4)) by (bit_vector);
}

proof fn lemma_mask6(x0: u8, x1: u8, x2: u8, x3: u8, x4: u8, x5: u8, x6: u8, x7: u8, y0: u8, y1: u8, y2: u8, y3: u8, y4: u8, y5: u8)
    ensures ((((x0 as u64) | ((x1 as u64) << 8u64) | ((x2 as u64) << 16u64) | ((x3 as u64) << 24u64) | ((x4 as u64) << 32u64) | ((x5 as u64) << 40u64) | ((x6 as u64) << 48u64) | ((x7 as u64) << 56u64)) ^ ((((((0u64 | ((y0 as u64) << 0u64)) | ((y1 as u64) << 8u64)) | ((y2 as u64) << 16u64)) | ((y3 as u64) << 24u64)) | ((y4 as u64) << 32u64)) | ((y5 as u64) << 40u64))) & 0xffffffffffffu64 == 0) == (x0 == y0 && x1 == y1 && x2 == y2 && x3 == y3 && x4 == y4 && x5 == y5),
{
    assert(((((x0 as u64) | ((x1 as u64) << 8u64) | ((x2 as u64) << 16u64) | ((x3 as u64) << 24u64) | ((x4 as u64) << 32u64) | ((x5 as u64) << 40u64) | ((x6 as u64) << 48u64) | ((x7 as u64) << 56u64)) ^ ((((((0u64 | ((y0 as u64) << 0u64)) | ((y1 as u64) << 8u64)) | ((y2 as u64) << 16u64)) | ((y3 as u64) << 24u64)) | ((y4 as u64) << 32u64)) | ((y5 as u64) << 40u64))) & 0xffffffffffffu64 == 0) == (x0 == y0 && x1 == y1 && x2 == y2 && x3 == y3 && x4 == y4 && x5 == y5)) by (bit_vector);
}

proof fn lemma_mask7(x0: u8, x1: u8, x2: u8, x3: u8, x4: u8, x5: u8, x6: u8, x7: u8, y0: u8, y1: u8, y2: u8, y3: u8, y4: u8, y5: u8, y6: u8)
    ensures ((((x0 as u64) | ((x1 as u64) << 8u64) | ((x2 as u64) << 16u64) | ((x3 as u64) << 24u64) | ((x4 as u64) << 32u64) | ((x5 as u64) << 40u64) | ((x6 as u64) << 48u64) | ((x7 as u64) << 56u64)) ^ (((((((0u64 | ((y0 as u64) << 0u64)) | ((y1 as u64) << 8u64)) | ((y2 as u64) << 16u64)) | ((y3 as u64) << 24u64)) | ((y4 as u64) << 32u64)) | ((y5 as u64) << 40u64)) | ((y6 as u64) << 48u64))) & 0xffffffffffffffu64 == 0) == (x0 == y0 && x1 == y1 && x2 == y2 && x3 == y3 && x4 == y4 && x5 == y5 && x6 == y6),
{
    assert(((((x0 as u64) | ((x1 as u64) << 8u64) | ((x2 as u64) << 16u64) | ((x3 as u64) << 24u64) | ((x4 as u64) << 32u64) | ((x5 as u64) << 40u64) | ((x6 as u64) << 48u64) | ((x7 as u64) << 56u64)) ^ (((((((0u64 | ((y0 as u64) << 0u64)) | ((y1 as u64) << 8u64)) | ((y2 as u64) << 16u64)) | ((y3 as u64) << 24u64)) | ((y4 as u64) << 32u64)) | ((y5 as u64) << 40u64)) | ((y6 as u64) << 48u64))) & 0xffffffffffffffu64 == 0) == (x0 == y0 && x1 == y1 && x2 == y2 && x3 == y3 && x4 == y4 && x5 == y5 && x6 == y6)) by (bit_vector);
}

proof fn lemma_mask8(x0: u8, x1: u8, x2: u8, x3: u8, x4: u8, x5: u8, x6: u8, x7: u8, y0: u8, y1: u8, y2: u8, y3: u8, y4: u8, y5: u8, y6: u8, y7: u8)
    ensures ((((x0 as u64) | ((x1 as u64) << 8u64) | ((x2 as u64) << 16u64) | ((x3 as u64) << 24u64) | ((x4 as u64) << 32u64) | ((x5 as u64) << 40u64) | ((x6 as u64) << 48u64) | ((x7 as u64) << 56u64)) ^ ((((((((0u64 | ((y0 as u64) << 0u64)) | ((y1 as u64) << 8u64)) | ((y2 as u64) << 16u64)) | ((y3 as u64) << 24u64)) | ((y4 as u64) << 32u64)) | ((y5 as u64) << 40u64)) | ((y6 as u64) << 48u64)) | ((y7 as u64) << 56u64))) & 0xffff_ffff_ffff_ffffu64 == 0) == (x0 == y0 && x1 == y1 && x2 == y2 && x3 == y3 && x4 == y4 && x5 == y5 && x6 == y6 && x7 == y7),
{
    assert(((((x0 as u64) | ((x1 as u64) << 8u64) | ((x2 as u64) << 16u64) | ((x3 as u64) << 24u64) | ((x4 as u64) << 32u64) | ((x5 as u64) << 40u64) | ((x6 as u64) << 48u64) | ((x7 as u64) << 56u64)) ^ ((((((((0u64 | ((y0 as u64) << 0u64)) | ((y1 as u64) << 8u64)) | ((y2 as u64) << 16u64)) | ((y3 as u64) << 24u64)) | ((y4 as u64) << 32u64)) | ((y5 as u64) << 40u64)) | ((y6 as u64) << 48u64)) | ((y7 as u64) << 56u64))) & 0xffff_ffff_ffff_ffffu64 == 0) == (x0 == y0 && x1 == y1 && x2 == y2 && x3 == y3 && x4 == y4 && x5 == y5 && x6 == y6 && x7 == y7)) by (bit_vector);
}

/// The masks of 0 to 8 bytes.
pub proof fn lemma_bmask_values()
    ensures
        bmask(0) == 0u64, bmask(1) == 0xffu64, bmask(2) == 0xffffu64, bmask(3) == 0xff_ffffu64,
        bmask(4) == 0xffff_ffffu64, bmask(5) == 0xff_ffff_ffffu64, bmask(6) == 0xffff_ffff_ffffu64,
        bmask(7) == 0xff_ffff_ffff_ffffu64, bmask(8) == 0xffff_ffff_ffff_ffffu64,
{
    assert(bmask(0) == 0u64) by (compute);
    assert(bmask(1) == 0xffu64) by (compute);
    assert(bmask(2) == 0xffffu64) by (compute);
    assert(bmask(3) == 0xff_ffffu64) by (compute);
    assert(bmask(4) == 0xffff_ffffu64) by (compute);
    assert(bmask(5) == 0xff_ffff_ffffu64) by (compute);
    assert(bmask(6) == 0xffff_ffff_ffffu64) by (compute);
    assert(bmask(7) == 0xff_ffff_ffff_ffffu64) by (compute);
}

/// Byte-wise equality of `x[a..a + n]` with `y`.
proof fn lemma_sub_eq(x: Seq<u8>, a: int, y: Seq<u8>, n: int)
    requires 0 <= n, y.len() == n, 0 <= a, a + n <= x.len(),
    ensures (x.subrange(a, a + n) == y) == (forall|q: int| 0 <= q < n ==> x[a + q] == y[q]),
{
    if x.subrange(a, a + n) == y {
        assert forall|q: int| 0 <= q < n implies x[a + q] == y[q] by {
            assert(x.subrange(a, a + n)[q] == x[a + q]);
        }
    } else {
        if forall|q: int| 0 <= q < n ==> x[a + q] == y[q] {
            assert(x.subrange(a, a + n) =~= y);
        }
    }
}

/// One masked word decides whether the `n <= 8` bytes of `x` from `a` are `y`.
pub proof fn lemma_word_eq(x: Seq<u8>, a: int, y: Seq<u8>, n: int)
    requires 0 <= n <= 8, y.len() == n, 0 <= a, a + 8 <= x.len(),
    ensures (((word_at(x, a) ^ pword(y, n)) & bmask(n)) == 0) == (x.subrange(a, a + n) == y),
{
    assert(bmask(0) == 0u64) by (compute);
    assert(bmask(1) == 0xffu64) by (compute);
    assert(bmask(2) == 0xffffu64) by (compute);
    assert(bmask(3) == 0xff_ffffu64) by (compute);
    assert(bmask(4) == 0xffff_ffffu64) by (compute);
    assert(bmask(5) == 0xff_ffff_ffffu64) by (compute);
    assert(bmask(6) == 0xffff_ffff_ffffu64) by (compute);
    assert(bmask(7) == 0xff_ffff_ffff_ffffu64) by (compute);
    if n == 0 {

        assert(pword(y, 0) == 0u64);
        lemma_mask0(x[a + 0], x[a + 1], x[a + 2], x[a + 3], x[a + 4], x[a + 5], x[a + 6], x[a + 7]);
        lemma_sub_eq(x, a, y, n);
    }
    if n == 1 {
        assert(pword(y, 1) == (pword(y, 0) | ((y[0] as u64) << 0u64)));
        assert(pword(y, 1) == (0u64 | ((y[0] as u64) << 0u64)));
        lemma_mask1(x[a + 0], x[a + 1], x[a + 2], x[a + 3], x[a + 4], x[a + 5], x[a + 6], x[a + 7], y[0]);
        lemma_sub_eq(x, a, y, n);
    }
    if n == 2 {
        assert(pword(y, 1) == (pword(y, 0) | ((y[0] as u64) << 0u64)));
        assert(pword(y, 2) == (pword(y, 1) | ((y[1] as u64) << 8u64)));
        assert(pword(y, 2) == ((0u64 | ((y[0] as u64) << 0u64)) | ((y[1] as u64) << 8u64)));
        lemma_mask2(x[a + 0], x[a + 1], x[a + 2], x[a + 3], x[a + 4], x[a + 5], x[a + 6], x[a + 7], y[0], y[1]);
        lemma_sub_eq(x, a, y, n);
    }
    if n == 3 {
        assert(pword(y, 1) == (pword(y, 0) | ((y[0] as u64) << 0u64)));
        assert(pword(y, 2) == (pword(y, 1) | ((y[1] as u64) << 8u64)));
        assert(pword(y, 3) == (pword(y, 2) | ((y[2] as u64) << 16u64)));
        assert(pword(y, 3) == (((0u64 | ((y[0] as u64) << 0u64)) | ((y[1] as u64) << 8u64)) | ((y[2] as u64) << 16u64)));
        lemma_mask3(x[a + 0], x[a + 1], x[a + 2], x[a + 3], x[a + 4], x[a + 5], x[a + 6], x[a + 7], y[0], y[1], y[2]);
        lemma_sub_eq(x, a, y, n);
    }
    if n == 4 {
        assert(pword(y, 1) == (pword(y, 0) | ((y[0] as u64) << 0u64)));
        assert(pword(y, 2) == (pword(y, 1) | ((y[1] as u64) << 8u64)));
        assert(pword(y, 3) == (pword(y, 2) | ((y[2] as u64) << 16u64)));
        assert(pword(y, 4) == (pword(y, 3) | ((y[3] as u64) << 24u64)));
        assert(pword(y, 4) == ((((0u64 | ((y[0] as u64) << 0u64)) | ((y[1] as u64) << 8u64)) | ((y[2] as u64) << 16u64)) | ((y[3] as u64) << 24u64)));
        lemma_mask4(x[a + 0], x[a + 1], x[a + 2], x[a + 3], x[a + 4], x[a + 5], x[a + 6], x[a + 7], y[0], y[1], y[2], y[3]);
        lemma_sub_eq(x, a, y, n);
    }
    if n == 5 {
        assert(pword(y, 1) == (pword(y, 0) | ((y[0] as u64) << 0u64)));
        assert(pword(y, 2) == (pword(y, 1) | ((y[1] as u64) << 8u64)));
        assert(pword(y, 3) == (pword(y, 2) | ((y[2] as u64) << 16u64)));
        assert(pword(y, 4) == (pword(y, 3) | ((y[3] as u64) << 24u64)));
        assert(pword(y, 5) == (pword(y, 4) | ((y[4] as u64) << 32u64)));
        assert(pword(y, 5) == (((((0u64 | ((y[0] as u64) << 0u64)) | ((y[1] as u64) << 8u64)) | ((y[2] as u64) << 16u64)) | ((y[3] as u64) << 24u64)) | ((y[4] as u64) << 32u64)));
        lemma_mask5(x[a + 0], x[a + 1], x[a + 2], x[a + 3], x[a + 4], x[a + 5], x[a + 6], x[a + 7], y[0], y[1], y[2], y[3], y[4]);
        lemma_sub_eq(x, a, y, n);
    }
    if n == 6 {
        assert(pword(y, 1) == (pword(y, 0) | ((y[0] as u64) << 0u64)));
        assert(pword(y, 2) == (pword(y, 1) | ((y[1] as u64) << 8u64)));
        assert(pword(y, 3) == (pword(y, 2) | ((y[2] as u64) << 16u64)));
        assert(pword(y, 4) == (pword(y, 3) | ((y[3] as u64) << 24u64)));
        assert(pword(y, 5) == (pword(y, 4) | ((y[4] as u64) << 32u64)));
        assert(pword(y, 6) == (pword(y, 5) | ((y[5] as u64) << 40u64)));
        assert(pword(y, 6) == ((((((0u64 | ((y[0] as u64) << 0u64)) | ((y[1] as u64) << 8u64)) | ((y[2] as u64) << 16u64)) | ((y[3] as u64) << 24u64)) | ((y[4] as u64) << 32u64)) | ((y[5] as u64) << 40u64)));
        lemma_mask6(x[a + 0], x[a + 1], x[a + 2], x[a + 3], x[a + 4], x[a + 5], x[a + 6], x[a + 7], y[0], y[1], y[2], y[3], y[4], y[5]);
        lemma_sub_eq(x, a, y, n);
    }
    if n == 7 {
        assert(pword(y, 1) == (pword(y, 0) | ((y[0] as u64) << 0u64)));
        assert(pword(y, 2) == (pword(y, 1) | ((y[1] as u64) << 8u64)));
        assert(pword(y, 3) == (pword(y, 2) | ((y[2] as u64) << 16u64)));
        assert(pword(y, 4) == (pword(y, 3) | ((y[3] as u64) << 24u64)));
        assert(pword(y, 5) == (pword(y, 4) | ((y[4] as u64) << 32u64)));
        assert(pword(y, 6) == (pword(y, 5) | ((y[5] as u64) << 40u64)));
        assert(pword(y, 7) == (pword(y, 6) | ((y[6] as u64) << 48u64)));
        assert(pword(y, 7) == (((((((0u64 | ((y[0] as u64) << 0u64)) | ((y[1] as u64) << 8u64)) | ((y[2] as u64) << 16u64)) | ((y[3] as u64) << 24u64)) | ((y[4] as u64) << 32u64)) | ((y[5] as u64) << 40u64)) | ((y[6] as u64) << 48u64)));
        lemma_mask7(x[a + 0], x[a + 1], x[a + 2], x[a + 3], x[a + 4], x[a + 5], x[a + 6], x[a + 7], y[0], y[1], y[2], y[3], y[4], y[5], y[6]);
        lemma_sub_eq(x, a, y, n);
    }
    if n == 8 {
        assert(pword(y, 1) == (pword(y, 0) | ((y[0] as u64) << 0u64)));
        assert(pword(y, 2) == (pword(y, 1) | ((y[1] as u64) << 8u64)));
        assert(pword(y, 3) == (pword(y, 2) | ((y[2] as u64) << 16u64)));
        assert(pword(y, 4) == (pword(y, 3) | ((y[3] as u64) << 24u64)));
        assert(pword(y, 5) == (pword(y, 4) | ((y[4] as u64) << 32u64)));
        assert(pword(y, 6) == (pword(y, 5) | ((y[5] as u64) << 40u64)));
        assert(pword(y, 7) == (pword(y, 6) | ((y[6] as u64) << 48u64)));
        assert(pword(y, 8) == (pword(y, 7) | ((y[7] as u64) << 56u64)));
        assert(pword(y, 8) == ((((((((0u64 | ((y[0] as u64) << 0u64)) | ((y[1] as u64) << 8u64)) | ((y[2] as u64) << 16u64)) | ((y[3] as u64) << 24u64)) | ((y[4] as u64) << 32u64)) | ((y[5] as u64) << 40u64)) | ((y[6] as u64) << 48u64)) | ((y[7] as u64) << 56u64)));
        lemma_mask8(x[a + 0], x[a + 1], x[a + 2], x[a + 3], x[a + 4], x[a + 5], x[a + 6], x[a + 7], y[0], y[1], y[2], y[3], y[4], y[5], y[6], y[7]);
        lemma_sub_eq(x, a, y, n);
    }
}

} // verus!
