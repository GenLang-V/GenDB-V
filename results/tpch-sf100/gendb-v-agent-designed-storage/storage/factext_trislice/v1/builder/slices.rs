//! Bit-slicing of the per-row signature words: plane `q` of half `h` gets, at bit `r % 64` of its word `r / 64`,
//! bit `q` of signature word `h` of row `r` (`slice_half`). Words are built one bit at a time (`plane_word`); the
//! planes of word `w` are written at `q * nw + w` (`lemma_index_unique`: distinct planes and words never share a
//! slot).
use vstd::prelude::*;
use crate::stores::factext_trislice::interface::{bit_at, plane_words, slice_bit, sig_bit};

verus! {

/// OR-ing bit `s` of `v` into position `i` of `x` sets bit `i` to that bit and keeps every other bit.
proof fn lemma_set_bit(x: u64, v: u64, s: u64, i: u64, j: u64)
    requires s < 64, i < 64, j < 64, !((x >> i) & 1u64 == 1u64),
    ensures
        j != i ==> ((((x | (((v >> s) & 1u64) << i)) >> j) & 1u64 == 1u64) == ((x >> j) & 1u64 == 1u64)),
        j == i ==> ((((x | (((v >> s) & 1u64) << i)) >> j) & 1u64 == 1u64) == ((v >> s) & 1u64 == 1u64)),
{
    assert(j != i ==> ((((x | (((v >> s) & 1u64) << i)) >> j) & 1u64 == 1u64) == ((x >> j) & 1u64 == 1u64)))
        by (bit_vector) requires s < 64, i < 64, j < 64;
    assert(j == i ==> ((((x | (((v >> s) & 1u64) << i)) >> j) & 1u64 == 1u64) == ((v >> s) & 1u64 == 1u64)))
        by (bit_vector) requires s < 64, i < 64, j < 64, !((x >> i) & 1u64 == 1u64);
}

/// No bit of 0 is set.
proof fn lemma_zero_bits(j: u64)
    requires j < 64,
    ensures !((0u64 >> j) & 1u64 == 1u64),
{
    assert(!((0u64 >> j) & 1u64 == 1u64)) by (bit_vector) requires j < 64;
}

/// Word `w` of plane `q` of half `h`: bit `i` is bit `q` of signature word `h` of row `64 w + i` (rows past `n`: 0).
pub fn plane_word(sig: &[u64], slen: usize, n: usize, h: usize, q: usize, w: usize) -> (x: u64)
    requires
        sig@.len() == 2 * n,
        slen == sig@.len(),
        h < 2,
        q < 64,
        64 * w < n,
    ensures
        forall|i: int| 0 <= i < 64 && 64 * w + i < n ==> #[trigger] bit_at(x, i) == sig_bit(sig@, h as int, q as int, 64 * w + i),
{
    let mut x: u64 = 0;
    let mut i: usize = 0;
    proof {
        assert forall|j: int| 0 <= j < 64 implies !#[trigger] bit_at(x, j) by {
            lemma_zero_bits(j as u64);
        }
    }
    while i < 64
        invariant
            sig@.len() == 2 * n, slen == sig@.len(),
            h < 2, q < 64, 64 * w < n,
            i <= 64,
            forall|j: int| 0 <= j < i && 64 * w + j < n ==> #[trigger] bit_at(x, j) == sig_bit(sig@, h as int, q as int, 64 * w + j),
            forall|j: int| i <= j < 64 ==> !#[trigger] bit_at(x, j),
        decreases 64 - i,
    {
        let r = 64 * w + i;
        if r < n {
            let v = sig[2 * r + h];
            let ghost x0 = x;
            assert(!bit_at(x0, i as int));
            x = x | (((v >> (q as u64)) & 1u64) << (i as u64));
            proof {
                assert forall|j: int| 0 <= j < 64 implies #[trigger] bit_at(x, j) == if j == i {
                    bit_at(v, q as int)
                } else {
                    bit_at(x0, j)
                } by {
                    lemma_set_bit(x0, v, q as u64, i as u64, j as u64);
                }
            }
        }
        i = i + 1;
    }
    x
}

/// Slots `q * nw + w` of distinct (plane, word) pairs differ.
proof fn lemma_index_unique(q: int, w: int, q2: int, w2: int, nw: int)
    requires
        0 <= q, 0 <= q2, 0 <= w < nw, 0 <= w2 < nw,
        q * nw + w == q2 * nw + w2,
    ensures q == q2 && w == w2,
{
    if q < q2 {
        assert(q2 * nw >= (q + 1) * nw) by (nonlinear_arith) requires q < q2, nw > 0;
        assert(false) by (nonlinear_arith) requires q2 * nw >= (q + 1) * nw, q * nw + w == q2 * nw + w2, w < nw, w2 >= 0;
    } else if q2 < q {
        assert(q * nw >= (q2 + 1) * nw) by (nonlinear_arith) requires q2 < q, nw > 0;
        assert(false) by (nonlinear_arith) requires q * nw >= (q2 + 1) * nw, q * nw + w == q2 * nw + w2, w2 < nw, w >= 0;
    }
}

/// Slot `q * nw + w` lies in the 64 planes.
proof fn lemma_index_range(q: int, w: int, nw: int)
    requires 0 <= q < 64, 0 <= w < nw,
    ensures 0 <= q * nw + w < 64 * nw,
{
    assert(q * nw + w < 64 * nw) by (nonlinear_arith) requires 0 <= q < 64, 0 <= w < nw;
    assert(q * nw >= 0) by (nonlinear_arith) requires 0 <= q, 0 <= nw;
}

/// Row `r` is bit `r % 64` of word `r / 64`.
proof fn lemma_row_word(r: int)
    requires 0 <= r,
    ensures r == 64 * (r / 64) + r % 64, 0 <= r % 64 < 64, 0 <= r / 64,
{
}

/// Half `h` of the bit-sliced signatures of the `n` rows of `sig` (two words per row): 64 planes of `plane_words(n)`
/// words.
pub fn slice_half(sig: &[u64], slen: usize, n: usize, h: usize) -> (v: Vec<u64>)
    requires
        sig@.len() == 2 * n,
        slen == sig@.len(),
        h < 2,
    ensures
        v@.len() == 64 * plane_words(n as int),
        forall|q: int, r: int| 0 <= q < 64 && 0 <= r < n ==>
            #[trigger] slice_bit(v@, plane_words(n as int), q, r) == sig_bit(sig@, h as int, q, r),
{
    let nw: usize = n / 64 + if n % 64 == 0 { 0 } else { 1 };
    assert(nw as int == plane_words(n as int));
    assert(64 * nw <= n + 63);
    let total: usize = 64 * nw;
    let mut v: Vec<u64> = crate::gendb_entry::work::filled(total, 0u64);
    let ghost nwi = nw as int;
    let mut w: usize = 0;
    while w < nw
        invariant
            sig@.len() == 2 * n, h < 2, slen == sig@.len(),
            nw as int == plane_words(n as int), nwi == nw as int, total == 64 * nw,
            nw == n / 64 + if n % 64 == 0 { 0usize } else { 1usize },
            w <= nw,
            v@.len() == total,
            forall|q: int, r: int| 0 <= q < 64 && 0 <= r < n && r / 64 < w ==>
                #[trigger] slice_bit(v@, nwi, q, r) == sig_bit(sig@, h as int, q, r),
        decreases nw - w,
    {
        assert(64 * w < n);
        let mut q: usize = 0;
        while q < 64
            invariant
                sig@.len() == 2 * n, h < 2, slen == sig@.len(),
                nw as int == plane_words(n as int), nwi == nw as int, total == 64 * nw,
                w < nw, 64 * w < n,
                q <= 64,
                v@.len() == total,
                forall|q2: int, r: int| 0 <= q2 < 64 && 0 <= r < n && (r / 64 < w || (r / 64 == w && q2 < q)) ==>
                    #[trigger] slice_bit(v@, nwi, q2, r) == sig_bit(sig@, h as int, q2, r),
            decreases 64 - q,
        {
            let x = plane_word(sig, slen, n, h, q, w);
            proof {
                lemma_index_range(q as int, w as int, nwi);
            }
            let ghost v0 = v@;
            let slot = q * nw + w;
            crate::gendb_entry::work::put(&mut v, slot, x);
            proof {
                assert forall|q2: int, r: int| 0 <= q2 < 64 && 0 <= r < n && (r / 64 < w || (r / 64 == w && q2 < q + 1)) implies
                    #[trigger] slice_bit(v@, nwi, q2, r) == sig_bit(sig@, h as int, q2, r) by {
                    lemma_row_word(r);
                    lemma_index_range(q2, r / 64, nwi);
                    if q2 == q && r / 64 == w {
                        assert(v@[q2 * nwi + r / 64] == x);
                        assert(bit_at(x, r % 64) == sig_bit(sig@, h as int, q as int, 64 * w + r % 64));
                    } else {
                        if q2 * nwi + r / 64 == slot {
                            lemma_index_unique(q2, r / 64, q as int, w as int, nwi);
                        }
                        assert(v@[q2 * nwi + r / 64] == v0[q2 * nwi + r / 64]);
                        assert(slice_bit(v0, nwi, q2, r) == sig_bit(sig@, h as int, q2, r));
                    }
                }
            }
            q = q + 1;
        }
        w = w + 1;
    }
    proof {
        assert forall|q: int, r: int| 0 <= q < 64 && 0 <= r < n implies
            #[trigger] slice_bit(v@, plane_words(n as int), q, r) == sig_bit(sig@, h as int, q, r) by {
            lemma_row_word(r);
            assert(r / 64 < w) by {
                assert(64 * (r / 64) <= r);
            }
        }
    }
    v
}

} // verus!
