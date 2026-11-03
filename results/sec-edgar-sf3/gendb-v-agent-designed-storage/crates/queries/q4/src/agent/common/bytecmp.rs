//! Byte-string comparison eight bytes at a time: `fast_cmp` is `lex_cmp` (skips the common prefix in 8-byte
//! little-endian words, then compares bytewise) and `same_bytes` checks two byte ranges for equality the same way.
//! `no_unwind`; lengths are passed in (slice `len` is not `no_unwind`).
use vstd::prelude::*;
use crate::spec::text::lex_cmp;

verus! {

/// The little-endian word of bytes `s[i, i + 8)`.
pub open spec fn w8(s: Seq<u8>, i: int) -> u64 {
    (s[i] as u64) | ((s[i + 1] as u64) << 8u64) | ((s[i + 2] as u64) << 16u64) | ((s[i + 3] as u64) << 24u64)
        | ((s[i + 4] as u64) << 32u64) | ((s[i + 5] as u64) << 40u64) | ((s[i + 6] as u64) << 48u64)
        | ((s[i + 7] as u64) << 56u64)
}

/// Bytes `s[i, i + 8)` as one word (read through an 8-byte subslice, so one bounds check covers the 8 loads).
fn load8(s: &[u8], i: usize) -> (w: u64)
    requires i + 8 <= s@.len(),
    ensures w == w8(s@, i as int),
    no_unwind
{
    let (_, tail) = s.split_at(i);
    let (b, _) = tail.split_at(8);
    assert(b@ =~= s@.subrange(i as int, i + 8));
    (b[0] as u64) | ((b[1] as u64) << 8u64) | ((b[2] as u64) << 16u64) | ((b[3] as u64) << 24u64)
        | ((b[4] as u64) << 32u64) | ((b[5] as u64) << 40u64) | ((b[6] as u64) << 48u64)
        | ((b[7] as u64) << 56u64)
}

/// Equal words have equal bytes.
proof fn lemma_w8_eq(x: Seq<u8>, y: Seq<u8>, i: int)
    requires 0 <= i, i + 8 <= x.len(), i + 8 <= y.len(), w8(x, i) == w8(y, i),
    ensures forall|t: int| i <= t < i + 8 ==> x[t] == y[t],
{
    let (a0, a1, a2, a3, a4, a5, a6, a7) = (x[i], x[i + 1], x[i + 2], x[i + 3], x[i + 4], x[i + 5], x[i + 6], x[i + 7]);
    let (b0, b1, b2, b3, b4, b5, b6, b7) = (y[i], y[i + 1], y[i + 2], y[i + 3], y[i + 4], y[i + 5], y[i + 6], y[i + 7]);
    assert(a0 == b0 && a1 == b1 && a2 == b2 && a3 == b3 && a4 == b4 && a5 == b5 && a6 == b6 && a7 == b7) by (bit_vector)
        requires
            (a0 as u64) | ((a1 as u64) << 8u64) | ((a2 as u64) << 16u64) | ((a3 as u64) << 24u64)
                | ((a4 as u64) << 32u64) | ((a5 as u64) << 40u64) | ((a6 as u64) << 48u64) | ((a7 as u64) << 56u64)
            == (b0 as u64) | ((b1 as u64) << 8u64) | ((b2 as u64) << 16u64) | ((b3 as u64) << 24u64)
                | ((b4 as u64) << 32u64) | ((b5 as u64) << 40u64) | ((b6 as u64) << 48u64) | ((b7 as u64) << 56u64);
    assert forall|t: int| i <= t < i + 8 implies x[t] == y[t] by {
        if t == i { } else if t == i + 1 { } else if t == i + 2 { } else if t == i + 3 { }
        else if t == i + 4 { } else if t == i + 5 { } else if t == i + 6 { } else { assert(t == i + 7); }
    }
}

/// A common stretch `[i, i + k)` does not change the order of the suffixes.
proof fn lemma_skip(x: Seq<u8>, y: Seq<u8>, i: int, k: int)
    requires 0 <= i, 0 <= k, i + k <= x.len(), i + k <= y.len(), forall|t: int| i <= t < i + k ==> x[t] == y[t],
    ensures
        lex_cmp(x.subrange(i, x.len() as int), y.subrange(i, y.len() as int))
            == lex_cmp(x.subrange(i + k, x.len() as int), y.subrange(i + k, y.len() as int)),
    decreases k,
{
    if k > 0 {
        let sx = x.subrange(i, x.len() as int);
        let sy = y.subrange(i, y.len() as int);
        assert(sx[0] == x[i] && sy[0] == y[i]);
        assert(sx.drop_first() =~= x.subrange(i + 1, x.len() as int));
        assert(sy.drop_first() =~= y.subrange(i + 1, y.len() as int));
        lemma_skip(x, y, i + 1, k - 1);
    }
}

/// Byte order of two slices (`lex_cmp`), lengths passed in.
pub fn fast_cmp(x: &[u8], xn: usize, y: &[u8], yn: usize) -> (r: i8)
    requires xn == x@.len(), yn == y@.len(),
    ensures r as int == lex_cmp(x@, y@),
    no_unwind
{
    let mut i: usize = 0;
    assert(x@.subrange(0, xn as int) =~= x@);
    assert(y@.subrange(0, yn as int) =~= y@);
    // Whole equal words.
    loop
        invariant
            xn == x@.len(), yn == y@.len(), i <= xn, i <= yn,
            lex_cmp(x@.subrange(i as int, xn as int), y@.subrange(i as int, yn as int)) == lex_cmp(x@, y@),
        decreases xn - i,
    {
        if xn - i < 8 || yn - i < 8 {
            break;
        }
        if load8(x, i) != load8(y, i) {
            break;
        }
        proof {
            lemma_w8_eq(x@, y@, i as int);
            lemma_skip(x@, y@, i as int, 8);
        }
        i = i + 8;
    }
    // The rest bytewise.
    while i < xn && i < yn
        invariant
            xn == x@.len(), yn == y@.len(), i <= xn, i <= yn,
            lex_cmp(x@.subrange(i as int, xn as int), y@.subrange(i as int, yn as int)) == lex_cmp(x@, y@),
        decreases xn - i,
    {
        let ghost sx = x@.subrange(i as int, xn as int);
        let ghost sy = y@.subrange(i as int, yn as int);
        assert(sx[0] == x@[i as int] && sy[0] == y@[i as int]);
        if x[i] < y[i] {
            return -1;
        } else if x[i] > y[i] {
            return 1;
        }
        assert(sx.drop_first() =~= x@.subrange(i + 1, xn as int));
        assert(sy.drop_first() =~= y@.subrange(i + 1, yn as int));
        i = i + 1;
    }
    if i < xn { 1 } else if i < yn { -1 } else { 0 }
}

/// Whether `a[x0, x1)` and `b[x0, x1)` hold the same bytes.
pub fn same_bytes(a: &[u8], b: &[u8], x0: usize, x1: usize) -> (r: bool)
    requires x0 <= x1, x1 <= a@.len(), x1 <= b@.len(),
    ensures r == (forall|y: int| x0 <= y < x1 ==> #[trigger] a@[y] == b@[y]),
    no_unwind
{
    let mut x = x0;
    loop
        invariant
            x0 <= x <= x1, x1 <= a@.len(), x1 <= b@.len(),
            forall|y: int| x0 <= y < x ==> #[trigger] a@[y] == b@[y],
        decreases x1 - x,
    {
        if x1 - x < 8 {
            break;
        }
        if load8(a, x) != load8(b, x) {
            break;
        }
        proof { lemma_w8_eq(a@, b@, x as int); }
        x = x + 8;
    }
    while x < x1
        invariant
            x0 <= x <= x1, x1 <= a@.len(), x1 <= b@.len(),
            forall|y: int| x0 <= y < x ==> #[trigger] a@[y] == b@[y],
        decreases x1 - x,
    {
        if a[x] != b[x] {
            return false;
        }
        x = x + 1;
    }
    true
}

} // verus!
