//! Equality of a stored text value (a column of offsets and bytes, `link::query::TextView`) with a byte string,
//! without allocation and without `slice::len` (so worker bodies may call it): the length test, then a byte loop.
//! `text_is` compares with a slice; `text_is_lit` with the first `n` bytes of a 24-byte array (a literal written in
//! the code).
use vstd::prelude::*;
use crate::link::query::{text_at, text_wf, TextView};

verus! {

/// The text column of the offsets `offs` and bytes `bytes`.
pub open spec fn tview(offs: Seq<i64>, bytes: Seq<u8>) -> TextView {
    TextView { offsets: offs, bytes }
}

/// The bytes `b[s..e]` equal `lit` (whose length is `n`).
pub fn bytes_eq(b: &[u8], s: usize, e: usize, lit: &[u8], n: usize) -> (r: bool)
    requires s <= e <= b@.len(), n == lit@.len(),
    ensures r == (b@.subrange(s as int, e as int) == lit@),
    no_unwind
{
    let ghost v = b@.subrange(s as int, e as int);
    if e - s != n {
        proof {
            if v == lit@ {
                assert(v.len() == n);
            }
        }
        return false;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            s <= e <= b@.len(), n == lit@.len(), e - s == n, i <= n, v == b@.subrange(s as int, e as int),
            forall|j: int| 0 <= j < i ==> #[trigger] v[j] == lit@[j],
        decreases n - i,
    {
        if b[s + i] != lit[i] {
            proof {
                assert(v[i as int] == b@[s + i]);
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(v =~= lit@);
    }
    true
}

/// Row `r` of the text column `(offs, bytes)` (of `rows` rows) equals `lit` (whose length is `n`).
pub fn text_is(offs: &[i64], bytes: &[u8], r: usize, lit: &[u8], n: usize, Ghost(rows): Ghost<int>) -> (b: bool)
    requires text_wf(tview(offs@, bytes@), rows), r < rows, n == lit@.len(),
    ensures b == (text_at(tview(offs@, bytes@), r as int) == lit@),
    no_unwind
{
    proof {
        assert(0 <= offs@[r as int] <= offs@[r + 1] <= bytes@.len());
        // a slice's length is a `usize`
        assert(vstd::slice::spec_slice_len(bytes) as int == bytes@.len());
    }
    let s = offs[r] as usize;
    let e = offs[r + 1] as usize;
    bytes_eq(bytes, s, e, lit, n)
}

/// The literal of a padded array: its first `n` bytes.
pub open spec fn lit_of(lit: [u8; 24], n: usize) -> Seq<u8> { lit@.subrange(0, n as int) }

/// The bytes `b[s..e]` equal the first `n` bytes of the padded literal `lit` (arrays are indexed directly: an array
/// coerced to a slice is not `no_unwind` in the pinned vstd).
pub fn bytes_eq_lit(b: &[u8], s: usize, e: usize, lit: &[u8; 24], n: usize) -> (r: bool)
    requires s <= e <= b@.len(), n <= 24,
    ensures r == (b@.subrange(s as int, e as int) == lit_of(*lit, n)),
    no_unwind
{
    let ghost v = b@.subrange(s as int, e as int);
    let ghost w = lit_of(*lit, n);
    if e - s != n {
        proof {
            if v == w {
                assert(v.len() == n);
            }
        }
        return false;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            s <= e <= b@.len(), n <= 24, e - s == n, i <= n, v == b@.subrange(s as int, e as int), w == lit_of(*lit, n),
            forall|j: int| 0 <= j < i ==> #[trigger] v[j] == w[j],
        decreases n - i,
    {
        if b[s + i] != lit[i] {
            proof {
                assert(v[i as int] == b@[s + i]);
                assert(w[i as int] == lit@[i as int]);
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(v =~= w);
    }
    true
}

/// Row `r` of the text column `(offs, bytes)` (of `rows` rows) equals the first `n` bytes of the padded literal.
pub fn text_is_lit(offs: &[i64], bytes: &[u8], r: usize, lit: &[u8; 24], n: usize, Ghost(rows): Ghost<int>) -> (b: bool)
    requires text_wf(tview(offs@, bytes@), rows), r < rows, n <= 24,
    ensures b == (text_at(tview(offs@, bytes@), r as int) == lit_of(*lit, n)),
    no_unwind
{
    proof {
        assert(0 <= offs@[r as int] <= offs@[r + 1] <= bytes@.len());
        assert(vstd::slice::spec_slice_len(bytes) as int == bytes@.len());
    }
    let s = offs[r] as usize;
    let e = offs[r + 1] as usize;
    bytes_eq_lit(bytes, s, e, lit, n)
}

} // verus!
