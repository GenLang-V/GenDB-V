//! `no_unwind` access to the values of a well-formed text column (`link::query::TextCol`): the bytes of value `i`
//! with their length (slice `len` is not `no_unwind`, so lengths travel with the slices), and byte equality.
use vstd::prelude::*;
use crate::link::query::{text_at, text_wf, TextCol, TextView};

verus! {

/// Value `i` of a text column of `n` rows and its length in bytes.
pub fn text_val(c: &TextCol, i: usize, Ghost(n): Ghost<int>) -> (r: (&'static [u8], usize))
    requires text_wf(c@, n), i < n,
    ensures r.0@ == text_at(c@, i as int), r.1 == r.0@.len(),
    no_unwind
{
    let a = c.offsets[i];
    let b = c.offsets[i + 1];
    assert(0 <= a <= b <= c@.bytes.len()) by {
        assert(c@.offsets[i as int] == a && c@.offsets[i + 1] == b);
    }
    assert(c.bytes@.len() == c.bytes.len() as int);
    let x = crate::gendb_entry::work::text_bytes(c, i);
    let len = (b - a) as usize;
    (x, len)
}

/// Bytes `a .. b` of `bytes` (for example a text value whose offsets were read earlier).
pub fn bytes_range(bytes: &'static [u8], a: usize, b: usize) -> (r: (&'static [u8], usize))
    requires a <= b <= bytes@.len(),
    ensures r.0@ == bytes@.subrange(a as int, b as int), r.1 == r.0@.len(),
    no_unwind
{
    let (_, tail) = bytes.split_at(a);
    let (mid, _) = tail.split_at(b - a);
    proof {
        assert(mid@ =~= bytes@.subrange(a as int, b as int));
    }
    (mid, b - a)
}

/// `a[x] .. b[x]` is the byte range of value `l[x]` of the text column `t`, for every `x < k`.
pub open spec fn col_offs(t: TextView, l: Seq<usize>, a: Seq<usize>, b: Seq<usize>, k: int) -> bool {
    forall|x: int| 0 <= x < k ==> #[trigger] a[x] as int == t.offsets[l[x] as int] && b[x] as int == t.offsets[l[x] + 1]
}

/// The byte ranges of the values `l[0..k]` of a text column of `n` rows into `a` and `b`: independent loads, all
/// issued before any value byte is read, so that their cache misses overlap.
pub fn gather_offs(t: &TextCol, Ghost(n): Ghost<int>, l: &Vec<usize>, k: usize, a: &mut Vec<usize>, b: &mut Vec<usize>)
    requires
        text_wf(t@, n), k <= l@.len(), k <= old(a)@.len(), k <= old(b)@.len(),
        forall|x: int| 0 <= x < k ==> (#[trigger] l@[x] as int) < n,
    ensures
        final(a)@.len() == old(a)@.len(), final(b)@.len() == old(b)@.len(),
        col_offs(t@, l@, final(a)@, final(b)@, k as int),
    no_unwind
{
    let mut q: usize = 0;
    while q < k
        invariant
            text_wf(t@, n), k <= l@.len(), k <= a@.len(), k <= b@.len(),
            a@.len() == old(a)@.len(), b@.len() == old(b)@.len(),
            forall|x: int| 0 <= x < k ==> (#[trigger] l@[x] as int) < n,
            q <= k, col_offs(t@, l@, a@, b@, q as int),
        decreases k - q,
    {
        let i = l[q];
        proof {
            assert((i as int) < n);
        }
        let x0 = t.offsets[i];
        let x1 = t.offsets[i + 1];
        proof {
            assert(t@.offsets[i as int] == x0 && t@.offsets[i + 1] == x1);
            // The offsets are at most the byte length, a `usize` slice length.
            assert(t.bytes@.len() == t.bytes.len() as int && t@.bytes == t.bytes@);
            assert(0 <= x0 <= x1 <= t@.bytes.len());
        }
        let ghost a0 = a@;
        let ghost b0 = b@;
        crate::gendb_entry::work::put(a, q, x0 as usize);
        crate::gendb_entry::work::put(b, q, x1 as usize);
        proof {
            assert forall|x: int| 0 <= x < q + 1 implies
                #[trigger] a@[x] as int == t@.offsets[l@[x] as int] && b@[x] as int == t@.offsets[l@[x] + 1] by {
                if x < q {
                    assert(a@[x] == a0[x] && b@[x] == b0[x]);
                }
            }
        }
        q = q + 1;
    }
}

/// The length in bytes of value `i`.
pub fn text_len(c: &TextCol, i: usize, Ghost(n): Ghost<int>) -> (r: usize)
    requires text_wf(c@, n), i < n,
    ensures r == text_at(c@, i as int).len(),
    no_unwind
{
    let a = c.offsets[i];
    let b = c.offsets[i + 1];
    assert(0 <= a <= b <= c@.bytes.len()) by {
        assert(c@.offsets[i as int] == a && c@.offsets[i + 1] == b);
    }
    assert(c.bytes@.len() == c.bytes.len() as int);
    (b - a) as usize
}

/// Byte equality of `x` (`xl` bytes) and `y` (`yl` bytes).
pub fn bytes_eq(x: &[u8], xl: usize, y: &[u8], yl: usize) -> (r: bool)
    requires xl == x@.len(), yl == y@.len(),
    ensures r == (x@ == y@),
    no_unwind
{
    if xl != yl {
        return false;
    }
    let mut k: usize = 0;
    while k < xl
        invariant k <= xl, xl == x@.len(), yl == y@.len(), xl == yl, forall|t: int| 0 <= t < k ==> x@[t] == y@[t],
        decreases xl - k,
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

} // verus!
