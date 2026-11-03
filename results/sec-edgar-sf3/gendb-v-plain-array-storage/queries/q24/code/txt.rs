//! Reading text values of a column (`link::query::TextCol`, row `i` = `bytes[offsets[i] .. offsets[i + 1]]`) in
//! worker tasks: length, exact equality, and the key hashes of `spec` (`tv_hash`, `ad_hash`). All `no_unwind`.
use vstd::prelude::*;
use crate::link::query::{text_at, text_wf, TextCol};
use crate::agent::hash::*;
use crate::agent::spec::{tv_hash, ad_hash};

verus! {

/// The byte length of value `i`.
pub fn text_len(t: &TextCol, i: usize, Ghost(n): Ghost<int>) -> (r: usize)
    requires text_wf(t@, n), (i as int) < n,
    ensures r == text_at(t@, i as int).len(),
    no_unwind
{
    let bytes: &'static [u8] = t.bytes;
    let a = t.offsets[i];
    let b = t.offsets[i + 1];
    assert(0 <= a <= b <= bytes.len()) by {
        assert(0 <= t@.offsets[i as int] <= t@.offsets[i + 1] <= t@.bytes.len());
    }
    let lo = a as usize;
    let hi = b as usize;
    hi - lo
}

/// The bytes of value `i` and their length.
pub fn text_get(t: &TextCol, i: usize, Ghost(n): Ghost<int>) -> (r: (&'static [u8], usize))
    requires text_wf(t@, n), (i as int) < n,
    ensures r.0@ == text_at(t@, i as int), r.1 == r.0@.len(),
    no_unwind
{
    proof {
        assert(0 <= t@.offsets[i as int] <= t@.offsets[i + 1] <= t@.bytes.len());
    }
    let bytes = crate::gendb_entry::work::text_bytes(t, i);
    let len = text_len(t, i, Ghost(n));
    (bytes, len)
}

/// Value `i` of `a` equals value `j` of `b`.
pub fn text_same(a: &TextCol, i: usize, na: Ghost<int>, b: &TextCol, j: usize, nb: Ghost<int>) -> (r: bool)
    requires text_wf(a@, na@), (i as int) < na@, text_wf(b@, nb@), (j as int) < nb@,
    ensures r == (text_at(a@, i as int) == text_at(b@, j as int)),
    no_unwind
{
    proof {
        assert(0 <= a@.offsets[i as int] <= a@.offsets[i + 1] <= a@.bytes.len());
        assert(0 <= b@.offsets[j as int] <= b@.offsets[j + 1] <= b@.bytes.len());
    }
    crate::gendb_entry::work::text_eq(a, i, b, j)
}

/// Value `i` of `a` equals the bytes `v` (`vlen` of them).
pub fn text_is(a: &TextCol, i: usize, Ghost(n): Ghost<int>, v: &[u8], vlen: usize) -> (r: bool)
    requires text_wf(a@, n), (i as int) < n, vlen == v@.len(),
    ensures r == (text_at(a@, i as int) == v@),
    no_unwind
{
    let (x, xlen) = text_get(a, i, Ghost(n));
    if xlen != vlen {
        return false;
    }
    let mut k: usize = 0;
    while k < vlen
        invariant
            k <= vlen, vlen == v@.len(), xlen == x@.len(), xlen == vlen,
            x@ == text_at(a@, i as int),
            forall|q: int| 0 <= q < k ==> x@[q] == v@[q],
        decreases vlen - k,
    {
        if x[k] != v[k] {
            return false;
        }
        k = k + 1;
    }
    proof {
        assert(x@ =~= v@);
    }
    true
}

/// `hash_text` of value `i` under `seed`.
pub fn hash_at(t: &TextCol, i: usize, Ghost(n): Ghost<int>, seed: u64) -> (h: u64)
    requires text_wf(t@, n), (i as int) < n,
    ensures h == hash_text(text_at(t@, i as int), seed),
    no_unwind
{
    let (bytes, len) = text_get(t, i, Ghost(n));
    hash_bytes(bytes, len, seed)
}

/// `tv_hash` of the values `i` of a tag column and a version column.
pub fn tv_hash_at(tag: &TextCol, ver: &TextCol, i: usize, Ghost(n): Ghost<int>) -> (h: u64)
    requires text_wf(tag@, n), text_wf(ver@, n), (i as int) < n,
    ensures h == tv_hash(text_at(tag@, i as int), text_at(ver@, i as int)), h != 0,
    no_unwind
{
    let ht = hash_at(tag, i, Ghost(n), SEED_TAG);
    let h = hash_at(ver, i, Ghost(n), ht);
    let r = h | 1u64;
    assert(r != 0) by (bit_vector) requires r == h | 1u64;
    r
}

/// `ad_hash` of value `i` of an adsh column.
pub fn ad_hash_at(t: &TextCol, i: usize, Ghost(n): Ghost<int>) -> (h: u64)
    requires text_wf(t@, n), (i as int) < n,
    ensures h == ad_hash(text_at(t@, i as int)), h != 0,
    no_unwind
{
    let h = hash_at(t, i, Ghost(n), SEED_ADSH);
    let r = h | 1u64;
    assert(r != 0) by (bit_vector) requires r == h | 1u64;
    r
}

} // verus!
