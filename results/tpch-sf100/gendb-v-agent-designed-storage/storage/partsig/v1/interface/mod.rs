//! Storage `partsig`: storage `custpart` (customer, part) with its 50 parts unchanged, extended by one part:
//! - part `SIG` (U64, one per stored part row): a 64-bit Bloom filter over the byte trigrams of the row's p_name.
//!   The trigram `a, b, c` hashes to bit `tri_hash(a, b, c)` in `0 .. 64` (the top 6 bits of the 32-bit Knuth
//!   multiplicative hash of its 24-bit value); `sig[c]` has the bit of every trigram of p_name of row `c` set
//!   (`sig_covers`; it may have more). A byte string with a trigram whose bit is not in a row's signature does not
//!   occur in that row's p_name, so a filter may skip the row (`lemma_sub_tri`). A signature other than all ones also
//!   says that the row's p_name is ASCII (`ascii_text`), so a skipped row needs no byte read at all.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::Row;
use crate::stores::custpart::interface as ci;
use ci::common::colfmt::{u8s, u64s, text_of};

verus! {

/// Parts of storage custpart, kept unchanged in front.
pub const CUSTPART_PARTS: usize = 50;
/// U64 `sig`: the trigram signatures of p_name.
pub const SIG: usize = 50;
/// Number of parts of storage partsig.
pub const PARTSIG_PARTS: usize = 51;

/// Bit position (`0 .. 64`) of the trigram `a, b, c`.
pub open spec fn tri_hash(a: u8, b: u8, c: u8) -> int {
    let x = (a as int) * 65536 + (b as int) * 256 + (c as int);
    ((x * 2654435761) % 4294967296) / 67108864
}

/// The signature bit of the trigram `a, b, c`.
pub open spec fn tri_bit(a: u8, b: u8, c: u8) -> u64 {
    1u64 << (tri_hash(a, b, c) as u64)
}

/// Signature `s` has the bit of the trigram of `t` starting at `p`.
pub open spec fn has_tri(s: u64, t: Seq<u8>, p: int) -> bool {
    s & tri_bit(t[p], t[p + 1], t[p + 2]) == tri_bit(t[p], t[p + 1], t[p + 2])
}

/// Signature `s` covers text `t`: it has the bit of every trigram of `t`.
pub open spec fn sig_covers(t: Seq<u8>, s: u64) -> bool {
    forall|p: int| 0 <= p && p + 2 < t.len() ==> #[trigger] has_tri(s, t, p)
}

/// Every byte of `t` is ASCII.
pub open spec fn ascii_text(t: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < t.len() ==> #[trigger] t[i] < 0x80
}

/// The all-ones signature (no ASCII claim).
pub const ALL: u64 = 0xffff_ffff_ffff_ffffu64;

/// Signature `s` of text `t`: it covers `t`, and `t` is ASCII unless `s` is all ones.
pub open spec fn sig_row_ok(t: Seq<u8>, s: u64) -> bool {
    &&& sig_covers(t, s)
    &&& s != ALL ==> ascii_text(t)
}

/// Rows of table part (its layout part).
pub open spec fn part_rows(parts: Seq<PartView>) -> int {
    u64s(parts[(ci::PART_FIRST + ci::PA_LAYOUT) as int])[0] as int
}

/// p_name of stored part row `c`.
pub open spec fn pname_of(parts: Seq<PartView>, c: int) -> Seq<u8> {
    text_of(u64s(parts[(ci::PART_FIRST + ci::PA_NAME_OFFS) as int]), u8s(parts[(ci::PART_FIRST + ci::PA_NAME_BYTES) as int]), c)
}

/// The signatures.
pub open spec fn sigs(parts: Seq<PartView>) -> Seq<u64> {
    u64s(parts[SIG as int])
}

/// One signature per part row, covering the row's p_name (and saying it is ASCII unless all ones).
pub open spec fn sig_ok(parts: Seq<PartView>) -> bool {
    &&& parts[SIG as int] is U64
    &&& sigs(parts).len() == part_rows(parts)
    &&& forall|c: int| 0 <= c < part_rows(parts) ==> #[trigger] sig_row_ok(pname_of(parts, c), sigs(parts)[c])
}

/// The custpart parts hold customer and part (custpart's `represents`), the last part the signatures.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& parts.len() == PARTSIG_PARTS
    &&& ci::represents(parts.subrange(0, CUSTPART_PARTS as int), rels)
    &&& sig_ok(parts)
}

/// The parts determine the relations they represent.
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    ci::lemma_represents_determines(parts.subrange(0, CUSTPART_PARTS as int), a, b);
}

/// The hash is a bit position.
pub proof fn lemma_tri_hash_range(a: u8, b: u8, c: u8)
    ensures 0 <= tri_hash(a, b, c) < 64,
{
    let x = (a as int) * 65536 + (b as int) * 256 + (c as int);
    let m = (x * 2654435761) % 4294967296;
    assert(0 <= m < 4294967296);
    assert(m / 67108864 < 64) by (nonlinear_arith) requires 0 <= m < 4294967296;
    assert(m / 67108864 >= 0) by (nonlinear_arith) requires 0 <= m;
}

/// The bit of the trigram `a, b, c`, computed (usable in worker bodies).
pub fn tri_bit_exec(a: u8, b: u8, c: u8) -> (r: u64)
    ensures r == tri_bit(a, b, c),
    no_unwind
{
    proof { lemma_tri_hash_range(a, b, c); }
    let x: u64 = (a as u64) * 65536 + (b as u64) * 256 + (c as u64);
    assert(x < 16777216);
    assert(x * 2654435761 < 0x1_0000_0000_0000_0000) by (nonlinear_arith) requires x < 16777216;
    let h: u64 = ((x * 2654435761) % 4294967296) / 67108864;
    assert(h as int == tri_hash(a, b, c));
    1u64 << h
}

/// A text containing `w` at `i` has in its signature the bit of every trigram of `w`.
pub proof fn lemma_sub_tri(t: Seq<u8>, s: u64, w: Seq<u8>, i: int, q: int)
    requires
        sig_covers(t, s),
        0 <= i, i + w.len() <= t.len(), t.subrange(i, i + w.len()) == w,
        0 <= q, q + 2 < w.len(),
    ensures has_tri(s, w, q),
{
    assert(t[i + q] == w[q] && t[i + q + 1] == w[q + 1] && t[i + q + 2] == w[q + 2]) by {
        assert(t.subrange(i, i + w.len())[q] == t[i + q]);
        assert(t.subrange(i, i + w.len())[q + 1] == t[i + q + 1]);
        assert(t.subrange(i, i + w.len())[q + 2] == t[i + q + 2]);
    }
    assert(has_tri(s, t, i + q));
}

} // verus!
