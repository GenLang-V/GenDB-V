//! Storage `supp_trisig`: storage `suppliers` (partsupp, supplier, nation, region, each in canonical row order) with
//! its 48 parts unchanged, extended by one part of skip metadata over supplier's own s_comment column:
//! - part `SUPP_SIG` (U64): the 128-bit byte-trigram signature (`trisig::sig_of`, two words) of s_comment of every
//!   canonical supplier row, words of row `r` at `2 r` and `2 r + 1`.
//! A LIKE pattern whose literal trigram bits are not all in a row's signature cannot match that row
//! (`trisig::lemma_sig_has`), so a scan reads 16 bytes per row instead of the comment's text for most rows.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::{Row, Val};
use crate::stores::suppliers::interface as si;
use si::common::colfmt::{u64s, u8s, text_of, text_parts_wf};
pub mod trisig;
use trisig::sig_of;

verus! {

/// Parts of storage suppliers, kept unchanged in front.
pub const SUPPLIERS_PARTS: usize = 48;
/// U64: the s_comment signatures, two words per canonical supplier row.
pub const SUPP_SIG: usize = 48;
/// Number of parts of storage supp_trisig.
pub const SUPP_TRISIG_PARTS: usize = 49;
/// Part index of the s_comment offsets (U64, rows + 1) in suppliers.
pub const S_COMMENT_OFFS_PART: usize = 27;
/// Part index of the s_comment bytes (U8) in suppliers.
pub const S_COMMENT_BYTES_PART: usize = 28;

/// The s_comment text of canonical supplier row `r` in the parts.
pub open spec fn comment_at(parts: Seq<PartView>, r: int) -> Seq<u8> {
    text_of(u64s(parts[S_COMMENT_OFFS_PART as int]), u8s(parts[S_COMMENT_BYTES_PART as int]), r)
}

/// Part `SUPP_SIG` holds the signature of s_comment of every supplier row (`n` rows): word `w` of row `r` at
/// `2 r + w`.
pub open spec fn sigs_ok(parts: Seq<PartView>, n: int) -> bool {
    &&& parts[SUPP_SIG as int] is U64
    &&& u64s(parts[SUPP_SIG as int]).len() == 2 * n
    &&& forall|r: int| 0 <= r < n ==> {
            &&& #[trigger] u64s(parts[SUPP_SIG as int])[2 * r] == sig_of(comment_at(parts, r), 0)
            &&& u64s(parts[SUPP_SIG as int])[2 * r + 1] == sig_of(comment_at(parts, r), 1)
        }
}

/// The suppliers parts hold its four tables (suppliers' `represents`), the last part the s_comment signatures.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& parts.len() == SUPP_TRISIG_PARTS
    &&& si::represents(parts.subrange(0, SUPPLIERS_PARTS as int), rels)
    &&& sigs_ok(parts, rels[1].len() as int)
}

/// The parts determine the relations they represent (the inherited parts already do).
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    si::lemma_represents_determines(parts.subrange(0, SUPPLIERS_PARTS as int), a, b);
}

/// Under `represents`, s_comment of supplier row `r` is `comment_at(parts, r)`, its signature is part `SUPP_SIG` at
/// `2 r` and `2 r + 1`, and the s_comment parts are well-formed text parts of every supplier row.
pub proof fn lemma_comment_sig(parts: Seq<PartView>, rels: Seq<Seq<Row>>, r: int)
    requires
        represents(parts, rels),
        0 <= r < rels[1].len(),
    ensures
        rels[1][r][6] == Val::Text(comment_at(parts, r)),
        u64s(parts[SUPP_SIG as int])[2 * r] == sig_of(comment_at(parts, r), 0),
        u64s(parts[SUPP_SIG as int])[2 * r + 1] == sig_of(comment_at(parts, r), 1),
        text_parts_wf(u64s(parts[S_COMMENT_OFFS_PART as int]), u8s(parts[S_COMMENT_BYTES_PART as int]), rels[1].len() as int),
        parts[S_COMMENT_OFFS_PART as int] is U64,
        parts[S_COMMENT_BYTES_PART as int] is U8,
{
    let base = parts.subrange(0, SUPPLIERS_PARTS as int);
    let tp = base.subrange(si::SUPPLIER_FIRST as int, (si::SUPPLIER_FIRST + si::SU_PARTS) as int);
    assert(si::supplier_ok(tp, rels[1]));
    assert(tp[si::SU_COMMENT_OFFS as int] == parts[S_COMMENT_OFFS_PART as int]);
    assert(tp[si::SU_COMMENT_BYTES as int] == parts[S_COMMENT_BYTES_PART as int]);
    assert(si::common::colfmt::text_col_at(tp, si::SU_COMMENT_OFFS as int, si::SU_COMMENT_BYTES as int, rels[1], 6));
}

} // verus!
