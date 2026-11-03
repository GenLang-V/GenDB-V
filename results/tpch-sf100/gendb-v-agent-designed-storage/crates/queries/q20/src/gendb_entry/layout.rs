// FRAMEWORK FILE: mathematical view of data-representation parts (`verification/obligations/gendb_entry/layout.rs`).
//
// Copied unchanged into every candidate crate as `crate::gendb_entry::layout`. Authors cannot edit
// it. A representation is an ordered list of typed parts: the builder returns owned parts
// (`OwnedPart`), the host stores them, and the query reads them back as borrowed parts (`Part`).
// Both have the same view, so "the query reads what the builder wrote" is one equality of views
// (the trusted storage round trip). The author defines `crate::agent::decode` over this view.
use vstd::prelude::*;
use crate::gendb_abi::{OwnedPart, Part};

verus! {

/// Element type and values of one part.
pub enum PartView {
    I8(Seq<i8>),
    I16(Seq<i16>),
    I32(Seq<i32>),
    I64(Seq<i64>),
    I128(Seq<i128>),
    U8(Seq<u8>),
    U16(Seq<u16>),
    U32(Seq<u32>),
    U64(Seq<u64>),
}

pub open spec fn part_view(p: Part) -> PartView {
    match p {
        Part::I8(s) => PartView::I8(s@),
        Part::I16(s) => PartView::I16(s@),
        Part::I32(s) => PartView::I32(s@),
        Part::I64(s) => PartView::I64(s@),
        Part::I128(s) => PartView::I128(s@),
        Part::U8(s) => PartView::U8(s@),
        Part::U16(s) => PartView::U16(s@),
        Part::U32(s) => PartView::U32(s@),
        Part::U64(s) => PartView::U64(s@),
    }
}

pub open spec fn owned_part_view(p: OwnedPart) -> PartView {
    match p {
        OwnedPart::I8(v) => PartView::I8(v@),
        OwnedPart::I16(v) => PartView::I16(v@),
        OwnedPart::I32(v) => PartView::I32(v@),
        OwnedPart::I64(v) => PartView::I64(v@),
        OwnedPart::I128(v) => PartView::I128(v@),
        OwnedPart::U8(v) => PartView::U8(v@),
        OwnedPart::U16(v) => PartView::U16(v@),
        OwnedPart::U32(v) => PartView::U32(v@),
        OwnedPart::U64(v) => PartView::U64(v@),
    }
}

/// View of the parts a query reads.
pub open spec fn parts_view(parts: Seq<Part>) -> Seq<PartView> {
    parts.map_values(|p: Part| part_view(p))
}

/// View of the parts a builder returns.
pub open spec fn owned_parts_view(parts: Seq<OwnedPart>) -> Seq<PartView> {
    parts.map_values(|p: OwnedPart| owned_part_view(p))
}

} // verus!
