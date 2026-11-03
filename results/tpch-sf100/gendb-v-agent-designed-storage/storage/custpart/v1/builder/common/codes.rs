//! Unsigned code widths of frame-of-reference columns (u8, u16, u32): the `Code` trait gives each width its
//! largest value, a `no_unwind` conversion from `u64`, and the owned part holding a code vector, so one generic
//! encoder serves every width.
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{owned_part_view, PartView};

verus! {

/// An unsigned code width.
pub trait Code: Copy + Send + Sync + Sized + 'static {
    /// Largest code value.
    spec fn cap() -> int;

    /// The code as an integer.
    spec fn val(c: Self) -> int;

    /// The part view of a code sequence.
    spec fn part_of(s: Seq<Self>) -> PartView;

    proof fn lemma_code(c: Self)
        ensures 0 <= Self::val(c) <= Self::cap();

    proof fn lemma_part_of(s: Seq<Self>)
        ensures
            crate::builder::iface::common::colfmt::is_code_part(Self::part_of(s)),
            crate::gendb_entry::stored::part_len(Self::part_of(s)) == s.len(),
            forall|i: int| 0 <= i < s.len() ==>
                #[trigger] crate::builder::iface::common::colfmt::code_at(Self::part_of(s), i) == Self::val(s[i]);

    /// `x` as a code.
    fn from_u64(x: u64) -> (c: Self)
        requires x <= Self::cap(),
        ensures Self::val(c) == x,
        no_unwind;

    /// Largest code value, `no_unwind`.
    fn cap_u64() -> (r: u64)
        ensures r == Self::cap(),
        no_unwind;

    /// The zero code.
    fn zero() -> (c: Self)
        ensures Self::val(c) == 0,
        no_unwind;

    /// The owned part of a code vector.
    fn into_part(v: Vec<Self>) -> (p: OwnedPart)
        ensures owned_part_view(p) == Self::part_of(v@);
}

impl Code for u8 {
    open spec fn cap() -> int { 255 }

    open spec fn val(c: u8) -> int { c as int }

    open spec fn part_of(s: Seq<u8>) -> PartView { PartView::U8(s) }

    proof fn lemma_code(c: u8) {}

    proof fn lemma_part_of(s: Seq<u8>) {}

    fn from_u64(x: u64) -> (c: u8) { x as u8 }

    fn cap_u64() -> (r: u64) { 255 }

    fn zero() -> (c: u8) { 0 }

    fn into_part(v: Vec<u8>) -> (p: OwnedPart) { OwnedPart::U8(v) }
}

impl Code for u16 {
    open spec fn cap() -> int { 65535 }

    open spec fn val(c: u16) -> int { c as int }

    open spec fn part_of(s: Seq<u16>) -> PartView { PartView::U16(s) }

    proof fn lemma_code(c: u16) {}

    proof fn lemma_part_of(s: Seq<u16>) {}

    fn from_u64(x: u64) -> (c: u16) { x as u16 }

    fn cap_u64() -> (r: u64) { 65535 }

    fn zero() -> (c: u16) { 0 }

    fn into_part(v: Vec<u16>) -> (p: OwnedPart) { OwnedPart::U16(v) }
}

impl Code for u32 {
    open spec fn cap() -> int { 4294967295 }

    open spec fn val(c: u32) -> int { c as int }

    open spec fn part_of(s: Seq<u32>) -> PartView { PartView::U32(s) }

    proof fn lemma_code(c: u32) {}

    proof fn lemma_part_of(s: Seq<u32>) {}

    fn from_u64(x: u64) -> (c: u32) { x as u32 }

    fn cap_u64() -> (r: u64) { 4294967295 }

    fn zero() -> (c: u32) { 0 }

    fn into_part(v: Vec<u32>) -> (p: OwnedPart) { OwnedPart::U32(v) }
}

} // verus!
