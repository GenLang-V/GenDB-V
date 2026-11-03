//! Storage `factspk`: storage `facts` (lineitem, orders) with its 75 parts unchanged, extended by a directory over
//! facts' l_partkey key index (a permutation of the stored lineitem rows sorted by l_partkey):
//! - part `DIR_BASE` (I64 `[kb]`): the key of directory entry 0;
//! - part `DIR_POS` (U32 `dir`, at least one entry): `dir[i]` is the first key-index position whose l_partkey is at
//!   least `kb + i`, or the row count when there is none (`dir_entry_ok`).
//! Because the key index is sorted, the rows of key `kb + i` are exactly the index positions `[dir[i], dir[i + 1])`.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::Row;
use crate::stores::facts::interface as fi;
use fi::common::colfmt::{u32s, u64s, i64s};
use fi::common::keyidx::{fkey, irow};

verus! {

/// Parts of storage facts, kept unchanged in front.
pub const FACTS_PARTS: usize = 75;
/// I64 `[kb]`: the key of directory entry 0.
pub const DIR_BASE: usize = 75;
/// U32 `dir`: the directory.
pub const DIR_POS: usize = 76;
/// Number of parts of storage factspk.
pub const FACTSPK_PARTS: usize = 77;

/// Rows of lineitem (its layout part).
pub open spec fn li_rows(parts: Seq<PartView>) -> int {
    u64s(parts[fi::LI_LAYOUT as int])[0] as int
}

/// Rows per group of lineitem (its layout part).
pub open spec fn li_bsize(parts: Seq<PartView>) -> int {
    u64s(parts[fi::LI_LAYOUT as int])[1] as int
}

/// l_partkey of the stored lineitem row at position `r` of facts' l_partkey key index.
pub open spec fn key_at(parts: Seq<PartView>, r: int) -> int {
    let bs = li_bsize(parts);
    fkey(u32s(parts[fi::LI_PARTKEY_CODES as int]), i64s(parts[fi::LI_PARTKEY_BASE as int]), bs,
        irow(u64s(parts[fi::LI_KEYIDX_KIND as int])[0], u32s(parts[fi::LI_KEYIDX_CODES as int]),
            u64s(parts[fi::LI_KEYIDX_BASE as int]), bs, r))
}

/// The directory.
pub open spec fn dir_of(parts: Seq<PartView>) -> Seq<u32> {
    u32s(parts[DIR_POS as int])
}

/// The key of directory entry 0.
pub open spec fn kb_of(parts: Seq<PartView>) -> int {
    i64s(parts[DIR_BASE as int])[0] as int
}

/// Entry `i` is the first index position whose key is at least `kb + i` (the row count when there is none).
pub open spec fn dir_entry_ok(parts: Seq<PartView>, i: int) -> bool {
    let d = dir_of(parts)[i] as int;
    &&& d <= li_rows(parts)
    &&& forall|r: int| 0 <= r < d ==> #[trigger] key_at(parts, r) < kb_of(parts) + i
    &&& d < li_rows(parts) ==> key_at(parts, d) >= kb_of(parts) + i
}

/// The directory parts.
pub open spec fn dir_ok(parts: Seq<PartView>) -> bool {
    &&& parts[DIR_BASE as int] is I64 && i64s(parts[DIR_BASE as int]).len() == 1
    &&& parts[DIR_POS as int] is U32 && dir_of(parts).len() >= 1
    &&& forall|i: int| 0 <= i < dir_of(parts).len() ==> #[trigger] dir_entry_ok(parts, i)
}

/// The facts parts hold lineitem and orders (facts' `represents`), the last two parts the directory.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& parts.len() == FACTSPK_PARTS
    &&& fi::represents(parts.subrange(0, FACTS_PARTS as int), rels)
    &&& dir_ok(parts)
}

/// The parts determine the relations they represent.
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    fi::lemma_represents_determines(parts.subrange(0, FACTS_PARTS as int), a, b);
}

} // verus!
