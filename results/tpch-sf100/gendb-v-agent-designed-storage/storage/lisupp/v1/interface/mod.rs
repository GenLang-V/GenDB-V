//! Storage `lisupp`: storage `facts` extended by a key index of lineitem by `l_suppkey`.
//!
//! Parts `0 .. 75` are the parts of `facts`, inherited unchanged (lineitem at `0 .. 48`, orders and the clustering
//! flag after it). This storage states only what it needs of them: the lineitem frame (`LI_LAYOUT`, `LI_GROUPS`),
//! the row map column (stored row `j` is canonical row `for_at(.., j)`, a bijection) and four frame-of-reference
//! columns over the stored rows (`li_cols_ok`): column 0 `l_suppkey` (U32 codes, I64 bases), column 1
//! `l_extendedprice` and column 2 `l_discount` (numeric(15, 2) coefficients, U32 / U8 codes, I64 bases) and
//! column 3 `l_shipdate` (days since 2000-01-01, U16 codes, I64 bases, I64 zone maxima per group).
//!
//! Parts `75 .. 78` are the new key index (`common::keyidx` format) over the `l_suppkey` column of the stored rows:
//! `SX_CODES` (U32) and `SX_BASES` (U64, one per lineitem block) list the stored rows in key order (index position
//! `r` holds stored row `fidx(.., r)`), `SX_KIND` is `[2]` when that list is a bijection sorted by key, else `[0]`
//! (no order known). The builder checks both properties at run time before it sets kind 2.
//!
//! The stored relation is lineitem projected on `[l_suppkey, l_extendedprice, l_discount, l_shipdate]` in canonical
//! row order (`declaration::stored_relations`). Values are exact: nothing is rounded, clipped or derived.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::{Row, Val};
pub mod common;
use common::colfmt::*;
use common::keyidx::keyidx_ok;

verus! {

/// Rows per group of the lineitem layout of `facts` (one-row groups are its fallback).
pub const BLOCK_ROWS: usize = 65536;

/// The frame of a table of `n` rows: `tp[0]` is U64 `[n, block rows]`, `tp[1]` the uniform groups of that block size.
pub open spec fn table_layout_ok(tp: Seq<PartView>, n: int) -> bool {
    &&& tp.len() >= 2
    &&& tp[0] is U64
    &&& u64s(tp[0]).len() == 2
    &&& u64s(tp[0])[0] == n
    &&& groups_part_ok(tp[1], n, u64s(tp[0])[1] as int)
}

// ---------------------------------------------------------------------------------------------- inherited lineitem

/// Number of lineitem parts of `facts` (the first parts of this storage).
pub const LI_PARTS: usize = 48;
/// lineitem: U64 [rows, block rows].
pub const LI_LAYOUT: usize = 0;
/// lineitem: U64 group starts.
pub const LI_GROUPS: usize = 1;
/// lineitem: U32 codes of the canonical row of each stored row.
pub const LI_PERM_CODES: usize = 2;
/// lineitem: U64 group bases of canonical rows.
pub const LI_PERM_BASE: usize = 3;
/// lineitem: U32 codes of l_suppkey.
pub const LI_SUPPKEY_CODES: usize = 8;
/// lineitem: I64 group bases of l_suppkey.
pub const LI_SUPPKEY_BASE: usize = 9;
/// lineitem: U32 codes of l_extendedprice.
pub const LI_EXTENDEDPRICE_CODES: usize = 14;
/// lineitem: I64 group bases of l_extendedprice.
pub const LI_EXTENDEDPRICE_BASE: usize = 15;
/// lineitem: U8 codes of l_discount.
pub const LI_DISCOUNT_CODES: usize = 16;
/// lineitem: I64 group bases of l_discount.
pub const LI_DISCOUNT_BASE: usize = 17;
/// lineitem: U16 codes of l_shipdate.
pub const LI_SHIPDATE_CODES: usize = 28;
/// lineitem: I64 group bases of l_shipdate.
pub const LI_SHIPDATE_BASE: usize = 29;
/// lineitem: I64 zone maxima of l_shipdate.
pub const LI_SHIPDATE_ZMAX: usize = 30;

/// Number of parts inherited from `facts`.
pub const INHERITED_PARTS: usize = 75;

/// The stored rows of lineitem: stored row `j` is canonical row `for_at(.., j)` of its row map column.
pub open spec fn li_rows(tp: Seq<PartView>, rel: Seq<Row>) -> Seq<Row> {
    perm_rows(tp, LI_GROUPS as int, LI_PERM_CODES as int, LI_PERM_BASE as int, rel)
}

/// The row map of lineitem (stored row -> canonical row).
pub open spec fn li_map(tp: Seq<PartView>, n: int) -> Seq<int> {
    for_map(gs_at(tp, LI_GROUPS as int), tp[LI_PERM_BASE as int], tp[LI_PERM_CODES as int], n)
}

/// The four stored columns of lineitem over its stored rows `rows`: 0 l_suppkey, 1 l_extendedprice, 2 l_discount,
/// 3 l_shipdate (with its zone maxima).
pub open spec fn li_cols_ok(tp: Seq<PartView>, rows: Seq<Row>) -> bool {
    &&& tp[LI_SUPPKEY_CODES as int] is U32
    &&& int_col_at(tp, LI_GROUPS as int, LI_SUPPKEY_CODES as int, LI_SUPPKEY_BASE as int, rows, 0)
    &&& tp[LI_EXTENDEDPRICE_CODES as int] is U32
    &&& num_col_at(tp, LI_GROUPS as int, LI_EXTENDEDPRICE_CODES as int, LI_EXTENDEDPRICE_BASE as int, rows, 1, 2)
    &&& tp[LI_DISCOUNT_CODES as int] is U8
    &&& num_col_at(tp, LI_GROUPS as int, LI_DISCOUNT_CODES as int, LI_DISCOUNT_BASE as int, rows, 2, 2)
    &&& tp[LI_SHIPDATE_CODES as int] is U16
    &&& date_col_at(tp, LI_GROUPS as int, LI_SHIPDATE_CODES as int, LI_SHIPDATE_BASE as int, rows, 3)
    &&& zone_at(tp, LI_GROUPS as int, LI_SHIPDATE_CODES as int, LI_SHIPDATE_BASE as int, LI_SHIPDATE_ZMAX as int)
}

/// Table lineitem (4 stored columns, clustered row order) in the inherited parts `tp`.
pub open spec fn li_ok(tp: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& tp.len() == LI_PARTS
    &&& table_layout_ok(tp, rel.len() as int)
    &&& rows_width(rel, 4)
    &&& tp[LI_PERM_CODES as int] is U32
    &&& perm_col_at(tp, LI_GROUPS as int, LI_PERM_CODES as int, LI_PERM_BASE as int, rel.len() as int)
    &&& li_cols_ok(tp, li_rows(tp, rel))
}

// ---------------------------------------------------------------------------------------------- the key index

/// Index part: U32 codes of the stored rows in l_suppkey order.
pub const SX_CODES: usize = 75;
/// Index part: U64 bases of those codes (one per lineitem block).
pub const SX_BASES: usize = 76;
/// Index part: U64 [kind] (0 none, 2 index).
pub const SX_KIND: usize = 77;

/// Number of parts of storage lisupp.
pub const LISUPP_PARTS: usize = 78;

/// The key index of the `n` stored lineitem rows by l_suppkey (`common::keyidx::keyidx_ok`, kind 0 or 2).
pub open spec fn index_ok(parts: Seq<PartView>, n: int) -> bool {
    &&& parts[SX_CODES as int] is U32
    &&& parts[SX_BASES as int] is U64
    &&& parts[SX_KIND as int] is U64
    &&& u64s(parts[SX_KIND as int]).len() == 1
    &&& keyidx_ok(u32s(parts[LI_SUPPKEY_CODES as int]), i64s(parts[LI_SUPPKEY_BASE as int]), u32s(parts[SX_CODES as int]),
            u64s(parts[SX_BASES as int]), u64s(parts[LI_LAYOUT as int])[1] as int, u64s(parts[SX_KIND as int])[0], n)
}

/// The parts hold lineitem's four stored columns (inherited parts) and the key index by l_suppkey.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& parts.len() == LISUPP_PARTS
    &&& rels.len() == 1
    &&& li_ok(parts.subrange(0, LI_PARTS as int), rels[0])
    &&& index_ok(parts, rels[0].len() as int)
}

/// The parts of table lineitem determine its rows.
pub proof fn lemma_li_determines(tp: Seq<PartView>, a: Seq<Row>, b: Seq<Row>)
    requires li_ok(tp, a), li_ok(tp, b),
    ensures a == b,
{
    let n = a.len() as int;
    let m = li_map(tp, n);
    assert(u64s(tp[0])[0] == n);
    assert(b.len() == n);
    assert forall|j: int, c: int| 0 <= j < n && 0 <= c < 4 implies #[trigger] stored_rows(a, m)[j][c] == stored_rows(b, m)[j][c] by {
        assert(li_rows(tp, a) == stored_rows(a, m));
        assert(li_rows(tp, b) == stored_rows(b, m));
        if c == 0 {
            assert(li_rows(tp, a)[j][0] == li_rows(tp, b)[j][0]);
        } else if c == 1 {
            assert(li_rows(tp, a)[j][1] == li_rows(tp, b)[j][1]);
        } else if c == 2 {
            assert(li_rows(tp, a)[j][2] == li_rows(tp, b)[j][2]);
        } else {
            assert(li_rows(tp, a)[j][3] == li_rows(tp, b)[j][3]);
        }
    }
    lemma_stored_rows_determine(a, b, m, n, 4);
}

/// The parts determine the relations they represent (complete lossless storage).
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    lemma_li_determines(parts.subrange(0, LI_PARTS as int), a[0], b[0]);
    assert(a =~= b);
}

} // verus!
