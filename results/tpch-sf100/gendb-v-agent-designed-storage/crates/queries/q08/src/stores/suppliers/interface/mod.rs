//! Storage `suppliers`: the partsupp, supplier, nation and region tables, each in canonical row order (stored row `j` is source row `j`), column by column (`common::colfmt`).
//!
//! Every table has the same frame: part `*_LAYOUT` (U64 `[rows, block rows]`), part `*_GROUPS` (U64 uniform group
//! starts: group `g` holds the stored rows `g * block .. min((g + 1) * block, rows)`; `block` is `BLOCK_ROWS`, or 1
//! when some block's values exceed a code width), then per column:
//! - bigint / numeric / date: a code part (U8, U16 or U32, one per row) and an I64 base part (one per group); the
//!   value of stored row `j` in group `g` is `base[g] + code[j]` (`colfmt::for_at`), numerics as coefficients of
//!   scale 2, dates as days since 2000-01-01; a zone part (I64, one per group) bounds a group's values from above
//!   (the base bounds them from below);
//! - low-cardinality text: a dictionary (U64 offsets + U8 bytes, entries strictly increasing bytewise, so
//!   distinct) and FOR codes (U64 bases) of each row's entry index;
//! - other text: U64 offsets (`rows + 1`, from 0) and U8 bytes.
//! A clustered table also has a row map column (`*_PERM_CODES` U32 + `*_PERM_BASE` U64): stored row `j` is canonical
//! row `for_at(.., j)`, a bijection (`colfmt::perm_col_at`), and its column predicates hold over
//! `colfmt::perm_rows` (`lemma_stored_rows_multiset`: the same multiset of rows as the relation). Other tables keep
//! canonical order: stored row `j` is canonical row `j`.
//! A table's parts sit at `<TABLE>_FIRST + <PREFIX>_<PART>`; `represents` states `<table>_ok` over that range.
//! Values are exact: nothing is rounded, clipped or derived.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::{Row, Val};
pub mod common;
use common::colfmt::*;
use common::keyidx::{keyidx_ok, fidx};

verus! {

/// Rows per group of every table (one-row groups are the fallback when a block's values exceed a code width).
pub const BLOCK_ROWS: usize = 65536;

/// The frame of a table of `n` rows: `tp[0]` is U64 `[n, block rows]`, `tp[1]` the uniform groups of that block size.
pub open spec fn table_layout_ok(tp: Seq<PartView>, n: int) -> bool {
    &&& tp.len() >= 2
    &&& tp[0] is U64
    &&& u64s(tp[0]).len() == 2
    &&& u64s(tp[0])[0] == n
    &&& groups_part_ok(tp[1], n, u64s(tp[0])[1] as int)
}


// ---------------------------------------------------------------------------------------------- partsupp

/// First part of table partsupp in this storage.
pub const PARTSUPP_FIRST: usize = 0;
/// Number of parts of table partsupp.
pub const PS_PARTS: usize = 13;
/// partsupp: U64 [rows, block rows].
pub const PS_LAYOUT: usize = 0;
/// partsupp: U64 group starts.
pub const PS_GROUPS: usize = 1;
/// partsupp: U32 codes of ps_partkey.
pub const PS_PARTKEY_CODES: usize = 2;
/// partsupp: I64 group bases of ps_partkey.
pub const PS_PARTKEY_BASE: usize = 3;
/// partsupp: U32 codes of ps_suppkey.
pub const PS_SUPPKEY_CODES: usize = 4;
/// partsupp: I64 group bases of ps_suppkey.
pub const PS_SUPPKEY_BASE: usize = 5;
/// partsupp: U16 codes of ps_availqty.
pub const PS_AVAILQTY_CODES: usize = 6;
/// partsupp: I64 group bases of ps_availqty.
pub const PS_AVAILQTY_BASE: usize = 7;
/// partsupp: U32 codes of ps_supplycost.
pub const PS_SUPPLYCOST_CODES: usize = 8;
/// partsupp: I64 group bases of ps_supplycost.
pub const PS_SUPPLYCOST_BASE: usize = 9;
/// partsupp: U64 offsets of ps_comment.
pub const PS_COMMENT_OFFS: usize = 10;
/// partsupp: U8 bytes of ps_comment.
pub const PS_COMMENT_BYTES: usize = 11;
/// partsupp: U64 [key index kind: 0 none, 1 stored rows sorted by key, 2 key index] of ps_partkey.
pub const PS_KEYIDX_KIND: usize = 12;

/// Table partsupp (5 columns, canonical row order) in its parts `tp`:
/// column 0 ps_partkey: bigint, FOR u32 codes + I64 bases.
/// column 1 ps_suppkey: bigint, FOR u32 codes + I64 bases.
/// column 2 ps_availqty: bigint, FOR u16 codes + I64 bases.
/// column 3 ps_supplycost: numeric(15,2) coefficient, FOR u32 codes + I64 bases.
/// column 4 ps_comment: text, U64 offsets + U8 bytes.
pub open spec fn partsupp_ok(tp: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& tp.len() == PS_PARTS
    &&& table_layout_ok(tp, rel.len() as int)
    &&& rows_width(rel, 5)
    &&& tp[PS_PARTKEY_CODES as int] is U32
    &&& int_col_at(tp, PS_GROUPS as int, PS_PARTKEY_CODES as int, PS_PARTKEY_BASE as int, rel, 0)
    &&& tp[PS_SUPPKEY_CODES as int] is U32
    &&& int_col_at(tp, PS_GROUPS as int, PS_SUPPKEY_CODES as int, PS_SUPPKEY_BASE as int, rel, 1)
    &&& tp[PS_AVAILQTY_CODES as int] is U16
    &&& int_col_at(tp, PS_GROUPS as int, PS_AVAILQTY_CODES as int, PS_AVAILQTY_BASE as int, rel, 2)
    &&& tp[PS_SUPPLYCOST_CODES as int] is U32
    &&& num_col_at(tp, PS_GROUPS as int, PS_SUPPLYCOST_CODES as int, PS_SUPPLYCOST_BASE as int, rel, 3, 2)
    &&& text_col_at(tp, PS_COMMENT_OFFS as int, PS_COMMENT_BYTES as int, rel, 4)
    &&& tp[PS_KEYIDX_KIND as int] is U64 && u64s(tp[PS_KEYIDX_KIND as int]).len() == 1
    &&& keyidx_ok(u32s(tp[PS_PARTKEY_CODES as int]), i64s(tp[PS_PARTKEY_BASE as int]), Seq::<u32>::empty(), Seq::<u64>::empty(), u64s(tp[PS_LAYOUT as int])[1] as int, u64s(tp[PS_KEYIDX_KIND as int])[0], rel.len() as int)
}

/// The parts of table partsupp determine its rows.
pub proof fn lemma_partsupp_determines(tp: Seq<PartView>, a: Seq<Row>, b: Seq<Row>)
    requires partsupp_ok(tp, a), partsupp_ok(tp, b),
    ensures a == b,
{
    assert forall|j: int, c: int| 0 <= j < a.len() && 0 <= c < 5 implies #[trigger] a[j][c] == b[j][c] by {
        if c == 0 {
            assert(a[j][0] == b[j][0]);
        } else if c == 1 {
            assert(a[j][1] == b[j][1]);
        } else if c == 2 {
            assert(a[j][2] == b[j][2]);
        } else if c == 3 {
            assert(a[j][3] == b[j][3]);
        } else if c == 4 {
            assert(a[j][4] == b[j][4]);
        }
    }
    lemma_rows_eq(a, b, 5);
}

// ---------------------------------------------------------------------------------------------- supplier

/// First part of table supplier in this storage.
pub const SUPPLIER_FIRST: usize = 13;
/// Number of parts of table supplier.
pub const SU_PARTS: usize = 17;
/// supplier: U64 [rows, block rows].
pub const SU_LAYOUT: usize = 0;
/// supplier: U64 group starts.
pub const SU_GROUPS: usize = 1;
/// supplier: U32 codes of s_suppkey.
pub const SU_SUPPKEY_CODES: usize = 2;
/// supplier: I64 group bases of s_suppkey.
pub const SU_SUPPKEY_BASE: usize = 3;
/// supplier: U64 offsets of s_name.
pub const SU_NAME_OFFS: usize = 4;
/// supplier: U8 bytes of s_name.
pub const SU_NAME_BYTES: usize = 5;
/// supplier: U64 offsets of s_address.
pub const SU_ADDRESS_OFFS: usize = 6;
/// supplier: U8 bytes of s_address.
pub const SU_ADDRESS_BYTES: usize = 7;
/// supplier: U8 codes of s_nationkey.
pub const SU_NATIONKEY_CODES: usize = 8;
/// supplier: I64 group bases of s_nationkey.
pub const SU_NATIONKEY_BASE: usize = 9;
/// supplier: U64 offsets of s_phone.
pub const SU_PHONE_OFFS: usize = 10;
/// supplier: U8 bytes of s_phone.
pub const SU_PHONE_BYTES: usize = 11;
/// supplier: U32 codes of s_acctbal.
pub const SU_ACCTBAL_CODES: usize = 12;
/// supplier: I64 group bases of s_acctbal.
pub const SU_ACCTBAL_BASE: usize = 13;
/// supplier: U64 offsets of s_comment.
pub const SU_COMMENT_OFFS: usize = 14;
/// supplier: U8 bytes of s_comment.
pub const SU_COMMENT_BYTES: usize = 15;
/// supplier: U64 [key index kind: 0 none, 1 stored rows sorted by key, 2 key index] of s_suppkey.
pub const SU_KEYIDX_KIND: usize = 16;

/// Table supplier (7 columns, canonical row order) in its parts `tp`:
/// column 0 s_suppkey: bigint, FOR u32 codes + I64 bases.
/// column 1 s_name: text, U64 offsets + U8 bytes.
/// column 2 s_address: text, U64 offsets + U8 bytes.
/// column 3 s_nationkey: bigint, FOR u8 codes + I64 bases.
/// column 4 s_phone: text, U64 offsets + U8 bytes.
/// column 5 s_acctbal: numeric(15,2) coefficient, FOR u32 codes + I64 bases.
/// column 6 s_comment: text, U64 offsets + U8 bytes.
pub open spec fn supplier_ok(tp: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& tp.len() == SU_PARTS
    &&& table_layout_ok(tp, rel.len() as int)
    &&& rows_width(rel, 7)
    &&& tp[SU_SUPPKEY_CODES as int] is U32
    &&& int_col_at(tp, SU_GROUPS as int, SU_SUPPKEY_CODES as int, SU_SUPPKEY_BASE as int, rel, 0)
    &&& text_col_at(tp, SU_NAME_OFFS as int, SU_NAME_BYTES as int, rel, 1)
    &&& text_col_at(tp, SU_ADDRESS_OFFS as int, SU_ADDRESS_BYTES as int, rel, 2)
    &&& tp[SU_NATIONKEY_CODES as int] is U8
    &&& int_col_at(tp, SU_GROUPS as int, SU_NATIONKEY_CODES as int, SU_NATIONKEY_BASE as int, rel, 3)
    &&& text_col_at(tp, SU_PHONE_OFFS as int, SU_PHONE_BYTES as int, rel, 4)
    &&& tp[SU_ACCTBAL_CODES as int] is U32
    &&& num_col_at(tp, SU_GROUPS as int, SU_ACCTBAL_CODES as int, SU_ACCTBAL_BASE as int, rel, 5, 2)
    &&& text_col_at(tp, SU_COMMENT_OFFS as int, SU_COMMENT_BYTES as int, rel, 6)
    &&& tp[SU_KEYIDX_KIND as int] is U64 && u64s(tp[SU_KEYIDX_KIND as int]).len() == 1
    &&& keyidx_ok(u32s(tp[SU_SUPPKEY_CODES as int]), i64s(tp[SU_SUPPKEY_BASE as int]), Seq::<u32>::empty(), Seq::<u64>::empty(), u64s(tp[SU_LAYOUT as int])[1] as int, u64s(tp[SU_KEYIDX_KIND as int])[0], rel.len() as int)
}

/// The parts of table supplier determine its rows.
pub proof fn lemma_supplier_determines(tp: Seq<PartView>, a: Seq<Row>, b: Seq<Row>)
    requires supplier_ok(tp, a), supplier_ok(tp, b),
    ensures a == b,
{
    assert forall|j: int, c: int| 0 <= j < a.len() && 0 <= c < 7 implies #[trigger] a[j][c] == b[j][c] by {
        if c == 0 {
            assert(a[j][0] == b[j][0]);
        } else if c == 1 {
            assert(a[j][1] == b[j][1]);
        } else if c == 2 {
            assert(a[j][2] == b[j][2]);
        } else if c == 3 {
            assert(a[j][3] == b[j][3]);
        } else if c == 4 {
            assert(a[j][4] == b[j][4]);
        } else if c == 5 {
            assert(a[j][5] == b[j][5]);
        } else if c == 6 {
            assert(a[j][6] == b[j][6]);
        }
    }
    lemma_rows_eq(a, b, 7);
}

// ---------------------------------------------------------------------------------------------- nation

/// First part of table nation in this storage.
pub const NATION_FIRST: usize = 30;
/// Number of parts of table nation.
pub const NA_PARTS: usize = 10;
/// nation: U64 [rows, block rows].
pub const NA_LAYOUT: usize = 0;
/// nation: U64 group starts.
pub const NA_GROUPS: usize = 1;
/// nation: U8 codes of n_nationkey.
pub const NA_NATIONKEY_CODES: usize = 2;
/// nation: I64 group bases of n_nationkey.
pub const NA_NATIONKEY_BASE: usize = 3;
/// nation: U64 offsets of n_name.
pub const NA_NAME_OFFS: usize = 4;
/// nation: U8 bytes of n_name.
pub const NA_NAME_BYTES: usize = 5;
/// nation: U8 codes of n_regionkey.
pub const NA_REGIONKEY_CODES: usize = 6;
/// nation: I64 group bases of n_regionkey.
pub const NA_REGIONKEY_BASE: usize = 7;
/// nation: U64 offsets of n_comment.
pub const NA_COMMENT_OFFS: usize = 8;
/// nation: U8 bytes of n_comment.
pub const NA_COMMENT_BYTES: usize = 9;

/// Table nation (4 columns, canonical row order) in its parts `tp`:
/// column 0 n_nationkey: bigint, FOR u8 codes + I64 bases.
/// column 1 n_name: text, U64 offsets + U8 bytes.
/// column 2 n_regionkey: bigint, FOR u8 codes + I64 bases.
/// column 3 n_comment: text, U64 offsets + U8 bytes.
pub open spec fn nation_ok(tp: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& tp.len() == NA_PARTS
    &&& table_layout_ok(tp, rel.len() as int)
    &&& rows_width(rel, 4)
    &&& tp[NA_NATIONKEY_CODES as int] is U8
    &&& int_col_at(tp, NA_GROUPS as int, NA_NATIONKEY_CODES as int, NA_NATIONKEY_BASE as int, rel, 0)
    &&& text_col_at(tp, NA_NAME_OFFS as int, NA_NAME_BYTES as int, rel, 1)
    &&& tp[NA_REGIONKEY_CODES as int] is U8
    &&& int_col_at(tp, NA_GROUPS as int, NA_REGIONKEY_CODES as int, NA_REGIONKEY_BASE as int, rel, 2)
    &&& text_col_at(tp, NA_COMMENT_OFFS as int, NA_COMMENT_BYTES as int, rel, 3)
}

/// The parts of table nation determine its rows.
pub proof fn lemma_nation_determines(tp: Seq<PartView>, a: Seq<Row>, b: Seq<Row>)
    requires nation_ok(tp, a), nation_ok(tp, b),
    ensures a == b,
{
    assert forall|j: int, c: int| 0 <= j < a.len() && 0 <= c < 4 implies #[trigger] a[j][c] == b[j][c] by {
        if c == 0 {
            assert(a[j][0] == b[j][0]);
        } else if c == 1 {
            assert(a[j][1] == b[j][1]);
        } else if c == 2 {
            assert(a[j][2] == b[j][2]);
        } else if c == 3 {
            assert(a[j][3] == b[j][3]);
        }
    }
    lemma_rows_eq(a, b, 4);
}

// ---------------------------------------------------------------------------------------------- region

/// First part of table region in this storage.
pub const REGION_FIRST: usize = 40;
/// Number of parts of table region.
pub const RE_PARTS: usize = 8;
/// region: U64 [rows, block rows].
pub const RE_LAYOUT: usize = 0;
/// region: U64 group starts.
pub const RE_GROUPS: usize = 1;
/// region: U8 codes of r_regionkey.
pub const RE_REGIONKEY_CODES: usize = 2;
/// region: I64 group bases of r_regionkey.
pub const RE_REGIONKEY_BASE: usize = 3;
/// region: U64 offsets of r_name.
pub const RE_NAME_OFFS: usize = 4;
/// region: U8 bytes of r_name.
pub const RE_NAME_BYTES: usize = 5;
/// region: U64 offsets of r_comment.
pub const RE_COMMENT_OFFS: usize = 6;
/// region: U8 bytes of r_comment.
pub const RE_COMMENT_BYTES: usize = 7;

/// Table region (3 columns, canonical row order) in its parts `tp`:
/// column 0 r_regionkey: bigint, FOR u8 codes + I64 bases.
/// column 1 r_name: text, U64 offsets + U8 bytes.
/// column 2 r_comment: text, U64 offsets + U8 bytes.
pub open spec fn region_ok(tp: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& tp.len() == RE_PARTS
    &&& table_layout_ok(tp, rel.len() as int)
    &&& rows_width(rel, 3)
    &&& tp[RE_REGIONKEY_CODES as int] is U8
    &&& int_col_at(tp, RE_GROUPS as int, RE_REGIONKEY_CODES as int, RE_REGIONKEY_BASE as int, rel, 0)
    &&& text_col_at(tp, RE_NAME_OFFS as int, RE_NAME_BYTES as int, rel, 1)
    &&& text_col_at(tp, RE_COMMENT_OFFS as int, RE_COMMENT_BYTES as int, rel, 2)
}

/// The parts of table region determine its rows.
pub proof fn lemma_region_determines(tp: Seq<PartView>, a: Seq<Row>, b: Seq<Row>)
    requires region_ok(tp, a), region_ok(tp, b),
    ensures a == b,
{
    assert forall|j: int, c: int| 0 <= j < a.len() && 0 <= c < 3 implies #[trigger] a[j][c] == b[j][c] by {
        if c == 0 {
            assert(a[j][0] == b[j][0]);
        } else if c == 1 {
            assert(a[j][1] == b[j][1]);
        } else if c == 2 {
            assert(a[j][2] == b[j][2]);
        }
    }
    lemma_rows_eq(a, b, 3);
}

/// Number of parts of storage suppliers.
pub const SUPPLIERS_PARTS: usize = 48;

/// The parts hold every table of the storage, each over its own part range (`<table>_ok`).
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& parts.len() == SUPPLIERS_PARTS
    &&& rels.len() == 4
    &&& partsupp_ok(parts.subrange(PARTSUPP_FIRST as int, (PARTSUPP_FIRST + PS_PARTS) as int), rels[0])
    &&& supplier_ok(parts.subrange(SUPPLIER_FIRST as int, (SUPPLIER_FIRST + SU_PARTS) as int), rels[1])
    &&& nation_ok(parts.subrange(NATION_FIRST as int, (NATION_FIRST + NA_PARTS) as int), rels[2])
    &&& region_ok(parts.subrange(REGION_FIRST as int, (REGION_FIRST + RE_PARTS) as int), rels[3])
}

/// The parts determine the relations they represent (complete lossless storage).
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    lemma_partsupp_determines(parts.subrange(PARTSUPP_FIRST as int, (PARTSUPP_FIRST + PS_PARTS) as int), a[0], b[0]);
    lemma_supplier_determines(parts.subrange(SUPPLIER_FIRST as int, (SUPPLIER_FIRST + SU_PARTS) as int), a[1], b[1]);
    lemma_nation_determines(parts.subrange(NATION_FIRST as int, (NATION_FIRST + NA_PARTS) as int), a[2], b[2]);
    lemma_region_determines(parts.subrange(REGION_FIRST as int, (REGION_FIRST + RE_PARTS) as int), a[3], b[3]);
    assert(a =~= b);
}

} // verus!
