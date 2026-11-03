//! Storage `custpart`: the customer and part tables, each in canonical row order (stored row `j` is source row `j`), column by column (`common::colfmt`).
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


// ---------------------------------------------------------------------------------------------- customer

/// First part of table customer in this storage.
pub const CUSTOMER_FIRST: usize = 0;
/// Number of parts of table customer.
pub const CU_PARTS: usize = 21;
/// customer: U64 [rows, block rows].
pub const CU_LAYOUT: usize = 0;
/// customer: U64 group starts.
pub const CU_GROUPS: usize = 1;
/// customer: U32 codes of c_custkey.
pub const CU_CUSTKEY_CODES: usize = 2;
/// customer: I64 group bases of c_custkey.
pub const CU_CUSTKEY_BASE: usize = 3;
/// customer: U64 offsets of c_name.
pub const CU_NAME_OFFS: usize = 4;
/// customer: U8 bytes of c_name.
pub const CU_NAME_BYTES: usize = 5;
/// customer: U64 offsets of c_address.
pub const CU_ADDRESS_OFFS: usize = 6;
/// customer: U8 bytes of c_address.
pub const CU_ADDRESS_BYTES: usize = 7;
/// customer: U8 codes of c_nationkey.
pub const CU_NATIONKEY_CODES: usize = 8;
/// customer: I64 group bases of c_nationkey.
pub const CU_NATIONKEY_BASE: usize = 9;
/// customer: U64 offsets of c_phone.
pub const CU_PHONE_OFFS: usize = 10;
/// customer: U8 bytes of c_phone.
pub const CU_PHONE_BYTES: usize = 11;
/// customer: U32 codes of c_acctbal.
pub const CU_ACCTBAL_CODES: usize = 12;
/// customer: I64 group bases of c_acctbal.
pub const CU_ACCTBAL_BASE: usize = 13;
/// customer: U8 codes of dictionary indices of c_mktsegment.
pub const CU_MKTSEGMENT_CODES: usize = 14;
/// customer: U64 group bases of dictionary indices of c_mktsegment.
pub const CU_MKTSEGMENT_BASE: usize = 15;
/// customer: U64 dictionary offsets of c_mktsegment.
pub const CU_MKTSEGMENT_DICT_OFFS: usize = 16;
/// customer: U8 dictionary bytes of c_mktsegment.
pub const CU_MKTSEGMENT_DICT_BYTES: usize = 17;
/// customer: U64 offsets of c_comment.
pub const CU_COMMENT_OFFS: usize = 18;
/// customer: U8 bytes of c_comment.
pub const CU_COMMENT_BYTES: usize = 19;
/// customer: U64 [key index kind: 0 none, 1 stored rows sorted by key, 2 key index] of c_custkey.
pub const CU_KEYIDX_KIND: usize = 20;

/// Table customer (8 columns, canonical row order) in its parts `tp`:
/// column 0 c_custkey: bigint, FOR u32 codes + I64 bases.
/// column 1 c_name: text, U64 offsets + U8 bytes.
/// column 2 c_address: text, U64 offsets + U8 bytes.
/// column 3 c_nationkey: bigint, FOR u8 codes + I64 bases.
/// column 4 c_phone: text, U64 offsets + U8 bytes.
/// column 5 c_acctbal: numeric(15,2) coefficient, FOR u32 codes + I64 bases.
/// column 6 c_mktsegment: text, sorted dictionary; FOR u8 codes of entry indices + U64 bases.
/// column 7 c_comment: text, U64 offsets + U8 bytes.
pub open spec fn customer_ok(tp: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& tp.len() == CU_PARTS
    &&& table_layout_ok(tp, rel.len() as int)
    &&& rows_width(rel, 8)
    &&& tp[CU_CUSTKEY_CODES as int] is U32
    &&& int_col_at(tp, CU_GROUPS as int, CU_CUSTKEY_CODES as int, CU_CUSTKEY_BASE as int, rel, 0)
    &&& text_col_at(tp, CU_NAME_OFFS as int, CU_NAME_BYTES as int, rel, 1)
    &&& text_col_at(tp, CU_ADDRESS_OFFS as int, CU_ADDRESS_BYTES as int, rel, 2)
    &&& tp[CU_NATIONKEY_CODES as int] is U8
    &&& int_col_at(tp, CU_GROUPS as int, CU_NATIONKEY_CODES as int, CU_NATIONKEY_BASE as int, rel, 3)
    &&& text_col_at(tp, CU_PHONE_OFFS as int, CU_PHONE_BYTES as int, rel, 4)
    &&& tp[CU_ACCTBAL_CODES as int] is U32
    &&& num_col_at(tp, CU_GROUPS as int, CU_ACCTBAL_CODES as int, CU_ACCTBAL_BASE as int, rel, 5, 2)
    &&& tp[CU_MKTSEGMENT_CODES as int] is U8
    &&& dict_col_at(tp, CU_GROUPS as int, CU_MKTSEGMENT_CODES as int, CU_MKTSEGMENT_BASE as int, CU_MKTSEGMENT_DICT_OFFS as int, CU_MKTSEGMENT_DICT_BYTES as int, rel, 6)
    &&& text_col_at(tp, CU_COMMENT_OFFS as int, CU_COMMENT_BYTES as int, rel, 7)
    &&& tp[CU_KEYIDX_KIND as int] is U64 && u64s(tp[CU_KEYIDX_KIND as int]).len() == 1
    &&& keyidx_ok(u32s(tp[CU_CUSTKEY_CODES as int]), i64s(tp[CU_CUSTKEY_BASE as int]), Seq::<u32>::empty(), Seq::<u64>::empty(), u64s(tp[CU_LAYOUT as int])[1] as int, u64s(tp[CU_KEYIDX_KIND as int])[0], rel.len() as int)
}

/// The parts of table customer determine its rows.
pub proof fn lemma_customer_determines(tp: Seq<PartView>, a: Seq<Row>, b: Seq<Row>)
    requires customer_ok(tp, a), customer_ok(tp, b),
    ensures a == b,
{
    assert forall|j: int, c: int| 0 <= j < a.len() && 0 <= c < 8 implies #[trigger] a[j][c] == b[j][c] by {
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
        } else if c == 7 {
            assert(a[j][7] == b[j][7]);
        }
    }
    lemma_rows_eq(a, b, 8);
}

// ---------------------------------------------------------------------------------------------- part

/// First part of table part in this storage.
pub const PART_FIRST: usize = 21;
/// Number of parts of table part.
pub const PA_PARTS: usize = 29;
/// part: U64 [rows, block rows].
pub const PA_LAYOUT: usize = 0;
/// part: U64 group starts.
pub const PA_GROUPS: usize = 1;
/// part: U32 codes of p_partkey.
pub const PA_PARTKEY_CODES: usize = 2;
/// part: I64 group bases of p_partkey.
pub const PA_PARTKEY_BASE: usize = 3;
/// part: U64 offsets of p_name.
pub const PA_NAME_OFFS: usize = 4;
/// part: U8 bytes of p_name.
pub const PA_NAME_BYTES: usize = 5;
/// part: U8 codes of dictionary indices of p_mfgr.
pub const PA_MFGR_CODES: usize = 6;
/// part: U64 group bases of dictionary indices of p_mfgr.
pub const PA_MFGR_BASE: usize = 7;
/// part: U64 dictionary offsets of p_mfgr.
pub const PA_MFGR_DICT_OFFS: usize = 8;
/// part: U8 dictionary bytes of p_mfgr.
pub const PA_MFGR_DICT_BYTES: usize = 9;
/// part: U8 codes of dictionary indices of p_brand.
pub const PA_BRAND_CODES: usize = 10;
/// part: U64 group bases of dictionary indices of p_brand.
pub const PA_BRAND_BASE: usize = 11;
/// part: U64 dictionary offsets of p_brand.
pub const PA_BRAND_DICT_OFFS: usize = 12;
/// part: U8 dictionary bytes of p_brand.
pub const PA_BRAND_DICT_BYTES: usize = 13;
/// part: U8 codes of dictionary indices of p_type.
pub const PA_TYPE_CODES: usize = 14;
/// part: U64 group bases of dictionary indices of p_type.
pub const PA_TYPE_BASE: usize = 15;
/// part: U64 dictionary offsets of p_type.
pub const PA_TYPE_DICT_OFFS: usize = 16;
/// part: U8 dictionary bytes of p_type.
pub const PA_TYPE_DICT_BYTES: usize = 17;
/// part: U8 codes of p_size.
pub const PA_SIZE_CODES: usize = 18;
/// part: I64 group bases of p_size.
pub const PA_SIZE_BASE: usize = 19;
/// part: U8 codes of dictionary indices of p_container.
pub const PA_CONTAINER_CODES: usize = 20;
/// part: U64 group bases of dictionary indices of p_container.
pub const PA_CONTAINER_BASE: usize = 21;
/// part: U64 dictionary offsets of p_container.
pub const PA_CONTAINER_DICT_OFFS: usize = 22;
/// part: U8 dictionary bytes of p_container.
pub const PA_CONTAINER_DICT_BYTES: usize = 23;
/// part: U32 codes of p_retailprice.
pub const PA_RETAILPRICE_CODES: usize = 24;
/// part: I64 group bases of p_retailprice.
pub const PA_RETAILPRICE_BASE: usize = 25;
/// part: U64 offsets of p_comment.
pub const PA_COMMENT_OFFS: usize = 26;
/// part: U8 bytes of p_comment.
pub const PA_COMMENT_BYTES: usize = 27;
/// part: U64 [key index kind: 0 none, 1 stored rows sorted by key, 2 key index] of p_partkey.
pub const PA_KEYIDX_KIND: usize = 28;

/// Table part (9 columns, canonical row order) in its parts `tp`:
/// column 0 p_partkey: bigint, FOR u32 codes + I64 bases.
/// column 1 p_name: text, U64 offsets + U8 bytes.
/// column 2 p_mfgr: text, sorted dictionary; FOR u8 codes of entry indices + U64 bases.
/// column 3 p_brand: text, sorted dictionary; FOR u8 codes of entry indices + U64 bases.
/// column 4 p_type: text, sorted dictionary; FOR u8 codes of entry indices + U64 bases.
/// column 5 p_size: bigint, FOR u8 codes + I64 bases.
/// column 6 p_container: text, sorted dictionary; FOR u8 codes of entry indices + U64 bases.
/// column 7 p_retailprice: numeric(15,2) coefficient, FOR u32 codes + I64 bases.
/// column 8 p_comment: text, U64 offsets + U8 bytes.
pub open spec fn part_ok(tp: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& tp.len() == PA_PARTS
    &&& table_layout_ok(tp, rel.len() as int)
    &&& rows_width(rel, 9)
    &&& tp[PA_PARTKEY_CODES as int] is U32
    &&& int_col_at(tp, PA_GROUPS as int, PA_PARTKEY_CODES as int, PA_PARTKEY_BASE as int, rel, 0)
    &&& text_col_at(tp, PA_NAME_OFFS as int, PA_NAME_BYTES as int, rel, 1)
    &&& tp[PA_MFGR_CODES as int] is U8
    &&& dict_col_at(tp, PA_GROUPS as int, PA_MFGR_CODES as int, PA_MFGR_BASE as int, PA_MFGR_DICT_OFFS as int, PA_MFGR_DICT_BYTES as int, rel, 2)
    &&& tp[PA_BRAND_CODES as int] is U8
    &&& dict_col_at(tp, PA_GROUPS as int, PA_BRAND_CODES as int, PA_BRAND_BASE as int, PA_BRAND_DICT_OFFS as int, PA_BRAND_DICT_BYTES as int, rel, 3)
    &&& tp[PA_TYPE_CODES as int] is U8
    &&& dict_col_at(tp, PA_GROUPS as int, PA_TYPE_CODES as int, PA_TYPE_BASE as int, PA_TYPE_DICT_OFFS as int, PA_TYPE_DICT_BYTES as int, rel, 4)
    &&& tp[PA_SIZE_CODES as int] is U8
    &&& int_col_at(tp, PA_GROUPS as int, PA_SIZE_CODES as int, PA_SIZE_BASE as int, rel, 5)
    &&& tp[PA_CONTAINER_CODES as int] is U8
    &&& dict_col_at(tp, PA_GROUPS as int, PA_CONTAINER_CODES as int, PA_CONTAINER_BASE as int, PA_CONTAINER_DICT_OFFS as int, PA_CONTAINER_DICT_BYTES as int, rel, 6)
    &&& tp[PA_RETAILPRICE_CODES as int] is U32
    &&& num_col_at(tp, PA_GROUPS as int, PA_RETAILPRICE_CODES as int, PA_RETAILPRICE_BASE as int, rel, 7, 2)
    &&& text_col_at(tp, PA_COMMENT_OFFS as int, PA_COMMENT_BYTES as int, rel, 8)
    &&& tp[PA_KEYIDX_KIND as int] is U64 && u64s(tp[PA_KEYIDX_KIND as int]).len() == 1
    &&& keyidx_ok(u32s(tp[PA_PARTKEY_CODES as int]), i64s(tp[PA_PARTKEY_BASE as int]), Seq::<u32>::empty(), Seq::<u64>::empty(), u64s(tp[PA_LAYOUT as int])[1] as int, u64s(tp[PA_KEYIDX_KIND as int])[0], rel.len() as int)
}

/// The parts of table part determine its rows.
pub proof fn lemma_part_determines(tp: Seq<PartView>, a: Seq<Row>, b: Seq<Row>)
    requires part_ok(tp, a), part_ok(tp, b),
    ensures a == b,
{
    assert forall|j: int, c: int| 0 <= j < a.len() && 0 <= c < 9 implies #[trigger] a[j][c] == b[j][c] by {
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
        } else if c == 7 {
            assert(a[j][7] == b[j][7]);
        } else if c == 8 {
            assert(a[j][8] == b[j][8]);
        }
    }
    lemma_rows_eq(a, b, 9);
}

/// Number of parts of storage custpart.
pub const CUSTPART_PARTS: usize = 50;

/// The parts hold every table of the storage, each over its own part range (`<table>_ok`).
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& parts.len() == CUSTPART_PARTS
    &&& rels.len() == 2
    &&& customer_ok(parts.subrange(CUSTOMER_FIRST as int, (CUSTOMER_FIRST + CU_PARTS) as int), rels[0])
    &&& part_ok(parts.subrange(PART_FIRST as int, (PART_FIRST + PA_PARTS) as int), rels[1])
}

/// The parts determine the relations they represent (complete lossless storage).
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    lemma_customer_determines(parts.subrange(CUSTOMER_FIRST as int, (CUSTOMER_FIRST + CU_PARTS) as int), a[0], b[0]);
    lemma_part_determines(parts.subrange(PART_FIRST as int, (PART_FIRST + PA_PARTS) as int), a[1], b[1]);
    assert(a =~= b);
}

} // verus!
