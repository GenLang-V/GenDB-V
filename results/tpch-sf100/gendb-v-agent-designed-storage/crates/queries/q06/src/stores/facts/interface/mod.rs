//! Storage `facts`: lineitem (every column but l_comment) and orders (every column but o_clerk and o_comment), clustered: orders stored by o_orderdate, lineitem stored in the order of its orders, column by column (`common::colfmt`).
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
pub mod cluster;
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


// ---------------------------------------------------------------------------------------------- lineitem

/// First part of table lineitem in this storage.
pub const LINEITEM_FIRST: usize = 0;
/// Number of parts of table lineitem.
pub const LI_PARTS: usize = 48;
/// lineitem: U64 [rows, block rows].
pub const LI_LAYOUT: usize = 0;
/// lineitem: U64 group starts.
pub const LI_GROUPS: usize = 1;
/// lineitem: U32 codes of the canonical row of each stored row.
pub const LI_PERM_CODES: usize = 2;
/// lineitem: U64 group bases of canonical rows.
pub const LI_PERM_BASE: usize = 3;
/// lineitem: U32 codes of l_orderkey.
pub const LI_ORDERKEY_CODES: usize = 4;
/// lineitem: I64 group bases of l_orderkey.
pub const LI_ORDERKEY_BASE: usize = 5;
/// lineitem: U32 codes of l_partkey.
pub const LI_PARTKEY_CODES: usize = 6;
/// lineitem: I64 group bases of l_partkey.
pub const LI_PARTKEY_BASE: usize = 7;
/// lineitem: U32 codes of l_suppkey.
pub const LI_SUPPKEY_CODES: usize = 8;
/// lineitem: I64 group bases of l_suppkey.
pub const LI_SUPPKEY_BASE: usize = 9;
/// lineitem: U8 codes of l_linenumber.
pub const LI_LINENUMBER_CODES: usize = 10;
/// lineitem: I64 group bases of l_linenumber.
pub const LI_LINENUMBER_BASE: usize = 11;
/// lineitem: U16 codes of l_quantity.
pub const LI_QUANTITY_CODES: usize = 12;
/// lineitem: I64 group bases of l_quantity.
pub const LI_QUANTITY_BASE: usize = 13;
/// lineitem: U32 codes of l_extendedprice.
pub const LI_EXTENDEDPRICE_CODES: usize = 14;
/// lineitem: I64 group bases of l_extendedprice.
pub const LI_EXTENDEDPRICE_BASE: usize = 15;
/// lineitem: U8 codes of l_discount.
pub const LI_DISCOUNT_CODES: usize = 16;
/// lineitem: I64 group bases of l_discount.
pub const LI_DISCOUNT_BASE: usize = 17;
/// lineitem: U8 codes of l_tax.
pub const LI_TAX_CODES: usize = 18;
/// lineitem: I64 group bases of l_tax.
pub const LI_TAX_BASE: usize = 19;
/// lineitem: U8 codes of dictionary indices of l_returnflag.
pub const LI_RETURNFLAG_CODES: usize = 20;
/// lineitem: U64 group bases of dictionary indices of l_returnflag.
pub const LI_RETURNFLAG_BASE: usize = 21;
/// lineitem: U64 dictionary offsets of l_returnflag.
pub const LI_RETURNFLAG_DICT_OFFS: usize = 22;
/// lineitem: U8 dictionary bytes of l_returnflag.
pub const LI_RETURNFLAG_DICT_BYTES: usize = 23;
/// lineitem: U8 codes of dictionary indices of l_linestatus.
pub const LI_LINESTATUS_CODES: usize = 24;
/// lineitem: U64 group bases of dictionary indices of l_linestatus.
pub const LI_LINESTATUS_BASE: usize = 25;
/// lineitem: U64 dictionary offsets of l_linestatus.
pub const LI_LINESTATUS_DICT_OFFS: usize = 26;
/// lineitem: U8 dictionary bytes of l_linestatus.
pub const LI_LINESTATUS_DICT_BYTES: usize = 27;
/// lineitem: U16 codes of l_shipdate.
pub const LI_SHIPDATE_CODES: usize = 28;
/// lineitem: I64 group bases of l_shipdate.
pub const LI_SHIPDATE_BASE: usize = 29;
/// lineitem: I64 group maxima (zone map) of l_shipdate.
pub const LI_SHIPDATE_ZMAX: usize = 30;
/// lineitem: U16 codes of l_commitdate.
pub const LI_COMMITDATE_CODES: usize = 31;
/// lineitem: I64 group bases of l_commitdate.
pub const LI_COMMITDATE_BASE: usize = 32;
/// lineitem: I64 group maxima (zone map) of l_commitdate.
pub const LI_COMMITDATE_ZMAX: usize = 33;
/// lineitem: U16 codes of l_receiptdate.
pub const LI_RECEIPTDATE_CODES: usize = 34;
/// lineitem: I64 group bases of l_receiptdate.
pub const LI_RECEIPTDATE_BASE: usize = 35;
/// lineitem: I64 group maxima (zone map) of l_receiptdate.
pub const LI_RECEIPTDATE_ZMAX: usize = 36;
/// lineitem: U8 codes of dictionary indices of l_shipinstruct.
pub const LI_SHIPINSTRUCT_CODES: usize = 37;
/// lineitem: U64 group bases of dictionary indices of l_shipinstruct.
pub const LI_SHIPINSTRUCT_BASE: usize = 38;
/// lineitem: U64 dictionary offsets of l_shipinstruct.
pub const LI_SHIPINSTRUCT_DICT_OFFS: usize = 39;
/// lineitem: U8 dictionary bytes of l_shipinstruct.
pub const LI_SHIPINSTRUCT_DICT_BYTES: usize = 40;
/// lineitem: U8 codes of dictionary indices of l_shipmode.
pub const LI_SHIPMODE_CODES: usize = 41;
/// lineitem: U64 group bases of dictionary indices of l_shipmode.
pub const LI_SHIPMODE_BASE: usize = 42;
/// lineitem: U64 dictionary offsets of l_shipmode.
pub const LI_SHIPMODE_DICT_OFFS: usize = 43;
/// lineitem: U8 dictionary bytes of l_shipmode.
pub const LI_SHIPMODE_DICT_BYTES: usize = 44;
/// lineitem: U32 codes of the stored row at each key-order position (key index) of l_partkey.
pub const LI_KEYIDX_CODES: usize = 45;
/// lineitem: U64 group bases of the key index of l_partkey.
pub const LI_KEYIDX_BASE: usize = 46;
/// lineitem: U64 [key index kind: 0 none, 1 stored rows sorted by key, 2 key index] of l_partkey.
pub const LI_KEYIDX_KIND: usize = 47;

/// The stored rows of table lineitem: stored row `j` is canonical row `for_at(.., j)` of its row map column.
pub open spec fn lineitem_rows(tp: Seq<PartView>, rel: Seq<Row>) -> Seq<Row> {
    perm_rows(tp, LI_GROUPS as int, LI_PERM_CODES as int, LI_PERM_BASE as int, rel)
}

/// The row map of table lineitem (stored row -> canonical row).
pub open spec fn lineitem_map(tp: Seq<PartView>, n: int) -> Seq<int> {
    for_map(gs_at(tp, LI_GROUPS as int), tp[LI_PERM_BASE as int], tp[LI_PERM_CODES as int], n)
}

/// Table lineitem (15 columns, clustered row order) in its parts `tp`:
/// column 0 l_orderkey: bigint, FOR u32 codes + I64 bases.
/// column 1 l_partkey: bigint, FOR u32 codes + I64 bases.
/// column 2 l_suppkey: bigint, FOR u32 codes + I64 bases.
/// column 3 l_linenumber: bigint, FOR u8 codes + I64 bases.
/// column 4 l_quantity: numeric(15,2) coefficient, FOR u16 codes + I64 bases.
/// column 5 l_extendedprice: numeric(15,2) coefficient, FOR u32 codes + I64 bases.
/// column 6 l_discount: numeric(15,2) coefficient, FOR u8 codes + I64 bases.
/// column 7 l_tax: numeric(15,2) coefficient, FOR u8 codes + I64 bases.
/// column 8 l_returnflag: text, sorted dictionary; FOR u8 codes of entry indices + U64 bases.
/// column 9 l_linestatus: text, sorted dictionary; FOR u8 codes of entry indices + U64 bases.
/// column 10 l_shipdate: date (days since 2000-01-01), FOR u16 codes + I64 bases + I64 zone maxima.
/// column 11 l_commitdate: date (days since 2000-01-01), FOR u16 codes + I64 bases + I64 zone maxima.
/// column 12 l_receiptdate: date (days since 2000-01-01), FOR u16 codes + I64 bases + I64 zone maxima.
/// column 13 l_shipinstruct: text, sorted dictionary; FOR u8 codes of entry indices + U64 bases.
/// column 14 l_shipmode: text, sorted dictionary; FOR u8 codes of entry indices + U64 bases.
pub open spec fn lineitem_ok(tp: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& tp.len() == LI_PARTS
    &&& table_layout_ok(tp, rel.len() as int)
    &&& rows_width(rel, 15)
    &&& tp[LI_PERM_CODES as int] is U32
    &&& perm_col_at(tp, LI_GROUPS as int, LI_PERM_CODES as int, LI_PERM_BASE as int, rel.len() as int)
    &&& lineitem_cols_ok(tp, lineitem_rows(tp, rel))
}

/// The columns of table lineitem over its stored rows `rows`.
pub open spec fn lineitem_cols_ok(tp: Seq<PartView>, rows: Seq<Row>) -> bool {
    &&& true
    &&& tp[LI_ORDERKEY_CODES as int] is U32
    &&& int_col_at(tp, LI_GROUPS as int, LI_ORDERKEY_CODES as int, LI_ORDERKEY_BASE as int, rows, 0)
    &&& tp[LI_PARTKEY_CODES as int] is U32
    &&& int_col_at(tp, LI_GROUPS as int, LI_PARTKEY_CODES as int, LI_PARTKEY_BASE as int, rows, 1)
    &&& tp[LI_SUPPKEY_CODES as int] is U32
    &&& int_col_at(tp, LI_GROUPS as int, LI_SUPPKEY_CODES as int, LI_SUPPKEY_BASE as int, rows, 2)
    &&& tp[LI_LINENUMBER_CODES as int] is U8
    &&& int_col_at(tp, LI_GROUPS as int, LI_LINENUMBER_CODES as int, LI_LINENUMBER_BASE as int, rows, 3)
    &&& tp[LI_QUANTITY_CODES as int] is U16
    &&& num_col_at(tp, LI_GROUPS as int, LI_QUANTITY_CODES as int, LI_QUANTITY_BASE as int, rows, 4, 2)
    &&& tp[LI_EXTENDEDPRICE_CODES as int] is U32
    &&& num_col_at(tp, LI_GROUPS as int, LI_EXTENDEDPRICE_CODES as int, LI_EXTENDEDPRICE_BASE as int, rows, 5, 2)
    &&& tp[LI_DISCOUNT_CODES as int] is U8
    &&& num_col_at(tp, LI_GROUPS as int, LI_DISCOUNT_CODES as int, LI_DISCOUNT_BASE as int, rows, 6, 2)
    &&& tp[LI_TAX_CODES as int] is U8
    &&& num_col_at(tp, LI_GROUPS as int, LI_TAX_CODES as int, LI_TAX_BASE as int, rows, 7, 2)
    &&& tp[LI_RETURNFLAG_CODES as int] is U8
    &&& dict_col_at(tp, LI_GROUPS as int, LI_RETURNFLAG_CODES as int, LI_RETURNFLAG_BASE as int, LI_RETURNFLAG_DICT_OFFS as int, LI_RETURNFLAG_DICT_BYTES as int, rows, 8)
    &&& tp[LI_LINESTATUS_CODES as int] is U8
    &&& dict_col_at(tp, LI_GROUPS as int, LI_LINESTATUS_CODES as int, LI_LINESTATUS_BASE as int, LI_LINESTATUS_DICT_OFFS as int, LI_LINESTATUS_DICT_BYTES as int, rows, 9)
    &&& tp[LI_SHIPDATE_CODES as int] is U16
    &&& date_col_at(tp, LI_GROUPS as int, LI_SHIPDATE_CODES as int, LI_SHIPDATE_BASE as int, rows, 10)
    &&& zone_at(tp, LI_GROUPS as int, LI_SHIPDATE_CODES as int, LI_SHIPDATE_BASE as int, LI_SHIPDATE_ZMAX as int)
    &&& tp[LI_COMMITDATE_CODES as int] is U16
    &&& date_col_at(tp, LI_GROUPS as int, LI_COMMITDATE_CODES as int, LI_COMMITDATE_BASE as int, rows, 11)
    &&& zone_at(tp, LI_GROUPS as int, LI_COMMITDATE_CODES as int, LI_COMMITDATE_BASE as int, LI_COMMITDATE_ZMAX as int)
    &&& tp[LI_RECEIPTDATE_CODES as int] is U16
    &&& date_col_at(tp, LI_GROUPS as int, LI_RECEIPTDATE_CODES as int, LI_RECEIPTDATE_BASE as int, rows, 12)
    &&& zone_at(tp, LI_GROUPS as int, LI_RECEIPTDATE_CODES as int, LI_RECEIPTDATE_BASE as int, LI_RECEIPTDATE_ZMAX as int)
    &&& tp[LI_SHIPINSTRUCT_CODES as int] is U8
    &&& dict_col_at(tp, LI_GROUPS as int, LI_SHIPINSTRUCT_CODES as int, LI_SHIPINSTRUCT_BASE as int, LI_SHIPINSTRUCT_DICT_OFFS as int, LI_SHIPINSTRUCT_DICT_BYTES as int, rows, 13)
    &&& tp[LI_SHIPMODE_CODES as int] is U8
    &&& dict_col_at(tp, LI_GROUPS as int, LI_SHIPMODE_CODES as int, LI_SHIPMODE_BASE as int, LI_SHIPMODE_DICT_OFFS as int, LI_SHIPMODE_DICT_BYTES as int, rows, 14)
    &&& tp[LI_KEYIDX_CODES as int] is U32 && tp[LI_KEYIDX_BASE as int] is U64
    &&& tp[LI_KEYIDX_KIND as int] is U64 && u64s(tp[LI_KEYIDX_KIND as int]).len() == 1
    &&& keyidx_ok(u32s(tp[LI_PARTKEY_CODES as int]), i64s(tp[LI_PARTKEY_BASE as int]), u32s(tp[LI_KEYIDX_CODES as int]), u64s(tp[LI_KEYIDX_BASE as int]), u64s(tp[LI_LAYOUT as int])[1] as int, u64s(tp[LI_KEYIDX_KIND as int])[0], rows.len() as int)
}

/// The parts of table lineitem determine its rows.
pub proof fn lemma_lineitem_determines(tp: Seq<PartView>, a: Seq<Row>, b: Seq<Row>)
    requires lineitem_ok(tp, a), lineitem_ok(tp, b),
    ensures a == b,
{
    let n = a.len() as int;
    let m = lineitem_map(tp, n);
    let (ra, rb) = (lineitem_rows(tp, a), lineitem_rows(tp, b));
    assert forall|j: int, c: int| 0 <= j < n && 0 <= c < 15 implies #[trigger] stored_rows(a, m)[j][c] == stored_rows(b, m)[j][c] by {
        if c == 0 {
            assert(ra[j][0] == rb[j][0]);
        } else if c == 1 {
            assert(ra[j][1] == rb[j][1]);
        } else if c == 2 {
            assert(ra[j][2] == rb[j][2]);
        } else if c == 3 {
            assert(ra[j][3] == rb[j][3]);
        } else if c == 4 {
            assert(ra[j][4] == rb[j][4]);
        } else if c == 5 {
            assert(ra[j][5] == rb[j][5]);
        } else if c == 6 {
            assert(ra[j][6] == rb[j][6]);
        } else if c == 7 {
            assert(ra[j][7] == rb[j][7]);
        } else if c == 8 {
            assert(ra[j][8] == rb[j][8]);
        } else if c == 9 {
            assert(ra[j][9] == rb[j][9]);
        } else if c == 10 {
            assert(ra[j][10] == rb[j][10]);
        } else if c == 11 {
            assert(ra[j][11] == rb[j][11]);
        } else if c == 12 {
            assert(ra[j][12] == rb[j][12]);
        } else if c == 13 {
            assert(ra[j][13] == rb[j][13]);
        } else if c == 14 {
            assert(ra[j][14] == rb[j][14]);
        }
    }
    lemma_stored_rows_determine(a, b, m, n, 15);
}

// ---------------------------------------------------------------------------------------------- orders

/// First part of table orders in this storage.
pub const ORDERS_FIRST: usize = 48;
/// Number of parts of table orders.
pub const OR_PARTS: usize = 26;
/// orders: U64 [rows, block rows].
pub const OR_LAYOUT: usize = 0;
/// orders: U64 group starts.
pub const OR_GROUPS: usize = 1;
/// orders: U32 codes of the canonical row of each stored row.
pub const OR_PERM_CODES: usize = 2;
/// orders: U64 group bases of canonical rows.
pub const OR_PERM_BASE: usize = 3;
/// orders: U32 codes of o_orderkey.
pub const OR_ORDERKEY_CODES: usize = 4;
/// orders: I64 group bases of o_orderkey.
pub const OR_ORDERKEY_BASE: usize = 5;
/// orders: U32 codes of o_custkey.
pub const OR_CUSTKEY_CODES: usize = 6;
/// orders: I64 group bases of o_custkey.
pub const OR_CUSTKEY_BASE: usize = 7;
/// orders: U8 codes of dictionary indices of o_orderstatus.
pub const OR_ORDERSTATUS_CODES: usize = 8;
/// orders: U64 group bases of dictionary indices of o_orderstatus.
pub const OR_ORDERSTATUS_BASE: usize = 9;
/// orders: U64 dictionary offsets of o_orderstatus.
pub const OR_ORDERSTATUS_DICT_OFFS: usize = 10;
/// orders: U8 dictionary bytes of o_orderstatus.
pub const OR_ORDERSTATUS_DICT_BYTES: usize = 11;
/// orders: U32 codes of o_totalprice.
pub const OR_TOTALPRICE_CODES: usize = 12;
/// orders: I64 group bases of o_totalprice.
pub const OR_TOTALPRICE_BASE: usize = 13;
/// orders: U16 codes of o_orderdate.
pub const OR_ORDERDATE_CODES: usize = 14;
/// orders: I64 group bases of o_orderdate.
pub const OR_ORDERDATE_BASE: usize = 15;
/// orders: I64 group maxima (zone map) of o_orderdate.
pub const OR_ORDERDATE_ZMAX: usize = 16;
/// orders: U8 codes of dictionary indices of o_orderpriority.
pub const OR_ORDERPRIORITY_CODES: usize = 17;
/// orders: U64 group bases of dictionary indices of o_orderpriority.
pub const OR_ORDERPRIORITY_BASE: usize = 18;
/// orders: U64 dictionary offsets of o_orderpriority.
pub const OR_ORDERPRIORITY_DICT_OFFS: usize = 19;
/// orders: U8 dictionary bytes of o_orderpriority.
pub const OR_ORDERPRIORITY_DICT_BYTES: usize = 20;
/// orders: U8 codes of o_shippriority.
pub const OR_SHIPPRIORITY_CODES: usize = 21;
/// orders: I64 group bases of o_shippriority.
pub const OR_SHIPPRIORITY_BASE: usize = 22;
/// orders: U32 codes of the stored row at each key-order position (key index) of o_orderkey.
pub const OR_KEYIDX_CODES: usize = 23;
/// orders: U64 group bases of the key index of o_orderkey.
pub const OR_KEYIDX_BASE: usize = 24;
/// orders: U64 [key index kind: 0 none, 1 stored rows sorted by key, 2 key index] of o_orderkey.
pub const OR_KEYIDX_KIND: usize = 25;

/// The stored rows of table orders: stored row `j` is canonical row `for_at(.., j)` of its row map column.
pub open spec fn orders_rows(tp: Seq<PartView>, rel: Seq<Row>) -> Seq<Row> {
    perm_rows(tp, OR_GROUPS as int, OR_PERM_CODES as int, OR_PERM_BASE as int, rel)
}

/// The row map of table orders (stored row -> canonical row).
pub open spec fn orders_map(tp: Seq<PartView>, n: int) -> Seq<int> {
    for_map(gs_at(tp, OR_GROUPS as int), tp[OR_PERM_BASE as int], tp[OR_PERM_CODES as int], n)
}

/// Table orders (7 columns, clustered row order) in its parts `tp`:
/// column 0 o_orderkey: bigint, FOR u32 codes + I64 bases.
/// column 1 o_custkey: bigint, FOR u32 codes + I64 bases.
/// column 2 o_orderstatus: text, sorted dictionary; FOR u8 codes of entry indices + U64 bases.
/// column 3 o_totalprice: numeric(15,2) coefficient, FOR u32 codes + I64 bases.
/// column 4 o_orderdate: date (days since 2000-01-01), FOR u16 codes + I64 bases + I64 zone maxima.
/// column 5 o_orderpriority: text, sorted dictionary; FOR u8 codes of entry indices + U64 bases.
/// column 6 o_shippriority: bigint, FOR u8 codes + I64 bases.
pub open spec fn orders_ok(tp: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& tp.len() == OR_PARTS
    &&& table_layout_ok(tp, rel.len() as int)
    &&& rows_width(rel, 7)
    &&& tp[OR_PERM_CODES as int] is U32
    &&& perm_col_at(tp, OR_GROUPS as int, OR_PERM_CODES as int, OR_PERM_BASE as int, rel.len() as int)
    &&& orders_cols_ok(tp, orders_rows(tp, rel))
}

/// The columns of table orders over its stored rows `rows`.
pub open spec fn orders_cols_ok(tp: Seq<PartView>, rows: Seq<Row>) -> bool {
    &&& true
    &&& tp[OR_ORDERKEY_CODES as int] is U32
    &&& int_col_at(tp, OR_GROUPS as int, OR_ORDERKEY_CODES as int, OR_ORDERKEY_BASE as int, rows, 0)
    &&& tp[OR_CUSTKEY_CODES as int] is U32
    &&& int_col_at(tp, OR_GROUPS as int, OR_CUSTKEY_CODES as int, OR_CUSTKEY_BASE as int, rows, 1)
    &&& tp[OR_ORDERSTATUS_CODES as int] is U8
    &&& dict_col_at(tp, OR_GROUPS as int, OR_ORDERSTATUS_CODES as int, OR_ORDERSTATUS_BASE as int, OR_ORDERSTATUS_DICT_OFFS as int, OR_ORDERSTATUS_DICT_BYTES as int, rows, 2)
    &&& tp[OR_TOTALPRICE_CODES as int] is U32
    &&& num_col_at(tp, OR_GROUPS as int, OR_TOTALPRICE_CODES as int, OR_TOTALPRICE_BASE as int, rows, 3, 2)
    &&& tp[OR_ORDERDATE_CODES as int] is U16
    &&& date_col_at(tp, OR_GROUPS as int, OR_ORDERDATE_CODES as int, OR_ORDERDATE_BASE as int, rows, 4)
    &&& zone_at(tp, OR_GROUPS as int, OR_ORDERDATE_CODES as int, OR_ORDERDATE_BASE as int, OR_ORDERDATE_ZMAX as int)
    &&& tp[OR_ORDERPRIORITY_CODES as int] is U8
    &&& dict_col_at(tp, OR_GROUPS as int, OR_ORDERPRIORITY_CODES as int, OR_ORDERPRIORITY_BASE as int, OR_ORDERPRIORITY_DICT_OFFS as int, OR_ORDERPRIORITY_DICT_BYTES as int, rows, 5)
    &&& tp[OR_SHIPPRIORITY_CODES as int] is U8
    &&& int_col_at(tp, OR_GROUPS as int, OR_SHIPPRIORITY_CODES as int, OR_SHIPPRIORITY_BASE as int, rows, 6)
    &&& tp[OR_KEYIDX_CODES as int] is U32 && tp[OR_KEYIDX_BASE as int] is U64
    &&& tp[OR_KEYIDX_KIND as int] is U64 && u64s(tp[OR_KEYIDX_KIND as int]).len() == 1
    &&& keyidx_ok(u32s(tp[OR_ORDERKEY_CODES as int]), i64s(tp[OR_ORDERKEY_BASE as int]), u32s(tp[OR_KEYIDX_CODES as int]), u64s(tp[OR_KEYIDX_BASE as int]), u64s(tp[OR_LAYOUT as int])[1] as int, u64s(tp[OR_KEYIDX_KIND as int])[0], rows.len() as int)
    &&& (u64s(tp[OR_KEYIDX_KIND as int])[0] == 2 ==> forall|r: int| 0 <= r < rows.len() ==>
            #[trigger] orders_map(tp, rows.len() as int)[fidx(u32s(tp[OR_KEYIDX_CODES as int]), u64s(tp[OR_KEYIDX_BASE as int]), u64s(tp[OR_LAYOUT as int])[1] as int, r)] == r)
}

/// The parts of table orders determine its rows.
pub proof fn lemma_orders_determines(tp: Seq<PartView>, a: Seq<Row>, b: Seq<Row>)
    requires orders_ok(tp, a), orders_ok(tp, b),
    ensures a == b,
{
    let n = a.len() as int;
    let m = orders_map(tp, n);
    let (ra, rb) = (orders_rows(tp, a), orders_rows(tp, b));
    assert forall|j: int, c: int| 0 <= j < n && 0 <= c < 7 implies #[trigger] stored_rows(a, m)[j][c] == stored_rows(b, m)[j][c] by {
        if c == 0 {
            assert(ra[j][0] == rb[j][0]);
        } else if c == 1 {
            assert(ra[j][1] == rb[j][1]);
        } else if c == 2 {
            assert(ra[j][2] == rb[j][2]);
        } else if c == 3 {
            assert(ra[j][3] == rb[j][3]);
        } else if c == 4 {
            assert(ra[j][4] == rb[j][4]);
        } else if c == 5 {
            assert(ra[j][5] == rb[j][5]);
        } else if c == 6 {
            assert(ra[j][6] == rb[j][6]);
        }
    }
    lemma_stored_rows_determine(a, b, m, n, 7);
}

/// Part of the co-clustering flag (U64 `[flag]`, `cluster`): 1 when the stored lineitem rows follow the stored orders.
pub const FACTS_CLUSTER: usize = 74;

/// Number of parts of storage facts.
pub const FACTS_PARTS: usize = 75;

/// The parts hold every table of the storage, each over its own part range (`<table>_ok`).
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& parts.len() == FACTS_PARTS
    &&& rels.len() == 2
    &&& lineitem_ok(parts.subrange(LINEITEM_FIRST as int, (LINEITEM_FIRST + LI_PARTS) as int), rels[0])
    &&& orders_ok(parts.subrange(ORDERS_FIRST as int, (ORDERS_FIRST + OR_PARTS) as int), rels[1])
    &&& parts[FACTS_CLUSTER as int] is U64 && u64s(parts[FACTS_CLUSTER as int]).len() == 1
    &&& u64s(parts[FACTS_CLUSTER as int])[0] == 1 ==> cluster::clustered(
            lineitem_rows(parts.subrange(LINEITEM_FIRST as int, (LINEITEM_FIRST + LI_PARTS) as int), rels[0]),
            orders_rows(parts.subrange(ORDERS_FIRST as int, (ORDERS_FIRST + OR_PARTS) as int), rels[1]))
}

/// The parts determine the relations they represent (complete lossless storage).
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    lemma_lineitem_determines(parts.subrange(LINEITEM_FIRST as int, (LINEITEM_FIRST + LI_PARTS) as int), a[0], b[0]);
    lemma_orders_determines(parts.subrange(ORDERS_FIRST as int, (ORDERS_FIRST + OR_PARTS) as int), a[1], b[1]);
    assert(a =~= b);
}

} // verus!
