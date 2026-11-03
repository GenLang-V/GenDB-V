//! Storage `liruns`: storage `facts` (its 75 parts, inherited unchanged) followed by layout metadata of its stored
//! lineitem rows: the run lengths of equal `l_orderkey`, sampled run starts, and a zone map of `l_quantity`.
//!
//! Inherited parts (`facts`: lineitem at `0 .. 48`, orders at `48 .. 74`, the co-clustering flag at 74). This storage
//! states only what it needs of them, with the definitions of `facts` (`common`, `cluster`: byte-for-byte copies):
//! - lineitem: the frame (`LI_LAYOUT` U64 `[rows, block rows]`, `LI_GROUPS` uniform groups), the row map column
//!   (stored row `j` is canonical row `for_at(.., j)`, a bijection) and columns 0 `l_orderkey` (U32 codes, I64 bases)
//!   and 1 `l_quantity` (numeric(15, 2) coefficients, U16 codes, I64 bases) of the stored rows;
//! - orders: the frame, the row map, columns 0 `o_orderkey`, 1 `o_custkey` (U32 codes, I64 bases), 2 `o_totalprice`
//!   (numeric(15, 2) coefficients, U32 codes, I64 bases), 3 `o_orderdate` (days since 2000-01-01, U16 codes, I64
//!   bases) and the `o_orderkey` key index (`common::keyidx`) with its row-map property;
//! - the co-clustering flag: when it is 1, the stored lineitem rows follow the stored orders (`cluster::clustered`).
//!
//! New parts:
//! - `RUN_META` (U64 `[mode, stride]`): mode `MODE_RUNS` (1) when the runs below are present (else 0, nothing known);
//! - `RUN_LENS` (U8, one per run): the stored lineitem rows split into maximal runs of equal `l_orderkey`: run `r`
//!   is the rows `rstart(r) .. rstart(r + 1)` (`rstart` = prefix sums of the lengths), every length at least 1,
//!   the runs cover all `n` rows, every row of a run has the key of its first row, and the rows on both sides of a
//!   run boundary have different keys (`runs_ok`). The run-length encoding of the stored key column: row counts of
//!   the layout, no value;
//! - `RUN_STARTS` (U64): `starts[b] == rstart(b * stride)` for `b * stride` below the run count (where parallel
//!   scans start);
//! - `QTY_ZMAX` (I64, one per lineitem group, in mode `MODE_RUNS`): a zone map of `l_quantity`: every coefficient of
//!   group `g` (rows `g * block .. (g + 1) * block`) is at most `zmax[g]`;
//! - `LONG_META` (U64 `[mode, lmax, nlong]`), `LONG_RUNS` and `LONG_STARTS` (U32, one per run): a permutation of the
//!   runs ordered by run length, longest first, then by run index, as run indices and as start rows (row positions
//!   into the stored lineitem rows). In mode `MODE_LONG` (`long_ok`) no run is longer than `lmax` and the first
//!   `nlong` entries are exactly the runs of length `lmax`, ascending. Positions and layout row counts only.
//!
//! The stored relations are lineitem projected on `[l_orderkey, l_quantity]` and orders projected on `[o_orderkey,
//! o_custkey, o_totalprice, o_orderdate]`, both in canonical row order (`declaration::stored_relations`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::{Row, Val};
pub mod common;
pub mod cluster;
use common::colfmt::*;
use common::keyidx::{keyidx_ok, fidx};

verus! {

/// The frame of a table of `n` rows: `tp[0]` is U64 `[n, block rows]`, `tp[1]` the uniform groups of that block size.
pub open spec fn table_layout_ok(tp: Seq<PartView>, n: int) -> bool {
    &&& tp.len() >= 2
    &&& tp[0] is U64
    &&& u64s(tp[0]).len() == 2
    &&& u64s(tp[0])[0] == n
    &&& groups_part_ok(tp[1], n, u64s(tp[0])[1] as int)
}

// ---------------------------------------------------------------------------------------------- inherited lineitem

/// First part of table lineitem.
pub const LINEITEM_FIRST: usize = 0;
/// Number of parts of table lineitem in `facts`.
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
/// lineitem: U16 codes of l_quantity.
pub const LI_QUANTITY_CODES: usize = 12;
/// lineitem: I64 group bases of l_quantity.
pub const LI_QUANTITY_BASE: usize = 13;

/// The stored rows of lineitem: stored row `j` is canonical row `for_at(.., j)` of its row map column.
pub open spec fn lineitem_rows(tp: Seq<PartView>, rel: Seq<Row>) -> Seq<Row> {
    perm_rows(tp, LI_GROUPS as int, LI_PERM_CODES as int, LI_PERM_BASE as int, rel)
}

/// The row map of lineitem (stored row -> canonical row).
pub open spec fn lineitem_map(tp: Seq<PartView>, n: int) -> Seq<int> {
    for_map(gs_at(tp, LI_GROUPS as int), tp[LI_PERM_BASE as int], tp[LI_PERM_CODES as int], n)
}

/// The two stored lineitem columns over the stored rows `rows`.
pub open spec fn lineitem_cols_ok(tp: Seq<PartView>, rows: Seq<Row>) -> bool {
    &&& tp[LI_ORDERKEY_CODES as int] is U32
    &&& int_col_at(tp, LI_GROUPS as int, LI_ORDERKEY_CODES as int, LI_ORDERKEY_BASE as int, rows, 0)
    &&& tp[LI_QUANTITY_CODES as int] is U16
    &&& num_col_at(tp, LI_GROUPS as int, LI_QUANTITY_CODES as int, LI_QUANTITY_BASE as int, rows, 1, 2)
}

/// Table lineitem `[l_orderkey, l_quantity]` in the lineitem parts `tp` (clustered row order).
pub open spec fn lineitem_ok(tp: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& tp.len() == LI_PARTS
    &&& table_layout_ok(tp, rel.len() as int)
    &&& rows_width(rel, 2)
    &&& tp[LI_PERM_CODES as int] is U32
    &&& perm_col_at(tp, LI_GROUPS as int, LI_PERM_CODES as int, LI_PERM_BASE as int, rel.len() as int)
    &&& lineitem_cols_ok(tp, lineitem_rows(tp, rel))
}

// ---------------------------------------------------------------------------------------------- inherited orders

/// First part of table orders.
pub const ORDERS_FIRST: usize = 48;
/// Number of parts of table orders in `facts`.
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
/// orders: U32 codes of o_totalprice.
pub const OR_TOTALPRICE_CODES: usize = 12;
/// orders: I64 group bases of o_totalprice.
pub const OR_TOTALPRICE_BASE: usize = 13;
/// orders: U16 codes of o_orderdate.
pub const OR_ORDERDATE_CODES: usize = 14;
/// orders: I64 group bases of o_orderdate.
pub const OR_ORDERDATE_BASE: usize = 15;
/// orders: U32 codes of the stored row at each key-order position (key index) of o_orderkey.
pub const OR_KEYIDX_CODES: usize = 23;
/// orders: U64 group bases of the key index of o_orderkey.
pub const OR_KEYIDX_BASE: usize = 24;
/// orders: U64 [key index kind: 0 none, 1 stored rows sorted by key, 2 key index] of o_orderkey.
pub const OR_KEYIDX_KIND: usize = 25;

/// The stored rows of orders: stored row `j` is canonical row `for_at(.., j)` of its row map column.
pub open spec fn orders_rows(tp: Seq<PartView>, rel: Seq<Row>) -> Seq<Row> {
    perm_rows(tp, OR_GROUPS as int, OR_PERM_CODES as int, OR_PERM_BASE as int, rel)
}

/// The row map of orders (stored row -> canonical row).
pub open spec fn orders_map(tp: Seq<PartView>, n: int) -> Seq<int> {
    for_map(gs_at(tp, OR_GROUPS as int), tp[OR_PERM_BASE as int], tp[OR_PERM_CODES as int], n)
}

/// The four stored orders columns and the o_orderkey key index over the stored rows `rows`.
pub open spec fn orders_cols_ok(tp: Seq<PartView>, rows: Seq<Row>) -> bool {
    &&& tp[OR_ORDERKEY_CODES as int] is U32
    &&& int_col_at(tp, OR_GROUPS as int, OR_ORDERKEY_CODES as int, OR_ORDERKEY_BASE as int, rows, 0)
    &&& tp[OR_CUSTKEY_CODES as int] is U32
    &&& int_col_at(tp, OR_GROUPS as int, OR_CUSTKEY_CODES as int, OR_CUSTKEY_BASE as int, rows, 1)
    &&& tp[OR_TOTALPRICE_CODES as int] is U32
    &&& num_col_at(tp, OR_GROUPS as int, OR_TOTALPRICE_CODES as int, OR_TOTALPRICE_BASE as int, rows, 2, 2)
    &&& tp[OR_ORDERDATE_CODES as int] is U16
    &&& date_col_at(tp, OR_GROUPS as int, OR_ORDERDATE_CODES as int, OR_ORDERDATE_BASE as int, rows, 3)
    &&& tp[OR_KEYIDX_CODES as int] is U32 && tp[OR_KEYIDX_BASE as int] is U64
    &&& tp[OR_KEYIDX_KIND as int] is U64 && u64s(tp[OR_KEYIDX_KIND as int]).len() == 1
    &&& keyidx_ok(u32s(tp[OR_ORDERKEY_CODES as int]), i64s(tp[OR_ORDERKEY_BASE as int]), u32s(tp[OR_KEYIDX_CODES as int]), u64s(tp[OR_KEYIDX_BASE as int]), u64s(tp[OR_LAYOUT as int])[1] as int, u64s(tp[OR_KEYIDX_KIND as int])[0], rows.len() as int)
    &&& (u64s(tp[OR_KEYIDX_KIND as int])[0] == 2 ==> forall|r: int| 0 <= r < rows.len() ==>
            #[trigger] orders_map(tp, rows.len() as int)[fidx(u32s(tp[OR_KEYIDX_CODES as int]), u64s(tp[OR_KEYIDX_BASE as int]), u64s(tp[OR_LAYOUT as int])[1] as int, r)] == r)
}

/// Table orders `[o_orderkey, o_custkey, o_totalprice, o_orderdate]` in the orders parts `tp` (stored by date).
pub open spec fn orders_ok(tp: Seq<PartView>, rel: Seq<Row>) -> bool {
    &&& tp.len() == OR_PARTS
    &&& table_layout_ok(tp, rel.len() as int)
    &&& rows_width(rel, 4)
    &&& tp[OR_PERM_CODES as int] is U32
    &&& perm_col_at(tp, OR_GROUPS as int, OR_PERM_CODES as int, OR_PERM_BASE as int, rel.len() as int)
    &&& orders_cols_ok(tp, orders_rows(tp, rel))
}

/// Part of the co-clustering flag (U64 `[flag]`).
pub const FACTS_CLUSTER: usize = 74;
/// Number of inherited parts (storage facts).
pub const FACTS_PARTS: usize = 75;

/// The lineitem parts of the storage.
pub open spec fn li_tp(parts: Seq<PartView>) -> Seq<PartView> {
    parts.subrange(LINEITEM_FIRST as int, (LINEITEM_FIRST + LI_PARTS) as int)
}

/// The orders parts of the storage.
pub open spec fn or_tp(parts: Seq<PartView>) -> Seq<PartView> {
    parts.subrange(ORDERS_FIRST as int, (ORDERS_FIRST + OR_PARTS) as int)
}

/// The inherited parts hold both tables and, under the flag, their co-clustering.
pub open spec fn inherited_ok(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& lineitem_ok(li_tp(parts), rels[0])
    &&& orders_ok(or_tp(parts), rels[1])
    &&& parts[FACTS_CLUSTER as int] is U64 && u64s(parts[FACTS_CLUSTER as int]).len() == 1
    &&& u64s(parts[FACTS_CLUSTER as int])[0] == 1 ==> cluster::clustered(lineitem_rows(li_tp(parts), rels[0]),
            orders_rows(or_tp(parts), rels[1]))
}

// ---------------------------------------------------------------------------------------------- the new parts

/// U64 `[mode, stride]`.
pub const RUN_META: usize = 75;
/// U8 run lengths.
pub const RUN_LENS: usize = 76;
/// U64 sampled run starts.
pub const RUN_STARTS: usize = 77;
/// I64 zone map of l_quantity (one maximum per lineitem group).
pub const QTY_ZMAX: usize = 78;
/// U64 `[mode, longest run length, runs of that length]` of the run permutation by length.
pub const LONG_META: usize = 79;
/// U32 run indices: the runs ordered by length (longest first), then by position.
pub const LONG_RUNS: usize = 80;
/// U32 start rows of the runs in the order of `LONG_RUNS`.
pub const LONG_STARTS: usize = 81;
/// Number of parts of storage liruns.
pub const LIRUNS_PARTS: usize = 82;
/// Mode of present runs.
pub const MODE_RUNS: u64 = 1;
/// Mode of a present run permutation.
pub const MODE_LONG: u64 = 1;

/// Rows per block of lineitem.
pub open spec fn li_bs(parts: Seq<PartView>) -> int {
    u64s(parts[LI_LAYOUT as int])[1] as int
}

/// l_orderkey of stored lineitem row `j`.
pub open spec fn lkey_at(parts: Seq<PartView>, j: int) -> int {
    i64s(parts[LI_ORDERKEY_BASE as int])[j / li_bs(parts)] + u32s(parts[LI_ORDERKEY_CODES as int])[j]
}

/// l_quantity coefficient (scale 2) of stored lineitem row `j`.
pub open spec fn lqty_at(parts: Seq<PartView>, j: int) -> int {
    i64s(parts[LI_QUANTITY_BASE as int])[j / li_bs(parts)] + u16s(parts[LI_QUANTITY_CODES as int])[j]
}

pub open spec fn u16s(p: PartView) -> Seq<u16> {
    match p {
        PartView::U16(s) => s,
        _ => Seq::empty(),
    }
}

/// Start row of run `r`: the sum of the first `r` run lengths.
pub open spec fn rstart(lens: Seq<u8>, r: int) -> int
    decreases r,
{
    if r <= 0 { 0 } else { rstart(lens, r - 1) + lens[r - 1] }
}

pub open spec fn run_meta(parts: Seq<PartView>) -> Seq<u64> {
    u64s(parts[RUN_META as int])
}

pub open spec fn run_lens(parts: Seq<PartView>) -> Seq<u8> {
    u8s(parts[RUN_LENS as int])
}

pub open spec fn run_starts(parts: Seq<PartView>) -> Seq<u64> {
    u64s(parts[RUN_STARTS as int])
}

pub open spec fn qty_zmax(parts: Seq<PartView>) -> Seq<i64> {
    i64s(parts[QTY_ZMAX as int])
}

/// Sample `b` is the start of run `b * stride`.
pub open spec fn start_ok(lens: Seq<u8>, starts: Seq<u64>, stride: int, b: int) -> bool {
    b * stride < lens.len() && starts[b] == rstart(lens, b * stride)
}

/// Every row of run `r` has the key of the run's first row.
pub open spec fn run_same(parts: Seq<PartView>, r: int) -> bool {
    let lens = run_lens(parts);
    forall|j: int| rstart(lens, r) <= j < rstart(lens, r + 1) ==>
        #[trigger] lkey_at(parts, j) == lkey_at(parts, rstart(lens, r))
}

/// The rows on both sides of the start of run `r` have different keys.
pub open spec fn run_cut(parts: Seq<PartView>, r: int) -> bool {
    let lens = run_lens(parts);
    lkey_at(parts, rstart(lens, r) - 1) != lkey_at(parts, rstart(lens, r))
}

/// The runs (when present) split the `n` stored lineitem rows into maximal runs of equal l_orderkey.
pub open spec fn runs_ok(parts: Seq<PartView>, n: int) -> bool {
    let lens = run_lens(parts);
    let nr = lens.len() as int;
    let stride = run_meta(parts)[1] as int;
    &&& parts[RUN_META as int] is U64 && run_meta(parts).len() == 2
    &&& parts[RUN_LENS as int] is U8
    &&& parts[RUN_STARTS as int] is U64
    &&& run_meta(parts)[0] == MODE_RUNS ==> {
        &&& stride >= 1
        &&& rstart(lens, nr) == n
        &&& forall|r: int| 0 <= r < nr ==> #[trigger] lens[r] >= 1 && run_same(parts, r)
        &&& forall|r: int| 0 < r < nr ==> #[trigger] run_cut(parts, r)
        &&& forall|b: int| 0 <= b < run_starts(parts).len() ==> #[trigger] start_ok(lens, run_starts(parts), stride, b)
    }
}

/// The zone map of l_quantity (when present) bounds every coefficient of its group from above.
pub open spec fn zone_ok(parts: Seq<PartView>, n: int) -> bool {
    &&& parts[QTY_ZMAX as int] is I64
    &&& run_meta(parts)[0] == MODE_RUNS ==> {
        &&& qty_zmax(parts).len() == i64s(parts[LI_QUANTITY_BASE as int]).len()
        &&& forall|j: int| 0 <= j < n ==> #[trigger] lqty_at(parts, j) <= qty_zmax(parts)[j / li_bs(parts)]
    }
}

pub open spec fn long_meta(parts: Seq<PartView>) -> Seq<u64> {
    u64s(parts[LONG_META as int])
}

pub open spec fn long_runs(parts: Seq<PartView>) -> Seq<u32> {
    u32s(parts[LONG_RUNS as int])
}

pub open spec fn long_starts(parts: Seq<PartView>) -> Seq<u32> {
    u32s(parts[LONG_STARTS as int])
}

/// Entry `i` of the permutation is a run of length `lmax`, and its start row is that run's start.
pub open spec fn long_at(lens: Seq<u8>, lr: Seq<u32>, ls: Seq<u32>, lmax: int, i: int) -> bool {
    &&& (lr[i] as int) < lens.len()
    &&& lens[lr[i] as int] == lmax
    &&& ls[i] as int == rstart(lens, lr[i] as int)
}

/// Run `r` is among the first `nlong` entries of the permutation.
pub open spec fn long_listed(lr: Seq<u32>, nlong: int, r: int) -> bool {
    exists|i: int| 0 <= i < nlong && lr[i] as int == r
}

/// The run permutation (when present, over present runs): no run is longer than `lmax`, and its first `nlong`
/// entries are exactly the runs of length `lmax`, by increasing run index, with their start rows. (The later entries
/// list the shorter runs by decreasing length; nothing is stated about them.)
pub open spec fn long_ok(parts: Seq<PartView>) -> bool {
    let lens = run_lens(parts);
    let nr = lens.len() as int;
    let meta = long_meta(parts);
    let lmax = meta[1] as int;
    let nlong = meta[2] as int;
    let lr = long_runs(parts);
    let ls = long_starts(parts);
    &&& parts[LONG_META as int] is U64 && meta.len() == 3
    &&& parts[LONG_RUNS as int] is U32
    &&& parts[LONG_STARTS as int] is U32
    &&& meta[0] == MODE_LONG ==> {
        &&& run_meta(parts)[0] == MODE_RUNS
        &&& nlong <= lr.len() && nlong <= ls.len()
        &&& forall|r: int| 0 <= r < nr ==> #[trigger] lens[r] <= lmax
        &&& forall|i: int| 0 <= i < nlong ==> #[trigger] long_at(lens, lr, ls, lmax, i)
        &&& forall|a: int, b: int| 0 <= a < b < nlong ==> #[trigger] lr[a] < #[trigger] lr[b]
        &&& forall|r: int| 0 <= r < nr && lens[r] == lmax ==> #[trigger] long_listed(lr, nlong, r)
    }
}

// ---------------------------------------------------------------------------------------------- represents

/// The inherited parts hold `[l_orderkey, l_quantity]` of lineitem and `[o_orderkey, o_custkey, o_totalprice,
/// o_orderdate]` of orders (with the co-clustering flag); the new parts are the runs and the zone map.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& parts.len() == LIRUNS_PARTS
    &&& rels.len() == 2
    &&& inherited_ok(parts, rels)
    &&& runs_ok(parts, rels[0].len() as int)
    &&& zone_ok(parts, rels[0].len() as int)
    &&& long_ok(parts)
}

/// The parts of lineitem determine its rows.
pub proof fn lemma_lineitem_determines(tp: Seq<PartView>, a: Seq<Row>, b: Seq<Row>)
    requires lineitem_ok(tp, a), lineitem_ok(tp, b),
    ensures a == b,
{
    let n = a.len() as int;
    let m = lineitem_map(tp, n);
    assert(b.len() == n);
    let (ra, rb) = (lineitem_rows(tp, a), lineitem_rows(tp, b));
    assert(ra == stored_rows(a, m));
    assert(rb == stored_rows(b, m));
    assert forall|j: int, c: int| 0 <= j < n && 0 <= c < 2 implies #[trigger] stored_rows(a, m)[j][c] == stored_rows(b, m)[j][c] by {
        if c == 0 {
            assert(ra[j][0] == rb[j][0]);
        } else {
            assert(ra[j][1] == rb[j][1]);
        }
    }
    lemma_stored_rows_determine(a, b, m, n, 2);
}

/// The parts of orders determine its rows.
pub proof fn lemma_orders_determines(tp: Seq<PartView>, a: Seq<Row>, b: Seq<Row>)
    requires orders_ok(tp, a), orders_ok(tp, b),
    ensures a == b,
{
    let n = a.len() as int;
    let m = orders_map(tp, n);
    assert(b.len() == n);
    let (ra, rb) = (orders_rows(tp, a), orders_rows(tp, b));
    assert(ra == stored_rows(a, m));
    assert(rb == stored_rows(b, m));
    assert forall|j: int, c: int| 0 <= j < n && 0 <= c < 4 implies #[trigger] stored_rows(a, m)[j][c] == stored_rows(b, m)[j][c] by {
        if c == 0 {
            assert(ra[j][0] == rb[j][0]);
        } else if c == 1 {
            assert(ra[j][1] == rb[j][1]);
        } else if c == 2 {
            assert(ra[j][2] == rb[j][2]);
        } else {
            assert(ra[j][3] == rb[j][3]);
        }
    }
    lemma_stored_rows_determine(a, b, m, n, 4);
}

/// The parts determine the relations they represent (complete lossless storage of the stored columns).
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    lemma_lineitem_determines(li_tp(parts), a[0], b[0]);
    lemma_orders_determines(or_tp(parts), a[1], b[1]);
    assert(a =~= b);
}

} // verus!
