//! Storage `num_vord`: storage `num` (its 27 parts, inherited unchanged) extended by a value order per unit:
//! - `P_VORDER` (`U64`, `n` entries): for every uom code `u`, positions `[unit_row(u), unit_row(u + 1))` of `vorder`
//!   (the stored rows of unit `u`, `unit_row(u)` being the start of the unit's first run) list exactly the stored
//!   rows of that same range, ordered by `value` descending (ties by stored row). `vorder_ok` states these facts.
//!   A `value DESC` scan of the rows of one unit (top-k by value, early stop) reads `vorder` from `unit_row(u)` on.
//!
//! The inherited parts (storage `num`): the `num` table (`n` rows, one per reported value), clustered by
//! `(uom, adsh, tag, version)`.
//!
//! Stored order. Stored row `i` is canonical row `orig[i]` (`P_ORIG`, a permutation of `0..n`). Stored rows are
//! sorted by (uom code, adsh code, pair code, canonical row), so:
//! - runs: `P_RUN_START` (`R + 1` entries) cuts the stored rows into `R` nonempty runs of equal `(uom, adsh)`; run `r`
//!   is stored rows `[run_start[r], run_start[r + 1])` with uom code `run_uom[r]` and adsh code `run_adsh[r]`; run keys
//!   strictly increase lexicographically (each `(uom, adsh)` combination is exactly one run);
//! - `P_UOM_RUNS` (`U + 1` entries): the runs of uom code `u` are `[uom_runs[u], uom_runs[u + 1])`
//!   (`group_starts_ok`), so a `uom = $1` filter is one dictionary lookup and one run range;
//! - inside a run, the pair codes `tv` are nondecreasing (rows of one `(tag, version)` are adjacent, and since pair
//!   codes follow tag order, rows of one tag are adjacent too).
//! Dictionaries (sorted, distinct, code order = byte order; `common::text`): uom, adsh, tag, version. `(tag, version)`
//! is coded once per row as a pair code `tv[i]` into the pair list `(pair_tag[p], pair_version[p])` (tag and version
//! codes), strictly increasing lexicographically, so pair code order is (tag, version) byte order.
//! Per stored row: `tv`, `ddate` (I32), `value` (I128, numeric(28,4) coefficients). Per run: `ddate` min and max
//! (skip bounds). In canonical row order (row `j`): `qtrs` (I32); `coreg` and `footnote` sparse: the increasing list
//! of non-NULL rows and their values as a text list (a row not listed is NULL).
use vstd::prelude::*;
use crate::spec::value::{Row, Val};
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::StoredParts;
pub mod common;
use common::text::{text_entry, text_parts_wf, text_strictly_sorted, u64_part, u8_part};
use common::cols::{i32_part, i128_part, text_col_ok, text_count};
use common::perm::{is_permutation, lemma_permutation_facts, position_of};
use common::runs::*;

verus! {

pub const P_ORIG: usize = 0;
pub const P_RUN_START: usize = 1;
pub const P_RUN_UOM: usize = 2;
pub const P_RUN_ADSH: usize = 3;
pub const P_UOM_RUNS: usize = 4;
pub const P_UOM_OFF: usize = 5;
pub const P_UOM_BYTES: usize = 6;
pub const P_ADSH_OFF: usize = 7;
pub const P_ADSH_BYTES: usize = 8;
pub const P_TV: usize = 9;
pub const P_PAIR_TAG: usize = 10;
pub const P_PAIR_VERSION: usize = 11;
pub const P_TAG_OFF: usize = 12;
pub const P_TAG_BYTES: usize = 13;
pub const P_VERSION_OFF: usize = 14;
pub const P_VERSION_BYTES: usize = 15;
pub const P_DDATE: usize = 16;
pub const P_VALUE: usize = 17;
pub const P_RUN_DDATE_MIN: usize = 18;
pub const P_RUN_DDATE_MAX: usize = 19;
pub const P_QTRS: usize = 20;
pub const P_COREG_ROWS: usize = 21;
pub const P_COREG_OFF: usize = 22;
pub const P_COREG_BYTES: usize = 23;
pub const P_FOOTNOTE_ROWS: usize = 24;
pub const P_FOOTNOTE_OFF: usize = 25;
pub const P_FOOTNOTE_BYTES: usize = 26;
pub const P_VORDER: usize = 27;
pub const PART_COUNT: usize = 28;

/// The first stored row of uom code `u` (`0 <= u <= U`): the start of the unit's first run (`n` for `u == U`).
pub open spec fn unit_row(parts: Seq<PartView>, u: int) -> int {
    u64s(parts, P_RUN_START)[u64s(parts, P_UOM_RUNS)[u] as int] as int
}

/// The row positions `lo, lo + 1, .., hi - 1`.
pub open spec fn span(lo: int, hi: int) -> Seq<u64> {
    Seq::new((hi - lo) as nat, |k: int| (lo + k) as u64)
}

/// The value order of unit `u`: positions `[lo, hi)` of `vorder` are the rows `[lo, hi)` (same multiset), with
/// nonincreasing values.
pub open spec fn unit_order_ok(parts: Seq<PartView>, u: int) -> bool {
    let vo = u64s(parts, P_VORDER);
    let value = i128_part(parts[P_VALUE as int]);
    let lo = unit_row(parts, u);
    let hi = unit_row(parts, u + 1);
    &&& 0 <= lo <= hi <= vo.len()
    &&& vo.subrange(lo, hi).to_multiset() == span(lo, hi).to_multiset()
    &&& forall|p: int, q: int| lo <= p < q < hi ==> #[trigger] value[vo[p] as int] >= #[trigger] value[vo[q] as int]
}

/// `vorder` has one entry per stored row and orders every unit's rows by value descending.
pub open spec fn vorder_ok(parts: Seq<PartView>) -> bool {
    &&& u64s(parts, P_VORDER).len() == row_count(parts)
    &&& forall|u: int| 0 <= u < uom_count(parts) ==> #[trigger] unit_order_ok(parts, u)
}

pub open spec fn u64s(parts: Seq<PartView>, p: usize) -> Seq<u64> {
    u64_part(parts[p as int])
}

/// Row count `n`.
pub open spec fn row_count(parts: Seq<PartView>) -> int {
    u64s(parts, P_ORIG).len() as int
}

/// Run count `R`.
pub open spec fn run_count(parts: Seq<PartView>) -> int {
    u64s(parts, P_RUN_UOM).len() as int
}

/// Dictionary sizes.
pub open spec fn uom_count(parts: Seq<PartView>) -> int { text_count(parts, P_UOM_OFF as int) }
pub open spec fn adsh_count(parts: Seq<PartView>) -> int { text_count(parts, P_ADSH_OFF as int) }
pub open spec fn tag_count(parts: Seq<PartView>) -> int { text_count(parts, P_TAG_OFF as int) }
pub open spec fn version_count(parts: Seq<PartView>) -> int { text_count(parts, P_VERSION_OFF as int) }
pub open spec fn pair_count(parts: Seq<PartView>) -> int { u64s(parts, P_PAIR_TAG).len() as int }

/// Dictionary value `k` of the text list in parts `po` (offsets), `po + 1` (bytes).
pub open spec fn dict_entry(parts: Seq<PartView>, po: usize, k: int) -> Seq<u8> {
    text_entry(u64_part(parts[po as int]), u8_part(parts[po + 1]), k)
}

/// Parts `po`, `po + 1` hold a sorted dictionary.
pub open spec fn dict_ok(parts: Seq<PartView>, po: usize) -> bool {
    &&& text_count(parts, po as int) >= 0
    &&& text_col_ok(parts, po as int, po + 1, text_count(parts, po as int))
    &&& text_strictly_sorted(u64_part(parts[po as int]), u8_part(parts[po + 1]), text_count(parts, po as int))
}

/// `tag` and `version` of stored row `i` (bytes).
pub open spec fn tag_of(parts: Seq<PartView>, i: int) -> Seq<u8> {
    dict_entry(parts, P_TAG_OFF, u64s(parts, P_PAIR_TAG)[u64s(parts, P_TV)[i] as int] as int)
}

pub open spec fn version_of(parts: Seq<PartView>, i: int) -> Seq<u8> {
    dict_entry(parts, P_VERSION_OFF, u64s(parts, P_PAIR_VERSION)[u64s(parts, P_TV)[i] as int] as int)
}

/// `adsh` and `uom` of the rows of run `r` (bytes).
pub open spec fn run_adsh_of(parts: Seq<PartView>, r: int) -> Seq<u8> {
    dict_entry(parts, P_ADSH_OFF, u64s(parts, P_RUN_ADSH)[r] as int)
}

pub open spec fn run_uom_of(parts: Seq<PartView>, r: int) -> Seq<u8> {
    dict_entry(parts, P_UOM_OFF, u64s(parts, P_RUN_UOM)[r] as int)
}

/// A sparse nullable text column at canonical row `j`: its listed value, or NULL.
pub open spec fn sparse_at(parts: Seq<PartView>, prows: usize, j: int) -> Val {
    let rows = u64s(parts, prows);
    if sparse_has(rows, j) {
        Val::Text(text_entry(u64_part(parts[prows + 1]), u8_part(parts[prows + 2]), sparse_index(rows, j)))
    } else {
        Val::Null
    }
}

/// Parts `prows`, `prows + 1`, `prows + 2` hold a sparse nullable text column of `n` rows.
pub open spec fn sparse_ok(parts: Seq<PartView>, prows: usize, n: int) -> bool {
    &&& parts[prows as int] is U64
    &&& sparse_rows_ok(u64s(parts, prows), n)
    &&& text_col_ok(parts, prows + 1, prows + 2, u64s(parts, prows).len() as int)
}

/// Every part has its type, length and order facts.
pub open spec fn num_layout_ok(parts: Seq<PartView>) -> bool {
    let n = row_count(parts);
    let nr = run_count(parts);
    let orig = u64s(parts, P_ORIG);
    let start = u64s(parts, P_RUN_START);
    let run_uom = u64s(parts, P_RUN_UOM);
    let run_adsh = u64s(parts, P_RUN_ADSH);
    let tv = u64s(parts, P_TV);
    let pair_tag = u64s(parts, P_PAIR_TAG);
    let pair_version = u64s(parts, P_PAIR_VERSION);
    let ddate = i32_part(parts[P_DDATE as int]);
    &&& parts.len() == PART_COUNT
    &&& parts[P_VORDER as int] is U64
    &&& vorder_ok(parts)
    &&& parts[P_ORIG as int] is U64 && parts[P_RUN_START as int] is U64 && parts[P_RUN_UOM as int] is U64
    &&& parts[P_RUN_ADSH as int] is U64 && parts[P_UOM_RUNS as int] is U64 && parts[P_TV as int] is U64
    &&& parts[P_PAIR_TAG as int] is U64 && parts[P_PAIR_VERSION as int] is U64
    &&& parts[P_DDATE as int] is I32 && parts[P_VALUE as int] is I128 && parts[P_QTRS as int] is I32
    &&& parts[P_RUN_DDATE_MIN as int] is I32 && parts[P_RUN_DDATE_MAX as int] is I32
    &&& is_permutation(orig, n as nat)
    &&& runs_partition_ok(start, nr, n)
    &&& run_adsh.len() == nr
    &&& pairs_increasing(run_uom, run_adsh)
    &&& forall|r: int| 0 <= r < nr ==> #[trigger] run_uom[r] < uom_count(parts) && run_adsh[r] < adsh_count(parts)
    &&& group_starts_ok(u64s(parts, P_UOM_RUNS), run_uom, uom_count(parts))
    &&& dict_ok(parts, P_UOM_OFF) && dict_ok(parts, P_ADSH_OFF) && dict_ok(parts, P_TAG_OFF) && dict_ok(parts, P_VERSION_OFF)
    &&& tv.len() == n
    &&& forall|i: int| 0 <= i < n ==> #[trigger] tv[i] < pair_count(parts)
    &&& pairs_increasing(pair_tag, pair_version)
    &&& forall|p: int| 0 <= p < pair_count(parts) ==> #[trigger] pair_tag[p] < tag_count(parts) && pair_version[p] < version_count(parts)
    &&& forall|r: int, i: int, j: int| #![trigger start[r], tv[i], tv[j]] 0 <= r < nr && start[r] <= i < j < start[r + 1] ==> tv[i] <= tv[j]
    &&& ddate.len() == n
    &&& i128_part(parts[P_VALUE as int]).len() == n
    &&& run_bounds_ok(ddate, start, i32_part(parts[P_RUN_DDATE_MIN as int]), i32_part(parts[P_RUN_DDATE_MAX as int]))
    &&& i32_part(parts[P_QTRS as int]).len() == n
    &&& sparse_ok(parts, P_COREG_ROWS, n)
    &&& sparse_ok(parts, P_FOOTNOTE_ROWS, n)
}

/// The relation row stored at position `i`.
pub open spec fn stored_row(parts: Seq<PartView>, rels: Seq<Seq<Row>>, i: int) -> Row {
    rels[0][u64s(parts, P_ORIG)[i] as int]
}

/// Columns of the row stored at `i` held per stored row: tag, version, ddate, value.
pub open spec fn stored_cols_ok(parts: Seq<PartView>, row: Row, i: int) -> bool {
    &&& row.len() == 9
    &&& row[1] == Val::Text(tag_of(parts, i))
    &&& row[2] == Val::Text(version_of(parts, i))
    &&& row[3] == Val::Int(i32_part(parts[P_DDATE as int])[i] as int)
    &&& row[7] == Val::Num { coeff: i128_part(parts[P_VALUE as int])[i] as int, scale: 4 }
}

/// Columns held per run: adsh and uom of every row of run `r`.
pub open spec fn run_cols_ok(parts: Seq<PartView>, row: Row, r: int) -> bool {
    &&& row[0] == Val::Text(run_adsh_of(parts, r))
    &&& row[5] == Val::Text(run_uom_of(parts, r))
}

/// Columns held in canonical row order: qtrs, coreg, footnote of canonical row `j`.
pub open spec fn canon_cols_ok(parts: Seq<PartView>, row: Row, j: int) -> bool {
    &&& row[4] == Val::Int(i32_part(parts[P_QTRS as int])[j] as int)
    &&& row[6] == sparse_at(parts, P_COREG_ROWS, j)
    &&& row[8] == sparse_at(parts, P_FOOTNOTE_ROWS, j)
}

/// The parts hold the `num` relation: canonical row `orig[i]` is stored at `i`.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    let n = row_count(parts);
    let start = u64s(parts, P_RUN_START);
    &&& num_layout_ok(parts)
    &&& rels.len() == 1
    &&& rels[0].len() == n
    &&& forall|i: int| 0 <= i < n ==> #[trigger] stored_cols_ok(parts, stored_row(parts, rels, i), i)
    &&& forall|r: int, i: int| 0 <= r < run_count(parts) && start[r] <= i < start[r + 1]
        ==> #[trigger] run_cols_ok(parts, stored_row(parts, rels, i), r)
    &&& forall|j: int| 0 <= j < n ==> #[trigger] canon_cols_ok(parts, rels[0][j], j)
}

/// Two rows with the same column facts at the same positions are equal.
proof fn lemma_row_determined(parts: Seq<PartView>, x: Row, y: Row, i: int, r: int, j: int)
    requires
        stored_cols_ok(parts, x, i), stored_cols_ok(parts, y, i),
        run_cols_ok(parts, x, r), run_cols_ok(parts, y, r),
        canon_cols_ok(parts, x, j), canon_cols_ok(parts, y, j),
    ensures x == y,
{
    assert(x =~= y);
}

/// Lossless: every value of every canonical row is a function of the parts.
#[verifier::spinoff_prover]
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    let n = row_count(parts);
    let orig = u64s(parts, P_ORIG);
    let start = u64s(parts, P_RUN_START);
    let nr = run_count(parts);
    lemma_permutation_facts(orig, n as nat);
    assert forall|j: int| 0 <= j < n implies #[trigger] a[0][j] == b[0][j] by {
        let i = position_of(orig, j);
        lemma_run_of(start, nr, n, i);
        let r = run_of(start, nr, i);
        assert(stored_row(parts, a, i) == a[0][j] && stored_row(parts, b, i) == b[0][j]);
        assert(stored_cols_ok(parts, stored_row(parts, a, i), i));
        assert(stored_cols_ok(parts, stored_row(parts, b, i), i));
        assert(run_cols_ok(parts, stored_row(parts, a, i), r));
        assert(run_cols_ok(parts, stored_row(parts, b, i), r));
        assert(canon_cols_ok(parts, a[0][j], j));
        assert(canon_cols_ok(parts, b[0][j], j));
        lemma_row_determined(parts, a[0][j], b[0][j], i, r, j);
    }
    assert(a[0] =~= b[0]);
    assert(a =~= b);
}

/// The stored rows, read in stored order, have the multiset of the relation (order-independent results such as
/// sums, counts and groups over the stored order equal those over the relation).
pub proof fn lemma_stored_rows_multiset(parts: Seq<PartView>, rels: Seq<Seq<Row>>)
    requires represents(parts, rels),
    ensures
        Seq::new(row_count(parts) as nat, |i: int| stored_row(parts, rels, i)).to_multiset() == rels[0].to_multiset(),
{
    let n = row_count(parts);
    common::perm::lemma_permuted_multiset(u64s(parts, P_ORIG), rels[0]);
    assert(Seq::new(n as nat, |i: int| stored_row(parts, rels, i))
        =~= Seq::new(rels[0].len(), |i: int| rels[0][u64s(parts, P_ORIG)[i] as int]));
}

/// The runs of uom code `u` are exactly `[uom_runs[u], uom_runs[u + 1])`.
pub proof fn lemma_uom_runs(parts: Seq<PartView>, u: int)
    requires num_layout_ok(parts), 0 <= u < uom_count(parts),
    ensures
        u64s(parts, P_UOM_RUNS)[u] <= u64s(parts, P_UOM_RUNS)[u + 1] <= run_count(parts),
        forall|r: int| 0 <= r < run_count(parts) ==> (#[trigger] u64s(parts, P_RUN_UOM)[r] == u
            <==> u64s(parts, P_UOM_RUNS)[u] <= r < u64s(parts, P_UOM_RUNS)[u + 1]),
{
    let g = u64s(parts, P_UOM_RUNS);
    let k0 = u64s(parts, P_RUN_UOM);
    assert(g[u] <= k0.len() && g[u + 1] <= k0.len());
    if g[u] > g[u + 1] {
        let r = g[u + 1] as int;
        assert(r < g[u] <==> k0[r] < u);
        assert(r < g[u + 1] <==> k0[r] < u + 1);
    }
    assert forall|r: int| 0 <= r < run_count(parts) implies (#[trigger] k0[r] == u <==> g[u] <= r < g[u + 1]) by {
        assert(r < g[u] <==> k0[r] < u);
        assert(r < g[u + 1] <==> k0[r] < u + 1);
    }
}

/// Number of rows.
pub fn read_row_count(st: &StoredParts) -> (n: usize)
    requires num_layout_ok(st@),
    ensures n == row_count(st@),
{
    st.part_len(P_ORIG)
}

/// Number of runs.
pub fn read_run_count(st: &StoredParts) -> (n: usize)
    requires num_layout_ok(st@),
    ensures n == run_count(st@),
{
    st.part_len(P_RUN_UOM)
}

} // verus!
