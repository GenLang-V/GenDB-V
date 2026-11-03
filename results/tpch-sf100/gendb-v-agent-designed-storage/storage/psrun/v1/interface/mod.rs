//! Storage `psrun`: storage `suppliers` (partsupp, supplier, nation, region) with its 48 parts unchanged, extended by
//! one part of skip metadata over partsupp's own key column:
//! - part `RUNS` (I64): `runs[0]` is a ratio `r >= 1`; then one entry per block of `RUN_ROWS` partsupp rows (block `b`
//!   is the stored rows `b * RUN_ROWS .. min((b + 1) * RUN_ROWS, rows)`): `NO_RUN`, or a key `k` such that every row
//!   `i` of the block has `ps_partkey == k + (i - b * RUN_ROWS) / r` (`block_run`). Partsupp in key order with `r`
//!   rows per key gives every block a run, so a reader finds the rows of a key inside such a block by arithmetic,
//!   without reading the key column.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::{Row, Val};
use crate::stores::suppliers::interface as si;
use si::common::colfmt::i64s;

verus! {

/// Parts of storage suppliers, kept unchanged in front.
pub const SUPPLIERS_PARTS: usize = 48;
/// I64 `runs`: the ratio, then one entry per block of partsupp rows.
pub const RUNS: usize = 48;
/// Number of parts of storage psrun.
pub const PSRUN_PARTS: usize = 49;
/// Partsupp rows per block of `runs`.
pub const RUN_ROWS: usize = 65536;
/// The entry of a block without a run.
pub const NO_RUN: i64 = -9223372036854775808i64;

/// Number of blocks of `RUN_ROWS` rows over `n` rows.
pub open spec fn run_blocks(n: int) -> int {
    (n + RUN_ROWS as int - 1) / (RUN_ROWS as int)
}

/// Every row `i` of block `b` of the partsupp rows `rel` has key `k + (i - b * RUN_ROWS) / r`.
pub open spec fn block_run(rel: Seq<Row>, b: int, k: int, r: int) -> bool {
    forall|i: int| b * RUN_ROWS <= i < rel.len() && i < b * RUN_ROWS + RUN_ROWS
        ==> #[trigger] rel[i][0] == Val::Int(k + (i - b * RUN_ROWS) / r)
}

/// The runs part over the partsupp rows `rel`: the ratio, and every block's entry `NO_RUN` or its run's first key.
pub open spec fn runs_ok(p: PartView, rel: Seq<Row>) -> bool {
    &&& p is I64
    &&& i64s(p).len() == run_blocks(rel.len() as int) + 1
    &&& i64s(p)[0] >= 1
    &&& forall|b: int| 0 <= b < run_blocks(rel.len() as int) && #[trigger] i64s(p)[b + 1] != NO_RUN
        ==> block_run(rel, b, i64s(p)[b + 1] as int, i64s(p)[0] as int)
}

/// The suppliers parts hold its four tables (suppliers' `represents`), the last part partsupp's key runs.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& parts.len() == PSRUN_PARTS
    &&& si::represents(parts.subrange(0, SUPPLIERS_PARTS as int), rels)
    &&& runs_ok(parts[RUNS as int], rels[0])
}

/// The parts determine the relations they represent.
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    si::lemma_represents_determines(parts.subrange(0, SUPPLIERS_PARTS as int), a, b);
}

} // verus!
