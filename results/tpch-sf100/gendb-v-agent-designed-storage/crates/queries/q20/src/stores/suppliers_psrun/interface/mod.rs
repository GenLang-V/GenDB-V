//! Storage `suppliers_psrun`: storage `suppliers` (partsupp, supplier, nation, region) with its parts unchanged in
//! front, extended by part `RUN` (I64 `[ratio, first]`), the run layout of partsupp's ps_partkey: when
//! `ratio >= 1`, partsupp row `k` has ps_partkey `first + k / ratio` (every key one run of `ratio` rows, keys
//! consecutive from `first`); `ratio == 0` states nothing.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::{Row, Val};
use crate::stores::suppliers::interface as si;

verus! {

/// Parts of storage suppliers, kept unchanged in front.
pub const SUPPLIERS_PARTS: usize = 48;
/// I64 `[ratio, first]`: the run layout of ps_partkey.
pub const RUN: usize = 48;
/// Number of parts of storage suppliers_psrun.
pub const PSRUN_PARTS: usize = 49;

/// The values of an I64 part (empty for another kind).
pub open spec fn run_i64s(p: PartView) -> Seq<i64> {
    match p {
        PartView::I64(s) => s,
        _ => Seq::empty(),
    }
}

/// The run layout `[ratio, first]` over the partsupp rows `ps`: with `ratio >= 1`, row `k` has ps_partkey
/// `first + k / ratio`.
pub open spec fn run_ok(run: Seq<i64>, ps: Seq<Row>) -> bool {
    &&& run.len() == 2
    &&& run[0] >= 1 ==> forall|k: int| 0 <= k < ps.len() ==> #[trigger] ps[k][0] == Val::Int(run[1] + k / (run[0] as int))
}

/// The suppliers parts hold partsupp, supplier, nation and region (suppliers' `represents`), the last part their
/// ps_partkey run layout.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& parts.len() == PSRUN_PARTS
    &&& si::represents(parts.subrange(0, SUPPLIERS_PARTS as int), rels)
    &&& parts[RUN as int] is I64
    &&& run_ok(run_i64s(parts[RUN as int]), rels[0])
}

/// The parts determine the relations they represent (those of suppliers).
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    si::lemma_represents_determines(parts.subrange(0, SUPPLIERS_PARTS as int), a, b);
}

} // verus!
