//! Storage `li_ordruns`: storage `facts` unchanged (its 75 parts, inherited, described by facts' own `represents`),
//! followed by one part: the run lengths of l_orderkey along the stored lineitem rows.
//!
//! facts stores lineitem grouped by order (co-clustered with orders), so equal l_orderkey values form runs of
//! consecutive stored rows. Part `RUN_LENS` (U8) is the run-length encoding of that column's layout: entry `r` is the
//! number of stored lineitem rows of the `r`-th maximal run of equal l_orderkey (`runs_ok`):
//! - run `r` covers stored rows `[run_start(r), run_start(r + 1))`, with `run_start(r)` the sum of the first `r`
//!   lengths, and the runs cover every stored row exactly once (`run_start(len) == rows`);
//! - every length is at least 1, every row of a run has the l_orderkey of the run's first row (`run_same`);
//! - runs are maximal: the first row of run `r > 0` has another l_orderkey than the last row of run `r - 1`
//!   (`run_split`).
//! The part is empty when some run is longer than 255 rows (or lineitem is empty): then it states nothing.
//! It stores no key value, no position and nothing of another table: only row counts of lineitem's own layout. A
//! query that pairs run `r` with stored orders row `r` must establish that pairing itself (for example from the
//! co-clustering flag of facts, the orders key and the run count).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::{Row, Val};
use crate::stores::facts::interface as F;

verus! {

/// Part of the run lengths (U8, one per run).
pub const RUN_LENS: usize = 75;
/// Number of parts of storage li_ordruns.
pub const LI_ORDRUNS_PARTS: usize = 76;
/// Longest run a U8 length holds.
pub const MAX_RUN: usize = 255;

/// The inherited parts (storage facts).
pub open spec fn facts_parts(parts: Seq<PartView>) -> Seq<PartView> {
    parts.subrange(0, F::FACTS_PARTS as int)
}

/// The run lengths.
pub open spec fn run_lens(parts: Seq<PartView>) -> Seq<u8> {
    match parts[RUN_LENS as int] {
        PartView::U8(s) => s,
        _ => Seq::empty(),
    }
}

/// The stored lineitem rows of facts (stored order, every stored column; column 0 is l_orderkey).
pub open spec fn stored_lines(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> Seq<Row> {
    F::lineitem_rows(facts_parts(parts).subrange(F::LINEITEM_FIRST as int, (F::LINEITEM_FIRST + F::LI_PARTS) as int), rels[0])
}

/// First stored row of run `r`: the sum of the first `r` run lengths.
pub open spec fn run_start(rl: Seq<u8>, r: int) -> int
    decreases r,
{
    if r <= 0 {
        0
    } else {
        run_start(rl, r - 1) + rl[r - 1]
    }
}

/// Row `i` of run `r` has the l_orderkey of the run's first row.
pub open spec fn run_same(rows: Seq<Row>, rl: Seq<u8>, r: int, i: int) -> bool {
    rows[run_start(rl, r) + i][0] == rows[run_start(rl, r)][0]
}

/// Run `r` starts with another l_orderkey than the row before it.
pub open spec fn run_split(rows: Seq<Row>, rl: Seq<u8>, r: int) -> bool {
    rows[run_start(rl, r)][0] != rows[run_start(rl, r) - 1][0]
}

/// The run lengths are the maximal runs of equal column 0 along `rows` (or empty, stating nothing).
pub open spec fn runs_ok(rows: Seq<Row>, rl: Seq<u8>) -> bool {
    rl.len() > 0 ==> {
        &&& run_start(rl, rl.len() as int) == rows.len()
        &&& forall|r: int| 0 <= r < rl.len() ==> #[trigger] rl[r] >= 1
        &&& forall|r: int, i: int| 0 <= r < rl.len() && 0 <= i < rl[r] ==> #[trigger] run_same(rows, rl, r, i)
        &&& forall|r: int| 0 < r < rl.len() ==> #[trigger] run_split(rows, rl, r)
    }
}

/// facts' relations in the inherited parts, then the run lengths of the stored lineitem rows.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& parts.len() == LI_ORDRUNS_PARTS
    &&& F::represents(facts_parts(parts), rels)
    &&& parts[RUN_LENS as int] is U8
    &&& runs_ok(stored_lines(parts, rels), run_lens(parts))
}

/// The parts determine the relations they represent (facts is lossless).
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    F::lemma_represents_determines(facts_parts(parts), a, b);
}

/// One more run: the start of run `r + 1` is the start of run `r` plus its length.
pub proof fn lemma_run_start_next(rl: Seq<u8>, r: int)
    requires 0 <= r,
    ensures run_start(rl, r + 1) == run_start(rl, r) + rl[r],
{
}

/// Run starts never decrease, and grow by at least one per nonempty run.
pub proof fn lemma_run_start_mono(rl: Seq<u8>, a: int, b: int)
    requires
        0 <= a <= b <= rl.len(),
        forall|r: int| 0 <= r < rl.len() ==> #[trigger] rl[r] >= 1,
    ensures
        run_start(rl, a) + (b - a) <= run_start(rl, b),
    decreases b - a,
{
    if a < b {
        lemma_run_start_mono(rl, a, b - 1);
        assert(rl[b - 1] >= 1);
    }
}

/// Run starts of a prefix are those of the whole sequence.
pub proof fn lemma_run_start_prefix(rl: Seq<u8>, m: Seq<u8>, r: int)
    requires
        0 <= r <= m.len() <= rl.len(),
        m == rl.subrange(0, m.len() as int),
    ensures
        run_start(m, r) == run_start(rl, r),
    decreases r,
{
    if r > 0 {
        lemma_run_start_prefix(rl, m, r - 1);
    }
}

} // verus!
