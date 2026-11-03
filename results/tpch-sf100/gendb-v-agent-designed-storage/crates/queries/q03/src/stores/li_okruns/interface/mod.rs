//! Storage `li_okruns`: storage `facts` (lineitem, orders) with its 75 parts unchanged, extended by the run offsets
//! of lineitem's l_orderkey column in facts' stored row order:
//! - part `RUN_STARTS` (U32 `st`, at least one entry, `st[0] == 0`): for every run `k < st.len() - 1` the stored
//!   rows `[st[k], st[k + 1])` are nonempty, inside the table and share one l_orderkey, and the row after the run (if
//!   any) has another key (`run_ok`). Built over a full table the runs cover it (`st` ends with the row count); the
//!   one-entry fallback `[0]` (no runs) is allowed too.
//! A query that relies on run `k` belonging to some order checks the key at `st[k]` at run time.
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::Row;
use crate::stores::facts::interface as fi;
use fi::common::colfmt::{u32s, u64s, i64s};

verus! {

/// Parts of storage facts, kept unchanged in front.
pub const FACTS_PARTS: usize = 75;
/// U32 `st`: the run starts, then the row count.
pub const RUN_STARTS: usize = 75;
/// Number of parts of storage li_okruns.
pub const LI_OKRUNS_PARTS: usize = 76;

/// Rows of lineitem (its layout part).
pub open spec fn li_rows(parts: Seq<PartView>) -> int {
    u64s(parts[fi::LI_LAYOUT as int])[0] as int
}

/// Rows per group of lineitem (its layout part).
pub open spec fn li_bsize(parts: Seq<PartView>) -> int {
    u64s(parts[fi::LI_LAYOUT as int])[1] as int
}

/// l_orderkey of stored lineitem row `s` (frame-of-reference: group base + code).
pub open spec fn okey_at(parts: Seq<PartView>, s: int) -> int {
    i64s(parts[fi::LI_ORDERKEY_BASE as int])[s / li_bsize(parts)] + u32s(parts[fi::LI_ORDERKEY_CODES as int])[s]
}

/// The run starts.
pub open spec fn starts(parts: Seq<PartView>) -> Seq<u32> {
    u32s(parts[RUN_STARTS as int])
}

/// Number of runs.
pub open spec fn nruns(parts: Seq<PartView>) -> int {
    starts(parts).len() - 1
}

/// Run `k`: rows `[st[k], st[k + 1])`, nonempty, inside the table, one key, and a different key right after it.
pub open spec fn run_ok(parts: Seq<PartView>, k: int) -> bool {
    let a = starts(parts)[k] as int;
    let b = starts(parts)[k + 1] as int;
    &&& a < b <= li_rows(parts)
    &&& forall|s: int| a <= s < b ==> #[trigger] okey_at(parts, s) == okey_at(parts, a)
    &&& b < li_rows(parts) ==> okey_at(parts, b) != okey_at(parts, b - 1)
}

/// The run offsets part.
pub open spec fn runs_ok(parts: Seq<PartView>) -> bool {
    &&& parts[RUN_STARTS as int] is U32
    &&& starts(parts).len() >= 1
    &&& starts(parts)[0] == 0
    &&& forall|k: int| 0 <= k < nruns(parts) ==> #[trigger] run_ok(parts, k)
}

/// The facts parts hold lineitem and orders (facts' `represents`), the last part the run offsets.
pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool {
    &&& parts.len() == LI_OKRUNS_PARTS
    &&& fi::represents(parts.subrange(0, FACTS_PARTS as int), rels)
    &&& runs_ok(parts)
}

/// The parts determine the relations they represent.
pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>)
    requires represents(parts, a), represents(parts, b),
    ensures a == b,
{
    fi::lemma_represents_determines(parts.subrange(0, FACTS_PARTS as int), a, b);
}

} // verus!
