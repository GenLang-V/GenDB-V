//! Group accumulators of the scan's entries and their equality with the anti-join's accumulators over the num rows.
//!
//! `ecount`/`esum`/`eabs` count, sum and absolutely sum the entries whose pair code has group key `k`. Over the
//! stored rows (in stored order) the anti-join's `gcount`/`gsum`/`gabs` of key `k` equal those of the scan's entries
//! of the runs of uom `$1` (rows of other runs never qualify), and over the canonical rows they are the same (the
//! stored order is a permutation).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::numeric::abs;
use crate::gendb_entry::layout::PartView;
use crate::stores::num_tvg::interface as N;
use crate::stores::pre::interface as P;
use crate::stores::num_tvg::interface::common::runs::{run_of, lemma_run_of};
use crate::link::query::{QuerySpec, gcount, gsum, gabs, hit, lemma_range_step, lemma_split, lemma_empty, lemma_full_range};
use crate::link::join::{sum_of, count_term, sum_term, abs_term, lemma_acc_sum_of, lemma_sum_of_perm};
use super::scan::{ScanInput, Entry};
use super::common::groupby::{pcount, psum, pabs, tsum, cnt_f, sum_f, abs_f};
use super::stored::*;
use super::model::*;

verus! {

/// Entries of group `k`: their number, value sum and absolute value sum.
pub open spec fn ecount(np: Seq<PartView>, es: Seq<Entry>, k: Row) -> nat
    decreases es.len(),
{
    if es.len() == 0 { 0 } else {
        ecount(np, es.drop_last(), k) + if keyp(np, es.last().key as int) == k { 1nat } else { 0nat }
    }
}

pub open spec fn esum(np: Seq<PartView>, es: Seq<Entry>, k: Row) -> int
    decreases es.len(),
{
    if es.len() == 0 { 0 } else {
        esum(np, es.drop_last(), k) + if keyp(np, es.last().key as int) == k { es.last().value as int } else { 0 }
    }
}

pub open spec fn eabs(np: Seq<PartView>, es: Seq<Entry>, k: Row) -> int
    decreases es.len(),
{
    if es.len() == 0 { 0 } else {
        eabs(np, es.drop_last(), k) + if keyp(np, es.last().key as int) == k { abs(es.last().value as int) } else { 0 }
    }
}

pub proof fn lemma_e_append(np: Seq<PartView>, a: Seq<Entry>, b: Seq<Entry>, k: Row)
    ensures
        ecount(np, a + b, k) == ecount(np, a, k) + ecount(np, b, k),
        esum(np, a + b, k) == esum(np, a, k) + esum(np, b, k),
        eabs(np, a + b, k) == eabs(np, a, k) + eabs(np, b, k),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        lemma_e_append(np, a, b.drop_last(), k);
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
    }
}

/// The stored rows in stored order.
pub open spec fn srows(np: Seq<PartView>, rn: Seq<Seq<Row>>) -> Seq<Row> {
    Seq::new(N::row_count(np) as nat, |i: int| N::stored_row(np, rn, i))
}

/// The three accumulators of the anti-join over stored rows `[lo, hi)` equal those of `es` at key `k`.
pub open spec fn acc_eq(ps: Seq<Literal>, pre: Seq<Row>, np: Seq<PartView>, rows: Seq<Row>, es: Seq<Entry>, k: Row) -> bool {
    let g = num_spec(ps, pre);
    &&& gcount(g, rows, k) == ecount(np, es, k)
    &&& gsum(g, rows, k, 1) == esum(np, es, k)
    &&& gabs(g, rows, k, 1) == eabs(np, es, k)
}

/// Rows `[s, e')` of run `r` (uom `$1`).
proof fn lemma_acc_rows(np: Seq<PartView>, pp: Seq<PartView>, rn: Seq<Seq<Row>>, rp: Seq<Seq<Row>>, inp: ScanInput,
    ps: Seq<Literal>, r: int, e: int, k: Row)
    requires
        N::represents(np, rn), P::represents(pp, rp), inp_matches(inp, np, pp, ps), inp.wf(),
        0 <= r < inp.runs, inp.run_start@[r] <= e <= inp.run_start@[r + 1],
        N::run_uom_of(np, r) == ukey(ps),
    ensures acc_eq(ps, rp[0], np, srows(np, rn).subrange(inp.run_start@[r] as int, e), inp.row_ents(r, inp.run_start@[r] as int, e), k),
    decreases e - inp.run_start@[r],
{
    let s = inp.run_start@[r] as int;
    let rows = srows(np, rn);
    let g = num_spec(ps, rp[0]);
    assert(inp.run_start@[r + 1] <= inp.run_start@[inp.runs as int]);
    if e == s {
        lemma_empty(g, rows, s, k, 1);
    } else {
        lemma_acc_rows(np, pp, rn, rp, inp, ps, r, e - 1, k);
        lemma_range_step(g, rows, s, e - 1, k, 1);
        lemma_pos_qual(np, pp, rn, rp, inp, ps, r, e - 1);
        let es = inp.row_ents(r, s, e);
        let es0 = inp.row_ents(r, s, e - 1);
        if inp.qual(r, e - 1) {
            assert(es.drop_last() == es0);
        } else {
            assert(es == es0);
        }
        assert(rows[e - 1] == N::stored_row(np, rn, e - 1));
    }
}

/// Runs `[r0, rb)`, all of uom `$1`.
proof fn lemma_acc_runs(np: Seq<PartView>, pp: Seq<PartView>, rn: Seq<Seq<Row>>, rp: Seq<Seq<Row>>, inp: ScanInput,
    ps: Seq<Literal>, r0: int, rb: int, k: Row)
    requires
        N::represents(np, rn), P::represents(pp, rp), inp_matches(inp, np, pp, ps), inp.wf(),
        0 <= r0 <= rb <= inp.runs,
        forall|r: int| r0 <= r < rb ==> #[trigger] N::run_uom_of(np, r) == ukey(ps),
    ensures acc_eq(ps, rp[0], np, srows(np, rn).subrange(inp.run_start@[r0] as int, inp.run_start@[rb] as int),
        inp.run_ents(r0, rb), k),
    decreases rb - r0,
{
    let rows = srows(np, rn);
    let g = num_spec(ps, rp[0]);
    let start = inp.run_start@;
    if rb == r0 {
        assert(start[r0] <= start[inp.runs as int]);
        lemma_empty(g, rows, start[r0] as int, k, 1);
    } else {
        lemma_acc_runs(np, pp, rn, rp, inp, ps, r0, rb - 1, k);
        assert(N::run_uom_of(np, rb - 1) == ukey(ps));
        lemma_acc_rows(np, pp, rn, rp, inp, ps, rb - 1, start[rb] as int, k);
        assert(start[r0] <= start[rb - 1]);
        assert(start[rb] <= start[inp.runs as int]);
        lemma_split(g, rows, start[r0] as int, start[rb - 1] as int, start[rb] as int, k, 1);
        lemma_e_append(np, inp.run_ents(r0, rb - 1), inp.row_ents(rb - 1, start[rb - 1] as int, start[rb] as int), k);
    }
}

/// Stored rows `[lo, hi)` lying in runs of another uom contribute nothing.
proof fn lemma_acc_none(np: Seq<PartView>, rn: Seq<Seq<Row>>, ps: Seq<Literal>, pre: Seq<Row>, lo: int, hi: int, k: Row)
    requires
        N::represents(np, rn), 0 <= lo <= hi <= N::row_count(np),
        forall|r: int| 0 <= r < N::run_count(np) && N::u64s(np, N::P_RUN_START)[r + 1] > lo
            && N::u64s(np, N::P_RUN_START)[r] < hi ==> #[trigger] N::run_uom_of(np, r) != ukey(ps),
    ensures
        gcount(num_spec(ps, pre), srows(np, rn).subrange(lo, hi), k) == 0,
        gsum(num_spec(ps, pre), srows(np, rn).subrange(lo, hi), k, 1) == 0,
        gabs(num_spec(ps, pre), srows(np, rn).subrange(lo, hi), k, 1) == 0,
    decreases hi - lo,
{
    let rows = srows(np, rn);
    let g = num_spec(ps, pre);
    if hi == lo {
        lemma_empty(g, rows, lo, k, 1);
    } else {
        lemma_acc_none(np, rn, ps, pre, lo, hi - 1, k);
        lemma_range_step(g, rows, lo, hi - 1, k, 1);
        let start = N::u64s(np, N::P_RUN_START);
        lemma_run_of(start, N::run_count(np), N::row_count(np), hi - 1);
        let r = run_of(start, N::run_count(np), hi - 1);
        lemma_pos_other_uom(np, rn, ps, pre, r, hi - 1);
        assert(rows[hi - 1] == N::stored_row(np, rn, hi - 1));
    }
}

/// The anti-join accumulators over the canonical num rows are those of the scan's entries of the uom-`$1` runs
/// `[r0, r1)` (the runs of that uom), or zero when no run has uom `$1`.
pub proof fn lemma_acc_all(np: Seq<PartView>, pp: Seq<PartView>, rn: Seq<Seq<Row>>, rp: Seq<Seq<Row>>, inp: ScanInput,
    ps: Seq<Literal>, r0: int, r1: int, es: Seq<Entry>, k: Row)
    requires
        N::represents(np, rn), P::represents(pp, rp), inp_matches(inp, np, pp, ps), inp.wf(),
        0 <= r0 <= r1 <= inp.runs,
        forall|r: int| 0 <= r < inp.runs ==> (#[trigger] N::run_uom_of(np, r) == ukey(ps)) == (r0 <= r < r1),
        es == inp.run_ents(r0, r1),
    ensures acc_eq(ps, rp[0], np, rn[0], es, k),
{
    let rows = srows(np, rn);
    let g = num_spec(ps, rp[0]);
    let start = inp.run_start@;
    let n = N::row_count(np);
    assert(start[r0] <= start[r1] <= start[inp.runs as int]);
    assert forall|r: int| 0 <= r < N::run_count(np) && start[r + 1] > 0 && start[r] < start[r0] implies
        #[trigger] N::run_uom_of(np, r) != ukey(ps) by {
        if r >= r0 {
            assert(start[r0] <= start[r]);
        }
    }
    lemma_acc_none(np, rn, ps, rp[0], 0, start[r0] as int, k);
    assert forall|r: int| 0 <= r < N::run_count(np) && start[r + 1] > start[r1] && start[r] < n implies
        #[trigger] N::run_uom_of(np, r) != ukey(ps) by {
        if r < r1 {
            assert(start[r + 1] <= start[r1]);
        }
    }
    lemma_acc_none(np, rn, ps, rp[0], start[r1] as int, n, k);
    assert forall|r: int| r0 <= r < r1 implies #[trigger] N::run_uom_of(np, r) == ukey(ps) by {}
    lemma_acc_runs(np, pp, rn, rp, inp, ps, r0, r1, k);
    lemma_split(g, rows, 0, start[r0] as int, n, k, 1);
    lemma_split(g, rows, start[r0] as int, start[r1] as int, n, k, 1);
    lemma_full_range(rows);
    // the stored order is a permutation of the canonical rows
    N::lemma_stored_rows_multiset(np, rn);
    assert(rows.to_multiset() == rn[0].to_multiset());
    lemma_acc_sum_of(g, rows, k, 1);
    lemma_acc_sum_of(g, rn[0], k, 1);
    lemma_sum_of_perm(rows, rn[0], count_term(g, k));
    lemma_sum_of_perm(rows, rn[0], sum_term(g, k, 1));
    lemma_sum_of_perm(rows, rn[0], abs_term(g, k, 1));
    lemma_e_append(np, Seq::empty(), es, k);
}


/// With valid pair codes, the entries of group key `keyp(p)` are the entries of pair code `p`.
pub proof fn lemma_e_to_p(np: Seq<PartView>, es: Seq<Entry>, p: u64)
    requires
        N::num_layout_ok(np), p < N::pair_count(np),
        forall|m: int| 0 <= m < es.len() ==> (#[trigger] es[m]).key < N::pair_count(np),
    ensures
        ecount(np, es, keyp(np, p as int)) == pcount(es, p),
        esum(np, es, keyp(np, p as int)) == psum(es, p),
        eabs(np, es, keyp(np, p as int)) == pabs(es, p),
    decreases es.len(),
{
    if es.len() > 0 {
        let ei = es.drop_last();
        assert forall|m: int| 0 <= m < ei.len() implies (#[trigger] ei[m]).key < N::pair_count(np) by {
            assert(ei[m] == es[m]);
        }
        lemma_e_to_p(np, ei, p);
        let x = es.last();
        assert(x == es[es.len() - 1]);
        if keyp(np, x.key as int) == keyp(np, p as int) {
            assert(ntag_str(np, x.key as int) == keyp(np, x.key as int)[0]->Text_0);
            assert(nver_str(np, x.key as int) == keyp(np, x.key as int)[1]->Text_0);
            lemma_npair_inj(np, x.key as int, p as int);
        }
    }
}

/// A key that no entry has accumulates nothing.
pub proof fn lemma_e_zero(np: Seq<PartView>, es: Seq<Entry>, k: Row)
    requires forall|m: int| 0 <= m < es.len() ==> keyp(np, (#[trigger] es[m]).key as int) != k,
    ensures ecount(np, es, k) == 0, esum(np, es, k) == 0, eabs(np, es, k) == 0,
    decreases es.len(),
{
    if es.len() > 0 {
        let ei = es.drop_last();
        assert forall|m: int| 0 <= m < ei.len() implies keyp(np, (#[trigger] ei[m]).key as int) != k by {
            assert(ei[m] == es[m]);
        }
        lemma_e_zero(np, ei, k);
        assert(es.last() == es[es.len() - 1]);
    }
}

/// The count of a group is at most the number of entries.
pub proof fn lemma_ecount_le(np: Seq<PartView>, es: Seq<Entry>, k: Row)
    ensures ecount(np, es, k) <= es.len(),
    decreases es.len(),
{
    if es.len() > 0 {
        lemma_ecount_le(np, es.drop_last(), k);
    }
}

/// A group with entries has an entry of its key.
pub proof fn lemma_ecount_witness(np: Seq<PartView>, es: Seq<Entry>, k: Row)
    requires ecount(np, es, k) > 0,
    ensures exists|m: int| 0 <= m < es.len() && keyp(np, (#[trigger] es[m]).key as int) == k,
{
    if !(exists|m: int| 0 <= m < es.len() && keyp(np, (#[trigger] es[m]).key as int) == k) {
        lemma_e_zero(np, es, k);
    }
}

} // verus!

