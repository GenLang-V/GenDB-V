//! The l_orderkey runs of storage `li_okruns` over the scan model (`model::runs_ok`), and how they are aligned with
//! the stored orders:
//! - `lemma_okruns`: storage `li_okruns` gives facts' `represents` over its first 75 parts (`bind::fpv`) and its run
//!   starts; `lemma_runs_model` restates the run contract over the model's decoded order keys;
//! - under co-clustering (`clus_ok`) the stored orders rows of consecutive runs strictly increase while they are
//!   orders rows (`lemma_pos_step`), so when the first and the last run of a range `[q, r]` start with the key of
//!   the orders row of the same index, every run between does too (`lemma_aligned_range`): run `k` is then the
//!   lines of orders row `k`, and a line of run `k` has the customer class of orders row `k` (`lemma_line_run`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stores::StoresView;
use crate::spec::value::*;
use crate::stores::facts::interface::*;
use crate::stores::facts::interface::common::colfmt::*;
use crate::stores::li_okruns::interface as lr;
use crate::stores::li_okruns::declaration as lrd;
use crate::stores::facts::declaration as fd;
use super::common::incseq::*;
use super::model::*;
use super::bind::*;
use super::open::*;
use super::kernel::{q_cls, lemma_line_order};

verus! {

// ------------------------------------------------------------------------------------------------ binding

/// li_okruns' stored relations are facts' (the same declaration).
proof fn lemma_same_relations(db: Database)
    ensures lrd::stored_relations(db) == fd::stored_relations(db),
{
    assert(lrd::stored_cols_t0() =~= fd::stored_cols_t0());
    assert(lrd::stored_cols_t1() =~= fd::stored_cols_t1());
    assert(lrd::stored_relations(db) =~= fd::stored_relations(db));
}

/// Storage `li_okruns` gives facts' `represents` over its first 75 parts, and its run starts.
pub proof fn lemma_okruns(sv: StoresView, db: Database)
    requires lr::represents(sv.li_okruns, lrd::stored_relations(db)),
    ensures
        represents(fpv(sv), fd::stored_relations(db)),
        runs_kind(sv),
        lr::runs_ok(sv.li_okruns),
{
    lemma_same_relations(db);
}

/// The model's order key of line `s` is li_okruns' `okey_at`.
proof fn lemma_lkey_at(sv: StoresView, c: Cols, s: int)
    requires
        li_from_parts(c, fpv(sv)), li_kinds(fpv(sv)), runs_kind(sv),
        0 <= s < c.n_l,
    ensures lkey(c, s) == lr::okey_at(sv.li_okruns, s),
{
    let p = sv.li_okruns;
    let f = fpv(sv);
    assert(ltp(f)[LI_LAYOUT as int] == p[LI_LAYOUT as int]);
    assert(ltp(f)[LI_ORDERKEY_CODES as int] == p[LI_ORDERKEY_CODES as int]);
    assert(ltp(f)[LI_ORDERKEY_BASE as int] == p[LI_ORDERKEY_BASE as int]);
    assert(ltp(f)[LI_LAYOUT as int] == f[LI_LAYOUT as int]);
    lemma_bs_group(c.bs_l as int, lr::li_bsize(p), c.n_l as int, s);
}

/// The run starts of storage `li_okruns` are correct runs of the model (`runs_ok`).
pub proof fn lemma_runs_model(sv: StoresView, c: Cols)
    requires
        li_from_parts(c, fpv(sv)), li_kinds(fpv(sv)), runs_kind(sv),
        lr::runs_ok(sv.li_okruns),
        PartView::U32(c.l_st@) == sv.li_okruns[lr::RUN_STARTS as int],
        c.n_st == c.l_st@.len(),
    ensures runs_ok(c),
{
    let p = sv.li_okruns;
    let f = fpv(sv);
    assert(lr::starts(p) == c.l_st@);
    assert(ltp(f)[LI_LAYOUT as int] == p[LI_LAYOUT as int]);
    assert(lr::li_rows(p) == c.n_l);
    assert forall|k: int| 0 <= k < c.l_st@.len() - 1 implies #[trigger] run_ok(c, k) by {
        assert(lr::run_ok(p, k));
        let a = c.l_st@[k] as int;
        let b = c.l_st@[k + 1] as int;
        lemma_lkey_at(sv, c, a);
        assert forall|s: int| a <= s < b implies #[trigger] lkey(c, s) == lkey(c, a) by {
            lemma_lkey_at(sv, c, s);
            assert(lr::okey_at(p, s) == lr::okey_at(p, a));
        }
        if b < c.n_l {
            lemma_lkey_at(sv, c, b);
            lemma_lkey_at(sv, c, b - 1);
        }
    }
}

// ------------------------------------------------------------------------------------------------ alignment

/// The run starts strictly increase.
pub proof fn lemma_runs_inc(c: Cols)
    requires runs_ok(c),
    ensures inc(c.l_st@),
{
    assert forall|k: int| 0 <= k < c.l_st@.len() - 1 implies #[trigger] c.l_st@[k] < c.l_st@[k + 1] by {
        assert(run_ok(c, k));
    }
}

/// The stored orders row of the first line of run `k` (`n_o` when its key has no order).
pub open spec fn run_pos(c: Cols, k: int) -> int {
    opos(c, lkey(c, c.l_st@[k] as int))
}

/// Consecutive runs (both inside the table) belong to strictly increasing orders rows while those are rows.
proof fn lemma_pos_step(c: Cols, k: int)
    requires
        runs_ok(c), clus_ok(c),
        0 <= k, k + 2 < c.l_st@.len(),
        run_pos(c, k + 1) < c.n_o,
    ensures
        run_pos(c, k + 1) > run_pos(c, k),
{
    let a = c.l_st@[k] as int;
    let b = c.l_st@[k + 1] as int;
    assert(run_ok(c, k));
    assert(run_ok(c, k + 1));
    assert(lkey(c, b - 1) == lkey(c, a));
    lemma_clus_mono(c, b - 1, b);
    if run_pos(c, k + 1) == run_pos(c, k) {
        // one orders row would hold both keys
        lemma_opos_row(c, lkey(c, b));
        lemma_opos_row(c, lkey(c, b - 1));
    }
}

/// One step of `lemma_pos_gap`: runs up to `r` belong to orders rows, so the row grows from run `j - 1` to `j`.
proof fn lemma_pos_gap_step(c: Cols, j: int, r: int)
    requires
        runs_ok(c), clus_ok(c),
        1 <= j <= r, r + 1 < c.l_st@.len(),
        r < c.n_o, run_pos(c, r) == r,
    ensures
        run_pos(c, j) > run_pos(c, j - 1),
{
    lemma_runs_inc(c);
    lemma_inc(c.l_st@, j, r);
    assert(run_ok(c, r));
    lemma_clus_mono(c, c.l_st@[j] as int, c.l_st@[r] as int);
    lemma_pos_step(c, j - 1);
}

/// Orders rows of runs `[i, j]` grow by at least one per run (run `r` is orders row `r`, `j <= r`).
proof fn lemma_pos_gap(c: Cols, i: int, j: int, r: int)
    requires
        runs_ok(c), clus_ok(c),
        0 <= i <= j <= r, r + 1 < c.l_st@.len(),
        r < c.n_o, run_pos(c, r) == r,
    ensures
        run_pos(c, j) >= run_pos(c, i) + (j - i),
    decreases j - i,
{
    if i < j {
        lemma_pos_gap(c, i, j - 1, r);
        lemma_pos_gap_step(c, j, r);
    }
}

/// Run `k` starts with the key of orders row `k`.
pub open spec fn aligned(c: Cols, k: int) -> bool {
    lkey(c, c.l_st@[k] as int) == okey(c, k)
}

/// When the first and the last run of `[q, r]` start with the keys of orders rows `q` and `r`, every run between
/// starts with the key of the orders row of its index.
pub proof fn lemma_aligned_range(c: Cols, q: int, r: int)
    requires
        runs_ok(c), clus_ok(c), keys_ok(c),
        0 <= q <= r < c.n_o, r + 1 < c.l_st@.len(),
        aligned(c, q), aligned(c, r),
    ensures
        forall|k: int| q <= k <= r ==> #[trigger] aligned(c, k),
{
    lemma_opos_at(c, lkey(c, c.l_st@[q] as int), q);
    lemma_opos_at(c, lkey(c, c.l_st@[r] as int), r);
    assert forall|k: int| q <= k <= r implies #[trigger] aligned(c, k) by {
        lemma_pos_gap(c, q, k, r);
        lemma_pos_gap(c, k, r, r);
        lemma_opos_row(c, lkey(c, c.l_st@[k] as int));
    }
}

/// A line of an aligned run `k` has the customer class of orders row `k`.
pub proof fn lemma_line_run(c: Cols, x: Ctx, k: int, j: int)
    requires
        runs_ok(c), keys_ok(c),
        0 <= k < c.n_o, k + 1 < c.l_st@.len(),
        aligned(c, k),
        c.l_st@[k] <= j < c.l_st@[k + 1],
    ensures o_cls(c, x, lkey(c, j)) == q_cls(c, x, k),
{
    assert(run_ok(c, k));
    assert(lkey(c, j) == lkey(c, c.l_st@[k] as int));
    lemma_line_order(c, x, j, k);
}

} // verus!
