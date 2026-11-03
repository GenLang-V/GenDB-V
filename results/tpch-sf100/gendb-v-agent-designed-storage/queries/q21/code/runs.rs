//! Run lengths of l_orderkey (storage `li_ordruns`) over the Q21 scan model (`super::model`): `rl[r]` is the length of
//! the `r`-th maximal run of equal l_orderkey along the stored lineitem rows, starting at `rstart(r)` (`runs_model`).
//! When there are exactly as many runs as stored orders rows and the last line's order exists, the runs pair up with
//! the orders rows one to one (`lemma_runs_aligned`: run `r` belongs to stored orders row `r`), so the lines of order
//! `p` are the rows of run `p` (`lemma_run_lines`), found without reading l_orderkey. Ported from the admitted Q4 model.
use vstd::prelude::*;
use crate::stores::li_ordruns::interface::{run_start, lemma_run_start_mono, lemma_run_start_next};
use super::model::*;

verus! {


/// First stored lineitem row of run `r`.
pub open spec fn rstart(c: Cols, r: int) -> int {
    run_start(c.rl@, r)
}

/// Row `i` of run `r` has the l_orderkey of the run's first row.
pub open spec fn lsame(c: Cols, r: int, i: int) -> bool {
    lkey(c, rstart(c, r) + i) == lkey(c, rstart(c, r))
}

/// Run `r` starts with another l_orderkey than the row before it.
pub open spec fn lsplit(c: Cols, r: int) -> bool {
    lkey(c, rstart(c, r)) != lkey(c, rstart(c, r) - 1)
}

/// The run lengths are the maximal runs of l_orderkey, one per stored orders row (`n_o` runs).
pub open spec fn runs_model(c: Cols) -> bool {
    &&& c.rl@.len() == c.n_o
    &&& c.n_o > 0
    &&& run_start(c.rl@, c.n_o as int) == c.n_l
    &&& forall|r: int| 0 <= r < c.n_o ==> #[trigger] c.rl@[r] >= 1
    &&& forall|r: int, i: int| 0 <= r < c.n_o && 0 <= i < c.rl@[r] ==> #[trigger] lsame(c, r, i)
    &&& forall|r: int| 0 < r < c.n_o ==> #[trigger] lsplit(c, r)
}

/// Run `r` holds the lines of stored orders row `r`.
pub open spec fn runs_aligned(c: Cols) -> bool {
    forall|r: int| 0 <= r < c.n_o ==> #[trigger] lkey(c, rstart(c, r)) == okey(c, r)
}

/// Runs start inside the table: `rstart(r) + (n_o - r) <= n_l`, and run `r` ends at `rstart(r + 1)`.
pub proof fn lemma_rstart_bounds(c: Cols, r: int)
    requires runs_model(c), 0 <= r <= c.n_o,
    ensures
        0 <= rstart(c, r),
        rstart(c, r) + (c.n_o - r) <= c.n_l,
        r < c.n_o ==> rstart(c, r + 1) == rstart(c, r) + c.rl@[r],
{
    lemma_run_start_mono(c.rl@, r, c.n_o as int);
    lemma_run_start_mono(c.rl@, 0, r);
    if r < c.n_o {
        lemma_run_start_next(c.rl@, r);
    }
}

/// Run starts are nondecreasing.
pub proof fn lemma_rstart_le(c: Cols, a: int, b: int)
    requires runs_model(c), 0 <= a <= b <= c.n_o,
    ensures rstart(c, a) <= rstart(c, b),
{
    lemma_run_start_mono(c.rl@, a, b);
}

/// The order position of run `r`'s key.
pub open spec fn fpos(c: Cols, r: int) -> int {
    rpos(c, lkey(c, rstart(c, r)))
}

/// `fpos` is nondecreasing (the lines follow the orders).
proof fn lemma_fpos_le(c: Cols, a: int, b: int)
    requires runs_model(c), lines_clustered(c), 0 <= a <= b < c.n_o,
    ensures fpos(c, a) <= fpos(c, b),
{
    lemma_rstart_le(c, a, b);
    lemma_rstart_bounds(c, a);
    lemma_rstart_bounds(c, b);
    lemma_lines_le(c, rstart(c, a), rstart(c, b));
}

/// The last run holds the last line, so its order position is that line's.
proof fn lemma_fpos_last(c: Cols)
    requires runs_model(c),
    ensures fpos(c, c.n_o - 1) == rpos(c, lkey(c, c.n_l - 1)),
{
    let r = c.n_o - 1;
    lemma_rstart_bounds(c, r);
    assert(rstart(c, r + 1) == c.n_l);
    assert(lsame(c, r, c.rl@[r] - 1));
}

/// Consecutive runs belong to different orders, when the later one's order exists.
proof fn lemma_fpos_lt(c: Cols, r: int)
    requires
        runs_model(c),
        lines_clustered(c),
        0 <= r < c.n_o - 1,
        fpos(c, r + 1) < c.n_o,
    ensures
        fpos(c, r) < fpos(c, r + 1),
{
    let e = rstart(c, r + 1);
    lemma_rstart_bounds(c, r);
    lemma_rstart_bounds(c, r + 1);
    assert(lsame(c, r, c.rl@[r] - 1));
    assert(lkey(c, e - 1) == lkey(c, rstart(c, r)));
    lemma_lines_le(c, e - 1, e);
    assert(lsplit(c, r + 1));
    if fpos(c, r) == fpos(c, r + 1) {
        lemma_rpos_bound(c, lkey(c, rstart(c, r)));
        lemma_rpos_bound(c, lkey(c, e));
    }
}

/// `fpos(r) >= r` (strictly increasing from 0).
proof fn lemma_fpos_ge(c: Cols, r: int)
    requires
        runs_model(c),
        lines_clustered(c),
        0 <= r < c.n_o,
        fpos(c, c.n_o - 1) < c.n_o,
    ensures
        fpos(c, r) >= r,
    decreases r,
{
    lemma_rpos_bound(c, lkey(c, rstart(c, r)));
    if r > 0 {
        lemma_fpos_ge(c, r - 1);
        lemma_fpos_le(c, r, c.n_o - 1);
        lemma_fpos_lt(c, r - 1);
    }
}

/// `fpos(r) <= r` (strictly increasing up to `n_o - 1`).
proof fn lemma_fpos_le_r(c: Cols, r: int)
    requires
        runs_model(c),
        lines_clustered(c),
        0 <= r < c.n_o,
        fpos(c, c.n_o - 1) < c.n_o,
    ensures
        fpos(c, r) <= r,
    decreases c.n_o - r,
{
    if r < c.n_o - 1 {
        lemma_fpos_le_r(c, r + 1);
        lemma_fpos_le(c, r + 1, c.n_o - 1);
        lemma_fpos_lt(c, r);
    }
}

/// With one run per stored orders row and the last line's order present, run `r` belongs to stored orders row `r`.
pub proof fn lemma_runs_aligned(c: Cols)
    requires
        runs_model(c),
        lines_clustered(c),
        rpos(c, lkey(c, c.n_l - 1)) < c.n_o,
    ensures
        runs_aligned(c),
{
    lemma_fpos_last(c);
    assert forall|r: int| 0 <= r < c.n_o implies #[trigger] lkey(c, rstart(c, r)) == okey(c, r) by {
        lemma_fpos_ge(c, r);
        lemma_fpos_le_r(c, r);
        lemma_rpos_bound(c, lkey(c, rstart(c, r)));
    }
}

/// The lines of stored order `p` are exactly the rows of run `p`.
pub proof fn lemma_run_lines(c: Cols, p: int)
    requires
        keys_distinct(c),
        lines_clustered(c),
        runs_model(c),
        runs_aligned(c),
        0 <= p < c.n_o,
    ensures
        merge_inv(c, p, rstart(c, p)),
        forall|j: int| 0 <= j < c.n_l ==> (#[trigger] lkey(c, j) == okey(c, p) <==> rstart(c, p) <= j < rstart(c, p + 1)),
{
    let s = rstart(c, p);
    let e = rstart(c, p + 1);
    lemma_rstart_bounds(c, p);
    lemma_rstart_bounds(c, p + 1);
    lemma_rpos_of(c, p);
    assert(lkey(c, s) == okey(c, p));
    if s > 0 {
        assert(p > 0);
        lemma_rstart_bounds(c, p - 1);
        assert(lsame(c, p - 1, c.rl@[p - 1] - 1));
        assert(lkey(c, s - 1) == okey(c, p - 1));
        lemma_rpos_of(c, p - 1);
    }
    assert(merge_inv(c, p, s));
    assert forall|j: int| s <= j < e implies #[trigger] lkey(c, j) == okey(c, p) by {
        assert(lsame(c, p, j - s));
    }
    if e < c.n_l {
        assert(p + 1 < c.n_o) by {
            if p + 1 == c.n_o {
                assert(e == c.n_l);
            }
        }
        assert(lkey(c, e) == okey(c, p + 1));
    }
    lemma_merge_step(c, p, s, e);
}

/// The run cursor: run `r` (a stored orders row) starts at `st` and holds row `a`.
pub open spec fn cur_ok(c: Cols, r: int, st: int, a: int) -> bool {
    &&& 0 <= r < c.n_o
    &&& st == rstart(c, r)
    &&& st <= a < st + c.rl@[r]
}

/// Facts the run scan relies on.
pub open spec fn runs_ready(c: Cols, k: int) -> bool {
    &&& cols_ok(c, k)
    &&& keys_distinct(c)
    &&& lines_clustered(c)
    &&& runs_model(c)
    &&& runs_aligned(c)
}


/// Run `r` ends at `rstart(r + 1) = rstart(r) + rl[r]`, inside the table, and holds at least one row.
pub proof fn lemma_run_end(c: Cols, r: int)
    requires runs_model(c), 0 <= r < c.n_o,
    ensures
        0 <= rstart(c, r),
        c.rl@[r] >= 1,
        rstart(c, r + 1) == rstart(c, r) + c.rl@[r],
        rstart(c, r + 1) <= c.n_l,
{
    lemma_rstart_bounds(c, r);
    lemma_rstart_bounds(c, r + 1);
}

} // verus!
