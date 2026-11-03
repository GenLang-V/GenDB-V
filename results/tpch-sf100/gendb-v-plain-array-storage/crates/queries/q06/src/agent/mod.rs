//! TPC-H Q6 (forecasting revenue change) over the flat `lineitem` storage:
//! `SUM(l_extendedprice * l_discount)` over the rows shipped in the year from `$1`, with discount within `$2 +/-
//! 0.01` and quantity below `$3`.
//!
//! Plan of a call (`query`):
//! 1. read the four columns as whole stored parts (`source`); compute the WHERE bounds from the parameters
//!    (`bounds`; a failing `$1 + INTERVAL '1' YEAR` is that SQL error);
//! 2. scan the rows in `workers` contiguous ranges, one `fork_join` task each (one range on the calling thread with
//!    one worker; above 32 tasks the ranges taper so that the tasks spawned last get fewer rows, `task_start`);
//!    each range is scanned in blocks by a three-stage selection-vector kernel (`kernel`): shipdate
//!    (4-byte column, every row), then discount and quantity of the surviving rows only, summing the exact products
//!    in an accumulator with saturating absolute mass (`accum`);
//! 3. merge the range accumulators in order; `Capacity` when the absolute mass leaves `i128`, else the one row
//!    (NULL without qualifying rows).
//!
//! Proof: the column view `crows(c)` is the projection of every bound database's `lineitem` table (`source`); the
//! accumulators are the normal form's `gsum`/`gabs`/`gcount` (`link::query`, instantiated in `normal`; kernel
//! bridge `kernel::lemma_range_gsum`); `body` relates the normal form to the SQL denotation (row, capacity, error)
//! and `outcome` states the fixed claim for each outcome over every bound database.
use vstd::prelude::*;

pub mod common;
pub mod columns;
pub mod normal;
pub mod source;
pub mod accum;
pub mod kernel;
pub mod body;
pub mod outcome;
pub mod bounds;

use crate::spec::value::*;
use crate::spec::ast::*;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db};
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::{QueryError, WorkerFailure};
use crate::gendb_entry::work::filled;
use crate::gendb_params::Params;
use crate::query::param_domain;
use crate::exec::value::{EVal, view_row};
use crate::link::query::*;
use crate::link::outcome::lemma_view_rows;
use crate::stores::flat_lineitem::declaration::stored_relations;
use crate::agent::columns::*;
use crate::agent::normal::*;
use crate::agent::source::*;
use crate::agent::accum::*;
use crate::agent::kernel::*;
use crate::agent::body::*;
use crate::agent::outcome::*;
use crate::agent::bounds::*;

verus! {

/// Rows per task below which fewer tasks are used.
pub const MIN_TASK_ROWS: usize = 65536;

/// Task counts from this one on scan with the strided stage 2 (`kernel::scan_range_strided`). Measured faster at
/// 64 workers and at 32 workers when the scheduler packs the threads onto one socket (as it does after long
/// single-threaded calls in the same process); about equal at 32 well-spread workers; slower on one thread.
pub const STRIDED_MIN_TASKS: usize = 2;

/// Task counts from this one on get tapered row ranges (`task_start`).
pub const TAPER_MIN_TASKS: usize = 33;

/// Prefix weight of the tapered split: tasks `0..t` together weigh `sum_{i<t} (17 (ntasks - 1) + 6 i)`. `fork_join`
/// spawns the tasks one by one from the last to the first, so task `i` starts later the lower `i` is; with many
/// tasks the last-spawned ones start several milliseconds late, and they get up to 15% fewer rows than the mean.
pub open spec fn taper_prefix(t: int, ntasks: int) -> int {
    t * (17 * ntasks - 20) + 3 * t * t
}

/// The weight of all `ntasks` tasks: `taper_prefix(ntasks, ntasks)`.
pub open spec fn taper_total(ntasks: int) -> int {
    20 * ntasks * ntasks - 20 * ntasks
}

/// First row of task `t` of `ntasks` over `n` rows (`n` for `t == ntasks`): equal ranges of `n / ntasks` rows (the
/// last task takes the rest), or the tapered ranges.
pub open spec fn task_start(t: int, ntasks: int, n: int, taper: bool) -> int {
    if t >= ntasks {
        n
    } else if taper {
        n * taper_prefix(t, ntasks) / taper_total(ntasks)
    } else {
        t * (n / ntasks)
    }
}

/// The taper weights grow with `t` up to the total.
proof fn lemma_taper_prefix(t: int, ntasks: int)
    requires ntasks >= 2, 0 <= t < ntasks,
    ensures
        0 <= taper_prefix(t, ntasks) <= taper_prefix(t + 1, ntasks) <= taper_total(ntasks),
        taper_total(ntasks) > 0,
{
    let m = 17 * ntasks - 20;
    assert(m > 0);
    assert(0 <= t * m + 3 * t * t) by (nonlinear_arith) requires t >= 0, m > 0;
    assert(t * m + 3 * t * t <= (t + 1) * m + 3 * (t + 1) * (t + 1)) by (nonlinear_arith) requires t >= 0, m > 0;
    // The total is the prefix at `ntasks`, and `t + 1 <= ntasks`.
    assert((t + 1) * m + 3 * (t + 1) * (t + 1) <= ntasks * m + 3 * ntasks * ntasks) by (nonlinear_arith)
        requires 0 <= t + 1 <= ntasks, m > 0;
    assert(ntasks * m + 3 * ntasks * ntasks == 20 * ntasks * ntasks - 20 * ntasks) by (nonlinear_arith)
        requires m == 17 * ntasks - 20;
    assert(20 * ntasks * ntasks - 20 * ntasks > 0) by (nonlinear_arith) requires ntasks >= 2;
}

/// The task ranges start at 0, are ordered and stay inside `[0, n]`.
pub proof fn lemma_task_start(t: int, ntasks: int, n: int, taper: bool)
    requires 0 <= t < ntasks, ntasks >= 1, n >= 0, taper ==> ntasks >= 2,
    ensures
        task_start(0, ntasks, n, taper) == 0,
        0 <= task_start(t, ntasks, n, taper) <= task_start(t + 1, ntasks, n, taper) <= n,
{
    if taper {
        let d = taper_total(ntasks);
        lemma_taper_prefix(t, ntasks);
        lemma_taper_prefix(0, ntasks);
        let w0 = taper_prefix(t, ntasks);
        let w1 = taper_prefix(t + 1, ntasks);
        assert(taper_prefix(0, ntasks) == 0);
        assert(n * 0 == 0);
        vstd::arithmetic::div_mod::lemma_div_multiples_vanish(0, d);
        assert(d * 0 == 0);
        assert(0 <= n * w0) by (nonlinear_arith) requires n >= 0, w0 >= 0;
        assert(n * w0 <= n * w1) by (nonlinear_arith) requires n >= 0, w0 <= w1;
        assert(n * w1 <= n * d) by (nonlinear_arith) requires n >= 0, w1 <= d;
        vstd::arithmetic::div_mod::lemma_div_is_ordered(0, n * w0, d);
        vstd::arithmetic::div_mod::lemma_div_is_ordered(n * w0, n * w1, d);
        vstd::arithmetic::div_mod::lemma_div_is_ordered(n * w1, n * d, d);
        vstd::arithmetic::div_mod::lemma_div_by_multiple(n, d);
        assert(0int / d == 0);
    } else {
        let chunk = n / ntasks;
        assert(chunk * ntasks <= n) by (nonlinear_arith) requires chunk == n / ntasks, ntasks >= 1, n >= 0;
        assert(0 <= chunk) by (nonlinear_arith) requires chunk == n / ntasks, ntasks >= 1, n >= 0;
        assert(t * chunk <= (t + 1) * chunk) by (nonlinear_arith) requires chunk >= 0, t >= 0;
        assert((t + 1) * chunk <= ntasks * chunk) by (nonlinear_arith) requires chunk >= 0, t + 1 <= ntasks;
        assert(0 <= t * chunk) by (nonlinear_arith) requires chunk >= 0, t >= 0;
        assert(ntasks * chunk == chunk * ntasks) by (nonlinear_arith);
        assert(0 * chunk == 0);
    }
}

/// `task_start` computed (`n` rows, `t <= ntasks <= MAX_WORKERS`).
fn task_start_exec(t: usize, ntasks: usize, n: usize, taper: bool) -> (r: usize)
    requires 0 <= t <= ntasks <= MAX_WORKERS, ntasks >= 1, taper ==> ntasks >= 2,
    ensures r as int == task_start(t as int, ntasks as int, n as int, taper),
{
    if t >= ntasks {
        n
    } else if taper {
        let tt = t as u128;
        let nt = ntasks as u128;
        let ghost wt = taper_prefix(t as int, ntasks as int);
        proof {
            lemma_task_start(t as int, ntasks as int, n as int, taper);
            lemma_taper_prefix(t as int, ntasks as int);
            // Operand bounds for the 128-bit arithmetic (t <= 64, ntasks <= 64).
            assert(tt * (17 * nt - 20) <= 64 * 1068) by (nonlinear_arith) requires tt <= 64, 2 <= nt <= 64;
            assert(3 * tt * tt <= 3 * 64 * 64) by (nonlinear_arith) requires tt <= 64;
            assert(20 * nt * nt <= 20 * 64 * 64) by (nonlinear_arith) requires nt <= 64;
            assert(20 * nt * nt >= 20 * nt) by (nonlinear_arith) requires nt >= 1;
            assert((n as int) * wt <= (n as int) * 100000) by (nonlinear_arith) requires n >= 0, 0 <= wt <= 100000;
        }
        let w = tt * (17 * nt - 20) + 3 * tt * tt;
        let d = 20 * nt * nt - 20 * nt;
        assert(w as int == wt);
        assert(d as int == taper_total(ntasks as int));
        let r = (n as u128) * w / d;
        r as usize
    } else {
        proof {
            lemma_task_start(t as int, ntasks as int, n as int, taper);
        }
        t * (n / ntasks)
    }
}

/// One scan task per row range, each with its scratch buffers.
fn make_tasks(c: Cols, b: Bounds, ntasks: usize, strided: bool, taper: bool) -> (tasks: Vec<ScanTask>)
    requires cols_wf(c), bounds_wf(b), 1 <= ntasks <= MAX_WORKERS, taper ==> ntasks >= 2,
    ensures
        tasks@.len() == ntasks,
        forall|t: int| 0 <= t < ntasks ==> (#[trigger] tasks@[t]).pre(),
        forall|t: int| 0 <= t < ntasks ==> (#[trigger] tasks@[t]).c == c && tasks@[t].b == b
            && tasks@[t].lo as int == task_start(t, ntasks as int, c.n as int, taper)
            && tasks@[t].hi as int == task_start(t + 1, ntasks as int, c.n as int, taper),
{
    let n = c.n;
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut t: usize = 0;
    while t < ntasks
        invariant
            cols_wf(c),
            bounds_wf(b),
            n == c.n,
            1 <= ntasks <= MAX_WORKERS,
            taper ==> ntasks >= 2,
            t <= ntasks,
            tasks@.len() == t,
            forall|u: int| 0 <= u < t ==> (#[trigger] tasks@[u]).pre(),
            forall|u: int| 0 <= u < t ==> (#[trigger] tasks@[u]).c == c && tasks@[u].b == b
                && tasks@[u].lo as int == task_start(u, ntasks as int, n as int, taper)
                && tasks@[u].hi as int == task_start(u + 1, ntasks as int, n as int, taper),
        decreases ntasks - t,
    {
        proof {
            lemma_task_start(t as int, ntasks as int, n as int, taper);
        }
        let lo = task_start_exec(t, ntasks, n, taper);
        let hi = task_start_exec(t + 1, ntasks, n, taper);
        let sel = filled(STRIDED_BLOCK_ROWS, 0u32);
        let sel2 = filled(STRIDED_BLOCK_ROWS, 0u32);
        tasks.push(ScanTask { c, b, lo, hi, sel, sel2, strided });
        t = t + 1;
    }
    tasks
}

/// The SUM over all rows: one range per task (at most `workers`), or the whole table on the calling thread.
fn scan_all(c: Cols, b: Bounds, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Acc, WorkerFailure>)
    requires cols_wf(c), bounds_wf(b), 1 <= workers <= MAX_WORKERS,
    ensures r matches Ok(a) ==> range_acc(c, b, 0, c.n as int, a),
{
    let n = c.n;
    let mut ntasks = workers;
    if n / MIN_TASK_ROWS < ntasks {
        ntasks = n / MIN_TASK_ROWS;
    }
    if ntasks <= 1 {
        let mut sel = filled(BLOCK_ROWS, 0u32);
        let mut sel2 = filled(BLOCK_ROWS, 0u32);
        return Ok(scan_range(&c, &b, 0, n, &mut sel, &mut sel2));
    }
    let taper = ntasks >= TAPER_MIN_TASKS;
    let tasks = make_tasks(c, b, ntasks, ntasks >= STRIDED_MIN_TASKS, taper);
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    // Merge the range accumulators in range order.
    let ghost g = g_of(b);
    let ghost e = Seq::<Val>::empty();
    let mut total = acc_new();
    let mut done: usize = 0;
    let mut t: usize = 0;
    proof {
        lemma_empty(g, crows(c), 0, e, 0);
        lemma_task_start(0, ntasks as int, n as int, taper);
    }
    while t < ntasks
        invariant
            cols_wf(c),
            n == c.n,
            2 <= ntasks <= MAX_WORKERS,
            t <= ntasks,
            outs@.len() == ntasks,
            tv.len() == ntasks,
            g == g_of(b),
            e == Seq::<Val>::empty(),
            forall|u: int| 0 <= u < ntasks ==> (#[trigger] tv[u]).c == c && tv[u].b == b
                && tv[u].lo as int == task_start(u, ntasks as int, n as int, taper)
                && tv[u].hi as int == task_start(u + 1, ntasks as int, n as int, taper),
            forall|u: int| 0 <= u < ntasks ==> tv[u].post(#[trigger] outs@[u]),
            done as int == task_start(t as int, ntasks as int, n as int, taper),
            done <= n,
            range_acc(c, b, 0, done as int, total),
        decreases ntasks - t,
    {
        proof {
            lemma_task_start(t as int, ntasks as int, n as int, taper);
            assert(tv[t as int].post(outs@[t as int]));
        }
        let part = outs[t];
        let hi = task_start_exec(t + 1, ntasks, n, taper);
        total = acc_merge(total, part,
            Ghost(gs(c, b, 0, done as int)), Ghost(ga(c, b, 0, done as int)), Ghost(gc(c, b, 0, done as int)),
            Ghost(gs(c, b, done as int, hi as int)), Ghost(ga(c, b, done as int, hi as int)), Ghost(gc(c, b, done as int, hi as int)));
        proof {
            lemma_split(g, crows(c), 0, done as int, hi as int, e, 0);
        }
        done = hi;
        t = t + 1;
    }
    proof {
        assert(done == n);
    }
    Ok(total)
}

pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost ps = params@;
    let ghost db0 = choose|db: Database| #[trigger] bound_db(sv, db);
    let ghost rels = stored_relations(db0);
    let c = read_cols(&mut stores.flat_lineitem, Ghost(rels));
    proof {
        lemma_db_rows(c, db0);
        assert(read_facts(sv, c, rels, ps));
    }
    let (b, t1) = match param_bounds(params) {
        ParamBounds::Bounds { b, t1 } => (b, t1),
        ParamBounds::Error(e) => {
            if c.n == 0 {
                proof {
                    lemma_empty_all(sv, c, rels, ps);
                }
                return Ok(Answer::Rows(single_row(EVal::Null)));
            }
            proof {
                lemma_error_all(sv, c, rels, ps, param_day(ps), e);
            }
            return Ok(Answer::SqlError(e));
        },
    };
    let ghost qb = qb_of(b);
    let ghost g = q6_spec(qb);
    let ghost e = Seq::<Val>::empty();
    let total = match scan_all(c, b, workers, dispatch) {
        Ok(a) => a,
        Err(f) => return Err(QueryError::WorkerFailed(f)),
    };
    proof {
        assert(crows(c).subrange(0, c.n as int) =~= crows(c));
    }
    if total.mass == MASS_CAP {
        proof {
            lemma_capacity_all(sv, c, rels, ps, qb, t1 as int);
        }
        return Ok(Answer::Capacity);
    }
    let v = if total.any { EVal::Num { coeff: total.sum, scale: 4 } } else { EVal::Null };
    proof {
        assert(v@ == agg_out(AggKind::Sum { scale: 4 }, gcount(g, crows(c), e), gsum(g, crows(c), e, 0)));
        lemma_rows_all(sv, c, rels, ps, qb, t1 as int);
    }
    Ok(Answer::Rows(single_row(v)))
}

/// The answer of one row with one value.
fn single_row(v: EVal) -> (rows: Vec<Vec<EVal>>)
    ensures view_rows(rows@) == seq![seq![v@]],
{
    let mut row: Vec<EVal> = Vec::new();
    row.push(v);
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    rows.push(row);
    proof {
        lemma_view_rows(rows@);
        assert(view_row(rows@[0]@) =~= seq![v@]);
        assert(view_rows(rows@) =~= seq![seq![v@]]);
    }
    rows
}

} // verus!
