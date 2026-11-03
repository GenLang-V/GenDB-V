//! TPC-H Q1 over the flat `lineitem` storage.
//!
//! Plan: read the seven columns Q1 needs as whole stored parts (`source`); split the rows into contiguous ranges,
//! one `fork_join` task per range (`task`), each scanning its range into a group table keyed by
//! (returnflag, linestatus) with exact per-group counts, sums and absolute masses (`scan`, `accum`); merge the
//! tables in range order (`merge`); then decide the outcome from the merged table (`output`): the SQL error of a
//! COUNT beyond int8, `Capacity` when a group's SUM/AVG leaves the machine domain, otherwise one row per group,
//! sorted by the key.
//!
//! Proof: the column view `crows(c)` is the projection of every bound database's `lineitem` table (`source`); the
//! accumulators are the normal form's `gcount`/`gsum`/`gabs` (`link::query`, instantiated in `normal`); `body`
//! relates the normal form to the SQL denotation (rows, capacity, and the COUNT error); `outcome` states the
//! fixed claim for each outcome over every bound database.
use vstd::prelude::*;

pub mod normal;
pub mod body;
pub mod columns;
pub mod accum;
pub mod scan;
pub mod block;
pub mod merge;
pub mod task;
pub mod source;
pub mod output;
pub mod outcome;

use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::datetime::*;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db};
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::query::param_domain;
use crate::exec::datetime::date_from_civil_exec;
use crate::link::query::view_rows;
use crate::stores::flat_lineitem::declaration::stored_relations;
use crate::agent::columns::*;
use crate::agent::accum::*;
use crate::agent::scan::*;
use crate::agent::block::*;
use crate::agent::merge::*;
use crate::agent::task::*;
use crate::agent::source::*;
use crate::agent::output::*;
use crate::agent::outcome::*;

verus! {

/// Rows per task below which fewer tasks are used.
pub const MIN_TASK_ROWS: usize = 65536;

/// First row of task `t` (`chunk = n / ntasks` rows per task).
pub open spec fn task_lo(t: int, chunk: int) -> int {
    t * chunk
}

/// End of task `t`'s rows: the next task's first row; the last task ends at `n`.
pub open spec fn task_hi(t: int, chunk: int, ntasks: int, n: int) -> int {
    if t + 1 == ntasks { n } else { (t + 1) * chunk }
}

/// The task ranges are ordered and inside `[0, n]`.
pub proof fn lemma_task_range(t: int, chunk: int, ntasks: int, n: int)
    requires 0 <= t < ntasks, ntasks >= 1, chunk == n / ntasks, n >= 0,
    ensures 0 <= task_lo(t, chunk) <= task_hi(t, chunk, ntasks, n) <= n,
{
    assert(chunk * ntasks <= n) by (nonlinear_arith) requires chunk == n / ntasks, ntasks >= 1, n >= 0;
    assert(0 <= chunk) by (nonlinear_arith) requires chunk == n / ntasks, ntasks >= 1, n >= 0;
    assert(t * chunk <= (t + 1) * chunk) by (nonlinear_arith) requires chunk >= 0, t >= 0;
    assert((t + 1) * chunk <= ntasks * chunk) by (nonlinear_arith) requires chunk >= 0, t + 1 <= ntasks;
    assert(0 <= t * chunk) by (nonlinear_arith) requires chunk >= 0, t >= 0;
}

/// Builds one scan task per row range.
fn make_tasks(c: Cols, ntasks: usize, limit: i32, Ghost(pd): Ghost<int>, small: bool) -> (tasks: Vec<ScanTask>)
    requires
        cols_wf(c),
        1 <= ntasks <= MAX_WORKERS,
        limit as int == pd + 10957,
    ensures
        tasks@.len() == ntasks,
        forall|t: int| 0 <= t < ntasks ==> (#[trigger] tasks@[t]).pre(),
        forall|t: int| 0 <= t < ntasks ==> (#[trigger] tasks@[t]).c == c && tasks@[t].limit == limit && tasks@[t].pd@ == pd
            && tasks@[t].small == small
            && tasks@[t].lo as int == task_lo(t, (c.n / ntasks) as int)
            && tasks@[t].hi as int == task_hi(t, (c.n / ntasks) as int, ntasks as int, c.n as int),
{
    let n = c.n;
    let chunk = n / ntasks;
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut t: usize = 0;
    while t < ntasks
        invariant
            cols_wf(c),
            n == c.n,
            1 <= ntasks <= MAX_WORKERS,
            chunk == n / ntasks,
            limit as int == pd + 10957,
            t <= ntasks,
            tasks@.len() == t,
            forall|u: int| 0 <= u < t ==> (#[trigger] tasks@[u]).pre(),
            forall|u: int| 0 <= u < t ==> (#[trigger] tasks@[u]).c == c && tasks@[u].limit == limit && tasks@[u].pd@ == pd
                && tasks@[u].small == small
                && tasks@[u].lo as int == task_lo(u, chunk as int)
                && tasks@[u].hi as int == task_hi(u, chunk as int, ntasks as int, n as int),
        decreases ntasks - t,
    {
        proof {
            lemma_task_range(t as int, chunk as int, ntasks as int, n as int);
        }
        let lo = t * chunk;
        let hi = if t + 1 == ntasks { n } else { (t + 1) * chunk };
        let slots = vec![new_acc(0, small); TASK_SLOTS];
        let idx = vec![0usize; IDX_LEN];
        let blk = crate::gendb_entry::work::filled(TASK_SLOTS, new_delta());
        let task = ScanTask { c, lo, hi, limit, pd: Ghost(pd), small, slots, idx, blk };
        proof {
            assert forall|code: int| 0 <= code < IDX_LEN implies #[trigger] idx@[code] == 0 by {
                assert(vstd::pervasive::cloned(0usize, idx@[code]));
            }
            assert(blk_zero(blk@));
            assert(task.pre());
        }
        tasks.push(task);
        t = t + 1;
    }
    tasks
}

/// Truncating a table's slot vector to its used slots keeps it.
pub proof fn lemma_table_prefix(pd: int, c: Cols, lo: int, i: int, slots: Seq<Acc>, ng: int, small: bool)
    requires table_ok(pd, c, lo, i, slots, ng), mode_ok(slots, ng, small),
    ensures table_ok(pd, c, lo, i, slots.subrange(0, ng), ng), mode_ok(slots.subrange(0, ng), ng, small),
{
    let s2 = slots.subrange(0, ng);
    assert forall|s: int| 0 <= s < ng implies #[trigger] s2[s] == slots[s] by {}
    assert forall|r: int| lo <= r < i && crate::agent::normal::q1_qual(pd, #[trigger] crow(c, r)) implies
        exists|s: int| 0 <= s < ng && key_of(c, r) == slot_key(c, #[trigger] s2[s]) by {
        let s = choose|s: int| 0 <= s < ng && key_of(c, r) == slot_key(c, #[trigger] slots[s]);
        assert(s2[s] == slots[s]);
    }
    assert forall|s: int, t: int| 0 <= s < ng && 0 <= t < ng && s != t implies slot_key(c, #[trigger] s2[s]) != slot_key(c, #[trigger] s2[t]) by {
        assert(s2[s] == slots[s] && s2[t] == slots[t]);
    }
}

/// How a range ends: its table was merged, a qualifying row's charge overflows `i128`, or the small mode does not
/// apply.
pub enum RangeEnd {
    Merged,
    RowOverflow(usize),
    NeedExact,
}

/// Completes the range `[lo, hi)` of a task's result and merges its table into the global table over `[0, lo)`.
fn absorb(c: &Cols, lo: usize, hi: usize, limit: i32, Ghost(pd): Ghost<int>, small: bool, gt: &mut Vec<Acc>, out: ScanOut)
    -> (r: RangeEnd)
    requires
        cols_wf(*c),
        lo <= hi <= c.n,
        limit as int == pd + 10957,
        scan_post(*c, lo, hi, pd, small, out),
        table_ok(pd, *c, 0, lo as int, old(gt)@, old(gt)@.len() as int),
        mode_ok(old(gt)@, old(gt)@.len() as int, small),
    ensures
        r matches RangeEnd::RowOverflow(m) ==> m < c.n && crate::agent::normal::q1_qual(pd, crow(*c, m as int))
            && !crate::link::expr::fits_i128(crate::agent::normal::charge(crow(*c, m as int))),
        r is NeedExact ==> small,
        r is Merged ==> table_ok(pd, *c, 0, hi as int, final(gt)@, final(gt)@.len() as int)
            && mode_ok(final(gt)@, final(gt)@.len() as int, small),
{
    let out = finish_range(c, lo, hi, limit, Ghost(pd), small, out);
    match out.stop {
        Stop::RowOverflow => {
            return RangeEnd::RowOverflow(out.at);
        },
        Stop::NeedExact => {
            return RangeEnd::NeedExact;
        },
        _ => {},
    }
    let mut w = out.slots;
    let ng = out.ng;
    proof {
        lemma_table_prefix(pd, *c, lo as int, hi as int, w@, ng as int, small);
    }
    w.truncate(ng);
    let wn = w.len();
    merge_table(c, lo, hi, Ghost(pd), Ghost(small), gt, &w, wn);
    RangeEnd::Merged
}

/// How the scan of all rows ends.
pub enum ScanEnd {
    /// The group table of all rows.
    Table(Vec<Acc>),
    /// A qualifying row whose charge overflows `i128`.
    RowOverflow(usize),
    /// A product outside 64 bits in small mode.
    NeedExact,
}

/// Scans all rows in `ntasks` parallel ranges and merges their tables: `Ok(Ok(gt))` the table of all rows,
/// `Ok(Err(m))` a qualifying row whose charge overflows `i128`, `Err` a failed worker join.
fn scan_all(c: Cols, ntasks: usize, limit: i32, Ghost(pd): Ghost<int>, small: bool, dispatch: &mut Dispatch)
    -> (r: Result<ScanEnd, crate::gendb_entry::runtime::WorkerFailure>)
    requires
        cols_wf(c),
        1 <= ntasks <= MAX_WORKERS,
        limit as int == pd + 10957,
    ensures
        r matches Ok(ScanEnd::Table(gt)) ==> full_table(pd, c, gt@),
        r matches Ok(ScanEnd::RowOverflow(m)) ==> m < c.n && crate::agent::normal::q1_qual(pd, crow(c, m as int))
            && !crate::link::expr::fits_i128(crate::agent::normal::charge(crow(c, m as int))),
        r matches Ok(ScanEnd::NeedExact) ==> small,
{
    let n = c.n;
    let chunk = n / ntasks;
    let tasks = make_tasks(c, ntasks, limit, Ghost(pd), small);
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    // Complete each range (a full table resumes on this thread) and merge the tables in range order.
    let mut outs = outs;
    let mut gt: Vec<Acc> = Vec::new();
    let mut done: usize = 0;
    let mut t: usize = 0;
    proof {
        assert(table_ok(pd, c, 0, 0, gt@, 0));
    }
    while t < ntasks
        invariant
            cols_wf(c),
            n == c.n,
            1 <= ntasks <= MAX_WORKERS,
            chunk == n / ntasks,
            limit as int == pd + 10957,
            t <= ntasks,
            outs@.len() == ntasks - t,
            tv.len() == ntasks,
            forall|u: int| 0 <= u < ntasks ==> (#[trigger] tv[u]).c == c && tv[u].limit == limit && tv[u].pd@ == pd
                && tv[u].small == small
                && tv[u].lo as int == task_lo(u, chunk as int) && tv[u].hi as int == task_hi(u, chunk as int, ntasks as int, n as int),
            forall|i: int| 0 <= i < outs@.len() ==> tv[t + i].post(#[trigger] outs@[i]),
            t < ntasks ==> done as int == task_lo(t as int, chunk as int),
            t == ntasks ==> done == n,
            table_ok(pd, c, 0, done as int, gt@, gt@.len() as int),
            mode_ok(gt@, gt@.len() as int, small),
        decreases ntasks - t,
    {
        proof {
            lemma_task_range(t as int, chunk as int, ntasks as int, n as int);
            assert(tv[t as int + 0].post(outs@[0]));
        }
        let ghost before = outs@;
        let out = outs.remove(0);
        let lo = t * chunk;
        let hi = if t + 1 == ntasks { n } else { (t + 1) * chunk };
        match absorb(&c, lo, hi, limit, Ghost(pd), small, &mut gt, out) {
            RangeEnd::RowOverflow(m) => return Ok(ScanEnd::RowOverflow(m)),
            RangeEnd::NeedExact => return Ok(ScanEnd::NeedExact),
            RangeEnd::Merged => {},
        }
        done = hi;
        proof {
            assert forall|i: int| 0 <= i < outs@.len() implies tv[(t + 1) + i].post(#[trigger] outs@[i]) by {
                assert(outs@[i] == before[i + 1]);
                assert(tv[t + (i + 1)].post(before[i + 1]));
            }
            if t + 1 < ntasks {
                assert(task_lo(t + 1, chunk as int) == (t + 1) * chunk);
            }
        }
        t = t + 1;
    }
    Ok(ScanEnd::Table(gt))
}

pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, params@, r),
{
    hide(read_facts);
    hide(cols_wf);
    let ghost sv = stores@;
    let ghost ps = params@;
    let ghost db0 = choose|db: Database| #[trigger] bound_db(sv, db);
    let ghost rels = stored_relations(db0);
    let c = read_cols(&mut stores.flat_lineitem, Ghost(rels));
    proof {
        lemma_rel_rows_ok(c, db0);
        assert(cols_wf(c)) by { reveal(cols_wf); }
        lemma_param(ps);
    }
    // The parameter as days since 2000-01-01, and the limit on stored dates (days since 1970-01-01).
    let pd = date_from_civil_exec(params.p0.y as i64, params.p0.m as i64, params.p0.d as i64);
    let ghost gpd = pd as int;
    let limit = (pd + 10957) as i32;
    proof {
        assert(read_facts(sv, c, rels, ps, gpd)) by { reveal(read_facts); }
    }
    let n = c.n;
    let mut ntasks = workers;
    if n / MIN_TASK_ROWS < ntasks {
        ntasks = n / MIN_TASK_ROWS;
    }
    if ntasks == 0 {
        ntasks = 1;
    }
    // Fast (small) mode first; a product outside 64 bits reruns the scan with exact masses.
    let mut end = match scan_all(c, ntasks, limit, Ghost(gpd), true, dispatch) {
        Err(e) => return Err(QueryError::WorkerFailed(e)),
        Ok(end) => end,
    };
    if let ScanEnd::NeedExact = end {
        end = match scan_all(c, ntasks, limit, Ghost(gpd), false, dispatch) {
            Err(e) => return Err(QueryError::WorkerFailed(e)),
            Ok(end) => end,
        };
    }
    let gt = match end {
        ScanEnd::Table(gt) => gt,
        ScanEnd::RowOverflow(m) => {
            proof {
                lemma_capacity_row_all(sv, c, rels, ps, gpd, m as int);
            }
            return Ok(Answer::Capacity);
        },
        ScanEnd::NeedExact => {
            // The exact mode never asks for the exact mode.
            proof {
                assert(false);
            }
            return Ok(Answer::Capacity);
        },
    };
    match finalize(&c, Ghost(gpd), &gt) {
        Outcome::Rows(rows) => {
            proof {
                lemma_rows_all(sv, c, rels, ps, gpd, view_rows(rows@));
            }
            Ok(Answer::Rows(rows))
        },
        Outcome::CountError => {
            proof {
                lemma_count_error_all(sv, c, rels, ps, gpd);
            }
            Ok(Answer::SqlError(SqlError::NumericValueOutOfRange))
        },
        Outcome::GroupCapacity => {
            proof {
                lemma_group_capacity_all(sv, c, rels, ps, gpd);
            }
            Ok(Answer::Capacity)
        },
    }
}

} // verus!
