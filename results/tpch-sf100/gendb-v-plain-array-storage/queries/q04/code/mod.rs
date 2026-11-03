//! TPC-H Q4 over the flat `orders` and `lineitem` storages.
//!
//! Plan: read `o_orderkey`, `o_orderdate`, `o_orderpriority` and `l_orderkey`, `l_commitdate`, `l_receiptdate` as whole
//! stored parts (`source`); compute the date window `[$1, $1 + 3 months)` on stored days; split `lineitem` into equal
//! row chunks and `orders` into the matching key ranges, one `fork_join` task per pair (`plan`, `task`). Each task
//! finds, for every order of its range in the window, the run of its key in `l_orderkey` by a forward search from the
//! previous run or a binary search, tests the run for a late row, and counts the found orders per priority; a separate
//! branch-free pass checks that its `l_orderkey` rows are in order. When every task saw its keys in order,
//! `l_orderkey` is sorted, so the runs are all rows of the key and the task tables merge into the result; otherwise the
//! calling thread recomputes the table by scanning `lineitem` for every order in the window. The rows (priority,
//! count) are sorted by priority (`output`).
//!
//! Proof: the normal form (`normal`, `link::query::QuerySpec`) states the WHERE (window and EXISTS) per projected
//! orders row; `body` relates it to the SQL denotation (rows, the COUNT error, the error of `$1 + 3 months` outside the
//! timestamp range); the tables count the qualifying row lists `lists::q_list` (`table`, `lists`); `outcome` states the
//! fixed claim for each outcome over every bound database.
use vstd::prelude::*;

pub mod cols;
pub mod lists;
pub mod table;
pub mod task;
pub mod normal;
pub mod body;
pub mod source;
pub mod output;
pub mod plan;
pub mod outcome;

use crate::spec::value::*;
use crate::spec::datetime::*;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db};
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::query::param_domain;
use crate::exec::datetime::{date_from_civil_exec, date_to_ts_exec, ts_add_interval_exec, floor_divmod};
use crate::link::query::view_rows;
use crate::stores::flat_lineitem::declaration as ld;
use crate::stores::flat_orders::declaration as od;
use crate::agent::cols::*;
use crate::agent::lists::*;
use crate::agent::normal::*;
use crate::agent::source::*;
use crate::agent::output::*;
use crate::agent::plan::*;
use crate::agent::outcome::*;

verus! {

/// `$1 + interval '3 month'` (timestamp microseconds) from the parameter day `pd` (days since 2000-01-01).
fn hi_bound(pd: i64) -> (r: Result<i64, SqlError>)
    requires -730119 <= pd <= 2921939,
    ensures
        match (r, hi_res(pd as int)) {
            (Ok(a), Ok(b)) => a as int == b,
            (Err(e), Err(f)) => e == f,
            _ => false,
        },
{
    match date_to_ts_exec(pd as i32) {
        Ok(t0) => ts_add_interval_exec(t0, 3, 0, 0),
        Err(e) => Err(e),
    }
}

/// The window on stored days: from `pd` to the first day whose midnight is not below `t1`.
fn window(pd: i64, t1: i64) -> (w: Win)
    requires -730119 <= pd <= 2921939, ts_valid(t1 as int),
    ensures win_of(w, pd as int, t1 as int),
{
    let (hq, rem) = floor_divmod(t1 + 86_399_999_999, 86_400_000_000);
    assert(hq * 86_400_000_000 >= t1 && (hq - 1) * 86_400_000_000 < t1);
    Win { dlo: pd + 10957, dhi: hq + 10957 }
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
    let ghost rl = ld::stored_relations(db0);
    let ghost ro = od::stored_relations(db0);
    let l = read_lcols(&mut stores.flat_lineitem, Ghost(rl));
    let o = read_ocols(&mut stores.flat_orders, Ghost(ro));
    proof {
        lemma_param(ps);
    }
    let pd = date_from_civil_exec(params.p0.y as i64, params.p0.m as i64, params.p0.d as i64);
    let ghost gpd = pd as int;
    proof {
        assert(read_facts(sv, l, o, rl, ro, ps, gpd));
    }
    let t1 = match hi_bound(pd) {
        Ok(t1) => t1,
        Err(e) => {
            if o.no > 0 {
                proof {
                    lemma_hi_err_all(sv, l, o, rl, ro, ps, gpd, e);
                }
                return Ok(Answer::SqlError(e));
            }
            let rows: Vec<Vec<crate::exec::value::EVal>> = Vec::new();
            proof {
                lemma_empty_all(sv, l, o, rl, ro, ps, gpd);
                assert(view_rows(rows@) =~= Seq::<Row>::empty());
            }
            return Ok(Answer::Rows(rows));
        },
    };
    let ghost gt1 = t1 as int;
    proof {
        lemma_hi_valid(gpd, gt1);
    }
    let w = window(pd, t1);
    let (reps, counts) = match compute_groups(&l, &o, w, workers, dispatch) {
        Ok(t) => t,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    match finalize(&o, &reps, &counts, Ghost(l), Ghost(w), Ghost(gpd), Ghost(gt1)) {
        Outcome::Rows(rows) => {
            proof {
                lemma_rows_all(sv, l, o, rl, ro, ps, gpd, gt1, view_rows(rows@));
            }
            Ok(Answer::Rows(rows))
        },
        Outcome::CountError => {
            proof {
                lemma_count_error_all(sv, l, o, rl, ro, ps, gpd, gt1);
            }
            Ok(Answer::SqlError(SqlError::NumericValueOutOfRange))
        },
    }
}

} // verus!
