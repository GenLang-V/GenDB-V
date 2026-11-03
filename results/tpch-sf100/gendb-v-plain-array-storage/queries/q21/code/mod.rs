//! TPC-H Q21 (suppliers who kept orders waiting) over the flat storages: per `s_name` of the suppliers of nation `$1`,
//! the number of their late lineitems in `F` orders where another supplier took part and no other supplier was late,
//! top 100 by that count descending, then name.
//!
//! Plan of a call (`query`):
//! 1. read the columns as whole stored parts (`cols::read_cols`; nothing is copied);
//! 2. the selected suppliers (`plan::build_sup`): those whose nation is named `$1`, ascending, with a key lookup
//!    (`scan::SupMap`; a row map and a bitmap when the supplier keys are dense);
//! 3. the lineitem scan (`plan::supplier_counts`): at most `workers` ranges starting at changes of `l_orderkey`, one
//!    `scan::ScanTask` each: per 64-row window, bit masks of the key changes and of the late rows (a vectorized pass)
//!    and of the first late row of every run (one addition), whose suppliers are looked up in the bitmap; the few runs
//!    whose first late supplier is selected are evaluated row by row and resolved against the order's status; when
//!    the keys are not sorted, every count is computed row by row instead;
//! 4. the groups per name (`groups::build_groups`) and their top 100 (`topk::top`), or the SQL error 22003 when a
//!    COUNT leaves int8; the output rows (`answer::out_rows`).
//!
//! Proof: the statement's body is the accumulator normal form of `link::query` over the joined rows (`denot`), whose
//! group counts are the stored-column counts `nf::gc` (`sums`); the scan computes the per-supplier counts `nf::ksum`
//! (`runs`, `scan`, `plan`), the groups are the names with a positive count (`groups`), and `answer` turns a sorted
//! top 100 of them into the fixed claim.
use vstd::prelude::*;
use std::sync::Arc;

pub mod common;
pub mod cols;
pub mod nf;
pub mod denot;
pub mod sums;
pub mod runs;
pub mod scan;
pub mod plan;
pub mod groups;
pub mod topk;
pub mod answer;

use crate::spec::value::*;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db, outcome_ok};
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::query::param_domain;
use crate::link::query::view_rows;
use cols::*;
use scan::SupMap;
use plan::{build_sup, supplier_counts};
use groups::*;
use topk::*;
use answer::*;
use denot::pb_of;

verus! {

pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, params@, r),
{
    hide(plan_facts);
    hide(grp_ok);
    hide(scan::sup_ok);
    let ghost sv = stores@;
    let ghost ps = params@;
    let ghost db0 = choose|db: Database| #[trigger] bound_db(sv, db);
    proof { assert(pb_of(ps) == params.p0@); }
    // 1. the columns
    let c = read_cols(stores, Ghost(db0));
    // 2. the selected suppliers
    let marc: Arc<SupMap> = Arc::new(build_sup(&c, params.p0, Ghost(sv)));
    let m: &SupMap = &*marc;
    // 3. their counts over all lineitem rows
    let tot = match supplier_counts(&c, &marc, workers, dispatch, Ghost(sv)) {
        Ok(t) => t,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    // 4. the groups, the COUNT domain, the top 100 and the rows
    let distinct = name_keys(&c, m, &tot, Ghost(sv));
    let (grep, gt) = build_groups(&c, m, &tot, distinct, Ghost(sv));
    proof {
        lemma_plan_facts(sv, pb_of(ps), c, *m, tot@, grep@, gt@);
    }
    match find_over(&gt) {
        Some(g0) => {
            proof {
                lemma_answer_err(sv, ps, c, *m, tot@, grep@, gt@, g0 as int);
            }
            return Ok(Answer::SqlError(SqlError::NumericValueOutOfRange));
        },
        None => {},
    }
    let sel = top(&c, m, &grep, &gt, Ghost(sv));
    let rows = out_rows(&c, m, &grep, &gt, &sel, Ghost(sv));
    proof {
        lemma_answer_rows(sv, ps, c, *m, tot@, grep@, gt@, sel@, view_rows(rows@));
    }
    Ok(Answer::Rows(rows))
}

} // verus!
