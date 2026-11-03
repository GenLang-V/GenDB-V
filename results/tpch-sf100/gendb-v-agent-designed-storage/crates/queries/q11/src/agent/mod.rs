//! TPC-H Q11 (important stock) over the admitted storage `suppliers` (partsupp, supplier, nation).
//!
//! Plan: open the column handles (`tables`), the run layout of ps_partkey (use `suppliers_psrun`) and the ps_suppkey
//! index (use `ps_suppidx`, `bitmap`: a one-thread scan reads its qualification masks from a bitmap of the rows of the
//! qualifying suppliers); find the nation keys named `$1` and the supplier key range (`supp`);
//! with partsupp stored sorted by ps_partkey and a narrow supplier key range, run the parallel fast plan (`plan`:
//! flag the qualifying suppliers, one pass over aligned row ranges (`scan`: per 4096-row chunk a branch-free
//! qualification mask, then only its set bits) emitting each ps_partkey group's SUM above a sampled bound, sorted in
//! the task, with the range's total and mass; then the HAVING threshold and each range's sorted prefix above it),
//! else the general plan (`general`). Merge the ranges' descending runs (`common::msort`) and answer in columns.
//!
//! Proof: `nf`/`sqlrow`/`sqlq` state the statement's body in normal form (`sqlq::lemma_body`), `capq` its capacity
//! domain (`capq::lemma_capacity`), `rows` the plan's accumulators over partsupp rows and their bridge to the
//! normal form, `finish::lemma_final` / `lemma_final_cap` the link to the fixed claim; `bind` gives every
//! database bound to the parts the same tables.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::query::{query_spec_at, param_domain};
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db, outcome_ok};
use crate::gendb_params::Params;
use crate::stores::suppliers_psrun::interface as ppi;

pub mod tables;
pub mod nf;
pub mod bind;
pub mod sqlrow;
pub mod sqlq;
pub mod capq;
pub mod rows;
pub mod supp;
pub mod groups;
pub mod scan;
pub mod tasks;
pub mod finish;
pub mod collect;
pub mod plan;
pub mod general;
pub mod bitmap;
pub mod common;

use tables::*;
use bind::*;
use supp::*;
use plan::*;
use general::*;
use finish::*;
use bitmap::*;

verus! {

pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost db0 = choose|db: Database| #[trigger] bound_db(sv, db);
    proof {
        lemma_bound(sv, db0);
        lemma_params(params@);
    }
    let ghost t = tabs_of(db0);
    let ghost name = params.p0@;
    let c0 = open_cols(stores, Ghost(sr_of(db0)));
    assert(cols_ok(c0, t));
    // The run layout of ps_partkey (storage suppliers_psrun): with 4-row runs the scan derives each row's key.
    let run = stores.suppliers_psrun.extent_i64(ppi::RUN, 0, 2);
    proof { assert(run@ =~= ppi::run_i64s(stores.suppliers_psrun@[ppi::RUN as int])); }
    let c = if run[0] == 4 {
        proof { lemma_krun(c0.ps, t.ps, run@); }
        Cols { ps: PSCols { krun: true, kfirst: run[1], ..c0.ps }, ..c0 }
    } else {
        c0
    };
    assert(cols_ok(c, t));
    // The ps_suppkey index (storage ps_suppidx): the one-thread scan marks the qualifying rows from it.
    proof {
        let rels = crate::stores::ps_suppidx::declaration::stored_relations(db0);
        assert(crate::stores::ps_suppidx::interface::represents(stores.ps_suppidx@, rels) && rels[0] == supp_rel(t));
    }
    let ix = open_index(&mut stores.ps_suppidx, Ghost(t));
    let nk = nation_keys(&c.n, params.p0, Ghost(t));
    let (smin, smax) = supplier_key_range(&c.s, Ghost(t));
    let wide: i128 = smax as i128 - smin as i128;
    let plan = if c.ps.kind == 1 && wide < scan::RANGE_LIM as i128 - 1 {
        let range = (wide + 1) as usize;
        match fast_plan(&c, &ix, &nk, smin, range, params.p1, workers, dispatch, Ghost(t), Ghost(name)) {
            Ok(o) => o,
            Err(e) => {
                let r = Err(e);
                assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(params@), r) by {}
                return r;
            },
        }
    } else {
        general_plan(&c, &nk, params.p1, Ghost(t), Ghost(name))
    };
    if plan.cap {
        let r = Ok(Answer::Capacity);
        proof {
            assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(params@), r) by {
                lemma_bound_same(sv, db0, db);
                lemma_bound(sv, db);
                lemma_final_cap(db, params@);
            }
        }
        return r;
    }
    let ghost res0 = plan.res@;
    let res = common::msort::merge_runs(plan.res, plan.runs);
    proof { lemma_res_ok_perm(t, name, res0, res@, params.p1 as int); }
    let cols = build_answer(&res);
    let r = Ok(Answer::Columns(cols));
    proof {
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(params@), r) by {
            lemma_bound_same(sv, db0, db);
            lemma_bound(sv, db);
            lemma_final(db, params@, res@);
        }
    }
    r
}

} // verus!
