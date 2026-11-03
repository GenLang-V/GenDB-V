// AUTHOR MODULE ROOT (crate::agent). You own every file under src/agent/.
//! TPC-H Q8 (market share per order year) over the storages `factsdir` (lineitem, orders and two key directories),
//! `custpart` (customer, part) and `suppliers` (supplier, nation, region).
//!
//! Index path (`idx`, when both directories are present, block sizes are powers of two and the part, customer and
//! supplier keys are dense, `idxload::load_dirs`): worker tasks walk ranges of the l_partkey directory, skip parts of
//! another type than `$3`, and process the lineitem rows of the others inside the order-date range in staged batches;
//! the merged accumulators are those of every stored row because the key index is a bijection (`idxspec`).
//!
//! Scan path (otherwise): on the calling thread read the column slices (`setup::load_cols`), build the part filter of type `$3`
//! (`pfpar::build_pfilter_par`: bitmaps over the part keys, scanned by worker tasks when the keys are dense) and the
//! nation statuses (`build::build_ntab`); choose the
//! stored lineitem range worth scanning (`run::scan_bounds`); split it into worker tasks that run the scan kernel
//! (`kernel`: part filter, order, date window, customer region, supplier nation, per-year accumulators); merge the
//! tasks' exact accumulators and derive the outcome (`run::answer_of`).
//!
//! Proof: `sql`, `group`, `norm`, `join` state the statement's meaning in per-lineitem terms; `model`, `decode`,
//! `filters`, `bind` tie the scan's per-row contribution to it for every database bound to the parts; `answer`
//! turns the year groups' sums into the statement's outcome.
use vstd::prelude::*;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::spec::ast::Literal;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::query::param_domain;
use crate::spec::value::Database;
use std::sync::Arc;

pub mod sql;
pub mod group;
pub mod norm;
pub mod join;
pub mod model;
pub mod kernel;
pub mod answer;
pub mod bind;
pub mod decode;
pub mod filters;
pub mod setup;
pub mod build;
pub mod run;
pub mod bounds;
pub mod pfpar;
pub mod idx;
pub mod idxspec;
pub mod idxload;
pub mod common;
pub mod cbits;

verus! {

use self::model::*;
use self::kernel::*;
use self::run::*;
use self::idx::*;
use self::idxspec::*;

/// The index path: tasks over the l_partkey directory's entries, merged, then the outcome.
/// Worker counts up to which the index kernel uses the customer region bitmap.
pub const CB_MAX_WORKERS: usize = 2;

fn idx_answer(c: Cols, f: PFilter, nt: NTab, d: Dirs, la: usize, lb: usize, workers: usize, dispatch: &mut Dispatch,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Result<Answer, QueryError>)
    requires
        idx_pre0(c, f, nt, d, 0, d.offs@.len() - 1, la as int, lb as int),
        1 <= workers <= MAX_WORKERS,
        param_domain(ps),
        acc_all(sv, ps, acc_range(c, pm_of(f), nt_view(nt), 0, c.n_l as int)),
    ensures answer_meets(sv, ps, r),
{
    // The serial kernel tests customer regions in a bitmap built here; with more workers the build would delay
    // every task, so they read the nation codes.
    let ghost nt_in = nt;
    let mut nt = nt;
    nt.cbits = if workers <= CB_MAX_WORKERS { self::cbits::build_cbits(&c, &nt) } else { Vec::new() };
    proof {
        assert(nt_view(nt) == nt_view(nt_in));
        assert(ntab_ok(nt));
        assert(bounds_ok(c, f, nt, la as int, lb as int));
    }
    let ghost fv = f;
    let ghost nv = nt;
    let ghost s = acc_range(c, pm_of(fv), nt_view(nv), 0, c.n_l as int);
    let fa = Arc::new(f);
    let na = Arc::new(nt);
    let (tasks, Ghost(es)) = make_idx_tasks(c, fa, na, d, la, lb, workers);
    let ghost ts = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    proof {
        assert forall|t: int| 0 <= t < outs@.len() implies #[trigger] es[t] <= es[t + 1]
            && idx_post(c, fv, nv, d, es[t], es[t + 1], outs@[t]) by {
            assert(ts[t].post(outs@[t]));
            assert(ts[t].pre());
        }
    }
    let tot = merge_idx(&outs, Ghost(c), Ghost(fv), Ghost(nv), Ghost(d), Ghost(es));
    proof {
        lemma_idx_all(c, pm_of(fv), nt_view(nv), d);
        lemma_acc_range_sane(c, pm_of(fv), nt_view(nv), 0, c.n_l as int);
    }
    if tot.ovf {
        proof {
            lemma_capacity(sv, ps, s);
        }
        return Ok(Answer::Capacity);
    }
    answer_of(&tot, Ghost(sv), Ghost(ps))
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
    // ---- setup on the calling thread
    let c = setup::load_cols(stores, Ghost(db0));
    let f0 = build::pfilter_base(&mut stores.custpart, params.p2, Ghost(sv), Ghost(db0), Ghost(ps));
    let nt0 = build::build_ntab(&mut stores.suppliers, params.p0, params.p1, Ghost(sv), Ghost(db0), Ghost(ps));
    proof {
        setup::lemma_tables(sv, db0);
    }
    let clustered0 = setup::first_u64(&mut stores.factsdir, crate::stores::factsdir::interface::FACTS_CLUSTER) == 1;
    proof {
        if clustered0 {
            decode::lemma_clustered(sv, db0, c);
        }
        bounds::lemma_zone(sv, db0, c);
    }
    if let Some(d) = idxload::load_dirs(&mut stores.factsdir, &c, &f0, Ghost(sv), Ghost(db0), Ghost(ps)) {
        let zm0 = setup::whole_i64(&mut stores.factsdir,
            crate::stores::factsdir::interface::ORDERS_FIRST + crate::stores::factsdir::interface::OR_ORDERDATE_ZMAX);
        let (la, lb) = bounds::scan_bounds(&c, &f0, &nt0, clustered0, zm0);
        let ghost s = acc_range(c, pm_of(f0), nt_view(nt0), 0, c.n_l as int);
        proof {
            assert forall|db: Database| #[trigger] bound_db(sv, db) implies self::sql::db_ok(db)
                && self::bind::acc_meets(db, ps, s) by {
                filters::lemma_dmodel(sv, db, ps, c, f0, nt0);
                bind::lemma_bind(db, ps, c, f0, nt_view(nt0), decode::lrows_of(sv, db), decode::omap_of(sv, c.n_o as int));
            }
        }
        return idx_answer(c, f0, nt0, d, la, lb, workers, dispatch, Ghost(sv), Ghost(ps));
    }
    // ---- the scan path
    let f = match pfpar::build_pfilter_par(&mut stores.custpart, params.p2, workers, dispatch, Ghost(sv), Ghost(db0),
        Ghost(ps)) {
        Ok(f) => f,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let ghost f_built = f;
    let f = build::pad_filter(f);
    proof {
        assert(filters::pf_from(sv, ps, f));
    }
    let nt = build::build_ntab(&mut stores.suppliers, params.p0, params.p1, Ghost(sv), Ghost(db0), Ghost(ps));
    proof {
        setup::lemma_tables(sv, db0);
    }
    let clustered = setup::first_u64(&mut stores.factsdir, crate::stores::factsdir::interface::FACTS_CLUSTER) == 1;
    proof {
        if clustered {
            decode::lemma_clustered(sv, db0, c);
        }
    }
    proof {
        bounds::lemma_zone(sv, db0, c);
    }
    let zm = setup::whole_i64(&mut stores.factsdir,
        crate::stores::factsdir::interface::ORDERS_FIRST + crate::stores::factsdir::interface::OR_ORDERDATE_ZMAX);
    let (la, lb) = bounds::scan_bounds(&c, &f, &nt, clustered, zm);
    // ---- the scan
    let ghost fv = f;
    let ghost nv = nt;
    let fa = Arc::new(f);
    let na = Arc::new(nt);
    let (tasks, Ghost(bs)) = make_tasks(c, fa, na, la, lb, clustered, workers);
    let ghost ts = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    proof {
        assert forall|t: int| 0 <= t < outs@.len() implies #[trigger] bs[t] <= bs[t + 1]
            && scan_post(c, fv, nv, bs[t], bs[t + 1], outs@[t]) by {
            assert(ts[t].post(outs@[t]));
            assert(ts[t].pre());
        }
    }
    let tot = merge_outs(&outs, Ghost(c), Ghost(fv), Ghost(nv), Ghost(bs));
    // ---- the outcome
    let ghost s = acc_range(c, pm_of(fv), nt_view(nv), 0, c.n_l as int);
    proof {
        lemma_bounds(c, fv, nv, la as int, lb as int);
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies self::sql::db_ok(db)
            && self::bind::acc_meets(db, ps, s) by {
            filters::lemma_dmodel(sv, db, ps, c, fv, nv);
            bind::lemma_bind(db, ps, c, fv, nt_view(nv), decode::lrows_of(sv, db), decode::omap_of(sv, c.n_o as int));
        }
        lemma_acc_range_sane(c, pm_of(fv), nt_view(nv), 0, c.n_l as int);
    }
    if tot.ovf {
        proof {
            lemma_capacity(sv, ps, s);
        }
        return Ok(Answer::Capacity);
    }
    answer_of(&tot, Ghost(sv), Ghost(ps))
}

} // verus!
