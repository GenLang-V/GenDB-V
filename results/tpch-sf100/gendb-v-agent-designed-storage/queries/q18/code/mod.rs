// AUTHOR MODULE ROOT (crate::agent). You own every file under src/agent/.
//! TPC-H Q18 (large volume customer) over the storages `liruns` (the lineitem and orders parts of `facts`: orders
//! stored by order date, lineitem co-clustered with them; plus the run lengths of equal l_orderkey and a zone map of
//! l_quantity) and `custpart` (customer by key).
//!
//! Plan: the lineitem rows of an order are one contiguous run in the order's stored position (checked co-clustering
//! flag), and `liruns` lists the runs' lengths. The runs are split into at most `workers` ranges of about equal run
//! counts, cut at sampled run starts (`drive::plan_runs`); each worker task (`kernel::Chunk`) walks its runs
//! (`scan::scan_runs`): a run of `len` rows can only be above `$1` when `len` times the largest l_quantity (the
//! zone map) is, so only those runs' quantities are read and summed exactly; an order is a group when that sum is
//! above `$1` (the IN subquery's HAVING) and its customer exists (`kernel::cust_find`: one probe at the dense key
//! position, else the key index). When only runs of the longest length can be above `$1` (`kmin >= lg_max`: 7-line
//! orders for `$1 >= 300`), the chunk instead visits just those runs through `liruns`' run permutation by length
//! (`scan::scan_long`: their start rows, one block-local code sum each, no per-run branch over the 150M runs); the
//! orders above `$1` are probed at their run index first (`plan::find_order_guess`). Without the run directory the
//! chunks scan every lineitem row (`scan::scan_chunk`).
//! Each task keeps its top 100 by o_totalprice DESC, o_orderdate; the calling thread merges them in range order and
//! reads c_name for the result rows (`drive::emit`). Without the cluster flag a general path scans every lineitem
//! per order.
//!
//! Proof: `facts` reads every bound database through the part-level model (`model`); `subq` evaluates the IN
//! subquery (GROUP BY l_orderkey HAVING SUM(l_quantity) > $1) under every joined row as the model's `qspec::big`;
//! `sqlrow`/`sqllink`/`answer` prove that the statement's rows are exactly the good orders' rows (`qspec::gseq`) and
//! that a top 100 of them is an allowed ORDER BY .. LIMIT 100 output. Every group's SUM fits `i128` (at most `l_n`
//! rows of at most 15 digits), so there is no capacity case.
use vstd::prelude::*;
pub mod common;
pub mod model;
pub mod facts;
pub mod qspec;
pub mod rels;
pub mod subq;
pub mod subqrow;
pub mod sqlrow;
pub mod sqllink;
pub mod answer;
pub mod cand;
pub mod kernel;
pub mod scan;
pub mod plan;
pub mod drive;
pub mod load;
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::{Answer, answer_meets, bound_db, stores_ready, outcome_ok};
use crate::gendb_params::Params;
use crate::query::{param_domain, query_spec_at};
use crate::spec::value::*;
use crate::spec::ast::Literal;
use model::*;
use facts::lemma_model;
use qspec::*;
use cand::*;
use answer::{bound_ok, lemma_q18_ordered};
use drive::*;

verus! {

/// Every database bound to the parts gives the statement's facts over the model.
proof fn lemma_bound(sv: crate::gendb_entry::stores::StoresView, ps: Seq<Literal>, db: Database)
    requires bound_db(sv, db), param_domain(ps),
    ensures bound_ok(db, model_of(sv), ps),
{
    lemma_model(sv, db);
}

/// The query: the top 100 groups of the model (`run_ok`), as the fixed SQL claim requires.
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
    let ghost db0 = choose|db: Database| bound_db(sv, db);
    proof {
        lemma_model(sv, db0);
    }
    let ghost m = model_of(sv);
    let ghost p = qp_of(ps);
    let c = load::load(stores, params, Ghost(m), Ghost(p));
    let ro = if c.cluster == 1 && c.idx_ok && c.r_mode == 1 {
        match run_runs(c, workers, dispatch, Ghost(m), Ghost(p)) {
            Ok(ro) => ro,
            Err(e) => {
                return Err(QueryError::WorkerFailed(e));
            },
        }
    } else if c.cluster == 1 && c.idx_ok {
        match run_fast(c, workers, dispatch, Ghost(m), Ghost(p)) {
            Ok(ro) => ro,
            Err(e) => {
                return Err(QueryError::WorkerFailed(e));
            },
        }
    } else {
        run_general(c, Ghost(m), Ghost(p))
    };
    proof {
        lemma_dates(m, p, ro.buf@, ro.len as int);
    }
    let rows = emit(&c, &ro.buf, ro.len, Ghost(m), Ghost(p));
    proof {
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies
            outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
            lemma_bound(sv, ps, db);
            lemma_q18_ordered(db, m, ps, cands_view(m, ro.buf@, ro.len as int));
        }
    }
    Ok(Answer::Rows(rows))
}

} // verus!
