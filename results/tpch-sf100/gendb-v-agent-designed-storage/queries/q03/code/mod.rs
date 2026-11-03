//! TPC-H Q3 (shipping priority) over the storages `li_okruns` (storage `facts`, orders stored by order date and
//! lineitem co-clustered with them, extended by the start row of every l_orderkey run of lineitem) and `custpart`
//! (customer by key). The use of `facts` itself only carries the interface that `li_okruns` extends; every part is
//! read through `li_okruns`.
//!
//! Plan: orders before the date cut (`plan::orders_cut`) own a prefix of the lineitem rows; the window of orders
//! whose lineitems can ship after the date starts at the first lineitem block whose shipdate zone maximum is after
//! it. The window is split into order ranges, one worker task each (`kernel::Chunk`): an order is a group when it is
//! dated before the date, its customer has the segment and some lineitem ships after the date. With dense customer
//! keys and a one-code segment, each task takes its orders in batches: a branch-free pass lists the batch's orders
//! dated before the date whose customer has the segment (a per-call bit set of the segment's customers for few
//! workers, the code column otherwise), then `dirsel` reads each listed order's lineitem run from the run starts
//! (checked against the orders' keys once per batch) and sums it in `i64` (`select` scans key codes instead when the
//! runs do not line up). Otherwise the per-order path of `kernel` tests the customer by `kernel::cust_ok`. Each
//! task keeps its top 10 by revenue DESC, o_orderdate; the calling thread merges them (`drive`). Without the cluster
//! flag a general path scans every lineitem per order.
//!
//! Proof: `facts` reads every bound database through the part-level model (`model`), `qspec` states the groups on the
//! model, `sqlrow`/`sqllink`/`answer` prove that the statement's rows are exactly those groups and that a top 10 of
//! them is an allowed ORDER BY .. LIMIT 10 output, and `capacity` proves the Capacity answer when a group's revenue
//! mass leaves `i128`.
use vstd::prelude::*;
pub mod common;
pub mod model;
pub mod facts;
pub mod qspec;
pub mod sqlrow;
pub mod sqllink;
pub mod answer;
pub mod capacity;
pub mod kernel;
pub mod select;
pub mod dirsel;
pub mod plan;
pub mod load;
pub mod drive;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::{Answer, answer_meets, bound_db, stores_ready, outcome_ok};
use crate::gendb_params::Params;
use crate::query::{param_domain, query_spec_at};
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::exec::value::EVal;
use crate::link::query::view_rows;
use common::topk::*;
use model::*;
use facts::lemma_model;
use qspec::*;
use answer::{bound_ok, lemma_q3_ordered};
use capacity::lemma_q3_capacity;
use kernel::*;
use drive::*;

verus! {

/// Without a customer of the segment there is no group.
proof fn lemma_no_segment(m: M, p: QP)
    requires
        model_ok(m),
        forall|i: int| 0 <= i < m.c_n ==> #[trigger] segtext(m, i) != p.seg,
    ensures
        gseq(m, p, 0, m.o_n) == Seq::<Row>::empty(),
        caps_ok(m, p),
{
    assert forall|q: int| 0 <= q < m.o_n implies !#[trigger] good(m, p, q) by {
        let f = cmatch_f(m, p, ocust(m, q));
        assert forall|i: int| 0 <= i < m.c_n implies #[trigger] f(i) == 0 by {}
        common::isum::lemma_isum_zero(m.c_n, f);
    }
    lemma_gseq_none(m, p, 0, m.o_n);
}

/// Every database bound to the parts gives the statement's facts over the model.
proof fn lemma_bound(sv: StoresView, ps: Seq<Literal>, db: Database)
    requires bound_db(sv, db), param_domain(ps),
    ensures bound_ok(db, model_of(sv), ps),
{
    lemma_model(sv, db);
}

/// The query: the top 10 groups of the model (`run_ok`), or Capacity, as the fixed SQL claim requires.
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
    let loaded = load::load(stores, params, Ghost(m), Ghost(p));
    let c = match loaded {
        Some(c) => c,
        None => {
            let rows: Vec<Vec<EVal>> = Vec::new();
            proof {
                lemma_no_segment(m, p);
                lemma_topk_empty(q3_keys(), q3_fams(), 10);
                assert(view_rows(rows@) =~= Seq::<Row>::empty());
                assert forall|db: Database| #[trigger] bound_db(sv, db) implies
                    outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
                    lemma_bound(sv, ps, db);
                    lemma_q3_ordered(db, m, ps, Seq::empty());
                }
            }
            return Ok(Answer::Rows(rows));
        },
    };
    let ro = if c.cluster == 1 && c.idx_ok {
        match run_fast(c, workers, dispatch, Ghost(m), Ghost(p)) {
            Ok(ro) => ro,
            Err(e) => {
                return Err(QueryError::WorkerFailed(e));
            },
        }
    } else {
        run_general(c, Ghost(m), Ghost(p))
    };
    if ro.ovf {
        proof {
            assert forall|db: Database| #[trigger] bound_db(sv, db) implies
                outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
                lemma_bound(sv, ps, db);
                lemma_q3_capacity(db, m, ps, ro.ovf_q as int);
            }
        }
        return Ok(Answer::Capacity);
    }
    proof {
        lemma_dates(m, p, ro.buf@, ro.len as int);
    }
    let rows = emit(&ro.buf, ro.len);
    proof {
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies
            outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
            lemma_bound(sv, ps, db);
            lemma_q3_ordered(db, m, ps, cands_view(ro.buf@, ro.len as int));
        }
    }
    Ok(Answer::Rows(rows))
}

} // verus!
