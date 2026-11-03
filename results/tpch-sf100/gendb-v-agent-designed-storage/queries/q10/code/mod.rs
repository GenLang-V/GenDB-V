//! TPC-H Q10 (returned item reporting) over the storages `facts` (orders stored by order date with zone maps,
//! lineitem co-clustered with them), `custpart` (customer by key) and `suppliers` (nation).
//!
//! Plan: the orders dated in `[$1, $1 + 3 months)` lie in a window of orders positions found with the date zone
//! maps (`plan::orders_window`); their lineitem rows are one contiguous range. Phase 1 splits the window into order
//! ranges (one worker task each, at most `drive::TASK_CAP`, `phase1::Chunk`): per order, the exact revenue of its
//! returned lineitems (`runs::build_runs`: branch-free key runs with running `i64` totals over chunks of a block with
//! small price/discount bases), recorded packed with the order's customer row in the segment of the customer's
//! partition (`part`: `PW` = 65536 customer rows, so one partition's accumulators stay in L2). Phase 2 splits the partitions into ranges (one task each, `phase2::Agg`):
//! per partition, every phase-1 task's segment is added into one reused accumulator, then scanned into the task's top
//! 20 groups (customers with a returned lineitem in the window whose nation exists) by revenue DESC; the calling
//! thread merges the ranges' top 20 (`drive`). A general serial path (`general`) runs when the layout is not
//! co-clustered, a segment is full or the revenue mass does not fit the fast path's `i64` accumulators.
//!
//! Proof: `facts` reads every bound database through the part-level model (`model`), `qspec` states the groups on
//! the model, `sqlrow`/`sqllink`/`answer` prove that the statement's rows are exactly those groups and that a top
//! 20 of them is an allowed ORDER BY .. LIMIT 20 output, and `capacity` proves the Capacity answer when a group's
//! revenue mass leaves `i128`.
use vstd::prelude::*;
pub mod common;
pub mod model;
pub mod facts;
pub mod qspec;
pub mod window;
pub mod kernel;
pub mod cand;
pub mod recs;
pub mod part;
pub mod plan;
pub mod runs;
pub mod phase1;
pub mod phase2;
pub mod general;
pub mod drive;
pub mod load;
pub mod emit;
pub mod sqlrow;
pub mod sqllink;
pub mod answer;
pub mod capacity;
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::{Answer, answer_meets, bound_db, stores_ready, outcome_ok};
use crate::gendb_params::Params;
use crate::query::{param_domain, query_spec_at};
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::relation::product_rows;
use crate::exec::value::EVal;
use crate::link::query::view_rows;
use crate::link::join::lemma_product_index;
use model::*;
use qspec::*;
use kernel::*;
use general::*;
use window::*;
use sqllink::{from_rows, db_ok};
use answer::*;

verus! {

/// Every database bound to the parts gives the model facts.
proof fn lemma_bound(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures db_ok(db), model_ok(model_of(sv)), rel_ok(model_of(sv), db), facts::kinds_ok(sv),
{
    facts::lemma_model(sv, db);
}

/// The FROM product has one row per combination of a customer, an order, a lineitem and a nation row.
proof fn lemma_from_len(db: Database)
    ensures from_rows(db).len() == db.tables[2].len() * db.tables[1].len() * db.tables[0].len() * db.tables[6].len(),
{
    let (t2, t1, t0, t6) = (db.tables[2], db.tables[1], db.tables[0], db.tables[6]);
    lemma_product_index(t2, t1);
    lemma_product_index(product_rows(t2, t1), t0);
    lemma_product_index(product_rows(product_rows(t2, t1), t0), t6);
}

/// With some table empty, the FROM product is empty.
proof fn lemma_from_empty(db: Database)
    requires db.tables[2].len() == 0 || db.tables[1].len() == 0 || db.tables[0].len() == 0 || db.tables[6].len() == 0,
    ensures from_rows(db).len() == 0,
{
    lemma_from_len(db);
    let (a, b, c, d) = (db.tables[2].len() as int, db.tables[1].len() as int, db.tables[0].len() as int, db.tables[6].len() as int);
    assert(a * b * c * d == 0) by (nonlinear_arith) requires a == 0 || b == 0 || c == 0 || d == 0;
}

/// With every table non-empty, the FROM product is non-empty.
proof fn lemma_from_nonempty(db: Database)
    requires db.tables[2].len() > 0 && db.tables[1].len() > 0 && db.tables[0].len() > 0 && db.tables[6].len() > 0,
    ensures from_rows(db).len() > 0,
{
    lemma_from_len(db);
    let (a, b, c, d) = (db.tables[2].len() as int, db.tables[1].len() as int, db.tables[0].len() as int, db.tables[6].len() as int);
    assert(a * b * c * d > 0) by (nonlinear_arith) requires a > 0, b > 0, c > 0, d > 0;
}

/// The query: the top 20 groups of the model (`run_ok`), Capacity, or the error of `$1 + 3 months`, as the fixed
/// SQL claim requires.
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
        lemma_bound(sv, db0);
        lemma_lit(ps);
    }
    let ghost m = model_of(sv);
    let (lo, hi_r) = date_window(params);
    let nl = stores.facts.part_len(F_L_KEY_C);
    let no = stores.facts.part_len(F_O_KEY_C);
    let nc = stores.custpart.part_len(C_KEY_C);
    let nn = stores.suppliers.part_len(N_KEY_C);
    proof {
        assert(nl == m.l_n && no == m.o_n && nc == m.c_n && nn == m.n_n);
    }
    let hi: i64 = match hi_r {
        Ok(h) => h,
        Err(e) => {
            if nl > 0 && no > 0 && nc > 0 && nn > 0 {
                proof {
                    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
                        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::SqlError(e))) by {
                        lemma_bound(sv, db);
                        lemma_from_nonempty(db);
                        lemma_q10_date_err(db, m, ps);
                    }
                }
                return Ok(Answer::SqlError(e));
            }
            proof {
                assert(crate::spec::datetime::date_valid(lo as int));
            }
            lo - 1
        },
    };
    let ghost p = QP { lo: lo as int, hi: hi as int };
    proof {
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies bound_ok(db, m, ps, p) by {
            lemma_bound(sv, db);
            if hi_r is Err {
                lemma_from_empty(db);
            }
        }
    }
    let c = load::load(stores, lo, hi, Ghost(m), Ghost(p));
    let mut fast: Option<RunOut> = None;
    if c.cluster == 1 && c.idx_ok {
        fast = match drive::run_fast(c, workers, dispatch, Ghost(m), Ghost(p)) {
            Ok(r) => r,
            Err(e) => {
                return Err(QueryError::WorkerFailed(e));
            },
        };
    }
    let ro = match fast {
        Some(ro) => ro,
        None => run_general(&c, Ghost(m), Ghost(p)),
    };
    if ro.ovf {
        proof {
            assert forall|db: Database| #[trigger] bound_db(sv, db) implies
                outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
                capacity::lemma_q10_capacity(db, m, ps, p, ro.ovf_c as int);
            }
        }
        return Ok(Answer::Capacity);
    }
    let t = load::load_txt(stores, Ghost(m));
    let rows = emit::emit(&c, &t, &ro.buf, ro.len, Ghost(m), Ghost(p));
    proof {
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies
            outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
            lemma_q10_ordered(db, m, ps, p, cand::cands_view(m, ro.buf@, ro.len as int));
        }
    }
    Ok(Answer::Rows(rows))
}

} // verus!
