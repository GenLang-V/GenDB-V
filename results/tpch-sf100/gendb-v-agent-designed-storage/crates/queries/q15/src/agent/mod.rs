//! TPC-H Q15 (top supplier) over the storages `lisupp` (lineitem of `facts` with a key index by l_suppkey) and
//! `suppliers` (supplier).
//!
//! Plan: compute the window `[lo, hi]` of ship dates (`window`); find the largest revenue `M` of a supplier group
//! (`is_max`) and, per supplier row, whether its key is a group of revenue `M`; emit those rows in supplier order
//! (`emit`) and sort them by `s_suppkey`. The general plan (`general`) is exact for any data.
//!
//! Proof: `sql` names the statement's pieces, `group` evaluates `revenue0` and its MAX in any context, `body` the
//! statement body (and its error and capacity outcomes), `answer` takes the plan's `M` and hits to an allowed
//! output, `model` relates the stored parts to every bound database.
use vstd::prelude::*;
pub mod window;
pub mod sql;
pub mod group;
pub mod body;
pub mod model;
pub mod answer;
pub mod emit;
pub mod general;
pub mod common;
pub mod pass1;
pub mod tasks;
pub mod fast;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::order::sort_rows;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db, outcome_ok};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::query::{param_domain, query_spec_at};
use crate::exec::value::EVal;
use crate::exec::ast::EOrderKey;
use crate::exec::relational::order::{sort_rows_exec, view_keys};
use crate::link::query::{view_rows, QuerySpec, group_caps};
use window::*;
use sql::*;
use group::*;
use body::*;
use model::*;
use answer::*;
use emit::*;
use general::*;

verus! {

/// What every bound database gives: its stored relations are what `lisupp` and `suppliers` represent.
proof fn lemma_rels(sv: StoresView, db: Database)
    requires bound_db(sv, db),
    ensures
        crate::stores::lisupp::interface::represents(sv.lisupp, crate::stores::lisupp::declaration::stored_relations(db)),
        crate::stores::suppliers::interface::represents(sv.suppliers, crate::stores::suppliers::declaration::stored_relations(db)),
{
}

/// The ORDER BY keys as executable keys.
fn order_keys_exec() -> (ks: Vec<EOrderKey>)
    ensures view_keys(ks@) == order_keys(),
{
    let ks = vec![EOrderKey { col: 0, desc: false, nulls_first: false }];
    proof {
        assert(view_keys(ks@) =~= order_keys());
    }
    ks
}

/// The rows of the plan's result: `M` and the hits of the supplier rows, sorted by `s_suppkey`.
fn answer_rows(c: &Li, s: &Su, lo: i64, hi: i64, m: i128, hits: &Hits, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(sv),
        param_domain(ps),
        lo as int == lo_of(ps),
        hi_ok(lo_of(ps), hi as int),
        li_link(*c, sv.lisupp),
        su_link(*s, sv.suppliers),
        group_caps(qg(lo as int, hi as int), xs_of(*c)),
        is_max(qg(lo as int, hi as int), xs_of(*c), m as int) || no_groups(qg(lo as int, hi as int), xs_of(*c)),
        hits_ok(*hits, *s, qg(lo as int, hi as int), xs_of(*c), m as int),
    ensures answer_meets(sv, ps, r),
{
    let ghost g = qg(lo as int, hi as int);
    let ghost xs = xs_of(*c);
    proof {
        let db0 = choose|db: Database| #[trigger] bound_db(sv, db);
        lemma_res_db(*s, sv, db0, g, xs, m as int);
    }
    let rows = emit_hits(s, m, hits, Ghost(g), Ghost(xs));
    let keys = order_keys_exec();
    let sorted = sort_rows_exec(&keys, rows);
    proof {
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(sorted))) by {
            lemma_li_db(*c, sv, db);
            lemma_res_db(*s, sv, db, g, xs, m as int);
            lemma_res_perm(db.tables[5], g, xs, xd(db), m as int);
            lemma_caps_perm(lo as int, hi as int, xs, xd(db));
            lemma_res_body(db, ps, hi as int, m as int);
            lemma_rows_ok(db, ps, res_rows(db.tables[5], g, xd(db), m as int));
        }
    }
    Ok(Answer::Rows(sorted))
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
    proof {
        lemma_rels(sv, db0);
    }
    let c = load_li(&mut stores.lisupp, Ghost(crate::stores::lisupp::declaration::stored_relations(db0)));
    let s = load_su(&mut stores.suppliers, Ghost(crate::stores::suppliers::declaration::stored_relations(db0)));
    proof {
        lemma_li_db(c, sv, db0);
        lemma_su_db(s, sv, db0);
    }
    let (lo, hir) = date_window(params);
    let hi = match hir {
        Err(e) => {
            if c.n == 0 {
                let rows: Vec<Vec<EVal>> = Vec::new();
                proof {
                    assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
                        lemma_li_db(c, sv, db);
                        lemma_body_empty(db, ps);
                        lemma_shape(ps);
                        lemma_rows_ok(db, ps, Seq::<Row>::empty());
                        assert(sort_rows(order_keys(), Seq::<Row>::empty()) =~= Seq::<Row>::empty());
                        assert(view_rows(rows@) =~= Seq::<Row>::empty());
                    }
                }
                return Ok(Answer::Rows(rows));
            }
            proof {
                assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::SqlError(e))) by {
                    lemma_li_db(c, sv, db);
                    lemma_body_err(db, ps);
                    lemma_shape(ps);
                }
            }
            return Ok(Answer::SqlError(e));
        },
        Ok(h) => h,
    };
    match fast::fast(&c, &s, lo, hi, workers, dispatch) {
        Err(e) => return Err(QueryError::WorkerFailed(e)),
        Ok(Some((m, hits))) => return answer_rows(&c, &s, lo, hi, m, &hits, Ghost(sv), Ghost(ps)),
        Ok(None) => {},
    }
    match general(&c, &s, lo, hi) {
        Err(gk) => {
            proof {
                let k = gk@;
                let g = qg(lo as int, hi as int);
                assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
                    lemma_li_db(c, sv, db);
                    lemma_acc_perm(g, xs_of(c), xd(db), k);
                    lemma_body_capacity(db, ps, hi as int, k);
                }
            }
            Ok(Answer::Capacity)
        },
        Ok((m, hits)) => answer_rows(&c, &s, lo, hi, m, &Hits::Dense(hits), Ghost(sv), Ghost(ps)),
    }
}

} // verus!
