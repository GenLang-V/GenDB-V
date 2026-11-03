//! TPC-H Q9 (product type profit measure) over the storages `facts` (lineitem, orders), `custpart` (part) and
//! `suppliers` (partsupp, supplier, nation).
//!
//! Plan: the part names are filtered once into a bit per part row (`pfilter`, one task per part range); then one
//! task per range of stored lineitem rows (`scan`) looks up, for each row whose part bit is set, its supplier's
//! nation, its partsupp row and its order (a cursor along the co-clustered orders) and adds the row's profit to the
//! cell of (order year, nation row); the calling thread merges the cells (`drive`), folds nation rows of equal name
//! and sorts the groups by nation, year DESC.
use vstd::prelude::*;
pub mod common;
pub mod model;
pub mod cols;
pub mod facts;
pub mod year;
pub mod qspec;
pub mod lookups;
pub mod cells;
pub mod sqlrow;
pub mod sqllink;
pub mod sqlsum;
pub mod answer;
pub mod errs;
pub mod scan;
pub mod pfilter;
pub mod build;
pub mod groups;
pub mod prep;
pub mod bits;
pub mod capacity;
pub mod output;
pub mod ptable;
pub mod drive;
pub mod shuffle;
pub mod rowbm;
pub mod sigmask;

use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::{Answer, answer_meets, bound_db, stores_ready, outcome_ok};
use crate::query::query_spec_at;
use crate::gendb_params::Params;
use crate::query::param_domain;
use crate::spec::value::*;
use model::*;

verus! {

/// The query: the groups (nation, year) with their profit sums, sorted, as the fixed SQL claim requires.
pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost db0 = choose|db: Database| #[trigger] bound_db(sv, db);
    proof { facts::lemma_model(sv, db0); }
    let ghost m = model_of(sv);
    let c = cols::load(stores, Ghost(m));
    let r = drive::run(c, params, workers, dispatch, Ghost(m));
    proof {
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(params@), r) by {
            facts::lemma_model(sv, db);
            assert(answer::bound_ok(db, m, params@));
        }
    }
    r
}

} // verus!
