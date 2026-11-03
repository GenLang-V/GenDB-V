//! TPC-H Q15 (top supplier) over the flat `lineitem` and `supplier` storages: the suppliers whose revenue
//! `SUM(l_extendedprice * (1 - l_discount))` over the lineitems shipped in `[$1, $1 + 3 months)` is the largest,
//! ordered by `s_suppkey`.
//!
//! Plan of a call (`query`):
//! 1. read `l_shipdate`, `l_suppkey`, `l_extendedprice`, `l_discount` and `s_suppkey` as whole stored parts
//!    (`cols`); compute the shipdate window from `$1` (`bounds`; a failing `$1 + INTERVAL '3' MONTH` is that SQL
//!    error when `lineitem` has a row);
//! 2. the fast path (`fast`): with dense supplier keys, one dense slot table on the calling thread (`scan`), or per
//!    row-range task partitioned (slot, term) lists merged slot range by slot range in parallel (`part`); it declines (`None`) on data unlike dbgen's, and then the serial general path
//!    (`general`) builds the groups exactly (or answers `Capacity` for a group whose mass leaves `i128`);
//! 3. the supplier rows whose key holds the largest SUM become the output rows (`answer::emit_rows`), sorted by
//!    `s_suppkey`.
//!
//! Proof: `normal` states the GROUP BY in the accumulator normal form and its per-row agreement with the AST;
//! `groups` evaluates `revenue0` under any outer context and the MAX subquery; `body` evaluates the whole body
//! (rows, SQL error, capacity); `answer` and `outcome` state the fixed claim for each outcome over every bound
//! database.
use vstd::prelude::*;

pub mod common;
pub mod normal;
pub mod cols;
pub mod bounds;
pub mod groups;
pub mod body;
pub mod answer;
pub mod scan;
pub mod fastspec;
pub mod part;
pub mod fast;
pub mod general;
pub mod outcome;

use crate::spec::value::*;
use crate::spec::ast::*;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db};
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::query::param_domain;
use crate::exec::value::ERow;
use crate::exec::relational::order::sort_rows_exec;
use crate::link::query::view_rows;
use crate::link::outcome::lemma_view_rows;
use crate::stores::flat_lineitem::declaration as ld;
use crate::stores::flat_supplier::declaration as sd;
use crate::agent::common::selection::range_filter;
use crate::agent::normal::*;
use crate::agent::cols::*;
use crate::agent::bounds::*;
use crate::agent::answer::*;
use crate::agent::fastspec::g_of;
use crate::agent::fast::fast_path;
use crate::agent::general::{general_path, GeneralOut};
use crate::agent::outcome::*;

verus! {

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
    let ghost lrels = ld::stored_relations(db0);
    let ghost srels = sd::stored_relations(db0);
    let c = read_cols(&mut stores.flat_lineitem, Ghost(lrels));
    let k = read_keys(&mut stores.flat_supplier, Ghost(srels));
    proof {
        assert(read_facts(sv, c, k, lrels, srels, ps));
        lemma_bound(sv, db0, c, k, lrels, srels, ps);
    }
    let (w, t1) = match param_bounds(params) {
        ParamBounds::Window { w, t1 } => (w, t1),
        ParamBounds::Error(e) => {
            if c.n == 0 {
                let empty: Vec<ERow> = Vec::new();
                proof {
                    lemma_empty_all(sv, c, k, lrels, srels, ps);
                    lemma_view_rows(empty@);
                    assert(view_rows(empty@) =~= Seq::<Row>::empty());
                }
                return Ok(Answer::Rows(empty));
            }
            proof {
                lemma_param(ps);
                lemma_error_all(sv, c, k, lrels, srels, ps, param_day(ps), e);
            }
            return Ok(Answer::SqlError(e));
        },
    };
    let ghost b = qb_of(w);
    let ghost g = g_of(w);
    let (idxs, best) = match fast_path(&c, &k, w, workers, dispatch, Ghost(srels[0])) {
        Err(f) => return Err(QueryError::WorkerFailed(f)),
        Ok(Some((idxs, best))) => (idxs, best as i128),
        Ok(None) => match general_path(&c, &k, w, Ghost(srels[0])) {
            GeneralOut::Capacity { key } => {
                proof {
                    lemma_capacity_all(sv, c, k, lrels, srels, ps, b, t1 as int, key@);
                }
                return Ok(Answer::Capacity);
            },
            GeneralOut::Picks { idxs, best } => (idxs, best),
        },
    };
    let ghost sel = range_filter(0, k.ns as int, pick_of(g, crows(c), srels[0], best as int));
    let rows = emit_rows(stores, &k, &idxs, best, Ghost(srels), Ghost(sel));
    let keys = order_keys();
    let sorted = sort_rows_exec(&keys, rows);
    proof {
        lemma_rows_all(sv, c, k, lrels, srels, ps, b, t1 as int, sel);
    }
    Ok(Answer::Rows(sorted))
}

} // verus!
