//! TPC-H Q16 (parts/supplier relationship) over the flat storages `flat_part`, `flat_partsupp`, `flat_supplier`.
//!
//! The statement's meaning is assembled and evaluated in the `sem_*` modules (`sem_result::lemma_answer_rows` and
//! the error lemmas are the final theorems). Execution: the supplier pass finds the excluded supplier keys
//! (`supp`); with a plain `$2` the fast path (`fast`: prefix dictionaries, the parallel part pass `parts`, the
//! parallel distinct-count pass `counts`, the sorted columns `output`) answers when the data has the TPC-H
//! partsupp layout and its other assumptions hold (`sem_link` relates its counts to the statement's groups);
//! otherwise the general serial path (`fallback`) answers.
pub mod model;
pub mod sem_ast;
pub mod common;
pub mod sem_sub;
pub mod sem_row;
pub mod sem_body;
pub mod sem_result;
pub mod cols;
pub mod supp;
pub mod parts;
pub mod counts;
pub mod output;
pub mod order;
pub mod sem_link;
pub mod prep;
pub mod fallback;
pub mod fast;

use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::order::sorted_by;
use crate::exec::relational::schema::view_rows;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::query::param_domain;
use crate::stores::flat_part::interface as pi;
use crate::stores::flat_partsupp::interface as psi;
use crate::stores::flat_supplier::interface as si;
use crate::agent::model::*;
use crate::agent::sem_ast::order_keys;
use crate::agent::sem_row::*;
use crate::agent::sem_result::*;
use crate::agent::cols::read_cols;
use crate::agent::supp::supp_pass;
use crate::agent::prep::size_list;
use crate::agent::fast::{FastOut, fast_answer, plain_exec};
use crate::agent::fallback::fallback;

verus! {

/// The answer when partsupp or part is empty: no rows.
proof fn lemma_empty(sv: StoresView, ps: Seq<crate::spec::ast::Literal>)
    requires stores_wf(sv), param_domain(ps), ps_n(sv) == 0 || part_n(sv) == 0,
    ensures forall|db: Database| #[trigger] bound_db(sv, db)
        ==> crate::spec::order::ordered_ok(db, crate::query::query_spec_at(ps), Ok::<Relation, SqlError>(Seq::<Row>::empty())),
{
    let out = Seq::<Row>::empty();
    assert forall|k: Row| #[trigger] is_group(sv, ps, k) implies gcount(sv, ps, k) <= crate::spec::limits::int8_max() by {
        let (c, a) = choose|c: int, a: int| 0 <= c < ps_n(sv) && 0 <= a < part_n(sv) && #[trigger] qual(sv, ps, c, a) && krow(sv, a) == k;
    }
    assert forall|r: Row| #[trigger] out.contains(r) <==> exists|k: Row| #[trigger] is_group(sv, ps, k) && r == out_row(sv, ps, k) by {
        if exists|k: Row| #[trigger] is_group(sv, ps, k) && r == out_row(sv, ps, k) {
            let k = choose|k: Row| #[trigger] is_group(sv, ps, k) && r == out_row(sv, ps, k);
            let (c, a) = choose|c: int, a: int| 0 <= c < ps_n(sv) && 0 <= a < part_n(sv) && #[trigger] qual(sv, ps, c, a) && krow(sv, a) == k;
        }
    }
    assert(sorted_by(order_keys(), out));
    lemma_answer_rows(sv, ps, out);
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
    proof {
        let db = choose|db: Database| #[trigger] bound_db(sv, db);
        lemma_tables(sv, db);
        lemma_keys(sv, db);
    }
    let np = stores.flat_part.part_len(pi::P_PARTKEY);
    let nq = stores.flat_partsupp.part_len(psi::PS_PARTKEY);
    proof {
        assert(np == part_n(sv));
        assert(nq == ps_n(sv));
    }
    if np == 0 || nq == 0 {
        let rows: Vec<Vec<crate::exec::value::EVal>> = Vec::new();
        proof {
            lemma_empty(sv, ps);
            assert(view_rows(rows@) =~= Seq::<Row>::empty());
        }
        return Ok(Answer::Rows(rows));
    }
    proof {
        assert(is_supplier(sv, ps_skeys(sv)[0] as int));
        assert(supp_n(sv) >= 1);
    }
    let c = read_cols(stores, Ghost(sv));
    let szl = size_list(params);
    proof { lemma_params(ps); }
    if plain_exec(params.p1) {
        match fast_answer(&c, params, &szl, workers, dispatch, Ghost(sv)) {
            FastOut::Done(cols) => return Ok(Answer::Columns(cols)),
            FastOut::Failed(e) => return Err(QueryError::WorkerFailed(e)),
            FastOut::Fallback => {},
        }
    }
    let supp = match supp_pass(&c, Ghost(sv), workers, dispatch) {
        Ok(s) => s,
        Err(e) => return Err(QueryError::WorkerFailed(e)),
    };
    let a = fallback(&c, params, &szl, &supp.ekeys, Ghost(sv));
    Ok(a)
}

} // verus!
