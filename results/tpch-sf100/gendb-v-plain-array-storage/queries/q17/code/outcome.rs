//! The fixed claim for each outcome of `query`, over every database bound to the stored parts: every bound database
//! has the stored tables (`tables::lemma_model`), so its body is the one `body` computes from the per-lineitem
//! totals `t = body::tot(sv, ps)`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::fns::div::num_div_fits;
use crate::gendb_entry::{bound_db, outcome_ok, answer_meets, Answer};
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::runtime::QueryError;
use crate::query::{param_domain, query_spec_at};
use crate::exec::value::{EVal, view_row};
use crate::link::query::view_rows;
use crate::link::outcome::{lemma_outcome_rows, lemma_outcome_err, lemma_view_rows};
use crate::agent::tables::*;
use crate::agent::ast::*;
use crate::agent::sub::*;
use crate::agent::joined::*;
use crate::agent::body::*;
use crate::agent::keys::*;
use crate::agent::capacity::lemma_body_capacity;

verus! {

/// The answer of one row with one value.
pub fn single_row(v: EVal) -> (rows: Vec<Vec<EVal>>)
    ensures view_rows(rows@) == seq![seq![v@]],
{
    let mut row: Vec<EVal> = Vec::new();
    row.push(v);
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    rows.push(row);
    proof {
        lemma_view_rows(rows@);
        assert(view_row(rows@[0]@) =~= seq![v@]);
        assert(view_rows(rows@) =~= seq![seq![v@]]);
    }
    rows
}

/// The parameters of the domain are text literals.
pub proof fn lemma_params_text(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures params_text(ps),
{
}

/// The row `[v]` of the totals: the allowed output of every bound database.
pub proof fn lemma_meets_row(sv: StoresView, ps: Seq<Literal>, rows: Vec<Vec<EVal>>, v: Val)
    requires
        model_ok(sv), sizes_ok(sv), param_domain(ps),
        out_val(tot(sv, ps)) == Ok::<Val, SqlError>(v),
        view_rows(rows@) == seq![seq![v]],
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Rows(rows))),
{
    lemma_params_text(ps);
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
        lemma_model(sv, db);
        lemma_body_rows(db, sv, ps);
        lemma_query_shape(ps);
        lemma_outcome_rows(db, query_spec_at(ps), seq![seq![v]]);
    }
}

/// The division's SQL error: the meaning of every bound database.
pub proof fn lemma_meets_div_err(sv: StoresView, ps: Seq<Literal>, e: SqlError)
    requires
        model_ok(sv), sizes_ok(sv), param_domain(ps),
        out_val(tot(sv, ps)) == Err::<Val, SqlError>(e),
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::SqlError(e))),
{
    lemma_params_text(ps);
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::SqlError(e))) by {
        lemma_model(sv, db);
        lemma_body_rows(db, sv, ps);
        lemma_query_shape(ps);
        lemma_outcome_err(db, query_spec_at(ps), e);
    }
}

/// The output's division outside its executable domain: every bound database is outside the capacity domain.
pub proof fn lemma_meets_capacity(sv: StoresView, ps: Seq<Literal>)
    requires model_ok(sv), sizes_ok(sv), param_domain(ps), !out_fits(tot(sv, ps)),
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Capacity)),
{
    lemma_params_text(ps);
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
        lemma_model(sv, db);
        lemma_body_rows(db, sv, ps);
        lemma_query_shape(ps);
    }
}

/// A selected key's AVG division outside its executable domain: every bound database is outside the capacity
/// domain.
pub proof fn lemma_meets_capacity_avg(sv: StoresView, ps: Seq<Literal>, keys: Seq<i64>, srows: Seq<int>, s: int)
    requires
        model_ok(sv), sizes_ok(sv), param_domain(ps),
        keys_ok(keys, srows, sv, ps), 0 <= s < keys.len(),
        kcnt(sv, keys[s] as int) > 0,
        !num_div_fits(ksum(sv, keys[s] as int), 2, kcnt(sv, keys[s] as int), 0),
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Capacity)),
{
    lemma_params_text(ps);
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
        lemma_model(sv, db);
        lemma_body_capacity(db, sv, ps, keys, srows, s);
        lemma_query_shape(ps);
    }
}

} // verus!
