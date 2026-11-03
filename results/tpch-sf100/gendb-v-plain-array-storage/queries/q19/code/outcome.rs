//! The fixed claim for each outcome of `query`, over every database bound to the stored parts: every bound database
//! has the stored tables (`tables::lemma_model`), so its body is the one `body` computes from the per-lineitem
//! totals `t = tot(sv, ps, 0, n_l)`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::gendb_entry::{bound_db, capacity_domain, outcome_ok, answer_meets, Answer};
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::runtime::QueryError;
use crate::query::{param_domain, query_spec_at};
use crate::exec::value::{EVal, view_row};
use crate::link::query::view_rows;
use crate::link::expr::i128_max;
use crate::link::outcome::{lemma_outcome_rows, lemma_outcome_err, lemma_view_rows};
use crate::agent::tables::*;
use crate::agent::line::*;
use crate::agent::ast::*;
use crate::agent::bind::adds_ok;
use crate::agent::joined::*;
use crate::agent::agg::*;
use crate::agent::body::*;

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

/// The aggregate row of the totals: the allowed output of every bound database.
pub proof fn lemma_meets_row(sv: StoresView, ps: Seq<Literal>, rows: Vec<Vec<EVal>>)
    requires
        model_ok(sv), param_domain(ps), adds_ok(ps),
        tot(sv, ps, 0, n_l(sv) as int).a_all <= i128_max(),
        view_rows(rows@) == seq![grow(tot(sv, ps, 0, n_l(sv) as int))],
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Rows(rows))),
{
    let t = tot(sv, ps, 0, n_l(sv) as int);
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
        lemma_model(sv, db);
        lemma_body_rows(db, sv, ps);
        lemma_query_shape(ps);
        lemma_outcome_rows(db, query_spec_at(ps), seq![grow(t)]);
    }
}

/// The volume mass beyond `i128::MAX`: every bound database is outside the capacity domain.
pub proof fn lemma_meets_capacity(sv: StoresView, ps: Seq<Literal>)
    requires
        model_ok(sv), param_domain(ps), adds_ok(ps),
        tot(sv, ps, 0, n_l(sv) as int).a_all > i128_max(),
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Capacity)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
        lemma_model(sv, db);
        lemma_body_rows(db, sv, ps);
        lemma_query_shape(ps);
    }
}

/// Some `$k + 10` past int4 and both tables with rows: the meaning of every bound database is that error.
pub proof fn lemma_meets_err(sv: StoresView, ps: Seq<Literal>)
    requires model_ok(sv), param_domain(ps), !adds_ok(ps), n_l(sv) > 0, n_p(sv) > 0,
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::SqlError(SqlError::NumericValueOutOfRange))),
{
    lemma_jrows_len(sv);
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::SqlError(SqlError::NumericValueOutOfRange))) by {
        lemma_model(sv, db);
        lemma_body_err(db, sv, ps);
        lemma_query_shape(ps);
        lemma_outcome_err(db, query_spec_at(ps), SqlError::NumericValueOutOfRange);
    }
}

/// A table without rows: one NULL is the allowed output of every bound database.
pub proof fn lemma_meets_empty(sv: StoresView, ps: Seq<Literal>, rows: Vec<Vec<EVal>>)
    requires
        model_ok(sv), param_domain(ps),
        n_l(sv) == 0 || n_p(sv) == 0,
        view_rows(rows@) == seq![seq![Val::Null]],
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Rows(rows))),
{
    lemma_jrows_len(sv);
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
        lemma_model(sv, db);
        lemma_body_empty(db, sv, ps);
        lemma_query_shape(ps);
        lemma_outcome_rows(db, query_spec_at(ps), seq![seq![Val::Null]]);
    }
}

} // verus!
