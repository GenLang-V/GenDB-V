//! The fixed claim for the error, capacity and empty outcomes of `query`, over every database bound to the stored
//! parts (the rows outcome is `answer::lemma_rows_all`): the columns read are those of every bound database
//! (`cols::lemma_bound`), so the outcome decided from them is the statement's (`body`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::order::*;
use crate::gendb_entry::{bound_db, capacity_domain};
use crate::gendb_entry::stores::StoresView;
use crate::query::{param_domain, query_spec_at};
use crate::link::query::*;
use crate::link::expr::i128_max;
use crate::link::outcome::{lemma_outcome_err, lemma_outcome_sorted};
use crate::agent::normal::*;
use crate::agent::cols::*;
use crate::agent::bounds::*;
use crate::agent::groups::*;
use crate::agent::body::*;

verus! {

/// The hypotheses of `body` hold for every bound database.
pub proof fn lemma_db_hyps(sv: StoresView, db: Database, c: Cols, k: SuppKeys, lrels: Seq<Seq<Row>>, srels: Seq<Seq<Row>>,
    ps: Seq<Literal>)
    requires bound_db(sv, db), read_facts(sv, c, k, lrels, srels, ps),
    ensures
        db_hyps(db, db.tables[0], srels[0]),
        xs_of(db.tables[0]) == crows(c),
        db.tables[0].len() == c.n,
{
    lemma_bound(sv, db, c, k, lrels, srels, ps);
    let srows = srels[0];
    assert forall|j: int| 0 <= j < srows.len() implies (#[trigger] srows[j]).len() == 7 && srows[j][0] is Int by {
        assert(keys_match(k, srows));
    }
    assert(proj_all(db.tables[0], src_cols()).len() == db.tables[0].len());
}

/// A group whose absolute SUM mass leaves `i128`: every bound database is outside the capacity domain.
pub proof fn lemma_capacity_all(sv: StoresView, c: Cols, k: SuppKeys, lrels: Seq<Seq<Row>>, srels: Seq<Seq<Row>>,
    ps: Seq<Literal>, b: QBounds, t1: int, key: Row)
    requires
        read_facts(sv, c, k, lrels, srels, ps),
        bounds_ok(ps, b, t1),
        gabs(q_spec(b), crows(c), key, 0) > i128_max(),
    ensures forall|db: Database| #[trigger] bound_db(sv, db) ==> !capacity_domain(db, query_spec_at(ps)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies !capacity_domain(db, query_spec_at(ps)) by {
        lemma_db_hyps(sv, db, c, k, lrels, srels, ps);
        lemma_query_shape(ps);
        lemma_body_capacity(db, db.tables[0], srels[0], ps, b, t1, key);
    }
}

/// `$1 + INTERVAL '3' MONTH` fails with `e` on a non-empty `lineitem`: every bound database's meaning is `e`.
pub proof fn lemma_error_all(sv: StoresView, c: Cols, k: SuppKeys, lrels: Seq<Seq<Row>>, srels: Seq<Seq<Row>>,
    ps: Seq<Literal>, pd: int, e: SqlError)
    requires
        read_facts(sv, c, k, lrels, srels, ps),
        c.n > 0,
        lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(pd)),
        q_end_val(pd) == Err::<Val, SqlError>(e),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(e)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(e)) by {
        lemma_db_hyps(sv, db, c, k, lrels, srels, ps);
        lemma_query_shape(ps);
        lemma_body_err(db, db.tables[0], srels[0], ps, pd, e);
        lemma_outcome_err(db, query_spec_at(ps), e);
    }
}

/// The product with no right rows is empty.
pub proof fn lemma_product_empty(a: Seq<Row>)
    ensures product_rows(a, Seq::<Row>::empty()) == Seq::<Row>::empty(),
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_product_empty(a.drop_last());
        assert(Seq::<Row>::empty().map_values(|r: Row| a.last() + r) =~= Seq::<Row>::empty());
        assert(Seq::<Row>::empty() + Seq::<Row>::empty() =~= Seq::<Row>::empty());
    }
}

/// Without `lineitem` rows the body is empty (its conditions are never evaluated).
pub proof fn lemma_body_no_rows(db: Database, srows: Seq<Row>, p0: Literal)
    requires db.tables.len() == 8, db.tables[0].len() == 0, db.tables[5] == srows,
    ensures eval_query(db, Seq::empty(), ast_body(p0)) == Ok::<Relation, SqlError>(Seq::empty()),
{
    let ctx = Seq::<Val>::empty();
    let e = Seq::<Row>::empty();
    assert(db.tables[0] =~= e);
    assert(eval_query(db, ctx, Query::Table(0)) == Ok::<Relation, SqlError>(e));
    assert(Seq::new(0, |i: int| eval_pred(db, ctx + e[i], p_date(0, p0))) =~= Seq::<Result<Truth, SqlError>>::empty());
    assert(keep_true(e, Seq::<Truth>::empty()) == e);
    assert(eval_query(db, ctx, g_input(0, p0)) == Ok::<Relation, SqlError>(e));
    let prep = Seq::<(Row, Row)>::empty();
    assert(prep.map_values(|p: (Row, Row)| p.0) =~= e);
    assert(prep.map_values(|p: (Row, Row)| p.1) =~= e);
    assert(crate::spec::equality::distinct_rows(e) == e);
    assert(group_rows(g_aggs(0), e, e) == Ok::<Seq<Row>, SqlError>(e)) by {
        assert(Seq::new(0, |gi: int| match agg_row(g_aggs(0), group_members(e, e, e[gi])) {
            Ok(a) => Ok(e[gi] + a),
            Err(err) => Err(err),
        }) =~= Seq::<Result<Row, SqlError>>::empty());
    }
    assert(eval_query(db, ctx, g_query(0, p0)) == Ok::<Relation, SqlError>(e));
    lemma_product_empty(srows);
    assert(eval_query(db, ctx, Query::Table(5)) == Ok::<Relation, SqlError>(srows));
    assert(eval_query(db, ctx, body_product(p0)) == Ok::<Relation, SqlError>(e));
    assert(eval_query(db, ctx, body_filter(p0)) == Ok::<Relation, SqlError>(e));
    assert(eval_query(db, ctx, ast_body(p0)) == Ok::<Relation, SqlError>(e));
}

/// An empty `lineitem` (whatever the window): the empty answer is every bound database's allowed output.
pub proof fn lemma_empty_all(sv: StoresView, c: Cols, k: SuppKeys, lrels: Seq<Seq<Row>>, srels: Seq<Seq<Row>>, ps: Seq<Literal>)
    requires read_facts(sv, c, k, lrels, srels, ps), c.n == 0,
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(Seq::empty())),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(Seq::empty())) by {
        lemma_db_hyps(sv, db, c, k, lrels, srels, ps);
        lemma_query_shape(ps);
        lemma_body_no_rows(db, srels[0], ps[0]);
        let e = Seq::<Row>::empty();
        assert(sorted_by(query_spec_at(ps).keys, e));
        lemma_outcome_sorted(db, query_spec_at(ps), e, e);
        assert(slice_rows(e, 0, None) =~= e);
    }
}

} // verus!
