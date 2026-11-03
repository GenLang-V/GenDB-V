//! The fixed claim for each outcome of `query`, over every database bound to the stored parts: the columns read
//! (`cols_match` of the stored relation `rels`) are those of every bound database (`lemma_bound`), so the outcome
//! decided from them is the statement's (`body`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::lit_val;
use crate::spec::order::*;
use crate::spec::datetime::*;
use crate::gendb_entry::{bound_db, capacity_domain};
use crate::gendb_entry::stores::StoresView;
use crate::query::{param_domain, query_spec_at};
use crate::link::query::*;
use crate::link::expr::i128_max;
use crate::link::outcome::{lemma_outcome_rows, lemma_outcome_err};
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_lineitem::declaration::stored_relations;
use crate::agent::normal::*;
use crate::agent::body::*;
use crate::agent::columns::*;
use crate::agent::source::*;

verus! {

/// The parameter literal `$1` is a valid date with its day number inside the declared range.
pub proof fn lemma_param(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures ({
        let p = ps[0];
        &&& p is Date
        &&& 1 <= p->Date_m <= 12
        &&& 1 <= p->Date_d <= 31
        &&& lit_val(p) == Ok::<Val, SqlError>(Val::Date(date_from_civil(p->Date_y, p->Date_m, p->Date_d)))
        &&& -730119 <= date_from_civil(p->Date_y, p->Date_m, p->Date_d) <= 2921939
    }),
{
    assert(date_from_civil(1, 1, 1) == -730119) by (compute);
    assert(date_from_civil(9999, 12, 31) == 2921939) by (compute);
    let p = ps[0];
    assert(days_in_month(p->Date_y, p->Date_m) <= 31);
}

/// What the read establishes about the stores and the parameters.
pub open spec fn read_facts(sv: StoresView, c: Cols, rels: Seq<Seq<Row>>, ps: Seq<Literal>) -> bool {
    &&& li::represents(sv.flat_lineitem, rels)
    &&& cols_match(c, rels[0])
    &&& param_domain(ps)
}

/// A bound database's table and the statement's shape.
pub proof fn lemma_bound(sv: StoresView, db: Database, c: Cols, rels: Seq<Seq<Row>>, ps: Seq<Literal>)
    requires bound_db(sv, db), read_facts(sv, c, rels, ps),
    ensures
        table_hyps(db, db.tables[0]),
        proj_all(db.tables[0], src_cols()) == crows(c),
        db.tables[0].len() == c.n,
        query_spec_at(ps).body == ast_body(ps),
        query_spec_at(ps).keys.len() == 0,
        query_spec_at(ps).limit is None,
        query_spec_at(ps).offset == 0,
{
    li::lemma_represents_determines(sv.flat_lineitem, stored_relations(db), rels);
    lemma_db_rows(c, db);
    lemma_query_shape(ps);
    assert(proj_all(db.tables[0], src_cols()).len() == db.tables[0].len());
}

/// Rows: inside the SUM's capacity condition, the one row `sum_row` is the allowed output.
pub proof fn lemma_rows_all(sv: StoresView, c: Cols, rels: Seq<Seq<Row>>, ps: Seq<Literal>, b: QBounds, t1: int)
    requires
        read_facts(sv, c, rels, ps),
        bounds_ok(ps, b, t1),
        gabs(q6_spec(b), crows(c), Seq::<Val>::empty(), 0) <= i128_max(),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==>
            ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(seq![sum_row(q6_spec(b), crows(c))])),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(seq![sum_row(q6_spec(b), crows(c))])) by {
        lemma_bound(sv, db, c, rels, ps);
        let rows = db.tables[0];
        lemma_pred_agrees(db, rows, ps, b, t1);
        lemma_body_rows(db, rows, ps, b);
        lemma_outcome_rows(db, query_spec_at(ps), seq![sum_row(q6_spec(b), crows(c))]);
    }
}

/// The SUM's absolute mass beyond `i128`: every bound database is outside the capacity domain.
pub proof fn lemma_capacity_all(sv: StoresView, c: Cols, rels: Seq<Seq<Row>>, ps: Seq<Literal>, b: QBounds, t1: int)
    requires
        read_facts(sv, c, rels, ps),
        bounds_ok(ps, b, t1),
        gabs(q6_spec(b), crows(c), Seq::<Val>::empty(), 0) > i128_max(),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> !capacity_domain(db, query_spec_at(ps)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies !capacity_domain(db, query_spec_at(ps)) by {
        lemma_bound(sv, db, c, rels, ps);
        let rows = db.tables[0];
        lemma_pred_agrees(db, rows, ps, b, t1);
        lemma_body_capacity(db, rows, ps, b);
    }
}

/// `$1 + INTERVAL '1' YEAR` fails with `e` on a non-empty table: every bound database's meaning is `e`.
pub proof fn lemma_error_all(sv: StoresView, c: Cols, rels: Seq<Seq<Row>>, ps: Seq<Literal>, pd: int, e: SqlError)
    requires
        read_facts(sv, c, rels, ps),
        c.n > 0,
        lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(pd)),
        year_end_val(pd) == Err::<Val, SqlError>(e),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(e)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(e)) by {
        lemma_bound(sv, db, c, rels, ps);
        lemma_body_err(db, db.tables[0], ps, pd, e);
        lemma_outcome_err(db, query_spec_at(ps), e);
    }
}

/// An empty table: the one row of NULL is every bound database's allowed output (the WHERE is never evaluated).
pub proof fn lemma_empty_all(sv: StoresView, c: Cols, rels: Seq<Seq<Row>>, ps: Seq<Literal>)
    requires read_facts(sv, c, rels, ps), c.n == 0,
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==>
            ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(seq![seq![Val::Null]])),
{
    let b = QBounds { plo: 0, phi: 0, dlo: 0, dhi: 0, qlim: 0 };
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(seq![seq![Val::Null]])) by {
        lemma_bound(sv, db, c, rels, ps);
        let rows = db.tables[0];
        let xs = proj_all(rows, src_cols());
        assert(xs =~= Seq::<Row>::empty());
        assert(pred_agrees(db, rows, src_cols(), ast_pred(ps), q6_spec(b)));
        lemma_body_rows(db, rows, ps, b);
        assert(sum_row(q6_spec(b), xs) =~= seq![Val::Null]);
        lemma_outcome_rows(db, query_spec_at(ps), seq![sum_row(q6_spec(b), xs)]);
    }
}

} // verus!
