//! The fixed claim for each outcome of `query`, over every database bound to the stored parts: the columns read
//! (`cols_match` of the stored relation `rels`) are those of every bound database (`lemma_bound`), so the outcome
//! decided from them is the statement's (`body`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::lit_val;
use crate::spec::order::*;
use crate::spec::datetime::*;
use crate::spec::limits::int8_max;
use crate::gendb_entry::{bound_db, capacity_domain};
use crate::gendb_entry::stores::StoresView;
use crate::query::{param_domain, query_spec_at};
use crate::exec::relational::domain::fits_query;
use crate::link::query::*;
use crate::link::expr::fits_i128;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_lineitem::declaration::stored_relations;
use crate::agent::normal::*;
use crate::agent::body::*;
use crate::agent::columns::*;
use crate::agent::source::*;
use crate::agent::output::*;

verus! {

/// The parameter literal is a date whose day number fits the stored-date comparison.
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

/// What the read establishes about the stores and the parameter.
pub open spec fn read_facts(sv: StoresView, c: Cols, rels: Seq<Seq<Row>>, ps: Seq<Literal>, pd: int) -> bool {
    &&& li::represents(sv.flat_lineitem, rels)
    &&& cols_match(c, rels[0])
    &&& param_domain(ps)
    &&& pd == date_from_civil(ps[0]->Date_y, ps[0]->Date_m, ps[0]->Date_d)
}

/// A bound database's table, parameter and statement shape.
pub proof fn lemma_bound(sv: StoresView, db: Database, c: Cols, rels: Seq<Seq<Row>>, ps: Seq<Literal>, pd: int)
    requires bound_db(sv, db), read_facts(sv, c, rels, ps, pd),
    ensures
        body_hyps(db, db.tables[0], ps[0], pd),
        proj_all(db.tables[0], src_cols()) == crows(c),
        query_spec_at(ps).body == ast_body(ps[0]),
        query_spec_at(ps).keys == ast_order_keys(),
        query_spec_at(ps).limit is None,
        query_spec_at(ps).offset == 0,
{
    li::lemma_represents_determines(sv.flat_lineitem, stored_relations(db), rels);
    lemma_db_rows(c, db);
    lemma_param(ps);
    lemma_query_shape(ps);
}

/// Rows: inside `group_caps`, a sorted permutation of the normal form's rows is an allowed output.
pub proof fn lemma_rows_all(sv: StoresView, c: Cols, rels: Seq<Seq<Row>>, ps: Seq<Literal>, pd: int, out: Seq<Row>)
    requires
        read_facts(sv, c, rels, ps, pd),
        group_caps(q1_spec(pd), crows(c)),
        result_ok(q1_spec(pd), ast_order_keys(), 0, None, crows(c), out),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)) by {
        lemma_bound(sv, db, c, rels, ps, pd);
        lemma_body_ok(db, db.tables[0], ps[0], pd);
        lemma_ordered_link(db, query_spec_at(ps), q1_spec(pd), crows(c), out);
    }
}

/// A qualifying row whose charge overflows `i128`: every bound database is outside the capacity domain.
pub proof fn lemma_capacity_row_all(sv: StoresView, c: Cols, rels: Seq<Seq<Row>>, ps: Seq<Literal>, pd: int, m: int)
    requires
        read_facts(sv, c, rels, ps, pd),
        0 <= m < c.n,
        q1_qual(pd, crow(c, m)),
        !fits_i128(charge(crow(c, m))),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> !capacity_domain(db, query_spec_at(ps)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies !capacity_domain(db, query_spec_at(ps)) by {
        lemma_bound(sv, db, c, rels, ps, pd);
        lemma_crows(c);
        let rows = db.tables[0];
        assert(proj_all(rows, src_cols())[m] == proj(rows[m], src_cols()));
        lemma_body_row_capacity(db, rows, ps[0], pd, m);
    }
}

/// A group outside its SUM/AVG capacity condition: every bound database is outside the capacity domain.
pub proof fn lemma_group_capacity_all(sv: StoresView, c: Cols, rels: Seq<Seq<Row>>, ps: Seq<Literal>, pd: int)
    requires
        read_facts(sv, c, rels, ps, pd),
        group_capacity(pd, crows(c)),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> !capacity_domain(db, query_spec_at(ps)),
{
    let (k, j) = choose|k: Row, j: int| #[trigger] group_violation(pd, crows(c), k, j);
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies !capacity_domain(db, query_spec_at(ps)) by {
        lemma_bound(sv, db, c, rels, ps, pd);
        lemma_body_group_capacity(db, db.tables[0], ps[0], pd, k, j);
    }
}

/// A group of more than int8 rows: every bound database's meaning is the error 22003.
pub proof fn lemma_count_error_all(sv: StoresView, c: Cols, rels: Seq<Seq<Row>>, ps: Seq<Literal>, pd: int)
    requires
        read_facts(sv, c, rels, ps, pd),
        exists|k: Row| #[trigger] gcount(q1_spec(pd), crows(c), k) > int8_max(),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==>
            ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange)),
{
    let k = choose|k: Row| #[trigger] gcount(q1_spec(pd), crows(c), k) > int8_max();
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange)) by {
        lemma_bound(sv, db, c, rels, ps, pd);
        lemma_body_count_error(db, db.tables[0], ps[0], pd, k);
    }
}

} // verus!
