//! The fixed claim for each outcome of `query`, over every database bound to the stored parts: the columns read
//! (`li_rows_ok` / `o_match` of the stored relations `rl`, `ro`) are those of every bound database (`lemma_bound`), so
//! the outcome decided from them is the statement's (`body`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::lit_val;
use crate::spec::order::*;
use crate::spec::datetime::*;
use crate::spec::limits::*;
use crate::gendb_entry::bound_db;
use crate::gendb_entry::stores::StoresView;
use crate::query::{param_domain, query_spec_at};
use crate::link::query::*;
use crate::stores::flat_lineitem::interface as li;
use crate::stores::flat_lineitem::declaration as ld;
use crate::stores::flat_orders::interface as oi;
use crate::stores::flat_orders::declaration as od;
use crate::agent::cols::*;
use crate::agent::normal::*;
use crate::agent::body::*;
use crate::agent::source::*;

verus! {

/// The parameter literal is a date with its day number in range.
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

/// What the reads establish about the stores and the parameter.
pub open spec fn read_facts(sv: StoresView, l: LCols, o: OCols, rl: Seq<Seq<Row>>, ro: Seq<Seq<Row>>, ps: Seq<Literal>, pd: int) -> bool {
    &&& li::represents(sv.flat_lineitem, rl)
    &&& oi::represents(sv.flat_orders, ro)
    &&& li_rows_ok(rl[0], l)
    &&& o_match(o, ro[0])
    &&& param_domain(ps)
    &&& pd == date_from_civil(ps[0]->Date_y, ps[0]->Date_m, ps[0]->Date_d)
}

/// A bound database's tables, the parameter and the statement shape.
pub proof fn lemma_bound(sv: StoresView, db: Database, l: LCols, o: OCols, rl: Seq<Seq<Row>>, ro: Seq<Seq<Row>>,
    ps: Seq<Literal>, pd: int)
    requires bound_db(sv, db), read_facts(sv, l, o, rl, ro, ps, pd),
    ensures
        body_hyps(db, db.tables[1], l, ps[0], pd),
        proj_all(db.tables[1], src_cols()) == crows(o),
        db.tables[1].len() == o.no,
        query_spec_at(ps).body == ast_body(ps[0]),
        query_spec_at(ps).keys == ast_order_keys(),
        query_spec_at(ps).limit is None,
        query_spec_at(ps).offset == 0,
{
    li::lemma_represents_determines(sv.flat_lineitem, ld::stored_relations(db), rl);
    oi::lemma_represents_determines(sv.flat_orders, od::stored_relations(db), ro);
    lemma_db_lineitem(db, l);
    lemma_db_orders(db, o);
    lemma_param(ps);
    lemma_query_shape(ps);
    assert(proj_all(db.tables[1], src_cols()).len() == db.tables[1].len());
}

/// Rows: inside `group_caps`, a sorted permutation of the normal form's rows is an allowed output.
pub proof fn lemma_rows_all(sv: StoresView, l: LCols, o: OCols, rl: Seq<Seq<Row>>, ro: Seq<Seq<Row>>, ps: Seq<Literal>,
    pd: int, t1: int, out: Seq<Row>)
    requires
        read_facts(sv, l, o, rl, ro, ps, pd),
        o.no > 0 ==> hi_res(pd) == Ok::<int, SqlError>(t1),
        group_caps(q4_spec(l, pd, t1), crows(o)),
        result_ok(q4_spec(l, pd, t1), ast_order_keys(), 0, None, crows(o), out),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(out)) by {
        lemma_bound(sv, db, l, o, rl, ro, ps, pd);
        lemma_body_ok(db, db.tables[1], l, ps[0], pd, t1);
        lemma_ordered_link(db, query_spec_at(ps), q4_spec(l, pd, t1), crows(o), out);
    }
}

/// A group of more than int8 rows: every bound database's meaning is the error 22003.
pub proof fn lemma_count_error_all(sv: StoresView, l: LCols, o: OCols, rl: Seq<Seq<Row>>, ro: Seq<Seq<Row>>,
    ps: Seq<Literal>, pd: int, t1: int)
    requires
        read_facts(sv, l, o, rl, ro, ps, pd),
        o.no > 0 ==> hi_res(pd) == Ok::<int, SqlError>(t1),
        exists|k: Row| #[trigger] gcount(q4_spec(l, pd, t1), crows(o), k) > int8_max(),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==>
            ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange)),
{
    let k = choose|k: Row| #[trigger] gcount(q4_spec(l, pd, t1), crows(o), k) > int8_max();
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies
        ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange)) by {
        lemma_bound(sv, db, l, o, rl, ro, ps, pd);
        lemma_body_count_error(db, db.tables[1], l, ps[0], pd, t1, k);
    }
}

/// The window's upper bound fails on a non-empty `orders` table: every bound database's meaning is that error.
pub proof fn lemma_hi_err_all(sv: StoresView, l: LCols, o: OCols, rl: Seq<Seq<Row>>, ro: Seq<Seq<Row>>,
    ps: Seq<Literal>, pd: int, e: SqlError)
    requires
        read_facts(sv, l, o, rl, ro, ps, pd),
        o.no > 0,
        hi_res(pd) == Err::<int, SqlError>(e),
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(e)),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies ordered_ok(db, query_spec_at(ps), Err::<Relation, SqlError>(e)) by {
        lemma_bound(sv, db, l, o, rl, ro, ps, pd);
        lemma_body_hi_err(db, db.tables[1], l, ps[0], pd, e);
    }
}

/// An empty `orders` table: the empty result (whatever the upper bound).
pub proof fn lemma_empty_all(sv: StoresView, l: LCols, o: OCols, rl: Seq<Seq<Row>>, ro: Seq<Seq<Row>>,
    ps: Seq<Literal>, pd: int)
    requires read_facts(sv, l, o, rl, ro, ps, pd), o.no == 0,
    ensures
        forall|db: Database| #[trigger] bound_db(sv, db) ==> ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(Seq::empty())),
{
    let g = q4_spec(l, pd, 0);
    assert(crows(o) =~= Seq::<Row>::empty());
    lemma_caps_empty(g);
    lemma_empty_grouped(g, ast_order_keys(), 0, None, Seq::<Row>::empty());
    lemma_rows_all(sv, l, o, rl, ro, ps, pd, 0, Seq::empty());
}

/// `$1 + 3 months` succeeded: it is a valid timestamp.
pub proof fn lemma_hi_valid(pd: int, t1: int)
    requires hi_res(pd) == Ok::<int, SqlError>(t1),
    ensures ts_valid(t1),
{
}

} // verus!
