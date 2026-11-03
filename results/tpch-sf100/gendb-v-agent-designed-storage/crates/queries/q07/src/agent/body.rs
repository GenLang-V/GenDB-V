//! The statement's body over a database of the schema: the derived table `shipping` evaluates to the SELECT
//! list of the joined rows the WHERE keeps (`ship`, `lemma_eval_shipping`), any per-row sum over it is a sum
//! over lineitem (`lemma_ship_sum`), and the GROUP BY is the normal form `g7` over it (`lemma_body`).
//!
//! Inputs: `tables_typed` (the columns the statement reads carry their declared types, from `db_wf`) and
//! `keys_unique` (the primary keys of supplier, orders, customer and nation, from the declared constraints).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::types::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::spec::numeric::*;
use crate::spec::typing::*;
use crate::spec::constraints::*;
use crate::spec::order::*;
use crate::spec::equality::*;
use crate::spec::limits::*;
use crate::schema::schema_spec;
use crate::gendb_constraints::{declared_db, declared_schema};
use crate::link::join::*;
use crate::link::query::*;
use crate::link::expr::lemma_compare_int;
use crate::bridge::equality::same_exact_type;
use crate::bridge::collect::lemma_collect_all;
use crate::exec::relational::domain::lemma_collect_pointwise;
use crate::query::{query_spec_at, param_typed};
use super::common::keysum::*;
use super::sqlq::*;
use super::reduce::*;

verus! {

// ------------------------------------------------------------------------------------------------ table rows

pub open spec fn sup_typed(r: Row) -> bool { r.len() == 7 && r[0] is Int && r[3] is Int }
pub open spec fn li_typed(r: Row) -> bool {
    r.len() == 16 && r[0] is Int && r[2] is Int && num152(r[5]) && num152(r[6]) && r[10] is Date
}
pub open spec fn ord_typed(r: Row) -> bool { r.len() == 9 && r[0] is Int && r[1] is Int }
pub open spec fn cust_typed(r: Row) -> bool { r.len() == 8 && r[0] is Int && r[3] is Int }
pub open spec fn nat_typed(r: Row) -> bool { r.len() == 4 && r[0] is Int && r[1] is Text }

/// The columns the statement reads carry their declared types.
pub open spec fn tables_typed(db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& forall|i: int| 0 <= i < t_sup(db).len() ==> sup_typed(#[trigger] t_sup(db)[i])
    &&& forall|i: int| 0 <= i < t_li(db).len() ==> li_typed(#[trigger] t_li(db)[i])
    &&& forall|i: int| 0 <= i < t_ord(db).len() ==> ord_typed(#[trigger] t_ord(db)[i])
    &&& forall|i: int| 0 <= i < t_cust(db).len() ==> cust_typed(#[trigger] t_cust(db)[i])
    &&& forall|i: int| 0 <= i < t_nat(db).len() ==> nat_typed(#[trigger] t_nat(db)[i])
}

/// The column types of the schema the statement reads.
proof fn lemma_schema_cols()
    ensures
        schema_spec().len() == 8,
        schema_spec()[5].columns.len() == 7,
        schema_spec()[5].columns[0] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[5].columns[3] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[0].columns.len() == 16,
        schema_spec()[0].columns[0] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[0].columns[2] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[0].columns[5] == (Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }),
        schema_spec()[0].columns[6] == (Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }),
        schema_spec()[0].columns[10] == (Column { ty: SqlType::Date, nullable: false }),
        schema_spec()[1].columns.len() == 9,
        schema_spec()[1].columns[0] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[1].columns[1] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[2].columns.len() == 8,
        schema_spec()[2].columns[0] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[2].columns[3] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[6].columns.len() == 4,
        schema_spec()[6].columns[0] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[6].columns[1] == (Column { ty: SqlType::Text, nullable: false }),
{
    assert(schema_spec().len() == 8) by (compute);
    assert(schema_spec()[5].columns.len() == 7) by (compute);
    assert(schema_spec()[5].columns[0] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
    assert(schema_spec()[5].columns[3] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
    assert(schema_spec()[0].columns.len() == 16) by (compute);
    assert(schema_spec()[0].columns[0] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
    assert(schema_spec()[0].columns[2] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
    assert(schema_spec()[0].columns[5] == (Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false })) by (compute);
    assert(schema_spec()[0].columns[6] == (Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false })) by (compute);
    assert(schema_spec()[0].columns[10] == (Column { ty: SqlType::Date, nullable: false })) by (compute);
    assert(schema_spec()[1].columns.len() == 9) by (compute);
    assert(schema_spec()[1].columns[0] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
    assert(schema_spec()[1].columns[1] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
    assert(schema_spec()[2].columns.len() == 8) by (compute);
    assert(schema_spec()[2].columns[0] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
    assert(schema_spec()[2].columns[3] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
    assert(schema_spec()[6].columns.len() == 4) by (compute);
    assert(schema_spec()[6].columns[0] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
    assert(schema_spec()[6].columns[1] == (Column { ty: SqlType::Text, nullable: false })) by (compute);
}

/// A database of the schema in the input domain has typed tables.
pub proof fn lemma_tables_typed(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures tables_typed(db),
{
    lemma_schema_cols();
    let s = schema_spec();
    assert forall|i: int| 0 <= i < t_sup(db).len() implies sup_typed(#[trigger] t_sup(db)[i]) by {
        let r = db.tables[5][i];
        assert(row_in_table(r, s[5]));
        assert(value_in_column(r[0], s[5].columns[0]));
        assert(value_in_column(r[3], s[5].columns[3]));
    }
    assert forall|i: int| 0 <= i < t_li(db).len() implies li_typed(#[trigger] t_li(db)[i]) by {
        let r = db.tables[0][i];
        assert(row_in_table(r, s[0]));
        assert(value_in_column(r[0], s[0].columns[0]));
        assert(value_in_column(r[2], s[0].columns[2]));
        assert(value_in_column(r[5], s[0].columns[5]));
        assert(value_in_column(r[6], s[0].columns[6]));
        assert(value_in_column(r[10], s[0].columns[10]));
    }
    assert forall|i: int| 0 <= i < t_ord(db).len() implies ord_typed(#[trigger] t_ord(db)[i]) by {
        let r = db.tables[1][i];
        assert(row_in_table(r, s[1]));
        assert(value_in_column(r[0], s[1].columns[0]));
        assert(value_in_column(r[1], s[1].columns[1]));
    }
    assert forall|i: int| 0 <= i < t_cust(db).len() implies cust_typed(#[trigger] t_cust(db)[i]) by {
        let r = db.tables[2][i];
        assert(row_in_table(r, s[2]));
        assert(value_in_column(r[0], s[2].columns[0]));
        assert(value_in_column(r[3], s[2].columns[3]));
    }
    assert forall|i: int| 0 <= i < t_nat(db).len() implies nat_typed(#[trigger] t_nat(db)[i]) by {
        let r = db.tables[6][i];
        assert(row_in_table(r, s[6]));
        assert(value_in_column(r[0], s[6].columns[0]));
        assert(value_in_column(r[1], s[6].columns[1]));
    }
}

// ------------------------------------------------------------------------------------------------ primary keys

/// The first declared constraint of supplier, orders, customer and nation is the primary key on column 0.
proof fn lemma_pk_decls()
    ensures
        declared_schema().len() == 8,
        declared_schema()[5].constraints.len() > 0,
        declared_schema()[5].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }),
        declared_schema()[1].constraints.len() > 0,
        declared_schema()[1].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }),
        declared_schema()[2].constraints.len() > 0,
        declared_schema()[2].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }),
        declared_schema()[6].constraints.len() > 0,
        declared_schema()[6].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true }),
{
    assert(declared_schema().len() == 8) by (compute);
    assert(declared_schema()[5].constraints.len() > 0) by (compute);
    assert(declared_schema()[5].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true })) by (compute);
    assert(declared_schema()[1].constraints.len() > 0) by (compute);
    assert(declared_schema()[1].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true })) by (compute);
    assert(declared_schema()[2].constraints.len() > 0) by (compute);
    assert(declared_schema()[2].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true })) by (compute);
    assert(declared_schema()[6].constraints.len() > 0) by (compute);
    assert(declared_schema()[6].constraints[0] == (Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true })) by (compute);
}

/// A table with a primary key on an integer column 0 has a unique column 0.
proof fn lemma_pk_unique(db: Database, t: int)
    requires
        constraints_hold(declared_db(db)),
        db.tables.len() == 8,
        t == 5 || t == 1 || t == 2 || t == 6,
        forall|i: int| 0 <= i < db.tables[t].len() ==> (#[trigger] db.tables[t][i])[0] is Int,
    ensures key_unique(db.tables[t], 0),
{
    let ddb = declared_db(db);
    lemma_pk_decls();
    let rows = db.tables[t];
    let cols = seq![0nat];
    assert forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < rows.len() && #[trigger] colv(rows[i], 0) == #[trigger] colv(rows[j], 0)
        implies i == j by {
        let (ki, kj) = (key_of(rows[i], cols), key_of(rows[j], cols));
        assert(ki =~= seq![rows[i][0]]);
        assert(kj =~= seq![rows[j][0]]);
        let a = rows[i][0]->Int_0;
        lemma_compare_int(a, a);
        assert(val_not_distinct(ki[0], kj[0]));
        assert(row_not_distinct(ki, kj));
        crate::bridge::constraints::lemma_primary_key_identifies(ddb, t, 0, cols, true, i, j);
    }
}

/// The shapes and keys of `reduce::red_ok`.
pub proof fn lemma_inputs_ok(db: Database)
    requires tables_typed(db), constraints_hold(declared_db(db)),
    ensures red_ok(db),
{
    assert forall|i: int| 0 <= i < db.tables[5].len() implies (#[trigger] db.tables[5][i])[0] is Int by {
        assert(sup_typed(t_sup(db)[i]));
    }
    assert forall|i: int| 0 <= i < db.tables[1].len() implies (#[trigger] db.tables[1][i])[0] is Int by {
        assert(ord_typed(t_ord(db)[i]));
    }
    assert forall|i: int| 0 <= i < db.tables[2].len() implies (#[trigger] db.tables[2][i])[0] is Int by {
        assert(cust_typed(t_cust(db)[i]));
    }
    assert forall|i: int| 0 <= i < db.tables[6].len() implies (#[trigger] db.tables[6][i])[0] is Int by {
        assert(nat_typed(t_nat(db)[i]));
    }
    lemma_pk_unique(db, 5);
    lemma_pk_unique(db, 1);
    lemma_pk_unique(db, 2);
    lemma_pk_unique(db, 6);
    assert(all_len(t_sup(db), 7)) by { assert forall|i: int| 0 <= i < t_sup(db).len() implies (#[trigger] t_sup(db)[i]).len() == 7 by { assert(sup_typed(t_sup(db)[i])); } }
    assert(all_len(t_li(db), 16)) by { assert forall|i: int| 0 <= i < t_li(db).len() implies (#[trigger] t_li(db)[i]).len() == 16 by { assert(li_typed(t_li(db)[i])); } }
    assert(all_len(t_ord(db), 9)) by { assert forall|i: int| 0 <= i < t_ord(db).len() implies (#[trigger] t_ord(db)[i]).len() == 9 by { assert(ord_typed(t_ord(db)[i])); } }
    assert(all_len(t_cust(db), 8)) by { assert forall|i: int| 0 <= i < t_cust(db).len() implies (#[trigger] t_cust(db)[i]).len() == 8 by { assert(cust_typed(t_cust(db)[i])); } }
    assert(all_len(t_nat(db), 4)) by { assert forall|i: int| 0 <= i < t_nat(db).len() implies (#[trigger] t_nat(db)[i]).len() == 4 by { assert(nat_typed(t_nat(db)[i])); } }
}

// ------------------------------------------------------------------------------------------------ joined rows typed

pub open spec fn j2_typed(x: Row) -> bool {
    &&& x.len() == 23
    &&& x[0] is Int && x[3] is Int && x[7] is Int && x[9] is Int
    &&& num152(x[12]) && num152(x[13]) && x[17] is Date
}
pub open spec fn j3_typed(x: Row) -> bool {
    &&& x.len() == 32
    &&& x[0] is Int && x[3] is Int && x[7] is Int && x[9] is Int
    &&& num152(x[12]) && num152(x[13]) && x[17] is Date
    &&& x[23] is Int && x[24] is Int
}
pub open spec fn j4_typed(x: Row) -> bool {
    &&& x.len() == 40
    &&& x[0] is Int && x[3] is Int && x[7] is Int && x[9] is Int
    &&& num152(x[12]) && num152(x[13]) && x[17] is Date
    &&& x[23] is Int && x[24] is Int
    &&& x[32] is Int && x[35] is Int
}
pub open spec fn j5_typed(x: Row) -> bool {
    &&& x.len() == 44
    &&& x[0] is Int && x[3] is Int && x[7] is Int && x[9] is Int
    &&& num152(x[12]) && num152(x[13]) && x[17] is Date
    &&& x[23] is Int && x[24] is Int
    &&& x[32] is Int && x[35] is Int
    &&& x[40] is Int && x[41] is Text
}

/// Every row of `a x b` satisfies `fab` when every pair of rows does.
proof fn lemma_product_rows_ok(a: Seq<Row>, b: Seq<Row>, fa: spec_fn(Row) -> bool, fb: spec_fn(Row) -> bool, fab: spec_fn(Row) -> bool)
    requires
        forall|i: int| 0 <= i < a.len() ==> fa(#[trigger] a[i]),
        forall|j: int| 0 <= j < b.len() ==> fb(#[trigger] b[j]),
        forall|x: Row, y: Row| fa(x) && fb(y) ==> #[trigger] fab(x + y),
    ensures forall|k: int| 0 <= k < product_rows(a, b).len() ==> fab(#[trigger] product_rows(a, b)[k]),
{
    crate::bridge::relation::lemma_product_rows_elems(a, b);
    let p = product_rows(a, b);
    assert forall|k: int| 0 <= k < p.len() implies fab(#[trigger] p[k]) by {
        assert(crate::bridge::relation::is_concat(p[k], a, b));
        let (i, j) = choose|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && p[k] == #[trigger] a[i] + #[trigger] b[j];
        assert(fa(a[i]) && fb(b[j]));
    }
}

/// Every joined row of the 6-way product is typed.
pub proof fn lemma_p6_typed(db: Database)
    requires tables_typed(db),
    ensures forall|k: int| 0 <= k < p6(db).len() ==> x_typed(#[trigger] p6(db)[k]),
{
    let f1 = |x: Row| sup_typed(x);
    let fl = |x: Row| li_typed(x);
    let f2 = |x: Row| j2_typed(x);
    assert forall|x: Row, y: Row| f1(x) && fl(y) implies #[trigger] f2(x + y) by {
        let z = x + y;
        assert(z[0] == x[0] && z[3] == x[3] && z[7] == y[0] && z[9] == y[2] && z[12] == y[5] && z[13] == y[6] && z[17] == y[10]);
    }
    lemma_product_rows_ok(t_sup(db), t_li(db), f1, fl, f2);
    let fo = |x: Row| ord_typed(x);
    let f3 = |x: Row| j3_typed(x);
    assert forall|x: Row, y: Row| f2(x) && fo(y) implies #[trigger] f3(x + y) by {
        let z = x + y;
        assert(z[0] == x[0] && z[3] == x[3] && z[7] == x[7] && z[9] == x[9] && z[12] == x[12] && z[13] == x[13] && z[17] == x[17]);
        assert(z[23] == y[0] && z[24] == y[1]);
    }
    lemma_product_rows_ok(p2(db), t_ord(db), f2, fo, f3);
    let fc = |x: Row| cust_typed(x);
    let f4 = |x: Row| j4_typed(x);
    assert forall|x: Row, y: Row| f3(x) && fc(y) implies #[trigger] f4(x + y) by {
        let z = x + y;
        assert(z[0] == x[0] && z[3] == x[3] && z[7] == x[7] && z[9] == x[9] && z[12] == x[12] && z[13] == x[13] && z[17] == x[17]);
        assert(z[23] == x[23] && z[24] == x[24] && z[32] == y[0] && z[35] == y[3]);
    }
    lemma_product_rows_ok(p3(db), t_cust(db), f3, fc, f4);
    let fnat = |x: Row| nat_typed(x);
    let f5 = |x: Row| j5_typed(x);
    assert forall|x: Row, y: Row| f4(x) && fnat(y) implies #[trigger] f5(x + y) by {
        let z = x + y;
        assert(z[0] == x[0] && z[3] == x[3] && z[7] == x[7] && z[9] == x[9] && z[12] == x[12] && z[13] == x[13] && z[17] == x[17]);
        assert(z[23] == x[23] && z[24] == x[24] && z[32] == x[32] && z[35] == x[35] && z[40] == y[0] && z[41] == y[1]);
    }
    lemma_product_rows_ok(p4(db), t_nat(db), f4, fnat, f5);
    let f6 = |x: Row| x_typed(x);
    assert forall|x: Row, y: Row| f5(x) && fnat(y) implies #[trigger] f6(x + y) by {
        let z = x + y;
        assert(z[0] == x[0] && z[3] == x[3] && z[7] == x[7] && z[9] == x[9] && z[12] == x[12] && z[13] == x[13] && z[17] == x[17]);
        assert(z[23] == x[23] && z[24] == x[24] && z[32] == x[32] && z[35] == x[35] && z[40] == x[40] && z[41] == x[41]);
        assert(z[44] == y[0] && z[45] == y[1]);
    }
    lemma_product_rows_ok(p5(db), t_nat(db), f5, fnat, f6);
}

// ------------------------------------------------------------------------------------------------ evaluation

/// The WHERE condition as a row predicate.
pub open spec fn jqf(ps: Seq<Literal>) -> spec_fn(Row) -> bool {
    |x: Row| jq(ps, x)
}

/// The rows of the derived table `shipping`.
pub open spec fn ship(db: Database, ps: Seq<Literal>) -> Seq<Row> {
    keep(p6(db), jqf(ps)).map_values(|x: Row| px(x))
}

/// One unfolding step: a product of two evaluated inputs.
proof fn lemma_product_step(db: Database, l: Query, r: Query, a: Seq<Row>, b: Seq<Row>)
    requires
        eval_query(db, Seq::empty(), l) == Ok::<Relation, SqlError>(a),
        eval_query(db, Seq::empty(), r) == Ok::<Relation, SqlError>(b),
    ensures
        eval_query(db, Seq::empty(), Query::Product { left: Box::new(l), right: Box::new(r) }) == Ok::<Relation, SqlError>(product_rows(a, b)),
{
}

/// One unfolding step: a base table.
proof fn lemma_table_step(db: Database, t: nat)
    requires t < db.tables.len(),
    ensures eval_query(db, Seq::empty(), Query::Table(t)) == Ok::<Relation, SqlError>(db.tables[t as int]),
{
}

/// One unfolding step: a SELECT list that evaluates without error on every input row.
proof fn lemma_project_step(db: Database, exprs: Seq<Expr>, input: Query, rows: Seq<Row>, vals: Seq<Row>)
    requires
        eval_query(db, Seq::empty(), input) == Ok::<Relation, SqlError>(rows),
        rows.len() == vals.len(),
        forall|i: int| 0 <= i < rows.len() ==> eval_exprs(db, #[trigger] rows[i], exprs) == Ok::<Row, SqlError>(vals[i]),
    ensures
        eval_query(db, Seq::empty(), Query::Project { exprs, input: Box::new(input) }) == Ok::<Relation, SqlError>(vals),
{
    let ctx = Seq::<Val>::empty();
    let rs = Seq::new(rows.len(), |i: int| eval_exprs(db, ctx + rows[i], exprs));
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(vals[i]) by {
        assert(ctx + rows[i] =~= rows[i]);
    }
    lemma_collect_all(rs, vals);
    lemma_collect_pointwise::<Row>();
    assert(eval_query(db, ctx, input) == Ok::<Relation, SqlError>(rows));
}

/// The FROM list evaluates to the 6-way product.
proof fn lemma_eval_prod(db: Database)
    requires db.tables.len() == 8,
    ensures eval_query(db, Seq::empty(), prod_q()) == Ok::<Relation, SqlError>(p6(db)),
{
    hide(eval_query);
    lemma_table_step(db, 5);
    lemma_table_step(db, 0);
    lemma_table_step(db, 1);
    lemma_table_step(db, 2);
    lemma_table_step(db, 6);
    let q2 = Query::Product { left: Box::new(Query::Table(5)), right: Box::new(Query::Table(0)) };
    lemma_product_step(db, Query::Table(5), Query::Table(0), t_sup(db), t_li(db));
    let q3 = Query::Product { left: Box::new(q2), right: Box::new(Query::Table(1)) };
    lemma_product_step(db, q2, Query::Table(1), p2(db), t_ord(db));
    let q4 = Query::Product { left: Box::new(q3), right: Box::new(Query::Table(2)) };
    lemma_product_step(db, q3, Query::Table(2), p3(db), t_cust(db));
    let q5 = Query::Product { left: Box::new(q4), right: Box::new(Query::Table(6)) };
    lemma_product_step(db, q4, Query::Table(6), p4(db), t_nat(db));
    lemma_product_step(db, q5, Query::Table(6), p5(db), t_nat(db));
}

/// `shipping` evaluates to `ship` (no error: every condition and expression is total on typed rows).
pub proof fn lemma_eval_shipping(db: Database, ps: Seq<Literal>)
    requires tables_typed(db), texts(ps),
    ensures eval_query(db, Seq::empty(), shipping_q(ps)) == Ok::<Relation, SqlError>(ship(db, ps)),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_exprs);
    let rows = p6(db);
    let t = |x: Row| true;
    lemma_eval_prod(db);
    lemma_p6_typed(db);
    crate::link::join::lemma_keep_all(rows, t);
    assert forall|i: int| 0 <= i < rows.len() && t(#[trigger] rows[i]) implies
        eval_pred(db, rows[i], where_pred(ps)) == Ok::<Truth, SqlError>(truth_of(jqf(ps)(rows[i]))) by {
        lemma_where_row(db, ps, rows[i]);
    }
    lemma_eval_filter(db, prod_q(), rows, t, where_pred(ps), jqf(ps), jqf(ps));
    let kept = keep(rows, jqf(ps));
    lemma_keep_members(rows, jqf(ps));
    let vs = kept.map_values(|x: Row| px(x));
    assert forall|i: int| 0 <= i < kept.len() implies eval_exprs(db, #[trigger] kept[i], proj_exprs()) == Ok::<Row, SqlError>(vs[i]) by {
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert(x_typed(rows[m]));
        lemma_proj_row(db, kept[i]);
    }
    lemma_project_step(db, proj_exprs(), filter_q(ps), kept, vs);
}

/// A per-row sum over `shipping` is the sum over lineitem of the lookup term `h1`.
pub proof fn lemma_ship_sum(db: Database, ps: Seq<Literal>, phi: spec_fn(Row) -> int)
    requires red_ok(db),
    ensures sum_of(ship(db, ps), phi) == sum_of(t_li(db), h1(db, ps, phi)),
{
    let rows = p6(db);
    let kept = keep(rows, jqf(ps));
    lemma_sum_of_map(kept, |x: Row| px(x), phi);
    lemma_sum_of_keep(rows, jqf(ps), h6(ps, phi));
    lemma_keep_members(rows, jqf(ps));
    assert forall|i: int| 0 <= i < kept.len() implies (|x: Row| phi((|x: Row| px(x))(x)))(#[trigger] kept[i]) == h6(ps, phi)(kept[i]) by {
        assert(jqf(ps)(kept[i]));
    }
    lemma_sum_of_ext(kept, |x: Row| phi((|x: Row| px(x))(x)), h6(ps, phi));
    lemma_chain(db, ps, phi);
}

// ------------------------------------------------------------------------------------------------ GROUP BY

/// The normal form of the GROUP BY over `shipping`: every row qualifies, the key is the first three columns,
/// the one aggregate SUM sums the scale-4 coefficient of column 3.
pub open spec fn g7() -> QuerySpec {
    QuerySpec {
        qual: |x: Row| true,
        key: |x: Row| seq![x[0], x[1], x[2]],
        arg: |j: int, x: Row| ncoef(x[3]),
        aggs: seq![AggKind::Sum { scale: 4 }],
        outs: seq![0nat, 1, 2, 3],
        grouped: true,
    }
}

/// The identity projection of a 4-column row.
pub open spec fn cols4() -> Seq<nat> {
    seq![0nat, 1, 2, 3]
}

/// Rows of `shipping`: the SELECT list of a typed joined row.
pub open spec fn ship_row(r: Row) -> bool {
    &&& r.len() == 4
    &&& r[0] is Text && r[1] is Text
    &&& r[2] is Num && r[2]->Num_scale == 0
    &&& r[3] is Num && r[3]->Num_scale == 4
}

pub proof fn lemma_ship_rows(db: Database, ps: Seq<Literal>)
    requires tables_typed(db),
    ensures
        forall|i: int| 0 <= i < ship(db, ps).len() ==> ship_row(#[trigger] ship(db, ps)[i]),
        proj_all(ship(db, ps), cols4()) == ship(db, ps),
{
    let rows = p6(db);
    let kept = keep(rows, jqf(ps));
    let sh = ship(db, ps);
    lemma_p6_typed(db);
    lemma_keep_members(rows, jqf(ps));
    assert forall|i: int| 0 <= i < sh.len() implies ship_row(#[trigger] sh[i]) by {
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert(x_typed(rows[m]));
        assert(sh[i] == px(kept[i]));
    }
    assert forall|i: int| 0 <= i < sh.len() implies #[trigger] proj(sh[i], cols4()) == sh[i] by {
        assert(ship_row(sh[i]));
        assert(proj(sh[i], cols4()) =~= sh[i]);
    }
    assert(proj_all(sh, cols4()) =~= sh);
}

/// Per row of `shipping`: the GROUP BY keys and the SUM argument evaluate to the normal form's.
pub proof fn lemma_ship_eval(db: Database, ps: Seq<Literal>, i: int)
    requires
        tables_typed(db),
        0 <= i < ship(db, ps).len(),
    ensures ({
        let r = ship(db, ps)[i];
        &&& proj(r, cols4()) == r
        &&& eval_exprs(db, r, group_keys()) == Ok::<Row, SqlError>((g7().key)(r))
        &&& agg_args(db, r, group_aggs()) == Ok::<Row, SqlError>(arg_vals(g7(), r))
    }),
{
    hide(eval_exprs);
    hide(agg_args);
    let sh = ship(db, ps);
    let r = sh[i];
    let g = g7();
    lemma_ship_rows(db, ps);
    assert(ship_row(r));
    assert(proj(r, cols4()) =~= r);
    lemma_eval_cols(db, r, seq![0nat, 1, 2]);
    assert(col_exprs(seq![0nat, 1, 2]) =~= group_keys());
    assert(select(r, seq![0nat, 1, 2]) =~= seq![r[0], r[1], r[2]]);
    reveal(agg_args);
    let aggs = group_aggs();
    let rs = agg_arg_results(db, r, aggs);
    lemma_agg_arg_results_index(db, r, aggs);
    lemma_agg_arg_sum(db, r, NumKind::Numeric, Expr::Col(3));
    assert(rs[0] == Ok::<Val, SqlError>(r[3]));
    let av = arg_vals(g, r);
    assert(av =~= seq![Val::Num { coeff: ncoef(r[3]), scale: 4 }]);
    assert(r[3] == Val::Num { coeff: ncoef(r[3]), scale: 4 });
    lemma_collect_all(rs, av);
}

/// The GROUP BY keys of `shipping` are exact: texts and numerics of scale 0.
pub proof fn lemma_ship_exact(db: Database, ps: Seq<Literal>)
    requires tables_typed(db),
    ensures keys_exact(g7(), ship(db, ps)),
{
    let g = g7();
    let xs = ship(db, ps);
    lemma_ship_rows(db, ps);
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        assert(ship_row(xs[a]) && ship_row(xs[b]));
        let (ka, kb) = ((g.key)(xs[a]), (g.key)(xs[b]));
        assert(ka.len() == 3 && kb.len() == 3);
        assert forall|m: int| 0 <= m < ka.len() implies same_exact_type(#[trigger] ka[m], kb[m]) by {}
        lemma_row_exact(ka, kb);
    }
}

/// The GROUP BY body is the normal form's rows over `shipping`, inside the SUM capacity.
pub proof fn lemma_body(db: Database, ps: Seq<Literal>)
    requires
        tables_typed(db),
        texts(ps),
        group_caps(g7(), ship(db, ps)),
    ensures
        denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(result_rows(g7(), ship(db, ps))),
{
    hide(eval_query);
    hide(eval_exprs);
    hide(agg_args);
    let g = g7();
    let sh = ship(db, ps);
    let cols = cols4();
    lemma_statement(ps);
    lemma_eval_shipping(db, ps);
    lemma_ship_rows(db, ps);
    let xs = proj_all(sh, cols);
    assert(keep_true(sh, qual_truths(g, xs)) == sh) by {
        crate::link::query::lemma_keep_all(sh, qual_truths(g, xs));
    }
    assert forall|i: int| 0 <= i < sh.len() && (g.qual)(proj(#[trigger] sh[i], cols)) implies
        eval_exprs(db, sh[i], group_keys()) == Ok::<Row, SqlError>((g.key)(proj(sh[i], cols))) by {
        lemma_ship_eval(db, ps, i);
    }
    assert forall|i: int| 0 <= i < sh.len() && (g.qual)(proj(#[trigger] sh[i], cols)) implies
        agg_args(db, sh[i], group_aggs()) == Ok::<Row, SqlError>(arg_vals(g, proj(sh[i], cols))) by {
        lemma_ship_eval(db, ps, i);
    }
    assert(agg_matches(group_aggs()[0], g.aggs[0]));
    assert(aggs_match(group_aggs(), g));
    lemma_ship_exact(db, ps);
    lemma_group_query(db, sh, cols, shipping_q(ps), group_keys(), group_aggs(), g);
    let fulls = gkeys(g, xs).map_values(|k: Row| full_row(g, xs, k));
    let res = result_rows(g, xs);
    assert forall|m: int| 0 <= m < fulls.len() implies #[trigger] fulls[m] == res[m] by {
        let k = gkeys(g, xs)[m];
        assert(full_row(g, xs, k).len() == 4) by {
            lemma_gkeys(g, xs);
            assert(gkeys(g, xs).contains(k));
            lemma_gkeys_witness(g, xs, k);
        }
        lemma_select_identity(full_row(g, xs, k), g.outs);
    }
    assert(fulls =~= res);
}

} // verus!
