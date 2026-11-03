//! Per-row agreement of the Q5 statement with its normal form (`q5spec`): the FROM product evaluates to the
//! left-deep product of the six tables; every joined full row (47 columns) has the column shapes of the schema;
//! on such a row the WHERE condition evaluates without error to `q5_qual` of its stored projection, the group key
//! to `q5_key`, and the SUM argument to the scale-4 numeric `q5_arg`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::limits::*;
use crate::spec::datetime::*;
use crate::spec::types::*;
use crate::spec::typing::*;
use crate::spec::eval::*;
use crate::spec::relation::*;
use crate::schema::schema_spec;
use crate::query::{param_domain, param_typed, query_spec_at};
use crate::link::query::*;
use crate::link::join::*;
use crate::link::expr::*;
use crate::agent::q5spec::*;

verus! {

// ------------------------------------------------------------------------------------------- statement shape

/// The statement is `q5_body` ordered by `q5_order`, without LIMIT or OFFSET.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures
        query_spec_at(ps) == (OrderedQuery { body: q5_body(ps), keys: q5_order(), limit: None, offset: 0 }),
{
}

// ------------------------------------------------------------------------------------------- the FROM product

/// Table ids of the FROM inputs in order.
pub open spec fn tids() -> Seq<nat> {
    seq![2nat, 1, 0, 5, 6, 7]
}

/// Widths of the full table rows in FROM order.
pub open spec fn full_ws() -> Seq<nat> {
    seq![8nat, 9, 16, 7, 4, 3]
}

/// The stored columns of each FROM input (customer, orders, lineitem, supplier, nation, region).
pub open spec fn fcols6() -> Seq<Seq<nat>> {
    seq![
        seq![0nat, 1, 2, 3, 4, 5, 6, 7],
        seq![0nat, 1, 2, 3, 4, 5, 7],
        seq![0nat, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14],
        seq![0nat, 1, 2, 3, 4, 5, 6],
        seq![0nat, 1, 2, 3],
        seq![0nat, 1, 2],
    ]
}

/// The stored relations of a database.
pub open spec fn rels_of_db(db: Database) -> Rels {
    Rels {
        c: proj_all(db.tables[2], fcols6()[0]),
        o: proj_all(db.tables[1], fcols6()[1]),
        l: proj_all(db.tables[0], fcols6()[2]),
        s: proj_all(db.tables[5], fcols6()[3]),
        n: proj_all(db.tables[6], fcols6()[4]),
        r: proj_all(db.tables[7], fcols6()[5]),
    }
}

/// Positions of the stored columns inside the 47-column joined full row.
pub open spec fn q5_cols() -> Seq<nat> {
    seq![
        0nat, 1, 2, 3, 4, 5, 6, 7,
        8, 9, 10, 11, 12, 13, 15,
        17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
        33, 34, 35, 36, 37, 38, 39,
        40, 41, 42, 43,
        44, 45, 46,
    ]
}

pub proof fn lemma_q5_cols()
    ensures
        q5_cols() == join_cols(full_ws(), fcols6()),
        q5_cols().len() == 44,
        offsets(full_ws()) == seq![0nat, 8, 17, 33, 40, 44, 47],
{
    assert(q5_cols() == join_cols(full_ws(), fcols6())) by (compute);
    assert(offsets(full_ws()) == seq![0nat, 8, 17, 33, 40, 44, 47]) by (compute);
}

/// The left-deep product of the six relations of `ts` named by `s`.
pub proof fn lemma_joined6(ts: Seq<Seq<Row>>, s: Seq<nat>)
    requires s.len() == 6,
    ensures
        joined_of(ts, s) == product_rows(product_rows(product_rows(product_rows(product_rows(
            ts[s[0] as int], ts[s[1] as int]), ts[s[2] as int]), ts[s[3] as int]), ts[s[4] as int]), ts[s[5] as int]),
{
    let s5 = s.drop_last();
    let s4 = s5.drop_last();
    let s3 = s4.drop_last();
    let s2 = s3.drop_last();
    let s1 = s2.drop_last();
    assert(s1.len() == 1 && s1[0] == s[0]);
    assert(s2.last() == s[1] && s3.last() == s[2] && s4.last() == s[3] && s5.last() == s[4] && s.last() == s[5]);
    assert(joined_of(ts, s1) == ts[s[0] as int]);
    assert(joined_of(ts, s2) == product_rows(joined_of(ts, s1), ts[s[1] as int]));
    assert(joined_of(ts, s3) == product_rows(joined_of(ts, s2), ts[s[2] as int]));
    assert(joined_of(ts, s4) == product_rows(joined_of(ts, s3), ts[s[3] as int]));
    assert(joined_of(ts, s5) == product_rows(joined_of(ts, s4), ts[s[4] as int]));
}

/// The FROM clause evaluates to the left-deep product of the six tables.
pub proof fn lemma_from_eval(db: Database)
    requires db.tables.len() == 8,
    ensures eval_query(db, Seq::empty(), q5_from()) == Ok::<Relation, SqlError>(joined_of(db.tables, tids())),
{
    let e = Seq::<Val>::empty();
    let t = db.tables;
    lemma_joined6(t, tids());
    let q1 = Query::Product { left: Box::new(Query::Table(2)), right: Box::new(Query::Table(1)) };
    let q2 = Query::Product { left: Box::new(q1), right: Box::new(Query::Table(0)) };
    let q3 = Query::Product { left: Box::new(q2), right: Box::new(Query::Table(5)) };
    let q4 = Query::Product { left: Box::new(q3), right: Box::new(Query::Table(6)) };
    assert(eval_query(db, e, Query::Table(2)) == Ok::<Relation, SqlError>(t[2]));
    assert(eval_query(db, e, Query::Table(1)) == Ok::<Relation, SqlError>(t[1]));
    assert(eval_query(db, e, q1) == Ok::<Relation, SqlError>(product_rows(t[2], t[1])));
    assert(eval_query(db, e, Query::Table(0)) == Ok::<Relation, SqlError>(t[0]));
    assert(eval_query(db, e, q2) == Ok::<Relation, SqlError>(product_rows(product_rows(t[2], t[1]), t[0])));
    assert(eval_query(db, e, Query::Table(5)) == Ok::<Relation, SqlError>(t[5]));
    assert(eval_query(db, e, q3) == Ok::<Relation, SqlError>(product_rows(product_rows(product_rows(t[2], t[1]), t[0]), t[5])));
    assert(eval_query(db, e, Query::Table(6)) == Ok::<Relation, SqlError>(t[6]));
    assert(eval_query(db, e, q4) == Ok::<Relation, SqlError>(
        product_rows(product_rows(product_rows(product_rows(t[2], t[1]), t[0]), t[5]), t[6])));
    assert(eval_query(db, e, Query::Table(7)) == Ok::<Relation, SqlError>(t[7]));
}

// ------------------------------------------------------------------------------------------- row shapes

pub open spec fn is_int8(v: Val) -> bool {
    v is Int && int8_min() <= v->Int_0 <= int8_max()
}

/// A numeric(15, 2) value: scale 2, fewer than 15 digits in the coefficient.
pub open spec fn is_num15(v: Val) -> bool {
    match v {
        Val::Num { coeff, scale } => scale == 2 && abs(coeff) < pow10(15),
        _ => false,
    }
}

/// The column shapes of a joined full row at the positions the statement reads.
pub open spec fn full_shape(x: Row) -> bool {
    &&& x.len() == 47
    &&& is_int8(x[0]) && is_int8(x[3]) && is_int8(x[8]) && is_int8(x[9]) && x[12] is Date
    &&& is_int8(x[17]) && is_int8(x[19]) && is_num15(x[22]) && is_num15(x[23])
    &&& is_int8(x[33]) && is_int8(x[36]) && is_int8(x[40]) && x[41] is Text && is_int8(x[42])
    &&& is_int8(x[44]) && x[45] is Text
}

/// A part of a joined full row is a row of its table (schema domain).
pub open spec fn part_in_table(i: int, x: Row) -> bool {
    row_in_table(x, schema_spec()[tids()[i] as int])
}

/// The schema columns the statement reads.
pub proof fn lemma_schema_cols()
    ensures
        schema_spec()[2].columns.len() == 8,
        schema_spec()[1].columns.len() == 9,
        schema_spec()[0].columns.len() == 16,
        schema_spec()[5].columns.len() == 7,
        schema_spec()[6].columns.len() == 4,
        schema_spec()[7].columns.len() == 3,
        schema_spec()[2].columns[0] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[2].columns[3] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[1].columns[0] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[1].columns[1] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[1].columns[4] == (Column { ty: SqlType::Date, nullable: false }),
        schema_spec()[0].columns[0] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[0].columns[2] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[0].columns[5] == (Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }),
        schema_spec()[0].columns[6] == (Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }),
        schema_spec()[5].columns[0] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[5].columns[3] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[6].columns[0] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[6].columns[1] == (Column { ty: SqlType::Text, nullable: false }),
        schema_spec()[6].columns[2] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[7].columns[0] == (Column { ty: SqlType::Int8, nullable: false }),
        schema_spec()[7].columns[1] == (Column { ty: SqlType::Text, nullable: false }),
{
    assert(schema_spec()[2].columns.len() == 8) by (compute);
    assert(schema_spec()[1].columns.len() == 9) by (compute);
    assert(schema_spec()[0].columns.len() == 16) by (compute);
    assert(schema_spec()[5].columns.len() == 7) by (compute);
    assert(schema_spec()[6].columns.len() == 4) by (compute);
    assert(schema_spec()[7].columns.len() == 3) by (compute);
    assert(schema_spec()[2].columns[0] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
    assert(schema_spec()[2].columns[3] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
    assert(schema_spec()[1].columns[0] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
    assert(schema_spec()[1].columns[1] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
    assert(schema_spec()[1].columns[4] == (Column { ty: SqlType::Date, nullable: false })) by (compute);
    assert(schema_spec()[0].columns[0] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
    assert(schema_spec()[0].columns[2] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
    assert(schema_spec()[0].columns[5] == (Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false })) by (compute);
    assert(schema_spec()[0].columns[6] == (Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false })) by (compute);
    assert(schema_spec()[5].columns[0] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
    assert(schema_spec()[5].columns[3] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
    assert(schema_spec()[6].columns[0] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
    assert(schema_spec()[6].columns[1] == (Column { ty: SqlType::Text, nullable: false })) by (compute);
    assert(schema_spec()[6].columns[2] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
    assert(schema_spec()[7].columns[0] == (Column { ty: SqlType::Int8, nullable: false })) by (compute);
    assert(schema_spec()[7].columns[1] == (Column { ty: SqlType::Text, nullable: false })) by (compute);
}

/// A value of a NOT NULL int8 column.
pub proof fn lemma_int8_value(v: Val)
    requires value_in_column(v, Column { ty: SqlType::Int8, nullable: false }),
    ensures is_int8(v),
{
}

/// A value of a NOT NULL numeric(15, 2) column.
pub proof fn lemma_num15_value(v: Val)
    requires value_in_column(v, Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }),
    ensures is_num15(v),
{
}

/// Every table of a well-formed database of the schema: rows of their table's width and domain.
pub proof fn lemma_inputs_ok(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures inputs_ok(db.tables, tids(), full_ws(), |i: int, x: Row| part_in_table(i, x)),
{
    lemma_schema_cols();
    assert(schema_spec().len() == 8) by (compute);
    let ok = |i: int, x: Row| part_in_table(i, x);
    assert forall|i: int, k: int| 0 <= i < tids().len() && 0 <= k < db.tables[tids()[i] as int].len() implies
        (#[trigger] db.tables[tids()[i] as int][k]).len() == full_ws()[i] && ok(i, db.tables[tids()[i] as int][k]) by {
        let t = tids()[i] as int;
        assert(row_in_table(db.tables[t][k], db.schema[t]));
        if i == 0 {} else if i == 1 {} else if i == 2 {} else if i == 3 {} else if i == 4 {} else {}
    }
}

/// A joined full row whose parts are rows of their tables has the statement's column shapes.
pub proof fn lemma_full_shape(x: Row)
    requires parts_ok(x, full_ws(), |i: int, p: Row| part_in_table(i, p)),
    ensures full_shape(x),
{
    let ok = |i: int, p: Row| part_in_table(i, p);
    lemma_q5_cols();
    lemma_schema_cols();
    let o = offsets(full_ws());
    lemma_parts_at(x, full_ws(), ok, 0);
    lemma_parts_at(x, full_ws(), ok, 1);
    lemma_parts_at(x, full_ws(), ok, 2);
    lemma_parts_at(x, full_ws(), ok, 3);
    lemma_parts_at(x, full_ws(), ok, 4);
    lemma_parts_at(x, full_ws(), ok, 5);
    let c = x.subrange(0, 8);
    let od = x.subrange(8, 17);
    let l = x.subrange(17, 33);
    let s = x.subrange(33, 40);
    let n = x.subrange(40, 44);
    let r = x.subrange(44, 47);
    assert(row_in_table(c, schema_spec()[2]));
    assert(row_in_table(od, schema_spec()[1]));
    assert(row_in_table(l, schema_spec()[0]));
    assert(row_in_table(s, schema_spec()[5]));
    assert(row_in_table(n, schema_spec()[6]));
    assert(row_in_table(r, schema_spec()[7]));
    assert(value_in_column(c[0], schema_spec()[2].columns[0]));
    assert(value_in_column(c[3], schema_spec()[2].columns[3]));
    assert(value_in_column(od[0], schema_spec()[1].columns[0]));
    assert(value_in_column(od[1], schema_spec()[1].columns[1]));
    assert(value_in_column(od[4], schema_spec()[1].columns[4]));
    assert(value_in_column(l[0], schema_spec()[0].columns[0]));
    assert(value_in_column(l[2], schema_spec()[0].columns[2]));
    assert(value_in_column(l[5], schema_spec()[0].columns[5]));
    assert(value_in_column(l[6], schema_spec()[0].columns[6]));
    assert(value_in_column(s[0], schema_spec()[5].columns[0]));
    assert(value_in_column(s[3], schema_spec()[5].columns[3]));
    assert(value_in_column(n[0], schema_spec()[6].columns[0]));
    assert(value_in_column(n[1], schema_spec()[6].columns[1]));
    assert(value_in_column(n[2], schema_spec()[6].columns[2]));
    assert(value_in_column(r[0], schema_spec()[7].columns[0]));
    assert(value_in_column(r[1], schema_spec()[7].columns[1]));
    lemma_num15_value(l[5]);
    lemma_num15_value(l[6]);
}

// ------------------------------------------------------------------------------------------- the WHERE condition

/// The stored projection of a joined full row at the positions the normal form reads.
pub proof fn lemma_proj_positions(x: Row)
    requires x.len() == 47,
    ensures ({
        let y = proj(x, q5_cols());
        &&& y.len() == 44
        &&& y[0] == x[0] && y[3] == x[3] && y[8] == x[8] && y[9] == x[9] && y[12] == x[12]
        &&& y[15] == x[17] && y[17] == x[19] && y[20] == x[22] && y[21] == x[23]
        &&& y[30] == x[33] && y[33] == x[36] && y[37] == x[40] && y[38] == x[41] && y[39] == x[42]
        &&& y[41] == x[44] && y[42] == x[45]
    }),
{
    lemma_q5_cols();
}

/// Equality of two int8 columns.
proof fn lemma_eq_int(db: Database, x: Row, a: nat, b: nat)
    requires a < x.len(), b < x.len(), is_int8(x[a as int]), is_int8(x[b as int]),
    ensures eval_pred(db, x, eq_cols(a, b)) == Ok::<Truth, SqlError>(truth_of(x[a as int] == x[b as int])),
{
    let (va, vb) = (x[a as int], x[b as int]);
    lemma_expr_col(db, x, a);
    lemma_expr_col(db, x, b);
    lemma_compare_int(va->Int_0, vb->Int_0);
    lemma_pred_cmp(db, x, CmpOp::Eq, Expr::Col(a), Expr::Col(b), va, vb, va->Int_0, vb->Int_0);
}

/// The values of the bound parameters.
pub open spec fn prm_of(ps: Seq<Literal>, hi: int) -> Prm {
    Prm {
        name: ps[0]->Text_0,
        lo: date_from_civil(ps[1]->Date_y, ps[1]->Date_m, ps[1]->Date_d),
        hi,
    }
}

/// The two literals in the declared domain: a text and a valid date.
pub proof fn lemma_params(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures
        ps[0] is Text,
        ps[1] is Date,
        lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Text(ps[0]->Text_0)),
        lit_val(ps[1]) == Ok::<Val, SqlError>(Val::Date(date_from_civil(ps[1]->Date_y, ps[1]->Date_m, ps[1]->Date_d))),
{
}

/// The WHERE condition before its last conjunct, on a row of the statement's shapes.
proof fn lemma_head_row(db: Database, x: Row, ps: Seq<Literal>, prm: Prm)
    requires
        full_shape(x),
        param_domain(ps),
        prm.name == ps[0]->Text_0,
        prm.lo == date_from_civil(ps[1]->Date_y, ps[1]->Date_m, ps[1]->Date_d),
    ensures
        eval_pred(db, x, pred_head(ps)) == Ok::<Truth, SqlError>(truth_of(
            x[0] == x[9] && x[17] == x[8] && x[19] == x[33] && x[3] == x[36] && x[36] == x[40] && x[42] == x[44]
                && x[45] == Val::Text(prm.name) && day_ge(x[12], prm.lo))),
{
    lemma_params(ps);
    lemma_eq_int(db, x, 0, 9);
    lemma_eq_int(db, x, 17, 8);
    lemma_eq_int(db, x, 19, 33);
    lemma_eq_int(db, x, 3, 36);
    lemma_eq_int(db, x, 36, 40);
    lemma_eq_int(db, x, 42, 44);
    let b1 = x[0] == x[9];
    let b2 = x[17] == x[8];
    let b3 = x[19] == x[33];
    let b4 = x[3] == x[36];
    let b5 = x[36] == x[40];
    let b6 = x[42] == x[44];
    lemma_pred_and(db, x, eq_cols(0, 9), eq_cols(17, 8), b1, b2);
    let p2 = and_p(eq_cols(0, 9), eq_cols(17, 8));
    lemma_pred_and(db, x, p2, eq_cols(19, 33), b1 && b2, b3);
    let p3 = and_p(p2, eq_cols(19, 33));
    lemma_pred_and(db, x, p3, eq_cols(3, 36), b1 && b2 && b3, b4);
    let p4 = and_p(p3, eq_cols(3, 36));
    lemma_pred_and(db, x, p4, eq_cols(36, 40), b1 && b2 && b3 && b4, b5);
    let p5 = and_p(p4, eq_cols(36, 40));
    lemma_pred_and(db, x, p5, eq_cols(42, 44), b1 && b2 && b3 && b4 && b5, b6);
    let bj = b1 && b2 && b3 && b4 && b5 && b6;
    assert(eval_pred(db, x, join_pred()) == Ok::<Truth, SqlError>(truth_of(bj)));
    // r_name = $1
    lemma_expr_col(db, x, 45);
    let t45 = x[45]->Text_0;
    lemma_pred_text_cmp(db, x, CmpOp::Eq, Expr::Col(45), Expr::Lit(ps[0]), t45, prm.name);
    let b7 = x[45] == Val::Text(prm.name);
    assert(text_cmp(CmpOp::Eq, t45, prm.name) == b7);
    lemma_pred_and(db, x, join_pred(), name_pred(ps), bj, b7);
    // o_orderdate >= $2
    lemma_expr_col(db, x, 12);
    let d = x[12]->Date_0;
    lemma_compare_date(d, prm.lo);
    lemma_pred_cmp(db, x, CmpOp::Ge, Expr::Col(12), Expr::Lit(ps[1]), x[12], Val::Date(prm.lo), d, prm.lo);
    let b8 = day_ge(x[12], prm.lo);
    lemma_pred_and(db, x, and_p(join_pred(), name_pred(ps)), date_ge_pred(ps), bj && b7, b8);
}

/// `CAST($2 AS timestamp)` in every environment: one evaluation step over the date literal.
proof fn lemma_cast_eval(db: Database, env: Row, ps: Seq<Literal>)
    requires param_domain(ps),
    ensures ({
        let lo = date_from_civil(ps[1]->Date_y, ps[1]->Date_m, ps[1]->Date_d);
        eval_expr(db, env, Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(ps[1])) })
            == match date_to_ts(lo) {
                Ok(t) => Ok::<Val, SqlError>(Val::Ts(t)),
                Err(e) => Err::<Val, SqlError>(e),
            }
    }),
{
    hide(date_to_ts);
    hide(date_from_civil);
    lemma_params(ps);
    let lo = date_from_civil(ps[1]->Date_y, ps[1]->Date_m, ps[1]->Date_d);
    assert(eval_expr(db, env, Expr::Lit(ps[1])) == Ok::<Val, SqlError>(Val::Date(lo)));
}

/// `$2 + INTERVAL '1' YEAR` in every environment: the interval step over the cast.
proof fn lemma_hi_step(db: Database, env: Row, ps: Seq<Literal>)
    requires param_domain(ps),
    ensures ({
        let lo = date_from_civil(ps[1]->Date_y, ps[1]->Date_m, ps[1]->Date_d);
        eval_expr(db, env, hi_expr(ps)) == match date_to_ts(lo) {
            Err(e) => Err::<Val, SqlError>(e),
            Ok(t0) => match ts_add_interval(t0, 12, 0, 0) {
                Ok(r) => Ok::<Val, SqlError>(Val::Ts(r)),
                Err(e) => Err::<Val, SqlError>(e),
            },
        }
    }),
{
    hide(date_to_ts);
    hide(ts_add_interval);
    hide(date_from_civil);
    hide(lit_val);
    lemma_cast_eval(db, env, ps);
}

/// The timestamp `$2 + INTERVAL '1' YEAR`, in every environment, when both steps succeed.
pub proof fn lemma_hi_eval(db: Database, env: Row, ps: Seq<Literal>, t0: int, hi: int)
    requires
        param_domain(ps),
        date_to_ts(date_from_civil(ps[1]->Date_y, ps[1]->Date_m, ps[1]->Date_d)) == Ok::<int, SqlError>(t0),
        ts_add_interval(t0, 12, 0, 0) == Ok::<int, SqlError>(hi),
    ensures eval_expr(db, env, hi_expr(ps)) == Ok::<Val, SqlError>(Val::Ts(hi)),
{
    lemma_hi_step(db, env, ps);
}

/// The timestamp step's first error, in every environment.
pub proof fn lemma_hi_err(db: Database, env: Row, ps: Seq<Literal>, e: SqlError)
    requires
        param_domain(ps),
        match date_to_ts(date_from_civil(ps[1]->Date_y, ps[1]->Date_m, ps[1]->Date_d)) {
            Err(e1) => e1 == e,
            Ok(t0) => ts_add_interval(t0, 12, 0, 0) == Err::<int, SqlError>(e),
        },
    ensures eval_expr(db, env, hi_expr(ps)) == Err::<Val, SqlError>(e),
{
    lemma_hi_step(db, env, ps);
}

/// The WHERE condition on a joined full row of the statement's shapes is two-valued: `q5_qual` of the row's
/// stored projection.
pub proof fn lemma_pred_row(db: Database, x: Row, ps: Seq<Literal>, prm: Prm, t0: int)
    requires
        full_shape(x),
        param_domain(ps),
        prm == prm_of(ps, prm.hi),
        date_to_ts(prm.lo) == Ok::<int, SqlError>(t0),
        ts_add_interval(t0, 12, 0, 0) == Ok::<int, SqlError>(prm.hi),
    ensures eval_pred(db, x, q5_pred(ps)) == Ok::<Truth, SqlError>(truth_of(q5_qual(prm, proj(x, q5_cols())))),
{
    lemma_head_row(db, x, ps, prm);
    lemma_hi_eval(db, x, ps, t0, prm.hi);
    lemma_expr_col(db, x, 12);
    let d = x[12]->Date_0;
    let u = usecs_per_day();
    assert(compare(Val::Date(d), Val::Ts(prm.hi)) == Some(sign(d * u - prm.hi)));
    lemma_pred_cmp(db, x, CmpOp::Lt, Expr::Col(12), hi_expr(ps), x[12], Val::Ts(prm.hi), d * u, prm.hi);
    let bh = x[0] == x[9] && x[17] == x[8] && x[19] == x[33] && x[3] == x[36] && x[36] == x[40] && x[42] == x[44]
        && x[45] == Val::Text(prm.name) && day_ge(x[12], prm.lo);
    lemma_pred_and(db, x, pred_head(ps), date_lt_pred(ps), bh, day_lt_ts(x[12], prm.hi));
    lemma_proj_positions(x);
}

/// On a row of the statement's shapes the WHERE condition fails with the timestamp step's error.
pub proof fn lemma_pred_row_err(db: Database, x: Row, ps: Seq<Literal>, e: SqlError)
    requires
        full_shape(x),
        param_domain(ps),
        eval_expr(db, x, hi_expr(ps)) == Err::<Val, SqlError>(e),
    ensures eval_pred(db, x, q5_pred(ps)) == Err::<Truth, SqlError>(e),
{
    hide(lit_val);
    hide(date_to_ts);
    hide(ts_add_interval);
    hide(cast);
    hide(add_interval);
    let prm = prm_of(ps, 0);
    lemma_head_row(db, x, ps, prm);
    lemma_expr_col(db, x, 12);
    assert(eval_pred(db, x, date_lt_pred(ps)) == Err::<Truth, SqlError>(e));
}

// ------------------------------------------------------------------------------------------- key and argument

/// The group key of a joined full row: `(n_name)`.
pub proof fn lemma_key_row(db: Database, x: Row)
    requires full_shape(x),
    ensures eval_exprs(db, x, q5_key_exprs()) == Ok::<Row, SqlError>(q5_key(proj(x, q5_cols()))),
{
    assert(q5_key_exprs() =~= col_exprs(seq![41nat]));
    lemma_eval_cols(db, x, seq![41nat]);
    lemma_proj_positions(x);
    assert(select(x, seq![41nat]) =~= q5_key(proj(x, q5_cols())));
}

/// `CAST(1 AS numeric)` is 1 at scale 0 (evaluated step by step: literal, then cast).
proof fn lemma_one_num(db: Database, x: Row)
    ensures eval_expr(db, x, one_num()) == Ok::<Val, SqlError>(Val::Num { coeff: 1, scale: 0 }),
{
    let l = Literal::Int { v: 1, kind: IntKind::Int4 };
    assert(int_in_range(IntKind::Int4, 1));
    assert(lit_val(l) == Ok::<Val, SqlError>(Val::Int(1)));
    assert(eval_expr(db, x, Expr::Lit(l)) == Ok::<Val, SqlError>(Val::Int(1)));
    assert(cast(CastOp::IntToNumeric, Val::Int(1)) == Ok::<Val, SqlError>(Val::Num { coeff: 1, scale: 0 }));
}

/// `CAST(1 AS numeric) - v` for a scale-2 value `v` below `10^15`: `100 - dc` at scale 2, below `10^16`.
proof fn lemma_omd_step(db: Database, x: Row, dc: int)
    requires
        23 < x.len(),
        x[23] == (Val::Num { coeff: dc, scale: 2 }),
        abs(dc) < pow10(15),
    ensures
        eval_expr(db, x, one_minus_disc()) == Ok::<Val, SqlError>(Val::Num { coeff: 100 - dc, scale: 2 }),
        abs(100 - dc) < pow10(16),
{
    lemma_expr_col(db, x, 23);
    lemma_one_num(db, x);
    assert(pow10(0) == 1);
    assert(pow10(1) == 10) by (compute);
    assert(pow10(2) == 100) by (compute);
    lemma_omd_node(db, x, dc);
}

/// The numeric subtraction node over the evaluated operands.
proof fn lemma_omd_node(db: Database, x: Row, dc: int)
    requires
        abs(dc) < pow10(15),
        eval_expr(db, x, one_num()) == Ok::<Val, SqlError>(Val::Num { coeff: 1, scale: 0 }),
        eval_expr(db, x, Expr::Col(23)) == Ok::<Val, SqlError>(Val::Num { coeff: dc, scale: 2 }),
        pow10(0) == 1, pow10(1) == 10, pow10(2) == 100,
    ensures
        eval_expr(db, x, one_minus_disc()) == Ok::<Val, SqlError>(Val::Num { coeff: 100 - dc, scale: 2 }),
        abs(100 - dc) < pow10(16),
{
    hide(pow10);
    hide(eval_expr);
    lemma_node_add(db, x, ArithOp::Sub, one_num(), Expr::Col(23), 1, 0, 1, dc, 2, 15, 2, 100, 1, 16);
}

/// `1 - l_discount` on a joined full row: `100 - dc` at scale 2, below `10^16` in absolute value.
proof fn lemma_omd_row(db: Database, x: Row)
    requires full_shape(x),
    ensures
        eval_expr(db, x, one_minus_disc()) == Ok::<Val, SqlError>(Val::Num { coeff: 100 - x[23]->Num_coeff, scale: 2 }),
        abs(100 - x[23]->Num_coeff) < pow10(16),
{
    lemma_omd_step(db, x, x[23]->Num_coeff);
}

/// `l_extendedprice * (1 - l_discount)` on a joined full row: `ep * (100 - dc)` at scale 4.
proof fn lemma_rev_row(db: Database, x: Row)
    requires full_shape(x),
    ensures
        eval_expr(db, x, rev_expr()) == Ok::<Val, SqlError>(Val::Num { coeff: x[22]->Num_coeff * (100 - x[23]->Num_coeff), scale: 4 }),
{
    let ep = x[22]->Num_coeff;
    let omd = 100 - x[23]->Num_coeff;
    lemma_expr_col(db, x, 22);
    lemma_omd_row(db, x);
    lemma_node_mul(db, x, Expr::Col(22), one_minus_disc(), ep, 2, 15, omd, 2, 16);
}

/// The aggregate arguments of a row whose SUM argument evaluates to `v`.
proof fn lemma_agg_args_one(db: Database, x: Row, v: Val)
    requires eval_expr(db, x, rev_expr()) == Ok::<Val, SqlError>(v),
    ensures agg_args(db, x, q5_aggs()) == Ok::<Row, SqlError>(seq![v]),
{
    let rs = agg_arg_results(db, x, q5_aggs());
    lemma_agg_arg_results_index(db, x, q5_aggs());
    lemma_agg_arg_sum(db, x, NumKind::Numeric, rev_expr());
    assert(rs.len() == 1);
    assert(rs[0] == Ok::<Val, SqlError>(v));
    assert(rs.drop_last() =~= Seq::<Result<Val, SqlError>>::empty());
    assert(collect(rs.drop_last()) == Ok::<Seq<Val>, SqlError>(Seq::<Val>::empty()));
    assert(rs.last() == Ok::<Val, SqlError>(v));
    assert(Seq::<Val>::empty().push(v) =~= seq![v]);
}

/// The SUM argument of a joined full row: the scale-4 numeric `q5_arg` of its stored projection.
pub proof fn lemma_arg_row(db: Database, x: Row)
    requires full_shape(x),
    ensures
        agg_args(db, x, q5_aggs()) == Ok::<Row, SqlError>(seq![Val::Num { coeff: q5_arg(proj(x, q5_cols())), scale: 4 }]),
{
    lemma_proj_positions(x);
    lemma_rev_row(db, x);
    let v = Val::Num { coeff: x[22]->Num_coeff * (100 - x[23]->Num_coeff), scale: 4 };
    lemma_agg_args_one(db, x, v);
    assert(coeff_of(proj(x, q5_cols())[20]) == x[22]->Num_coeff);
    assert(coeff_of(proj(x, q5_cols())[21]) == x[23]->Num_coeff);
}

} // verus!
