//! TPC-H Q1 as an accumulator normal form (`link::query::QuerySpec`) over the stored lineitem relation, and the
//! proof that the statement's SQL body denotes the normal form's rows.
//!
//! The relation is `lineitem_rel(db)`: the 15 stored lineitem columns of every row in canonical order (storage
//! `facts`, `stored_relations(db)[0]`). Column positions: 4 l_quantity, 5 l_extendedprice, 6 l_discount, 7 l_tax
//! (numeric(15,2) coefficients at scale 2), 8 l_returnflag, 9 l_linestatus (text), 10 l_shipdate (date, days since
//! 2000-01-01). Aggregate `j` of the statement: 0 SUM(qty), 1 SUM(price), 2 SUM(price*(1-disc)) (scale 4),
//! 3 SUM(price*(1-disc)*(1+tax)) (scale 6), 4 AVG(qty), 5 AVG(price), 6 AVG(disc), 7 COUNT(*).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::int::*;
use crate::spec::eval::*;
use crate::spec::order::*;
use crate::spec::relation::*;
use crate::spec::equality::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::types::*;
use crate::spec::typing::*;
use crate::spec::datetime::*;
use crate::spec::limits::*;
use crate::link::query::*;
use crate::link::expr::*;
use crate::link::source::*;
use crate::bridge::collect::lemma_collect_all;
use crate::bridge::equality::same_exact_type;
use crate::query::*;
use crate::schema::schema_spec;
use crate::stores::facts::declaration::*;
use crate::exec::relational::domain::fits_query;
use crate::gendb_entry::capacity_domain;
use super::common::group_outcomes::*;

verus! {

// ------------------------------------------------------------------------------------------- the normal form

/// The aggregate kinds of the statement, in SELECT order (after the two key columns).
pub open spec fn q1_aggs() -> Seq<AggKind> {
    seq![AggKind::Sum { scale: 2 }, AggKind::Sum { scale: 2 }, AggKind::Sum { scale: 4 }, AggKind::Sum { scale: 6 },
        AggKind::Avg { scale: 2 }, AggKind::Avg { scale: 2 }, AggKind::Avg { scale: 2 }, AggKind::Count]
}

/// Output columns: the whole `key ++ aggregates` row.
pub open spec fn q1_outs() -> Seq<nat> {
    seq![0nat, 1, 2, 3, 4, 5, 6, 7, 8, 9]
}

/// WHERE l_shipdate <= p (p in days since 2000-01-01).
pub open spec fn q1_qual(p: int, r: Row) -> bool {
    r[10] is Date && ival(r[10]) <= p
}

/// GROUP BY l_returnflag, l_linestatus.
pub open spec fn q1_key(r: Row) -> Row {
    seq![r[8], r[9]]
}

/// The exact argument coefficient of aggregate `j` on row `r` (COUNT has none: 0).
pub open spec fn q1_arg(j: int, r: Row) -> int {
    let q = ival(r[4]);
    let pr = ival(r[5]);
    let d = ival(r[6]);
    let t = ival(r[7]);
    if j == 0 || j == 4 {
        q
    } else if j == 1 || j == 5 {
        pr
    } else if j == 2 {
        pr * (100 - d)
    } else if j == 3 {
        pr * (100 - d) * (100 + t)
    } else if j == 6 {
        d
    } else {
        0
    }
}

pub open spec fn q1_spec(p: int) -> QuerySpec {
    QuerySpec {
        qual: |r: Row| q1_qual(p, r),
        key: |r: Row| q1_key(r),
        arg: |j: int, r: Row| q1_arg(j, r),
        aggs: q1_aggs(),
        outs: q1_outs(),
        grouped: true,
    }
}

/// The day number of the bound parameter `$1`.
pub open spec fn param_day(ps: Seq<Literal>) -> int {
    match ps[0] {
        Literal::Date { y, m, d } => date_from_civil(y, m, d),
        _ => 0,
    }
}

/// The stored lineitem relation of `db`.
pub open spec fn lineitem_rel(db: Database) -> Seq<Row> {
    stored_relations(db)[0]
}

// ------------------------------------------------------------------------------------------- the statement's AST

pub open spec fn q1_pred(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Le, a: Expr::Col(10), b: Expr::Lit(ps[0]) }
}

pub open spec fn q1_input(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: q1_pred(ps), input: Box::new(Query::Table(0)) }
}

pub open spec fn q1_key_exprs() -> Seq<Expr> {
    seq![Expr::Col(8), Expr::Col(9)]
}

/// `1 - l_discount`.
pub open spec fn one_minus_disc() -> Expr {
    Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric,
        a: Box::new(Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) }),
        b: Box::new(Expr::Col(6)) }
}

/// `1 + l_tax`.
pub open spec fn one_plus_tax() -> Expr {
    Expr::Arith { op: ArithOp::Add, kind: NumKind::Numeric,
        a: Box::new(Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) }),
        b: Box::new(Expr::Col(7)) }
}

/// `l_extendedprice * (1 - l_discount)`.
pub open spec fn disc_price() -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Col(5)), b: Box::new(one_minus_disc()) }
}

/// `l_extendedprice * (1 - l_discount) * (1 + l_tax)`.
pub open spec fn charge() -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(disc_price()), b: Box::new(one_plus_tax()) }
}

pub open spec fn q1_agg_asts() -> Seq<Agg> {
    seq![
        Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(4) },
        Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(5) },
        Agg::Sum { kind: NumKind::Numeric, arg: disc_price() },
        Agg::Sum { kind: NumKind::Numeric, arg: charge() },
        Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(4) },
        Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(5) },
        Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(6) },
        Agg::CountStar
    ]
}

pub open spec fn q1_body(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: q1_key_exprs(), aggs: q1_agg_asts(), input: Box::new(q1_input(ps)) }
}

pub open spec fn q1_order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 0, desc: false, nulls_first: false }, OrderKey { col: 1, desc: false, nulls_first: false }]
}

/// The statement's AST is the one spelled out above.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == q1_body(ps),
        query_spec_at(ps).keys == q1_order_keys(),
        query_spec_at(ps).limit is None,
        query_spec_at(ps).offset == 0,
{
    assert(query_spec_at(ps).body == q1_body(ps));
    assert(query_spec_at(ps).keys =~= q1_order_keys());
}

// ------------------------------------------------------------------------------------------- per-row facts

/// The 15 stored columns are the table columns 0..14, so a projected row agrees with its table row there.
pub proof fn lemma_cols_identity()
    ensures
        stored_cols_t0().len() == 15,
        forall|k: int| 0 <= k < 15 ==> #[trigger] stored_cols_t0()[k] == k,
{
    assert forall|k: int| 0 <= k < 15 implies #[trigger] stored_cols_t0()[k] == k by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else if k == 5 {}
        else if k == 6 {} else if k == 7 {} else if k == 8 {} else if k == 9 {} else if k == 10 {} else if k == 11 {}
        else if k == 12 {} else if k == 13 {} else if k == 14 {}
    }
}

/// The value shapes of one stored lineitem row (from the declared column domains).
pub open spec fn row_shape(x: Row) -> bool {
    &&& x.len() == 15
    &&& x[4] is Num && x[4]->Num_scale == 2 && abs(x[4]->Num_coeff) < pow10(15)
    &&& x[5] is Num && x[5]->Num_scale == 2 && abs(x[5]->Num_coeff) < pow10(15)
    &&& x[6] is Num && x[6]->Num_scale == 2 && abs(x[6]->Num_coeff) < pow10(15)
    &&& x[7] is Num && x[7]->Num_scale == 2 && abs(x[7]->Num_coeff) < pow10(15)
    &&& x[8] is Text
    &&& x[9] is Text
    &&& x[10] is Date
}

/// Every row of the stored relation of a well-formed database has the row shape.
pub proof fn lemma_rel_shape(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures
        lineitem_rel(db).len() == db.tables[0].len(),
        forall|i: int| 0 <= i < lineitem_rel(db).len() ==> row_shape(#[trigger] lineitem_rel(db)[i]),
{
    lemma_stored_relations(db);
    let rel = lineitem_rel(db);
    let cs = stored_columns_t0();
    assert forall|i: int| 0 <= i < rel.len() implies row_shape(#[trigger] rel[i]) by {
        assert(rel[i].len() == cs.len());
        assert(value_in_column(rel[i][4], cs[4]));
        assert(value_in_column(rel[i][5], cs[5]));
        assert(value_in_column(rel[i][6], cs[6]));
        assert(value_in_column(rel[i][7], cs[7]));
        assert(value_in_column(rel[i][8], cs[8]));
        assert(value_in_column(rel[i][9], cs[9]));
        assert(value_in_column(rel[i][10], cs[10]));
    }
}

/// The table rows project onto the stored relation, and each table row has 16 columns.
pub proof fn lemma_table_rows(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures
        lineitem_rel(db) == proj_all(db.tables[0], stored_cols_t0()),
        forall|i: int| 0 <= i < db.tables[0].len() ==> (#[trigger] db.tables[0][i]).len() == 16,
        forall|i: int, k: int| 0 <= i < db.tables[0].len() && 0 <= k < 15 ==> #[trigger] lineitem_rel(db)[i][k] == db.tables[0][i][k],
{
    lemma_declared_schema();
    lemma_cols_identity();
    lemma_proj_all_index(db.tables[0], stored_cols_t0());
    assert forall|i: int| 0 <= i < db.tables[0].len() implies (#[trigger] db.tables[0][i]).len() == 16 by {
        assert(row_in_table(db.tables[0][i], db.schema[0]));
    }
    assert forall|i: int, k: int| 0 <= i < db.tables[0].len() && 0 <= k < 15 implies #[trigger] lineitem_rel(db)[i][k] == db.tables[0][i][k] by {
        assert(stored_cols_t0()[k] == k);
    }
}

/// The parameter literal evaluates to its day.
pub proof fn lemma_param_lit(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(param_day(ps))),
{
}

/// WHERE: the condition evaluates, on every table row, to the normal form's truth value.
pub proof fn lemma_pred_agrees(db: Database, ps: Seq<Literal>)
    requires db.schema == schema_spec(), db_wf(db), param_domain(ps),
    ensures pred_agrees(db, db.tables[0], stored_cols_t0(), q1_pred(ps), q1_spec(param_day(ps))),
{
    let rows = db.tables[0];
    let cols = stored_cols_t0();
    let g = q1_spec(param_day(ps));
    lemma_rel_shape(db);
    lemma_table_rows(db);
    lemma_param_lit(ps);
    lemma_proj_all_index(rows, cols);
    assert forall|i: int| 0 <= i < rows.len() implies
        eval_pred(db, #[trigger] rows[i], q1_pred(ps)) == Ok::<Truth, SqlError>(truth_of((g.qual)(proj(rows[i], cols)))) by {
        let x = lineitem_rel(db)[i];
        assert(row_shape(x));
        assert(x == proj(rows[i], cols));
        assert(x[10] == rows[i][10]);
        let d = ival(x[10]);
        lemma_expr_col(db, rows[i], 10);
        lemma_compare_date(d, param_day(ps));
        lemma_pred_cmp(db, rows[i], CmpOp::Le, Expr::Col(10), Expr::Lit(ps[0]), x[10], Val::Date(param_day(ps)), d, param_day(ps));
    }
}

/// The key expressions on one table row `env` whose projection is `x`.
pub proof fn lemma_row_keys(db: Database, env: Row, x: Row)
    requires env.len() == 16, x.len() == 15, x[8] == env[8], x[9] == env[9],
    ensures eval_exprs(db, env, q1_key_exprs()) == Ok::<Row, SqlError>(q1_key(x)),
{
    let idxs = seq![8nat, 9nat];
    assert(col_exprs(idxs) =~= q1_key_exprs());
    lemma_eval_cols(db, env, idxs);
    assert(select(env, idxs) =~= q1_key(x));
}

/// GROUP BY keys: the key expressions evaluate to the normal form's key on every table row.
pub proof fn lemma_keys_agree(db: Database, p: int)
    requires db.schema == schema_spec(), db_wf(db),
    ensures keys_agree(db, db.tables[0], stored_cols_t0(), q1_key_exprs(), q1_spec(p)),
{
    let rows = db.tables[0];
    let cols = stored_cols_t0();
    let g = q1_spec(p);
    lemma_table_rows(db);
    lemma_proj_all_index(rows, cols);
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], cols)) implies
        eval_exprs(db, rows[i], q1_key_exprs()) == Ok::<Row, SqlError>((g.key)(proj(rows[i], cols))) by {
        let x = lineitem_rel(db)[i];
        assert(x == proj(rows[i], cols));
        lemma_row_keys(db, rows[i], x);
    }
}

/// `1 :: numeric` is the numeric 1 at scale 0.
pub open spec fn one_numeric() -> Expr {
    Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) }
}

/// `1 :: numeric` evaluates to 1 at scale 0 (two unfolding steps: the literal, then the cast).
pub proof fn lemma_eval_one_numeric(db: Database, env: Row)
    ensures eval_expr(db, env, one_numeric()) == Ok::<Val, SqlError>(Val::Num { coeff: 1, scale: 0 }),
{
    let l = Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 });
    assert(int_in_range(IntKind::Int4, 1));
    assert(eval_expr(db, env, l) == Ok::<Val, SqlError>(Val::Int(1)));
}

pub proof fn lemma_pow10_small()
    ensures pow10(0) == 1, pow10(1) == 10, pow10(2) == 100, pow10(15) == 1_000_000_000_000_000,
{
    assert(pow10(0) == 1 && pow10(1) == 10 && pow10(2) == 100) by (compute);
    assert(pow10(15) == 1_000_000_000_000_000) by (compute);
}

/// `1 - l_discount` on a row with discount coefficient `c6`.
pub proof fn lemma_eval_one_minus_disc(db: Database, env: Row, c6: int)
    requires env.len() > 6, env[6] == (Val::Num { coeff: c6, scale: 2 }), abs(c6) < pow10(15),
    ensures
        eval_expr(db, env, one_minus_disc()) == Ok::<Val, SqlError>(Val::Num { coeff: 100 - c6, scale: 2 }),
        abs(100 - c6) < pow10(16),
{
    lemma_pow10_small();
    assert(one_minus_disc() == Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(one_numeric()), b: Box::new(Expr::Col(6)) });
    lemma_eval_one_numeric(db, env);
    lemma_expr_col(db, env, 6);
    lemma_node_add(db, env, ArithOp::Sub, one_numeric(), Expr::Col(6), 1, 0, 1, c6, 2, 15, 2, 100, 1, 16);
}

/// `1 + l_tax` on a row with tax coefficient `c7`.
pub proof fn lemma_eval_one_plus_tax(db: Database, env: Row, c7: int)
    requires env.len() > 7, env[7] == (Val::Num { coeff: c7, scale: 2 }), abs(c7) < pow10(15),
    ensures
        eval_expr(db, env, one_plus_tax()) == Ok::<Val, SqlError>(Val::Num { coeff: 100 + c7, scale: 2 }),
        abs(100 + c7) < pow10(16),
{
    lemma_pow10_small();
    assert(one_plus_tax() == Expr::Arith { op: ArithOp::Add, kind: NumKind::Numeric, a: Box::new(one_numeric()), b: Box::new(Expr::Col(7)) });
    lemma_eval_one_numeric(db, env);
    lemma_expr_col(db, env, 7);
    lemma_node_add(db, env, ArithOp::Add, one_numeric(), Expr::Col(7), 1, 0, 1, c7, 2, 15, 2, 100, 1, 16);
}

/// `l_extendedprice * (1 - l_discount)`.
pub proof fn lemma_eval_disc_price(db: Database, env: Row, c5: int, c6: int)
    requires
        env.len() > 6,
        env[5] == (Val::Num { coeff: c5, scale: 2 }), abs(c5) < pow10(15),
        env[6] == (Val::Num { coeff: c6, scale: 2 }), abs(c6) < pow10(15),
    ensures
        eval_expr(db, env, disc_price()) == Ok::<Val, SqlError>(Val::Num { coeff: c5 * (100 - c6), scale: 4 }),
        abs(c5 * (100 - c6)) < pow10(31),
{
    lemma_eval_one_minus_disc(db, env, c6);
    lemma_expr_col(db, env, 5);
    lemma_node_mul(db, env, Expr::Col(5), one_minus_disc(), c5, 2, 15, 100 - c6, 2, 16);
}

/// `l_extendedprice * (1 - l_discount) * (1 + l_tax)`.
pub proof fn lemma_eval_charge(db: Database, env: Row, c5: int, c6: int, c7: int)
    requires
        env.len() > 7,
        env[5] == (Val::Num { coeff: c5, scale: 2 }), abs(c5) < pow10(15),
        env[6] == (Val::Num { coeff: c6, scale: 2 }), abs(c6) < pow10(15),
        env[7] == (Val::Num { coeff: c7, scale: 2 }), abs(c7) < pow10(15),
    ensures
        eval_expr(db, env, charge()) == Ok::<Val, SqlError>(Val::Num { coeff: c5 * (100 - c6) * (100 + c7), scale: 6 }),
{
    lemma_eval_disc_price(db, env, c5, c6);
    lemma_eval_one_plus_tax(db, env, c7);
    lemma_node_mul(db, env, disc_price(), one_plus_tax(), c5 * (100 - c6), 4, 31, 100 + c7, 2, 16);
}

/// The aggregate arguments of a row with coefficients `c4 .. c7`, in aggregate order.
pub open spec fn expected_args(c4: int, c5: int, c6: int, c7: int) -> Row {
    seq![Val::Num { coeff: c4, scale: 2 }, Val::Num { coeff: c5, scale: 2 }, Val::Num { coeff: c5 * (100 - c6), scale: 4 },
        Val::Num { coeff: c5 * (100 - c6) * (100 + c7), scale: 6 }, Val::Num { coeff: c4, scale: 2 },
        Val::Num { coeff: c5, scale: 2 }, Val::Num { coeff: c6, scale: 2 }, Val::Null]
}

/// The normal form's argument values of a row of the row shape are `expected_args`.
pub proof fn lemma_arg_vals(x: Row, p: int)
    requires row_shape(x),
    ensures arg_vals(q1_spec(p), x) == expected_args(ival(x[4]), ival(x[5]), ival(x[6]), ival(x[7])),
{
    let vs = arg_vals(q1_spec(p), x);
    let ev = expected_args(ival(x[4]), ival(x[5]), ival(x[6]), ival(x[7]));
    assert(vs.len() == 8 && ev.len() == 8);
    assert(vs[0] == ev[0]);
    assert(vs[1] == ev[1]);
    assert(vs[2] == ev[2]);
    assert(vs[3] == ev[3]);
    assert(vs[4] == ev[4]);
    assert(vs[5] == ev[5]);
    assert(vs[6] == ev[6]);
    assert(vs[7] == ev[7]);
    assert(vs =~= ev);
}

/// The precondition of the per-row argument lemmas: row `env` with coefficients `c4 .. c7`.
pub open spec fn coeff_row(env: Row, c4: int, c5: int, c6: int, c7: int) -> bool {
    &&& env.len() == 16
    &&& env[4] == (Val::Num { coeff: c4, scale: 2 })
    &&& env[5] == (Val::Num { coeff: c5, scale: 2 }) && abs(c5) < pow10(15)
    &&& env[6] == (Val::Num { coeff: c6, scale: 2 }) && abs(c6) < pow10(15)
    &&& env[7] == (Val::Num { coeff: c7, scale: 2 }) && abs(c7) < pow10(15)
}

/// The SQL argument of aggregate `j` of row `env` is `expected_args(..)[j]`.
pub proof fn lemma_arg_result_at(db: Database, env: Row, c4: int, c5: int, c6: int, c7: int, j: int)
    requires coeff_row(env, c4, c5, c6, c7), 0 <= j < 8,
    ensures agg_arg_results(db, env, q1_agg_asts())[j] == Ok::<Val, SqlError>(expected_args(c4, c5, c6, c7)[j]),
{
    hide(eval_expr);
    let aggs = q1_agg_asts();
    let rs = agg_arg_results(db, env, aggs);
    let ev = expected_args(c4, c5, c6, c7);
    assert(rs[j] == agg_arg(db, env, aggs[j]));
    let n = NumKind::Numeric;
    if j == 0 {
        lemma_expr_col(db, env, 4);
        assert(aggs[0] == Agg::Sum { kind: n, arg: Expr::Col(4) });
        lemma_agg_arg_sum(db, env, n, Expr::Col(4));
    } else if j == 1 {
        lemma_expr_col(db, env, 5);
        assert(aggs[1] == Agg::Sum { kind: n, arg: Expr::Col(5) });
        lemma_agg_arg_sum(db, env, n, Expr::Col(5));
    } else if j == 2 {
        lemma_eval_disc_price(db, env, c5, c6);
        assert(aggs[2] == Agg::Sum { kind: n, arg: disc_price() });
        lemma_agg_arg_sum(db, env, n, disc_price());
    } else if j == 3 {
        lemma_eval_charge(db, env, c5, c6, c7);
        assert(aggs[3] == Agg::Sum { kind: n, arg: charge() });
        lemma_agg_arg_sum(db, env, n, charge());
    } else if j == 4 {
        lemma_expr_col(db, env, 4);
        assert(aggs[4] == Agg::Avg { kind: n, arg: Expr::Col(4) });
        lemma_agg_arg_avg(db, env, n, Expr::Col(4));
    } else if j == 5 {
        lemma_expr_col(db, env, 5);
        assert(aggs[5] == Agg::Avg { kind: n, arg: Expr::Col(5) });
        lemma_agg_arg_avg(db, env, n, Expr::Col(5));
    } else if j == 6 {
        lemma_expr_col(db, env, 6);
        assert(aggs[6] == Agg::Avg { kind: n, arg: Expr::Col(6) });
        lemma_agg_arg_avg(db, env, n, Expr::Col(6));
    } else {
        assert(aggs[7] == Agg::CountStar);
        lemma_agg_arg_count(db, env);
    }
}

/// The SQL arguments of the aggregates of row `env` are `expected_args` of its coefficients.
pub proof fn lemma_arg_results(db: Database, env: Row, c4: int, c5: int, c6: int, c7: int)
    requires coeff_row(env, c4, c5, c6, c7),
    ensures
        forall|j: int| 0 <= j < 8 ==> #[trigger] agg_arg_results(db, env, q1_agg_asts())[j]
            == Ok::<Val, SqlError>(expected_args(c4, c5, c6, c7)[j]),
{
    assert forall|j: int| 0 <= j < 8 implies #[trigger] agg_arg_results(db, env, q1_agg_asts())[j]
        == Ok::<Val, SqlError>(expected_args(c4, c5, c6, c7)[j]) by {
        lemma_arg_result_at(db, env, c4, c5, c6, c7, j);
    }
}

/// The argument of every aggregate on one table row `env` whose projection is `x`.
pub proof fn lemma_row_args(db: Database, env: Row, x: Row, p: int)
    requires
        env.len() == 16,
        row_shape(x),
        forall|k: int| 0 <= k < 15 ==> #[trigger] x[k] == env[k],
    ensures
        agg_args(db, env, q1_agg_asts()) == Ok::<Row, SqlError>(arg_vals(q1_spec(p), x)),
{
    let (c4, c5, c6, c7) = (ival(x[4]), ival(x[5]), ival(x[6]), ival(x[7]));
    assert(x[4] == env[4] && x[5] == env[5] && x[6] == env[6] && x[7] == env[7]);
    assert(coeff_row(env, c4, c5, c6, c7));
    lemma_arg_results(db, env, c4, c5, c6, c7);
    lemma_arg_vals(x, p);
    let rs = agg_arg_results(db, env, q1_agg_asts());
    let vs = arg_vals(q1_spec(p), x);
    assert(rs.len() == 8);
    assert forall|j: int| 0 <= j < rs.len() implies #[trigger] rs[j] == Ok::<Val, SqlError>(vs[j]) by {}
    lemma_collect_all(rs, vs);
}

/// Aggregate arguments: on every table row the arguments are the normal form's.
pub proof fn lemma_args_agree(db: Database, p: int)
    requires db.schema == schema_spec(), db_wf(db),
    ensures args_agree(db, db.tables[0], stored_cols_t0(), q1_agg_asts(), q1_spec(p)),
{
    let rows = db.tables[0];
    let cols = stored_cols_t0();
    let g = q1_spec(p);
    lemma_rel_shape(db);
    lemma_table_rows(db);
    lemma_proj_all_index(rows, cols);
    assert forall|i: int| 0 <= i < rows.len() && (g.qual)(proj(#[trigger] rows[i], cols)) implies
        agg_args(db, rows[i], q1_agg_asts()) == Ok::<Row, SqlError>(arg_vals(g, proj(rows[i], cols))) by {
        let x = lineitem_rel(db)[i];
        assert(x == proj(rows[i], cols));
        assert(row_shape(x));
        lemma_row_args(db, rows[i], x, p);
    }
}

pub proof fn lemma_aggs_match(p: int)
    ensures aggs_match(q1_agg_asts(), q1_spec(p)),
{
    let aggs = q1_agg_asts();
    let g = q1_spec(p);
    assert forall|j: int| 0 <= j < aggs.len() implies agg_matches(#[trigger] aggs[j], g.aggs[j]) by {
        if j == 0 {} else if j == 1 {} else if j == 2 {} else if j == 3 {} else if j == 4 {} else if j == 5 {} else if j == 6 {} else {}
    }
}

/// The keys of the stored rows are two texts, so SQL "not distinct" is equality.
pub proof fn lemma_keys_exact(db: Database, p: int)
    requires db.schema == schema_spec(), db_wf(db),
    ensures keys_exact(q1_spec(p), lineitem_rel(db)),
{
    let xs = lineitem_rel(db);
    let g = q1_spec(p);
    lemma_rel_shape(db);
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        let (ka, kb) = ((g.key)(xs[a]), (g.key)(xs[b]));
        assert(row_shape(xs[a]) && row_shape(xs[b]));
        assert forall|i: int| 0 <= i < ka.len() implies same_exact_type(#[trigger] ka[i], kb[i]) by {}
        lemma_row_exact(ka, kb);
    }
}

// ------------------------------------------------------------------------------------------- the link

/// Every group key of the qualifying rows has two columns.
pub proof fn lemma_gkeys_len(p: int, xs: Seq<Row>, k: Row)
    requires gkeys(q1_spec(p), xs).contains(k),
    ensures k.len() == 2,
{
    lemma_gkeys_witness(q1_spec(p), xs, k);
}

/// The full rows of the groups are the normal form's result rows (every output column is selected).
pub proof fn lemma_result_rows_full(p: int, xs: Seq<Row>)
    ensures result_rows(q1_spec(p), xs) == gkeys(q1_spec(p), xs).map_values(|k: Row| full_row(q1_spec(p), xs, k)),
{
    let g = q1_spec(p);
    let ks = gkeys(g, xs);
    assert forall|i: int| 0 <= i < ks.len() implies
        #[trigger] out_row(g, xs, ks[i]) == full_row(g, xs, ks[i]) by {
        assert(ks.contains(ks[i]));
        lemma_gkeys_len(p, xs, ks[i]);
        let f = full_row(g, xs, ks[i]);
        assert(f.len() == 10);
        assert forall|m: int| 0 <= m < g.outs.len() implies #[trigger] g.outs[m] == m by {}
        lemma_select_identity(f, g.outs);
    }
    assert(result_rows(g, xs) =~= ks.map_values(|k: Row| full_row(g, xs, k)));
}

/// The WHERE clause over the table keeps the rows whose projection qualifies.
pub proof fn lemma_input_rows(db: Database, ps: Seq<Literal>)
    requires db.schema == schema_spec(), db_wf(db), param_domain(ps),
    ensures
        eval_query(db, Seq::empty(), q1_input(ps)) == Ok::<Relation, SqlError>(keep_true(db.tables[0],
            qual_truths(q1_spec(param_day(ps)), proj_all(db.tables[0], stored_cols_t0())))),
{
    lemma_declared_schema();
    assert(eval_query(db, Seq::empty(), Query::Table(0)) == Ok::<Relation, SqlError>(db.tables[0]));
    lemma_pred_agrees(db, ps);
    lemma_filter_rows(db, Query::Table(0), db.tables[0], stored_cols_t0(), q1_pred(ps), q1_spec(param_day(ps)));
}

/// Inside `group_caps`, the GROUP BY denotes the full row of every group key.
pub proof fn lemma_group_eval(db: Database, ps: Seq<Literal>)
    requires
        db.schema == schema_spec(),
        db_wf(db),
        param_domain(ps),
        group_caps(q1_spec(param_day(ps)), lineitem_rel(db)),
    ensures ({
        let g = q1_spec(param_day(ps));
        let xs = lineitem_rel(db);
        eval_query(db, Seq::empty(), q1_body(ps)) == Ok::<Relation, SqlError>(gkeys(g, xs).map_values(|k: Row| full_row(g, xs, k)))
    }),
{
    hide(eval_query);
    let p = param_day(ps);
    let g = q1_spec(p);
    lemma_table_rows(db);
    lemma_input_rows(db, ps);
    lemma_keys_agree(db, p);
    lemma_args_agree(db, p);
    lemma_aggs_match(p);
    lemma_keys_exact(db, p);
    lemma_group_query(db, db.tables[0], stored_cols_t0(), q1_input(ps), q1_key_exprs(), q1_agg_asts(), g);
}

/// Inside `group_caps`, the statement's body denotes the normal form's rows over the stored relation.
pub proof fn lemma_body_rows(db: Database, ps: Seq<Literal>)
    requires
        db.schema == schema_spec(),
        db_wf(db),
        param_domain(ps),
        group_caps(q1_spec(param_day(ps)), lineitem_rel(db)),
    ensures
        denote_body(db, query_spec_at(ps)) == Ok::<Relation, SqlError>(result_rows(q1_spec(param_day(ps)), lineitem_rel(db))),
{
    hide(eval_query);
    lemma_query_shape(ps);
    lemma_group_eval(db, ps);
    lemma_result_rows_full(param_day(ps), lineitem_rel(db));
}

// ------------------------------------------------------------------------------------------- non-row outcomes

/// The SQL premises of the GROUP BY (per-row agreement, exact keys) for every database of the schema.
pub proof fn lemma_q1_premises(db: Database, ps: Seq<Literal>)
    requires db.schema == schema_spec(), db_wf(db), param_domain(ps),
    ensures
        group_premises(db, db.tables[0], stored_cols_t0(), q1_input(ps), q1_key_exprs(), q1_agg_asts(), q1_spec(param_day(ps))),
        proj_all(db.tables[0], stored_cols_t0()) == lineitem_rel(db),
{
    let p = param_day(ps);
    lemma_table_rows(db);
    lemma_input_rows(db, ps);
    lemma_keys_agree(db, p);
    lemma_args_agree(db, p);
    lemma_aggs_match(p);
    lemma_keys_exact(db, p);
}

/// A group whose COUNT exceeds int8: the GROUP BY is the SQL error 22003.
proof fn lemma_group_count_err_q1(db: Database, ps: Seq<Literal>, k: Row)
    requires
        db.schema == schema_spec(), db_wf(db), param_domain(ps),
        gcount(q1_spec(param_day(ps)), lineitem_rel(db), k) > int8_max(),
    ensures eval_query(db, Seq::empty(), q1_body(ps)) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    hide(eval_query);
    hide(group_premises);
    lemma_q1_premises(db, ps);
    assert(q1_spec(param_day(ps)).aggs[7] is Count);
    lemma_group_count_err(db, db.tables[0], stored_cols_t0(), q1_input(ps), q1_key_exprs(), q1_agg_asts(),
        q1_spec(param_day(ps)), k, 7);
}

/// A group whose COUNT exceeds int8: the statement is the SQL error 22003.
pub proof fn lemma_body_count_err(db: Database, ps: Seq<Literal>, k: Row)
    requires
        db.schema == schema_spec(), db_wf(db), param_domain(ps),
        gcount(q1_spec(param_day(ps)), lineitem_rel(db), k) > int8_max(),
    ensures denote_body(db, query_spec_at(ps)) == Err::<Relation, SqlError>(SqlError::NumericValueOutOfRange),
{
    hide(eval_query);
    lemma_query_shape(ps);
    lemma_group_count_err_q1(db, ps, k);
}

/// The capacity violation at the GROUP BY node.
proof fn lemma_group_capacity_q1(db: Database, ps: Seq<Literal>, k: Row, j: int)
    requires
        db.schema == schema_spec(), db_wf(db), param_domain(ps),
        forall|k2: Row| #[trigger] gcount(q1_spec(param_day(ps)), lineitem_rel(db), k2) <= int8_max(),
        gcount(q1_spec(param_day(ps)), lineitem_rel(db), k) > 0,
        0 <= j < 7,
        agg_over(q1_spec(param_day(ps)), lineitem_rel(db), k, j),
    ensures !fits_query(db, Seq::empty(), q1_body(ps)),
{
    hide(eval_query);
    hide(fits_query);
    hide(group_premises);
    lemma_q1_premises(db, ps);
    let g = q1_spec(param_day(ps));
    assert(!(g.aggs[j] is Count));
    lemma_group_capacity(db, db.tables[0], stored_cols_t0(), q1_input(ps), q1_key_exprs(), q1_agg_asts(), g, k, j);
}

/// Every COUNT in int8 and a non-empty group's SUM/AVG aggregate `j < 7` outside its capacity condition: the
/// database is outside the statement's capacity domain.
pub proof fn lemma_body_capacity(db: Database, ps: Seq<Literal>, k: Row, j: int)
    requires
        db.schema == schema_spec(), db_wf(db), param_domain(ps),
        forall|k2: Row| #[trigger] gcount(q1_spec(param_day(ps)), lineitem_rel(db), k2) <= int8_max(),
        gcount(q1_spec(param_day(ps)), lineitem_rel(db), k) > 0,
        0 <= j < 7,
        agg_over(q1_spec(param_day(ps)), lineitem_rel(db), k, j),
    ensures !capacity_domain(db, query_spec_at(ps)),
{
    hide(eval_query);
    hide(fits_query);
    lemma_query_shape(ps);
    lemma_group_capacity_q1(db, ps, k, j);
}

} // verus!
