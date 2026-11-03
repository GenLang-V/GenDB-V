//! The statement's meaning, part 1: its AST in named pieces (`body_q`, `lemma_statement`), the database facts
//! the proof reads (`db_ok`, from `db_wf` and the schema), and the value of every per-row condition:
//! - `SUBSTRING(c, 1, 2)` is `sub2` of the text (`lemma_eval_sub2`); the IN list is "the code has a group"
//!   (`lemma_eval_in_list`);
//! - the AVG subquery, under any outer row, is one row holding `avg_val(db, ps)`: AVG over the rows of `g2`
//!   (positive balance, listed code), in the accumulator normal form of `link::query` (`lemma_eval_sub_q`; inside
//!   the division domain `group_caps(g2(ps), ctab(db))`);
//! - NOT EXISTS is "no orders row has the key" (`lemma_eval_not_exists`);
//! - the WHERE condition is `True` exactly when `mq` holds (`lemma_eval_where`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::types::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::typing::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::chars::*;
use crate::spec::fns::*;
use crate::spec::fns::substring::*;
use crate::spec::limits::*;
use crate::schema::schema_spec;
use crate::query::{param_domain, query_spec_at};
use crate::link::expr::{ival, tval};
use crate::link::query::*;
use crate::link::exists::lemma_exists_filter_table;
use crate::bridge::collect::lemma_collect_all;
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::exec::relational::domain::lemma_collect_pointwise;
use super::common::sub2::*;
use super::model::*;
use super::scan::lemma_gid_range;

verus! {

// ------------------------------------------------------------------------------------------------ the AST

/// An int4 literal.
pub open spec fn lit_int(v: int) -> Expr {
    Expr::Lit(Literal::Int { v, kind: IntKind::Int4 })
}

/// `SUBSTRING(Col(c), 1, 2)`.
pub open spec fn sub2_expr(c: nat) -> Expr {
    Expr::Call { f: ScalarFn::Substring3, args: seq![Expr::Col(c), lit_int(1), lit_int(2)] }
}

/// `SUBSTRING(Col(c), 1, 2) = l`.
pub open spec fn eq_pred(c: nat, l: Literal) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: sub2_expr(c), b: Expr::Lit(l) }
}

/// The IN list over column `c`: an OR chain of the seven equalities, left-deep.
pub open spec fn in_list(c: nat, ps: Seq<Literal>) -> Pred {
    let o1 = Pred::Or(Box::new(eq_pred(c, ps[0])), Box::new(eq_pred(c, ps[1])));
    let o2 = Pred::Or(Box::new(o1), Box::new(eq_pred(c, ps[2])));
    let o3 = Pred::Or(Box::new(o2), Box::new(eq_pred(c, ps[3])));
    let o4 = Pred::Or(Box::new(o3), Box::new(eq_pred(c, ps[4])));
    let o5 = Pred::Or(Box::new(o4), Box::new(eq_pred(c, ps[5])));
    Pred::Or(Box::new(o5), Box::new(eq_pred(c, ps[6])))
}

/// The subquery's condition (outer row first, so the inner c_phone is column 12 and c_acctbal column 13).
pub open spec fn sub_pred(ps: Seq<Literal>) -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(13), b: Expr::Lit(Literal::Num { coeff: 0, scale: 2 }) }),
        Box::new(in_list(12, ps)),
    )
}

/// `SELECT AVG(c_acctbal) FROM customer WHERE ...`.
pub open spec fn sub_q(ps: Seq<Literal>) -> Query {
    Query::Aggregate {
        aggs: seq![Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(13) }],
        input: Box::new(Query::Filter { pred: sub_pred(ps), input: Box::new(Query::Table(2)) }),
    }
}

/// `c_acctbal > (subquery)`.
pub open spec fn gt_sub(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(5), b: Expr::Subquery(Box::new(sub_q(ps))) }
}

/// The condition of the EXISTS subquery: `o_custkey = c_custkey`.
pub open spec fn ex_pred() -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(9), b: Expr::Col(0) }
}

/// `SELECT * FROM orders WHERE o_custkey = c_custkey`.
pub open spec fn ex_q() -> Query {
    Query::Filter { pred: ex_pred(), input: Box::new(Query::Table(1)) }
}

/// The outer WHERE condition.
pub open spec fn where_pred(ps: Seq<Literal>) -> Pred {
    Pred::And(
        Box::new(Pred::And(Box::new(in_list(4, ps)), Box::new(gt_sub(ps)))),
        Box::new(Pred::Not(Box::new(Pred::Exists(Box::new(ex_q()))))),
    )
}

pub open spec fn filter_q(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: where_pred(ps), input: Box::new(Query::Table(2)) }
}

/// The derived table's columns: `SUBSTRING(c_phone, 1, 2)`, `c_acctbal`.
pub open spec fn proj_exprs() -> Seq<Expr> {
    seq![sub2_expr(4), Expr::Col(5)]
}

pub open spec fn project_q(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: proj_exprs(), input: Box::new(filter_q(ps)) }
}

pub open spec fn group_keys() -> Seq<Expr> {
    seq![Expr::Col(0)]
}

pub open spec fn group_aggs() -> Seq<Agg> {
    seq![Agg::CountStar, Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(1) }]
}

/// The statement's body.
pub open spec fn body_q(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: group_keys(), aggs: group_aggs(), input: Box::new(project_q(ps)) }
}

/// `ORDER BY cntrycode`.
pub open spec fn order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 0, desc: false, nulls_first: false }]
}

/// The generated AST is the named one.
pub proof fn lemma_statement(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == body_q(ps),
        query_spec_at(ps).keys == order_keys(),
        query_spec_at(ps).offset == 0,
        query_spec_at(ps).limit == None::<nat>,
{
}

// ------------------------------------------------------------------------------------------------ database facts

pub open spec fn ctab(db: Database) -> Seq<Row> {
    db.tables[2]
}

pub open spec fn otab(db: Database) -> Seq<Row> {
    db.tables[1]
}

/// A customer row as the proof reads it: 8 columns, an int8 key, a text phone, a numeric(15, 2) balance.
pub open spec fn crow_ok(r: Row) -> bool {
    &&& r.len() == 8
    &&& r[0] is Int
    &&& i64::MIN <= ival(r[0]) <= i64::MAX
    &&& r[4] is Text
    &&& r[5] is Num
    &&& r[5]->Num_scale == 2
    &&& -acct_bound() < ival(r[5]) < acct_bound()
}

/// An orders row: 9 columns, an int8 o_custkey.
pub open spec fn orow_ok(r: Row) -> bool {
    &&& r.len() == 9
    &&& r[1] is Int
}

pub open spec fn db_ok(db: Database) -> bool {
    &&& db.tables.len() == 8
    &&& forall|i: int| 0 <= i < ctab(db).len() ==> #[trigger] crow_ok(ctab(db)[i])
    &&& forall|j: int| 0 <= j < otab(db).len() ==> #[trigger] orow_ok(otab(db)[j])
}

/// The declared column types give `db_ok`.
pub proof fn lemma_db_ok(db: Database)
    requires db.schema == schema_spec(), db_wf(db),
    ensures db_ok(db),
{
    crate::stores::custpart::declaration::lemma_declared_schema();
    crate::stores::orders_custidx::declaration::lemma_declared_schema();
    let cs = schema_spec()[2];
    let os = schema_spec()[1];
    let ccols = crate::stores::custpart::declaration::stored_cols_t0();
    assert(proj_columns_at(cs, ccols, 0) == cs.columns[0]);
    assert(cs.columns[0] == Column { ty: SqlType::Int8, nullable: false }) by {
        assert(crate::link::source::proj_columns(cs, ccols)[0] == cs.columns[0]);
    }
    assert(cs.columns[4] == Column { ty: SqlType::Text, nullable: false }) by {
        assert(crate::link::source::proj_columns(cs, ccols)[4] == cs.columns[4]);
    }
    assert(cs.columns[5] == Column { ty: SqlType::Numeric { precision: 15, scale: 2 }, nullable: false }) by {
        assert(crate::link::source::proj_columns(cs, ccols)[5] == cs.columns[5]);
    }
    assert(os.columns[1] == Column { ty: SqlType::Int8, nullable: false }) by {
        let ocols = crate::stores::orders_custidx::declaration::stored_cols_t0();
        assert(crate::link::source::proj_columns(os, ocols)[0] == os.columns[1]);
    }
    assert(pow10(15) == 1_000_000_000_000_000) by (compute);
    assert forall|i: int| 0 <= i < ctab(db).len() implies #[trigger] crow_ok(ctab(db)[i]) by {
        let r = ctab(db)[i];
        assert(row_in_table(db.tables[2][i], db.schema[2]));
        assert(value_in_column(r[0], cs.columns[0]));
        assert(value_in_column(r[4], cs.columns[4]));
        assert(value_in_column(r[5], cs.columns[5]));
    }
    assert forall|j: int| 0 <= j < otab(db).len() implies #[trigger] orow_ok(otab(db)[j]) by {
        let r = otab(db)[j];
        assert(row_in_table(db.tables[1][j], db.schema[1]));
        assert(value_in_column(r[1], os.columns[1]));
    }
}

/// Column `k` of `cols` projected from `t` (a name for one step of `proj_columns`).
pub open spec fn proj_columns_at(t: TableSchema, cols: Seq<nat>, k: int) -> Column {
    t.columns[cols[k] as int]
}

// ------------------------------------------------------------------------------------------------ row helpers

/// c_phone, c_acctbal coefficient, c_custkey of a customer row; its country code.
pub open spec fn cphone(r: Row) -> Seq<u8> {
    tval(r[4])
}

pub open spec fn cacct(r: Row) -> int {
    ival(r[5])
}

pub open spec fn ckey(r: Row) -> int {
    ival(r[0])
}

pub open spec fn code(r: Row) -> Seq<u8> {
    sub2(cphone(r))
}

/// The code is listed (some parameter slot holds it).
pub open spec fn listed(ps: Seq<Literal>, t: Seq<u8>) -> bool {
    gid(ps, t) < 7
}

/// Every slot holds a text literal.
pub open spec fn ps_ok(ps: Seq<Literal>) -> bool {
    &&& ps.len() == 7
    &&& forall|k: int| 0 <= k < 7 ==> #[trigger] ps[k] == Literal::Text(ptext(ps, k))
}

pub proof fn lemma_ps_ok(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures ps_ok(ps),
{
    assert forall|k: int| 0 <= k < 7 implies #[trigger] ps[k] == Literal::Text(ptext(ps, k)) by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else if k == 5 {} else {}
    }
}

/// Some slot holds `t` exactly when it has a group.
pub proof fn lemma_listed(ps: Seq<Literal>, t: Seq<u8>)
    ensures listed(ps, t) == (exists|k: int| 0 <= k < 7 && #[trigger] ptext(ps, k) == t),
{
    lemma_gid_range(ps, 0, t);
    if exists|k: int| 0 <= k < 7 && #[trigger] ptext(ps, k) == t {
        let k = choose|k: int| 0 <= k < 7 && #[trigger] ptext(ps, k) == t;
        assert(gid(ps, t) <= k);
    }
}

// ------------------------------------------------------------------------------------------------ expressions

/// `SUBSTRING(Col(c), 1, 2)` of a text value is `sub2` of it.
pub proof fn lemma_eval_sub2(db: Database, env: Row, c: nat, b: Seq<u8>)
    requires c < env.len(), env[c as int] == Val::Text(b),
    ensures eval_expr(db, env, sub2_expr(c)) == Ok::<Val, SqlError>(Val::Text(sub2(b))),
{
    let args = seq![Expr::Col(c), lit_int(1), lit_int(2)];
    let vs = seq![Val::Text(b), Val::Int(1), Val::Int(2)];
    lemma_expr_results_index(db, env, args);
    assert(int_in_range(IntKind::Int4, 1)) by (compute);
    assert(int_in_range(IntKind::Int4, 2)) by (compute);
    let rs = expr_results(db, env, args);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        assert(rs[i] == eval_expr(db, env, args[i]));
    }
    lemma_collect_all(rs, vs);
    assert(eval_exprs(db, env, args) == Ok::<Row, SqlError>(vs));
    lemma_sub2(b);
    assert(!(exists|k: int| 0 <= k < vs.len() && #[trigger] vs[k] is Null));
    assert(substring_end(1, 2) == Some(3int));
    assert(apply_fn(ScalarFn::Substring3, vs) == Ok::<Val, SqlError>(Val::Text(sub2(b))));
}

/// `SUBSTRING(Col(c), 1, 2) = p` on a text value.
pub proof fn lemma_eval_eq(db: Database, env: Row, c: nat, b: Seq<u8>, p: Seq<u8>)
    requires c < env.len(), env[c as int] == Val::Text(b),
    ensures eval_pred(db, env, eq_pred(c, Literal::Text(p))) == Ok::<Truth, SqlError>(truth_of(sub2(b) == p)),
{
    lemma_eval_sub2(db, env, c, b);
    lemma_lex_cmp_zero(sub2(b), p);
    assert(eval_expr(db, env, Expr::Lit(Literal::Text(p))) == Ok::<Val, SqlError>(Val::Text(p)));
}

/// `truth_or` of two-valued truths.
proof fn lemma_or2(x: bool, y: bool)
    ensures truth_or(truth_of(x), truth_of(y)) == truth_of(x || y),
{
}

/// The IN list over a text column is "the code is listed".
pub proof fn lemma_eval_in_list(db: Database, env: Row, c: nat, b: Seq<u8>, ps: Seq<Literal>)
    requires c < env.len(), env[c as int] == Val::Text(b), ps_ok(ps),
    ensures eval_pred(db, env, in_list(c, ps)) == Ok::<Truth, SqlError>(truth_of(listed(ps, sub2(b)))),
{
    let t = sub2(b);
    let e = |k: int| eq_pred(c, ps[k]);
    assert forall|k: int| 0 <= k < 7 implies eval_pred(db, env, #[trigger] eq_pred(c, ps[k])) == Ok::<Truth, SqlError>(truth_of(ptext(ps, k) == t)) by {
        assert(ps[k] == Literal::Text(ptext(ps, k)));
        lemma_eval_eq(db, env, c, b, ptext(ps, k));
    }
    let o1 = Pred::Or(Box::new(eq_pred(c, ps[0])), Box::new(eq_pred(c, ps[1])));
    let o2 = Pred::Or(Box::new(o1), Box::new(eq_pred(c, ps[2])));
    let o3 = Pred::Or(Box::new(o2), Box::new(eq_pred(c, ps[3])));
    let o4 = Pred::Or(Box::new(o3), Box::new(eq_pred(c, ps[4])));
    let o5 = Pred::Or(Box::new(o4), Box::new(eq_pred(c, ps[5])));
    let o6 = Pred::Or(Box::new(o5), Box::new(eq_pred(c, ps[6])));
    assert(in_list(c, ps) == o6);
    let h = |k: int| ptext(ps, k) == t;
    let x1 = h(0) || h(1);
    let x2 = x1 || h(2);
    let x3 = x2 || h(3);
    let x4 = x3 || h(4);
    let x5 = x4 || h(5);
    let x6 = x5 || h(6);
    lemma_or2(h(0), h(1));
    assert(eval_pred(db, env, o1) == Ok::<Truth, SqlError>(truth_of(x1)));
    lemma_or2(x1, h(2));
    assert(eval_pred(db, env, o2) == Ok::<Truth, SqlError>(truth_of(x2)));
    lemma_or2(x2, h(3));
    assert(eval_pred(db, env, o3) == Ok::<Truth, SqlError>(truth_of(x3)));
    lemma_or2(x3, h(4));
    assert(eval_pred(db, env, o4) == Ok::<Truth, SqlError>(truth_of(x4)));
    lemma_or2(x4, h(5));
    assert(eval_pred(db, env, o5) == Ok::<Truth, SqlError>(truth_of(x5)));
    lemma_or2(x5, h(6));
    assert(eval_pred(db, env, o6) == Ok::<Truth, SqlError>(truth_of(x6)));
    lemma_listed(ps, t);
    if x6 {
        assert(exists|k: int| 0 <= k < 7 && #[trigger] ptext(ps, k) == t) by {
            if h(0) { assert(ptext(ps, 0) == t); }
            else if h(1) { assert(ptext(ps, 1) == t); }
            else if h(2) { assert(ptext(ps, 2) == t); }
            else if h(3) { assert(ptext(ps, 3) == t); }
            else if h(4) { assert(ptext(ps, 4) == t); }
            else if h(5) { assert(ptext(ps, 5) == t); }
            else { assert(ptext(ps, 6) == t); }
        }
    }
    if listed(ps, t) {
        let k = choose|k: int| 0 <= k < 7 && #[trigger] ptext(ps, k) == t;
        assert(h(k));
        assert(x6) by {
            if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else if k == 5 {} else {}
        }
    }
}

// ------------------------------------------------------------------------------------------------ the AVG subquery

/// The subquery's rows: a positive balance and a listed code.
pub open spec fn sq(ps: Seq<Literal>, r: Row) -> bool {
    cacct(r) > 0 && listed(ps, code(r))
}

/// The subquery in normal form over the customer rows: AVG of the balance (scale 2) of the `sq` rows.
pub open spec fn g2(ps: Seq<Literal>) -> QuerySpec {
    QuerySpec {
        qual: |r: Row| sq(ps, r),
        key: |r: Row| Seq::<Val>::empty(),
        arg: |j: int, r: Row| cacct(r),
        aggs: seq![AggKind::Avg { scale: 2 }],
        outs: seq![0nat],
        grouped: false,
    }
}

/// The subquery's value: AVG of the `sq` rows' balances (NULL without such rows).
pub open spec fn avg_val(db: Database, ps: Seq<Literal>) -> Val {
    agg_out(AggKind::Avg { scale: 2 }, gcount(g2(ps), ctab(db), Seq::empty()), gsum(g2(ps), ctab(db), Seq::empty(), 0))
}

/// The identity column list of a customer row.
pub open spec fn id8() -> Seq<nat> {
    seq![0nat, 1, 2, 3, 4, 5, 6, 7]
}

/// Projecting 8-column rows on all their columns keeps them.
pub proof fn lemma_proj_id8(rows: Seq<Row>)
    requires forall|i: int| 0 <= i < rows.len() ==> (#[trigger] rows[i]).len() == 8,
    ensures proj_all(rows, id8()) == rows,
{
    assert forall|i: int| 0 <= i < rows.len() implies #[trigger] proj_all(rows, id8())[i] == rows[i] by {
        assert(proj(rows[i], id8()) =~= rows[i]);
    }
    assert(proj_all(rows, id8()) =~= rows);
}

/// The subquery's condition on one customer row under an 8-column outer row.
pub proof fn lemma_eval_sub_pred(db: Database, ctx: Row, r: Row, ps: Seq<Literal>)
    requires ctx.len() == 8, crow_ok(r), ps_ok(ps),
    ensures eval_pred(db, ctx + r, sub_pred(ps)) == Ok::<Truth, SqlError>(truth_of(sq(ps, r))),
{
    let env = ctx + r;
    assert(env[13] == r[5]);
    assert(env[12] == r[4]);
    let a = cacct(r);
    assert(r[5] == Val::Num { coeff: a, scale: 2 });
    assert(num_in_range(0, 2)) by {
        assert(decimal_digits(0) == 0);
    }
    assert(lit_val(Literal::Num { coeff: 0, scale: 2 }) == Ok::<Val, SqlError>(Val::Num { coeff: 0, scale: 2 }));
    assert(num_cmp(a, 2, 0, 2) == sign(a)) by {
        assert(pow10(0) == 1);
        assert(align(a, 2, 2) == a);
        assert(align(0, 2, 2) == 0);
    }
    let gt = Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(13), b: Expr::Lit(Literal::Num { coeff: 0, scale: 2 }) };
    assert(env.len() == 16);
    assert(eval_expr(db, env, Expr::Col(13)) == Ok::<Val, SqlError>(Val::Num { coeff: a, scale: 2 }));
    assert(0 <= numeric_dscale_max());
    assert(eval_expr(db, env, Expr::Lit(Literal::Num { coeff: 0, scale: 2 })) == Ok::<Val, SqlError>(Val::Num { coeff: 0, scale: 2 }));
    assert(compare(Val::Num { coeff: a, scale: 2 }, Val::Num { coeff: 0, scale: 2 }) == Some(sign(a)));
    assert(cmp_truth(CmpOp::Gt, Val::Num { coeff: a, scale: 2 }, Val::Num { coeff: 0, scale: 2 }) == Ok::<Truth, SqlError>(truth_of(a > 0)));
    assert(eval_pred(db, env, gt) == Ok::<Truth, SqlError>(truth_of(a > 0)));
    lemma_eval_in_list(db, env, 12, cphone(r), ps);
}

/// One step of the Aggregate denotation under an outer context.
proof fn lemma_aggregate_unfold_ctx(db: Database, ctx: Row, input: Query, aggs: Seq<Agg>, kept: Seq<Row>, args: Seq<Row>)
    requires
        eval_query(db, ctx, input) == Ok::<Relation, SqlError>(kept),
        collect(Seq::new(kept.len(), |i: int| agg_args(db, ctx + kept[i], aggs))) == Ok::<Seq<Row>, SqlError>(args),
    ensures
        eval_query(db, ctx, Query::Aggregate { aggs, input: Box::new(input) })
            == match agg_row(aggs, args) {
                Err(err) => Err(err),
                Ok(row) => Ok::<Relation, SqlError>(seq![row]),
            },
{
    lemma_collect_pointwise::<Row>();
}

/// A WHERE over base table `t` under the context `ctx`, every row's condition succeeding with `truths[i]`.
pub proof fn lemma_filter_table(db: Database, ctx: Row, pred: Pred, t: nat, truths: Seq<Truth>)
    requires
        t < db.tables.len(),
        truths.len() == db.tables[t as int].len(),
        forall|i: int| 0 <= i < truths.len() ==> #[trigger] eval_pred(db, ctx + db.tables[t as int][i], pred)
            == Ok::<Truth, SqlError>(truths[i]),
    ensures
        eval_query(db, ctx, Query::Filter { pred, input: Box::new(Query::Table(t)) })
            == Ok::<Relation, SqlError>(keep_true(db.tables[t as int], truths)),
{
    let rows = db.tables[t as int];
    let prs = Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred));
    assert forall|i: int| 0 <= i < prs.len() implies #[trigger] prs[i] == Ok::<Truth, SqlError>(truths[i]) by {}
    lemma_collect_all(prs, truths);
    lemma_collect_pointwise::<Truth>();
    assert(eval_query(db, ctx, Query::Table(t)) == Ok::<Relation, SqlError>(rows));
}

/// The subquery's WHERE keeps the `sq` rows.
pub proof fn lemma_sub_filter(db: Database, ctx: Row, ps: Seq<Literal>)
    requires db_ok(db), ctx.len() == 8, ps_ok(ps),
    ensures
        eval_query(db, ctx, Query::Filter { pred: sub_pred(ps), input: Box::new(Query::Table(2)) })
            == Ok::<Relation, SqlError>(keep_true(ctab(db), qual_truths(g2(ps), ctab(db)))),
{
    hide(eval_pred);
    hide(eval_query);
    let rows = ctab(db);
    let truths = qual_truths(g2(ps), rows);
    assert forall|i: int| 0 <= i < truths.len() implies #[trigger] eval_pred(db, ctx + rows[i], sub_pred(ps))
        == Ok::<Truth, SqlError>(truths[i]) by {
        assert(crow_ok(rows[i]));
        reveal(eval_pred);
        lemma_eval_sub_pred(db, ctx, rows[i], ps);
    }
    reveal(eval_query);
    lemma_filter_table(db, ctx, sub_pred(ps), 2, truths);
}

/// The AVG argument of a customer row under an 8-column outer row.
pub proof fn lemma_sub_arg(db: Database, ctx: Row, r: Row, ps: Seq<Literal>)
    requires ctx.len() == 8, crow_ok(r),
    ensures
        agg_args(db, ctx + r, seq![Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(13) }])
            == Ok::<Row, SqlError>(arg_vals(g2(ps), r)),
{
    let aggs = seq![Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(13) }];
    let env = ctx + r;
    assert(env[13] == r[5]);
    lemma_agg_arg_results_index(db, env, aggs);
    let ar = agg_arg_results(db, env, aggs);
    assert(ar[0] == agg_arg(db, env, aggs[0]));
    assert(agg_arg(db, env, aggs[0]) == eval_expr(db, env, Expr::Col(13)));
    assert(r[5] == Val::Num { coeff: cacct(r), scale: 2 });
    assert(arg_vals(g2(ps), r) =~= seq![Val::Num { coeff: cacct(r), scale: 2 }]);
    lemma_collect_all(ar, seq![Val::Num { coeff: cacct(r), scale: 2 }]);
}

/// The AVG subquery under an 8-column outer row: one row holding `avg_val`.
pub proof fn lemma_eval_sub_q(db: Database, ctx: Row, ps: Seq<Literal>)
    requires
        db_ok(db),
        ctx.len() == 8,
        ps_ok(ps),
        group_caps(g2(ps), ctab(db)),
    ensures
        eval_query(db, ctx, sub_q(ps)) == Ok::<Relation, SqlError>(seq![seq![avg_val(db, ps)]]),
{
    hide(eval_pred);
    hide(agg_args);
    hide(agg_row);
    hide(eval_query);
    let g = g2(ps);
    let rows = ctab(db);
    let cols = id8();
    assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] rows[i]).len() == 8 by {
        assert(crow_ok(rows[i]));
    }
    lemma_proj_id8(rows);
    let xs = proj_all(rows, cols);
    let filt = Query::Filter { pred: sub_pred(ps), input: Box::new(Query::Table(2)) };
    lemma_sub_filter(db, ctx, ps);
    let kept = keep_true(rows, qual_truths(g, xs));
    // Aggregate arguments of the kept rows.
    lemma_kept_rows(g, rows, cols);
    let aggs = seq![Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(13) }];
    let args = Seq::new(kept.len(), |i: int| arg_vals(g, proj(kept[i], cols)));
    let pre = Seq::new(kept.len(), |i: int| agg_args(db, ctx + kept[i], aggs));
    assert forall|i: int| 0 <= i < pre.len() implies #[trigger] pre[i] == Ok::<Row, SqlError>(args[i]) by {
        assert(rows.contains(kept[i]));
        let m = choose|m: int| 0 <= m < rows.len() && rows[m] == kept[i];
        assert(crow_ok(rows[m]));
        assert(proj(kept[i], cols) =~= kept[i]);
        lemma_sub_arg(db, ctx, kept[i], ps);
    }
    lemma_collect_all(pre, args);
    let q = qrows(g, xs);
    assert(args =~= q.map_values(|x: Row| arg_vals(g, x)));
    lemma_scalar_members(g, xs);
    assert(aggs_match(aggs, g)) by {
        assert(agg_matches(aggs[0], g.aggs[0]));
    }
    lemma_agg_row(g, aggs, xs, Seq::empty());
    reveal(eval_query);
    lemma_aggregate_unfold_ctx(db, ctx, filt, aggs, kept, args);
    let outs = agg_outs(g, xs, Seq::empty());
    assert(outs =~= seq![avg_val(db, ps)]);
}

// ------------------------------------------------------------------------------------------------ NOT EXISTS

/// Some orders row has o_custkey `k`.
pub open spec fn has_ord(db: Database, k: int) -> bool {
    exists|j: int| 0 <= j < otab(db).len() && #[trigger] otab(db)[j][1] == Val::Int(k)
}

/// `NOT EXISTS (SELECT * FROM orders WHERE o_custkey = c_custkey)` on a customer row.
pub proof fn lemma_eval_not_exists(db: Database, r: Row)
    requires db_ok(db), crow_ok(r),
    ensures
        eval_pred(db, r, Pred::Not(Box::new(Pred::Exists(Box::new(ex_q())))))
            == Ok::<Truth, SqlError>(truth_of(!has_ord(db, ckey(r)))),
{
    let o = otab(db);
    assert forall|j: int| 0 <= j < o.len() implies #[trigger] eval_pred(db, r + o[j], ex_pred())
        == Ok::<Truth, SqlError>(truth_of(o[j][1] == Val::Int(ckey(r)))) by {
        assert(orow_ok(o[j]));
        let env = r + o[j];
        assert(env.len() == 17);
        assert(env[9] == o[j][1]);
        assert(env[0] == r[0]);
        let x = ival(o[j][1]);
        let k = ckey(r);
        assert(o[j][1] == Val::Int(x));
        assert(r[0] == Val::Int(k));
        assert(eval_expr(db, env, Expr::Col(9)) == Ok::<Val, SqlError>(Val::Int(x)));
        assert(eval_expr(db, env, Expr::Col(0)) == Ok::<Val, SqlError>(Val::Int(k)));
        assert(compare(Val::Int(x), Val::Int(k)) == Some(sign(x - k)));
        assert(cmp_truth(CmpOp::Eq, Val::Int(x), Val::Int(k)) == Ok::<Truth, SqlError>(truth_of(x == k)));
        assert((x == k) == (o[j][1] == Val::Int(k)));
    }
    lemma_exists_filter_table(db, r, ex_pred(), 1);
    let w = exists|j: int| 0 <= j < o.len() && #[trigger] eval_pred(db, r + o[j], ex_pred()) == Ok::<Truth, SqlError>(Truth::True);
    if w {
        let j = choose|j: int| 0 <= j < o.len() && #[trigger] eval_pred(db, r + o[j], ex_pred()) == Ok::<Truth, SqlError>(Truth::True);
        assert(orow_ok(o[j]));
        assert(o[j][1] == Val::Int(ckey(r)));
        assert(has_ord(db, ckey(r)));
    }
    if has_ord(db, ckey(r)) {
        let j = choose|j: int| 0 <= j < o.len() && #[trigger] o[j][1] == Val::Int(ckey(r));
        assert(eval_pred(db, r + o[j], ex_pred()) == Ok::<Truth, SqlError>(Truth::True));
    }
    assert(Query::Filter { pred: ex_pred(), input: Box::new(Query::Table(1)) } == ex_q());
}

// ------------------------------------------------------------------------------------------------ the WHERE condition

/// A customer row of the result: listed code, balance above the average, no orders.
pub open spec fn mq(db: Database, ps: Seq<Literal>, avg: Val, r: Row) -> bool {
    listed(ps, code(r)) && gt_avg(cacct(r), avg) && !has_ord(db, ckey(r))
}

/// A scalar subquery evaluating to the one value `av`.
proof fn lemma_eval_subq_expr(db: Database, env: Row, q: Query, av: Val)
    requires eval_query(db, env, q) == Ok::<Relation, SqlError>(seq![seq![av]]),
    ensures eval_expr(db, env, Expr::Subquery(Box::new(q))) == Ok::<Val, SqlError>(av),
{
    assert(seq![seq![av]].len() == 1);
    assert(first_col(seq![seq![av]][0]) == Ok::<Val, SqlError>(av));
    assert(subquery_value(seq![seq![av]]) == Ok::<Val, SqlError>(av));
}

/// One step of a comparison over evaluated operands.
proof fn lemma_eval_cmp_step(db: Database, env: Row, op: CmpOp, a: Expr, b: Expr, va: Val, vb: Val)
    requires
        eval_expr(db, env, a) == Ok::<Val, SqlError>(va),
        eval_expr(db, env, b) == Ok::<Val, SqlError>(vb),
    ensures eval_pred(db, env, Pred::Cmp { op, a, b }) == cmp_truth(op, va, vb),
{
}

/// `a > av` for a balance at scale 2 against NULL or a numeric.
proof fn lemma_cmp_avg(c: int, av: Val)
    requires av is Null || av is Num,
    ensures
        cmp_truth(CmpOp::Gt, Val::Num { coeff: c, scale: 2 }, av)
            == Ok::<Truth, SqlError>(if av is Null { Truth::Unknown } else { truth_of(gt_avg(c, av)) }),
{
}

/// `c_acctbal > (q)` for a subquery `q` evaluating to the one value `av` (NULL or numeric).
proof fn lemma_eval_gt_at(db: Database, r: Row, q: Query, av: Val)
    requires crow_ok(r), eval_query(db, r, q) == Ok::<Relation, SqlError>(seq![seq![av]]), av is Null || av is Num,
    ensures
        eval_pred(db, r, Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(5), b: Expr::Subquery(Box::new(q)) })
            == Ok::<Truth, SqlError>(if av is Null { Truth::Unknown } else { truth_of(gt_avg(cacct(r), av)) }),
{
    lemma_eval_subq_expr(db, r, q, av);
    assert(r[5] == Val::Num { coeff: cacct(r), scale: 2 });
    lemma_expr_col_val(db, r, 5);
    lemma_eval_cmp_step(db, r, CmpOp::Gt, Expr::Col(5), Expr::Subquery(Box::new(q)), r[5], av);
    lemma_cmp_avg(cacct(r), av);
}

/// A column reference inside the row.
proof fn lemma_expr_col_val(db: Database, env: Row, c: nat)
    requires c < env.len(),
    ensures eval_expr(db, env, Expr::Col(c)) == Ok::<Val, SqlError>(env[c as int]),
{
}

/// `c_acctbal > (subquery)` on a customer row: `Unknown` against NULL, otherwise `gt_avg`.
pub proof fn lemma_eval_gt_sub(db: Database, r: Row, ps: Seq<Literal>)
    requires db_ok(db), crow_ok(r), ps_ok(ps), group_caps(g2(ps), ctab(db)), avg_val(db, ps) is Null || avg_val(db, ps) is Num,
    ensures
        eval_pred(db, r, gt_sub(ps)) == Ok::<Truth, SqlError>(
            if avg_val(db, ps) is Null { Truth::Unknown } else { truth_of(gt_avg(cacct(r), avg_val(db, ps))) }),
{
    lemma_eval_sub_q(db, r, ps);
    lemma_eval_gt_at(db, r, sub_q(ps), avg_val(db, ps));
}

/// The WHERE condition on a customer row: it succeeds, and it is `True` exactly when `mq` holds.
pub proof fn lemma_eval_where(db: Database, r: Row, ps: Seq<Literal>)
    requires db_ok(db), crow_ok(r), ps_ok(ps), group_caps(g2(ps), ctab(db)), avg_val(db, ps) is Null || avg_val(db, ps) is Num,
    ensures
        eval_pred(db, r, where_pred(ps)) is Ok,
        (eval_pred(db, r, where_pred(ps))->Ok_0 is True) == mq(db, ps, avg_val(db, ps), r),
{
    lemma_eval_in_list(db, r, 4, cphone(r), ps);
    lemma_eval_gt_sub(db, r, ps);
    lemma_eval_not_exists(db, r);
    let a = Pred::And(Box::new(in_list(4, ps)), Box::new(gt_sub(ps)));
    let ne = Pred::Not(Box::new(Pred::Exists(Box::new(ex_q()))));
    assert(where_pred(ps) == Pred::And(Box::new(a), Box::new(ne)));
    assert(eval_pred(db, r, a) is Ok);
    assert(eval_pred(db, r, where_pred(ps)) == Ok::<Truth, SqlError>(truth_and(eval_pred(db, r, a)->Ok_0, eval_pred(db, r, ne)->Ok_0)));
}

} // verus!
