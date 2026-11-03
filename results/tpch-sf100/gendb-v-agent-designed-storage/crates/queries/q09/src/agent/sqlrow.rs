//! The Q9 statement's AST in named pieces (`q9_*`; `lemma_q9_shape` identifies them with `query::query_spec_at`) and
//! its per-row meaning. A FROM row is `part ++ supplier ++ lineitem ++ partsupp ++ orders ++ nation` (50 columns);
//! the statement reads 17 of them (`q9_cols`), the projected row `x`: p_partkey, p_name | s_suppkey, s_nationkey |
//! l_orderkey, l_partkey, l_suppkey, l_quantity, l_extendedprice, l_discount | ps_partkey, ps_suppkey,
//! ps_supplycost | o_orderkey, o_orderdate | n_nationkey, n_name. On such a row the WHERE condition is the join
//! equalities and `p_name LIKE $1` (`lemma_pred_eval`; LIKE's error is the condition's error), and the SELECT list
//! is `(n_name, EXTRACT(YEAR FROM o_orderdate), l_extendedprice * (1 - l_discount) - ps_supplycost * l_quantity)`
//! (`lemma_project_eval`, `sel_row`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::IntKind;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::collect;
use crate::spec::datetime::{date_valid, civil_from_date};
use crate::spec::fns::like::like_value;
use crate::spec::fns::apply_fn;
use crate::spec::fns::extract::extract_field;
use crate::query::{query_spec_at, param_domain};
use crate::link::query::{proj, col_exprs, lemma_eval_cols, select, lemma_node_mul, lemma_node_add};
use crate::link::expr::{ival, tval, int_cmp, lemma_expr_col, lemma_pred_cmp, lemma_pred_and, lemma_compare_int};
use crate::bridge::collect::lemma_collect_all;
use super::qspec::*;
use super::year::year_of;

verus! {

/// `Col(a) = Col(b)`.
pub open spec fn eqp(a: nat, b: nat) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(a), b: Expr::Col(b) }
}

/// The join equalities: s_suppkey = l_suppkey, ps_suppkey = l_suppkey, ps_partkey = l_partkey, p_partkey =
/// l_partkey, o_orderkey = l_orderkey, s_nationkey = n_nationkey.
pub open spec fn q9_joins() -> Pred {
    Pred::And(Box::new(Pred::And(Box::new(Pred::And(Box::new(Pred::And(Box::new(Pred::And(
        Box::new(eqp(9, 18)), Box::new(eqp(33, 18)))), Box::new(eqp(32, 17)))), Box::new(eqp(0, 17)))), Box::new(eqp(37, 16)))),
        Box::new(eqp(12, 46)))
}

/// `p_name LIKE $1` (escape `\`).
pub open spec fn like_expr(ps: Seq<Literal>) -> Expr {
    Expr::Call { f: ScalarFn::Like, args: seq![Expr::Col(1), Expr::Lit(ps[0]), Expr::Lit(Literal::Text(seq![92u8]))] }
}

pub open spec fn q9_pred(ps: Seq<Literal>) -> Pred {
    Pred::And(Box::new(q9_joins()), Box::new(Pred::OfBool(like_expr(ps))))
}

/// `1 - l_discount`.
pub open spec fn one_minus_disc() -> Expr {
    Expr::Arith {
        op: ArithOp::Sub,
        kind: NumKind::Numeric,
        a: Box::new(Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) }),
        b: Box::new(Expr::Col(22)),
    }
}

/// `l_extendedprice * (1 - l_discount)`.
pub open spec fn disc_price() -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Col(21)), b: Box::new(one_minus_disc()) }
}

/// `ps_supplycost * l_quantity`.
pub open spec fn cost_qty() -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Col(35)), b: Box::new(Expr::Col(20)) }
}

/// The amount.
pub open spec fn q9_amount() -> Expr {
    Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(disc_price()), b: Box::new(cost_qty()) }
}

/// `EXTRACT(YEAR FROM o_orderdate)`.
pub open spec fn year_expr() -> Expr {
    Expr::Call { f: ScalarFn::ExtractYear, args: seq![Expr::Col(41)] }
}

/// The SELECT list of the derived table.
pub open spec fn q9_exprs() -> Seq<Expr> {
    seq![Expr::Col(47), year_expr(), q9_amount()]
}

/// FROM part, supplier, lineitem, partsupp, orders, nation.
pub open spec fn q9_from() -> Query {
    Query::Product {
        left: Box::new(Query::Product {
            left: Box::new(Query::Product {
                left: Box::new(Query::Product {
                    left: Box::new(Query::Product { left: Box::new(Query::Table(3)), right: Box::new(Query::Table(5)) }),
                    right: Box::new(Query::Table(0)),
                }),
                right: Box::new(Query::Table(4)),
            }),
            right: Box::new(Query::Table(1)),
        }),
        right: Box::new(Query::Table(6)),
    }
}

pub open spec fn q9_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: q9_pred(ps), input: Box::new(q9_from()) }
}

pub open spec fn q9_project(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: q9_exprs(), input: Box::new(q9_filter(ps)) }
}

/// GROUP BY nation, o_year.
pub open spec fn q9_gkeys() -> Seq<Expr> {
    seq![Expr::Col(0), Expr::Col(1)]
}

/// SUM(amount).
pub open spec fn q9_aggs() -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(2) }]
}

pub open spec fn q9_body(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: q9_gkeys(), aggs: q9_aggs(), input: Box::new(q9_project(ps)) }
}

/// ORDER BY nation, o_year DESC.
pub open spec fn q9_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 0, desc: false, nulls_first: false }, OrderKey { col: 1, desc: true, nulls_first: true }]
}

/// The statement is these pieces, ordered by `q9_keys`, without OFFSET and LIMIT.
pub proof fn lemma_q9_shape(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == q9_body(ps),
        query_spec_at(ps).keys == q9_keys(),
        query_spec_at(ps).limit is None,
        query_spec_at(ps).offset == 0,
{
    assert(query_spec_at(ps).keys =~= q9_keys());
    assert(query_spec_at(ps).body == q9_body(ps));
}

/// The binding's literal: `$1` is its text.
pub proof fn lemma_params(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures ps[0] == Literal::Text(qp_of(ps).pat),
{
}

// ------------------------------------------------------------------------------------------------ the read columns

/// Positions read in the FROM row.
pub open spec fn q9_cols() -> Seq<nat> {
    seq![0nat, 1, 9, 12, 16, 17, 18, 20, 21, 22, 32, 33, 35, 37, 41, 46, 47]
}

/// A projected row of the declared column types (numerics of precision 15 at scale 2, valid dates).
pub open spec fn xrow_typed(x: Row) -> bool {
    &&& x.len() == 17
    &&& x[0] is Int && x[1] is Text && x[2] is Int && x[3] is Int && x[4] is Int && x[5] is Int && x[6] is Int
    &&& x[7] matches Val::Num { coeff, scale } && scale == 2 && -pow10(15) < coeff < pow10(15)
    &&& x[8] matches Val::Num { coeff, scale } && scale == 2 && -pow10(15) < coeff < pow10(15)
    &&& x[9] matches Val::Num { coeff, scale } && scale == 2 && -pow10(15) < coeff < pow10(15)
    &&& x[10] is Int && x[11] is Int
    &&& x[12] matches Val::Num { coeff, scale } && scale == 2 && -pow10(15) < coeff < pow10(15)
    &&& x[13] is Int
    &&& x[14] matches Val::Date(d) && date_valid(d)
    &&& x[15] is Int && x[16] is Text
}

/// The join equalities on a projected row.
pub open spec fn joins_x(x: Row) -> bool {
    &&& ival(x[2]) == ival(x[6])
    &&& ival(x[11]) == ival(x[6])
    &&& ival(x[10]) == ival(x[5])
    &&& ival(x[0]) == ival(x[5])
    &&& ival(x[13]) == ival(x[4])
    &&& ival(x[3]) == ival(x[15])
}

/// `p_name LIKE $1` on a projected row.
pub open spec fn like_x(p: QP, x: Row) -> Result<Val, SqlError> {
    like_value(x[1], Val::Text(p.pat), Val::Text(esc()))
}

/// The WHERE condition on a projected row (two-valued when LIKE does not raise).
pub open spec fn qual_x(p: QP, x: Row) -> bool {
    joins_x(x) && like_x(p, x) == Ok::<Val, SqlError>(Val::Bool(true))
}

/// The amount's coefficient (scale 4) on a projected row.
pub open spec fn amt_x(x: Row) -> int {
    ival(x[8]) * (100 - ival(x[9])) - ival(x[12]) * ival(x[7])
}

/// The derived table's row of a projected row: n_name, the order year, the amount.
pub open spec fn sel_row(x: Row) -> Row {
    seq![x[16], Val::Num { coeff: year_of(ival(x[14])), scale: 0 }, Val::Num { coeff: amt_x(x), scale: 4 }]
}

/// The FROM row `env` reads the projected row `x`.
pub open spec fn env_reads(env: Row, x: Row) -> bool {
    env.len() == 50 && x == proj(env, q9_cols())
}

proof fn lemma_env_vals(env: Row, x: Row)
    requires env_reads(env, x),
    ensures
        x.len() == 17,
        env[0] == x[0], env[1] == x[1], env[9] == x[2], env[12] == x[3], env[16] == x[4], env[17] == x[5],
        env[18] == x[6], env[20] == x[7], env[21] == x[8], env[22] == x[9], env[32] == x[10], env[33] == x[11],
        env[35] == x[12], env[37] == x[13], env[41] == x[14], env[46] == x[15], env[47] == x[16],
{
}

/// One join equality of two integer columns.
proof fn lemma_eqp(db: Database, env: Row, a: nat, b: nat)
    requires a < env.len(), b < env.len(), env[a as int] is Int, env[b as int] is Int,
    ensures eval_pred(db, env, eqp(a, b)) == Ok::<Truth, SqlError>(truth_of(ival(env[a as int]) == ival(env[b as int]))),
{
    lemma_expr_col(db, env, a);
    lemma_expr_col(db, env, b);
    lemma_compare_int(ival(env[a as int]), ival(env[b as int]));
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(a), Expr::Col(b), env[a as int], env[b as int], ival(env[a as int]), ival(env[b as int]));
}

/// The join equalities on a FROM row.
pub proof fn lemma_joins_eval(db: Database, env: Row, x: Row)
    requires env_reads(env, x), xrow_typed(x),
    ensures eval_pred(db, env, q9_joins()) == Ok::<Truth, SqlError>(truth_of(joins_x(x))),
{
    hide(eval_pred);
    lemma_env_vals(env, x);
    lemma_eqp(db, env, 9, 18);
    lemma_eqp(db, env, 33, 18);
    lemma_eqp(db, env, 32, 17);
    lemma_eqp(db, env, 0, 17);
    lemma_eqp(db, env, 37, 16);
    lemma_eqp(db, env, 12, 46);
    let (b1, b2, b3, b4, b5, b6) = (ival(x[2]) == ival(x[6]), ival(x[11]) == ival(x[6]), ival(x[10]) == ival(x[5]),
        ival(x[0]) == ival(x[5]), ival(x[13]) == ival(x[4]), ival(x[3]) == ival(x[15]));
    lemma_pred_and(db, env, eqp(9, 18), eqp(33, 18), b1, b2);
    let p2 = Pred::And(Box::new(eqp(9, 18)), Box::new(eqp(33, 18)));
    lemma_pred_and(db, env, p2, eqp(32, 17), b1 && b2, b3);
    let p3 = Pred::And(Box::new(p2), Box::new(eqp(32, 17)));
    lemma_pred_and(db, env, p3, eqp(0, 17), b1 && b2 && b3, b4);
    let p4 = Pred::And(Box::new(p3), Box::new(eqp(0, 17)));
    lemma_pred_and(db, env, p4, eqp(37, 16), b1 && b2 && b3 && b4, b5);
    let p5 = Pred::And(Box::new(p4), Box::new(eqp(37, 16)));
    lemma_pred_and(db, env, p5, eqp(12, 46), b1 && b2 && b3 && b4 && b5, b6);
    assert(q9_joins() == Pred::And(Box::new(p5), Box::new(eqp(12, 46))));
}

/// A list of three expressions.
proof fn lemma_eval3(db: Database, env: Row, es: Seq<Expr>, v0: Val, v1: Val, v2: Val)
    requires
        es.len() == 3,
        eval_expr(db, env, es[0]) == Ok::<Val, SqlError>(v0),
        eval_expr(db, env, es[1]) == Ok::<Val, SqlError>(v1),
        eval_expr(db, env, es[2]) == Ok::<Val, SqlError>(v2),
    ensures eval_exprs(db, env, es) == Ok::<Row, SqlError>(seq![v0, v1, v2]),
{
    let rs = expr_results(db, env, es);
    lemma_expr_results_index(db, env, es);
    lemma_collect_all(rs, seq![v0, v1, v2]);
}

/// One unfolding step of a function call.
proof fn lemma_call(db: Database, env: Row, f: ScalarFn, args: Seq<Expr>)
    ensures eval_expr(db, env, Expr::Call { f, args }) == match eval_exprs(db, env, args) {
        Err(err) => Err(err),
        Ok(vs) => apply_fn(f, vs),
    },
{
}

/// One unfolding step of a boolean condition.
proof fn lemma_ofbool(db: Database, env: Row, e: Expr)
    ensures eval_pred(db, env, Pred::OfBool(e)) == match eval_expr(db, env, e) {
        Err(err) => Err(err),
        Ok(v) => truth_of_val(v),
    },
{
}

/// A list of one expression.
proof fn lemma_eval1(db: Database, env: Row, es: Seq<Expr>, v0: Val)
    requires es.len() == 1, eval_expr(db, env, es[0]) == Ok::<Val, SqlError>(v0),
    ensures eval_exprs(db, env, es) == Ok::<Row, SqlError>(seq![v0]),
{
    let rs = expr_results(db, env, es);
    lemma_expr_results_index(db, env, es);
    lemma_collect_all(rs, seq![v0]);
}

/// `p_name LIKE $1` on a FROM row: the condition `OfBool(..)` is LIKE's value (or error).
pub proof fn lemma_like_eval(db: Database, env: Row, x: Row, ps: Seq<Literal>)
    requires env_reads(env, x), xrow_typed(x), param_domain(ps),
    ensures
        like_x(qp_of(ps), x) is Ok ==> (like_x(qp_of(ps), x) matches Ok(Val::Bool(b))
            && eval_pred(db, env, Pred::OfBool(like_expr(ps))) == Ok::<Truth, SqlError>(truth_of(b))),
        like_x(qp_of(ps), x) matches Err(e) ==> eval_pred(db, env, Pred::OfBool(like_expr(ps))) == Err::<Truth, SqlError>(e),
{
    hide(like_value);
    hide(eval_expr);
    hide(eval_exprs);
    hide(eval_pred);
    lemma_env_vals(env, x);
    lemma_params(ps);
    let p = qp_of(ps);
    let args = seq![Expr::Col(1), Expr::Lit(ps[0]), Expr::Lit(Literal::Text(seq![92u8]))];
    lemma_expr_col(db, env, 1);
    crate::link::expr::lemma_expr_text(db, env, p.pat);
    crate::link::expr::lemma_expr_text(db, env, seq![92u8]);
    lemma_eval3(db, env, args, x[1], Val::Text(p.pat), Val::Text(seq![92u8]));
    assert(esc() == seq![92u8]);
    let lv = like_value(x[1], Val::Text(p.pat), Val::Text(esc()));
    lemma_call(db, env, ScalarFn::Like, args);
    assert(apply_fn(ScalarFn::Like, seq![x[1], Val::Text(p.pat), Val::Text(seq![92u8])]) == lv);
    assert(eval_expr(db, env, like_expr(ps)) == lv);
    lemma_ofbool(db, env, like_expr(ps));
    if lv is Ok {
        lemma_like_bool(x[1], p.pat);
    }
}

/// LIKE on text arguments is a boolean or an error.
proof fn lemma_like_bool(s: Val, pat: Seq<u8>)
    requires s is Text,
    ensures like_value(s, Val::Text(pat), Val::Text(esc())) is Ok ==> like_value(s, Val::Text(pat), Val::Text(esc())) is Ok
        && like_value(s, Val::Text(pat), Val::Text(esc()))->Ok_0 is Bool,
{
}

/// The WHERE condition on a FROM row: two-valued when LIKE does not raise, LIKE's error otherwise.
pub proof fn lemma_pred_eval(db: Database, env: Row, x: Row, ps: Seq<Literal>)
    requires env_reads(env, x), xrow_typed(x), param_domain(ps),
    ensures
        like_x(qp_of(ps), x) is Ok ==> eval_pred(db, env, q9_pred(ps)) == Ok::<Truth, SqlError>(truth_of(qual_x(qp_of(ps), x))),
        like_x(qp_of(ps), x) matches Err(e) ==> eval_pred(db, env, q9_pred(ps)) == Err::<Truth, SqlError>(e),
{
    lemma_joins_eval(db, env, x);
    lemma_like_eval(db, env, x, ps);
    let p = qp_of(ps);
    if like_x(p, x) is Ok {
        let b = like_x(p, x)->Ok_0->Bool_0;
        lemma_pred_and(db, env, q9_joins(), Pred::OfBool(like_expr(ps)), joins_x(x), b);
    }
}

/// pow10 values used by the amount's digit bounds.
proof fn lemma_pow10_small()
    ensures pow10(0) == 1, pow10(1) == 10, pow10(2) == 100,
{
    assert(pow10(0) == 1) by (compute);
    assert(pow10(1) == 10) by (compute);
    assert(pow10(2) == 100) by (compute);
}

/// The amount on a FROM row: the numeric of scale 4 with coefficient `amt_x`.
pub proof fn lemma_amount_eval(db: Database, env: Row, x: Row)
    requires env_reads(env, x), xrow_typed(x),
    ensures eval_expr(db, env, q9_amount()) == Ok::<Val, SqlError>(Val::Num { coeff: amt_x(x), scale: 4 }),
{
    lemma_env_vals(env, x);
    lemma_pow10_small();
    lemma_pow10_monotone(15, 16);
    lemma_pow10_monotone(16, 31);
    lemma_pow10_monotone(30, 31);
    lemma_pow10_monotone(31, 32);
    let (q, pr, ds, c) = (ival(x[7]), ival(x[8]), ival(x[9]), ival(x[12]));
    let one = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) };
    assert(eval_expr(db, env, Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) == Ok::<Val, SqlError>(Val::Int(1)));
    assert(eval_expr(db, env, one) == Ok::<Val, SqlError>(Val::Num { coeff: 1, scale: 0 }));
    lemma_expr_col(db, env, 20);
    lemma_expr_col(db, env, 21);
    lemma_expr_col(db, env, 22);
    lemma_expr_col(db, env, 35);
    assert(abs(1) < pow10(1));
    assert(abs(ds) < pow10(15));
    assert(max_nat(0, 2) == 2);
    lemma_node_add(db, env, ArithOp::Sub, one, Expr::Col(22), 1, 0, 1, ds, 2, 15, 2, 100, 1, 16);
    assert(eval_expr(db, env, one_minus_disc()) == Ok::<Val, SqlError>(Val::Num { coeff: 100 - ds, scale: 2 }));
    assert(abs(pr) < pow10(15));
    lemma_node_mul(db, env, Expr::Col(21), one_minus_disc(), pr, 2, 15, 100 - ds, 2, 16);
    assert(abs(c) < pow10(15) && abs(q) < pow10(15));
    lemma_node_mul(db, env, Expr::Col(35), Expr::Col(20), c, 2, 15, q, 2, 15);
    assert(max_nat(4, 4) == 4);
    lemma_pow10_monotone(30, 31);
    lemma_node_add(db, env, ArithOp::Sub, disc_price(), cost_qty(), pr * (100 - ds), 4, 31, c * q, 4, 30, 4, 1, 1, 32);
}

/// `EXTRACT(YEAR FROM o_orderdate)` on a FROM row.
pub proof fn lemma_year_eval(db: Database, env: Row, x: Row)
    requires env_reads(env, x), xrow_typed(x),
    ensures eval_expr(db, env, year_expr()) == Ok::<Val, SqlError>(Val::Num { coeff: year_of(ival(x[14])), scale: 0 }),
{
    hide(civil_from_date);
    hide(eval_expr);
    hide(eval_exprs);
    lemma_env_vals(env, x);
    lemma_expr_col(db, env, 41);
    let args = seq![Expr::Col(41)];
    lemma_eval1(db, env, args, x[14]);
    lemma_call(db, env, ScalarFn::ExtractYear, args);
    assert(extract_field(ScalarFn::ExtractYear, civil_from_date(ival(x[14]))) == year_of(ival(x[14])));
}

/// The SELECT list on a FROM row is `sel_row`.
pub proof fn lemma_project_eval(db: Database, env: Row, x: Row)
    requires env_reads(env, x), xrow_typed(x),
    ensures eval_exprs(db, env, q9_exprs()) == Ok::<Row, SqlError>(sel_row(x)),
{
    hide(eval_expr);
    hide(eval_exprs);
    hide(civil_from_date);
    hide(year_of);
    lemma_env_vals(env, x);
    lemma_expr_col(db, env, 47);
    lemma_year_eval(db, env, x);
    lemma_amount_eval(db, env, x);
    lemma_eval3(db, env, q9_exprs(), x[16], Val::Num { coeff: year_of(ival(x[14])), scale: 0 }, Val::Num { coeff: amt_x(x), scale: 4 });
    assert(sel_row(x) =~= seq![x[16], Val::Num { coeff: year_of(ival(x[14])), scale: 0 }, Val::Num { coeff: amt_x(x), scale: 4 }]);
}

} // verus!
