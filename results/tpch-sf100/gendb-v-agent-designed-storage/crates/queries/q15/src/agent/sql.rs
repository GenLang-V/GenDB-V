//! The Q15 statement's AST in named pieces and its per-row meaning.
//!
//! The view `revenue0` appears twice: as the right input of the FROM product (outer context empty) and inside the
//! scalar subquery `SELECT MAX(total_revenue) FROM revenue0`, which is evaluated with the product row (9 columns) as
//! its context. Its pieces are therefore parameterized by the context length `o` (0 or 9): lineitem column `c` is
//! `Col(o + c)` (`rev_group(o, ps)`). `lemma_shape` identifies the pieces with `query::query_spec_at`.
//!
//! Per lineitem row (in an environment holding the row's columns at `o ..`): the WHERE condition is
//! `lo <= l_shipdate <= hi` for the window of `window::hi_ok` (`lemma_pred_row`) or the error of
//! `$1 + 3 months` (`lemma_pred_err_row`); the group key is `[l_suppkey]` and the SUM argument the numeric
//! `l_extendedprice * (100 - l_discount)` at scale 4 (`lemma_args_row`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::IntKind;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::collect;
use crate::spec::datetime::*;
use crate::query::{query_spec_at, param_typed};
use crate::link::query::{col_exprs, lemma_eval_cols, select, lemma_node_mul, lemma_node_add};
use crate::link::expr::{lemma_expr_col, lemma_pred_cmp, lemma_pred_and, lemma_compare_int, lemma_compare_date};
use super::window::*;

verus! {

// ------------------------------------------------------------------------------------------------ the pieces

/// `$1 + INTERVAL '3' MONTH` (a timestamp).
pub open spec fn hi_expr(ps: Seq<Literal>) -> Expr {
    Expr::AddInterval {
        arg: Box::new(Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(ps[0])) }),
        months: 3i32,
        days: 0i32,
        micros: 0i64,
    }
}

/// `l_shipdate >= $1` with lineitem at offset `o`.
pub open spec fn p_ge(o: nat, ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(o + 10), b: Expr::Lit(ps[0]) }
}

/// `l_shipdate < $1 + INTERVAL '3' MONTH` with lineitem at offset `o`.
pub open spec fn p_lt(o: nat, ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(o + 10), b: hi_expr(ps) }
}

/// The WHERE condition of `revenue0` with lineitem at offset `o`.
pub open spec fn p_date(o: nat, ps: Seq<Literal>) -> Pred {
    Pred::And(Box::new(p_ge(o, ps)), Box::new(p_lt(o, ps)))
}

/// `1 :: numeric`.
pub open spec fn one_num() -> Expr {
    Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) }
}

/// `1 - l_discount` with lineitem at offset `o`.
pub open spec fn one_minus(o: nat) -> Expr {
    Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(one_num()), b: Box::new(Expr::Col(o + 6)) }
}

/// `l_extendedprice * (1 - l_discount)` with lineitem at offset `o`.
pub open spec fn rev_arg(o: nat) -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Col(o + 5)), b: Box::new(one_minus(o)) }
}

pub open spec fn rev_aggs(o: nat) -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: rev_arg(o) }]
}

/// GROUP BY l_suppkey.
pub open spec fn rev_keys(o: nat) -> Seq<Expr> {
    seq![Expr::Col(o + 2)]
}

pub open spec fn rev_filter(o: nat, ps: Seq<Literal>) -> Query {
    Query::Filter { pred: p_date(o, ps), input: Box::new(Query::Table(0)) }
}

/// `revenue0` with lineitem at offset `o`.
pub open spec fn rev_group(o: nat, ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: rev_keys(o), aggs: rev_aggs(o), input: Box::new(rev_filter(o, ps)) }
}

/// `MAX(total_revenue)` over `revenue0` in the product row's context (9 columns): the revenue is column 10.
pub open spec fn max_aggs() -> Seq<Agg> {
    seq![Agg::Max(Expr::Col(10))]
}

/// `SELECT MAX(total_revenue) FROM revenue0`.
pub open spec fn max_q(ps: Seq<Literal>) -> Query {
    Query::Aggregate { aggs: max_aggs(), input: Box::new(rev_group(9, ps)) }
}

/// `s_suppkey = supplier_no`.
pub open spec fn p_key() -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(7) }
}

/// `total_revenue = (SELECT MAX(total_revenue) FROM revenue0)`.
pub open spec fn p_max(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(8), b: Expr::Subquery(Box::new(max_q(ps))) }
}

pub open spec fn outer_pred(ps: Seq<Literal>) -> Pred {
    Pred::And(Box::new(p_key()), Box::new(p_max(ps)))
}

/// FROM supplier, revenue0.
pub open spec fn prod_q(ps: Seq<Literal>) -> Query {
    Query::Product { left: Box::new(Query::Table(5)), right: Box::new(rev_group(0, ps)) }
}

pub open spec fn filt_q(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: outer_pred(ps), input: Box::new(prod_q(ps)) }
}

/// SELECT s_suppkey, s_name, s_address, s_phone, total_revenue.
pub open spec fn out_cols() -> Seq<nat> {
    seq![0nat, 1, 2, 4, 8]
}

pub open spec fn body_q(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: col_exprs(out_cols()), input: Box::new(filt_q(ps)) }
}

/// ORDER BY s_suppkey.
pub open spec fn order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 0, desc: false, nulls_first: false }]
}

/// The statement is these pieces, ordered by s_suppkey, without OFFSET or LIMIT.
pub proof fn lemma_shape(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == body_q(ps),
        query_spec_at(ps).keys == order_keys(),
        query_spec_at(ps).limit is None,
        query_spec_at(ps).offset == 0,
{
    assert(col_exprs(out_cols()) =~= seq![Expr::Col(0), Expr::Col(1), Expr::Col(2), Expr::Col(4), Expr::Col(8)]);
    assert(query_spec_at(ps).keys =~= order_keys());
    assert(rev_keys(0) =~= seq![Expr::Col(2)]);
    assert(rev_keys(9) =~= seq![Expr::Col(11)]);
    assert(rev_aggs(0) =~= seq![Agg::Sum { kind: NumKind::Numeric, arg: rev_arg(0) }]);
    assert(max_aggs() =~= seq![Agg::Max(Expr::Col(10))]);
}

// ------------------------------------------------------------------------------------------------ per row

proof fn lemma_pow10_small()
    ensures pow10(0) == 1, pow10(1) == 10, pow10(2) == 100,
{
    assert(pow10(0) == 1) by (compute);
    assert(pow10(1) == 10) by (compute);
    assert(pow10(2) == 100) by (compute);
}

/// `l_extendedprice * (1 - l_discount)` on an environment holding the price and discount coefficients (scale 2,
/// at most 15 digits) at `o + 5` and `o + 6`: the numeric `pr * (100 - ds)` at scale 4.
pub proof fn lemma_arg_eval(db: Database, env: Row, o: nat, pr: int, ds: int)
    requires
        env.len() > o + 6,
        env[(o + 5) as int] == (Val::Num { coeff: pr, scale: 2 }),
        env[(o + 6) as int] == (Val::Num { coeff: ds, scale: 2 }),
        -pow10(15) < pr < pow10(15),
        -pow10(15) < ds < pow10(15),
    ensures
        eval_expr(db, env, rev_arg(o)) == Ok::<Val, SqlError>(Val::Num { coeff: pr * (100 - ds), scale: 4 }),
{
    lemma_pow10_small();
    lemma_pow10_monotone(15, 16);
    let one = one_num();
    assert(eval_expr(db, env, Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) == Ok::<Val, SqlError>(Val::Int(1)));
    assert(eval_expr(db, env, one) == Ok::<Val, SqlError>(Val::Num { coeff: 1, scale: 0 }));
    lemma_expr_col(db, env, o + 5);
    lemma_expr_col(db, env, o + 6);
    assert(abs(1) < pow10(1));
    assert(abs(ds) < pow10(15));
    assert(max_nat(0, 2) == 2);
    lemma_node_add(db, env, ArithOp::Sub, one, Expr::Col(o + 6), 1, 0, 1, ds, 2, 15, 2, 100, 1, 16);
    assert(eval_expr(db, env, one_minus(o)) == Ok::<Val, SqlError>(Val::Num { coeff: 100 - ds, scale: 2 }));
    assert(abs(pr) < pow10(15));
    lemma_node_mul(db, env, Expr::Col(o + 5), one_minus(o), pr, 2, 15, 100 - ds, 2, 16);
}

/// The SUM argument list on such an environment.
pub proof fn lemma_args_row(db: Database, env: Row, o: nat, pr: int, ds: int)
    requires
        env.len() > o + 6,
        env[(o + 5) as int] == (Val::Num { coeff: pr, scale: 2 }),
        env[(o + 6) as int] == (Val::Num { coeff: ds, scale: 2 }),
        -pow10(15) < pr < pow10(15),
        -pow10(15) < ds < pow10(15),
    ensures
        agg_args(db, env, rev_aggs(o)) == Ok::<Row, SqlError>(seq![Val::Num { coeff: pr * (100 - ds), scale: 4 }]),
{
    let v = Val::Num { coeff: pr * (100 - ds), scale: 4 };
    lemma_arg_eval(db, env, o, pr, ds);
    let rs = agg_arg_results(db, env, rev_aggs(o));
    lemma_agg_arg_results_index(db, env, rev_aggs(o));
    assert(rs[0] == agg_arg(db, env, rev_aggs(o)[0]));
    assert(rs.len() == 1);
    assert(rs.drop_last().len() == 0);
    assert(collect(rs.drop_last()) == Ok::<Seq<Val>, SqlError>(Seq::empty()));
    assert(rs.last() == Ok::<Val, SqlError>(v));
    assert(Seq::<Val>::empty().push(v) =~= seq![v]);
}

/// The group key on such an environment.
pub proof fn lemma_keys_row(db: Database, env: Row, o: nat)
    requires env.len() > o + 2,
    ensures eval_exprs(db, env, rev_keys(o)) == Ok::<Row, SqlError>(seq![env[(o + 2) as int]]),
{
    assert(rev_keys(o) =~= col_exprs(seq![o + 2]));
    lemma_eval_cols(db, env, seq![o + 2]);
    assert(select(env, seq![o + 2]) =~= seq![env[(o + 2) as int]]);
}

/// `x * U < t` exactly when `x <= (t - 1) / U` (floor division, `U > 0`).
pub proof fn lemma_lt_floor(x: int, t: int, u: int)
    requires u > 0,
    ensures (x * u < t) == (x <= (t - 1) / u),
{
    let q = (t - 1) / u;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(t - 1, u);
    vstd::arithmetic::div_mod::lemma_mod_bound(t - 1, u);
    if x <= q {
        assert(x * u <= q * u) by (nonlinear_arith) requires x <= q, u > 0;
        assert(u * q == q * u) by (nonlinear_arith);
    } else {
        assert(x * u >= (q + 1) * u) by (nonlinear_arith) requires x >= q + 1, u > 0;
        assert((q + 1) * u == q * u + u) by (nonlinear_arith);
        assert(u * q == q * u) by (nonlinear_arith);
    }
}

/// `$1 + 3 months` evaluates (in any environment) to `hi_value`.
pub proof fn lemma_hi_expr(db: Database, env: Row, ps: Seq<Literal>)
    requires param_typed(ps),
    ensures
        eval_expr(db, env, hi_expr(ps)) == match hi_value(lo_of(ps)) {
            Ok(t) => Ok::<Val, SqlError>(Val::Ts(t)),
            Err(e) => Err::<Val, SqlError>(e),
        },
{
    lemma_lit(ps);
    let lit = Expr::Lit(ps[0]);
    let cast_e = Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(lit) };
    assert(eval_expr(db, env, lit) == lit_val(ps[0]));
    match date_to_ts(lo_of(ps)) {
        Ok(t) => {
            assert(eval_expr(db, env, cast_e) == Ok::<Val, SqlError>(Val::Ts(t)));
        },
        Err(e) => {
            assert(eval_expr(db, env, cast_e) == Err::<Val, SqlError>(e));
        },
    }
}

/// `l_shipdate >= $1` on an environment holding the ship date at `o + 10`.
proof fn lemma_ge_row(db: Database, env: Row, o: nat, ps: Seq<Literal>, sd: int)
    requires
        param_typed(ps),
        env.len() > o + 10,
        env[(o + 10) as int] == Val::Date(sd),
    ensures
        eval_pred(db, env, p_ge(o, ps)) == Ok::<Truth, SqlError>(truth_of(sd >= lo_of(ps))),
{
    hide(eval_pred);
    hide(eval_expr);
    let lo = lo_of(ps);
    lemma_lit(ps);
    assert(eval_expr(db, env, Expr::Lit(ps[0])) == lit_val(ps[0])) by {
        reveal(eval_expr);
    }
    lemma_expr_col(db, env, o + 10);
    lemma_compare_date(sd, lo);
    lemma_pred_cmp(db, env, CmpOp::Ge, Expr::Col(o + 10), Expr::Lit(ps[0]), Val::Date(sd), Val::Date(lo), sd, lo);
}

/// The WHERE condition of `revenue0` on an environment holding the ship date at `o + 10`, for the window
/// `[lo, hi]` of `hi_ok`.
pub proof fn lemma_pred_row(db: Database, env: Row, o: nat, ps: Seq<Literal>, hi: int, sd: int)
    requires
        param_typed(ps),
        hi_ok(lo_of(ps), hi),
        env.len() > o + 10,
        env[(o + 10) as int] == Val::Date(sd),
    ensures
        eval_pred(db, env, p_date(o, ps)) == Ok::<Truth, SqlError>(truth_of(lo_of(ps) <= sd && sd <= hi)),
{
    hide(eval_pred);
    hide(eval_expr);
    let lo = lo_of(ps);
    let t1 = hi_value(lo)->Ok_0;
    let u = usecs_per_day();
    lemma_ge_row(db, env, o, ps, sd);
    lemma_hi_expr(db, env, ps);
    lemma_expr_col(db, env, o + 10);
    assert(compare(Val::Date(sd), Val::Ts(t1)) == Some(sign(sd * u - t1)));
    lemma_pred_cmp(db, env, CmpOp::Lt, Expr::Col(o + 10), hi_expr(ps), Val::Date(sd), Val::Ts(t1), sd * u, t1);
    lemma_lt_floor(sd, t1, u);
    lemma_pred_and(db, env, p_ge(o, ps), p_lt(o, ps), sd >= lo, sd * u < t1);
}

/// One unfolding step: a comparison whose right operand fails.
proof fn lemma_cmp_err_right(db: Database, env: Row, op: CmpOp, a: Expr, b: Expr, va: Val, e: SqlError)
    requires
        eval_expr(db, env, a) == Ok::<Val, SqlError>(va),
        eval_expr(db, env, b) == Err::<Val, SqlError>(e),
    ensures eval_pred(db, env, Pred::Cmp { op, a, b }) == Err::<Truth, SqlError>(e),
{
}

/// One unfolding step: a conjunction whose right operand fails after the left one succeeded.
proof fn lemma_and_err_right(db: Database, env: Row, a: Pred, b: Pred, t: Truth, e: SqlError)
    requires
        eval_pred(db, env, a) == Ok::<Truth, SqlError>(t),
        eval_pred(db, env, b) == Err::<Truth, SqlError>(e),
    ensures eval_pred(db, env, Pred::And(Box::new(a), Box::new(b))) == Err::<Truth, SqlError>(e),
{
}

/// An error of `$1 + 3 months` is the outcome of the WHERE condition on every lineitem row.
pub proof fn lemma_pred_err_row(db: Database, env: Row, o: nat, ps: Seq<Literal>, sd: int)
    requires
        param_typed(ps),
        hi_value(lo_of(ps)) is Err,
        env.len() > o + 10,
        env[(o + 10) as int] == Val::Date(sd),
    ensures
        eval_pred(db, env, p_date(o, ps)) == Err::<Truth, SqlError>(hi_value(lo_of(ps))->Err_0),
{
    hide(eval_pred);
    hide(eval_expr);
    let e = hi_value(lo_of(ps))->Err_0;
    lemma_ge_row(db, env, o, ps, sd);
    lemma_hi_expr(db, env, ps);
    lemma_expr_col(db, env, o + 10);
    lemma_cmp_err_right(db, env, CmpOp::Lt, Expr::Col(o + 10), hi_expr(ps), Val::Date(sd), e);
    lemma_and_err_right(db, env, p_ge(o, ps), p_lt(o, ps), truth_of(sd >= lo_of(ps)), e);
}

/// `s_suppkey = supplier_no` on a product row.
pub proof fn lemma_key_pred(db: Database, y: Row, a: int, b: int)
    requires
        y.len() == 9,
        y[0] == Val::Int(a),
        y[7] == Val::Int(b),
    ensures
        eval_pred(db, y, p_key()) == Ok::<Truth, SqlError>(truth_of(a == b)),
{
    hide(eval_expr);
    lemma_expr_col(db, y, 0);
    lemma_expr_col(db, y, 7);
    lemma_compare_int(a, b);
    lemma_pred_cmp(db, y, CmpOp::Eq, Expr::Col(0), Expr::Col(7), Val::Int(a), Val::Int(b), a, b);
}

} // verus!
