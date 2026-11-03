//! The Q10 statement's AST in named pieces (`q10_*`; `lemma_q10_shape` identifies them with `query::query_spec_at`)
//! and its per-row meaning: on a joined row `customer ++ orders ++ lineitem ++ nation` (37 columns) whose read
//! columns hold `ck, cn | ok, oc, od | lk, rf | nk`, the WHERE condition is the two-valued
//! `ck == oc && lk == ok && lo <= od <= hi && rf == 'R' && cn == nk` (`lemma_pred_eval`, for the window `[lo, hi]`
//! of `window::hi_ok`), or the error of `$1 + 3 months` (`lemma_pred_err`); the group key is
//! `(c_custkey, c_name, c_acctbal, c_phone, n_name, c_address, c_comment)` and the SUM argument is the numeric
//! `pr * (100 - ds)` at scale 4.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::IntKind;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::collect;
use crate::spec::datetime::*;
use crate::query::{query_spec_at, param_domain, param_typed};
use crate::link::query::{col_exprs, lemma_eval_cols, select, lemma_node_mul, lemma_node_add};
use crate::link::expr::{lemma_expr_col, lemma_expr_text, lemma_pred_cmp, lemma_pred_text_cmp, lemma_pred_and,
    lemma_compare_int, lemma_compare_date};
use super::qspec::r_text;
use super::window::*;

verus! {

/// `$1 + INTERVAL '3' MONTH` (a timestamp).
pub open spec fn hi_expr(ps: Seq<Literal>) -> Expr {
    Expr::AddInterval {
        arg: Box::new(Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(ps[0])) }),
        months: 3i32,
        days: 0i32,
        micros: 0i64,
    }
}

/// `c_custkey = o_custkey AND l_orderkey = o_orderkey` (positions 0, 9, 17, 8).
pub open spec fn p_join() -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) }),
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(17), b: Expr::Col(8) }),
    )
}

/// `.. AND o_orderdate >= $1` (position 12).
pub open spec fn p_ge(ps: Seq<Literal>) -> Pred {
    Pred::And(Box::new(p_join()), Box::new(Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(12), b: Expr::Lit(ps[0]) }))
}

/// `.. AND o_orderdate < $1 + INTERVAL '3' MONTH`.
pub open spec fn p_lt(ps: Seq<Literal>) -> Pred {
    Pred::And(Box::new(p_ge(ps)), Box::new(Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(12), b: hi_expr(ps) }))
}

/// `.. AND l_returnflag = 'R'` (position 25).
pub open spec fn p_rf(ps: Seq<Literal>) -> Pred {
    Pred::And(Box::new(p_lt(ps)), Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(25), b: Expr::Lit(Literal::Text(r_text())) }))
}

/// The WHERE condition: `.. AND c_nationkey = n_nationkey` (positions 3, 33).
pub open spec fn q10_pred(ps: Seq<Literal>) -> Pred {
    Pred::And(Box::new(p_rf(ps)), Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(3), b: Expr::Col(33) }))
}

/// GROUP BY c_custkey, c_name, c_acctbal, c_phone, n_name, c_address, c_comment.
pub open spec fn q10_gkeys() -> Seq<Expr> {
    seq![Expr::Col(0), Expr::Col(1), Expr::Col(5), Expr::Col(4), Expr::Col(34), Expr::Col(2), Expr::Col(7)]
}

/// `l_extendedprice * (1 - l_discount)`.
pub open spec fn q10_arg() -> Expr {
    Expr::Arith {
        op: ArithOp::Mul,
        kind: NumKind::Numeric,
        a: Box::new(Expr::Col(22)),
        b: Box::new(Expr::Arith {
            op: ArithOp::Sub,
            kind: NumKind::Numeric,
            a: Box::new(Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) }),
            b: Box::new(Expr::Col(23)),
        }),
    }
}

pub open spec fn q10_aggs() -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: q10_arg() }]
}

/// FROM customer, orders, lineitem, nation.
pub open spec fn q10_from() -> Query {
    Query::Product {
        left: Box::new(Query::Product {
            left: Box::new(Query::Product { left: Box::new(Query::Table(2)), right: Box::new(Query::Table(1)) }),
            right: Box::new(Query::Table(0)),
        }),
        right: Box::new(Query::Table(6)),
    }
}

pub open spec fn q10_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: q10_pred(ps), input: Box::new(q10_from()) }
}

pub open spec fn q10_group(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: q10_gkeys(), aggs: q10_aggs(), input: Box::new(q10_filter(ps)) }
}

/// SELECT c_custkey, c_name, revenue, c_acctbal, n_name, c_address, c_phone, c_comment (positions of the GROUP BY
/// row `key ++ [revenue]`).
pub open spec fn q10_outs() -> Seq<nat> {
    seq![0nat, 1, 7, 2, 4, 5, 3, 6]
}

pub open spec fn q10_body(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: col_exprs(q10_outs()), input: Box::new(q10_group(ps)) }
}

/// The statement is these pieces, ordered by `qspec::q10_keys` with LIMIT 20.
pub proof fn lemma_q10_shape(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == q10_body(ps),
        query_spec_at(ps).keys == super::qspec::q10_keys(),
        query_spec_at(ps).limit == Some(20nat),
        query_spec_at(ps).offset == 0,
{
    assert(col_exprs(q10_outs()) =~= seq![Expr::Col(0), Expr::Col(1), Expr::Col(7), Expr::Col(2), Expr::Col(4),
        Expr::Col(5), Expr::Col(3), Expr::Col(6)]);
    assert(query_spec_at(ps).keys =~= super::qspec::q10_keys());
    assert(r_text() =~= seq![82u8]);
}

/// pow10 values used by the argument's digit bounds.
proof fn lemma_pow10_small()
    ensures pow10(0) == 1, pow10(1) == 10, pow10(2) == 100,
{
    assert(pow10(0) == 1) by (compute);
    assert(pow10(1) == 10) by (compute);
    assert(pow10(2) == 100) by (compute);
}

/// The SUM argument on a row with `l_extendedprice = pr`, `l_discount = ds` (coefficients at scale 2, at most 15
/// digits): the numeric `pr * (100 - ds)` at scale 4.
pub proof fn lemma_arg_eval(db: Database, env: Row, pr: int, ds: int)
    requires
        env.len() == 37,
        env[22] == (Val::Num { coeff: pr, scale: 2 }),
        env[23] == (Val::Num { coeff: ds, scale: 2 }),
        -pow10(15) < pr < pow10(15),
        -pow10(15) < ds < pow10(15),
    ensures
        eval_expr(db, env, q10_arg()) == Ok::<Val, SqlError>(Val::Num { coeff: pr * (100 - ds), scale: 4 }),
{
    lemma_pow10_small();
    lemma_pow10_monotone(15, 16);
    let one = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) };
    assert(eval_expr(db, env, Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) == Ok::<Val, SqlError>(Val::Int(1)));
    assert(eval_expr(db, env, one) == Ok::<Val, SqlError>(Val::Num { coeff: 1, scale: 0 }));
    lemma_expr_col(db, env, 22);
    lemma_expr_col(db, env, 23);
    assert(crate::spec::numeric::abs(1) < pow10(1));
    assert(crate::spec::numeric::abs(ds) < pow10(15));
    assert(max_nat(0, 2) == 2);
    lemma_node_add(db, env, ArithOp::Sub, one, Expr::Col(23), 1, 0, 1, ds, 2, 15, 2, 100, 1, 16);
    let sub = Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(one), b: Box::new(Expr::Col(23)) };
    assert(eval_expr(db, env, sub) == Ok::<Val, SqlError>(Val::Num { coeff: 100 - ds, scale: 2 }));
    assert(crate::spec::numeric::abs(pr) < pow10(15));
    lemma_node_mul(db, env, Expr::Col(22), sub, pr, 2, 15, 100 - ds, 2, 16);
}

/// One aggregate argument list: its value.
proof fn lemma_agg_args_one(db: Database, env: Row, v: Val)
    requires eval_expr(db, env, q10_arg()) == Ok::<Val, SqlError>(v),
    ensures agg_args(db, env, q10_aggs()) == Ok::<Row, SqlError>(seq![v]),
{
    let rs = agg_arg_results(db, env, q10_aggs());
    lemma_agg_arg_results_index(db, env, q10_aggs());
    assert(rs[0] == agg_arg(db, env, q10_aggs()[0]));
    assert(rs.len() == 1);
    assert(rs.drop_last().len() == 0);
    assert(collect(rs.drop_last()) == Ok::<Seq<Val>, SqlError>(Seq::empty()));
    assert(rs.last() == Ok::<Val, SqlError>(v));
    assert(Seq::<Val>::empty().push(v) =~= seq![v]);
}

/// `x * U < t` exactly when `x <= (t - 1) / U` (floor division, `U > 0`).
pub proof fn lemma_lt_floor(x: int, t: int, u: int)
    requires u > 0,
    ensures (x * u < t) == (x <= (t - 1) / u),
{
    let q = (t - 1) / u;
    let r = (t - 1) % u;
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

/// One unfolding step: a literal evaluates to its value.
proof fn lemma_expr_lit(db: Database, env: Row, l: Literal)
    ensures eval_expr(db, env, Expr::Lit(l)) == lit_val(l),
{
}

/// One unfolding step: a cast of an evaluated operand.
proof fn lemma_expr_cast(db: Database, env: Row, op: CastOp, a: Expr)
    ensures
        eval_expr(db, env, Expr::Cast { cast: op, arg: Box::new(a) }) == match eval_expr(db, env, a) {
            Err(err) => Err(err),
            Ok(v) => cast(op, v),
        },
{
}

/// One unfolding step: an interval added to an evaluated operand.
proof fn lemma_expr_add_interval(db: Database, env: Row, a: Expr, months: i32, days: i32, micros: i64)
    ensures
        eval_expr(db, env, Expr::AddInterval { arg: Box::new(a), months, days, micros }) == match eval_expr(db, env, a) {
            Err(err) => Err(err),
            Ok(v) => add_interval(v, months, days, micros),
        },
{
}

/// One unfolding step: a comparison whose right operand fails.
proof fn lemma_cmp_err_right(db: Database, env: Row, op: CmpOp, a: Expr, b: Expr, va: Val, e: SqlError)
    requires
        eval_expr(db, env, a) == Ok::<Val, SqlError>(va),
        eval_expr(db, env, b) == Err::<Val, SqlError>(e),
    ensures eval_pred(db, env, Pred::Cmp { op, a, b }) == Err::<Truth, SqlError>(e),
{
}

/// One unfolding step: a conjunction whose left operand fails.
proof fn lemma_and_err_left(db: Database, env: Row, a: Pred, b: Pred, e: SqlError)
    requires eval_pred(db, env, a) == Err::<Truth, SqlError>(e),
    ensures eval_pred(db, env, Pred::And(Box::new(a), Box::new(b))) == Err::<Truth, SqlError>(e),
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

/// `$1 + 3 months` evaluates (in any environment) to `hi_value`.
proof fn lemma_hi_expr(db: Database, env: Row, ps: Seq<Literal>)
    requires param_typed(ps),
    ensures
        eval_expr(db, env, hi_expr(ps)) == match hi_value(lo_of(ps)) {
            Ok(t) => Ok::<Val, SqlError>(Val::Ts(t)),
            Err(e) => Err::<Val, SqlError>(e),
        },
{
    hide(eval_expr);
    lemma_lit(ps);
    lemma_expr_lit(db, env, ps[0]);
    let lit = Expr::Lit(ps[0]);
    let cast_e = Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(lit) };
    lemma_expr_cast(db, env, CastOp::DateToTimestamp, lit);
    lemma_expr_add_interval(db, env, cast_e, 3i32, 0i32, 0i64);
    match date_to_ts(lo_of(ps)) {
        Ok(t) => {
            assert(eval_expr(db, env, cast_e) == Ok::<Val, SqlError>(Val::Ts(t)));
        },
        Err(e) => {
            assert(eval_expr(db, env, cast_e) == Err::<Val, SqlError>(e));
        },
    }
}

/// The join condition and `o_orderdate >= $1` on a joined row.
proof fn lemma_ge_eval(db: Database, env: Row, ps: Seq<Literal>, ck: int, ok: int, oc: int, od: int, lk: int)
    requires
        param_typed(ps),
        env.len() == 37,
        env[0] == Val::Int(ck),
        env[8] == Val::Int(ok),
        env[9] == Val::Int(oc),
        env[12] == Val::Date(od),
        env[17] == Val::Int(lk),
    ensures
        eval_pred(db, env, p_ge(ps)) == Ok::<Truth, SqlError>(truth_of(ck == oc && lk == ok && od >= lo_of(ps))),
{
    hide(eval_pred);
    hide(eval_expr);
    let lo = lo_of(ps);
    lemma_lit(ps);
    lemma_expr_lit(db, env, ps[0]);
    // c_custkey = o_custkey
    lemma_expr_col(db, env, 0);
    lemma_expr_col(db, env, 9);
    lemma_compare_int(ck, oc);
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(0), Expr::Col(9), Val::Int(ck), Val::Int(oc), ck, oc);
    let pa = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) };
    // l_orderkey = o_orderkey
    lemma_expr_col(db, env, 17);
    lemma_expr_col(db, env, 8);
    lemma_compare_int(lk, ok);
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(17), Expr::Col(8), Val::Int(lk), Val::Int(ok), lk, ok);
    let pb = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(17), b: Expr::Col(8) };
    lemma_pred_and(db, env, pa, pb, ck == oc, lk == ok);
    // o_orderdate >= $1
    lemma_expr_col(db, env, 12);
    lemma_compare_date(od, lo);
    lemma_pred_cmp(db, env, CmpOp::Ge, Expr::Col(12), Expr::Lit(ps[0]), Val::Date(od), Val::Date(lo), od, lo);
    let pc = Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(12), b: Expr::Lit(ps[0]) };
    lemma_pred_and(db, env, p_join(), pc, ck == oc && lk == ok, od >= lo);
}

/// The WHERE condition on a joined row, from the values of its read columns, for the window `[lo, hi]`.
pub proof fn lemma_pred_eval(db: Database, env: Row, ps: Seq<Literal>, hi: int, ck: int, cn: int, ok: int, oc: int,
    od: int, lk: int, rf: Seq<u8>, nk: int)
    requires
        param_typed(ps),
        hi_ok(lo_of(ps), hi),
        env.len() == 37,
        env[0] == Val::Int(ck),
        env[3] == Val::Int(cn),
        env[8] == Val::Int(ok),
        env[9] == Val::Int(oc),
        env[12] == Val::Date(od),
        env[17] == Val::Int(lk),
        env[25] == Val::Text(rf),
        env[33] == Val::Int(nk),
    ensures
        eval_pred(db, env, q10_pred(ps)) == Ok::<Truth, SqlError>(truth_of(
            ck == oc && lk == ok && lo_of(ps) <= od && od <= hi && rf == r_text() && cn == nk)),
{
    hide(eval_pred);
    hide(eval_expr);
    let lo = lo_of(ps);
    let t1 = hi_value(lo)->Ok_0;
    let u = usecs_per_day();
    lemma_ge_eval(db, env, ps, ck, ok, oc, od, lk);
    // o_orderdate < $1 + 3 months
    lemma_hi_expr(db, env, ps);
    lemma_expr_col(db, env, 12);
    assert(compare(Val::Date(od), Val::Ts(t1)) == Some(sign(od * u - t1)));
    lemma_pred_cmp(db, env, CmpOp::Lt, Expr::Col(12), hi_expr(ps), Val::Date(od), Val::Ts(t1), od * u, t1);
    lemma_lt_floor(od, t1, u);
    let pd = Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(12), b: hi_expr(ps) };
    lemma_pred_and(db, env, p_ge(ps), pd, ck == oc && lk == ok && od >= lo, od * u < t1);
    // l_returnflag = 'R'
    lemma_expr_col(db, env, 25);
    lemma_expr_text(db, env, r_text());
    lemma_pred_text_cmp(db, env, CmpOp::Eq, Expr::Col(25), Expr::Lit(Literal::Text(r_text())), rf, r_text());
    let pe = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(25), b: Expr::Lit(Literal::Text(r_text())) };
    lemma_pred_and(db, env, p_lt(ps), pe, ck == oc && lk == ok && od >= lo && od * u < t1, rf == r_text());
    // c_nationkey = n_nationkey
    lemma_expr_col(db, env, 3);
    lemma_expr_col(db, env, 33);
    lemma_compare_int(cn, nk);
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(3), Expr::Col(33), Val::Int(cn), Val::Int(nk), cn, nk);
    let pf = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(3), b: Expr::Col(33) };
    lemma_pred_and(db, env, p_rf(ps), pf, ck == oc && lk == ok && od >= lo && od * u < t1 && rf == r_text(), cn == nk);
}

/// An error of `$1 + 3 months` is the outcome of the WHERE condition on every joined row.
pub proof fn lemma_pred_err(db: Database, env: Row, ps: Seq<Literal>, ck: int, ok: int, oc: int, od: int, lk: int)
    requires
        param_typed(ps),
        hi_value(lo_of(ps)) is Err,
        env.len() == 37,
        env[0] == Val::Int(ck),
        env[8] == Val::Int(ok),
        env[9] == Val::Int(oc),
        env[12] == Val::Date(od),
        env[17] == Val::Int(lk),
    ensures
        eval_pred(db, env, q10_pred(ps)) == Err::<Truth, SqlError>(hi_value(lo_of(ps))->Err_0),
{
    hide(eval_pred);
    hide(eval_expr);
    let e = hi_value(lo_of(ps))->Err_0;
    lemma_ge_eval(db, env, ps, ck, ok, oc, od, lk);
    lemma_hi_expr(db, env, ps);
    lemma_expr_col(db, env, 12);
    lemma_cmp_err_right(db, env, CmpOp::Lt, Expr::Col(12), hi_expr(ps), Val::Date(od), e);
    let pd = Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(12), b: hi_expr(ps) };
    lemma_and_err_right(db, env, p_ge(ps), pd, truth_of(ck == oc && lk == ok && od >= lo_of(ps)), e);
    let pe = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(25), b: Expr::Lit(Literal::Text(r_text())) };
    lemma_and_err_left(db, env, p_lt(ps), pe, e);
    let pf = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(3), b: Expr::Col(33) };
    lemma_and_err_left(db, env, p_rf(ps), pf, e);
}

/// The group key on a joined row.
pub proof fn lemma_keys_eval(db: Database, env: Row)
    requires env.len() == 37,
    ensures
        eval_exprs(db, env, q10_gkeys()) == Ok::<Row, SqlError>(seq![env[0], env[1], env[5], env[4], env[34], env[2], env[7]]),
{
    assert(q10_gkeys() =~= col_exprs(seq![0nat, 1, 5, 4, 34, 2, 7]));
    lemma_eval_cols(db, env, seq![0nat, 1, 5, 4, 34, 2, 7]);
    assert(select(env, seq![0nat, 1, 5, 4, 34, 2, 7]) =~= seq![env[0], env[1], env[5], env[4], env[34], env[2], env[7]]);
}

/// The SUM argument list on a joined row.
pub proof fn lemma_args_eval(db: Database, env: Row, pr: int, ds: int)
    requires
        env.len() == 37,
        env[22] == (Val::Num { coeff: pr, scale: 2 }),
        env[23] == (Val::Num { coeff: ds, scale: 2 }),
        -pow10(15) < pr < pow10(15),
        -pow10(15) < ds < pow10(15),
    ensures
        agg_args(db, env, q10_aggs()) == Ok::<Row, SqlError>(seq![Val::Num { coeff: pr * (100 - ds), scale: 4 }]),
{
    lemma_arg_eval(db, env, pr, ds);
    lemma_agg_args_one(db, env, Val::Num { coeff: pr * (100 - ds), scale: 4 });
}

} // verus!
