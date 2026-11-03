//! The Q3 statement's AST in named pieces (`q3_*`; `lemma_q3_shape` identifies them with `query::query_spec_at`) and
//! its per-row meaning: on a joined row `customer ++ orders ++ lineitem` (33 columns) whose read columns hold the
//! values `ck, st, ok, oc, od, sp, lk, pr, ds, sh`, the WHERE condition is the two-valued
//! `st == $1 && ck == oc && lk == ok && od < $2 && sh > $2`, the group key is `(lk, od, sp)` and the SUM argument
//! is the numeric `pr * (100 - ds)` at scale 4 (`lemma_row_eval`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::IntKind;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::relation::collect;
use crate::spec::datetime::{date_from_civil, date_valid, valid_ymd};
use crate::query::{query_spec_at, param_domain};
use crate::link::query::{col_exprs, lemma_eval_cols, select, lemma_node_mul, lemma_node_add};
use crate::link::expr::{lemma_expr_col, lemma_expr_text, lemma_pred_cmp, lemma_pred_text_cmp, lemma_pred_and,
    lemma_compare_int, lemma_compare_date};
use super::qspec::*;

verus! {

/// `c_mktsegment = $1 AND c_custkey = o_custkey AND l_orderkey = o_orderkey AND o_orderdate < $2 AND
/// l_shipdate > $2` over the joined row (positions: 6, 0, 9, 17, 8, 12, 27).
pub open spec fn q3_pred(ps: Seq<Literal>) -> Pred {
    Pred::And(
        Box::new(Pred::And(
            Box::new(Pred::And(
                Box::new(Pred::And(
                    Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(6), b: Expr::Lit(ps[0]) }),
                    Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) }),
                )),
                Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(17), b: Expr::Col(8) }),
            )),
            Box::new(Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(12), b: Expr::Lit(ps[1]) }),
        )),
        Box::new(Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(27), b: Expr::Lit(ps[1]) }),
    )
}

/// GROUP BY l_orderkey, o_orderdate, o_shippriority.
pub open spec fn q3_gkeys() -> Seq<Expr> {
    seq![Expr::Col(17), Expr::Col(12), Expr::Col(15)]
}

/// `l_extendedprice * (1 - l_discount)`.
pub open spec fn q3_arg() -> Expr {
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

pub open spec fn q3_aggs() -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: q3_arg() }]
}

/// FROM customer, orders, lineitem.
pub open spec fn q3_from() -> Query {
    Query::Product { left: Box::new(Query::Product { left: Box::new(Query::Table(2)), right: Box::new(Query::Table(1)) }), right: Box::new(Query::Table(0)) }
}

pub open spec fn q3_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: q3_pred(ps), input: Box::new(q3_from()) }
}

pub open spec fn q3_group(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: q3_gkeys(), aggs: q3_aggs(), input: Box::new(q3_filter(ps)) }
}

/// SELECT l_orderkey, revenue, o_orderdate, o_shippriority (positions of the GROUP BY row).
pub open spec fn q3_outs() -> Seq<nat> {
    seq![0nat, 3, 1, 2]
}

pub open spec fn q3_body(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: col_exprs(q3_outs()), input: Box::new(q3_group(ps)) }
}

/// The statement is these pieces, ordered by `q3_keys` with LIMIT 10.
pub proof fn lemma_q3_shape(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == q3_body(ps),
        query_spec_at(ps).keys == q3_keys(),
        query_spec_at(ps).limit == Some(10nat),
        query_spec_at(ps).offset == 0,
{
    assert(col_exprs(q3_outs()) =~= seq![Expr::Col(0), Expr::Col(3), Expr::Col(1), Expr::Col(2)]);
    assert(query_spec_at(ps).keys =~= q3_keys());
}

/// The binding's literals: `$1` evaluates to its text, `$2` to its date (`qp_of`).
pub proof fn lemma_params(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures
        ps[0] == Literal::Text(qp_of(ps).seg),
        lit_val(ps[1]) == Ok::<Val, SqlError>(Val::Date(qp_of(ps).day)),
        date_valid(qp_of(ps).day),
{
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
        env.len() == 33,
        env[22] == (Val::Num { coeff: pr, scale: 2 }),
        env[23] == (Val::Num { coeff: ds, scale: 2 }),
        -pow10(15) < pr < pow10(15),
        -pow10(15) < ds < pow10(15),
    ensures
        eval_expr(db, env, q3_arg()) == Ok::<Val, SqlError>(Val::Num { coeff: pr * (100 - ds), scale: 4 }),
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
    requires eval_expr(db, env, q3_arg()) == Ok::<Val, SqlError>(v),
    ensures agg_args(db, env, q3_aggs()) == Ok::<Row, SqlError>(seq![v]),
{
    let rs = agg_arg_results(db, env, q3_aggs());
    lemma_agg_arg_results_index(db, env, q3_aggs());
    assert(rs[0] == agg_arg(db, env, q3_aggs()[0]));
    assert(rs.len() == 1);
    assert(rs.drop_last().len() == 0);
    assert(collect(rs.drop_last()) == Ok::<Seq<Val>, SqlError>(Seq::empty()));
    assert(rs.last() == Ok::<Val, SqlError>(v));
    assert(Seq::<Val>::empty().push(v) =~= seq![v]);
}

/// `$2` evaluates to its date.
proof fn lemma_lit_date(db: Database, env: Row, ps: Seq<Literal>)
    requires param_domain(ps),
    ensures eval_expr(db, env, Expr::Lit(ps[1])) == Ok::<Val, SqlError>(Val::Date(qp_of(ps).day)),
{
    lemma_params(ps);
}

/// The WHERE condition on a joined row, from the values of its read columns.
pub proof fn lemma_pred_eval(db: Database, env: Row, ps: Seq<Literal>, ck: int, st: Seq<u8>, ok: int, oc: int, od: int,
    lk: int, sh: int)
    requires
        param_domain(ps),
        env.len() == 33,
        env[0] == Val::Int(ck),
        env[6] == Val::Text(st),
        env[8] == Val::Int(ok),
        env[9] == Val::Int(oc),
        env[12] == Val::Date(od),
        env[17] == Val::Int(lk),
        env[27] == Val::Date(sh),
    ensures
        eval_pred(db, env, q3_pred(ps)) == Ok::<Truth, SqlError>(truth_of(
            st == qp_of(ps).seg && ck == oc && lk == ok && od < qp_of(ps).day && sh > qp_of(ps).day)),
{
    hide(eval_pred);
    hide(eval_expr);
    let p = qp_of(ps);
    lemma_params(ps);
    // c_mktsegment = $1
    lemma_expr_col(db, env, 6);
    lemma_expr_text(db, env, p.seg);
    lemma_pred_text_cmp(db, env, CmpOp::Eq, Expr::Col(6), Expr::Lit(ps[0]), st, p.seg);
    let p18 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(6), b: Expr::Lit(ps[0]) };
    // c_custkey = o_custkey
    lemma_expr_col(db, env, 0);
    lemma_expr_col(db, env, 9);
    lemma_compare_int(ck, oc);
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(0), Expr::Col(9), Val::Int(ck), Val::Int(oc), ck, oc);
    let p21 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) };
    lemma_pred_and(db, env, p18, p21, st == p.seg, ck == oc);
    let p22 = Pred::And(Box::new(p18), Box::new(p21));
    // l_orderkey = o_orderkey
    lemma_expr_col(db, env, 17);
    lemma_expr_col(db, env, 8);
    lemma_compare_int(lk, ok);
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(17), Expr::Col(8), Val::Int(lk), Val::Int(ok), lk, ok);
    let p25 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(17), b: Expr::Col(8) };
    lemma_pred_and(db, env, p22, p25, st == p.seg && ck == oc, lk == ok);
    let p26 = Pred::And(Box::new(p22), Box::new(p25));
    // o_orderdate < $2
    lemma_lit_date(db, env, ps);
    lemma_expr_col(db, env, 12);
    lemma_compare_date(od, p.day);
    lemma_pred_cmp(db, env, CmpOp::Lt, Expr::Col(12), Expr::Lit(ps[1]), Val::Date(od), Val::Date(p.day), od, p.day);
    let p30 = Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(12), b: Expr::Lit(ps[1]) };
    lemma_pred_and(db, env, p26, p30, st == p.seg && ck == oc && lk == ok, od < p.day);
    let p31 = Pred::And(Box::new(p26), Box::new(p30));
    // l_shipdate > $2
    lemma_expr_col(db, env, 27);
    lemma_compare_date(sh, p.day);
    lemma_pred_cmp(db, env, CmpOp::Gt, Expr::Col(27), Expr::Lit(ps[1]), Val::Date(sh), Val::Date(p.day), sh, p.day);
    let p35 = Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(27), b: Expr::Lit(ps[1]) };
    lemma_pred_and(db, env, p31, p35, st == p.seg && ck == oc && lk == ok && od < p.day, sh > p.day);
    assert(q3_pred(ps) == Pred::And(Box::new(p31), Box::new(p35)));
}

/// The group key on a joined row.
pub proof fn lemma_keys_eval(db: Database, env: Row, od: int, sp: int, lk: int)
    requires
        env.len() == 33,
        env[12] == Val::Date(od),
        env[15] == Val::Int(sp),
        env[17] == Val::Int(lk),
    ensures
        eval_exprs(db, env, q3_gkeys()) == Ok::<Row, SqlError>(seq![Val::Int(lk), Val::Date(od), Val::Int(sp)]),
{
    assert(q3_gkeys() =~= col_exprs(seq![17nat, 12, 15]));
    lemma_eval_cols(db, env, seq![17nat, 12, 15]);
    assert(select(env, seq![17nat, 12, 15]) =~= seq![Val::Int(lk), Val::Date(od), Val::Int(sp)]);
}

/// The SUM argument list on a joined row.
pub proof fn lemma_args_eval(db: Database, env: Row, pr: int, ds: int)
    requires
        env.len() == 33,
        env[22] == (Val::Num { coeff: pr, scale: 2 }),
        env[23] == (Val::Num { coeff: ds, scale: 2 }),
        -pow10(15) < pr < pow10(15),
        -pow10(15) < ds < pow10(15),
    ensures
        agg_args(db, env, q3_aggs()) == Ok::<Row, SqlError>(seq![Val::Num { coeff: pr * (100 - ds), scale: 4 }]),
{
    lemma_arg_eval(db, env, pr, ds);
    lemma_agg_args_one(db, env, Val::Num { coeff: pr * (100 - ds), scale: 4 });
}

} // verus!
