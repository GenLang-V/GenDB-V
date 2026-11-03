//! The statement's AST and its evaluation on one row of `lineitem x part`.
//!
//! A row `x` of the product is a lineitem row (16 columns) followed by a part row (9 columns). Its six query
//! columns are `z = proj(x, c6())`: l_partkey (1), l_extendedprice (5), l_discount (6), l_shipdate (10),
//! p_partkey (16) and p_type (20). On a typed row the WHERE condition is `terms::zq` of `z`
//! (`lemma_row_pred`), and the two SUM arguments are `av0(z)` (the CASE: the value at scale 4 for a promotion
//! type, else the numeric 0 of scale 0) and `av1(z)` (the value at scale 4) (`lemma_row_args`). LIKE 'PROMO%'
//! never raises (`lemma_like_ok`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::eval::*;
use crate::spec::numeric::*;
use crate::spec::int::IntKind;
use crate::spec::datetime::*;
use crate::spec::chars::chars;
use crate::spec::fns::like::*;
use crate::spec::relation::collect;
use crate::link::expr::*;
use crate::link::query::{proj, lemma_node_mul, lemma_node_add, lemma_agg_arg_sum};
use crate::bridge::collect::lemma_collect_all;
use crate::query::*;
use super::terms::*;
use super::answer::{hi_expr, win_ok, out_expr};

verus! {

// ------------------------------------------------------------------------------------------------ the AST

/// `l_partkey = p_partkey` (n35).
pub open spec fn pred_key() -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(1), b: Expr::Col(16) }
}

/// `l_shipdate >= $1` (n39).
pub open spec fn pred_lo(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(10), b: Expr::Lit(ps[0]) }
}

/// `l_shipdate < $1 + INTERVAL '1' MONTH` (n46).
pub open spec fn pred_hi(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(10), b: hi_expr(ps) }
}

/// The WHERE condition (n47).
pub open spec fn pred_q(ps: Seq<Literal>) -> Pred {
    Pred::And(Box::new(Pred::And(Box::new(pred_key()), Box::new(pred_lo(ps)))), Box::new(pred_hi(ps)))
}

/// `l_extendedprice * (1 - l_discount)` (n19 / n31).
pub open spec fn val_expr() -> Expr {
    Expr::Arith {
        op: ArithOp::Mul, kind: NumKind::Numeric,
        a: Box::new(Expr::Col(5)),
        b: Box::new(Expr::Arith {
            op: ArithOp::Sub, kind: NumKind::Numeric,
            a: Box::new(Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) }),
            b: Box::new(Expr::Col(6)),
        }),
    }
}

/// `1 - l_discount` (n18).
pub open spec fn one_minus_disc() -> Expr {
    Expr::Arith {
        op: ArithOp::Sub, kind: NumKind::Numeric,
        a: Box::new(Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) }),
        b: Box::new(Expr::Col(6)),
    }
}

/// `p_type LIKE 'PROMO%'` (n11).
pub open spec fn like_expr() -> Expr {
    Expr::Call { f: ScalarFn::Like, args: seq![Expr::Col(20), Expr::Lit(Literal::Text(promo_pat())), Expr::Lit(Literal::Text(seq![92u8]))] }
}

/// The CASE (n23).
pub open spec fn case_expr() -> Expr {
    Expr::If {
        cond: Box::new(Pred::OfBool(like_expr())),
        then_e: Box::new(val_expr()),
        else_e: Box::new(Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 0, kind: IntKind::Int4 })) }),
    }
}

/// The aggregates (n24, n32).
pub open spec fn aggs_q() -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: case_expr() }, Agg::Sum { kind: NumKind::Numeric, arg: val_expr() }]
}

/// The FROM product (n50).
pub open spec fn product_q() -> Query {
    Query::Product { left: Box::new(Query::Table(0)), right: Box::new(Query::Table(3)) }
}

/// The filtered product (n51).
pub open spec fn filter_q(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: pred_q(ps), input: Box::new(product_q()) }
}

/// The aggregate (n52).
pub open spec fn agg_q(ps: Seq<Literal>) -> Query {
    Query::Aggregate { aggs: aggs_q(), input: Box::new(filter_q(ps)) }
}

/// The statement: the projection of the aggregate, without ORDER BY, OFFSET or LIMIT.
pub proof fn lemma_ast(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == (Query::Project { exprs: seq![out_expr()], input: Box::new(agg_q(ps)) }),
        query_spec_at(ps).keys.len() == 0,
        query_spec_at(ps).offset == 0,
        query_spec_at(ps).limit is None,
{
    assert(query_spec_at(ps).keys =~= Seq::<OrderKey>::empty());
    assert(query_spec_at(ps).body == (Query::Project { exprs: seq![out_expr()], input: Box::new(agg_q(ps)) }));
}

// ------------------------------------------------------------------------------------------------ typed rows

/// Columns of the six query values of a product row.
pub open spec fn c6() -> Seq<nat> {
    seq![1nat, 5nat, 6nat, 10nat, 16nat, 20nat]
}

/// The six query values of a product row.
pub open spec fn zx(x: Row) -> Row {
    proj(x, c6())
}

/// A numeric(15, 2) value.
pub open spec fn num2(v: Val) -> bool {
    v == Val::Num { coeff: ival(v), scale: 2 } && -p15i() < ival(v) < p15i()
}

/// `10^15`.
pub open spec fn p15i() -> int {
    1_000_000_000_000_000
}

/// The typing facts the condition and the arguments need of a product row.
pub open spec fn prow_typed(x: Row) -> bool {
    &&& x.len() == 25
    &&& x[1] == Val::Int(ival(x[1]))
    &&& x[16] == Val::Int(ival(x[16]))
    &&& num2(x[5]) && num2(x[6])
    &&& x[10] == Val::Date(ival(x[10]))
    &&& x[20] == Val::Text(tval(x[20]))
}

/// The query values of a product row.
pub proof fn lemma_zx(x: Row)
    requires x.len() == 25,
    ensures
        zx(x).len() == 6,
        zx(x)[0] == x[1], zx(x)[1] == x[5], zx(x)[2] == x[6], zx(x)[3] == x[10], zx(x)[4] == x[16], zx(x)[5] == x[20],
{
}

// ------------------------------------------------------------------------------------------------ the condition

/// A literal evaluates to its value.
pub proof fn lemma_eval_lit(db: Database, env: Row, l: Literal)
    ensures eval_expr(db, env, Expr::Lit(l)) == lit_val(l),
{
}

/// An int4 literal's value.
pub proof fn lemma_int_lit(v: int)
    requires crate::spec::int::int_in_range(IntKind::Int4, v),
    ensures lit_val(Literal::Int { v, kind: IntKind::Int4 }) == Ok::<Val, SqlError>(Val::Int(v)),
{
}

/// A cast of an expression.
pub proof fn lemma_cast_eval(db: Database, env: Row, op: CastOp, a: Expr, va: Val)
    requires eval_expr(db, env, a) == Ok::<Val, SqlError>(va),
    ensures eval_expr(db, env, Expr::Cast { cast: op, arg: Box::new(a) }) == cast(op, va),
{
}

/// An int4 literal cast to numeric.
pub proof fn lemma_cast_int(db: Database, env: Row, v: int)
    requires crate::spec::int::int_in_range(IntKind::Int4, v),
    ensures
        eval_expr(db, env, Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v, kind: IntKind::Int4 })) })
            == Ok::<Val, SqlError>(Val::Num { coeff: v, scale: 0 }),
{
    hide(eval_expr);
    hide(lit_val);
    lemma_int_lit(v);
    lemma_eval_lit(db, env, Literal::Int { v, kind: IntKind::Int4 });
    lemma_cast_eval(db, env, CastOp::IntToNumeric, Expr::Lit(Literal::Int { v, kind: IntKind::Int4 }), Val::Int(v));
}

/// A function call on its evaluated arguments.
pub proof fn lemma_call_eval(db: Database, env: Row, f: ScalarFn, args: Seq<Expr>, vs: Row)
    requires eval_exprs(db, env, args) == Ok::<Row, SqlError>(vs),
    ensures eval_expr(db, env, Expr::Call { f, args }) == crate::spec::fns::apply_fn(f, vs),
{
}

/// A boolean expression as a condition.
pub proof fn lemma_ofbool(db: Database, env: Row, e: Expr, b: bool)
    requires eval_expr(db, env, e) == Ok::<Val, SqlError>(Val::Bool(b)),
    ensures eval_pred(db, env, Pred::OfBool(e)) == Ok::<Truth, SqlError>(truth_of(b)),
{
}

/// A comparison whose right operand errs (the left succeeding) is that error.
pub proof fn lemma_cmp_err_right(db: Database, env: Row, op: CmpOp, a: Expr, b: Expr, e: SqlError)
    requires eval_expr(db, env, a) is Ok, eval_expr(db, env, b) == Err::<Val, SqlError>(e),
    ensures eval_pred(db, env, Pred::Cmp { op, a, b }) == Err::<Truth, SqlError>(e),
{
}

/// `AND` with a succeeding left and an erring right operand is that error.
pub proof fn lemma_and_err_right(db: Database, env: Row, a: Pred, b: Pred, e: SqlError)
    requires eval_pred(db, env, a) is Ok, eval_pred(db, env, b) == Err::<Truth, SqlError>(e),
    ensures eval_pred(db, env, Pred::And(Box::new(a), Box::new(b))) == Err::<Truth, SqlError>(e),
{
}

/// The CASE from its condition and its value.
pub proof fn lemma_case(db: Database, x: Row, b: bool, val: Val)
    requires
        eval_pred(db, x, Pred::OfBool(like_expr())) == Ok::<Truth, SqlError>(truth_of(b)),
        eval_expr(db, x, val_expr()) == Ok::<Val, SqlError>(val),
        eval_expr(db, x, Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 0, kind: IntKind::Int4 })) })
            == Ok::<Val, SqlError>(Val::Num { coeff: 0, scale: 0 }),
    ensures
        eval_expr(db, x, case_expr()) == Ok::<Val, SqlError>(if b { val } else { Val::Num { coeff: 0, scale: 0 } }),
{
}

/// The WHERE condition on a typed row is `zq` of its query values.
pub proof fn lemma_row_pred(db: Database, x: Row, ps: Seq<Literal>, lo: int, hi: int)
    requires
        win_ok(ps, lo, hi),
        prow_typed(x),
    ensures
        eval_pred(db, x, pred_q(ps)) == Ok::<Truth, SqlError>(truth_of(zq(lo, hi, zx(x)))),
{
    hide(eval_pred);
    hide(eval_expr);
    let (k1, k2, s) = (ival(x[1]), ival(x[16]), ival(x[10]));
    lemma_zx(x);
    // l_partkey = p_partkey
    lemma_expr_col(db, x, 1);
    lemma_expr_col(db, x, 16);
    lemma_compare_int(k1, k2);
    lemma_pred_cmp(db, x, CmpOp::Eq, Expr::Col(1), Expr::Col(16), Val::Int(k1), Val::Int(k2), k1, k2);
    // l_shipdate >= $1
    lemma_expr_col(db, x, 10);
    assert(lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(lo)));
    lemma_eval_lit(db, x, ps[0]);
    lemma_compare_date(s, lo);
    lemma_pred_cmp(db, x, CmpOp::Ge, Expr::Col(10), Expr::Lit(ps[0]), Val::Date(s), Val::Date(lo), s, lo);
    // l_shipdate < $1 + 1 month
    lemma_hi_closed(ps);
    lemma_expr_closed(db, x, hi_expr(ps));
    lemma_compare_date_midnight(s, hi);
    lemma_pred_cmp(db, x, CmpOp::Lt, Expr::Col(10), hi_expr(ps), Val::Date(s), Val::Ts(hi * usecs_per_day()), s, hi);
    lemma_pred_and(db, x, pred_key(), pred_lo(ps), k1 == k2, lo <= s);
    lemma_pred_and(db, x, Pred::And(Box::new(pred_key()), Box::new(pred_lo(ps))), pred_hi(ps), k1 == k2 && lo <= s, s < hi);
}

/// `$1 + INTERVAL '1' MONTH` has no column reference.
pub proof fn lemma_hi_closed(ps: Seq<Literal>)
    ensures closed_expr(hi_expr(ps)),
{
    reveal_with_fuel(closed_expr, 3);
}

/// With `$1 + 1 month` erring, the WHERE condition errs on every typed row with that error.
pub proof fn lemma_row_pred_err(db: Database, x: Row, ps: Seq<Literal>, e: SqlError)
    requires
        param_domain(ps),
        eval_expr(closed_db(), Seq::empty(), hi_expr(ps)) == Err::<Val, SqlError>(e),
        prow_typed(x),
    ensures
        eval_pred(db, x, pred_q(ps)) == Err::<Truth, SqlError>(e),
{
    hide(eval_expr);
    hide(eval_pred);
    let (k1, k2, s) = (ival(x[1]), ival(x[16]), ival(x[10]));
    lemma_expr_col(db, x, 1);
    lemma_expr_col(db, x, 16);
    lemma_compare_int(k1, k2);
    lemma_pred_cmp(db, x, CmpOp::Eq, Expr::Col(1), Expr::Col(16), Val::Int(k1), Val::Int(k2), k1, k2);
    lemma_expr_col(db, x, 10);
    let lo = date_from_civil(ps[0]->Date_y, ps[0]->Date_m, ps[0]->Date_d);
    assert(lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(lo)));
    lemma_eval_lit(db, x, ps[0]);
    lemma_compare_date(s, lo);
    lemma_pred_cmp(db, x, CmpOp::Ge, Expr::Col(10), Expr::Lit(ps[0]), Val::Date(s), Val::Date(lo), s, lo);
    lemma_hi_closed(ps);
    lemma_expr_closed(db, x, hi_expr(ps));
    lemma_cmp_err_right(db, x, CmpOp::Lt, Expr::Col(10), hi_expr(ps), e);
    lemma_pred_and(db, x, pred_key(), pred_lo(ps), k1 == k2, lo <= s);
    lemma_and_err_right(db, x, Pred::And(Box::new(pred_key()), Box::new(pred_lo(ps))), pred_hi(ps), e);
}

// ------------------------------------------------------------------------------------------------ LIKE

/// The characters of `'PROMO%'`: one byte each.
pub open spec fn promo_chars() -> Seq<Seq<u8>> {
    seq![seq![80u8], seq![82u8], seq![79u8], seq![77u8], seq![79u8], seq![37u8]]
}

/// The tokens of `'PROMO%'`: five literal characters and `%`.
pub open spec fn promo_toks() -> Seq<LikeTok> {
    seq![LikeTok::Lit(seq![80u8]), LikeTok::Lit(seq![82u8]), LikeTok::Lit(seq![79u8]), LikeTok::Lit(seq![77u8]),
        LikeTok::Lit(seq![79u8]), LikeTok::Any]
}

/// The tokens of `'PROMO%'` with escape `\` have no dangling escape.
pub proof fn lemma_promo_tokens()
    ensures
        chars(promo_pat()) == promo_chars(),
        chars(seq![92u8]) == seq![seq![92u8]],
        like_tokens(chars(promo_pat()), Some(seq![92u8]), 0) == promo_toks(),
        crate::bridge::fns::like::no_dangling(like_tokens(chars(promo_pat()), Some(seq![92u8]), 0)),
{
    assert(chars(seq![92u8]) == seq![seq![92u8]]) by (compute);
    assert(chars(promo_pat()) == promo_chars()) by (compute);
    assert(like_tokens(promo_chars(), Some(seq![92u8]), 0) == promo_toks()) by (compute);
    let t = promo_toks();
    assert forall|k: int| 0 <= k < t.len() implies !(#[trigger] t[k] is Dangling) by {
        if k == 0 {} else if k == 1 {} else if k == 2 {} else if k == 3 {} else if k == 4 {} else {}
    }
}

/// `s LIKE 'PROMO%'` is a boolean: true exactly for `promo_text(s)`.
pub proof fn lemma_like_ok(s: Seq<u8>)
    ensures like_value(Val::Text(s), Val::Text(promo_pat()), Val::Text(seq![92u8])) == Ok::<Val, SqlError>(Val::Bool(promo_text(s))),
{
    lemma_promo_tokens();
    let toks = like_tokens(chars(promo_pat()), Some(seq![92u8]), 0);
    crate::bridge::fns::like::lemma_like_mt_std(chars(s), toks);
    assert(escape_of(chars(seq![92u8])) == Some(seq![92u8]));
}

/// The LIKE call on a product row with a text p_type.
pub proof fn lemma_like_eval(db: Database, x: Row)
    requires x.len() == 25, x[20] == Val::Text(tval(x[20])),
    ensures eval_pred(db, x, Pred::OfBool(like_expr())) == Ok::<Truth, SqlError>(truth_of(promo_text(tval(x[20])))),
{
    hide(eval_expr);
    hide(eval_pred);
    hide(eval_exprs);
    hide(like_value);
    let args = seq![Expr::Col(20), Expr::Lit(Literal::Text(promo_pat())), Expr::Lit(Literal::Text(seq![92u8]))];
    let vs = seq![x[20], Val::Text(promo_pat()), Val::Text(seq![92u8])];
    let rs = expr_results(db, x, args);
    lemma_expr_results_index(db, x, args);
    lemma_expr_col(db, x, 20);
    lemma_expr_text(db, x, promo_pat());
    lemma_expr_text(db, x, seq![92u8]);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        assert(rs[i] == eval_expr(db, x, args[i]));
    }
    reveal(eval_exprs);
    lemma_collect_all(rs, vs);
    assert(eval_exprs(db, x, args) == Ok::<Row, SqlError>(vs));
    lemma_like_ok(tval(x[20]));
    lemma_call_eval(db, x, ScalarFn::Like, args, vs);
    assert(crate::spec::fns::apply_fn(ScalarFn::Like, vs) == like_value(vs[0], vs[1], vs[2]));
    lemma_ofbool(db, x, like_expr(), promo_text(tval(x[20])));
}

// ------------------------------------------------------------------------------------------------ the arguments

/// `l_extendedprice * (1 - l_discount)` of a row: the coefficient of scale 4.
pub open spec fn av1(z: Row) -> Val {
    Val::Num { coeff: zv(z), scale: 4 }
}

/// The CASE of a row: the value for a promotion type, else the numeric 0 of scale 0.
pub open spec fn av0(z: Row) -> Val {
    if zp(z) { Val::Num { coeff: zv(z), scale: 4 } } else { Val::Num { coeff: 0, scale: 0 } }
}

pub proof fn lemma_pow10_values()
    ensures pow10(0) == 1, pow10(1) == 10, pow10(2) == 100, pow10(15) == p15i(), pow10(17) == 100 * p15i(),
{
    assert(pow10(17) == 100 * p15i()) by (compute);
    assert(pow10(15) == p15i()) by (compute);
    assert(pow10(2) == 100) by (compute);
    assert(pow10(1) == 10) by (compute);
}

/// `l_extendedprice * (1 - l_discount)` on a typed row.
pub proof fn lemma_val_eval(db: Database, x: Row)
    requires prow_typed(x),
    ensures eval_expr(db, x, val_expr()) == Ok::<Val, SqlError>(av1(zx(x))),
{
    hide(eval_expr);
    lemma_zx(x);
    lemma_pow10_values();
    let (p, d) = (ival(x[5]), ival(x[6]));
    lemma_expr_col(db, x, 5);
    lemma_expr_col(db, x, 6);
    let one = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) };
    assert(crate::spec::int::int_in_range(IntKind::Int4, 1)) by (compute);
    lemma_cast_int(db, x, 1);
    // 1 - d at scale 2
    lemma_node_add(db, x, ArithOp::Sub, one, Expr::Col(6), 1, 0, 1, d, 2, 15, 2, 100, 1, 17);
    assert(1 * 100 - d * 1 == 100 - d);
    // p * (100 - d) at scale 4
    lemma_node_mul(db, x, Expr::Col(5), one_minus_disc(), p, 2, 15, 100 - d, 2, 17);
}

/// The two SUM arguments of a typed row.
pub proof fn lemma_row_args(db: Database, x: Row)
    requires prow_typed(x),
    ensures agg_args(db, x, aggs_q()) == Ok::<Row, SqlError>(seq![av0(zx(x)), av1(zx(x))]),
{
    hide(eval_expr);
    hide(eval_pred);
    hide(agg_arg);
    hide(promo_text);
    hide(av0);
    hide(av1);
    hide(zx);
    hide(prow_typed);
    lemma_case_row(db, x);
    lemma_val_row(db, x);
    lemma_agg_arg_sum(db, x, NumKind::Numeric, case_expr());
    lemma_agg_arg_sum(db, x, NumKind::Numeric, val_expr());
    let rs = agg_arg_results(db, x, aggs_q());
    lemma_agg_arg_results_index(db, x, aggs_q());
    let vs = seq![av0(zx(x)), av1(zx(x))];
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        assert(rs[i] == agg_arg(db, x, aggs_q()[i]));
    }
    lemma_collect_all(rs, vs);
}

/// The value argument on a typed row.
pub proof fn lemma_val_row(db: Database, x: Row)
    requires prow_typed(x),
    ensures eval_expr(db, x, val_expr()) == Ok::<Val, SqlError>(av1(zx(x))),
{
    lemma_val_eval(db, x);
}

/// The CASE argument on a typed row.
pub proof fn lemma_case_row(db: Database, x: Row)
    requires prow_typed(x),
    ensures eval_expr(db, x, case_expr()) == Ok::<Val, SqlError>(av0(zx(x))),
{
    hide(eval_expr);
    hide(eval_pred);
    hide(promo_text);
    lemma_zx(x);
    lemma_val_eval(db, x);
    lemma_like_eval(db, x);
    assert(crate::spec::int::int_in_range(IntKind::Int4, 0)) by (compute);
    lemma_cast_int(db, x, 0);
    lemma_case(db, x, promo_text(tval(x[20])), av1(zx(x)));
}

} // verus!
