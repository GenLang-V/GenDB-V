//! TPC-H Q12 in the accumulator normal form of `link::query` (`QuerySpec`), the statement's AST, and the per-row
//! agreement of the AST with the normal form.
//!
//! FROM is `orders x lineitem`: a joined row is an orders row (9 columns) followed by a lineitem row (16 columns).
//! The normal form reads its projection onto `j_cols()` = (o_orderkey, o_orderpriority, l_orderkey, l_shipdate,
//! l_commitdate, l_receiptdate, l_shipmode), positions 0..7 of `x` below. A projected row qualifies (`q12_qual`)
//! when the keys match, the ship mode is `$1` or `$2`, `l_commitdate < l_receiptdate`, `l_shipdate < l_commitdate`,
//! and the receipt day `r` (days since 2000-01-01) satisfies `r >= pd` and `r * usecs < t1` (`pd` the parameter
//! `$3`, `t1` the timestamp `$3 + 1 year`). The group key is the ship mode; aggregate 0 counts the high-priority
//! rows (`o_orderpriority` is `1-URGENT` or `2-HIGH`), aggregate 1 the others (`arg_of`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::scalar::*;
use crate::spec::datetime::*;
use crate::spec::equality::row_not_distinct;
use crate::spec::numeric::sign;
use crate::spec::relation::*;
use crate::link::query::*;
use crate::link::expr::*;
use crate::bridge::equality::same_exact_type;
use crate::agent::common::int_groups::*;

verus! {

// ------------------------------------------------------------------------------------------------ parameters

/// Microseconds per day.
pub open spec fn usecs() -> int {
    86_400_000_000
}

/// `$1`: its bytes.
pub open spec fn p1_of(ps: Seq<Literal>) -> Seq<u8> {
    match ps[0] { Literal::Text(b) => b, _ => Seq::empty() }
}

/// `$2`: its bytes.
pub open spec fn p2_of(ps: Seq<Literal>) -> Seq<u8> {
    match ps[1] { Literal::Text(b) => b, _ => Seq::empty() }
}

/// `$3`: its day number (days since 2000-01-01).
pub open spec fn pd_of(ps: Seq<Literal>) -> int {
    match ps[2] { Literal::Date { y, m, d } => date_from_civil(y, m, d), _ => 0 }
}

/// `$3::timestamp + interval '1 year'` for the parameter day `pd`.
pub open spec fn hi_res(pd: int) -> Result<int, SqlError> {
    match date_to_ts(pd) {
        Ok(t) => ts_add_interval(t, 12, 0, 0),
        Err(e) => Err(e),
    }
}

/// `1-URGENT`.
pub open spec fn urgent() -> Seq<u8> {
    seq![49u8, 45u8, 85u8, 82u8, 71u8, 69u8, 78u8, 84u8]
}

/// `2-HIGH`.
pub open spec fn high2() -> Seq<u8> {
    seq![50u8, 45u8, 72u8, 73u8, 71u8, 72u8]
}

/// A priority of the high group.
pub open spec fn is_high(b: Seq<u8>) -> bool {
    b == urgent() || b == high2()
}

// ------------------------------------------------------------------------------------------------ the normal form

/// Joined-row positions the normal form reads (orders: 0, 5; lineitem: 9 + 0, 9 + 10, 9 + 11, 9 + 12, 9 + 14).
pub open spec fn j_cols() -> Seq<nat> {
    seq![0nat, 5, 9, 19, 20, 21, 23]
}

/// WHERE of Q12 on a projected row `x` (the values' kinds are those of the columns, `j_row_ok`).
pub open spec fn q12_qual(p1: Seq<u8>, p2: Seq<u8>, pd: int, t1: int, x: Row) -> bool {
    &&& ival(x[0]) == ival(x[2])
    &&& (tval(x[6]) == p1 || tval(x[6]) == p2)
    &&& ival(x[4]) < ival(x[5])
    &&& ival(x[3]) < ival(x[4])
    &&& ival(x[5]) >= pd
    &&& ival(x[5]) * usecs() < t1
}

/// The two CASE indicators: aggregate 0 is 1 for a high priority, aggregate 1 is 1 for any other.
pub open spec fn arg_of(j: int, x: Row) -> int {
    if (j == 0) == is_high(tval(x[1])) { 1 } else { 0 }
}

pub open spec fn q12_spec(p1: Seq<u8>, p2: Seq<u8>, pd: int, t1: int) -> QuerySpec {
    QuerySpec {
        qual: |x: Row| q12_qual(p1, p2, pd, t1, x),
        key: |x: Row| seq![x[6]],
        arg: |j: int, x: Row| arg_of(j, x),
        aggs: seq![AggKind::Sum { scale: 0 }, AggKind::Sum { scale: 0 }],
        outs: seq![0nat, 1, 2],
        grouped: true,
    }
}

/// The normal form at the binding `ps` (with the upper bound `t1`).
pub open spec fn spec_at(ps: Seq<Literal>, t1: int) -> QuerySpec {
    q12_spec(p1_of(ps), p2_of(ps), pd_of(ps), t1)
}

// ------------------------------------------------------------------------------------------------ the statement's AST

/// `o_orderpriority = '1-URGENT' OR o_orderpriority = '2-HIGH'` (n9).
pub open spec fn ast_high() -> Pred {
    Pred::Or(
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5), b: Expr::Lit(Literal::Text(urgent())) }),
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5), b: Expr::Lit(Literal::Text(high2())) }),
    )
}

/// `o_orderpriority <> '1-URGENT' AND o_orderpriority <> '2-HIGH'` (n24).
pub open spec fn ast_low() -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Ne, a: Expr::Col(5), b: Expr::Lit(Literal::Text(urgent())) }),
        Box::new(Pred::Cmp { op: CmpOp::Ne, a: Expr::Col(5), b: Expr::Lit(Literal::Text(high2())) }),
    )
}

/// `CASE WHEN c THEN 1 ELSE 0 END`.
pub open spec fn ast_case(c: Pred) -> Expr {
    Expr::If {
        cond: Box::new(c),
        then_e: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })),
        else_e: Box::new(Expr::Lit(Literal::Int { v: 0, kind: IntKind::Int4 })),
    }
}

pub open spec fn ast_aggs() -> Seq<Agg> {
    two_sums(ast_case(ast_high()), ast_case(ast_low()))
}

pub open spec fn ast_keys() -> Seq<Expr> {
    seq![Expr::Col(23)]
}

/// `$3::timestamp + interval '1 year'` (n61).
pub open spec fn hi_expr(p: Literal) -> Expr {
    Expr::AddInterval {
        arg: Box::new(Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(p)) }),
        months: 12i32,
        days: 0i32,
        micros: 0i64,
    }
}

/// `o_orderkey = l_orderkey AND l_shipmode IN ($1, $2)` (n43).
pub open spec fn ast_p43(ps: Seq<Literal>) -> Pred {
    Pred::And(
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) }),
        Box::new(Pred::Or(
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(23), b: Expr::Lit(ps[0]) }),
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(23), b: Expr::Lit(ps[1]) }),
        )),
    )
}

/// `.. AND l_commitdate < l_receiptdate AND l_shipdate < l_commitdate AND l_receiptdate >= $3` (n56).
pub open spec fn ast_p56(ps: Seq<Literal>) -> Pred {
    Pred::And(
        Box::new(Pred::And(
            Box::new(Pred::And(
                Box::new(ast_p43(ps)),
                Box::new(Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(20), b: Expr::Col(21) }),
            )),
            Box::new(Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(19), b: Expr::Col(20) }),
        )),
        Box::new(Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(21), b: Expr::Lit(ps[2]) }),
    )
}

/// `l_receiptdate < $3 + interval '1 year'` (n62).
pub open spec fn ast_p62(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(21), b: hi_expr(ps[2]) }
}

/// The WHERE of Q12 (n63).
pub open spec fn ast_pred(ps: Seq<Literal>) -> Pred {
    Pred::And(Box::new(ast_p56(ps)), Box::new(ast_p62(ps)))
}

/// `orders x lineitem` (n66).
pub open spec fn ast_from() -> Query {
    Query::Product { left: Box::new(Query::Table(1)), right: Box::new(Query::Table(0)) }
}

pub open spec fn ast_input(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: ast_pred(ps), input: Box::new(ast_from()) }
}

pub open spec fn ast_body(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: ast_keys(), aggs: ast_aggs(), input: Box::new(ast_input(ps)) }
}

pub open spec fn ast_order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 0, desc: false, nulls_first: false }]
}

/// The emitted statement is this AST.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures
        crate::query::query_spec_at(ps).body == ast_body(ps),
        crate::query::query_spec_at(ps).keys == ast_order_keys(),
        crate::query::query_spec_at(ps).limit is None,
        crate::query::query_spec_at(ps).offset == 0,
{
    assert(urgent() =~= seq![49u8, 45u8, 85u8, 82u8, 71u8, 69u8, 78u8, 84u8]);
    assert(high2() =~= seq![50u8, 45u8, 72u8, 73u8, 71u8, 72u8]);
}

// ------------------------------------------------------------------------------------------------ per-row agreement

/// A joined row as the statement reads it: 25 columns, the keys integers, the dates dates, the texts texts.
pub open spec fn j_row_ok(r: Row) -> bool {
    &&& r.len() == 25
    &&& r[0] is Int
    &&& r[5] is Text
    &&& r[9] is Int
    &&& r[19] is Date
    &&& r[20] is Date
    &&& r[21] is Date
    &&& r[23] is Text
}

/// The parameter facts the per-row lemmas use: two texts and a date with day number `pd`.
pub open spec fn params_ok(ps: Seq<Literal>, pd: int) -> bool {
    &&& ps.len() == 3
    &&& ps[0] == Literal::Text(p1_of(ps))
    &&& ps[1] == Literal::Text(p2_of(ps))
    &&& lit_val(ps[2]) == Ok::<Val, SqlError>(Val::Date(pd))
}

/// Projection onto `j_cols()`.
pub proof fn lemma_proj_row(r: Row)
    requires r.len() == 25,
    ensures proj(r, j_cols()) == seq![r[0], r[5], r[9], r[19], r[20], r[21], r[23]],
{
    assert(proj(r, j_cols()) =~= seq![r[0], r[5], r[9], r[19], r[20], r[21], r[23]]);
}

/// The upper bound expression evaluates to `hi_res` (independent of the row).
pub proof fn lemma_hi_expr(db: Database, env: Row, p: Literal, pd: int)
    requires lit_val(p) == Ok::<Val, SqlError>(Val::Date(pd)),
    ensures
        eval_expr(db, env, hi_expr(p)) == match hi_res(pd) {
            Ok(t1) => Ok::<Val, SqlError>(Val::Ts(t1)),
            Err(e) => Err::<Val, SqlError>(e),
        },
{
    let c = Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(p)) };
    assert(eval_expr(db, env, Expr::Lit(p)) == Ok::<Val, SqlError>(Val::Date(pd)));
    match date_to_ts(pd) {
        Ok(t) => {
            assert(eval_expr(db, env, c) == Ok::<Val, SqlError>(Val::Ts(t)));
        },
        Err(e) => {
            assert(eval_expr(db, env, c) == Err::<Val, SqlError>(e));
        },
    }
}

/// A literal evaluates to its value.
proof fn lemma_lit(db: Database, r: Row, l: Literal)
    ensures eval_expr(db, r, Expr::Lit(l)) == lit_val(l),
{
}

/// The key and ship-mode part of the WHERE (n43).
proof fn lemma_p43(db: Database, r: Row, ps: Seq<Literal>, pd: int)
    requires j_row_ok(r), params_ok(ps, pd),
    ensures
        eval_pred(db, r, ast_p43(ps)) == Ok::<Truth, SqlError>(truth_of(
            ival(r[0]) == ival(r[9]) && (tval(r[23]) == p1_of(ps) || tval(r[23]) == p2_of(ps)))),
{
    hide(eval_pred);
    hide(eval_expr);
    let (k0, k9) = (r[0]->Int_0, r[9]->Int_0);
    lemma_expr_col(db, r, 0);
    lemma_expr_col(db, r, 9);
    lemma_compare_int(k0, k9);
    lemma_pred_cmp(db, r, CmpOp::Eq, Expr::Col(0), Expr::Col(9), r[0], r[9], k0, k9);
    let m = tval(r[23]);
    assert(r[23] == Val::Text(m));
    lemma_expr_col(db, r, 23);
    lemma_expr_text(db, r, p1_of(ps));
    lemma_expr_text(db, r, p2_of(ps));
    lemma_pred_text_cmp(db, r, CmpOp::Eq, Expr::Col(23), Expr::Lit(ps[0]), m, p1_of(ps));
    lemma_pred_text_cmp(db, r, CmpOp::Eq, Expr::Col(23), Expr::Lit(ps[1]), m, p2_of(ps));
    let eq1 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(23), b: Expr::Lit(ps[0]) };
    let eq2 = Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(23), b: Expr::Lit(ps[1]) };
    lemma_pred_or(db, r, eq1, eq2, m == p1_of(ps), m == p2_of(ps));
    lemma_pred_and(db, r, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) }, Pred::Or(Box::new(eq1), Box::new(eq2)),
        k0 == k9, m == p1_of(ps) || m == p2_of(ps));
}

/// The WHERE without its upper bound (n56).
pub open spec fn qual56(p1: Seq<u8>, p2: Seq<u8>, pd: int, x: Row) -> bool {
    &&& ival(x[0]) == ival(x[2])
    &&& (tval(x[6]) == p1 || tval(x[6]) == p2)
    &&& ival(x[4]) < ival(x[5])
    &&& ival(x[3]) < ival(x[4])
    &&& ival(x[5]) >= pd
}

proof fn lemma_p56(db: Database, r: Row, ps: Seq<Literal>, pd: int)
    requires j_row_ok(r), params_ok(ps, pd),
    ensures eval_pred(db, r, ast_p56(ps)) == Ok::<Truth, SqlError>(truth_of(qual56(p1_of(ps), p2_of(ps), pd, proj(r, j_cols())))),
{
    hide(eval_pred);
    hide(eval_expr);
    lemma_proj_row(r);
    lemma_p43(db, r, ps, pd);
    let (s, c, d) = (r[19]->Date_0, r[20]->Date_0, r[21]->Date_0);
    lemma_expr_col(db, r, 19);
    lemma_expr_col(db, r, 20);
    lemma_expr_col(db, r, 21);
    lemma_compare_date(c, d);
    lemma_pred_cmp(db, r, CmpOp::Lt, Expr::Col(20), Expr::Col(21), r[20], r[21], c, d);
    lemma_compare_date(s, c);
    lemma_pred_cmp(db, r, CmpOp::Lt, Expr::Col(19), Expr::Col(20), r[19], r[20], s, c);
    lemma_compare_date(d, pd);
    lemma_lit(db, r, ps[2]);
    lemma_pred_cmp(db, r, CmpOp::Ge, Expr::Col(21), Expr::Lit(ps[2]), r[21], Val::Date(pd), d, pd);
    let a1 = ival(r[0]) == ival(r[9]) && (tval(r[23]) == p1_of(ps) || tval(r[23]) == p2_of(ps));
    let lt1 = Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(20), b: Expr::Col(21) };
    let lt2 = Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(19), b: Expr::Col(20) };
    let ge = Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(21), b: Expr::Lit(ps[2]) };
    lemma_pred_and(db, r, ast_p43(ps), lt1, a1, c < d);
    let p47 = Pred::And(Box::new(ast_p43(ps)), Box::new(lt1));
    lemma_pred_and(db, r, p47, lt2, a1 && c < d, s < c);
    let p51 = Pred::And(Box::new(p47), Box::new(lt2));
    lemma_pred_and(db, r, p51, ge, a1 && c < d && s < c, d >= pd);
}

/// The WHERE on one joined row, when the upper bound is the timestamp `t1`: the normal form's condition.
pub proof fn lemma_pred_row(db: Database, r: Row, ps: Seq<Literal>, pd: int, t1: int)
    requires j_row_ok(r), params_ok(ps, pd), hi_res(pd) == Ok::<int, SqlError>(t1),
    ensures
        eval_pred(db, r, ast_pred(ps)) == Ok::<Truth, SqlError>(truth_of(q12_qual(p1_of(ps), p2_of(ps), pd, t1, proj(r, j_cols())))),
{
    hide(eval_pred);
    hide(eval_expr);
    lemma_proj_row(r);
    lemma_p56(db, r, ps, pd);
    let d = r[21]->Date_0;
    lemma_expr_col(db, r, 21);
    lemma_hi_expr(db, r, ps[2], pd);
    assert(compare(Val::Date(d), Val::Ts(t1)) == Some(sign(d * usecs() - t1)));
    lemma_pred_cmp(db, r, CmpOp::Lt, Expr::Col(21), hi_expr(ps[2]), r[21], Val::Ts(t1), d * usecs(), t1);
    lemma_pred_and(db, r, ast_p56(ps), ast_p62(ps), qual56(p1_of(ps), p2_of(ps), pd, proj(r, j_cols())), d * usecs() < t1);
}

/// The WHERE on one joined row, when the upper bound is the error `e`: the error.
pub proof fn lemma_pred_row_err(db: Database, r: Row, ps: Seq<Literal>, pd: int, e: SqlError)
    requires j_row_ok(r), params_ok(ps, pd), hi_res(pd) == Err::<int, SqlError>(e),
    ensures eval_pred(db, r, ast_pred(ps)) == Err::<Truth, SqlError>(e),
{
    lemma_p56(db, r, ps, pd);
    lemma_expr_col(db, r, 21);
    lemma_hi_expr(db, r, ps[2], pd);
    assert(eval_pred(db, r, ast_p62(ps)) == Err::<Truth, SqlError>(e));
}

/// The GROUP BY key on one joined row is the normal form's key.
pub proof fn lemma_keys_row(db: Database, r: Row)
    requires j_row_ok(r),
    ensures eval_exprs(db, r, ast_keys()) == Ok::<Row, SqlError>(seq![proj(r, j_cols())[6]]),
{
    hide(eval_exprs);
    hide(eval_expr);
    lemma_proj_row(r);
    let ks = ast_keys();
    assert(ks =~= col_exprs(seq![23nat]));
    lemma_eval_cols(db, r, seq![23nat]);
    assert(select(r, seq![23nat]) =~= seq![proj(r, j_cols())[6]]);
}

/// One evaluation step of `CASE WHEN cond THEN a ELSE b END` (lazy: only the taken branch).
proof fn lemma_eval_if(db: Database, r: Row, cond: Pred, a: Expr, b: Expr, x: bool)
    requires eval_pred(db, r, cond) == Ok::<Truth, SqlError>(truth_of(x)),
    ensures
        eval_expr(db, r, Expr::If { cond: Box::new(cond), then_e: Box::new(a), else_e: Box::new(b) })
            == if x { eval_expr(db, r, a) } else { eval_expr(db, r, b) },
{
}

/// An int4 literal `v` (0 or 1).
proof fn lemma_int_lit(db: Database, r: Row, v: int)
    requires v == 0 || v == 1,
    ensures eval_expr(db, r, Expr::Lit(Literal::Int { v, kind: IntKind::Int4 })) == Ok::<Val, SqlError>(Val::Int(v)),
{
    assert(int_in_range(IntKind::Int4, v));
    assert(lit_val(Literal::Int { v, kind: IntKind::Int4 }) == Ok::<Val, SqlError>(Val::Int(v)));
}

/// `CASE WHEN c THEN 1 ELSE 0 END` of a condition that evaluates to a two-valued truth.
proof fn lemma_case(db: Database, r: Row, c: Pred, b: bool)
    requires eval_pred(db, r, c) == Ok::<Truth, SqlError>(truth_of(b)),
    ensures eval_expr(db, r, ast_case(c)) == Ok::<Val, SqlError>(Val::Int(if b { 1 } else { 0 })),
{
    let one = Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 });
    let zero = Expr::Lit(Literal::Int { v: 0, kind: IntKind::Int4 });
    lemma_int_lit(db, r, 1);
    lemma_int_lit(db, r, 0);
    lemma_eval_if(db, r, c, one, zero, b);
}

/// The two CASE conditions on one joined row.
proof fn lemma_conds(db: Database, r: Row)
    requires j_row_ok(r),
    ensures
        eval_pred(db, r, ast_high()) == Ok::<Truth, SqlError>(truth_of(is_high(tval(r[5])))),
        eval_pred(db, r, ast_low()) == Ok::<Truth, SqlError>(truth_of(!is_high(tval(r[5])))),
{
    hide(eval_pred);
    hide(eval_expr);
    let p = tval(r[5]);
    assert(r[5] == Val::Text(p));
    lemma_expr_col(db, r, 5);
    lemma_expr_text(db, r, urgent());
    lemma_expr_text(db, r, high2());
    let u = Expr::Lit(Literal::Text(urgent()));
    let h = Expr::Lit(Literal::Text(high2()));
    lemma_pred_text_cmp(db, r, CmpOp::Eq, Expr::Col(5), u, p, urgent());
    lemma_pred_text_cmp(db, r, CmpOp::Eq, Expr::Col(5), h, p, high2());
    lemma_pred_text_cmp(db, r, CmpOp::Ne, Expr::Col(5), u, p, urgent());
    lemma_pred_text_cmp(db, r, CmpOp::Ne, Expr::Col(5), h, p, high2());
    lemma_pred_or(db, r, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5), b: u }, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5), b: h },
        p == urgent(), p == high2());
    lemma_pred_and(db, r, Pred::Cmp { op: CmpOp::Ne, a: Expr::Col(5), b: u }, Pred::Cmp { op: CmpOp::Ne, a: Expr::Col(5), b: h },
        p != urgent(), p != high2());
}

/// Two int4 SUMs over the argument expressions `e1`, `e2`.
pub open spec fn two_sums(e1: Expr, e2: Expr) -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Int4, arg: e1 }, Agg::Sum { kind: NumKind::Int4, arg: e2 }]
}

/// The argument outcomes of the two SUMs: one per aggregate, each its expression's value. (Each step is stated with
/// the evaluators hidden: unfolding them on the AST is expensive.)
proof fn lemma_two_results(db: Database, r: Row, e1: Expr, e2: Expr)
    ensures
        agg_arg_results(db, r, two_sums(e1, e2)).len() == 2,
        agg_arg_results(db, r, two_sums(e1, e2))[0] == eval_expr(db, r, e1),
        agg_arg_results(db, r, two_sums(e1, e2))[1] == eval_expr(db, r, e2),
{
    hide(eval_expr);
    hide(agg_arg);
    hide(collect);
    hide(agg_arg_results);
    let aggs = two_sums(e1, e2);
    lemma_agg_arg_results_index(db, r, aggs);
    assert(aggs[0] == Agg::Sum { kind: NumKind::Int4, arg: e1 });
    assert(aggs[1] == Agg::Sum { kind: NumKind::Int4, arg: e2 });
    lemma_agg_arg_sum(db, r, NumKind::Int4, e1);
    lemma_agg_arg_sum(db, r, NumKind::Int4, e2);
}

/// The arguments of two int4 SUMs whose argument expressions evaluate to `v1` and `v2`.
proof fn lemma_two_sums(db: Database, r: Row, e1: Expr, e2: Expr, v1: Val, v2: Val)
    requires eval_expr(db, r, e1) == Ok::<Val, SqlError>(v1), eval_expr(db, r, e2) == Ok::<Val, SqlError>(v2),
    ensures agg_args(db, r, two_sums(e1, e2)) == Ok::<Row, SqlError>(seq![v1, v2]),
{
    hide(eval_expr);
    hide(agg_arg);
    hide(collect);
    hide(agg_arg_results);
    lemma_two_results(db, r, e1, e2);
    let rs = agg_arg_results(db, r, two_sums(e1, e2));
    let vs = seq![v1, v2];
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        if i == 0 {} else { assert(i == 1); }
    }
    crate::bridge::collect::lemma_collect_all(rs, vs);
    crate::exec::relational::domain::lemma_agg_args(db, r, two_sums(e1, e2));
}

/// The two SUM arguments on one joined row: the normal form's int arguments.
pub proof fn lemma_args_row(db: Database, r: Row, g: QuerySpec)
    requires j_row_ok(r), g.aggs.len() == 2, forall|j: int, x: Row| #[trigger] (g.arg)(j, x) == arg_of(j, x),
    ensures agg_args(db, r, ast_aggs()) == Ok::<Row, SqlError>(int_args(g, proj(r, j_cols()))),
{
    hide(eval_expr);
    hide(eval_pred);
    hide(agg_args);
    lemma_proj_row(r);
    lemma_conds(db, r);
    let hi = is_high(tval(r[5]));
    lemma_case(db, r, ast_high(), hi);
    lemma_case(db, r, ast_low(), !hi);
    let v1 = Val::Int(if hi { 1 } else { 0 });
    let v2 = Val::Int(if hi { 0 } else { 1 });
    lemma_two_sums(db, r, ast_case(ast_high()), ast_case(ast_low()), v1, v2);
    let x = proj(r, j_cols());
    assert(x[1] == r[5]);
    assert((g.arg)(0, x) == arg_of(0, x));
    assert((g.arg)(1, x) == arg_of(1, x));
    assert(int_args(g, x) =~= seq![v1, v2]);
}

/// The aggregates are SUMs over int4 arguments.
pub proof fn lemma_aggs_int4(g: QuerySpec)
    requires g.aggs.len() == 2,
    ensures int4_sums(ast_aggs(), g),
{
}

/// Keys of projected rows are single texts: SQL "not distinct" is equality.
pub proof fn lemma_keys_exact(g: QuerySpec, xs: Seq<Row>)
    requires
        forall|x: Row| #[trigger] (g.key)(x) == seq![x[6]],
        forall|i: int| 0 <= i < xs.len() ==> (#[trigger] xs[i]).len() == 7 && xs[i][6] is Text,
    ensures keys_exact(g, xs),
{
    assert forall|a: int, b: int| 0 <= a < xs.len() && 0 <= b < xs.len() && (g.qual)(xs[a]) && (g.qual)(xs[b]) implies
        (row_not_distinct(#[trigger] (g.key)(xs[a]), #[trigger] (g.key)(xs[b])) <==> (g.key)(xs[a]) == (g.key)(xs[b])) by {
        let ka = (g.key)(xs[a]);
        let kb = (g.key)(xs[b]);
        assert(ka == seq![xs[a][6]]);
        assert(kb == seq![xs[b][6]]);
        assert(xs[a][6] is Text && xs[b][6] is Text);
        assert forall|i: int| 0 <= i < ka.len() implies same_exact_type(#[trigger] ka[i], kb[i]) by {}
        lemma_row_exact(ka, kb);
    }
}

} // verus!
