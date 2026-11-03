//! The statement's AST and its evaluation on one row of `lineitem x part`.
//!
//! A row `x` of the product is a lineitem row (16 columns) followed by a part row (9 columns). Its ten query values
//! are `zx(x) = proj(x, c10())`: l_partkey (1), l_quantity (4), l_extendedprice (5), l_discount (6), l_shipinstruct
//! (13), l_shipmode (14), p_partkey (16), p_brand (19), p_size (21) and p_container (22). On a typed row, arm `a` of
//! the WHERE condition is `terms::arm_w` of those values unless `$q + 10` leaves int4, in which case it is the error
//! 22003 (`lemma_arm`); the whole condition is `terms::wq` (`lemma_row_pred`) or that error
//! (`lemma_row_pred_err`). The SUM argument is the value at scale 4 (`lemma_row_arg`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::eval::*;
use crate::spec::numeric::*;
use crate::spec::int::{IntKind, int_in_range, int_result};
use crate::spec::limits::int4_max;
use crate::link::expr::*;
use crate::link::query::{proj, lemma_node_mul, lemma_node_add, lemma_agg_arg_sum};
use crate::bridge::collect::lemma_collect_all;
use crate::query::*;
use super::terms::*;
use super::bind::{num2, int8v, textv};

verus! {

// ------------------------------------------------------------------------------------------------ the AST

/// An int4 literal.
pub open spec fn int4(v: int) -> Literal {
    Literal::Int { v, kind: IntKind::Int4 }
}

pub open spec fn cmp(op: CmpOp, a: Expr, b: Expr) -> Pred {
    Pred::Cmp { op, a, b }
}

pub open spec fn and(a: Pred, b: Pred) -> Pred {
    Pred::And(Box::new(a), Box::new(b))
}

pub open spec fn or(a: Pred, b: Pred) -> Pred {
    Pred::Or(Box::new(a), Box::new(b))
}

/// `col = 'text'`.
pub open spec fn text_eq(c: nat, t: Seq<u8>) -> Pred {
    cmp(CmpOp::Eq, Expr::Col(c), Expr::Lit(Literal::Text(t)))
}

/// `p_partkey = l_partkey`.
pub open spec fn key_pred() -> Pred {
    cmp(CmpOp::Eq, Expr::Col(16), Expr::Col(1))
}

/// `p_brand = $b`.
pub open spec fn brand_pred(pb: Literal) -> Pred {
    cmp(CmpOp::Eq, Expr::Col(19), Expr::Lit(pb))
}

/// `p_container IN (..)` of arm `a`.
pub open spec fn conts_pred(a: int) -> Pred {
    or(or(or(text_eq(22, cont_lit(a, 0)), text_eq(22, cont_lit(a, 1))), text_eq(22, cont_lit(a, 2))), text_eq(22, cont_lit(a, 3)))
}

/// An int4 expression cast to numeric.
pub open spec fn ncast(e: Expr) -> Expr {
    Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(e) }
}

/// `$q + 10` (int4).
pub open spec fn add10(pq: Literal) -> Expr {
    Expr::Arith { op: ArithOp::Add, kind: NumKind::Int4, a: Box::new(Expr::Lit(pq)), b: Box::new(Expr::Lit(int4(10))) }
}

/// `l_quantity >= $q`.
pub open spec fn qge_pred(pq: Literal) -> Pred {
    cmp(CmpOp::Ge, Expr::Col(4), ncast(Expr::Lit(pq)))
}

/// `l_quantity <= $q + 10`.
pub open spec fn qle_pred(pq: Literal) -> Pred {
    cmp(CmpOp::Le, Expr::Col(4), ncast(add10(pq)))
}

/// `p_size BETWEEN 1 AND smax`.
pub open spec fn size_pred(a: int) -> Pred {
    and(cmp(CmpOp::Ge, Expr::Col(21), Expr::Lit(int4(1))), cmp(CmpOp::Le, Expr::Col(21), Expr::Lit(int4(smax(a)))))
}

/// `l_shipmode IN ('AIR', 'AIR REG')`.
pub open spec fn mode_pred() -> Pred {
    or(text_eq(14, air()), text_eq(14, air_reg()))
}

/// `l_shipinstruct = 'DELIVER IN PERSON'`.
pub open spec fn instr_pred() -> Pred {
    text_eq(13, dip())
}

/// The arm's conjunction up to `l_quantity >= $q`.
pub open spec fn head_pred(ps: Seq<Literal>, a: int) -> Pred {
    and(and(and(key_pred(), brand_pred(ps[2 * a])), conts_pred(a)), qge_pred(ps[2 * a + 1]))
}

/// Arm `a` (nodes n75, n143, n212).
pub open spec fn arm_pred(ps: Seq<Literal>, a: int) -> Pred {
    and(and(and(and(head_pred(ps, a), qle_pred(ps[2 * a + 1])), size_pred(a)), mode_pred()), instr_pred())
}

/// The WHERE condition (n213).
pub open spec fn pred_q(ps: Seq<Literal>) -> Pred {
    or(or(arm_pred(ps, 0), arm_pred(ps, 1)), arm_pred(ps, 2))
}

/// `1 - l_discount` (n5).
pub open spec fn one_minus_disc() -> Expr {
    Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(ncast(Expr::Lit(int4(1)))), b: Box::new(Expr::Col(6)) }
}

/// `l_extendedprice * (1 - l_discount)` (n6).
pub open spec fn val_expr() -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Col(5)), b: Box::new(one_minus_disc()) }
}

/// The aggregate `SUM(..)` (n7).
pub open spec fn sum_agg() -> Agg {
    Agg::Sum { kind: NumKind::Numeric, arg: val_expr() }
}

/// The FROM product (n216).
pub open spec fn product_q() -> Query {
    Query::Product { left: Box::new(Query::Table(0)), right: Box::new(Query::Table(3)) }
}

/// The filtered product (n217).
pub open spec fn filter_q(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: pred_q(ps), input: Box::new(product_q()) }
}

/// The aggregate (n218), the statement's body.
pub open spec fn agg_q(ps: Seq<Literal>) -> Query {
    Query::Aggregate { aggs: seq![sum_agg()], input: Box::new(filter_q(ps)) }
}

/// The statement: the aggregate, without ORDER BY, OFFSET or LIMIT.
pub proof fn lemma_ast(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == agg_q(ps),
        query_spec_at(ps).keys.len() == 0,
        query_spec_at(ps).offset == 0,
        query_spec_at(ps).limit is None,
{
    assert(query_spec_at(ps).keys =~= Seq::<OrderKey>::empty());
    assert(query_spec_at(ps).body == agg_q(ps));
}

// ------------------------------------------------------------------------------------------------ typed rows

/// Columns of the ten query values of a product row.
pub open spec fn c10() -> Seq<nat> {
    seq![1nat, 4nat, 5nat, 6nat, 13nat, 14nat, 16nat, 19nat, 21nat, 22nat]
}

/// The ten query values of a product row.
pub open spec fn zx(x: Row) -> Row {
    proj(x, c10())
}

/// The typing facts the condition and the argument need of a product row.
pub open spec fn xrow_typed(x: Row) -> bool {
    &&& x.len() == 25
    &&& int8v(x[1]) && int8v(x[16]) && int8v(x[21])
    &&& num2(x[4]) && num2(x[5]) && num2(x[6])
    &&& textv(x[13]) && textv(x[14]) && textv(x[19]) && textv(x[22])
}

/// The query values of a product row.
pub proof fn lemma_zx(x: Row)
    requires x.len() == 25,
    ensures
        zx(x).len() == 10,
        zx(x)[0] == x[1], zx(x)[1] == x[4], zx(x)[2] == x[5], zx(x)[3] == x[6], zx(x)[4] == x[13], zx(x)[5] == x[14],
        zx(x)[6] == x[16], zx(x)[7] == x[19], zx(x)[8] == x[21], zx(x)[9] == x[22],
{
}

/// A text parameter (`$1`, `$3`, `$5`) and an integer parameter (`$2`, `$4`, `$6`) of a binding in the domain.
pub proof fn lemma_params(ps: Seq<Literal>, a: int)
    requires param_domain(ps), 0 <= a < 3,
    ensures
        ps[2 * a] == Literal::Text(brand_p(ps, a)),
        ps[2 * a + 1] == int4(qty_p(ps, a)),
        int_in_range(IntKind::Int4, qty_p(ps, a)),
{
    if a == 0 {
    } else if a == 1 {
    } else {
    }
}

// ------------------------------------------------------------------------------------------------ evaluation steps

/// An int4 literal in range is its value.
proof fn lemma_eval_int4(db: Database, env: Row, v: int)
    requires int_in_range(IntKind::Int4, v),
    ensures eval_expr(db, env, Expr::Lit(int4(v))) == Ok::<Val, SqlError>(Val::Int(v)),
{
}

/// A cast to numeric of an integer.
proof fn lemma_ncast(db: Database, env: Row, e: Expr, v: int)
    requires eval_expr(db, env, e) == Ok::<Val, SqlError>(Val::Int(v)),
    ensures eval_expr(db, env, ncast(e)) == Ok::<Val, SqlError>(Val::Num { coeff: v, scale: 0 }),
{
}

/// A cast to numeric of an error is that error.
proof fn lemma_ncast_err(db: Database, env: Row, e: Expr, err: SqlError)
    requires eval_expr(db, env, e) == Err::<Val, SqlError>(err),
    ensures eval_expr(db, env, ncast(e)) == Err::<Val, SqlError>(err),
{
}

/// `$q + 10` is the int4 result of the sum.
proof fn lemma_add10(db: Database, env: Row, v: int)
    requires int_in_range(IntKind::Int4, v),
    ensures eval_expr(db, env, add10(int4(v))) == int_result(IntKind::Int4, v + 10),
{
    lemma_eval_int4(db, env, v);
    assert(int_in_range(IntKind::Int4, 10));
    lemma_eval_int4(db, env, 10);
}

/// A comparison whose right operand errs (the left succeeding) is that error.
proof fn lemma_cmp_err(db: Database, env: Row, op: CmpOp, a: Expr, b: Expr, e: SqlError)
    requires eval_expr(db, env, a) is Ok, eval_expr(db, env, b) == Err::<Val, SqlError>(e),
    ensures eval_pred(db, env, cmp(op, a, b)) == Err::<Truth, SqlError>(e),
{
}

/// `AND` with an erring left operand.
proof fn lemma_and_err_l(db: Database, env: Row, a: Pred, b: Pred, e: SqlError)
    requires eval_pred(db, env, a) == Err::<Truth, SqlError>(e),
    ensures eval_pred(db, env, and(a, b)) == Err::<Truth, SqlError>(e),
{
}

/// `AND` with a succeeding left and an erring right operand.
proof fn lemma_and_err_r(db: Database, env: Row, a: Pred, b: Pred, e: SqlError)
    requires eval_pred(db, env, a) is Ok, eval_pred(db, env, b) == Err::<Truth, SqlError>(e),
    ensures eval_pred(db, env, and(a, b)) == Err::<Truth, SqlError>(e),
{
}

/// `OR` with an erring left operand.
proof fn lemma_or_err_l(db: Database, env: Row, a: Pred, b: Pred, e: SqlError)
    requires eval_pred(db, env, a) == Err::<Truth, SqlError>(e),
    ensures eval_pred(db, env, or(a, b)) == Err::<Truth, SqlError>(e),
{
}

/// `OR` with a succeeding left and an erring right operand.
proof fn lemma_or_err_r(db: Database, env: Row, a: Pred, b: Pred, e: SqlError)
    requires eval_pred(db, env, a) is Ok, eval_pred(db, env, b) == Err::<Truth, SqlError>(e),
    ensures eval_pred(db, env, or(a, b)) == Err::<Truth, SqlError>(e),
{
}

/// `col = 'text'` on a text column.
proof fn lemma_text_eq(db: Database, x: Row, c: nat, t: Seq<u8>)
    requires c < x.len(), textv(x[c as int]),
    ensures eval_pred(db, x, text_eq(c, t)) == Ok::<Truth, SqlError>(truth_of(tval(x[c as int]) == t)),
{
    lemma_expr_col(db, x, c);
    lemma_expr_text(db, x, t);
    lemma_pred_text_cmp(db, x, CmpOp::Eq, Expr::Col(c), Expr::Lit(Literal::Text(t)), tval(x[c as int]), t);
}

pub proof fn lemma_pow10_values()
    ensures pow10(0) == 1, pow10(1) == 10, pow10(2) == 100, pow10(15) == super::model::p15(), pow10(17) == 100 * super::model::p15(),
{
    assert(pow10(17) == 100 * super::model::p15()) by (compute);
    assert(pow10(15) == super::model::p15()) by (compute);
    assert(pow10(2) == 100) by (compute);
    assert(pow10(1) == 10) by (compute);
    assert(pow10(0) == 1) by (compute);
}

/// A quantity (scale 2) against an integer cast to numeric: the order of `q` and `100 v`.
proof fn lemma_qty_cmp(db: Database, x: Row, op: CmpOp, e: Expr, v: int)
    requires
        x.len() == 25,
        num2(x[4]),
        eval_expr(db, x, ncast(e)) == Ok::<Val, SqlError>(Val::Num { coeff: v, scale: 0 }),
    ensures eval_pred(db, x, cmp(op, Expr::Col(4), ncast(e))) == Ok::<Truth, SqlError>(truth_of(int_cmp(op, ival(x[4]), 100 * v))),
{
    let q = ival(x[4]);
    lemma_expr_col(db, x, 4);
    lemma_compare_num(q, 2, v, 0);
    lemma_pow10_values();
    lemma_align_same(q, 2);
    lemma_align_by(v, 0, 2, 100);
    assert(max_nat(2, 0) == 2);
    lemma_pred_cmp(db, x, op, Expr::Col(4), ncast(e), x[4], Val::Num { coeff: v, scale: 0 }, q, 100 * v);
}

// ------------------------------------------------------------------------------------------------ one arm

/// The arm's head (`p_partkey = l_partkey AND p_brand = $b AND p_container IN (..) AND l_quantity >= $q`) on a
/// typed row: two-valued.
proof fn lemma_head(db: Database, x: Row, ps: Seq<Literal>, a: int)
    requires param_domain(ps), 0 <= a < 3, xrow_typed(x),
    ensures
        eval_pred(db, x, head_pred(ps, a)) == Ok::<Truth, SqlError>(truth_of(
            ival(x[16]) == ival(x[1]) && tval(x[19]) == brand_p(ps, a) && cont_in(a, tval(x[22]))
                && ival(x[4]) >= 100 * qty_p(ps, a))),
{
    hide(eval_pred);
    hide(eval_expr);
    lemma_params(ps, a);
    let (k1, k2) = (ival(x[1]), ival(x[16]));
    // p_partkey = l_partkey
    lemma_expr_col(db, x, 16);
    lemma_expr_col(db, x, 1);
    lemma_compare_int(k2, k1);
    lemma_pred_cmp(db, x, CmpOp::Eq, Expr::Col(16), Expr::Col(1), x[16], x[1], k2, k1);
    // p_brand = $b
    lemma_expr_col(db, x, 19);
    lemma_expr_text(db, x, brand_p(ps, a));
    lemma_pred_text_cmp(db, x, CmpOp::Eq, Expr::Col(19), Expr::Lit(ps[2 * a]), tval(x[19]), brand_p(ps, a));
    lemma_pred_and(db, x, key_pred(), brand_pred(ps[2 * a]), k2 == k1, tval(x[19]) == brand_p(ps, a));
    // p_container IN (..)
    let ct = tval(x[22]);
    lemma_text_eq(db, x, 22, cont_lit(a, 0));
    lemma_text_eq(db, x, 22, cont_lit(a, 1));
    lemma_text_eq(db, x, 22, cont_lit(a, 2));
    lemma_text_eq(db, x, 22, cont_lit(a, 3));
    lemma_pred_or(db, x, text_eq(22, cont_lit(a, 0)), text_eq(22, cont_lit(a, 1)), ct == cont_lit(a, 0), ct == cont_lit(a, 1));
    lemma_pred_or(db, x, or(text_eq(22, cont_lit(a, 0)), text_eq(22, cont_lit(a, 1))), text_eq(22, cont_lit(a, 2)),
        ct == cont_lit(a, 0) || ct == cont_lit(a, 1), ct == cont_lit(a, 2));
    lemma_pred_or(db, x, or(or(text_eq(22, cont_lit(a, 0)), text_eq(22, cont_lit(a, 1))), text_eq(22, cont_lit(a, 2))),
        text_eq(22, cont_lit(a, 3)), ct == cont_lit(a, 0) || ct == cont_lit(a, 1) || ct == cont_lit(a, 2), ct == cont_lit(a, 3));
    lemma_pred_and(db, x, and(key_pred(), brand_pred(ps[2 * a])), conts_pred(a), k2 == k1 && tval(x[19]) == brand_p(ps, a),
        cont_in(a, ct));
    // l_quantity >= $q
    let v = qty_p(ps, a);
    lemma_eval_int4(db, x, v);
    lemma_ncast(db, x, Expr::Lit(int4(v)), v);
    lemma_qty_cmp(db, x, CmpOp::Ge, Expr::Lit(int4(v)), v);
    lemma_pred_and(db, x, and(and(key_pred(), brand_pred(ps[2 * a])), conts_pred(a)), qge_pred(ps[2 * a + 1]),
        k2 == k1 && tval(x[19]) == brand_p(ps, a) && cont_in(a, ct), ival(x[4]) >= 100 * v);
}

/// `$q + 10` of arm `a` leaves int4.
pub open spec fn ovf(ps: Seq<Literal>, a: int) -> bool {
    qty_p(ps, a) + 10 > int4_max()
}

/// Arm `a` on a typed row: two-valued (`arm_w`) inside int4, else the error 22003 of `$q + 10`.
pub proof fn lemma_arm(db: Database, x: Row, ps: Seq<Literal>, a: int)
    requires param_domain(ps), 0 <= a < 3, xrow_typed(x),
    ensures
        !ovf(ps, a) ==> eval_pred(db, x, arm_pred(ps, a)) == Ok::<Truth, SqlError>(truth_of(arm_w(ps, a, zx(x)))),
        ovf(ps, a) ==> eval_pred(db, x, arm_pred(ps, a)) == Err::<Truth, SqlError>(SqlError::NumericValueOutOfRange),
{
    hide(eval_pred);
    hide(eval_expr);
    lemma_params(ps, a);
    lemma_zx(x);
    lemma_head(db, x, ps, a);
    let v = qty_p(ps, a);
    let pq = ps[2 * a + 1];
    let h = ival(x[16]) == ival(x[1]) && tval(x[19]) == brand_p(ps, a) && cont_in(a, tval(x[22])) && ival(x[4]) >= 100 * v;
    lemma_add10(db, x, v);
    lemma_expr_col(db, x, 4);
    if ovf(ps, a) {
        assert(int_result(IntKind::Int4, v + 10) == Err::<Val, SqlError>(SqlError::NumericValueOutOfRange));
        lemma_ncast_err(db, x, add10(pq), SqlError::NumericValueOutOfRange);
        lemma_cmp_err(db, x, CmpOp::Le, Expr::Col(4), ncast(add10(pq)), SqlError::NumericValueOutOfRange);
        lemma_and_err_r(db, x, head_pred(ps, a), qle_pred(pq), SqlError::NumericValueOutOfRange);
        lemma_and_err_l(db, x, and(head_pred(ps, a), qle_pred(pq)), size_pred(a), SqlError::NumericValueOutOfRange);
        lemma_and_err_l(db, x, and(and(head_pred(ps, a), qle_pred(pq)), size_pred(a)), mode_pred(), SqlError::NumericValueOutOfRange);
        lemma_and_err_l(db, x, and(and(and(head_pred(ps, a), qle_pred(pq)), size_pred(a)), mode_pred()), instr_pred(),
            SqlError::NumericValueOutOfRange);
    } else {
        assert(int_result(IntKind::Int4, v + 10) == Ok::<Val, SqlError>(Val::Int(v + 10)));
        lemma_ncast(db, x, add10(pq), v + 10);
        lemma_qty_cmp(db, x, CmpOp::Le, add10(pq), v + 10);
        let le = ival(x[4]) <= 100 * (v + 10);
        lemma_pred_and(db, x, head_pred(ps, a), qle_pred(pq), h, le);
        // p_size BETWEEN 1 AND smax
        let sz = ival(x[21]);
        lemma_expr_col(db, x, 21);
        assert(int_in_range(IntKind::Int4, 1));
        assert(int_in_range(IntKind::Int4, smax(a)));
        lemma_eval_int4(db, x, 1);
        lemma_eval_int4(db, x, smax(a));
        lemma_compare_int(sz, 1);
        lemma_compare_int(sz, smax(a));
        lemma_pred_cmp(db, x, CmpOp::Ge, Expr::Col(21), Expr::Lit(int4(1)), x[21], Val::Int(1), sz, 1);
        lemma_pred_cmp(db, x, CmpOp::Le, Expr::Col(21), Expr::Lit(int4(smax(a))), x[21], Val::Int(smax(a)), sz, smax(a));
        lemma_pred_and(db, x, cmp(CmpOp::Ge, Expr::Col(21), Expr::Lit(int4(1))), cmp(CmpOp::Le, Expr::Col(21), Expr::Lit(int4(smax(a)))),
            sz >= 1, sz <= smax(a));
        lemma_pred_and(db, x, and(head_pred(ps, a), qle_pred(pq)), size_pred(a), h && le, sz >= 1 && sz <= smax(a));
        // l_shipmode IN ('AIR', 'AIR REG')
        let sm = tval(x[14]);
        lemma_text_eq(db, x, 14, air());
        lemma_text_eq(db, x, 14, air_reg());
        lemma_pred_or(db, x, text_eq(14, air()), text_eq(14, air_reg()), sm == air(), sm == air_reg());
        lemma_pred_and(db, x, and(and(head_pred(ps, a), qle_pred(pq)), size_pred(a)), mode_pred(),
            h && le && sz >= 1 && sz <= smax(a), mode_in(sm));
        // l_shipinstruct = 'DELIVER IN PERSON'
        let si = tval(x[13]);
        lemma_text_eq(db, x, 13, dip());
        lemma_pred_and(db, x, and(and(and(head_pred(ps, a), qle_pred(pq)), size_pred(a)), mode_pred()), instr_pred(),
            h && le && sz >= 1 && sz <= smax(a) && mode_in(sm), si == dip());
    }
}

/// The WHERE condition on a typed row, every `$q + 10` inside int4: `wq` of its query values.
pub proof fn lemma_row_pred(db: Database, x: Row, ps: Seq<Literal>)
    requires param_domain(ps), xrow_typed(x), !ovf(ps, 0), !ovf(ps, 1), !ovf(ps, 2),
    ensures eval_pred(db, x, pred_q(ps)) == Ok::<Truth, SqlError>(truth_of(wq(ps, zx(x)))),
{
    hide(eval_pred);
    let w = zx(x);
    lemma_arm(db, x, ps, 0);
    lemma_arm(db, x, ps, 1);
    lemma_arm(db, x, ps, 2);
    lemma_pred_or(db, x, arm_pred(ps, 0), arm_pred(ps, 1), arm_w(ps, 0, w), arm_w(ps, 1, w));
    lemma_pred_or(db, x, or(arm_pred(ps, 0), arm_pred(ps, 1)), arm_pred(ps, 2), arm_w(ps, 0, w) || arm_w(ps, 1, w), arm_w(ps, 2, w));
}

/// The WHERE condition on a typed row, some `$q + 10` outside int4: the error 22003.
pub proof fn lemma_row_pred_err(db: Database, x: Row, ps: Seq<Literal>)
    requires param_domain(ps), xrow_typed(x), ovf(ps, 0) || ovf(ps, 1) || ovf(ps, 2),
    ensures eval_pred(db, x, pred_q(ps)) == Err::<Truth, SqlError>(SqlError::NumericValueOutOfRange),
{
    hide(eval_pred);
    let e = SqlError::NumericValueOutOfRange;
    lemma_arm(db, x, ps, 0);
    lemma_arm(db, x, ps, 1);
    lemma_arm(db, x, ps, 2);
    if ovf(ps, 0) {
        lemma_or_err_l(db, x, arm_pred(ps, 0), arm_pred(ps, 1), e);
        lemma_or_err_l(db, x, or(arm_pred(ps, 0), arm_pred(ps, 1)), arm_pred(ps, 2), e);
    } else if ovf(ps, 1) {
        lemma_or_err_r(db, x, arm_pred(ps, 0), arm_pred(ps, 1), e);
        lemma_or_err_l(db, x, or(arm_pred(ps, 0), arm_pred(ps, 1)), arm_pred(ps, 2), e);
    } else {
        lemma_pred_or(db, x, arm_pred(ps, 0), arm_pred(ps, 1), arm_w(ps, 0, zx(x)), arm_w(ps, 1, zx(x)));
        lemma_or_err_r(db, x, or(arm_pred(ps, 0), arm_pred(ps, 1)), arm_pred(ps, 2), e);
    }
}

// ------------------------------------------------------------------------------------------------ the argument

/// The SUM argument of a typed row: the value as a numeric of scale 4.
pub open spec fn xv(x: Row) -> Val {
    Val::Num { coeff: wv(zx(x)), scale: 4 }
}

/// `l_extendedprice * (1 - l_discount)` on a typed row.
pub proof fn lemma_val_eval(db: Database, x: Row)
    requires xrow_typed(x),
    ensures eval_expr(db, x, val_expr()) == Ok::<Val, SqlError>(xv(x)),
{
    hide(eval_expr);
    lemma_zx(x);
    lemma_pow10_values();
    let (p, d) = (ival(x[5]), ival(x[6]));
    lemma_expr_col(db, x, 5);
    lemma_expr_col(db, x, 6);
    let one = ncast(Expr::Lit(int4(1)));
    assert(int_in_range(IntKind::Int4, 1));
    lemma_eval_int4(db, x, 1);
    lemma_ncast(db, x, Expr::Lit(int4(1)), 1);
    // 1 - d at scale 2
    lemma_node_add(db, x, ArithOp::Sub, one, Expr::Col(6), 1, 0, 1, d, 2, 15, 2, 100, 1, 17);
    assert(1 * 100 - d * 1 == 100 - d);
    // p * (100 - d) at scale 4
    lemma_node_mul(db, x, Expr::Col(5), one_minus_disc(), p, 2, 15, 100 - d, 2, 17);
}

/// The aggregate arguments of a typed row.
pub proof fn lemma_row_arg(db: Database, x: Row)
    requires xrow_typed(x),
    ensures agg_args(db, x, seq![sum_agg()]) == Ok::<Row, SqlError>(seq![xv(x)]),
{
    hide(eval_expr);
    hide(agg_arg);
    lemma_val_eval(db, x);
    lemma_agg_arg_sum(db, x, NumKind::Numeric, val_expr());
    let aggs = seq![sum_agg()];
    let rs = agg_arg_results(db, x, aggs);
    lemma_agg_arg_results_index(db, x, aggs);
    let vs = seq![xv(x)];
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Val, SqlError>(vs[i]) by {
        assert(rs[i] == agg_arg(db, x, aggs[i]));
    }
    lemma_collect_all(rs, vs);
}

} // verus!
