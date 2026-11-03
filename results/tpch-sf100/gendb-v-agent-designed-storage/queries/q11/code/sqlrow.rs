//! The statement's AST in named pieces (`lemma_query_shape`: `query.rs`'s `query_spec_at(ps)` is exactly these
//! pieces) and what each piece evaluates to on one joined row.
//!
//! A joined row `x` of `partsupp x supplier x nation` has 16 values: partsupp at 0..5, supplier at 5..12, nation at
//! 12..16. The outer query reads it directly (WHERE `where_p`, key `Col(0)`, argument of `sum_agg`); the HAVING
//! subquery reads it behind the group row `w` (2 values), so its copies `where_s` / `sum_agg_s` name every column
//! two positions later. `lemma_where_shift` / `lemma_args_shift` show the copies evaluate on `w + x` exactly as the
//! originals on `x`, whatever `w`'s values.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::scalar::*;
use crate::spec::numeric::{abs, pow10};
use crate::spec::relation::{collect, product_rows};
use crate::spec::limits::numeric_int_digits_max;
use crate::link::expr::{ival, lemma_pred_cmp, lemma_pred_text_cmp, lemma_pred_and, lemma_compare_int, int_cmp, text_cmp};
use crate::link::query::{QuerySpec, arg_vals, lemma_node_mul};
use crate::link::join::lemma_product_index;
use crate::query::query_spec_at;
use super::nf::*;
use super::tables::Tabs;

verus! {

// ------------------------------------------------------------------------------------------------ the pieces

pub open spec fn col(i: nat) -> Expr {
    Expr::Col(i)
}

pub open spec fn eq_p(a: nat, b: nat) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(a), b: Expr::Col(b) }
}

/// `FROM partsupp, supplier, nation`.
pub open spec fn prod_q() -> Query {
    Query::Product {
        left: Box::new(Query::Product { left: Box::new(Query::Table(4)), right: Box::new(Query::Table(5)) }),
        right: Box::new(Query::Table(6)),
    }
}

/// The WHERE condition with its columns starting at `d` (0: the outer query, 2: the HAVING subquery).
pub open spec fn where_at(d: nat, lit: Literal) -> Pred {
    Pred::And(
        Box::new(Pred::And(Box::new(eq_p(1 + d, 5 + d)), Box::new(eq_p(8 + d, 12 + d)))),
        Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(13 + d), b: Expr::Lit(lit) }),
    )
}

/// `ps_supplycost * ps_availqty` with its columns starting at `d`.
pub open spec fn arg_at(d: nat) -> Expr {
    Expr::Arith {
        op: ArithOp::Mul,
        kind: NumKind::Numeric,
        a: Box::new(Expr::Col(3 + d)),
        b: Box::new(Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Col(2 + d)) }),
    }
}

pub open spec fn sum_at(d: nat) -> Agg {
    Agg::Sum { kind: NumKind::Numeric, arg: arg_at(d) }
}

/// The WHERE filter of the outer query.
pub open spec fn where_q(lit: Literal) -> Query {
    Query::Filter { pred: where_at(0, lit), input: Box::new(prod_q()) }
}

/// The GROUP BY of the outer query.
pub open spec fn group_q(lit: Literal) -> Query {
    Query::GroupBy { keys: seq![Expr::Col(0)], aggs: seq![sum_at(0)], input: Box::new(where_q(lit)) }
}

/// The subquery's aggregate (columns behind the 2-value group row).
pub open spec fn agg_s(lit: Literal) -> Query {
    Query::Aggregate { aggs: seq![sum_at(2)], input: Box::new(Query::Filter { pred: where_at(2, lit), input: Box::new(prod_q()) }) }
}

/// The same aggregate at the top level (no outer row): what `agg_s` evaluates to.
pub open spec fn agg_0(lit: Literal) -> Query {
    Query::Aggregate { aggs: seq![sum_at(0)], input: Box::new(where_q(lit)) }
}

/// `SUM(..) * $2`: column 2 of `group row ++ aggregate row`.
pub open spec fn mul_e(p: Literal) -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Col(2)), b: Box::new(Expr::Lit(p)) }
}

pub open spec fn sub_q(lit: Literal, p: Literal) -> Query {
    Query::Project { exprs: seq![mul_e(p)], input: Box::new(agg_s(lit)) }
}

/// The HAVING condition on a group row.
pub open spec fn having_p(lit: Literal, p: Literal) -> Pred {
    Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(1), b: Expr::Subquery(Box::new(sub_q(lit, p))) }
}

pub open spec fn body_q(lit: Literal, p: Literal) -> Query {
    Query::Filter { pred: having_p(lit, p), input: Box::new(group_q(lit)) }
}

pub open spec fn order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 1, desc: true, nulls_first: true }]
}

/// `query.rs`'s statement is the named pieces.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == body_q(ps[0], ps[1]),
        query_spec_at(ps).keys == order_keys(),
        query_spec_at(ps).limit is None,
        query_spec_at(ps).offset == 0,
{
}

// ------------------------------------------------------------------------------------------------ joined rows

/// A joined row of typed partsupp, supplier and nation rows (the values the conditions and the argument read).
pub open spec fn x_typed(x: Row) -> bool {
    &&& x.len() == 16
    &&& x[0] is Int && x[1] is Int && x[2] is Int
    &&& i64::MIN <= ival(x[0]) <= i64::MAX
    &&& i64::MIN <= ival(x[2]) <= i64::MAX
    &&& x[3] is Num && x[3]->scale == 2
    &&& abs(ival(x[3])) < pow10(15)
    &&& x[5] is Int && x[8] is Int && x[12] is Int
    &&& x[13] is Text
}

/// Every joined row is typed.
pub proof fn lemma_xs_typed(t: Tabs)
    requires tabs_typed(t),
    ensures forall|i: int| 0 <= i < xs(t).len() ==> #[trigger] x_typed(xs(t)[i]),
{
    let ab = product_rows(t.ps, t.s);
    lemma_product_index(t.ps, t.s);
    lemma_product_index(ab, t.n);
    assert forall|i: int| 0 <= i < xs(t).len() implies #[trigger] x_typed(xs(t)[i]) by {
        let nl = t.n.len() as int;
        let sl = t.s.len() as int;
        assert(nl > 0) by (nonlinear_arith) requires xs(t).len() == ab.len() * nl, 0 <= i < xs(t).len(), ab.len() >= 0;
        let u = i / nl;
        let q = i % nl;
        assert(0 <= u < ab.len() && 0 <= q < nl && i == u * nl + q) by (nonlinear_arith)
            requires xs(t).len() == ab.len() * nl, 0 <= i < xs(t).len(), nl > 0, u == i / nl, q == i % nl;
        assert(xs(t)[i] == ab[u] + t.n[q]);
        assert(sl > 0) by (nonlinear_arith) requires ab.len() == t.ps.len() * sl, 0 <= u < ab.len(), t.ps.len() >= 0;
        let k = u / sl;
        let j = u % sl;
        assert(0 <= k < t.ps.len() && 0 <= j < sl && u == k * sl + j) by (nonlinear_arith)
            requires ab.len() == t.ps.len() * sl, 0 <= u < ab.len(), sl > 0, k == u / sl, j == u % sl;
        assert(ab[u] == t.ps[k] + t.s[j]);
        assert(ps_typed(t.ps[k]));
        assert(s_typed(t.s[j]));
        assert(n_typed(t.n[q]));
        let x = xs(t)[i];
        assert(x == (t.ps[k] + t.s[j]) + t.n[q]);
        assert(x[0] == t.ps[k][0] && x[1] == t.ps[k][1] && x[2] == t.ps[k][2] && x[3] == t.ps[k][3]);
        assert(x[5] == t.s[j][0] && x[8] == t.s[j][3] && x[12] == t.n[q][0] && x[13] == t.n[q][1]);
    }
}

/// Every joined row has 16 values.
pub proof fn lemma_xs_width(t: Tabs)
    requires tabs_typed(t),
    ensures forall|i: int| 0 <= i < xs(t).len() ==> (#[trigger] xs(t)[i]).len() == 16,
{
    lemma_xs_typed(t);
    assert forall|i: int| 0 <= i < xs(t).len() implies (#[trigger] xs(t)[i]).len() == 16 by {
        assert(x_typed(xs(t)[i]));
    }
}

// ------------------------------------------------------------------------------------------------ per-row values

/// Equality of two integer columns of a typed row.
proof fn lemma_eq_int(db: Database, env: Row, a: nat, b: nat)
    requires a < env.len(), b < env.len(), env[a as int] is Int, env[b as int] is Int,
    ensures eval_pred(db, env, eq_p(a, b)) == Ok::<Truth, SqlError>(truth_of(env[a as int] == env[b as int])),
{
    let (va, vb) = (env[a as int], env[b as int]);
    lemma_compare_int(ival(va), ival(vb));
    lemma_pred_cmp(db, env, CmpOp::Eq, Expr::Col(a), Expr::Col(b), va, vb, ival(va), ival(vb));
}

/// The WHERE condition on a typed joined row.
pub proof fn lemma_where_row(db: Database, x: Row, name: Seq<u8>)
    requires x_typed(x),
    ensures eval_pred(db, x, where_at(0, Literal::Text(name))) == Ok::<Truth, SqlError>(truth_of(qualx(name, x))),
{
    lemma_eq_int(db, x, 1, 5);
    lemma_eq_int(db, x, 8, 12);
    let nm = x[13]->Text_0;
    assert(eval_expr(db, x, Expr::Lit(Literal::Text(name))) == Ok::<Val, SqlError>(Val::Text(name)));
    lemma_pred_text_cmp(db, x, CmpOp::Eq, Expr::Col(13), Expr::Lit(Literal::Text(name)), nm, name);
    let p1 = Pred::And(Box::new(eq_p(1, 5)), Box::new(eq_p(8, 12)));
    lemma_pred_and(db, x, eq_p(1, 5), eq_p(8, 12), x[1] == x[5], x[8] == x[12]);
    lemma_pred_and(db, x, p1, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(13), b: Expr::Lit(Literal::Text(name)) },
        x[1] == x[5] && x[8] == x[12], text_cmp(CmpOp::Eq, nm, name));
    assert(text_cmp(CmpOp::Eq, nm, name) == (x[13] == Val::Text(name)));
}

/// A column two positions later behind a 2-value row reads the same value.
proof fn lemma_col_shift(db: Database, w: Row, x: Row, i: nat)
    requires w.len() == 2, i < x.len(),
    ensures eval_expr(db, w + x, Expr::Col(i + 2)) == eval_expr(db, x, Expr::Col(i)),
{
    assert((w + x)[i + 2int] == x[i as int]);
}

/// A comparison whose operands evaluate alike in two environments evaluates alike.
proof fn lemma_cmp_same(db: Database, e1: Row, e2: Row, op: CmpOp, a1: Expr, b1: Expr, a2: Expr, b2: Expr)
    requires eval_expr(db, e1, a1) == eval_expr(db, e2, a2), eval_expr(db, e1, b1) == eval_expr(db, e2, b2),
    ensures eval_pred(db, e1, Pred::Cmp { op, a: a1, b: b1 }) == eval_pred(db, e2, Pred::Cmp { op, a: a2, b: b2 }),
{
    hide(eval_query);
    reveal_with_fuel(eval_pred, 1);
}

/// A literal has one value in every environment.
proof fn lemma_lit_same(db: Database, e1: Row, e2: Row, l: Literal)
    ensures eval_expr(db, e1, Expr::Lit(l)) == eval_expr(db, e2, Expr::Lit(l)),
{
}

/// A conjunction whose operands evaluate alike in two environments evaluates alike.
proof fn lemma_and_same(db: Database, e1: Row, e2: Row, a1: Pred, b1: Pred, a2: Pred, b2: Pred)
    requires eval_pred(db, e1, a1) == eval_pred(db, e2, a2), eval_pred(db, e1, b1) == eval_pred(db, e2, b2),
    ensures eval_pred(db, e1, Pred::And(Box::new(a1), Box::new(b1))) == eval_pred(db, e2, Pred::And(Box::new(a2), Box::new(b2))),
{
    hide(eval_expr);
    hide(eval_query);
}

/// The subquery's WHERE copy on `w + x` is the outer WHERE on `x`.
pub proof fn lemma_where_shift(db: Database, w: Row, x: Row, lit: Literal)
    requires w.len() == 2, x.len() == 16,
    ensures eval_pred(db, w + x, where_at(2, lit)) == eval_pred(db, x, where_at(0, lit)),
{
    hide(eval_pred);
    hide(eval_expr);
    lemma_col_shift(db, w, x, 1);
    lemma_col_shift(db, w, x, 5);
    lemma_col_shift(db, w, x, 8);
    lemma_col_shift(db, w, x, 12);
    lemma_col_shift(db, w, x, 13);
    lemma_lit_same(db, w + x, x, lit);
    lemma_cmp_same(db, w + x, x, CmpOp::Eq, Expr::Col(3), Expr::Col(7), Expr::Col(1), Expr::Col(5));
    lemma_cmp_same(db, w + x, x, CmpOp::Eq, Expr::Col(10), Expr::Col(14), Expr::Col(8), Expr::Col(12));
    lemma_cmp_same(db, w + x, x, CmpOp::Eq, Expr::Col(15), Expr::Lit(lit), Expr::Col(13), Expr::Lit(lit));
    lemma_and_same(db, w + x, x, eq_p(3, 7), eq_p(10, 14), eq_p(1, 5), eq_p(8, 12));
    let a2 = Pred::And(Box::new(eq_p(3, 7)), Box::new(eq_p(10, 14)));
    let a0 = Pred::And(Box::new(eq_p(1, 5)), Box::new(eq_p(8, 12)));
    lemma_and_same(db, w + x, x, a2, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(15), b: Expr::Lit(lit) },
        a0, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(13), b: Expr::Lit(lit) });
}

/// A cast whose argument evaluates alike evaluates alike.
proof fn lemma_cast_same(db: Database, e1: Row, e2: Row, c: CastOp, a1: Expr, a2: Expr)
    requires eval_expr(db, e1, a1) == eval_expr(db, e2, a2),
    ensures eval_expr(db, e1, Expr::Cast { cast: c, arg: Box::new(a1) }) == eval_expr(db, e2, Expr::Cast { cast: c, arg: Box::new(a2) }),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_exprs);
}

/// An arithmetic node whose operands evaluate alike evaluates alike.
proof fn lemma_arith_same(db: Database, e1: Row, e2: Row, op: ArithOp, k: NumKind, a1: Expr, b1: Expr, a2: Expr, b2: Expr)
    requires eval_expr(db, e1, a1) == eval_expr(db, e2, a2), eval_expr(db, e1, b1) == eval_expr(db, e2, b2),
    ensures
        eval_expr(db, e1, Expr::Arith { op, kind: k, a: Box::new(a1), b: Box::new(b1) })
            == eval_expr(db, e2, Expr::Arith { op, kind: k, a: Box::new(a2), b: Box::new(b2) }),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_exprs);
}

/// The subquery's argument copy on `w + x` is the outer argument on `x`.
pub proof fn lemma_arg_shift(db: Database, w: Row, x: Row)
    requires w.len() == 2, x.len() == 16,
    ensures eval_expr(db, w + x, arg_at(2)) == eval_expr(db, x, arg_at(0)),
{
    hide(eval_expr);
    lemma_col_shift(db, w, x, 2);
    lemma_col_shift(db, w, x, 3);
    lemma_cast_same(db, w + x, x, CastOp::IntToNumeric, Expr::Col(4), Expr::Col(2));
    let c2 = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Col(4)) };
    let c0 = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Col(2)) };
    lemma_arith_same(db, w + x, x, ArithOp::Mul, NumKind::Numeric, Expr::Col(5), c2, Expr::Col(3), c0);
}

/// The cast of the availqty column on a typed joined row.
proof fn lemma_cast_row(db: Database, x: Row)
    requires x_typed(x),
    ensures
        eval_expr(db, x, Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Col(2)) })
            == Ok::<Val, SqlError>(Val::Num { coeff: ival(x[2]), scale: 0 }),
{
    hide(eval_query);
    hide(eval_pred);
    hide(eval_exprs);
    assert(eval_expr(db, x, Expr::Col(2)) == Ok::<Val, SqlError>(x[2]));
}

/// The argument on a typed joined row: the coefficient `argx(x)` at scale 2.
pub proof fn lemma_arg_row(db: Database, x: Row)
    requires x_typed(x),
    ensures
        eval_expr(db, x, arg_at(0)) == Ok::<Val, SqlError>(Val::Num { coeff: argx(x), scale: 2 }),
        abs(argx(x)) < pow10(34),
{
    hide(eval_expr);
    let c = ival(x[3]);
    let q = ival(x[2]);
    let cast_e = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Col(2)) };
    lemma_cast_row(db, x);
    crate::link::expr::lemma_expr_col(db, x, 3);
    assert(eval_expr(db, x, Expr::Col(3)) == Ok::<Val, SqlError>(Val::Num { coeff: c, scale: 2 }));
    assert(abs(q) < pow10(19)) by {
        assert(pow10(19) == 10000000000000000000) by (compute);
    }
    assert(numeric_int_digits_max() == 131072);
    lemma_node_mul(db, x, Expr::Col(3), cast_e, c, 2, 15, q, 0, 19);
}

/// The aggregate arguments of the outer SUM on a typed joined row.
pub proof fn lemma_args_row(db: Database, x: Row, g: QuerySpec)
    requires
        x_typed(x),
        g.aggs == seq![crate::link::query::AggKind::Sum { scale: 2 }],
        (g.arg)(0, x) == argx(x),
    ensures agg_args(db, x, seq![sum_at(0)]) == Ok::<Row, SqlError>(arg_vals(g, x)),
{
    lemma_arg_row(db, x);
    let aggs = seq![sum_at(0)];
    lemma_agg_arg_results_index(db, x, aggs);
    let rs = agg_arg_results(db, x, aggs);
    assert(rs[0] == eval_expr(db, x, arg_at(0)));
    crate::bridge::collect::lemma_collect_all(rs, arg_vals(g, x));
}

/// The aggregate arguments of the subquery's SUM copy on `w + x` are the outer ones on `x`.
pub proof fn lemma_args_shift(db: Database, w: Row, x: Row)
    requires w.len() == 2, x.len() == 16,
    ensures agg_args(db, w + x, seq![sum_at(2)]) == agg_args(db, x, seq![sum_at(0)]),
{
    lemma_arg_shift(db, w, x);
    let a2 = seq![sum_at(2)];
    let a0 = seq![sum_at(0)];
    lemma_agg_arg_results_index(db, w + x, a2);
    lemma_agg_arg_results_index(db, x, a0);
    assert(agg_arg_results(db, w + x, a2) =~= agg_arg_results(db, x, a0));
}

/// The group key on a joined row.
pub proof fn lemma_key_row(db: Database, x: Row)
    requires x.len() > 0,
    ensures eval_exprs(db, x, seq![Expr::Col(0)]) == Ok::<Row, SqlError>(seq![x[0]]),
{
    let es = seq![Expr::Col(0)];
    lemma_expr_results_index(db, x, es);
    crate::bridge::collect::lemma_collect_all(expr_results(db, x, es), seq![x[0]]);
}

} // verus!
