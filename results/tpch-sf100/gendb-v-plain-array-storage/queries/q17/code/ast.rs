//! The statement's AST (`query::query_spec_at`) cut into named sub-trees, bottom-up:
//!
//! - `q_from`: `FROM lineitem, part`, the product of the tables 0 and 3 (joined rows of 16 + 9 = 25 values;
//!   `l_partkey` at 1, `l_quantity` at 4, `l_extendedprice` at 5, `p_partkey` at 16, `p_brand` at 19,
//!   `p_container` at 22);
//! - `sub_q`: the correlated scalar subquery `SELECT 0.2 * AVG(l_quantity) FROM lineitem WHERE l_partkey =
//!   p_partkey`, evaluated with the joined row as context (its inner lineitem row follows at 25..41: inner
//!   `l_partkey` at 26, inner `l_quantity` at 29; the aggregate row follows the context at 25);
//! - `q_pred`: `p_partkey = l_partkey AND p_brand = $1 AND p_container = $2 AND l_quantity < (sub_q)`;
//! - `q_agg`: `SUM(l_extendedprice)` over the kept joined rows;
//! - `q_body`: `SELECT sum / 7.0` over the one aggregate row.
//!
//! `lemma_query_shape` states that `query_spec_at(ps)` is exactly this tree, unordered, without LIMIT or OFFSET.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::query::query_spec_at;

verus! {

pub open spec fn and(a: Pred, b: Pred) -> Pred {
    Pred::And(Box::new(a), Box::new(b))
}

/// FROM: `lineitem x part`.
pub open spec fn q_from() -> Query {
    Query::Product { left: Box::new(Query::Table(0)), right: Box::new(Query::Table(3)) }
}

/// `p_partkey = l_partkey`.
pub open spec fn key_pred() -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(16), b: Expr::Col(1) }
}

/// `p_brand = $1`.
pub open spec fn brand_pred(p0: Literal) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(19), b: Expr::Lit(p0) }
}

/// `p_container = $2`.
pub open spec fn cont_pred(p1: Literal) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(22), b: Expr::Lit(p1) }
}

/// The subquery's WHERE: inner `l_partkey` = outer `p_partkey`.
pub open spec fn sub_key_pred() -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(26), b: Expr::Col(16) }
}

pub open spec fn sub_filter() -> Query {
    Query::Filter { pred: sub_key_pred(), input: Box::new(Query::Table(0)) }
}

/// `AVG(l_quantity)` of the inner rows.
pub open spec fn sub_aggs() -> Seq<Agg> {
    seq![Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(29) }]
}

pub open spec fn sub_agg() -> Query {
    Query::Aggregate { aggs: sub_aggs(), input: Box::new(sub_filter()) }
}

/// The literal `0.2`.
pub open spec fn fifth_lit() -> Literal { Literal::Num { coeff: 2, scale: 1 } }

/// `0.2 * AVG(..)` over the aggregate row (the context's 25 values, then the average).
pub open spec fn sub_mul() -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Lit(fifth_lit())), b: Box::new(Expr::Col(25)) }
}

pub open spec fn sub_q() -> Query {
    Query::Project { exprs: seq![sub_mul()], input: Box::new(sub_agg()) }
}

/// `l_quantity < (sub_q)`.
pub open spec fn lt_pred() -> Pred {
    Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(4), b: Expr::Subquery(Box::new(sub_q())) }
}

/// The first three conjuncts (the join key and the part conditions).
pub open spec fn part_pred(ps: Seq<Literal>) -> Pred {
    and(and(key_pred(), brand_pred(ps[0])), cont_pred(ps[1]))
}

/// The WHERE condition.
pub open spec fn q_pred(ps: Seq<Literal>) -> Pred {
    and(part_pred(ps), lt_pred())
}

pub open spec fn q_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: q_pred(ps), input: Box::new(q_from()) }
}

/// `SUM(l_extendedprice)`.
pub open spec fn q_aggs() -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(5) }]
}

pub open spec fn q_agg(ps: Seq<Literal>) -> Query {
    Query::Aggregate { aggs: q_aggs(), input: Box::new(q_filter(ps)) }
}

/// The literal `7.0`.
pub open spec fn seven_lit() -> Literal { Literal::Num { coeff: 70, scale: 1 } }

/// `sum / 7.0`.
pub open spec fn div_expr() -> Expr {
    Expr::Call { f: ScalarFn::DivNumeric, args: seq![Expr::Col(0), Expr::Lit(seven_lit())] }
}

pub open spec fn q_body(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: seq![div_expr()], input: Box::new(q_agg(ps)) }
}

/// The statement is this tree, without ORDER BY, LIMIT or OFFSET.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures query_spec_at(ps) == (OrderedQuery { body: q_body(ps), keys: seq![], limit: None, offset: 0 }),
{
}

} // verus!
