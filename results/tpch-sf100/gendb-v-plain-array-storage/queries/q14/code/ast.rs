//! The statement's AST (`query::query_spec_at`) cut into named sub-trees, bottom-up:
//!
//! - `q_from`: `FROM lineitem, part`, the product of the tables 0 and 3 (joined rows of 16 + 9 = 25 values;
//!   `l_partkey` at 1, `l_extendedprice` at 5, `l_discount` at 6, `l_shipdate` at 10, `p_partkey` at 16, `p_type`
//!   at 20);
//! - `q_pred`: `l_partkey = p_partkey AND l_shipdate >= $1 AND l_shipdate < $1 + INTERVAL '1' MONTH`;
//! - `q_aggs`: `SUM(CASE WHEN p_type LIKE 'PROMO%' THEN volume ELSE 0 END)` and `SUM(volume)` with
//!   `volume = l_extendedprice * (1 - l_discount)`;
//! - `q_body`: `SELECT 100.00 * sum0 / sum1` over the one aggregate row.
//!
//! `lemma_query_shape` states that `query_spec_at(ps)` is exactly this tree, unordered, without LIMIT or OFFSET.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
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

/// `l_partkey = p_partkey`.
pub open spec fn key_pred() -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(1), b: Expr::Col(16) }
}

/// `l_shipdate >= $1`.
pub open spec fn lo_pred(p0: Literal) -> Pred {
    Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(10), b: Expr::Lit(p0) }
}

/// `$1 + INTERVAL '1' MONTH` (the date cast to a timestamp, plus one month).
pub open spec fn month_end(p0: Literal) -> Expr {
    Expr::AddInterval {
        arg: Box::new(Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(p0)) }),
        months: 1i32,
        days: 0i32,
        micros: 0i64,
    }
}

/// `l_shipdate < $1 + INTERVAL '1' MONTH`.
pub open spec fn hi_pred(p0: Literal) -> Pred {
    Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(10), b: month_end(p0) }
}

/// The WHERE condition.
pub open spec fn q_pred(ps: Seq<Literal>) -> Pred {
    and(and(key_pred(), lo_pred(ps[0])), hi_pred(ps[0]))
}

pub open spec fn q_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: q_pred(ps), input: Box::new(q_from()) }
}

/// `CAST(k AS numeric)` of an int4 literal.
pub open spec fn num_int(k: int) -> Expr {
    Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: k, kind: IntKind::Int4 })) }
}

/// `l_extendedprice * (1 - l_discount)`.
pub open spec fn vol_expr() -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Col(5)),
        b: Box::new(Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(num_int(1)), b: Box::new(Expr::Col(6)) }) }
}

/// The bytes of the pattern `'PROMO%'` and of the escape `'\'`.
pub open spec fn promo_pat() -> Seq<u8> { seq![80u8, 82u8, 79u8, 77u8, 79u8, 37u8] }
pub open spec fn esc_bytes() -> Seq<u8> { seq![92u8] }

/// `p_type LIKE 'PROMO%'` (the frontend's escape `\`).
pub open spec fn like_call() -> Expr {
    Expr::Call { f: ScalarFn::Like, args: seq![Expr::Col(20), Expr::Lit(Literal::Text(promo_pat())), Expr::Lit(Literal::Text(esc_bytes()))] }
}

/// `CASE WHEN p_type LIKE 'PROMO%' THEN volume ELSE 0 END`.
pub open spec fn case_expr() -> Expr {
    Expr::If { cond: Box::new(Pred::OfBool(like_call())), then_e: Box::new(vol_expr()), else_e: Box::new(num_int(0)) }
}

pub open spec fn q_aggs() -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: case_expr() }, Agg::Sum { kind: NumKind::Numeric, arg: vol_expr() }]
}

pub open spec fn q_agg(ps: Seq<Literal>) -> Query {
    Query::Aggregate { aggs: q_aggs(), input: Box::new(q_filter(ps)) }
}

/// `100.00 * sum0`.
pub open spec fn mul_expr() -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Lit(Literal::Num { coeff: 10000, scale: 2 })),
        b: Box::new(Expr::Col(0)) }
}

/// `100.00 * sum0 / sum1`.
pub open spec fn div_expr() -> Expr {
    Expr::Call { f: ScalarFn::DivNumeric, args: seq![mul_expr(), Expr::Col(1)] }
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
