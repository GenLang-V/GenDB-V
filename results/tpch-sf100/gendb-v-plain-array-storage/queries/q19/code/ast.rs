//! The statement's AST (`query::query_spec_at`) cut into named sub-trees, bottom-up:
//!
//! - `q_from`: `FROM lineitem, part`, the product of the tables 0 and 3 (joined rows of 16 + 9 = 25 values;
//!   `l_partkey` at 1, `l_quantity` at 4, `l_extendedprice` at 5, `l_discount` at 6, `l_shipinstruct` at 13,
//!   `l_shipmode` at 14, `p_partkey` at 16, `p_brand` at 19, `p_size` at 21, `p_container` at 22);
//! - `branch(k, pb, pv)`: the `k`-th parenthesized group of the WHERE clause, a left-nested chain of eight
//!   conjuncts (key match, brand, container list, quantity lower and upper bound, size range, ship mode list, ship
//!   instruction), with the brand parameter literal `pb` and the quantity parameter literal `pv`;
//! - `q_pred`: `(branch 0 OR branch 1) OR branch 2`;
//! - `q_aggs`: `SUM(l_extendedprice * (1 - l_discount))`; `q_body`: the aggregate over the filter.
//!
//! `lemma_query_shape` states that `query_spec_at(ps)` is exactly this tree, unordered, without LIMIT or OFFSET.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::query::query_spec_at;
use crate::agent::line::{cont_lit, air_lit, air_reg_lit, dip_lit};

verus! {

pub open spec fn and(a: Pred, b: Pred) -> Pred {
    Pred::And(Box::new(a), Box::new(b))
}

pub open spec fn or(a: Pred, b: Pred) -> Pred {
    Pred::Or(Box::new(a), Box::new(b))
}

/// An int4 literal.
pub open spec fn int4(v: int) -> Literal { Literal::Int { v, kind: IntKind::Int4 } }

/// `Col(c) = '<text>'`.
pub open spec fn col_eq_text(c: nat, t: Seq<u8>) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(c), b: Expr::Lit(Literal::Text(t)) }
}

/// FROM: `lineitem x part`.
pub open spec fn q_from() -> Query {
    Query::Product { left: Box::new(Query::Table(0)), right: Box::new(Query::Table(3)) }
}

/// `p_partkey = l_partkey`.
pub open spec fn key_pred() -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(16), b: Expr::Col(1) }
}

/// `p_brand = $k`.
pub open spec fn brand_pred(pb: Literal) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(19), b: Expr::Lit(pb) }
}

/// `p_container IN (...)` of branch `k`: a left-nested OR of four equalities.
pub open spec fn cont_pred(k: int) -> Pred {
    or(or(or(col_eq_text(22, cont_lit(k, 0)), col_eq_text(22, cont_lit(k, 1))), col_eq_text(22, cont_lit(k, 2))),
        col_eq_text(22, cont_lit(k, 3)))
}

/// `l_quantity >= $k` (the int4 parameter cast to numeric).
pub open spec fn qge_pred(pv: Literal) -> Pred {
    Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(4), b: Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(pv)) } }
}

/// `$k + 10` (int4 addition).
pub open spec fn plus10(pv: Literal) -> Expr {
    Expr::Arith { op: ArithOp::Add, kind: NumKind::Int4, a: Box::new(Expr::Lit(pv)), b: Box::new(Expr::Lit(int4(10))) }
}

/// `l_quantity <= $k + 10`.
pub open spec fn qle_pred(pv: Literal) -> Pred {
    Pred::Cmp { op: CmpOp::Le, a: Expr::Col(4), b: Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(plus10(pv)) } }
}

/// `p_size BETWEEN 1 AND hi`.
pub open spec fn size_pred(hi: int) -> Pred {
    and(Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(21), b: Expr::Lit(int4(1)) },
        Pred::Cmp { op: CmpOp::Le, a: Expr::Col(21), b: Expr::Lit(int4(hi)) })
}

/// `l_shipmode IN ('AIR', 'AIR REG')`.
pub open spec fn mode_pred() -> Pred {
    or(col_eq_text(14, air_lit()), col_eq_text(14, air_reg_lit()))
}

/// `l_shipinstruct = 'DELIVER IN PERSON'`.
pub open spec fn instr_pred() -> Pred {
    col_eq_text(13, dip_lit())
}

/// The first five conjuncts of branch `k`.
pub open spec fn head5(k: int, pb: Literal, pv: Literal) -> Pred {
    and(and(and(and(key_pred(), brand_pred(pb)), cont_pred(k)), qge_pred(pv)), qle_pred(pv))
}

/// Branch `k` with the brand literal `pb` and the quantity literal `pv`.
pub open spec fn branch(k: int, pb: Literal, pv: Literal) -> Pred {
    and(and(and(head5(k, pb, pv), size_pred(5 * (k + 1))), mode_pred()), instr_pred())
}

/// The WHERE condition.
pub open spec fn q_pred(ps: Seq<Literal>) -> Pred {
    or(or(branch(0, ps[0], ps[1]), branch(1, ps[2], ps[3])), branch(2, ps[4], ps[5]))
}

pub open spec fn q_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: q_pred(ps), input: Box::new(q_from()) }
}

/// `CAST(k AS numeric)` of an int4 literal.
pub open spec fn num_int(k: int) -> Expr {
    Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(int4(k))) }
}

/// `l_extendedprice * (1 - l_discount)`.
pub open spec fn vol_expr() -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Col(5)),
        b: Box::new(Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(num_int(1)), b: Box::new(Expr::Col(6)) }) }
}

pub open spec fn q_aggs() -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: vol_expr() }]
}

/// The statement's body: the aggregate over the filter.
pub open spec fn q_body(ps: Seq<Literal>) -> Query {
    Query::Aggregate { aggs: q_aggs(), input: Box::new(q_filter(ps)) }
}

/// The statement is this tree, without ORDER BY, LIMIT or OFFSET.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures query_spec_at(ps) == (OrderedQuery { body: q_body(ps), keys: seq![], limit: None, offset: 0 }),
{
    assert(cont_lit(0, 0) =~= seq![83u8, 77u8, 32u8, 67u8, 65u8, 83u8, 69u8]);
    assert(q_pred(ps) == query_spec_at(ps).body->Aggregate_input->Filter_pred);
}

} // verus!
