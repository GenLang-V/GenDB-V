//! The statement's AST (`crate::query::query_spec_at`) cut into named pieces. The join and WHERE of the outer
//! query and of the subquery are the same trees with column positions shifted by the context length `c` (0 outside,
//! 3 inside the HAVING subquery, whose environment starts with the outer group row).
use vstd::prelude::*;
use crate::spec::ast::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::query::query_spec_at;

verus! {

/// `n.adsh = s.adsh` (positions 0 and 9 of a joined row, after `c` context values).
pub open spec fn pred_join(c: nat) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(c + 0), b: Expr::Col(c + 9) }
}

/// `n.uom = $1 AND s.fy = $2 AND n.value IS NOT NULL`.
pub open spec fn pred_where(ps: Seq<Literal>, c: nat) -> Pred {
    Pred::And(
        Box::new(Pred::And(
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(c + 5), b: Expr::Lit(ps[0]) }),
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(c + 19), b: Expr::Lit(ps[1]) }),
        )),
        Box::new(Pred::Not(Box::new(Pred::IsNull(Expr::Col(c + 7))))),
    )
}

/// `num x sub`.
pub open spec fn q_product() -> Query {
    Query::Product { left: Box::new(Query::Table(1)), right: Box::new(Query::Table(0)) }
}

pub open spec fn q_join(c: nat) -> Query {
    Query::Filter { pred: pred_join(c), input: Box::new(q_product()) }
}

pub open spec fn q_where(ps: Seq<Literal>, c: nat) -> Query {
    Query::Filter { pred: pred_where(ps, c), input: Box::new(q_join(c)) }
}

/// `SUM(n.value)` with the value at position `c + 7`.
pub open spec fn agg_sum(c: nat) -> Agg {
    Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(c + 7) }
}

/// `GROUP BY s.name, s.cik` with `SUM(n.value)` (outer query).
pub open spec fn keys_top() -> Seq<Expr> {
    seq![Expr::Col(11), Expr::Col(10)]
}

pub open spec fn q_group_top(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: keys_top(), aggs: seq![agg_sum(0)], input: Box::new(q_where(ps, 0)) }
}

/// `GROUP BY s2.cik` with `SUM(n2.value)` (subquery, context of 3 values).
pub open spec fn keys_cik() -> Seq<Expr> {
    seq![Expr::Col(13)]
}

pub open spec fn q_group_cik(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: keys_cik(), aggs: seq![agg_sum(3)], input: Box::new(q_where(ps, 3)) }
}

/// `SELECT sub_total`.
pub open spec fn q_project(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: seq![Expr::Col(4)], input: Box::new(q_group_cik(ps)) }
}

/// `AVG(sub_total)`.
pub open spec fn agg_avg() -> Agg {
    Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(3) }
}

pub open spec fn q_avg(ps: Seq<Literal>) -> Query {
    Query::Aggregate { aggs: seq![agg_avg()], input: Box::new(q_project(ps)) }
}

/// `HAVING SUM(n.value) > (subquery)`.
pub open spec fn pred_having(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(2), b: Expr::Subquery(Box::new(q_avg(ps))) }
}

pub open spec fn q_body(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: pred_having(ps), input: Box::new(q_group_top(ps)) }
}

/// `ORDER BY total_value DESC`.
pub open spec fn order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 2, desc: true, nulls_first: true }]
}

/// The statement is these pieces.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures
        query_spec_at(ps).body == q_body(ps),
        query_spec_at(ps).keys == order_keys(),
        query_spec_at(ps).limit == Some(100nat),
        query_spec_at(ps).offset == 0,
{
    assert(pred_join(0) == Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0), b: Expr::Col(9) });
    assert(pred_join(3) == Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(3), b: Expr::Col(12) });
    assert(agg_sum(0) == Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(7) });
    assert(agg_sum(3) == Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(10) });
    assert(query_spec_at(ps).body == q_body(ps));
}

} // verus!
