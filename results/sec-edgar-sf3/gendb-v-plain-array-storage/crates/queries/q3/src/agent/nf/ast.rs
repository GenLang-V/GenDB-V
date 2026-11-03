//! Named parts of the statement's AST (`crate::query::query_spec_at`): the FROM/WHERE block of the outer query
//! and of the HAVING subquery differ only by the column offset `d` of their environment (0 at top level, 3 inside
//! the HAVING subquery, whose context is the 3-column group row).
use vstd::prelude::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::query::query_spec_at;

verus! {

/// `n.adsh = s.adsh` at column offset `d`.
pub open spec fn join_pred(d: nat) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(0 + d), b: Expr::Col(9 + d) }
}

/// `n.uom = $1 AND s.fy = $2 AND n.value IS NOT NULL` at column offset `d`.
pub open spec fn where_pred(d: nat, ps: Seq<Literal>) -> Pred {
    Pred::And(
        Box::new(Pred::And(
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5 + d), b: Expr::Lit(ps[0]) }),
            Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(19 + d), b: Expr::Lit(ps[1]) }),
        )),
        Box::new(Pred::Not(Box::new(Pred::IsNull(Expr::Col(7 + d))))),
    )
}

/// `num x sub`.
pub open spec fn from_q() -> Query {
    Query::Product { left: Box::new(Query::Table(1)), right: Box::new(Query::Table(0)) }
}

/// The join condition over the product.
pub open spec fn join_q(d: nat) -> Query {
    Query::Filter { pred: join_pred(d), input: Box::new(from_q()) }
}

/// The WHERE block.
pub open spec fn where_q(d: nat, ps: Seq<Literal>) -> Query {
    Query::Filter { pred: where_pred(d, ps), input: Box::new(join_q(d)) }
}

/// `GROUP BY s.name, s.cik` with `SUM(n.value)`.
pub open spec fn outer_keys() -> Seq<Expr> {
    seq![Expr::Col(11), Expr::Col(10)]
}

pub open spec fn outer_aggs() -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(7) }]
}

pub open spec fn outer_gb(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: outer_keys(), aggs: outer_aggs(), input: Box::new(where_q(0, ps)) }
}

/// The subquery's `GROUP BY s2.cik` with `SUM(n2.value)` (context of 3 columns).
pub open spec fn inner_keys() -> Seq<Expr> {
    seq![Expr::Col(13)]
}

pub open spec fn inner_aggs() -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(10) }]
}

pub open spec fn inner_gb(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: inner_keys(), aggs: inner_aggs(), input: Box::new(where_q(3, ps)) }
}

/// `SELECT sub_total` over the subquery's groups.
pub open spec fn inner_proj(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: seq![Expr::Col(4)], input: Box::new(inner_gb(ps)) }
}

/// `SELECT AVG(sub_total)`.
pub open spec fn avg_aggs() -> Seq<Agg> {
    seq![Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(3) }]
}

pub open spec fn avg_q(ps: Seq<Literal>) -> Query {
    Query::Aggregate { aggs: avg_aggs(), input: Box::new(inner_proj(ps)) }
}

/// `HAVING SUM(n.value) > (subquery)` over the group row `[name, cik, total]`.
pub open spec fn having_pred(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(2), b: Expr::Subquery(Box::new(avg_q(ps))) }
}

pub open spec fn body_q(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: having_pred(ps), input: Box::new(outer_gb(ps)) }
}

/// `ORDER BY total_value DESC`.
pub open spec fn order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 2, desc: true, nulls_first: true }]
}

/// The statement is these parts.
pub proof fn lemma_query_parts(ps: Seq<Literal>)
    ensures
        query_spec_at(ps) == (OrderedQuery { body: body_q(ps), keys: order_keys(), limit: Some(100nat), offset: 0nat }),
{
    assert(outer_keys() =~= seq![Expr::Col(11), Expr::Col(10)]);
    assert(query_spec_at(ps).body == body_q(ps));
    assert(query_spec_at(ps).keys =~= order_keys());
}

} // verus!
