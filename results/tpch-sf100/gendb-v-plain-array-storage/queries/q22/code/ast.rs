//! The statement's AST (`crate::query::query_spec_at`) assembled from named pieces, so that proofs can talk about
//! one node at a time (`lemma_query_shape` proves the assembly equal to the fixed statement).
//!
//! Environments: the outer WHERE condition reads a customer row (8 positions: `c_custkey` 0, `c_phone` 4,
//! `c_acctbal` 5). The AVG subquery reads its own customer row after those 8 positions (`c_phone` 12,
//! `c_acctbal` 13); the NOT EXISTS subquery reads an orders row after them (`o_custkey` 9).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::query::query_spec_at;

verus! {

/// `SUBSTRING(Col(c), 1, 2)`.
pub open spec fn sub2(c: nat) -> Expr {
    Expr::Call {
        f: ScalarFn::Substring3,
        args: seq![Expr::Col(c), Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 }), Expr::Lit(Literal::Int { v: 2, kind: IntKind::Int4 })],
    }
}

/// `SUBSTRING(Col(c), 1, 2) = l`.
pub open spec fn eqp(c: nat, l: Literal) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: sub2(c), b: Expr::Lit(l) }
}

pub open spec fn or(a: Pred, b: Pred) -> Pred { Pred::Or(Box::new(a), Box::new(b)) }
pub open spec fn and(a: Pred, b: Pred) -> Pred { Pred::And(Box::new(a), Box::new(b)) }

/// `SUBSTRING(Col(c), 1, 2) IN ($1, .., $7)` as the frontend's left-nested OR chain.
pub open spec fn in7(c: nat, ps: Seq<Literal>) -> Pred {
    or(or(or(or(or(or(eqp(c, ps[0]), eqp(c, ps[1])), eqp(c, ps[2])), eqp(c, ps[3])), eqp(c, ps[4])), eqp(c, ps[5])),
        eqp(c, ps[6]))
}

/// The subquery's WHERE: `c_acctbal > 0.00 AND SUBSTRING(c_phone, 1, 2) IN (..)` (inner positions 13 and 12).
pub open spec fn sub_pred(ps: Seq<Literal>) -> Pred {
    and(Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(13), b: Expr::Lit(Literal::Num { coeff: 0, scale: 2 }) }, in7(12, ps))
}

pub open spec fn sub_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: sub_pred(ps), input: Box::new(Query::Table(2)) }
}

/// The AVG aggregate of the subquery.
pub open spec fn sub_aggs() -> Seq<Agg> {
    seq![Agg::Avg { kind: NumKind::Numeric, arg: Expr::Col(13) }]
}

/// `SELECT AVG(c_acctbal) FROM customer WHERE ..`.
pub open spec fn sub_agg(ps: Seq<Literal>) -> Query {
    Query::Aggregate { aggs: sub_aggs(), input: Box::new(sub_filter(ps)) }
}

/// `c_acctbal > (subquery)`.
pub open spec fn gt_pred(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Gt, a: Expr::Col(5), b: Expr::Subquery(Box::new(sub_agg(ps))) }
}

/// `o_custkey = c_custkey` in the NOT EXISTS subquery.
pub open spec fn ex_pred() -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(9), b: Expr::Col(0) }
}

/// `EXISTS (SELECT * FROM orders WHERE o_custkey = c_custkey)`.
pub open spec fn ex() -> Pred {
    Pred::Exists(Box::new(Query::Filter { pred: ex_pred(), input: Box::new(Query::Table(1)) }))
}

/// The outer WHERE condition.
pub open spec fn where_pred(ps: Seq<Literal>) -> Pred {
    and(and(in7(4, ps), gt_pred(ps)), Pred::Not(Box::new(ex())))
}

pub open spec fn filtered(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: where_pred(ps), input: Box::new(Query::Table(2)) }
}

/// `SELECT SUBSTRING(c_phone, 1, 2), c_acctbal`.
pub open spec fn proj_exprs() -> Seq<Expr> {
    seq![sub2(4), Expr::Col(5)]
}

pub open spec fn projected(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: proj_exprs(), input: Box::new(filtered(ps)) }
}

/// `GROUP BY cntrycode` with `COUNT(*), SUM(c_acctbal)`.
pub open spec fn group_keys() -> Seq<Expr> { seq![Expr::Col(0)] }

pub open spec fn group_aggs() -> Seq<Agg> {
    seq![Agg::CountStar, Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(1) }]
}

pub open spec fn body(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: group_keys(), aggs: group_aggs(), input: Box::new(projected(ps)) }
}

/// `ORDER BY cntrycode`.
pub open spec fn order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 0, desc: false, nulls_first: false }]
}

/// The fixed statement is the assembly above, without LIMIT/OFFSET.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures query_spec_at(ps) == (OrderedQuery { body: body(ps), keys: order_keys(), limit: None, offset: 0 }),
{
}

} // verus!
