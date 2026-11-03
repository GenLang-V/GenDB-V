//! The statement's AST (`crate::query::query_spec_at`) assembled from named pieces, so that proofs can talk about
//! one node at a time (`lemma_query_shape` proves the assembly equal to the fixed statement).
//!
//! Environment of the WHERE and the GROUP BY (47 positions, the FROM order): customer 0..8 (c_custkey 0,
//! c_nationkey 3), orders 8..17 (o_orderkey 8, o_custkey 9, o_orderdate 12), lineitem 17..33 (l_orderkey 17,
//! l_suppkey 19, l_extendedprice 22, l_discount 23), supplier 33..40 (s_suppkey 33, s_nationkey 36), nation
//! 40..44 (n_nationkey 40, n_name 41, n_regionkey 42), region 44..47 (r_regionkey 44, r_name 45).
use vstd::prelude::*;
use crate::spec::int::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::query::query_spec_at;

verus! {

/// `col i = col j`.
pub open spec fn eq_cols(i: nat, j: nat) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(i), b: Expr::Col(j) }
}

pub open spec fn and(a: Pred, b: Pred) -> Pred {
    Pred::And(Box::new(a), Box::new(b))
}

pub open spec fn prod(l: Query, r: Query) -> Query {
    Query::Product { left: Box::new(l), right: Box::new(r) }
}

/// The join and region conditions (node n36): `c_custkey = o_custkey AND l_orderkey = o_orderkey AND
/// l_suppkey = s_suppkey AND c_nationkey = s_nationkey AND s_nationkey = n_nationkey AND n_regionkey = r_regionkey
/// AND r_name = $1`, innermost first.
pub open spec fn join_conds(ps: Seq<Literal>) -> Pred {
    and(and(and(and(and(and(eq_cols(0, 9), eq_cols(17, 8)), eq_cols(19, 33)), eq_cols(3, 36)), eq_cols(36, 40)),
        eq_cols(42, 44)),
        Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(45), b: Expr::Lit(ps[0]) })
}

/// `o_orderdate >= $2` (node n40).
pub open spec fn date_ge(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(12), b: Expr::Lit(ps[1]) }
}

/// `$2 + INTERVAL '1' YEAR` (node n46): the date cast to a timestamp, plus 12 months.
pub open spec fn hi_expr(ps: Seq<Literal>) -> Expr {
    Expr::AddInterval {
        arg: Box::new(Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(ps[1])) }),
        months: 12i32,
        days: 0i32,
        micros: 0i64,
    }
}

/// `o_orderdate < $2 + INTERVAL '1' YEAR` (node n47).
pub open spec fn date_lt(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(12), b: hi_expr(ps) }
}

/// The whole WHERE (node n48).
pub open spec fn where_pred(ps: Seq<Literal>) -> Pred {
    and(and(join_conds(ps), date_ge(ps)), date_lt(ps))
}

/// `FROM customer, orders, lineitem, supplier, nation, region` (node n59, left-deep).
pub open spec fn from_q() -> Query {
    prod(prod(prod(prod(prod(Query::Table(2), Query::Table(1)), Query::Table(0)), Query::Table(5)), Query::Table(6)),
        Query::Table(7))
}

/// `1::numeric`.
pub open spec fn e_one() -> Expr {
    Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) }
}

/// `l_extendedprice * (1 - l_discount)` (node n7).
pub open spec fn e_rev() -> Expr {
    Expr::Arith {
        op: ArithOp::Mul,
        kind: NumKind::Numeric,
        a: Box::new(Expr::Col(22)),
        b: Box::new(Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(e_one()), b: Box::new(Expr::Col(23)) }),
    }
}

/// `GROUP BY n_name`.
pub open spec fn ast_keys() -> Seq<Expr> {
    seq![Expr::Col(41)]
}

/// `SUM(l_extendedprice * (1 - l_discount))`.
pub open spec fn ast_aggs() -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: e_rev() }]
}

/// `WHERE` over the product.
pub open spec fn filtered(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: where_pred(ps), input: Box::new(from_q()) }
}

/// The statement body (without ORDER BY).
pub open spec fn body(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: ast_keys(), aggs: ast_aggs(), input: Box::new(filtered(ps)) }
}

/// `ORDER BY revenue DESC`.
pub open spec fn order_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 1, desc: true, nulls_first: true }]
}

/// The fixed statement is the assembly above.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures query_spec_at(ps) == (OrderedQuery { body: body(ps), keys: order_keys(), limit: None, offset: 0 }),
{
}

} // verus!
