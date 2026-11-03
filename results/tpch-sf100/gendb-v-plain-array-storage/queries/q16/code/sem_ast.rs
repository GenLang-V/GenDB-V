//! The statement's AST (`crate::query::query_spec_at`) assembled from named pieces, so that proofs can talk about
//! one node at a time (`lemma_query_shape` proves the assembly equal to the fixed statement).
//!
//! Environment of the WHERE condition (14 positions): partsupp 0..5 (ps_partkey 0, ps_suppkey 1), then part 5..14
//! (p_partkey 5, p_brand 8, p_type 9, p_size 10). The NOT IN subquery reads supplier rows after these 14 positions:
//! s_suppkey at 14, s_comment at 20.
use vstd::prelude::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::query::query_spec_at;

verus! {

pub open spec fn and(a: Pred, b: Pred) -> Pred {
    Pred::And(Box::new(a), Box::new(b))
}

pub open spec fn or(a: Pred, b: Pred) -> Pred {
    Pred::Or(Box::new(a), Box::new(b))
}

/// The escape string of `LIKE` without `ESCAPE` (a backslash).
pub open spec fn backslash() -> Seq<u8> {
    seq![92u8]
}

/// `'%Customer%Complaints%'` (opaque: its 21 bytes are revealed only where they matter).
#[verifier::opaque]
pub open spec fn comment_pat() -> Seq<u8> {
    seq![37u8, 67u8, 117u8, 115u8, 116u8, 111u8, 109u8, 101u8, 114u8, 37u8, 67u8, 111u8, 109u8, 112u8, 108u8, 97u8,
        105u8, 110u8, 116u8, 115u8, 37u8]
}

/// `p_partkey = ps_partkey` (node n8).
pub open spec fn key_eq() -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(5), b: Expr::Col(0) }
}

/// `p_brand <> $1` (node n12).
pub open spec fn brand_ne(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Ne, a: Expr::Col(8), b: Expr::Lit(ps[0]) }
}

/// `p_type LIKE $2` (node n19).
pub open spec fn type_like(ps: Seq<Literal>) -> Expr {
    Expr::Call { f: ScalarFn::Like, args: seq![Expr::Col(9), Expr::Lit(ps[1]), Expr::Lit(Literal::Text(backslash()))] }
}

/// `p_type NOT LIKE $2` (node n21).
pub open spec fn type_not_like(ps: Seq<Literal>) -> Pred {
    Pred::Not(Box::new(Pred::OfBool(type_like(ps))))
}

/// `p_size = $(3 + i)`.
pub open spec fn size_eq(ps: Seq<Literal>, i: int) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(10), b: Expr::Lit(ps[2 + i]) }
}

/// The first `n` disjuncts of `p_size IN ($3, .., $10)`, left-nested (`size_in(ps, 8)` is node n61).
pub open spec fn size_in(ps: Seq<Literal>, n: int) -> Pred
    decreases n,
{
    if n <= 1 { size_eq(ps, 0) } else { or(size_in(ps, n - 1), size_eq(ps, n - 1)) }
}

/// `s_comment LIKE '%Customer%Complaints%'` (node n70).
pub open spec fn comment_like() -> Expr {
    Expr::Call { f: ScalarFn::Like, args: seq![Expr::Col(20), Expr::Lit(Literal::Text(comment_pat())),
        Expr::Lit(Literal::Text(backslash()))] }
}

/// `WHERE s_comment LIKE ..` over supplier (node n73).
pub open spec fn sub_filter() -> Query {
    Query::Filter { pred: Pred::OfBool(comment_like()), input: Box::new(Query::Table(5)) }
}

/// `SELECT s_suppkey FROM supplier WHERE ..` (node n74).
pub open spec fn sub_query() -> Query {
    Query::Project { exprs: seq![Expr::Col(14)], input: Box::new(sub_filter()) }
}

/// `ps_suppkey IN (subquery)` (node n75).
pub open spec fn in_sub() -> Pred {
    Pred::AnyCmp { op: CmpOp::Eq, e: Expr::Col(1), q: Box::new(sub_query()) }
}

/// `ps_suppkey NOT IN (subquery)` (node n76).
pub open spec fn not_in() -> Pred {
    Pred::Not(Box::new(in_sub()))
}

/// The conjunctions of the WHERE condition, innermost first (nodes n13, n22, n62, n77).
pub open spec fn where1(ps: Seq<Literal>) -> Pred { and(key_eq(), brand_ne(ps)) }
pub open spec fn where2(ps: Seq<Literal>) -> Pred { and(where1(ps), type_not_like(ps)) }
pub open spec fn where3(ps: Seq<Literal>) -> Pred { and(where2(ps), size_in(ps, 8)) }
pub open spec fn where_pred(ps: Seq<Literal>) -> Pred { and(where3(ps), not_in()) }

/// `FROM partsupp, part` (node n80).
pub open spec fn from_q() -> Query {
    Query::Product { left: Box::new(Query::Table(4)), right: Box::new(Query::Table(3)) }
}

/// The WHERE over the product (node n81).
pub open spec fn filtered(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: where_pred(ps), input: Box::new(from_q()) }
}

/// `GROUP BY p_brand, p_type, p_size` and `COUNT(DISTINCT ps_suppkey)`.
pub open spec fn group_keys() -> Seq<Expr> {
    seq![Expr::Col(8), Expr::Col(9), Expr::Col(10)]
}

pub open spec fn group_aggs() -> Seq<Agg> {
    seq![Agg::DistinctAgg(Box::new(Agg::Count(Expr::Col(1))))]
}

/// The statement body (node n82).
pub open spec fn body(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: group_keys(), aggs: group_aggs(), input: Box::new(filtered(ps)) }
}

/// `ORDER BY supplier_cnt DESC, p_brand, p_type, p_size` over the output columns.
pub open spec fn order_keys() -> Seq<OrderKey> {
    seq![
        OrderKey { col: 3, desc: true, nulls_first: true },
        OrderKey { col: 0, desc: false, nulls_first: false },
        OrderKey { col: 1, desc: false, nulls_first: false },
        OrderKey { col: 2, desc: false, nulls_first: false },
    ]
}

/// The fixed statement is the assembly above, without LIMIT/OFFSET.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures query_spec_at(ps) == (OrderedQuery { body: body(ps), keys: order_keys(), limit: None, offset: 0 }),
{
    reveal_with_fuel(size_in, 8);
    reveal(comment_pat);
    assert(comment_pat() =~= seq![37u8, 67u8, 117u8, 115u8, 116u8, 111u8, 109u8, 101u8, 114u8, 37u8, 67u8, 111u8,
        109u8, 112u8, 108u8, 97u8, 105u8, 110u8, 116u8, 115u8, 37u8]);
}

} // verus!
