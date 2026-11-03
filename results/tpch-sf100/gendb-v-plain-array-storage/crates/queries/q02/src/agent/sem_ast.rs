//! The statement's AST (`crate::query::query_spec_at`) assembled from named pieces, so that proofs can talk about
//! one node at a time (`lemma_query_shape` proves the assembly equal to the fixed statement).
//!
//! Outer environment (28 positions): part 0..9 (p_partkey 0, p_mfgr 2, p_type 4, p_size 5), supplier 9..16
//! (s_suppkey 9, s_name 10, s_address 11, s_nationkey 12, s_phone 13, s_acctbal 14, s_comment 15), partsupp 16..21
//! (ps_partkey 16, ps_suppkey 17, ps_supplycost 19), nation 21..25 (n_nationkey 21, n_name 22, n_regionkey 23),
//! region 25..28 (r_regionkey 25, r_name 26). The subquery's rows (19 positions) follow the outer row:
//! partsupp 28..33, supplier 33..40, nation 40..44, region 44..47.
use vstd::prelude::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::query::query_spec_at;
use crate::link::query::col_exprs;

verus! {

/// `col i = col j`.
pub open spec fn eq_cols(i: nat, j: nat) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(i), b: Expr::Col(j) }
}

/// `col i = literal`.
pub open spec fn eq_lit(i: nat, l: Literal) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(i), b: Expr::Lit(l) }
}

pub open spec fn and(a: Pred, b: Pred) -> Pred {
    Pred::And(Box::new(a), Box::new(b))
}

/// The escape string of `LIKE` without `ESCAPE` (a backslash).
pub open spec fn backslash() -> Seq<u8> {
    seq![92u8]
}

/// `p_type LIKE $2`.
pub open spec fn like_expr(ps: Seq<Literal>) -> Expr {
    Expr::Call { f: ScalarFn::Like, args: seq![Expr::Col(4), Expr::Lit(ps[1]), Expr::Lit(Literal::Text(backslash()))] }
}

/// The outer WHERE conditions before the subquery comparison (node n40), innermost first.
pub open spec fn outer_filters(ps: Seq<Literal>) -> Pred {
    and(and(and(and(and(and(eq_cols(0, 16), eq_cols(9, 17)), eq_lit(5, ps[0])), Pred::OfBool(like_expr(ps))),
        eq_cols(12, 21)), eq_cols(23, 25)), eq_lit(26, ps[2]))
}

/// The subquery's WHERE (node n63).
pub open spec fn sub_filters(ps: Seq<Literal>) -> Pred {
    and(and(and(and(eq_cols(0, 28), eq_cols(33, 29)), eq_cols(36, 40)), eq_cols(42, 44)), eq_lit(45, ps[2]))
}

pub open spec fn prod(l: Query, r: Query) -> Query {
    Query::Product { left: Box::new(l), right: Box::new(r) }
}

/// `FROM partsupp, supplier, nation, region` of the subquery.
pub open spec fn sub_from() -> Query {
    prod(prod(prod(Query::Table(4), Query::Table(5)), Query::Table(6)), Query::Table(7))
}

/// The aggregate `MIN(ps_supplycost)` (position 31 of the subquery environment).
pub open spec fn sub_aggs() -> Seq<Agg> {
    seq![Agg::Min(Expr::Col(31))]
}

/// `SELECT MIN(ps_supplycost) FROM .. WHERE ..` (node n72).
pub open spec fn sub_query(ps: Seq<Literal>) -> Query {
    Query::Aggregate { aggs: sub_aggs(), input: Box::new(Query::Filter { pred: sub_filters(ps), input: Box::new(sub_from()) }) }
}

/// `ps_supplycost = (subquery)` (node n74).
pub open spec fn cost_eq_min(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(19), b: Expr::Subquery(Box::new(sub_query(ps))) }
}

/// The whole outer WHERE (node n75).
pub open spec fn outer_pred(ps: Seq<Literal>) -> Pred {
    and(outer_filters(ps), cost_eq_min(ps))
}

/// `FROM part, supplier, partsupp, nation, region`.
pub open spec fn outer_from() -> Query {
    prod(prod(prod(prod(Query::Table(3), Query::Table(5)), Query::Table(4)), Query::Table(6)), Query::Table(7))
}

/// The output columns: s_acctbal, s_name, n_name, p_partkey, p_mfgr, s_address, s_phone, s_comment.
pub open spec fn out_cols() -> Seq<nat> {
    seq![14nat, 10nat, 22nat, 0nat, 2nat, 11nat, 13nat, 15nat]
}

/// `WHERE` over the product.
pub open spec fn filtered(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: outer_pred(ps), input: Box::new(outer_from()) }
}

/// The statement body (without ORDER BY / LIMIT).
pub open spec fn body(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: col_exprs(out_cols()), input: Box::new(filtered(ps)) }
}

/// `ORDER BY s_acctbal DESC, n_name, s_name, p_partkey` over the output columns.
pub open spec fn order_keys() -> Seq<OrderKey> {
    seq![
        OrderKey { col: 0, desc: true, nulls_first: true },
        OrderKey { col: 2, desc: false, nulls_first: false },
        OrderKey { col: 1, desc: false, nulls_first: false },
        OrderKey { col: 3, desc: false, nulls_first: false },
    ]
}

/// The fixed statement is the assembly above, with `LIMIT 100`.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures query_spec_at(ps) == (OrderedQuery { body: body(ps), keys: order_keys(), limit: Some(100), offset: 0 }),
{
    assert(col_exprs(out_cols()) =~= seq![Expr::Col(14), Expr::Col(10), Expr::Col(22), Expr::Col(0), Expr::Col(2),
        Expr::Col(11), Expr::Col(13), Expr::Col(15)]);
}

} // verus!
