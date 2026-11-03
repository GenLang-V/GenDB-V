//! The statement's AST (`query::query_spec_at`) cut into named sub-trees, bottom-up:
//!
//! - `q8_from`: `FROM part, supplier, lineitem, orders, customer, nation n1, nation n2, region`, the left-deep
//!   product of the tables 3, 5, 0, 1, 2, 6, 6, 7 (joined rows of 60 values);
//! - `q8_pred`: the WHERE condition (eleven comparisons, left-nested `AND`s);
//! - `q8_inner`: the derived table `all_nations`, `SELECT EXTRACT(YEAR FROM o_orderdate), l_extendedprice *
//!   (1 - l_discount), n2.n_name` over the filtered rows;
//! - `q8_group`: `GROUP BY o_year` with `SUM(CASE WHEN nation = $1 THEN volume ELSE 0 END)` and `SUM(volume)`;
//! - `q8_body`: `SELECT o_year, <sum0> / <sum1>`, ordered by `o_year`.
//!
//! `lemma_query_shape` states that `query_spec_at(ps)` is exactly this tree.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::query::query_spec_at;

verus! {

pub open spec fn prod(l: Query, r: Query) -> Query {
    Query::Product { left: Box::new(l), right: Box::new(r) }
}

pub open spec fn and(a: Pred, b: Pred) -> Pred {
    Pred::And(Box::new(a), Box::new(b))
}

pub open spec fn eq_cols(i: nat, j: nat) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(i), b: Expr::Col(j) }
}

/// FROM: `((((((part x supplier) x lineitem) x orders) x customer) x nation) x nation) x region`.
pub open spec fn q8_from() -> Query {
    prod(prod(prod(prod(prod(prod(prod(Query::Table(3), Query::Table(5)), Query::Table(0)), Query::Table(1)),
        Query::Table(2)), Query::Table(6)), Query::Table(6)), Query::Table(7))
}

/// `r_name = $2`.
pub open spec fn reg_cmp(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(58), b: Expr::Lit(ps[1]) }
}

/// `o_orderdate BETWEEN DATE '1995-01-01' AND DATE '1996-12-31'`.
pub open spec fn date_pred() -> Pred {
    and(Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(36), b: Expr::Lit(Literal::Date { y: 1995, m: 1, d: 1 }) },
        Pred::Cmp { op: CmpOp::Le, a: Expr::Col(36), b: Expr::Lit(Literal::Date { y: 1996, m: 12, d: 31 }) })
}

/// `p_type = $3`.
pub open spec fn type_cmp(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(4), b: Expr::Lit(ps[2]) }
}

/// The joins of the WHERE condition, left-nested as written (`p_partkey = l_partkey AND .. AND
/// n1.n_regionkey = r_regionkey`).
pub open spec fn join_pred() -> Pred {
    and(and(and(and(and(eq_cols(0, 17), eq_cols(9, 18)), eq_cols(16, 32)), eq_cols(33, 41)), eq_cols(44, 49)),
        eq_cols(51, 57))
}

/// The WHERE condition.
pub open spec fn q8_pred(ps: Seq<Literal>) -> Pred {
    and(and(and(and(join_pred(), reg_cmp(ps)), eq_cols(12, 53)), date_pred()), type_cmp(ps))
}

pub open spec fn q8_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: q8_pred(ps), input: Box::new(q8_from()) }
}

/// `CAST(1 AS numeric)` and `CAST(0 AS numeric)` (integer literals promoted to numeric).
pub open spec fn num_one() -> Expr {
    Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 1, kind: IntKind::Int4 })) }
}

pub open spec fn num_zero() -> Expr {
    Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Lit(Literal::Int { v: 0, kind: IntKind::Int4 })) }
}

/// `EXTRACT(YEAR FROM o_orderdate)`.
pub open spec fn year_expr() -> Expr {
    Expr::Call { f: ScalarFn::ExtractYear, args: seq![Expr::Col(36)] }
}

/// `l_extendedprice * (1 - l_discount)`.
pub open spec fn vol_expr() -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Col(21)),
        b: Box::new(Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(num_one()), b: Box::new(Expr::Col(22)) }) }
}

/// The derived table's columns: `o_year, volume, nation`.
pub open spec fn inner_exprs() -> Seq<Expr> {
    seq![year_expr(), vol_expr(), Expr::Col(54)]
}

pub open spec fn q8_inner(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: inner_exprs(), input: Box::new(q8_filter(ps)) }
}

/// `CASE WHEN nation = $1 THEN volume ELSE 0 END`.
pub open spec fn case_expr(ps: Seq<Literal>) -> Expr {
    Expr::If {
        cond: Box::new(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(2), b: Expr::Lit(ps[0]) }),
        then_e: Box::new(Expr::Col(1)),
        else_e: Box::new(num_zero()),
    }
}

pub open spec fn group_keys() -> Seq<Expr> { seq![Expr::Col(0)] }

pub open spec fn group_aggs(ps: Seq<Literal>) -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: case_expr(ps) }, Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(1) }]
}

pub open spec fn q8_group(ps: Seq<Literal>) -> Query {
    Query::GroupBy { keys: group_keys(), aggs: group_aggs(ps), input: Box::new(q8_inner(ps)) }
}

/// `SELECT o_year, sum0 / sum1`.
pub open spec fn outer_exprs() -> Seq<Expr> {
    seq![Expr::Col(0), Expr::Call { f: ScalarFn::DivNumeric, args: seq![Expr::Col(1), Expr::Col(2)] }]
}

pub open spec fn q8_body(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: outer_exprs(), input: Box::new(q8_group(ps)) }
}

/// `ORDER BY o_year`.
pub open spec fn q8_order() -> Seq<OrderKey> {
    seq![OrderKey { col: 0, desc: false, nulls_first: false }]
}

/// The statement is this tree, ordered by `o_year`, without LIMIT or OFFSET.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures query_spec_at(ps) == (OrderedQuery { body: q8_body(ps), keys: q8_order(), limit: None, offset: 0 }),
{
}

} // verus!
