//! The statement's AST (`query::query_spec_at`) cut into named sub-trees, innermost first. Environments (positions):
//!
//! - outer rows of `FROM supplier, nation`: 11 values (`s_suppkey` 0, `s_name` 1, `s_address` 2, `s_nationkey` 3,
//!   `n_nationkey` 7, `n_name` 8);
//! - the partsupp subquery appends a partsupp row: 16 values (`ps_partkey` 11, `ps_suppkey` 12, `ps_availqty` 13);
//! - the part subquery appends a part row to those 16: 25 values (`p_partkey` 16, `p_name` 17);
//! - the lineitem subquery appends a lineitem row to the 16: 32 values (`l_partkey` 17, `l_suppkey` 18,
//!   `l_quantity` 20, `l_shipdate` 26); its aggregate row follows the 16 context values at 16.
//!
//! `lemma_query_shape` states that `query_spec_at(ps)` is exactly this tree, ordered by `s_name`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::query::query_spec_at;

verus! {

pub open spec fn and(a: Pred, b: Pred) -> Pred {
    Pred::And(Box::new(a), Box::new(b))
}

// ------------------------------------------------------------------------------------------ lineitem subquery

/// `l_partkey = ps_partkey AND l_suppkey = ps_suppkey`.
pub open spec fn li_key_pred() -> Pred {
    and(Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(17), b: Expr::Col(11) }, Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(18), b: Expr::Col(12) })
}

/// `l_shipdate >= $2`.
pub open spec fn li_ge_pred(p1: Literal) -> Pred {
    Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(26), b: Expr::Lit(p1) }
}

/// `$2 + INTERVAL '1' YEAR` (the date cast to a timestamp).
pub open spec fn year_end(p1: Literal) -> Expr {
    Expr::AddInterval {
        arg: Box::new(Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(p1)) }),
        months: 12i32, days: 0i32, micros: 0i64,
    }
}

/// `l_shipdate < $2 + INTERVAL '1' YEAR`.
pub open spec fn li_lt_pred(p1: Literal) -> Pred {
    Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(26), b: year_end(p1) }
}

/// The lineitem subquery's WHERE.
pub open spec fn li_pred(p1: Literal) -> Pred {
    and(and(li_key_pred(), li_ge_pred(p1)), li_lt_pred(p1))
}

pub open spec fn li_filter(p1: Literal) -> Query {
    Query::Filter { pred: li_pred(p1), input: Box::new(Query::Table(0)) }
}

/// `SUM(l_quantity)`.
pub open spec fn li_aggs() -> Seq<Agg> {
    seq![Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(20) }]
}

pub open spec fn li_agg(p1: Literal) -> Query {
    Query::Aggregate { aggs: li_aggs(), input: Box::new(li_filter(p1)) }
}

/// The literal `0.5`.
pub open spec fn half_lit() -> Literal { Literal::Num { coeff: 5, scale: 1 } }

/// `0.5 * SUM(..)` over the aggregate row.
pub open spec fn half_mul() -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Lit(half_lit())), b: Box::new(Expr::Col(16)) }
}

/// `SELECT 0.5 * SUM(l_quantity) FROM lineitem WHERE ..`.
pub open spec fn li_sub(p1: Literal) -> Query {
    Query::Project { exprs: seq![half_mul()], input: Box::new(li_agg(p1)) }
}

// ------------------------------------------------------------------------------------------ part subquery

/// The escape string of `LIKE` (a backslash).
pub open spec fn esc_lit() -> Literal { Literal::Text(seq![92u8]) }

/// `p_name LIKE $1`.
pub open spec fn like_expr(p0: Literal) -> Expr {
    Expr::Call { f: ScalarFn::Like, args: seq![Expr::Col(17), Expr::Lit(p0), Expr::Lit(esc_lit())] }
}

pub open spec fn part_pred(p0: Literal) -> Pred { Pred::OfBool(like_expr(p0)) }

pub open spec fn part_filter(p0: Literal) -> Query {
    Query::Filter { pred: part_pred(p0), input: Box::new(Query::Table(3)) }
}

/// `SELECT p_partkey FROM part WHERE p_name LIKE $1`.
pub open spec fn part_sub(p0: Literal) -> Query {
    Query::Project { exprs: seq![Expr::Col(16)], input: Box::new(part_filter(p0)) }
}

// ------------------------------------------------------------------------------------------ partsupp subquery

/// `ps_partkey IN (part_sub)`.
pub open spec fn ps_in_pred(p0: Literal) -> Pred {
    Pred::AnyCmp { op: CmpOp::Eq, e: Expr::Col(11), q: Box::new(part_sub(p0)) }
}

/// `ps_availqty::numeric`.
pub open spec fn aq_cast() -> Expr {
    Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Col(13)) }
}

/// `ps_availqty > (li_sub)`.
pub open spec fn ps_gt_pred(p1: Literal) -> Pred {
    Pred::Cmp { op: CmpOp::Gt, a: aq_cast(), b: Expr::Subquery(Box::new(li_sub(p1))) }
}

pub open spec fn ps_pred(ps: Seq<Literal>) -> Pred { and(ps_in_pred(ps[0]), ps_gt_pred(ps[1])) }

pub open spec fn ps_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: ps_pred(ps), input: Box::new(Query::Table(4)) }
}

/// `SELECT ps_suppkey FROM partsupp WHERE ..`.
pub open spec fn ps_sub(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: seq![Expr::Col(12)], input: Box::new(ps_filter(ps)) }
}

// ------------------------------------------------------------------------------------------ outer query

/// `s_suppkey IN (ps_sub)`.
pub open spec fn out_in_pred(ps: Seq<Literal>) -> Pred {
    Pred::AnyCmp { op: CmpOp::Eq, e: Expr::Col(0), q: Box::new(ps_sub(ps)) }
}

/// `s_nationkey = n_nationkey`.
pub open spec fn out_nat_pred() -> Pred { Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(3), b: Expr::Col(7) } }

/// `n_name = $3`.
pub open spec fn out_name_pred(p2: Literal) -> Pred { Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(8), b: Expr::Lit(p2) } }

pub open spec fn out_pred(ps: Seq<Literal>) -> Pred {
    and(and(out_in_pred(ps), out_nat_pred()), out_name_pred(ps[2]))
}

/// `FROM supplier, nation`.
pub open spec fn out_from() -> Query {
    Query::Product { left: Box::new(Query::Table(5)), right: Box::new(Query::Table(6)) }
}

pub open spec fn out_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: out_pred(ps), input: Box::new(out_from()) }
}

/// `SELECT s_name, s_address`.
pub open spec fn out_exprs() -> Seq<Expr> { seq![Expr::Col(1), Expr::Col(2)] }

pub open spec fn q_body(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: out_exprs(), input: Box::new(out_filter(ps)) }
}

/// `ORDER BY s_name`.
pub open spec fn q_keys() -> Seq<OrderKey> { seq![OrderKey { col: 0, desc: false, nulls_first: false }] }

/// The statement is this tree, ordered by `s_name`, without LIMIT or OFFSET.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures query_spec_at(ps) == (OrderedQuery { body: q_body(ps), keys: q_keys(), limit: None, offset: 0 }),
{
}

} // verus!
