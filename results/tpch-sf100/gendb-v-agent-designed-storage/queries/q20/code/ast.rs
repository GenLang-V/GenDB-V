//! The statement's AST in named pieces (`lemma_query_shape` identifies them with the fixed `query_spec_at`).
//!
//! Environments (annotated-ast.txt): the outer rows are `supplier ++ nation` (11 values); the partsupp subquery
//! appends a partsupp row (16 values); the part subquery a part row (25 values); the lineitem subquery a lineitem row
//! (32 values), and its projection the SUM (17 values).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::query::query_spec_at;

verus! {

/// `Col(a) op Col(b)`.
pub open spec fn ccmp(op: CmpOp, a: nat, b: nat) -> Pred {
    Pred::Cmp { op, a: Expr::Col(a), b: Expr::Col(b) }
}

pub open spec fn cand(a: Pred, b: Pred) -> Pred {
    Pred::And(Box::new(a), Box::new(b))
}

/// `p_name LIKE $1` (escape `\`), on `ctx(16) ++ part`.
pub open spec fn like_expr(ps: Seq<Literal>) -> Expr {
    Expr::Call { f: ScalarFn::Like, args: seq![Expr::Col(17), Expr::Lit(ps[0]), Expr::Lit(Literal::Text(seq![92u8]))] }
}

/// `SELECT p_partkey FROM part WHERE p_name LIKE $1`.
pub open spec fn part_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: Pred::OfBool(like_expr(ps)), input: Box::new(Query::Table(3)) }
}

pub open spec fn part_q(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: seq![Expr::Col(16)], input: Box::new(part_filter(ps)) }
}

/// `ps_partkey IN (part_q)`.
pub open spec fn in_part(ps: Seq<Literal>) -> Pred {
    Pred::AnyCmp { op: CmpOp::Eq, e: Expr::Col(11), q: Box::new(part_q(ps)) }
}

/// `$2 + INTERVAL '1' YEAR`.
pub open spec fn hi_expr(ps: Seq<Literal>) -> Expr {
    Expr::AddInterval {
        arg: Box::new(Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(Expr::Lit(ps[1])) }),
        months: 12i32, days: 0i32, micros: 0i64,
    }
}

/// The lineitem subquery's WHERE on `ctx(16) ++ lineitem`.
pub open spec fn li_pred(ps: Seq<Literal>) -> Pred {
    cand(
        cand(
            cand(ccmp(CmpOp::Eq, 17, 11), ccmp(CmpOp::Eq, 18, 12)),
            Pred::Cmp { op: CmpOp::Ge, a: Expr::Col(26), b: Expr::Lit(ps[1]) },
        ),
        Pred::Cmp { op: CmpOp::Lt, a: Expr::Col(26), b: hi_expr(ps) },
    )
}

pub open spec fn li_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: li_pred(ps), input: Box::new(Query::Table(0)) }
}

/// `SUM(l_quantity)`.
pub open spec fn sum_agg() -> Agg {
    Agg::Sum { kind: NumKind::Numeric, arg: Expr::Col(20) }
}

pub open spec fn li_agg(ps: Seq<Literal>) -> Query {
    Query::Aggregate { aggs: seq![sum_agg()], input: Box::new(li_filter(ps)) }
}

/// `0.5 * SUM(..)` on `ctx(16) ++ [sum]`.
pub open spec fn half_expr() -> Expr {
    Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(Expr::Lit(Literal::Num { coeff: 5, scale: 1 })),
        b: Box::new(Expr::Col(16)) }
}

pub open spec fn li_q(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: seq![half_expr()], input: Box::new(li_agg(ps)) }
}

/// `ps_availqty > (li_q)`.
pub open spec fn avail_pred(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Gt, a: Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(Expr::Col(13)) },
        b: Expr::Subquery(Box::new(li_q(ps))) }
}

/// The partsupp subquery's WHERE on `ctx(11) ++ partsupp`.
pub open spec fn ps_pred(ps: Seq<Literal>) -> Pred {
    cand(in_part(ps), avail_pred(ps))
}

pub open spec fn ps_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: ps_pred(ps), input: Box::new(Query::Table(4)) }
}

/// `SELECT ps_suppkey FROM partsupp WHERE ...`.
pub open spec fn ps_q(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: seq![Expr::Col(12)], input: Box::new(ps_filter(ps)) }
}

/// `s_suppkey IN (ps_q)`.
pub open spec fn in_ps(ps: Seq<Literal>) -> Pred {
    Pred::AnyCmp { op: CmpOp::Eq, e: Expr::Col(0), q: Box::new(ps_q(ps)) }
}

/// `n_name = $3`.
pub open spec fn name_pred(ps: Seq<Literal>) -> Pred {
    Pred::Cmp { op: CmpOp::Eq, a: Expr::Col(8), b: Expr::Lit(ps[2]) }
}

/// The outer WHERE on `supplier ++ nation`.
pub open spec fn outer_pred(ps: Seq<Literal>) -> Pred {
    cand(cand(in_ps(ps), ccmp(CmpOp::Eq, 3, 7)), name_pred(ps))
}

pub open spec fn outer_from() -> Query {
    Query::Product { left: Box::new(Query::Table(5)), right: Box::new(Query::Table(6)) }
}

pub open spec fn outer_filter(ps: Seq<Literal>) -> Query {
    Query::Filter { pred: outer_pred(ps), input: Box::new(outer_from()) }
}

/// `SELECT s_name, s_address ...`.
pub open spec fn body_q(ps: Seq<Literal>) -> Query {
    Query::Project { exprs: seq![Expr::Col(1), Expr::Col(2)], input: Box::new(outer_filter(ps)) }
}

/// `ORDER BY s_name`.
pub open spec fn q_keys() -> Seq<OrderKey> {
    seq![OrderKey { col: 0, desc: false, nulls_first: false }]
}

/// The fixed statement is these pieces.
pub proof fn lemma_query_shape(ps: Seq<Literal>)
    ensures query_spec_at(ps) == (OrderedQuery { body: body_q(ps), keys: q_keys(), limit: None, offset: 0nat }),
{
}

} // verus!
