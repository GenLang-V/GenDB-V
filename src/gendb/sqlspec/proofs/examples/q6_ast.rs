//! TPC-H Q6 (standard text, `benchmarks/tpc-h/{schema,queries}.sql`) as the AST the translator emits, in both
//! forms: the spec constant and the exec constructor proved equal to it. This is the emission pattern of
//! `gendb_frontend::translator`: a flat let-chain of nodes, children before parents, each followed by one view
//! equality. lineitem = table 7; columns 4 l_quantity, 5 l_extendedprice, 6 l_discount (numeric(15,2)),
//! 10 l_shipdate (date).
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::int::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::exec::ast::*;

verus! {

pub open spec fn q6_spec() -> OrderedQuery {
    let n0 = Expr::Col(10);
    let n1 = Expr::Lit(Literal::Date { y: 1994, m: 1, d: 1 });
    let n2 = Pred::Cmp { op: CmpOp::Ge, a: n0, b: n1 };
    let n3 = Expr::Col(10);
    let n4 = Expr::Lit(Literal::Date { y: 1994, m: 1, d: 1 });
    let n5 = Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(n4) };
    let n6 = Expr::AddInterval { arg: Box::new(n5), months: 12, days: 0, micros: 0 };
    let n7 = Pred::Cmp { op: CmpOp::Lt, a: n3, b: n6 };
    let n8 = Pred::And(Box::new(n2), Box::new(n7));
    let n9 = Expr::Col(6);
    let n10 = Expr::Lit(Literal::Num { coeff: 6, scale: 2 });
    let n11 = Expr::Lit(Literal::Num { coeff: 1, scale: 2 });
    let n12 = Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(n10), b: Box::new(n11) };
    let n13 = Pred::Cmp { op: CmpOp::Ge, a: n9, b: n12 };
    let n14 = Expr::Col(6);
    let n15 = Expr::Lit(Literal::Num { coeff: 6, scale: 2 });
    let n16 = Expr::Lit(Literal::Num { coeff: 1, scale: 2 });
    let n17 = Expr::Arith { op: ArithOp::Add, kind: NumKind::Numeric, a: Box::new(n15), b: Box::new(n16) };
    let n18 = Pred::Cmp { op: CmpOp::Le, a: n14, b: n17 };
    let n19 = Pred::And(Box::new(n13), Box::new(n18));
    let n20 = Pred::And(Box::new(n8), Box::new(n19));
    let n21 = Expr::Col(4);
    let n22 = Expr::Lit(Literal::Int { v: 24, kind: IntKind::Int4 });
    let n23 = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(n22) };
    let n24 = Pred::Cmp { op: CmpOp::Lt, a: n21, b: n23 };
    let n25 = Pred::And(Box::new(n20), Box::new(n24));
    let n26 = Query::Table(7);
    let n27 = Query::Filter { pred: n25, input: Box::new(n26) };
    let n28 = Expr::Col(5);
    let n29 = Expr::Col(6);
    let n30 = Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(n28), b: Box::new(n29) };
    let n31 = Agg::Sum { kind: NumKind::Numeric, arg: n30 };
    let n32 = Query::Aggregate { aggs: seq![n31], input: Box::new(n27) };
    OrderedQuery { body: n32, keys: seq![], limit: None, offset: 0 }
}

/// Emission pattern: each exec node is followed by a ghost equality with the spec node (one view unfolding
/// per step), so the proof is linear in the AST size and needs no fuel or `compute`.
pub fn q6_exec() -> (q: EOrderedQuery)
    ensures q@ == q6_spec(),
{
    let ghost g0 = Expr::Col(10);
    let e0 = EExpr::Col(10);
    assert(view_expr(e0) == g0);
    let ghost g1 = Expr::Lit(Literal::Date { y: 1994, m: 1, d: 1 });
    let e1 = EExpr::Lit(ELiteral::Date { y: 1994, m: 1, d: 1 });
    assert(view_expr(e1) == g1);
    let ghost g2 = Pred::Cmp { op: CmpOp::Ge, a: g0, b: g1 };
    let e2 = EPred::Cmp { op: CmpOp::Ge, a: e0, b: e1 };
    assert(view_pred(e2) == g2);
    let ghost g3 = Expr::Col(10);
    let e3 = EExpr::Col(10);
    assert(view_expr(e3) == g3);
    let ghost g4 = Expr::Lit(Literal::Date { y: 1994, m: 1, d: 1 });
    let e4 = EExpr::Lit(ELiteral::Date { y: 1994, m: 1, d: 1 });
    assert(view_expr(e4) == g4);
    let ghost g5 = Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(g4) };
    let e5 = EExpr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(e4) };
    assert(view_expr(e5) == g5);
    let ghost g6 = Expr::AddInterval { arg: Box::new(g5), months: 12, days: 0, micros: 0 };
    let e6 = EExpr::AddInterval { arg: Box::new(e5), months: 12, days: 0, micros: 0 };
    assert(view_expr(e6) == g6);
    let ghost g7 = Pred::Cmp { op: CmpOp::Lt, a: g3, b: g6 };
    let e7 = EPred::Cmp { op: CmpOp::Lt, a: e3, b: e6 };
    assert(view_pred(e7) == g7);
    let ghost g8 = Pred::And(Box::new(g2), Box::new(g7));
    let e8 = EPred::And(Box::new(e2), Box::new(e7));
    assert(view_pred(e8) == g8);
    let ghost g9 = Expr::Col(6);
    let e9 = EExpr::Col(6);
    assert(view_expr(e9) == g9);
    let ghost g10 = Expr::Lit(Literal::Num { coeff: 6, scale: 2 });
    let e10 = EExpr::Lit(ELiteral::Num { coeff: 6, scale: 2 });
    assert(view_expr(e10) == g10);
    let ghost g11 = Expr::Lit(Literal::Num { coeff: 1, scale: 2 });
    let e11 = EExpr::Lit(ELiteral::Num { coeff: 1, scale: 2 });
    assert(view_expr(e11) == g11);
    let ghost g12 = Expr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(g10), b: Box::new(g11) };
    let e12 = EExpr::Arith { op: ArithOp::Sub, kind: NumKind::Numeric, a: Box::new(e10), b: Box::new(e11) };
    assert(view_expr(e12) == g12);
    let ghost g13 = Pred::Cmp { op: CmpOp::Ge, a: g9, b: g12 };
    let e13 = EPred::Cmp { op: CmpOp::Ge, a: e9, b: e12 };
    assert(view_pred(e13) == g13);
    let ghost g14 = Expr::Col(6);
    let e14 = EExpr::Col(6);
    assert(view_expr(e14) == g14);
    let ghost g15 = Expr::Lit(Literal::Num { coeff: 6, scale: 2 });
    let e15 = EExpr::Lit(ELiteral::Num { coeff: 6, scale: 2 });
    assert(view_expr(e15) == g15);
    let ghost g16 = Expr::Lit(Literal::Num { coeff: 1, scale: 2 });
    let e16 = EExpr::Lit(ELiteral::Num { coeff: 1, scale: 2 });
    assert(view_expr(e16) == g16);
    let ghost g17 = Expr::Arith { op: ArithOp::Add, kind: NumKind::Numeric, a: Box::new(g15), b: Box::new(g16) };
    let e17 = EExpr::Arith { op: ArithOp::Add, kind: NumKind::Numeric, a: Box::new(e15), b: Box::new(e16) };
    assert(view_expr(e17) == g17);
    let ghost g18 = Pred::Cmp { op: CmpOp::Le, a: g14, b: g17 };
    let e18 = EPred::Cmp { op: CmpOp::Le, a: e14, b: e17 };
    assert(view_pred(e18) == g18);
    let ghost g19 = Pred::And(Box::new(g13), Box::new(g18));
    let e19 = EPred::And(Box::new(e13), Box::new(e18));
    assert(view_pred(e19) == g19);
    let ghost g20 = Pred::And(Box::new(g8), Box::new(g19));
    let e20 = EPred::And(Box::new(e8), Box::new(e19));
    assert(view_pred(e20) == g20);
    let ghost g21 = Expr::Col(4);
    let e21 = EExpr::Col(4);
    assert(view_expr(e21) == g21);
    let ghost g22 = Expr::Lit(Literal::Int { v: 24, kind: IntKind::Int4 });
    let e22 = EExpr::Lit(ELiteral::Int { v: 24, kind: IntKind::Int4 });
    assert(view_expr(e22) == g22);
    let ghost g23 = Expr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(g22) };
    let e23 = EExpr::Cast { cast: CastOp::IntToNumeric, arg: Box::new(e22) };
    assert(view_expr(e23) == g23);
    let ghost g24 = Pred::Cmp { op: CmpOp::Lt, a: g21, b: g23 };
    let e24 = EPred::Cmp { op: CmpOp::Lt, a: e21, b: e23 };
    assert(view_pred(e24) == g24);
    let ghost g25 = Pred::And(Box::new(g20), Box::new(g24));
    let e25 = EPred::And(Box::new(e20), Box::new(e24));
    assert(view_pred(e25) == g25);
    let ghost g26 = Query::Table(7);
    let e26 = EQuery::Table(7);
    assert(view_query(e26) == g26);
    let ghost g27 = Query::Filter { pred: g25, input: Box::new(g26) };
    let e27 = EQuery::Filter { pred: e25, input: Box::new(e26) };
    assert(view_query(e27) == g27);
    let ghost g28 = Expr::Col(5);
    let e28 = EExpr::Col(5);
    assert(view_expr(e28) == g28);
    let ghost g29 = Expr::Col(6);
    let e29 = EExpr::Col(6);
    assert(view_expr(e29) == g29);
    let ghost g30 = Expr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(g28), b: Box::new(g29) };
    let e30 = EExpr::Arith { op: ArithOp::Mul, kind: NumKind::Numeric, a: Box::new(e28), b: Box::new(e29) };
    assert(view_expr(e30) == g30);
    let ghost g31 = Agg::Sum { kind: NumKind::Numeric, arg: g30 };
    let e31 = EAgg::Sum { kind: NumKind::Numeric, arg: e30 };
    assert(view_agg(e31) == g31);
    let ghost g32 = Query::Aggregate { aggs: seq![g31], input: Box::new(g27) };
    let l32 = vec![e31];
    assert(view_aggs(l32@) =~= seq![g31]);
    let e32 = EQuery::Aggregate { aggs: l32, input: Box::new(e27) };
    assert(view_query(e32) == g32);
    let q = EOrderedQuery { body: e32, keys: Vec::new(), limit: None, offset: 0 };
    assert(q@.keys =~= q6_spec().keys);
    q
}

} // verus!
