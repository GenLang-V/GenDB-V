//! Executable AST: the constructors of `spec::ast` with `Vec`/`Box` children and machine literals, and the
//! structural view onto the spec AST. The views are free spec functions (a recursive `View` impl would be a trait
//! cycle); those of `EExpr`/`EPred`/`EAgg`/`EQuery` are one mutual recursion, and the list views (`view_exprs`,
//! `view_aggs`) are index-guarded for its termination.
//! The literal representation limits (numeric coefficient in `i128`, scale in `u32`) are the only difference from
//! the spec AST; the emitter refuses a literal outside them as `executable_domain` (a static, concrete reason).
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::int::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;

verus! {

/// `spec::ast::Literal` in machine integers. A date literal keeps its civil fields; `lit_exec` validates them.
pub enum ELiteral {
    Null { ty: ScalarTy },
    Bool(bool),
    Int { v: i64, kind: IntKind },
    Num { coeff: i128, scale: u32 },
    Date { y: i32, m: i32, d: i32 },
    Text(Vec<u8>),
}

pub enum EExpr {
    Col(usize),
    Lit(ELiteral),
    Neg { kind: NumKind, arg: Box<EExpr> },
    Arith { op: ArithOp, kind: NumKind, a: Box<EExpr>, b: Box<EExpr> },
    Cast { cast: CastOp, arg: Box<EExpr> },
    AddInterval { arg: Box<EExpr>, months: i32, days: i32, micros: i64 },
    Call { f: ScalarFn, args: Vec<EExpr> },
    If { cond: Box<EPred>, then_e: Box<EExpr>, else_e: Box<EExpr> },
    Subquery(Box<EQuery>),
}

pub enum EPred {
    Cmp { op: CmpOp, a: EExpr, b: EExpr },
    And(Box<EPred>, Box<EPred>),
    Or(Box<EPred>, Box<EPred>),
    Not(Box<EPred>),
    IsNull(EExpr),
    OfBool(EExpr),
    Exists(Box<EQuery>),
    AnyCmp { op: CmpOp, e: EExpr, q: Box<EQuery> },
}

pub enum EAgg {
    CountStar,
    Count(EExpr),
    Sum { kind: NumKind, arg: EExpr },
    Min(EExpr),
    Max(EExpr),
    Avg { kind: NumKind, arg: EExpr },
    DistinctAgg(Box<EAgg>),
}

pub enum EQuery {
    Table(usize),
    Filter { pred: EPred, input: Box<EQuery> },
    Project { exprs: Vec<EExpr>, input: Box<EQuery> },
    Product { left: Box<EQuery>, right: Box<EQuery> },
    LeftJoin { left: Box<EQuery>, right: Box<EQuery>, on: EPred },
    Aggregate { aggs: Vec<EAgg>, input: Box<EQuery> },
    GroupBy { keys: Vec<EExpr>, aggs: Vec<EAgg>, input: Box<EQuery> },
    Distinct(Box<EQuery>),
}

/// One ORDER BY key: output column, direction and NULL placement (`spec::ast::OrderKey`).
pub struct EOrderKey {
    pub col: usize,
    pub desc: bool,
    pub nulls_first: bool,
}

/// A query body with top-level ORDER BY / LIMIT / OFFSET (`spec::ast::OrderedQuery`).
pub struct EOrderedQuery {
    pub body: EQuery,
    pub keys: Vec<EOrderKey>,
    pub limit: Option<u64>,
    pub offset: u64,
}

pub open spec fn view_lit(l: ELiteral) -> Literal {
    match l {
        ELiteral::Null { ty } => Literal::Null { ty },
        ELiteral::Bool(b) => Literal::Bool(b),
        ELiteral::Int { v, kind } => Literal::Int { v: v as int, kind },
        ELiteral::Num { coeff, scale } => Literal::Num { coeff: coeff as int, scale: scale as nat },
        ELiteral::Date { y, m, d } => Literal::Date { y: y as int, m: m as int, d: d as int },
        ELiteral::Text(b) => Literal::Text(b@),
    }
}

pub open spec fn view_expr(e: EExpr) -> Expr
    decreases e,
{
    match e {
        EExpr::Col(i) => Expr::Col(i as nat),
        EExpr::Lit(l) => Expr::Lit(view_lit(l)),
        EExpr::Neg { kind, arg } => Expr::Neg { kind, arg: Box::new(view_expr(*arg)) },
        EExpr::Arith { op, kind, a, b } =>
            Expr::Arith { op, kind, a: Box::new(view_expr(*a)), b: Box::new(view_expr(*b)) },
        EExpr::Cast { cast, arg } => Expr::Cast { cast, arg: Box::new(view_expr(*arg)) },
        EExpr::AddInterval { arg, months, days, micros } =>
            Expr::AddInterval { arg: Box::new(view_expr(*arg)), months, days, micros },
        EExpr::Call { f, args } => Expr::Call { f, args: view_exprs(args@) },
        EExpr::If { cond, then_e, else_e } => Expr::If {
            cond: Box::new(view_pred(*cond)),
            then_e: Box::new(view_expr(*then_e)),
            else_e: Box::new(view_expr(*else_e)),
        },
        EExpr::Subquery(q) => Expr::Subquery(Box::new(view_query(*q))),
    }
}

pub open spec fn view_exprs(es: Seq<EExpr>) -> Seq<Expr>
    decreases es,
{
    Seq::new(es.len(), |i: int| if 0 <= i < es.len() { view_expr(es[i]) } else { Expr::Col(0) })
}

pub open spec fn view_agg(a: EAgg) -> Agg
    decreases a,
{
    match a {
        EAgg::CountStar => Agg::CountStar,
        EAgg::Count(e) => Agg::Count(view_expr(e)),
        EAgg::Sum { kind, arg } => Agg::Sum { kind, arg: view_expr(arg) },
        EAgg::Min(e) => Agg::Min(view_expr(e)),
        EAgg::Max(e) => Agg::Max(view_expr(e)),
        EAgg::Avg { kind, arg } => Agg::Avg { kind, arg: view_expr(arg) },
        EAgg::DistinctAgg(inner) => Agg::DistinctAgg(Box::new(view_agg(*inner))),
    }
}

pub open spec fn view_aggs(aggs: Seq<EAgg>) -> Seq<Agg>
    decreases aggs,
{
    Seq::new(aggs.len(), |j: int| if 0 <= j < aggs.len() { view_agg(aggs[j]) } else { Agg::CountStar })
}

pub open spec fn view_pred(p: EPred) -> Pred
    decreases p,
{
    match p {
        EPred::Cmp { op, a, b } => Pred::Cmp { op, a: view_expr(a), b: view_expr(b) },
        EPred::And(a, b) => Pred::And(Box::new(view_pred(*a)), Box::new(view_pred(*b))),
        EPred::Or(a, b) => Pred::Or(Box::new(view_pred(*a)), Box::new(view_pred(*b))),
        EPred::Not(a) => Pred::Not(Box::new(view_pred(*a))),
        EPred::IsNull(e) => Pred::IsNull(view_expr(e)),
        EPred::OfBool(e) => Pred::OfBool(view_expr(e)),
        EPred::Exists(q) => Pred::Exists(Box::new(view_query(*q))),
        EPred::AnyCmp { op, e, q } => Pred::AnyCmp { op, e: view_expr(e), q: Box::new(view_query(*q)) },
    }
}

pub open spec fn view_query(q: EQuery) -> Query
    decreases q,
{
    match q {
        EQuery::Table(t) => Query::Table(t as nat),
        EQuery::Filter { pred, input } => Query::Filter { pred: view_pred(pred), input: Box::new(view_query(*input)) },
        EQuery::Project { exprs, input } => Query::Project { exprs: view_exprs(exprs@), input: Box::new(view_query(*input)) },
        EQuery::Product { left, right } =>
            Query::Product { left: Box::new(view_query(*left)), right: Box::new(view_query(*right)) },
        EQuery::LeftJoin { left, right, on } =>
            Query::LeftJoin { left: Box::new(view_query(*left)), right: Box::new(view_query(*right)), on: view_pred(on) },
        EQuery::Aggregate { aggs, input } => Query::Aggregate { aggs: view_aggs(aggs@), input: Box::new(view_query(*input)) },
        EQuery::GroupBy { keys, aggs, input } =>
            Query::GroupBy { keys: view_exprs(keys@), aggs: view_aggs(aggs@), input: Box::new(view_query(*input)) },
        EQuery::Distinct(input) => Query::Distinct(Box::new(view_query(*input))),
    }
}

/// Length and elements of the index-guarded list view `view_exprs`.
pub proof fn lemma_view_exprs_index(es: Seq<EExpr>)
    ensures
        view_exprs(es).len() == es.len(),
        forall|i: int| 0 <= i < es.len() ==> #[trigger] view_exprs(es)[i] == view_expr(es[i]),
{
}

/// Length and elements of the index-guarded list view `view_aggs`.
pub proof fn lemma_view_aggs_index(aggs: Seq<EAgg>)
    ensures
        view_aggs(aggs).len() == aggs.len(),
        forall|j: int| 0 <= j < aggs.len() ==> #[trigger] view_aggs(aggs)[j] == view_agg(aggs[j]),
{
}

pub open spec fn view_order_key(k: EOrderKey) -> OrderKey {
    OrderKey { col: k.col as nat, desc: k.desc, nulls_first: k.nulls_first }
}

pub open spec fn view_order_keys(ks: Seq<EOrderKey>) -> Seq<OrderKey> {
    ks.map_values(|k: EOrderKey| view_order_key(k))
}

pub open spec fn view_ordered(q: EOrderedQuery) -> OrderedQuery {
    OrderedQuery {
        body: view_query(q.body),
        keys: view_order_keys(q.keys@),
        limit: match q.limit { Some(n) => Some(n as nat), None => None },
        offset: q.offset as nat,
    }
}

impl View for ELiteral { type V = Literal; open spec fn view(&self) -> Literal { view_lit(*self) } }
impl View for EExpr { type V = Expr; open spec fn view(&self) -> Expr { view_expr(*self) } }
impl View for EPred { type V = Pred; open spec fn view(&self) -> Pred { view_pred(*self) } }
impl View for EAgg { type V = Agg; open spec fn view(&self) -> Agg { view_agg(*self) } }
impl View for EQuery { type V = Query; open spec fn view(&self) -> Query { view_query(*self) } }
impl View for EOrderedQuery { type V = OrderedQuery; open spec fn view(&self) -> OrderedQuery { view_ordered(*self) } }

} // verus!
