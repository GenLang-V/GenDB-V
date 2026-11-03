//! The resolved, typed SQL AST: the shared interface between the frontend (which emits it) and the
//! semantics/evaluator (which give it meaning). Names, scopes, implicit casts and operator overloading are
//! resolved: columns are positions in the environment `outer context ++ current row`, every operator names
//! its operand type, and every PostgreSQL implicit cast is an explicit `Cast` node.
//!
//! The constructors compose freely: any nesting, any number of children, no size/depth/arity limit. `Expr`,
//! `Pred` and `Query` are mutually recursive (a scalar subquery is an `Expr`, a CASE condition a `Pred`), and
//! so are their denotation, typing, domain and executable evaluator.
//! Exec mirror: `exec::ast` (same constructors; `Vec` for `Seq`, machine literals) with a structural view.
//! Constructors outside this file are not supported; the frontend refuses them by name. The operator tags
//! (`IntKind`, `NumKind`, `ArithOp`, `CmpOp`, `CastOp`) are defined next to their meaning in `spec::int` and
//! `spec::scalar`.
//!
//! Every constructor has a denotation (`spec::eval`) and a typing rule (`spec::typing`). What a particular
//! statement may use is decided per statement: the frontend's named refusals, the typing check `wf_ordered`
//! and the bindable source columns. A typed constructor is not a claim that any implementation or proof for it
//! exists.
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::int::*;
use crate::spec::scalar::*;

verus! {

/// Literal constants, carried as source components; the spec computes their values.
pub enum Literal {
    /// Typed `NULL` (the type the resolver assigned, e.g. `NULL::integer`).
    Null { ty: ScalarTy },
    Bool(bool),
    /// Integer literal of type `kind` (`int4` if it fits, else `int8`; larger literals are numeric).
    Int { v: int, kind: IntKind },
    /// Decimal literal `coeff * 10^-scale` (`0.060` is `{60, 3}`).
    Num { coeff: int, scale: nat },
    /// `DATE 'y-m-d'` (civil components; validity is checked by typing).
    Date { y: int, m: int, d: int },
    /// String literal bytes (UTF-8). For comparison with `char(n)` the resolver right-trims spaces.
    Text(Seq<u8>),
}

/// Leaf scalar functions of `Expr::Call` (operand types resolved by the frontend; meaning `spec::fns`).
#[derive(Clone, Copy)]
pub enum ScalarFn {
    /// `int4 / int4` (truncating; 22012 on a zero divisor).
    DivInt4,
    /// `int8 / int8`.
    DivInt8,
    /// `numeric / numeric` (PostgreSQL `select_div_scale`, rounded half away from zero).
    DivNumeric,
    /// `s LIKE p ESCAPE esc` -> bool.
    Like,
    /// `SUBSTRING(s FROM start)`.
    Substring2,
    /// `SUBSTRING(s FROM start FOR len)`.
    Substring3,
    /// `EXTRACT(YEAR FROM d)` -> numeric scale 0.
    ExtractYear,
    ExtractMonth,
    ExtractDay,
    /// `char(n)` value padded with spaces to `n` characters.
    PadBpchar,
}

/// Scalar expressions.
pub enum Expr {
    /// Position `i` of the environment `ctx ++ row`.
    Col(nat),
    Lit(Literal),
    /// Unary minus at operand type `kind`.
    Neg { kind: NumKind, arg: Box<Expr> },
    /// `a op b`, both operands of type `kind`.
    Arith { op: ArithOp, kind: NumKind, a: Box<Expr>, b: Box<Expr> },
    Cast { cast: CastOp, arg: Box<Expr> },
    /// `timestamp + interval` with PostgreSQL's interval fields (`INTERVAL '1' YEAR` = 12 months).
    AddInterval { arg: Box<Expr>, months: i32, days: i32, micros: i64 },
    /// Leaf scalar function over the argument values (arguments left to right).
    Call { f: ScalarFn, args: Seq<Expr> },
    /// Searched CASE with one branch: `CASE WHEN cond THEN then_e ELSE else_e END` (lazy: only the taken branch
    /// is evaluated).
    If { cond: Box<Pred>, then_e: Box<Expr>, else_e: Box<Expr> },
    /// Scalar subquery (one column); sees the current environment as its context (correlation).
    Subquery(Box<Query>),
}

/// Conditions (three-valued).
pub enum Pred {
    Cmp { op: CmpOp, a: Expr, b: Expr },
    And(Box<Pred>, Box<Pred>),
    Or(Box<Pred>, Box<Pred>),
    Not(Box<Pred>),
    /// `e IS NULL` (two-valued). `IS NOT NULL` is `Not(IsNull(e))`.
    IsNull(Expr),
    /// A boolean expression used as a condition (NULL is `Unknown`).
    OfBool(Expr),
    /// `EXISTS (q)`; `q` sees the current environment as its context (correlation).
    Exists(Box<Query>),
    /// `e op ANY (q)` (`IN` is `AnyCmp` with `Eq`); `q` sees the current environment as its context.
    AnyCmp { op: CmpOp, e: Expr, q: Box<Query> },
}

/// Aggregates. Result types: `COUNT` -> int8; `SUM(int4)` -> int8; `SUM(int8)` -> numeric (scale 0);
/// `SUM(numeric)` -> numeric (the input's scale). SUM is exact; only its final value is range-checked.
pub enum Agg {
    CountStar,
    Count(Expr),
    Sum { kind: NumKind, arg: Expr },
    Min(Expr),
    Max(Expr),
    Avg { kind: NumKind, arg: Expr },
    /// `agg(DISTINCT ...)`: the inner aggregate over the non-NULL values, one per not-distinct class
    /// (`spec::equality::distinct_vals`).
    DistinctAgg(Box<Agg>),
}

/// Relational queries (bag semantics: the result is a sequence whose order is canonical but only its
/// multiset is observable, except through the top-level `OrderedQuery`).
pub enum Query {
    /// Base table by id (DDL order).
    Table(nat),
    /// `WHERE` / `HAVING` / `ON` of inner joins: keep rows whose condition is `True`.
    Filter { pred: Pred, input: Box<Query> },
    /// `SELECT e1, ..., en` (one output row per input row).
    Project { exprs: Seq<Expr>, input: Box<Query> },
    /// Cross product (left-major); inner join = `Filter` over `Product`. Non-lateral: `right` sees only `ctx`.
    Product { left: Box<Query>, right: Box<Query> },
    /// `left LEFT JOIN right ON on`: unmatched left rows are padded with NULLs.
    LeftJoin { left: Box<Query>, right: Box<Query>, on: Pred },
    /// Aggregation without GROUP BY: exactly one row, also on empty input.
    Aggregate { aggs: Seq<Agg>, input: Box<Query> },
    /// `GROUP BY keys`: one row `keys ++ aggs` per class of not-distinct key tuples (`spec::equality`: NULLs
    /// group together, numerics by value), groups in first-occurrence order; the first member's key represents
    /// the group.
    GroupBy { keys: Seq<Expr>, aggs: Seq<Agg>, input: Box<Query> },
    /// `SELECT DISTINCT`: one row per not-distinct class (`spec::equality`), first occurrence.
    Distinct(Box<Query>),
}

/// One `ORDER BY` key: an output column, direction and NULL placement (defaults filled by the resolver:
/// ASC NULLS LAST, DESC NULLS FIRST).
pub struct OrderKey {
    pub col: nat,
    pub desc: bool,
    pub nulls_first: bool,
}

/// A top-level statement: body plus `ORDER BY` / `LIMIT` / `OFFSET` (only at top level).
pub struct OrderedQuery {
    pub body: Query,
    pub keys: Seq<OrderKey>,
    pub limit: Option<nat>,
    pub offset: nat,
}

} // verus!
