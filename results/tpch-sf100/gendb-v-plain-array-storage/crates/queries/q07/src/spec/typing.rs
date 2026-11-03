//! Static typing of the AST (deterministic functions) and the input domain of databases.
//!
//! `type_expr`, `type_exprs`, `type_agg`, `type_aggs`, `type_pred` and `type_query` are one mutual recursion
//! over the schema. `ScalarTy::Numeric { scale }` is an upper bound on the display scale (`spec::types`). The
//! rules of scalar functions and of MIN/MAX/AVG/DISTINCT aggregates live in `spec::fns` and `spec::aggs`.
//! A checked statement is one for which `wf_ordered` holds and a well-formed database one for which `db_wf`
//! holds; the evaluator's theorems are stated for both, and the frontend must emit ASTs that satisfy these
//! rules. The verified executable checkers `exec::relational::check::{check_ordered, check_db}` decide them;
//! type soundness is proved in `bridge::typing`.
use vstd::prelude::*;
use crate::spec::limits::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::datetime::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::fns::*;
use crate::spec::aggs::avg::*;
use crate::spec::aggs::minmax::*;
use crate::spec::aggs::distinct::*;

verus! {

// ------------------------------------------------------------------ types of literals and operators

/// The non-nullable column type of `ty`.
pub open spec fn nn(ty: ScalarTy) -> ColTy {
    ColTy { ty, nullable: false }
}

/// Static type of a literal; `None` for an invalid literal.
pub open spec fn type_lit(l: Literal) -> Option<ColTy> {
    match l {
        Literal::Null { ty } => Some(ColTy { ty, nullable: true }),
        Literal::Bool(_) => Some(nn(ScalarTy::Bool)),
        Literal::Int { v, kind } =>
            if !int_in_range(kind, v) { None } else {
                Some(nn(match kind { IntKind::Int4 => ScalarTy::Int4, IntKind::Int8 => ScalarTy::Int8 }))
            },
        Literal::Num { coeff, scale } =>
            if scale <= numeric_dscale_max() && num_in_range(coeff, scale) {
                Some(nn(ScalarTy::Numeric { scale: scale as u32 }))
            } else {
                None
            },
        Literal::Date { y, m, d } =>
            if valid_ymd(y, m, d) && date_valid(date_from_civil(y, m, d)) { Some(nn(ScalarTy::Date)) } else { None },
        Literal::Text(_) => Some(nn(ScalarTy::Text)),
    }
}

/// Operand type of a numeric operator kind; `Numeric` accepts every static scale.
pub open spec fn kind_accepts(kind: NumKind, t: ScalarTy) -> bool {
    match (kind, t) {
        (NumKind::Int4, ScalarTy::Int4) => true,
        (NumKind::Int8, ScalarTy::Int8) => true,
        (NumKind::Numeric, ScalarTy::Numeric { .. }) => true,
        _ => false,
    }
}

/// Display-scale bound of a numeric type (0 otherwise).
pub open spec fn scale_of(t: ScalarTy) -> nat {
    match t {
        ScalarTy::Numeric { scale } => scale as nat,
        _ => 0,
    }
}

/// Result type of `a op b` at `kind`; numeric result scales above PostgreSQL's display-scale limit are
/// refused (`numeric_scale_limit`).
pub open spec fn arith_ty(op: ArithOp, kind: NumKind, ta: ScalarTy, tb: ScalarTy) -> Option<ScalarTy> {
    if !kind_accepts(kind, ta) || !kind_accepts(kind, tb) {
        None
    } else {
        match kind {
            NumKind::Numeric => {
                let s = match op {
                    ArithOp::Mul => scale_of(ta) + scale_of(tb),
                    _ => max_nat(scale_of(ta), scale_of(tb)),
                };
                if s <= numeric_dscale_max() { Some(ScalarTy::Numeric { scale: s as u32 }) } else { None }
            },
            _ => Some(ta),
        }
    }
}

/// Result type of a cast of an operand of type `t`.
pub open spec fn cast_ty(op: CastOp, t: ScalarTy) -> Option<ScalarTy> {
    match (op, t) {
        (CastOp::Int4ToInt8, ScalarTy::Int4) => Some(ScalarTy::Int8),
        (CastOp::IntToNumeric, ScalarTy::Int4) => Some(ScalarTy::Numeric { scale: 0 }),
        (CastOp::IntToNumeric, ScalarTy::Int8) => Some(ScalarTy::Numeric { scale: 0 }),
        (CastOp::DateToTimestamp, ScalarTy::Date) => Some(ScalarTy::Timestamp),
        _ => None,
    }
}

/// Comparison families (§ spec::scalar::compare).
pub open spec fn family(t: ScalarTy) -> int {
    match t {
        ScalarTy::Bool => 0,
        ScalarTy::Int4 => 1,
        ScalarTy::Int8 => 1,
        ScalarTy::Numeric { .. } => 1,
        ScalarTy::Date => 2,
        ScalarTy::Timestamp => 2,
        ScalarTy::Text => 3,
    }
}

// ------------------------------------------------------------------ types of compound constructors

/// Branch types of one `ScalarTy` shape: equal, or both numeric (the scale bounds may differ).
pub open spec fn same_shape(a: ScalarTy, b: ScalarTy) -> bool {
    match (a, b) {
        (ScalarTy::Numeric { .. }, ScalarTy::Numeric { .. }) => true,
        _ => a == b,
    }
}

/// Type of `CASE WHEN cond THEN a ELSE b END`: a typed condition and branches of one shape (the frontend inserts
/// PostgreSQL's common-type casts); the numeric scale bound is the larger one; nullable if either branch is.
pub open spec fn if_ty(cond_ok: bool, then_t: Option<ColTy>, else_t: Option<ColTy>) -> Option<ColTy> {
    match (then_t, else_t) {
        (Some(a), Some(b)) =>
            if cond_ok && same_shape(a.ty, b.ty) {
                Some(ColTy {
                    ty: match (a.ty, b.ty) {
                        (ScalarTy::Numeric { scale: x }, ScalarTy::Numeric { scale: y }) =>
                            ScalarTy::Numeric { scale: if x >= y { x } else { y } },
                        _ => a.ty,
                    },
                    nullable: a.nullable || b.nullable,
                })
            } else {
                None
            },
        _ => None,
    }
}

/// Type of a scalar subquery: exactly one output column; nullable (no row gives NULL).
pub open spec fn subquery_ty(q: Option<Seq<ColTy>>) -> Option<ColTy> {
    match q {
        Some(tys) => if tys.len() == 1 { Some(ColTy { ty: tys[0].ty, nullable: true }) } else { None },
        None => None,
    }
}

/// Typing of `e op ANY (q)`: a typed operand and a one-column subquery of the same comparison family.
pub open spec fn any_cmp_ok(op: CmpOp, e: Option<ColTy>, q: Option<Seq<ColTy>>) -> bool {
    match (e, q) {
        (Some(t), Some(tys)) => tys.len() == 1 && family(t.ty) == family(tys[0].ty),
        _ => false,
    }
}

/// Output types of `SELECT DISTINCT`: the input's (every type has a total value equality within its family).
pub open spec fn distinct_ty(q: Option<Seq<ColTy>>) -> Option<Seq<ColTy>> {
    q
}

/// Column types of a base table.
pub open spec fn table_tys(t: TableSchema) -> Seq<ColTy> {
    t.columns.map_values(|c: Column| col_ty_of(c))
}

/// The same types, all nullable (the right side of a LEFT JOIN).
pub open spec fn nullable_all(tys: Seq<ColTy>) -> Seq<ColTy> {
    tys.map_values(|t: ColTy| ColTy { ty: t.ty, nullable: true })
}

// ------------------------------------------------------------------ the typing recursion

/// Type of an expression under the environment types `env` (`ctx ++ row`); `None` = ill-typed.
pub open spec fn type_expr(schema: Schema, env: Seq<ColTy>, e: Expr) -> Option<ColTy>
    decreases e,
{
    match e {
        Expr::Col(i) => if i < env.len() { Some(env[i as int]) } else { None },
        Expr::Lit(l) => type_lit(l),
        Expr::Neg { kind, arg } => match type_expr(schema, env, *arg) {
            Some(t) => if kind_accepts(kind, t.ty) { Some(t) } else { None },
            None => None,
        },
        Expr::Arith { op, kind, a, b } => match (type_expr(schema, env, *a), type_expr(schema, env, *b)) {
            (Some(ta), Some(tb)) => match arith_ty(op, kind, ta.ty, tb.ty) {
                Some(t) => Some(ColTy { ty: t, nullable: ta.nullable || tb.nullable }),
                None => None,
            },
            _ => None,
        },
        Expr::Cast { cast: op, arg } => match type_expr(schema, env, *arg) {
            Some(t) => match cast_ty(op, t.ty) {
                Some(r) => Some(ColTy { ty: r, nullable: t.nullable }),
                None => None,
            },
            None => None,
        },
        Expr::AddInterval { arg, months, days, micros } => match type_expr(schema, env, *arg) {
            Some(t) => if t.ty is Timestamp { Some(t) } else { None },
            None => None,
        },
        Expr::Call { f, args } => match type_exprs(schema, env, args) {
            Some(ts) => type_fn(f, ts),
            None => None,
        },
        Expr::If { cond, then_e, else_e } =>
            if_ty(type_pred(schema, env, *cond), type_expr(schema, env, *then_e), type_expr(schema, env, *else_e)),
        Expr::Subquery(q) => subquery_ty(type_query(schema, env, *q)),
    }
}

/// Types of a list of expressions (all must type). Recursive rather than quantified, so that `by (compute)`
/// can decide typing of concrete ASTs.
pub open spec fn type_exprs(schema: Schema, env: Seq<ColTy>, es: Seq<Expr>) -> Option<Seq<ColTy>>
    decreases es,
{
    if es.len() == 0 {
        Some(Seq::empty())
    } else {
        match (type_exprs(schema, env, es.drop_last()), type_expr(schema, env, es.last())) {
            (Some(ts), Some(t)) => Some(ts.push(t)),
            _ => None,
        }
    }
}

/// Result type of an aggregate over rows of environment types `env` (types in `spec::ast::Agg`).
pub open spec fn type_agg(schema: Schema, env: Seq<ColTy>, a: Agg) -> Option<ColTy>
    decreases a,
{
    match a {
        Agg::CountStar => Some(nn(ScalarTy::Int8)),
        Agg::Count(e) => if type_expr(schema, env, e) is Some { Some(nn(ScalarTy::Int8)) } else { None },
        Agg::Sum { kind, arg } => match type_expr(schema, env, arg) {
            Some(t) => if !kind_accepts(kind, t.ty) { None } else {
                Some(ColTy {
                    ty: match kind {
                        NumKind::Int4 => ScalarTy::Int8,
                        NumKind::Int8 => ScalarTy::Numeric { scale: 0 },
                        NumKind::Numeric => t.ty,
                    },
                    nullable: true,
                })
            },
            None => None,
        },
        Agg::Min(e) => match type_expr(schema, env, e) {
            Some(t) => minmax_ty(t),
            None => None,
        },
        Agg::Max(e) => match type_expr(schema, env, e) {
            Some(t) => minmax_ty(t),
            None => None,
        },
        Agg::Avg { kind, arg } => match type_expr(schema, env, arg) {
            Some(t) => avg_ty(kind, t),
            None => None,
        },
        Agg::DistinctAgg(inner) => match type_agg(schema, env, *inner) {
            Some(t) => distinct_agg_ty(*inner, t),
            None => None,
        },
    }
}

/// Types of a list of aggregates (all must type; recursive like `type_exprs`).
pub open spec fn type_aggs(schema: Schema, env: Seq<ColTy>, aggs: Seq<Agg>) -> Option<Seq<ColTy>>
    decreases aggs,
{
    if aggs.len() == 0 {
        Some(Seq::empty())
    } else {
        match (type_aggs(schema, env, aggs.drop_last()), type_agg(schema, env, aggs.last())) {
            (Some(ts), Some(t)) => Some(ts.push(t)),
            _ => None,
        }
    }
}

/// A condition is well-typed under the environment types `env`.
pub open spec fn type_pred(schema: Schema, env: Seq<ColTy>, p: Pred) -> bool
    decreases p,
{
    match p {
        Pred::Cmp { op, a, b } => match (type_expr(schema, env, a), type_expr(schema, env, b)) {
            (Some(ta), Some(tb)) => family(ta.ty) == family(tb.ty),
            _ => false,
        },
        Pred::And(a, b) => type_pred(schema, env, *a) && type_pred(schema, env, *b),
        Pred::Or(a, b) => type_pred(schema, env, *a) && type_pred(schema, env, *b),
        Pred::Not(a) => type_pred(schema, env, *a),
        Pred::IsNull(e) => type_expr(schema, env, e) is Some,
        Pred::OfBool(e) => match type_expr(schema, env, e) {
            Some(t) => t.ty is Bool,
            None => false,
        },
        Pred::Exists(q) => type_query(schema, env, *q) is Some,
        Pred::AnyCmp { op, e, q } => any_cmp_ok(op, type_expr(schema, env, e), type_query(schema, env, *q)),
    }
}

/// Output column types of a query under outer context types `ctx`.
pub open spec fn type_query(schema: Schema, ctx: Seq<ColTy>, q: Query) -> Option<Seq<ColTy>>
    decreases q,
{
    match q {
        Query::Table(t) => if t < schema.len() { Some(table_tys(schema[t as int])) } else { None },
        Query::Filter { pred, input } => match type_query(schema, ctx, *input) {
            Some(tys) => if type_pred(schema, ctx + tys, pred) { Some(tys) } else { None },
            None => None,
        },
        Query::Project { exprs, input } => match type_query(schema, ctx, *input) {
            Some(tys) => type_exprs(schema, ctx + tys, exprs),
            None => None,
        },
        Query::Product { left, right } => match (type_query(schema, ctx, *left), type_query(schema, ctx, *right)) {
            (Some(l), Some(r)) => Some(l + r),
            _ => None,
        },
        Query::LeftJoin { left, right, on } => match (type_query(schema, ctx, *left), type_query(schema, ctx, *right)) {
            (Some(l), Some(r)) => if type_pred(schema, ctx + l + r, on) { Some(l + nullable_all(r)) } else { None },
            _ => None,
        },
        Query::Aggregate { aggs, input } => match type_query(schema, ctx, *input) {
            Some(tys) => type_aggs(schema, ctx + tys, aggs),
            None => None,
        },
        Query::GroupBy { keys, aggs, input } => match type_query(schema, ctx, *input) {
            Some(tys) => match (type_exprs(schema, ctx + tys, keys), type_aggs(schema, ctx + tys, aggs)) {
                (Some(k), Some(a)) => Some(k + a),
                _ => None,
            },
            None => None,
        },
        Query::Distinct(input) => distinct_ty(type_query(schema, ctx, *input)),
    }
}

// ------------------------------------------------------------------ checked statements

/// Every ORDER BY key names one of `arity` output columns.
pub open spec fn keys_in_range(keys: Seq<OrderKey>, arity: nat) -> bool
    decreases keys.len(),
{
    keys.len() == 0 || (keys.last().col < arity && keys_in_range(keys.drop_last(), arity))
}

/// A checked top-level statement: well-formed schema, typed body, ORDER BY keys name output columns.
pub open spec fn wf_ordered(schema: Schema, oq: OrderedQuery) -> bool {
    schema_wf(schema) && match type_query(schema, Seq::empty(), oq.body) {
        Some(tys) => keys_in_range(oq.keys, tys.len()),
        None => false,
    }
}

// ------------------------------------------------------------------ database input domain

/// Values a column of declared type `c` may hold (the input domain of databases).
pub open spec fn value_in_column(v: Val, c: Column) -> bool {
    match v {
        Val::Null => c.nullable,
        Val::Bool(_) => c.ty is Bool,
        Val::Int(x) => match c.ty {
            SqlType::Int4 => int_in_range(IntKind::Int4, x),
            SqlType::Int8 => int_in_range(IntKind::Int8, x),
            _ => false,
        },
        Val::Num { coeff, scale } => match c.ty {
            SqlType::Numeric { precision, scale: s } => scale == s as nat && abs(coeff) < pow10(precision as nat),
            _ => false,
        },
        Val::Date(d) => c.ty is Date && date_valid(d),
        Val::Ts(t) => c.ty is Timestamp && ts_valid(t),
        Val::Text(b) => match c.ty {
            SqlType::Text => text_ok(b),
            SqlType::Varchar { max_chars } => text_ok(b) && utf8_chars(b) <= max_chars as nat,
            SqlType::Bpchar { len } => text_ok(b) && utf8_chars(b) <= len as nat && (b.len() == 0 || b.last() != 0x20u8),
            _ => false,
        },
    }
}

/// Text bytes: no NUL byte. UTF-8 well-formedness of stored text is a decoder obligation (the exec text
/// representation is bytes); comparisons are bytewise.
pub open spec fn text_ok(b: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < b.len() ==> #[trigger] b[i] != 0u8
}

/// Code points of well-formed UTF-8 = bytes that are not continuation bytes (`10xxxxxx`, `spec::chars::is_cont`).
/// The range test is written out rather than calling `is_cont`: the two are equal, but admitted proofs were
/// checked against this form, and with the call one of them exceeds the SMT resource limit.
pub open spec fn utf8_chars(b: Seq<u8>) -> nat
    decreases b.len(),
{
    if b.len() == 0 { 0 } else { utf8_chars(b.drop_last()) + if 0x80u8 <= b.last() < 0xC0u8 { 0nat } else { 1nat } }
}

/// A row of table `t`: its arity and every value in its column's domain.
pub open spec fn row_in_table(r: Row, t: TableSchema) -> bool {
    r.len() == t.columns.len() && forall|c: int| 0 <= c < r.len() ==> value_in_column(#[trigger] r[c], t.columns[c])
}

/// Well-formed database: one relation per table, every row in its table's domain.
pub open spec fn db_wf(db: Database) -> bool {
    &&& schema_wf(db.schema)
    &&& db.tables.len() == db.schema.len()
    &&& forall|t: int, i: int| 0 <= t < db.tables.len() && 0 <= i < db.tables[t].len()
        ==> row_in_table(#[trigger] db.tables[t][i], db.schema[t])
}

} // verus!
