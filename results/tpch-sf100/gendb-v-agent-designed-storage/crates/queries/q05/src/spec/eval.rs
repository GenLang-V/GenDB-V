//! The compositional denotation. Each constructor evaluates its children (left to right, rows in canonical
//! order) and applies one operator from `spec::scalar` / `spec::relation`; the first SQL error in that order is
//! the outcome. Total on every AST; the meaning of a well-typed AST is the claim (`spec::typing`).
//!
//! `eval_expr`, `eval_exprs`, `agg_arg`, `agg_args`, `eval_pred` and `eval_query` are one mutual recursion over
//! the database (an expression may contain a subquery, a CASE condition a predicate). Termination: every call
//! is on a strict sub-AST; list elements are guarded by their index (`es[i]` for `0 <= i < es.len()`).
//!
//! `If` (CASE) is lazy: the condition, then only the taken branch. A scalar subquery and `AnyCmp` evaluate their
//! whole subquery first (with `ctx = env`), then apply `subquery_value` / `any_cmp_truth`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::datetime::*;
use crate::spec::limits::*;
use crate::spec::scalar::*;
use crate::spec::types::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::fns::*;
use crate::spec::equality::*;

verus! {

/// Value of a literal; an invalid literal (out-of-range integer, numeric beyond PostgreSQL's format, invalid
/// date) is ill-typed and refused by typing.
pub open spec fn lit_val(l: Literal) -> Result<Val, SqlError> {
    match l {
        Literal::Null { .. } => Ok(Val::Null),
        Literal::Bool(b) => Ok(Val::Bool(b)),
        Literal::Int { v, kind } => if int_in_range(kind, v) { Ok(Val::Int(v)) } else { Err(SqlError::TypeError) },
        Literal::Num { coeff, scale } =>
            if scale <= numeric_dscale_max() && num_in_range(coeff, scale) {
                Ok(Val::Num { coeff, scale })
            } else {
                Err(SqlError::TypeError)
            },
        Literal::Date { y, m, d } =>
            if valid_ymd(y, m, d) && date_valid(date_from_civil(y, m, d)) {
                Ok(Val::Date(date_from_civil(y, m, d)))
            } else {
                Err(SqlError::TypeError)
            },
        Literal::Text(bytes) => Ok(Val::Text(bytes)),
    }
}

/// Scalar expression under environment `env` (`ctx ++ row`).
pub open spec fn eval_expr(db: Database, env: Row, e: Expr) -> Result<Val, SqlError>
    decreases e,
{
    match e {
        Expr::Col(i) => if i < env.len() { Ok(env[i as int]) } else { Err(SqlError::TypeError) },
        Expr::Lit(l) => lit_val(l),
        Expr::Neg { kind, arg } => match eval_expr(db, env, *arg) {
            Err(err) => Err(err),
            Ok(v) => neg(kind, v),
        },
        Expr::Arith { op, kind, a, b } => match eval_expr(db, env, *a) {
            Err(err) => Err(err),
            Ok(va) => match eval_expr(db, env, *b) {
                Err(err) => Err(err),
                Ok(vb) => arith(op, kind, va, vb),
            },
        },
        Expr::Cast { cast: op, arg } => match eval_expr(db, env, *arg) {
            Err(err) => Err(err),
            Ok(v) => cast(op, v),
        },
        Expr::AddInterval { arg, months, days, micros } => match eval_expr(db, env, *arg) {
            Err(err) => Err(err),
            Ok(v) => add_interval(v, months, days, micros),
        },
        Expr::Call { f, args } => match eval_exprs(db, env, args) {
            Err(err) => Err(err),
            Ok(vs) => apply_fn(f, vs),
        },
        Expr::If { cond, then_e, else_e } => match eval_pred(db, env, *cond) {
            Err(err) => Err(err),
            Ok(Truth::True) => eval_expr(db, env, *then_e),
            Ok(_) => eval_expr(db, env, *else_e),
        },
        Expr::Subquery(q) => match eval_query(db, env, *q) {
            Err(err) => Err(err),
            Ok(rows) => subquery_value(rows),
        },
    }
}

/// The single column of a subquery row (typing guarantees one column; a row without one is ill-typed).
pub open spec fn first_col(r: Row) -> Result<Val, SqlError> {
    if r.len() > 0 { Ok(r[0]) } else { Err(SqlError::TypeError) }
}

/// Value of a scalar subquery from its rows: no row is NULL, one row is its column, more than one row raises
/// `CardinalityViolation` (21000).
pub open spec fn subquery_value(rows: Relation) -> Result<Val, SqlError> {
    if rows.len() == 0 {
        Ok(Val::Null)
    } else if rows.len() == 1 {
        first_col(rows[0])
    } else {
        Err(SqlError::CardinalityViolation)
    }
}

/// `v op ANY (rows)`: the Kleene OR of `v op row[0]` over the rows in order, starting from `False` (so the empty
/// set is `False` even for a NULL `v`, and a NULL element makes a non-match `Unknown`).
pub open spec fn any_cmp_truth(op: CmpOp, v: Val, rows: Relation) -> Result<Truth, SqlError>
    decreases rows.len(),
{
    if rows.len() == 0 {
        Ok(Truth::False)
    } else {
        match any_cmp_truth(op, v, rows.drop_last()) {
            Err(err) => Err(err),
            Ok(t) => match first_col(rows.last()) {
                Err(err) => Err(err),
                Ok(x) => match cmp_truth(op, v, x) {
                    Err(err) => Err(err),
                    Ok(u) => Ok(truth_or(t, u)),
                },
            },
        }
    }
}

/// `SELECT DISTINCT`: one row per not-distinct class (`spec::equality`), the first occurrence, in order.
pub open spec fn distinct_query_rows(rows: Relation) -> Result<Relation, SqlError> {
    Ok(distinct_rows(rows))
}

/// Per-element outcomes of a list of expressions (index-guarded for termination).
pub open spec fn expr_results(db: Database, env: Row, es: Seq<Expr>) -> Seq<Result<Val, SqlError>>
    decreases es, 0nat,
{
    Seq::new(es.len(), |i: int| if 0 <= i < es.len() { eval_expr(db, env, es[i]) } else { Err(SqlError::TypeError) })
}

/// A list of expressions, left to right.
pub open spec fn eval_exprs(db: Database, env: Row, es: Seq<Expr>) -> Result<Row, SqlError>
    decreases es, 1nat,
{
    collect(expr_results(db, env, es))
}

pub proof fn lemma_eval_exprs_empty(db: Database, env: Row)
    ensures eval_exprs(db, env, Seq::empty()) == Ok::<Row, SqlError>(Seq::empty()),
{
    assert(expr_results(db, env, Seq::empty()) =~= Seq::<Result<Val, SqlError>>::empty());
}

/// `eval_exprs` of a non-empty list: the prefix, then the last expression.
pub proof fn lemma_eval_exprs_step(db: Database, env: Row, es: Seq<Expr>)
    requires es.len() > 0,
    ensures
        eval_exprs(db, env, es) == match eval_exprs(db, env, es.drop_last()) {
            Err(e) => Err(e),
            Ok(vs) => match eval_expr(db, env, es.last()) {
                Err(e) => Err(e),
                Ok(v) => Ok(vs.push(v)),
            },
        },
{
    let rs = expr_results(db, env, es);
    let d = es.drop_last();
    assert(rs.drop_last() =~= expr_results(db, env, d));
}

/// Elements of the per-element outcome sequences.
pub proof fn lemma_expr_results_index(db: Database, env: Row, es: Seq<Expr>)
    ensures
        expr_results(db, env, es).len() == es.len(),
        forall|i: int| 0 <= i < es.len() ==> #[trigger] expr_results(db, env, es)[i] == eval_expr(db, env, es[i]),
{
}

pub proof fn lemma_agg_arg_results_index(db: Database, env: Row, aggs: Seq<Agg>)
    ensures
        agg_arg_results(db, env, aggs).len() == aggs.len(),
        forall|j: int| 0 <= j < aggs.len() ==> #[trigger] agg_arg_results(db, env, aggs)[j] == agg_arg(db, env, aggs[j]),
{
}

/// Argument value of one aggregate in one row (`CountStar` has none; `Null` stands in and is ignored).
pub open spec fn agg_arg(db: Database, env: Row, a: Agg) -> Result<Val, SqlError>
    decreases a,
{
    match a {
        Agg::CountStar => Ok(Val::Null),
        Agg::Count(e) => eval_expr(db, env, e),
        Agg::Sum { kind, arg } => eval_expr(db, env, arg),
        Agg::Min(e) => eval_expr(db, env, e),
        Agg::Max(e) => eval_expr(db, env, e),
        Agg::Avg { kind, arg } => eval_expr(db, env, arg),
        Agg::DistinctAgg(inner) => agg_arg(db, env, *inner),
    }
}

/// Per-aggregate argument outcomes of one row (index-guarded for termination).
pub open spec fn agg_arg_results(db: Database, env: Row, aggs: Seq<Agg>) -> Seq<Result<Val, SqlError>>
    decreases aggs, 0nat,
{
    Seq::new(aggs.len(), |j: int| if 0 <= j < aggs.len() { agg_arg(db, env, aggs[j]) } else { Err(SqlError::TypeError) })
}

pub open spec fn agg_args(db: Database, env: Row, aggs: Seq<Agg>) -> Result<Row, SqlError>
    decreases aggs, 1nat,
{
    collect(agg_arg_results(db, env, aggs))
}

/// Per input row of a GROUP BY: its key tuple, then its aggregate arguments. (`eval_query` inlines this body
/// so that the recursion descends into `keys` and `aggs` separately; `lemma_group_input` identifies the two.)
pub open spec fn group_input(db: Database, env: Row, keys: Seq<Expr>, aggs: Seq<Agg>) -> Result<(Row, Row), SqlError> {
    match eval_exprs(db, env, keys) {
        Err(err) => Err(err),
        Ok(k) => match agg_args(db, env, aggs) {
            Err(err) => Err(err),
            Ok(a) => Ok((k, a)),
        },
    }
}

/// Number of output columns of a query (static; needed for LEFT JOIN padding).
pub open spec fn query_arity(schema: Schema, q: Query) -> nat
    decreases q,
{
    match q {
        Query::Table(t) => if t < schema.len() { schema[t as int].columns.len() } else { 0 },
        Query::Filter { pred, input } => query_arity(schema, *input),
        Query::Project { exprs, input } => exprs.len(),
        Query::Product { left, right } => query_arity(schema, *left) + query_arity(schema, *right),
        Query::LeftJoin { left, right, on } => query_arity(schema, *left) + query_arity(schema, *right),
        Query::Aggregate { aggs, input } => aggs.len(),
        Query::GroupBy { keys, aggs, input } => keys.len() + aggs.len(),
        Query::Distinct(input) => query_arity(schema, *input),
    }
}

/// Condition under environment `env`. `AND`/`OR` evaluate both operands (strict; an error in either is the
/// outcome), then combine with Kleene logic.
pub open spec fn eval_pred(db: Database, env: Row, p: Pred) -> Result<Truth, SqlError>
    decreases p,
{
    match p {
        Pred::Cmp { op, a, b } => match eval_expr(db, env, a) {
            Err(err) => Err(err),
            Ok(va) => match eval_expr(db, env, b) {
                Err(err) => Err(err),
                Ok(vb) => cmp_truth(op, va, vb),
            },
        },
        Pred::And(a, b) => match eval_pred(db, env, *a) {
            Err(err) => Err(err),
            Ok(ta) => match eval_pred(db, env, *b) {
                Err(err) => Err(err),
                Ok(tb) => Ok(truth_and(ta, tb)),
            },
        },
        Pred::Or(a, b) => match eval_pred(db, env, *a) {
            Err(err) => Err(err),
            Ok(ta) => match eval_pred(db, env, *b) {
                Err(err) => Err(err),
                Ok(tb) => Ok(truth_or(ta, tb)),
            },
        },
        Pred::Not(a) => match eval_pred(db, env, *a) {
            Err(err) => Err(err),
            Ok(t) => Ok(truth_not(t)),
        },
        Pred::IsNull(e) => match eval_expr(db, env, e) {
            Err(err) => Err(err),
            Ok(v) => Ok(truth_of(v is Null)),
        },
        Pred::OfBool(e) => match eval_expr(db, env, e) {
            Err(err) => Err(err),
            Ok(v) => truth_of_val(v),
        },
        Pred::Exists(q) => match eval_query(db, env, *q) {
            Err(err) => Err(err),
            Ok(rows) => Ok(truth_of(rows.len() > 0)),
        },
        Pred::AnyCmp { op, e, q } => match eval_expr(db, env, e) {
            Err(err) => Err(err),
            Ok(v) => match eval_query(db, env, *q) {
                Err(err) => Err(err),
                Ok(rows) => any_cmp_truth(op, v, rows),
            },
        },
    }
}

/// Query under outer context `ctx` (empty at top level; the outer environment for a correlated subquery).
pub open spec fn eval_query(db: Database, ctx: Row, q: Query) -> Result<Relation, SqlError>
    decreases q,
{
    match q {
        Query::Table(t) => if t < db.tables.len() { Ok(db.tables[t as int]) } else { Err(SqlError::TypeError) },
        Query::Filter { pred, input } => match eval_query(db, ctx, *input) {
            Err(err) => Err(err),
            Ok(rows) => match collect(Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred))) {
                Err(err) => Err(err),
                Ok(truths) => Ok(keep_true(rows, truths)),
            },
        },
        Query::Project { exprs, input } => match eval_query(db, ctx, *input) {
            Err(err) => Err(err),
            Ok(rows) => collect(Seq::new(rows.len(), |i: int| eval_exprs(db, ctx + rows[i], exprs))),
        },
        Query::Product { left, right } => match eval_query(db, ctx, *left) {
            Err(err) => Err(err),
            Ok(l) => match eval_query(db, ctx, *right) {
                Err(err) => Err(err),
                Ok(r) => Ok(product_rows(l, r)),
            },
        },
        Query::LeftJoin { left, right, on } => match eval_query(db, ctx, *left) {
            Err(err) => Err(err),
            Ok(l) => match eval_query(db, ctx, *right) {
                Err(err) => Err(err),
                Ok(r) => match collect(Seq::new(l.len(), |i: int|
                    collect(Seq::new(r.len(), |j: int| eval_pred(db, ctx + l[i] + r[j], on))))) {
                    Err(err) => Err(err),
                    Ok(truths) => Ok(left_join_rows(l, r, truths, query_arity(db.schema, *right))),
                },
            },
        },
        Query::Aggregate { aggs, input } => match eval_query(db, ctx, *input) {
            Err(err) => Err(err),
            Ok(rows) => match collect(Seq::new(rows.len(), |i: int| agg_args(db, ctx + rows[i], aggs))) {
                Err(err) => Err(err),
                Ok(args) => match agg_row(aggs, args) {
                    Err(err) => Err(err),
                    Ok(row) => Ok(seq![row]),
                },
            },
        },
        Query::GroupBy { keys, aggs, input } => match eval_query(db, ctx, *input) {
            Err(err) => Err(err),
            Ok(rows) => match collect(Seq::new(rows.len(), |i: int|
                match eval_exprs(db, ctx + rows[i], keys) {
                    Err(err) => Err(err),
                    Ok(k) => match agg_args(db, ctx + rows[i], aggs) {
                        Err(err) => Err(err),
                        Ok(a) => Ok((k, a)),
                    },
                })) {
                Err(err) => Err(err),
                Ok(prepared) => group_rows(
                    aggs,
                    prepared.map_values(|p: (Row, Row)| p.0),
                    prepared.map_values(|p: (Row, Row)| p.1),
                ),
            },
        },
        Query::Distinct(input) => match eval_query(db, ctx, *input) {
            Err(err) => Err(err),
            Ok(rows) => distinct_query_rows(rows),
        },
    }
}

} // verus!
