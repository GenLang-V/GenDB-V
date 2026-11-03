//! The relational operators of the denotation applied to evaluated children (engine toolkit; nothing here names
//! a query, a table or a column).
//!
//! `spec::eval::eval_query` evaluates a node's children and then applies one operator to their rows. This module
//! names those operators as functions of the child rows (`filter_op`, `project_op`, `left_join_op`,
//! `aggregate_op`, `group_by_op`; `product_rows` and `distinct_rows` are already `spec::relation` functions), and
//! `lemma_eval_op` unfolds one node of `eval_query` into them. A physical operator that receives its children's
//! rows in another order, or computes them another way, is proved against these functions; the bag congruence
//! lemmas (`engine_link::congruence`) relate their results on reordered inputs.
//!
//! Per-row outcome sequences are those of `exec::relational::domain` (`filter_results`, `project_results`, ...),
//! so the domain lemmas there apply unchanged.
//!
//! Also here: two-valued filtering (`pred_keeps`, `lemma_filter_keeps`: a condition that never errs and is
//! `True` exactly where `f` holds keeps `link::join::keep(rows, f)`), filters whose every row errs
//! (`lemma_filter_all_err`, the "raise only if reached" rule), and uniform error sequences (`uniform`,
//! `lemma_collect_uniform`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::equality::*;
use crate::exec::relational::domain::*;
use crate::bridge::collect::*;
use crate::link::join::keep;
use crate::link::capacity::lemma_collect_uniform_err;

verus! {

// ------------------------------------------------------------------------------------- the operators

/// WHERE / HAVING / inner-join ON over evaluated rows: the first condition error in row order, else the rows
/// whose condition is `True`.
pub open spec fn filter_op(db: Database, ctx: Row, rows: Seq<Row>, pred: Pred) -> Result<Relation, SqlError> {
    match collect(filter_results(db, ctx, rows, pred)) {
        Err(e) => Err(e),
        Ok(truths) => Ok(keep_true(rows, truths)),
    }
}

/// SELECT list over evaluated rows (one output row per input row, first error in row order).
pub open spec fn project_op(db: Database, ctx: Row, rows: Seq<Row>, exprs: Seq<Expr>) -> Result<Relation, SqlError> {
    collect(project_results(db, ctx, rows, exprs))
}

/// LEFT JOIN over evaluated inputs (`arity`: the right input's static arity, the NULL padding width).
pub open spec fn left_join_op(db: Database, ctx: Row, l: Seq<Row>, r: Seq<Row>, on: Pred, arity: nat) -> Result<Relation, SqlError> {
    match collect(left_join_results(db, ctx, l, r, on)) {
        Err(e) => Err(e),
        Ok(truths) => Ok(left_join_rows(l, r, truths, arity)),
    }
}

/// Aggregation without GROUP BY over evaluated rows: the arguments of every row, then exactly one row.
pub open spec fn aggregate_op(db: Database, ctx: Row, rows: Seq<Row>, aggs: Seq<Agg>) -> Result<Relation, SqlError> {
    match collect(agg_args_results(db, ctx, rows, aggs)) {
        Err(e) => Err(e),
        Ok(args) => match agg_row(aggs, args) {
            Err(e) => Err(e),
            Ok(row) => Ok(seq![row]),
        },
    }
}

/// GROUP BY over evaluated rows: every row's key and arguments, then one row per group (`spec::relation::group_rows`).
pub open spec fn group_by_op(db: Database, ctx: Row, rows: Seq<Row>, keys: Seq<Expr>, aggs: Seq<Agg>) -> Result<Relation, SqlError> {
    match collect(group_input_results(db, ctx, rows, keys, aggs)) {
        Err(e) => Err(e),
        Ok(prepared) => group_rows(aggs, prepared.map_values(|p: (Row, Row)| p.0), prepared.map_values(|p: (Row, Row)| p.1)),
    }
}

/// One node of the denotation: its children evaluated, then its operator.
pub proof fn lemma_eval_op(db: Database, ctx: Row, q: Query)
    ensures
        eval_query(db, ctx, q) == match q {
            Query::Table(t) => if t < db.tables.len() { Ok(db.tables[t as int]) } else { Err(SqlError::TypeError) },
            Query::Filter { pred, input } => match eval_query(db, ctx, *input) {
                Err(e) => Err(e),
                Ok(rows) => filter_op(db, ctx, rows, pred),
            },
            Query::Project { exprs, input } => match eval_query(db, ctx, *input) {
                Err(e) => Err(e),
                Ok(rows) => project_op(db, ctx, rows, exprs),
            },
            Query::Product { left, right } => match eval_query(db, ctx, *left) {
                Err(e) => Err(e),
                Ok(l) => match eval_query(db, ctx, *right) {
                    Err(e) => Err(e),
                    Ok(r) => Ok(product_rows(l, r)),
                },
            },
            Query::LeftJoin { left, right, on } => match eval_query(db, ctx, *left) {
                Err(e) => Err(e),
                Ok(l) => match eval_query(db, ctx, *right) {
                    Err(e) => Err(e),
                    Ok(r) => left_join_op(db, ctx, l, r, on, query_arity(db.schema, *right)),
                },
            },
            Query::Aggregate { aggs, input } => match eval_query(db, ctx, *input) {
                Err(e) => Err(e),
                Ok(rows) => aggregate_op(db, ctx, rows, aggs),
            },
            Query::GroupBy { keys, aggs, input } => match eval_query(db, ctx, *input) {
                Err(e) => Err(e),
                Ok(rows) => group_by_op(db, ctx, rows, keys, aggs),
            },
            Query::Distinct(input) => match eval_query(db, ctx, *input) {
                Err(e) => Err(e),
                Ok(rows) => Ok(distinct_rows(rows)),
            },
        },
{
    match q {
        Query::Filter { pred, input } => lemma_eval_filter(db, ctx, pred, input),
        Query::Project { exprs, input } => lemma_eval_project(db, ctx, exprs, input),
        Query::LeftJoin { left, right, on } => lemma_eval_left_join(db, ctx, left, right, on),
        Query::Aggregate { aggs, input } => lemma_eval_aggregate(db, ctx, aggs, input),
        Query::GroupBy { keys, aggs, input } => lemma_eval_group_by(db, ctx, keys, aggs, input),
        _ => {},
    }
}

// ------------------------------------------------------------------------------------- uniform errors

/// Every outcome is a value or the one SQL error `e` (hazard H1: the first error of a sequence does not depend on
/// its order). A sequence without errors is uniform for every `e`.
pub open spec fn uniform<T>(rs: Seq<Result<T, SqlError>>, e: SqlError) -> bool {
    forall|i: int| 0 <= i < rs.len() ==> #[trigger] rs[i] is Ok || rs[i] == Err::<T, SqlError>(e)
}

/// The first-error collection of a uniform sequence: `Err(e)` exactly when some element errs, otherwise every
/// value in order.
pub proof fn lemma_collect_uniform<T>(rs: Seq<Result<T, SqlError>>, e: SqlError)
    requires uniform(rs, e),
    ensures
        (collect(rs) is Ok) == (forall|i: int| 0 <= i < rs.len() ==> #[trigger] rs[i] is Ok),
        collect(rs) is Ok || collect(rs) == Err::<Seq<T>, SqlError>(e),
        collect(rs) is Ok ==> collect(rs)->Ok_0.len() == rs.len() && forall|i: int| 0 <= i < rs.len()
            ==> #[trigger] rs[i] == Ok::<T, SqlError>(collect(rs)->Ok_0[i]),
{
    lemma_collect_ok(rs);
    if !(collect(rs) is Ok) {
        let i = choose|i: int| 0 <= i < rs.len() && !(#[trigger] rs[i] is Ok);
        assert(rs[i] == Err::<T, SqlError>(e));
        lemma_collect_uniform_err(rs, e, i);
    }
}

// ------------------------------------------------------------------------------------- two-valued filters

/// The condition evaluates without error on every row (environment `ctx + rows[i]`) and is `True` exactly where
/// `f` holds (`False` and `Unknown` both drop the row).
pub open spec fn pred_keeps(db: Database, ctx: Row, rows: Seq<Row>, pred: Pred, f: spec_fn(Row) -> bool) -> bool {
    forall|i: int| 0 <= i < rows.len() ==> {
        &&& #[trigger] eval_pred(db, ctx + rows[i], pred) is Ok
        &&& (eval_pred(db, ctx + rows[i], pred)->Ok_0 is True) == f(rows[i])
    }
}

/// `keep_true` of truths that are `True` exactly where `f` holds is `keep(rows, f)`.
pub proof fn lemma_keep_true_as_keep(rows: Seq<Row>, truths: Seq<Truth>, f: spec_fn(Row) -> bool)
    requires
        truths.len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] truths[i] is True) == f(rows[i]),
    ensures keep_true(rows, truths) == keep(rows, f),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let (ri, ti) = (rows.drop_last(), truths.drop_last());
        assert forall|i: int| 0 <= i < ri.len() implies (#[trigger] ti[i] is True) == f(ri[i]) by {
            assert(ti[i] == truths[i] && ri[i] == rows[i]);
        }
        lemma_keep_true_as_keep(ri, ti, f);
        assert((truths[rows.len() - 1] is True) == f(rows[rows.len() - 1]));
    }
}

/// A two-valued, error-free condition keeps exactly `keep(rows, f)`.
pub proof fn lemma_filter_keeps(db: Database, ctx: Row, rows: Seq<Row>, pred: Pred, f: spec_fn(Row) -> bool)
    requires pred_keeps(db, ctx, rows, pred, f),
    ensures filter_op(db, ctx, rows, pred) == Ok::<Relation, SqlError>(keep(rows, f)),
{
    let rs = filter_results(db, ctx, rows, pred);
    let truths = Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred)->Ok_0);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Truth, SqlError>(truths[i]) by {
        assert(eval_pred(db, ctx + rows[i], pred) is Ok);
    }
    lemma_collect_all(rs, truths);
    assert forall|i: int| 0 <= i < rows.len() implies (#[trigger] truths[i] is True) == f(rows[i]) by {
        assert(eval_pred(db, ctx + rows[i], pred) is Ok);
    }
    lemma_keep_true_as_keep(rows, truths, f);
}

/// "Raise only if reached": a condition that errs with `e` on every row makes the filter `Err(e)` exactly when
/// there is a row; an empty input is `Ok` with no row (the condition is never evaluated).
pub proof fn lemma_filter_all_err(db: Database, ctx: Row, rows: Seq<Row>, pred: Pred, e: SqlError)
    requires forall|i: int| 0 <= i < rows.len() ==> #[trigger] eval_pred(db, ctx + rows[i], pred) == Err::<Truth, SqlError>(e),
    ensures
        filter_op(db, ctx, rows, pred) == if rows.len() == 0 {
            Ok::<Relation, SqlError>(Seq::empty())
        } else {
            Err::<Relation, SqlError>(e)
        },
{
    let rs = filter_results(db, ctx, rows, pred);
    if rows.len() == 0 {
        assert(rs =~= Seq::<Result<Truth, SqlError>>::empty());
        assert(keep_true(rows, Seq::<Truth>::empty()) =~= Seq::<Row>::empty());
    } else {
        assert(rs[0] == Err::<Truth, SqlError>(e));
        assert forall|k: int| 0 <= k < rs.len() implies #[trigger] rs[k] is Ok || rs[k] == Err::<Truth, SqlError>(e) by {}
        lemma_collect_uniform_err(rs, e, 0);
    }
}

} // verus!
