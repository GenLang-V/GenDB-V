//! Capacity and SQL-error propagation rules (optional author toolkit; nothing here names a query).
//!
//! The capacity domain of a statement is the executable domain of its canonical evaluation,
//! `exec::relational::domain::fits_query` (children left to right, rows in order, stopping at the first SQL
//! error). An implementation that answers `Capacity` proves `!fits_query(db, Seq::empty(), body)`; one that answers
//! an SQL error proves the exact outcome `eval_query(db, Seq::empty(), body) == Err(e)`. These rules state when a
//! condition or error found by any evaluation order is the canonical one:
//!
//! - sequences: `lemma_fits_each_violation` (some element outside its domain, and no element inside its domain
//!   errs), `lemma_collect_uniform_err` (all errors share one code);
//! - constructors: `lemma_first_input` / `lemma_second_input` (a child's condition or error is the parent's),
//!   `lemma_filter_capacity` / `lemma_filter_err` (per-row conditions), `lemma_aggregate_capacity` /
//!   `lemma_aggregate_err`, `lemma_group_by_capacity` / `lemma_group_by_err` (aggregate values; group order does
//!   not matter under the stated premises);
//! - aggregate values: `lemma_sum_inside_ok`, `lemma_avg_inside_ok`, `lemma_count_value` (which aggregates cannot
//!   err inside their capacity condition), `aggs_ok_inside`; one group's row: `lemma_agg_row_ok_inside`,
//!   `lemma_agg_row_capacity`;
//! - absolute mass (the SUM/AVG condition `sum_mass_fits`): `lemma_num_mass_append`, `lemma_int_mass_append`,
//!   `lemma_num_mass_uniform`, `lemma_num_sum_abs`, `lemma_num_sum_bound`, `lemma_int_sum_bound`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::limits::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::equality::*;
use crate::spec::aggs::avg::*;
use crate::exec::relational::domain::*;
use crate::exec::relational::aggregate::{num_sum_at, lemma_num_sum_at, lemma_num_mass_nonneg};
use crate::bridge::collect::*;
use crate::link::query::lemma_avg_ok;

verus! {

// ------------------------------------------------------------------ sequences

/// Some element is outside its domain predicate and no element inside its domain predicate errs: the canonical
/// left-to-right evaluation reaches the first such element, so the sequence is outside `fits_each`.
pub proof fn lemma_fits_each_violation<T>(rs: Seq<Result<T, SqlError>>, fs: Seq<bool>, i: int)
    requires
        rs.len() == fs.len(), 0 <= i < fs.len(), !fs[i],
        forall|k: int| 0 <= k < fs.len() && #[trigger] fs[k] ==> rs[k] is Ok,
    ensures !fits_each(rs, fs),
{
    lemma_fits_each_violation_below(rs, fs, i + 1, i);
}

/// Induction for `lemma_fits_each_violation`: some violation lies below `n`; the first one is reached.
pub proof fn lemma_fits_each_violation_below<T>(rs: Seq<Result<T, SqlError>>, fs: Seq<bool>, n: int, i: int)
    requires
        rs.len() == fs.len(), 0 <= i < n <= fs.len(), !fs[i],
        forall|k: int| 0 <= k < fs.len() && #[trigger] fs[k] ==> rs[k] is Ok,
    ensures !fits_each(rs, fs),
    decreases n,
{
    if exists|k: int| 0 <= k < n - 1 && !#[trigger] fs[k] {
        let k = choose|k: int| 0 <= k < n - 1 && !#[trigger] fs[k];
        lemma_fits_each_violation_below(rs, fs, n - 1, k);
    } else {
        assert forall|k: int| 0 <= k < n - 1 implies #[trigger] rs[k] is Ok by {
            assert(fs[k]);
        }
        lemma_each_capacity(rs, fs, n - 1);
    }
}

/// Every element succeeds or fails with the same code `e`, and one fails: the outcome is `Err(e)`, whatever the
/// position of the first failure.
pub proof fn lemma_collect_uniform_err<T>(rs: Seq<Result<T, SqlError>>, e: SqlError, i: int)
    requires
        0 <= i < rs.len(), rs[i] == Err::<T, SqlError>(e),
        forall|k: int| 0 <= k < rs.len() ==> #[trigger] rs[k] is Ok || rs[k] == Err::<T, SqlError>(e),
    ensures collect(rs) == Err::<Seq<T>, SqlError>(e),
{
    lemma_collect_uniform_err_below(rs, e, i + 1, i);
}

/// Induction for `lemma_collect_uniform_err`: some error lies below `n`; the first one is the outcome.
pub proof fn lemma_collect_uniform_err_below<T>(rs: Seq<Result<T, SqlError>>, e: SqlError, n: int, i: int)
    requires
        0 <= i < n <= rs.len(), rs[i] is Err,
        forall|k: int| 0 <= k < rs.len() ==> #[trigger] rs[k] is Ok || rs[k] == Err::<T, SqlError>(e),
    ensures collect(rs) == Err::<Seq<T>, SqlError>(e),
    decreases n,
{
    if exists|k: int| 0 <= k < n - 1 && #[trigger] rs[k] is Err {
        let k = choose|k: int| 0 <= k < n - 1 && #[trigger] rs[k] is Err;
        lemma_collect_uniform_err_below(rs, e, n - 1, k);
    } else {
        assert forall|k: int| 0 <= k < n - 1 implies #[trigger] rs[k] is Ok by {}
        assert(rs[n - 1] is Err);
        lemma_collect_first_err(rs, n - 1);
    }
}

// ------------------------------------------------------------------ child queries

/// The child query a constructor evaluates first (`None` for a table).
pub open spec fn first_input(q: Query) -> Option<Query> {
    match q {
        Query::Table(_) => None,
        Query::Filter { pred, input } => Some(*input),
        Query::Project { exprs, input } => Some(*input),
        Query::Product { left, right } => Some(*left),
        Query::LeftJoin { left, right, on } => Some(*left),
        Query::Aggregate { aggs, input } => Some(*input),
        Query::GroupBy { keys, aggs, input } => Some(*input),
        Query::Distinct(input) => Some(*input),
    }
}

/// A condition outside the domain, or an SQL error, of the first child is the parent's.
pub proof fn lemma_first_input(db: Database, ctx: Row, q: Query)
    requires first_input(q) is Some,
    ensures
        !fits_query(db, ctx, first_input(q)->Some_0) ==> !fits_query(db, ctx, q),
        eval_query(db, ctx, first_input(q)->Some_0) is Err ==> eval_query(db, ctx, q) == eval_query(db, ctx, first_input(q)->Some_0),
{
}

/// The right input of a product or LEFT JOIN, once the left input succeeded.
pub proof fn lemma_second_input(db: Database, ctx: Row, q: Query, l: Relation)
    requires
        q is Product || q is LeftJoin,
        eval_query(db, ctx, first_input(q)->Some_0) == Ok::<Relation, SqlError>(l),
    ensures
        ({
            let right = match q { Query::Product { left, right } => *right, Query::LeftJoin { left, right, on } => *right, _ => q };
            &&& !fits_query(db, ctx, right) ==> !fits_query(db, ctx, q)
            &&& eval_query(db, ctx, right) is Err ==> eval_query(db, ctx, q) == eval_query(db, ctx, right)
        }),
{
}

// ------------------------------------------------------------------ filters (WHERE, HAVING, JOIN .. ON trees)

/// A row's condition outside its domain, when no condition inside its domain errs.
pub proof fn lemma_filter_capacity(db: Database, ctx: Row, pred: Pred, input: Box<Query>, rows: Relation, i: int)
    requires
        eval_query(db, ctx, *input) == Ok::<Relation, SqlError>(rows),
        0 <= i < rows.len(), !fits_pred(db, ctx + rows[i], pred),
        forall|k: int| 0 <= k < rows.len() && #[trigger] fits_pred(db, ctx + rows[k], pred)
            ==> eval_pred(db, ctx + rows[k], pred) is Ok,
    ensures !fits_query(db, ctx, Query::Filter { pred, input }),
{
    lemma_fits_filter(db, ctx, pred, input);
    lemma_filter_fits_each(db, ctx, rows, pred);
    let rs = filter_results(db, ctx, rows, pred);
    let fs = filter_fs(db, ctx, rows, pred);
    assert forall|k: int| 0 <= k < fs.len() && #[trigger] fs[k] implies rs[k] is Ok by {
        assert(fits_pred(db, ctx + rows[k], pred));
    }
    lemma_fits_each_violation(rs, fs, i);
}

/// Every row's condition succeeds or fails with code `e`, and one fails: the filter is `Err(e)`.
pub proof fn lemma_filter_err(db: Database, ctx: Row, pred: Pred, input: Box<Query>, rows: Relation, e: SqlError, i: int)
    requires
        eval_query(db, ctx, *input) == Ok::<Relation, SqlError>(rows),
        0 <= i < rows.len(), eval_pred(db, ctx + rows[i], pred) == Err::<Truth, SqlError>(e),
        forall|k: int| 0 <= k < rows.len() ==> #[trigger] eval_pred(db, ctx + rows[k], pred) is Ok
            || eval_pred(db, ctx + rows[k], pred) == Err::<Truth, SqlError>(e),
    ensures eval_query(db, ctx, Query::Filter { pred, input }) == Err::<Relation, SqlError>(e),
{
    lemma_eval_filter(db, ctx, pred, input);
    let rs = filter_results(db, ctx, rows, pred);
    assert forall|k: int| 0 <= k < rs.len() implies #[trigger] rs[k] is Ok || rs[k] == Err::<Truth, SqlError>(e) by {
        assert(rs[k] == eval_pred(db, ctx + rows[k], pred));
    }
    lemma_collect_uniform_err(rs, e, i);
}

// ------------------------------------------------------------------ aggregate values

/// Every aggregate of a group that is inside its capacity condition succeeds.
pub open spec fn aggs_ok_inside(aggs: Seq<Agg>, args: Seq<Row>) -> bool {
    forall|j: int| 0 <= j < aggs.len() && #[trigger] fits_agg_value(aggs[j], column(args, j))
        ==> agg_value(aggs[j], column(args, j)) is Ok
}

/// COUNT(*) and COUNT(e) never leave the capacity domain; the value is the count, or the SQL error 22003 beyond
/// int8.
pub proof fn lemma_count_value(a: Agg, vs: Seq<Val>)
    requires a is CountStar || a is Count,
    ensures
        fits_agg_value(a, vs),
        ({
            let n = if a is CountStar { vs.len() as int } else { count_non_null(vs) as int };
            &&& n <= int8_max() ==> agg_value(a, vs) == Ok::<Val, SqlError>(Val::Int(n))
            &&& n > int8_max() ==> agg_value(a, vs) == Err::<Val, SqlError>(SqlError::NumericValueOutOfRange)
        }),
{
    assert(int8_min() < 0);
}

/// `|num_sum_at| <= num_mass_at` (the sum aligned to scale `t` is bounded by the absolute mass at `t`).
pub proof fn lemma_num_sum_abs(vs: Seq<Val>, t: nat)
    ensures abs(num_sum_at(vs, t)) <= num_mass_at(vs, t),
    decreases vs.len(),
{
    if vs.len() > 0 {
        lemma_num_sum_abs(vs.drop_last(), t);
        if let Val::Num { coeff, scale } = vs.last() {
            let k = (t - scale) as nat;
            lemma_pow10_positive(k);
            let p = pow10(k);
            assert(abs(coeff * p) == abs(coeff) * p) by (nonlinear_arith) requires p >= 1;
        }
    }
}

/// `|int_sum| <= int_mass`.
pub proof fn lemma_int_sum_bound(vs: Seq<Val>)
    ensures abs(int_sum(vs)) <= int_mass(vs), int_mass(vs) >= 0,
    decreases vs.len(),
{
    if vs.len() > 0 {
        lemma_int_sum_bound(vs.drop_last());
    }
}

/// The exact numeric sum is bounded by the absolute mass at the result scale.
pub proof fn lemma_num_sum_bound(vs: Seq<Val>)
    ensures
        num_sum(vs).1 == num_max_scale(vs),
        abs(num_sum(vs).0) <= num_mass_at(vs, num_max_scale(vs)),
{
    let t = num_max_scale(vs);
    lemma_num_sum_at(vs, t);
    assert(pow10(0) == 1);
    assert(align(num_sum(vs).0, t, t) == num_sum(vs).0 * 1);
    lemma_num_sum_abs(vs, t);
}

/// SUM of int8 or numeric succeeds inside its capacity condition (the exact sum is far inside PostgreSQL's numeric
/// format). (SUM of int4 is int8: its range check can fail inside the condition.)
pub proof fn lemma_sum_inside_ok(kind: NumKind, arg: Expr, vs: Seq<Val>)
    requires !(kind is Int4), all_of_kind(kind, vs), fits_agg_value(Agg::Sum { kind, arg }, vs),
    ensures agg_value(Agg::Sum { kind, arg }, vs) is Ok,
{
    if count_non_null(vs) > 0 {
        match kind {
            NumKind::Numeric => {
                lemma_num_sum_bound(vs);
                lemma_num_in_range_small(num_sum(vs).0, num_sum(vs).1);
            },
            _ => {
                lemma_int_sum_bound(vs);
                lemma_num_in_range_small(int_sum(vs), 0);
            },
        }
    }
}

/// AVG succeeds inside its capacity condition.
pub proof fn lemma_avg_inside_ok(kind: NumKind, arg: Expr, vs: Seq<Val>)
    requires all_of_kind(kind, vs), fits_agg_value(Agg::Avg { kind, arg }, vs),
    ensures agg_value(Agg::Avg { kind, arg }, vs) is Ok,
{
    if count_non_null(vs) > 0 {
        let s = avg_sum(kind, vs);
        if kind is Numeric {
            lemma_num_sum_bound(vs);
            lemma_num_in_range_small(s.0, s.1);
        }
        lemma_avg_ok(s.0, s.1, count_non_null(vs) as int);
    }
}

// ------------------------------------------------------------------ aggregate rows, Aggregate and GroupBy

/// Inside `fits_agg_row` every aggregate of the group succeeds (given `aggs_ok_inside`).
pub proof fn lemma_agg_row_ok_inside(aggs: Seq<Agg>, args: Seq<Row>)
    requires fits_agg_row(aggs, args), aggs_ok_inside(aggs, args),
    ensures agg_row(aggs, args) is Ok,
{
    let rs = agg_value_results(aggs, args);
    let fs = agg_value_fs(aggs, args);
    lemma_agg_row(aggs, args);
    assert forall|j: int| 0 <= j < rs.len() implies #[trigger] rs[j] is Ok by {
        lemma_all_ok_before(rs, fs, j);
    }
    lemma_collect_ok(rs);
}

/// Inside `fits_each`, when every element inside its domain succeeds, every element succeeds (by induction on
/// the position: all earlier elements succeeded, so element `j`'s domain predicate is required).
pub proof fn lemma_all_ok_before(rs: Seq<Result<Val, SqlError>>, fs: Seq<bool>, j: int)
    requires
        rs.len() == fs.len(), 0 <= j < rs.len(), fits_each(rs, fs),
        forall|k: int| 0 <= k < fs.len() && #[trigger] fs[k] ==> rs[k] is Ok,
    ensures rs[j] is Ok,
    decreases j,
{
    assert forall|k: int| 0 <= k < j implies #[trigger] rs[k] is Ok by {
        lemma_all_ok_before(rs, fs, k);
    }
    assert(ok_before(rs, j));
    assert(fs[j]);
}

/// One aggregate outside its capacity condition, the others succeeding inside theirs: the group's row is outside
/// `fits_agg_row`.
pub proof fn lemma_agg_row_capacity(aggs: Seq<Agg>, args: Seq<Row>, j: int)
    requires 0 <= j < aggs.len(), !fits_agg_value(aggs[j], column(args, j)), aggs_ok_inside(aggs, args),
    ensures !fits_agg_row(aggs, args),
{
    let rs = agg_value_results(aggs, args);
    let fs = agg_value_fs(aggs, args);
    assert forall|k: int| 0 <= k < fs.len() && #[trigger] fs[k] implies rs[k] is Ok by {
        assert(fits_agg_value(aggs[k], column(args, k)));
    }
    lemma_fits_each_violation(rs, fs, j);
}

/// Aggregate (no GROUP BY) over `rows`, row `i`'s arguments `args[i]`: an aggregate outside its capacity
/// condition, the others succeeding inside theirs, puts the statement node outside `fits_query`.
pub proof fn lemma_aggregate_capacity(db: Database, ctx: Row, aggs: Seq<Agg>, input: Box<Query>, rows: Relation,
    args: Seq<Row>, j: int)
    requires
        eval_query(db, ctx, *input) == Ok::<Relation, SqlError>(rows),
        args.len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> #[trigger] agg_args(db, ctx + rows[i], aggs) == Ok::<Row, SqlError>(args[i]),
        0 <= j < aggs.len(), !fits_agg_value(aggs[j], column(args, j)), aggs_ok_inside(aggs, args),
    ensures !fits_query(db, ctx, Query::Aggregate { aggs, input }),
{
    let rs = agg_args_results(db, ctx, rows, aggs);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(args[i]) by {}
    lemma_collect_all(rs, args);
    lemma_agg_row_capacity(aggs, args, j);
}

/// Aggregate: one aggregate fails with `e`, every other succeeds or fails with `e`: the node is `Err(e)`.
pub proof fn lemma_aggregate_err(db: Database, ctx: Row, aggs: Seq<Agg>, input: Box<Query>, rows: Relation,
    args: Seq<Row>, e: SqlError, j: int)
    requires
        eval_query(db, ctx, *input) == Ok::<Relation, SqlError>(rows),
        args.len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> #[trigger] agg_args(db, ctx + rows[i], aggs) == Ok::<Row, SqlError>(args[i]),
        0 <= j < aggs.len(), agg_value(aggs[j], column(args, j)) == Err::<Val, SqlError>(e),
        forall|k: int| 0 <= k < aggs.len() ==> #[trigger] agg_value(aggs[k], column(args, k)) is Ok
            || agg_value(aggs[k], column(args, k)) == Err::<Val, SqlError>(e),
    ensures eval_query(db, ctx, Query::Aggregate { aggs, input }) == Err::<Relation, SqlError>(e),
{
    lemma_eval_aggregate(db, ctx, aggs, input);
    let rs = agg_args_results(db, ctx, rows, aggs);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<Row, SqlError>(args[i]) by {}
    lemma_collect_all(rs, args);
    lemma_agg_row(aggs, args);
    let vs = agg_value_results(aggs, args);
    lemma_collect_uniform_err(vs, e, j);
}

/// GROUP BY over `rows`, row `i`'s key `ks[i]` and arguments `args[i]`; groups `distinct_rows(ks)[g]`: one group
/// with an aggregate outside its capacity condition, every group's aggregates inside theirs succeeding, puts the
/// node outside `fits_query` (whatever the group order).
pub proof fn lemma_group_by_capacity(db: Database, ctx: Row, keys: Seq<Expr>, aggs: Seq<Agg>, input: Box<Query>,
    rows: Relation, ks: Seq<Row>, args: Seq<Row>, g: int, j: int)
    requires
        eval_query(db, ctx, *input) == Ok::<Relation, SqlError>(rows),
        ks.len() == rows.len(), args.len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> #[trigger] group_input(db, ctx + rows[i], keys, aggs)
            == Ok::<(Row, Row), SqlError>((ks[i], args[i])),
        0 <= g < distinct_rows(ks).len(), 0 <= j < aggs.len(),
        !fits_agg_value(aggs[j], column(group_members(ks, args, distinct_rows(ks)[g]), j)),
        forall|h: int| 0 <= h < distinct_rows(ks).len() ==> #[trigger] aggs_ok_inside(aggs, group_members(ks, args, distinct_rows(ks)[h])),
    ensures !fits_query(db, ctx, Query::GroupBy { keys, aggs, input }),
{
    lemma_fits_group_by(db, ctx, keys, aggs, input);
    let prepared = lemma_group_prepared(db, ctx, keys, aggs, rows, ks, args);
    let ds = distinct_rows(ks);
    let rs = group_results(aggs, ks, args);
    let fs = groups_fs(aggs, ks, args);
    assert forall|h: int| 0 <= h < fs.len() && #[trigger] fs[h] implies rs[h] is Ok by {
        assert(aggs_ok_inside(aggs, group_members(ks, args, ds[h])));
        lemma_agg_row_ok_inside(aggs, group_members(ks, args, ds[h]));
    }
    assert(aggs_ok_inside(aggs, group_members(ks, args, ds[g])));
    lemma_agg_row_capacity(aggs, group_members(ks, args, ds[g]), j);
    lemma_fits_each_violation(rs, fs, g);
}

/// GROUP BY: one group's aggregate fails with `e`, every group's aggregates succeed or fail with `e`: the node is
/// `Err(e)` (whatever the group order).
pub proof fn lemma_group_by_err(db: Database, ctx: Row, keys: Seq<Expr>, aggs: Seq<Agg>, input: Box<Query>,
    rows: Relation, ks: Seq<Row>, args: Seq<Row>, e: SqlError, g: int, j: int)
    requires
        eval_query(db, ctx, *input) == Ok::<Relation, SqlError>(rows),
        ks.len() == rows.len(), args.len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> #[trigger] group_input(db, ctx + rows[i], keys, aggs)
            == Ok::<(Row, Row), SqlError>((ks[i], args[i])),
        0 <= g < distinct_rows(ks).len(), 0 <= j < aggs.len(),
        agg_value(aggs[j], column(group_members(ks, args, distinct_rows(ks)[g]), j)) == Err::<Val, SqlError>(e),
        forall|h: int, k: int| 0 <= h < distinct_rows(ks).len() && 0 <= k < aggs.len()
            ==> #[trigger] agg_value(aggs[k], column(group_members(ks, args, distinct_rows(ks)[h]), k)) is Ok
                || agg_value(aggs[k], column(group_members(ks, args, distinct_rows(ks)[h]), k)) == Err::<Val, SqlError>(e),
    ensures eval_query(db, ctx, Query::GroupBy { keys, aggs, input }) == Err::<Relation, SqlError>(e),
{
    lemma_eval_group_by(db, ctx, keys, aggs, input);
    let prepared = lemma_group_prepared(db, ctx, keys, aggs, rows, ks, args);
    let ds = distinct_rows(ks);
    let rs = group_results(aggs, ks, args);
    assert forall|h: int| 0 <= h < rs.len() implies #[trigger] rs[h] is Ok || rs[h] == Err::<Row, SqlError>(e) by {
        let m = group_members(ks, args, ds[h]);
        let vs = agg_value_results(aggs, m);
        lemma_agg_row(aggs, m);
        if exists|k: int| 0 <= k < aggs.len() && #[trigger] vs[k] is Err {
            let k = choose|k: int| 0 <= k < aggs.len() && #[trigger] vs[k] is Err;
            assert(vs[k] == agg_value(aggs[k], column(m, k)));
            assert forall|k2: int| 0 <= k2 < vs.len() implies #[trigger] vs[k2] is Ok || vs[k2] == Err::<Val, SqlError>(e) by {
                assert(vs[k2] == agg_value(aggs[k2], column(m, k2)));
            }
            lemma_collect_uniform_err(vs, e, k);
        } else {
            lemma_collect_ok(vs);
        }
    }
    let m = group_members(ks, args, ds[g]);
    let vs = agg_value_results(aggs, m);
    lemma_agg_row(aggs, m);
    assert(vs[j] == agg_value(aggs[j], column(m, j)));
    assert forall|k2: int| 0 <= k2 < vs.len() implies #[trigger] vs[k2] is Ok || vs[k2] == Err::<Val, SqlError>(e) by {
        assert(vs[k2] == agg_value(aggs[k2], column(m, k2)));
    }
    lemma_collect_uniform_err(vs, e, j);
    assert(rs[g] == Err::<Row, SqlError>(e));
    lemma_collect_uniform_err(rs, e, g);
}

/// The per-row GROUP BY inputs collect to `(ks[i], args[i])`; the keys and arguments are its two projections.
pub proof fn lemma_group_prepared(db: Database, ctx: Row, keys: Seq<Expr>, aggs: Seq<Agg>, rows: Relation, ks: Seq<Row>,
    args: Seq<Row>) -> (prepared: Seq<(Row, Row)>)
    requires
        ks.len() == rows.len(), args.len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> #[trigger] group_input(db, ctx + rows[i], keys, aggs)
            == Ok::<(Row, Row), SqlError>((ks[i], args[i])),
    ensures
        collect(group_input_results(db, ctx, rows, keys, aggs)) == Ok::<Seq<(Row, Row)>, SqlError>(prepared),
        prepared.map_values(|p: (Row, Row)| p.0) == ks,
        prepared.map_values(|p: (Row, Row)| p.1) == args,
{
    let prepared = Seq::new(rows.len(), |i: int| (ks[i], args[i]));
    let rs = group_input_results(db, ctx, rows, keys, aggs);
    assert forall|i: int| 0 <= i < rs.len() implies #[trigger] rs[i] == Ok::<(Row, Row), SqlError>(prepared[i]) by {
        lemma_group_input_results(db, ctx, rows, keys, aggs, i);
    }
    lemma_collect_all(rs, prepared);
    assert(prepared.map_values(|p: (Row, Row)| p.0) =~= ks);
    assert(prepared.map_values(|p: (Row, Row)| p.1) =~= args);
    prepared
}

// ------------------------------------------------------------------ absolute mass

/// The numeric mass of concatenated values is the sum of the masses.
pub proof fn lemma_num_mass_append(a: Seq<Val>, b: Seq<Val>, t: nat)
    ensures num_mass_at(a + b, t) == num_mass_at(a, t) + num_mass_at(b, t),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        lemma_num_mass_append(a, b.drop_last(), t);
    }
}

/// The integer mass of concatenated values is the sum of the masses.
pub proof fn lemma_int_mass_append(a: Seq<Val>, b: Seq<Val>)
    ensures int_mass(a + b) == int_mass(a) + int_mass(b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        lemma_int_mass_append(a, b.drop_last());
    }
}

/// Numeric values of one scale `s` (for example a typed column or product): the result scale is `s` when some value
/// is numeric, and the mass at `s` is the sum of the absolute coefficients (`num_mass_at(vs, s)`, each term
/// `|coeff| * 10^0`).
pub proof fn lemma_num_mass_uniform(vs: Seq<Val>, s: nat)
    requires forall|i: int| 0 <= i < vs.len() ==> (#[trigger] vs[i] matches Val::Num { coeff, scale } ==> scale == s),
    ensures
        num_max_scale(vs) <= s,
        (exists|i: int| 0 <= i < vs.len() && #[trigger] vs[i] is Num) ==> num_max_scale(vs) == s,
        num_mass_at(vs, s) >= 0,
    decreases vs.len(),
{
    lemma_num_mass_nonneg(vs, s);
    if vs.len() > 0 {
        let d = vs.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies (#[trigger] d[i] matches Val::Num { coeff, scale } ==> scale == s) by {
            assert(d[i] == vs[i]);
        }
        lemma_num_mass_uniform(d, s);
        if exists|i: int| 0 <= i < vs.len() && #[trigger] vs[i] is Num {
            let i = choose|i: int| 0 <= i < vs.len() && #[trigger] vs[i] is Num;
            if i < vs.len() - 1 {
                assert(d[i] == vs[i]);
            }
        }
    }
}

} // verus!
