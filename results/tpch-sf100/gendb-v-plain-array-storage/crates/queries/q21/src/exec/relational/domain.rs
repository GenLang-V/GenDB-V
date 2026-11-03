//! The finite executable domain of queries: where the verified evaluator computes a result rather than refusing
//! with `Capacity`. `fits_pred` / `fits_query` extend `exec::domain::fits_expr` / `fits_exprs` over the canonical
//! evaluation of `spec::eval` (children left to right, rows in sequence order, stopping at the first SQL error):
//! they require exactly the machine-representability conditions of the intermediates that evaluation computes.
//! They are domain predicates only — the SQL meaning (`eval_query`) is exact and unbounded; an executable
//! `Capacity` refusal proves the corresponding predicate false.
//!
//! Conditions beyond the scalar ones:
//! - `SUM` / `AVG` of every kind: the absolute mass of the group's argument values is at most `i128::MAX`
//!   (`sum_mass_fits`). The mass is the sum of the absolute values, numeric coefficients aligned to the group's
//!   result scale (`num_max_scale`, the scale of `spec::relation::num_sum`). It does not depend on the row order or
//!   on a partition of the rows, and it bounds every partial sum in any order at that scale. (It replaced an
//!   earlier row-order partial-sum condition and an "integer SUM needs none" rule that relied on materialized
//!   inputs.) COUNT needs none: a count beyond int8 is the SQL error of `int_result`, not a capacity condition.
//! - `LEFT JOIN`: the static arity of the right input (NULL padding width) fits `usize`.
//!
//! Layout, top-down:
//! - the domain of a left-to-right, first-error evaluation of a sequence (`fits_each`) and its loop lemmas;
//! - the per-row outcome sequences of the operators (`*_results`), written as `eval_query` evaluates them;
//! - the SUM / AVG mass;
//! - the domain predicates `fits_pred` / `fits_query` with the aggregate domains and the per-row domain sequences
//!   (`*_fs`) they use;
//! - quantified forms of the Filter / LEFT JOIN per-row domains (`*_fits`);
//! - unfolding lemmas: `eval_query` and `fits_query` of one constructor stated with the named sequences.
//!
//! These definitions are the admitted input domain of the checked entry points and of saved agent proofs. Their
//! bodies are fixed: change one only as a reviewed domain change, and re-verify the saved candidates (admitted
//! proofs sit close to the solver's resource limit).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::numeric::*;
use crate::spec::ast::*;
use crate::spec::relation::*;
use crate::spec::eval::*;
use crate::spec::equality::*;
use crate::exec::domain::*;
use crate::bridge::collect::*;
/// `collect` only depends on the elements (`bridge::collect`; re-exported here, where the operators' per-row
/// sequences are named).
pub use crate::bridge::collect::lemma_collect_pointwise;

verus! {

// ------------------------------------------------------------------ first-error evaluation of a sequence
//
// `rs`: the element outcomes, `fs`: the element domain predicates.

/// Every element before `i` succeeded.
pub open spec fn ok_before<T>(rs: Seq<Result<T, SqlError>>, i: int) -> bool {
    forall|j: int| 0 <= j < i ==> #[trigger] rs[j] is Ok
}

/// Domain of a left-to-right, first-error evaluation of a sequence: the domain predicate `fs[i]` of element `i`
/// is required exactly when every earlier element succeeded (nothing after an error is computed).
pub open spec fn fits_each<T>(rs: Seq<Result<T, SqlError>>, fs: Seq<bool>) -> bool {
    forall|i: int| 0 <= i < fs.len() && ok_before(rs, i) ==> #[trigger] fs[i]
}

/// Loop invariant of such an evaluation: every element before `i` was inside its domain.
pub open spec fn fits_before(fs: Seq<bool>, i: int) -> bool {
    forall|j: int| 0 <= j < i ==> #[trigger] fs[j]
}

/// Loop exit: element `i` leaves its domain (`Capacity`).
pub proof fn lemma_each_capacity<T>(rs: Seq<Result<T, SqlError>>, fs: Seq<bool>, i: int)
    requires 0 <= i < fs.len(), ok_before(rs, i), !fs[i],
    ensures !fits_each(rs, fs),
{
}

/// Loop exit: element `i` is the first SQL error.
pub proof fn lemma_each_err<T>(rs: Seq<Result<T, SqlError>>, fs: Seq<bool>, i: int)
    requires
        rs.len() == fs.len(), 0 <= i < rs.len(),
        ok_before(rs, i), fits_before(fs, i), fs[i], rs[i] is Err,
    ensures
        fits_each(rs, fs),
        collect(rs) == Err::<Seq<T>, SqlError>(rs[i]->Err_0),
{
    lemma_collect_first_err(rs, i);
    assert forall|k: int| 0 <= k < fs.len() && ok_before(rs, k) implies #[trigger] fs[k] by {
        if k > i {
            assert(rs[i] is Ok);
        }
    }
}

/// Loop end: every element succeeded with value `vs[k]`.
pub proof fn lemma_each_done<T>(rs: Seq<Result<T, SqlError>>, fs: Seq<bool>, vs: Seq<T>)
    requires
        rs.len() == fs.len(), vs.len() == rs.len(),
        forall|k: int| 0 <= k < rs.len() ==> #[trigger] rs[k] == Ok::<T, SqlError>(vs[k]),
        fits_before(fs, fs.len() as int),
    ensures
        fits_each(rs, fs),
        collect(rs) == Ok::<Seq<T>, SqlError>(vs),
{
    lemma_collect_all(rs, vs);
}

/// `fits_each` only depends on the elements of the domain sequence.
pub proof fn lemma_fits_each_pointwise<T>()
    ensures
        forall|rs: Seq<Result<T, SqlError>>, fs1: Seq<bool>, fs2: Seq<bool>|
            fs1.len() == fs2.len() && (forall|j: int| 0 <= j < fs1.len() ==> fs1[j] == fs2[j])
            ==> #[trigger] fits_each(rs, fs1) == #[trigger] fits_each(rs, fs2),
{
    assert forall|rs: Seq<Result<T, SqlError>>, fs1: Seq<bool>, fs2: Seq<bool>|
        fs1.len() == fs2.len() && (forall|j: int| 0 <= j < fs1.len() ==> fs1[j] == fs2[j])
        implies #[trigger] fits_each(rs, fs1) == #[trigger] fits_each(rs, fs2) by {
        assert(fs1 =~= fs2);
    }
}

// ------------------------------------------------------------------ per-row outcomes of the operators

/// WHERE condition of every input row (`ctx`: the outer context).
pub open spec fn filter_results(db: Database, ctx: Row, rows: Seq<Row>, pred: Pred) -> Seq<Result<Truth, SqlError>> {
    Seq::new(rows.len(), |i: int| eval_pred(db, ctx + rows[i], pred))
}

/// Output row of every input row.
pub open spec fn project_results(db: Database, ctx: Row, rows: Seq<Row>, exprs: Seq<Expr>) -> Seq<Result<Row, SqlError>> {
    Seq::new(rows.len(), |i: int| eval_exprs(db, ctx + rows[i], exprs))
}

/// ON condition of one left row (`env` = context + left row) against every right row.
pub open spec fn join_results(db: Database, env: Row, right: Seq<Row>, on: Pred) -> Seq<Result<Truth, SqlError>> {
    Seq::new(right.len(), |j: int| eval_pred(db, env + right[j], on))
}

/// ON conditions of every left row against all right rows (each collected first-error).
pub open spec fn left_join_results(db: Database, ctx: Row, left: Seq<Row>, right: Seq<Row>, on: Pred)
    -> Seq<Result<Seq<Truth>, SqlError>>
{
    Seq::new(left.len(), |i: int| collect(Seq::new(right.len(), |j: int| eval_pred(db, ctx + left[i] + right[j], on))))
}

/// Aggregate arguments of every input row (`spec::eval::agg_args`).
pub open spec fn agg_args_results(db: Database, ctx: Row, rows: Seq<Row>, aggs: Seq<Agg>) -> Seq<Result<Row, SqlError>> {
    Seq::new(rows.len(), |i: int| agg_args(db, ctx + rows[i], aggs))
}

/// Per input row of a GROUP BY: `spec::eval::group_input` (written out as in `eval_query`; see
/// `lemma_group_input_results`).
pub open spec fn group_input_results(db: Database, ctx: Row, rows: Seq<Row>, keys: Seq<Expr>, aggs: Seq<Agg>)
    -> Seq<Result<(Row, Row), SqlError>>
{
    Seq::new(rows.len(), |i: int|
        match eval_exprs(db, ctx + rows[i], keys) {
            Err(err) => Err(err),
            Ok(k) => match agg_args(db, ctx + rows[i], aggs) {
                Err(err) => Err(err),
                Ok(a) => Ok((k, a)),
            },
        })
}

pub proof fn lemma_group_input_results(db: Database, ctx: Row, rows: Seq<Row>, keys: Seq<Expr>, aggs: Seq<Agg>, i: int)
    requires 0 <= i < rows.len(),
    ensures group_input_results(db, ctx, rows, keys, aggs)[i] == group_input(db, ctx + rows[i], keys, aggs),
{
}

/// Value of every aggregate over its argument column (`args`: one argument row per input row).
pub open spec fn agg_value_results(aggs: Seq<Agg>, args: Seq<Row>) -> Seq<Result<Val, SqlError>> {
    Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(args, j)))
}

/// Output row of every group (first-occurrence order of the distinct keys): key + aggregate values.
pub open spec fn group_results(aggs: Seq<Agg>, keys: Seq<Row>, args: Seq<Row>) -> Seq<Result<Row, SqlError>> {
    let ks = distinct_rows(keys);
    Seq::new(ks.len(), |g: int|
        match agg_row(aggs, group_members(keys, args, ks[g])) {
            Ok(a) => Ok(ks[g] + a),
            Err(e) => Err(e),
        })
}

// ------------------------------------------------------------------ SUM / AVG absolute mass

/// Largest scale of the numeric values (0 when there is none): the result scale of `spec::relation::num_sum`
/// (`exec::relational::aggregate::lemma_num_sum_at`).
pub open spec fn num_max_scale(vs: Seq<Val>) -> nat
    decreases vs.len(),
{
    if vs.len() == 0 {
        0
    } else {
        match vs.last() {
            Val::Num { coeff, scale } => max_nat(num_max_scale(vs.drop_last()), scale),
            _ => num_max_scale(vs.drop_last()),
        }
    }
}

/// Absolute mass of the numeric values at scale `t`: the sum of `|coeff| * 10^(t - scale)` (used with `t` at least
/// every value's scale; other values count 0).
pub open spec fn num_mass_at(vs: Seq<Val>, t: nat) -> int
    decreases vs.len(),
{
    if vs.len() == 0 {
        0
    } else {
        num_mass_at(vs.drop_last(), t) + match vs.last() {
            Val::Num { coeff, scale } => abs(coeff) * pow10((t - scale) as nat),
            _ => 0,
        }
    }
}

/// Absolute mass of the integer values: the sum of `|x|` (other values count 0).
pub open spec fn int_mass(vs: Seq<Val>) -> int
    decreases vs.len(),
{
    if vs.len() == 0 {
        0
    } else {
        int_mass(vs.drop_last()) + match vs.last() {
            Val::Int(x) => abs(x),
            _ => 0,
        }
    }
}

/// Absolute mass of the arguments of a `SUM` / `AVG` of operand kind `kind`: numeric coefficients at the group's
/// result scale, integers at scale 0.
pub open spec fn sum_mass(kind: NumKind, vs: Seq<Val>) -> int {
    match kind {
        NumKind::Numeric => num_mass_at(vs, num_max_scale(vs)),
        _ => int_mass(vs),
    }
}

/// Capacity condition of `SUM` / `AVG`: the absolute mass is `i128`-representable.
pub open spec fn sum_mass_fits(kind: NumKind, vs: Seq<Val>) -> bool {
    sum_mass(kind, vs) <= i128::MAX as int
}

// ------------------------------------------------------------------ the domain predicates
//
// `fits_expr`/`fits_exprs` (`exec::domain`), `project_fs`, `agg_args_fs`, `fits_agg_args`, `agg_arg_fs`,
// `fits_agg_arg`, `fits_pred` and `fits_query` are one mutual recursion (termination: strict sub-AST, or the
// same list at a smaller rank; list elements index-guarded).

/// Domain of a condition under the environment `env` (context + row).
pub open spec fn fits_pred(db: Database, env: Row, p: Pred) -> bool
    decreases p,
{
    match p {
        Pred::Cmp { op, a, b } => fits_expr(db, env, a) && (eval_expr(db, env, a) is Ok ==> fits_expr(db, env, b)),
        Pred::And(a, b) => fits_pred(db, env, *a) && (eval_pred(db, env, *a) is Ok ==> fits_pred(db, env, *b)),
        Pred::Or(a, b) => fits_pred(db, env, *a) && (eval_pred(db, env, *a) is Ok ==> fits_pred(db, env, *b)),
        Pred::Not(a) => fits_pred(db, env, *a),
        Pred::IsNull(e) => fits_expr(db, env, e),
        Pred::OfBool(e) => fits_expr(db, env, e),
        Pred::Exists(q) => fits_query(db, env, *q),
        Pred::AnyCmp { op, e, q } => fits_expr(db, env, e) && (eval_expr(db, env, e) is Ok ==> fits_query(db, env, *q)),
    }
}

/// Domain of a query under the outer context `ctx`: every child, then every per-row evaluation up to the first
/// SQL error, then the aggregate values (`fits_agg_row`, `fits_groups`).
pub open spec fn fits_query(db: Database, ctx: Row, q: Query) -> bool
    decreases q,
{
    match q {
        Query::Table(_) => true,
        Query::Filter { pred, input } => fits_query(db, ctx, *input) && match eval_query(db, ctx, *input) {
            Err(_) => true,
            Ok(rows) => fits_each(filter_results(db, ctx, rows, pred),
                Seq::new(rows.len(), |i: int| fits_pred(db, ctx + rows[i], pred))),
        },
        Query::Project { exprs, input } => fits_query(db, ctx, *input) && match eval_query(db, ctx, *input) {
            Err(_) => true,
            Ok(rows) => fits_each(project_results(db, ctx, rows, exprs), project_fs(db, ctx, rows, exprs)),
        },
        Query::Product { left, right } => fits_query(db, ctx, *left)
            && (eval_query(db, ctx, *left) is Ok ==> fits_query(db, ctx, *right)),
        Query::LeftJoin { left, right, on } => query_arity(db.schema, *right) <= usize::MAX
            && fits_query(db, ctx, *left) && match eval_query(db, ctx, *left) {
                Err(_) => true,
                Ok(l) => fits_query(db, ctx, *right) && match eval_query(db, ctx, *right) {
                    Err(_) => true,
                    Ok(r) => fits_each(left_join_results(db, ctx, l, r, on),
                        Seq::new(l.len(), |i: int| fits_each(join_results(db, ctx + l[i], r, on),
                            Seq::new(r.len(), |j: int| fits_pred(db, ctx + l[i] + r[j], on))))),
                },
            },
        Query::Aggregate { aggs, input } => fits_query(db, ctx, *input) && match eval_query(db, ctx, *input) {
            Err(_) => true,
            Ok(rows) => fits_each(agg_args_results(db, ctx, rows, aggs), agg_args_fs(db, ctx, rows, aggs))
                && match collect(agg_args_results(db, ctx, rows, aggs)) {
                    Err(_) => true,
                    Ok(args) => fits_agg_row(aggs, args),
                },
        },
        Query::GroupBy { keys, aggs, input } => fits_query(db, ctx, *input) && match eval_query(db, ctx, *input) {
            Err(_) => true,
            Ok(rows) => fits_each(group_input_results(db, ctx, rows, keys, aggs),
                    Seq::new(rows.len(), |i: int| fits_exprs(db, ctx + rows[i], keys)
                        && (eval_exprs(db, ctx + rows[i], keys) is Ok ==> fits_agg_args(db, ctx + rows[i], aggs))))
                && match collect(group_input_results(db, ctx, rows, keys, aggs)) {
                    Err(_) => true,
                    Ok(prepared) => fits_groups(aggs, prepared.map_values(|p: (Row, Row)| p.0),
                        prepared.map_values(|p: (Row, Row)| p.1)),
                },
        },
        Query::Distinct(input) => fits_query(db, ctx, *input),
    }
}

/// Domain of the output row of every input row of a projection.
pub open spec fn project_fs(db: Database, ctx: Row, rows: Seq<Row>, exprs: Seq<Expr>) -> Seq<bool>
    decreases exprs, 1nat,
{
    Seq::new(rows.len(), |i: int| fits_exprs(db, ctx + rows[i], exprs))
}

/// Domain of the aggregate arguments of every input row.
pub open spec fn agg_args_fs(db: Database, ctx: Row, rows: Seq<Row>, aggs: Seq<Agg>) -> Seq<bool>
    decreases aggs, 2nat,
{
    Seq::new(rows.len(), |i: int| fits_agg_args(db, ctx + rows[i], aggs))
}

/// Domain of the argument of every aggregate of one row.
pub open spec fn agg_arg_fs(db: Database, env: Row, aggs: Seq<Agg>) -> Seq<bool>
    decreases aggs, 0nat,
{
    Seq::new(aggs.len(), |j: int| if 0 <= j < aggs.len() { fits_agg_arg(db, env, aggs[j]) } else { true })
}

/// Domain of the argument of one aggregate on one row (`spec::eval::agg_arg`).
pub open spec fn fits_agg_arg(db: Database, env: Row, a: Agg) -> bool
    decreases a,
{
    match a {
        Agg::CountStar => true,
        Agg::Count(e) => fits_expr(db, env, e),
        Agg::Sum { kind, arg } => fits_expr(db, env, arg),
        Agg::Min(e) => fits_expr(db, env, e),
        Agg::Max(e) => fits_expr(db, env, e),
        Agg::Avg { kind, arg } => fits_expr(db, env, arg),
        Agg::DistinctAgg(inner) => fits_agg_arg(db, env, *inner),
    }
}

/// Domain of the arguments of all aggregates on one row (`spec::eval::agg_args`).
pub open spec fn fits_agg_args(db: Database, env: Row, aggs: Seq<Agg>) -> bool
    decreases aggs, 1nat,
{
    fits_each(agg_arg_results(db, env, aggs), agg_arg_fs(db, env, aggs))
}

/// Domain of one aggregate value over its argument values `vs` (`spec::relation::agg_value`).
pub open spec fn fits_agg_value(a: Agg, vs: Seq<Val>) -> bool
    decreases a,
{
    match a {
        Agg::Sum { kind, arg } => all_of_kind(kind, vs) ==> sum_mass_fits(kind, vs),
        // AVG's domain includes the SUM mass condition (`exec::aggs::avg::fits_avg_value`).
        Agg::Avg { kind, arg } => crate::exec::aggs::avg::fits_avg_value(kind, vs),
        Agg::DistinctAgg(inner) => fits_agg_value(*inner, distinct_vals(vs)),
        _ => true,
    }
}

/// Domain of every aggregate value, over the argument column of each (`agg_value_results`).
pub open spec fn agg_value_fs(aggs: Seq<Agg>, args: Seq<Row>) -> Seq<bool> {
    Seq::new(aggs.len(), |j: int| fits_agg_value(aggs[j], column(args, j)))
}

/// Domain of the aggregate row of one group (`spec::relation::agg_row`).
pub open spec fn fits_agg_row(aggs: Seq<Agg>, args: Seq<Row>) -> bool {
    fits_each(agg_value_results(aggs, args), agg_value_fs(aggs, args))
}

/// Domain of one GROUP BY input row (`spec::eval::group_input`).
pub open spec fn fits_group_input(db: Database, env: Row, keys: Seq<Expr>, aggs: Seq<Agg>) -> bool {
    fits_exprs(db, env, keys) && (eval_exprs(db, env, keys) is Ok ==> fits_agg_args(db, env, aggs))
}

/// `fits_group_input` of every input row (the per-row domain of the `GroupBy` case of `fits_query`, named).
pub open spec fn group_input_fs(db: Database, ctx: Row, rows: Seq<Row>, keys: Seq<Expr>, aggs: Seq<Agg>) -> Seq<bool> {
    Seq::new(rows.len(), |i: int| fits_group_input(db, ctx + rows[i], keys, aggs))
}

/// Domain of the aggregate row of every group (`group_results`).
pub open spec fn groups_fs(aggs: Seq<Agg>, keys: Seq<Row>, args: Seq<Row>) -> Seq<bool> {
    let ks = distinct_rows(keys);
    Seq::new(ks.len(), |g: int| fits_agg_row(aggs, group_members(keys, args, ks[g])))
}

/// Domain of the groups of a GROUP BY (`spec::relation::group_rows`), up to the first SQL error.
pub open spec fn fits_groups(aggs: Seq<Agg>, keys: Seq<Row>, args: Seq<Row>) -> bool {
    fits_each(group_results(aggs, keys, args), groups_fs(aggs, keys, args))
}

pub proof fn lemma_project_fs_index(db: Database, ctx: Row, rows: Seq<Row>, exprs: Seq<Expr>)
    ensures
        project_fs(db, ctx, rows, exprs).len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> #[trigger] project_fs(db, ctx, rows, exprs)[i] == fits_exprs(db, ctx + rows[i], exprs),
{
}

pub proof fn lemma_agg_args_fs_index(db: Database, ctx: Row, rows: Seq<Row>, aggs: Seq<Agg>)
    ensures
        agg_args_fs(db, ctx, rows, aggs).len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> #[trigger] agg_args_fs(db, ctx, rows, aggs)[i] == fits_agg_args(db, ctx + rows[i], aggs),
{
}

pub proof fn lemma_agg_arg_fs_index(db: Database, env: Row, aggs: Seq<Agg>)
    ensures
        agg_arg_fs(db, env, aggs).len() == aggs.len(),
        forall|j: int| 0 <= j < aggs.len() ==> #[trigger] agg_arg_fs(db, env, aggs)[j] == fits_agg_arg(db, env, aggs[j]),
{
}

pub proof fn lemma_group_input_unfold(db: Database, env: Row, keys: Seq<Expr>, aggs: Seq<Agg>)
    ensures
        group_input(db, env, keys, aggs) == match eval_exprs(db, env, keys) {
            Err(err) => Err(err),
            Ok(k) => match agg_args(db, env, aggs) {
                Err(err) => Err(err),
                Ok(a) => Ok::<(Row, Row), SqlError>((k, a)),
            },
        },
        fits_group_input(db, env, keys, aggs)
            == (fits_exprs(db, env, keys) && (eval_exprs(db, env, keys) is Ok ==> fits_agg_args(db, env, aggs))),
{
}

// ------------------------------------------------------------------ Filter / LEFT JOIN per-row domains, quantified
//
// `fits_query` states these per-row domains as `fits_each` over inline sequences; the `*_fs` sequences name them
// and the `*_fits` predicates state them with a quantifier. The lemmas below prove the forms equal.

/// Domain of the condition of every input row of a filter.
pub open spec fn filter_fs(db: Database, ctx: Row, rows: Seq<Row>, pred: Pred) -> Seq<bool> {
    Seq::new(rows.len(), |i: int| fits_pred(db, ctx + rows[i], pred))
}

/// Domain of the ON condition of one left row (`env`) against every right row.
pub open spec fn join_fs(db: Database, env: Row, right: Seq<Row>, on: Pred) -> Seq<bool> {
    Seq::new(right.len(), |j: int| fits_pred(db, env + right[j], on))
}

/// Domain of the ON conditions of every left row (`join_row_fits`).
pub open spec fn left_join_fs(db: Database, ctx: Row, left: Seq<Row>, right: Seq<Row>, on: Pred) -> Seq<bool> {
    Seq::new(left.len(), |i: int| join_row_fits(db, ctx + left[i], right, on))
}

/// Domain of the per-row conditions of a filter (quantified form of the `Filter` case of `fits_query`).
pub open spec fn filter_fits(db: Database, ctx: Row, rows: Seq<Row>, pred: Pred) -> bool {
    forall|i: int| 0 <= i < rows.len() && ok_before(filter_results(db, ctx, rows, pred), i)
        ==> #[trigger] fits_pred(db, ctx + rows[i], pred)
}

/// Domain of the ON conditions of one left row against the right rows.
pub open spec fn join_row_fits(db: Database, env: Row, right: Seq<Row>, on: Pred) -> bool {
    forall|j: int| 0 <= j < right.len() && ok_before(join_results(db, env, right, on), j)
        ==> #[trigger] fits_pred(db, env + right[j], on)
}

/// Domain of the ON conditions of a LEFT JOIN (quantified form of the `LeftJoin` case of `fits_query`).
pub open spec fn left_join_fits(db: Database, ctx: Row, left: Seq<Row>, right: Seq<Row>, on: Pred) -> bool {
    forall|i: int| 0 <= i < left.len() && ok_before(left_join_results(db, ctx, left, right, on), i)
        ==> #[trigger] join_row_fits(db, ctx + left[i], right, on)
}

pub proof fn lemma_filter_fits_each(db: Database, ctx: Row, rows: Seq<Row>, pred: Pred)
    ensures
        fits_each(filter_results(db, ctx, rows, pred), filter_fs(db, ctx, rows, pred)) == filter_fits(db, ctx, rows, pred),
        fits_each(filter_results(db, ctx, rows, pred), Seq::new(rows.len(), |i: int| fits_pred(db, ctx + rows[i], pred)))
            == filter_fits(db, ctx, rows, pred),
{
    hide(eval_pred);
    hide(fits_pred);
    let fs = filter_fs(db, ctx, rows, pred);
    let rs = filter_results(db, ctx, rows, pred);
    if fits_each(rs, fs) {
        assert forall|i: int| 0 <= i < rows.len() && ok_before(rs, i)
            implies #[trigger] fits_pred(db, ctx + rows[i], pred) by {
            assert(fs[i]);
        }
    }
    if filter_fits(db, ctx, rows, pred) {
        assert forall|i: int| 0 <= i < fs.len() && ok_before(rs, i) implies #[trigger] fs[i] by {
            assert(fits_pred(db, ctx + rows[i], pred));
        }
    }
}

pub proof fn lemma_join_row_fits_each(db: Database, env: Row, r: Seq<Row>, on: Pred)
    ensures
        fits_each(join_results(db, env, r, on), join_fs(db, env, r, on)) == join_row_fits(db, env, r, on),
        fits_each(join_results(db, env, r, on), Seq::new(r.len(), |j: int| fits_pred(db, env + r[j], on)))
            == join_row_fits(db, env, r, on),
{
    hide(eval_pred);
    hide(fits_pred);
    let fs = join_fs(db, env, r, on);
    let rs = join_results(db, env, r, on);
    if fits_each(rs, fs) {
        assert forall|j: int| 0 <= j < r.len() && ok_before(rs, j)
            implies #[trigger] fits_pred(db, env + r[j], on) by {
            assert(fs[j]);
        }
    }
    if join_row_fits(db, env, r, on) {
        assert forall|j: int| 0 <= j < fs.len() && ok_before(rs, j) implies #[trigger] fs[j] by {
            assert(fits_pred(db, env + r[j], on));
        }
    }
}

/// The inline per-left-row domain of the `LeftJoin` case of `fits_query` is `left_join_fits`.
proof fn lemma_left_join_fits_each(db: Database, ctx: Row, l: Seq<Row>, r: Seq<Row>, on: Pred)
    ensures
        fits_each(left_join_results(db, ctx, l, r, on), Seq::new(l.len(), |i: int| fits_each(join_results(db, ctx + l[i], r, on),
            Seq::new(r.len(), |j: int| fits_pred(db, ctx + l[i] + r[j], on))))) == left_join_fits(db, ctx, l, r, on),
{
    hide(eval_pred);
    let fs = Seq::new(l.len(), |i: int| fits_each(join_results(db, ctx + l[i], r, on),
        Seq::new(r.len(), |j: int| fits_pred(db, ctx + l[i] + r[j], on))));
    let rs = left_join_results(db, ctx, l, r, on);
    assert forall|i: int| 0 <= i < l.len() implies fs[i] == #[trigger] join_row_fits(db, ctx + l[i], r, on) by {
        lemma_join_row_fits_each(db, ctx + l[i], r, on);
    }
    if fits_each(rs, fs) {
        assert forall|i: int| 0 <= i < l.len() && ok_before(rs, i)
            implies #[trigger] join_row_fits(db, ctx + l[i], r, on) by {
            assert(fs[i]);
        }
    }
    if left_join_fits(db, ctx, l, r, on) {
        assert forall|i: int| 0 <= i < fs.len() && ok_before(rs, i) implies #[trigger] fs[i] by {
            assert(join_row_fits(db, ctx + l[i], r, on));
        }
    }
}

pub proof fn lemma_left_join_fs(db: Database, ctx: Row, l: Seq<Row>, r: Seq<Row>, on: Pred)
    ensures fits_each(left_join_results(db, ctx, l, r, on), left_join_fs(db, ctx, l, r, on)) == left_join_fits(db, ctx, l, r, on),
{
    hide(eval_pred);
    hide(join_row_fits);
    let fs = left_join_fs(db, ctx, l, r, on);
    let rs = left_join_results(db, ctx, l, r, on);
    if fits_each(rs, fs) {
        assert forall|i: int| 0 <= i < l.len() && ok_before(rs, i)
            implies #[trigger] join_row_fits(db, ctx + l[i], r, on) by {
            assert(fs[i]);
        }
    }
    if left_join_fits(db, ctx, l, r, on) {
        assert forall|i: int| 0 <= i < fs.len() && ok_before(rs, i) implies #[trigger] fs[i] by {
            assert(join_row_fits(db, ctx + l[i], r, on));
        }
    }
}

// ------------------------------------------------------------------ denotation of one constructor, named

pub proof fn lemma_eval_filter(db: Database, ctx: Row, pred: Pred, input: Box<Query>)
    ensures
        eval_query(db, ctx, Query::Filter { pred, input }) == match eval_query(db, ctx, *input) {
            Err(e) => Err(e),
            Ok(rows) => match collect(filter_results(db, ctx, rows, pred)) {
                Err(e) => Err(e),
                Ok(truths) => Ok(keep_true(rows, truths)),
            },
        },
{
    lemma_collect_pointwise::<Truth>();
}

pub proof fn lemma_eval_project(db: Database, ctx: Row, exprs: Seq<Expr>, input: Box<Query>)
    ensures
        eval_query(db, ctx, Query::Project { exprs, input }) == match eval_query(db, ctx, *input) {
            Err(e) => Err(e),
            Ok(rows) => collect(project_results(db, ctx, rows, exprs)),
        },
{
    lemma_collect_pointwise::<Row>();
}

pub proof fn lemma_eval_left_join(db: Database, ctx: Row, left: Box<Query>, right: Box<Query>, on: Pred)
    ensures
        eval_query(db, ctx, Query::LeftJoin { left, right, on }) == match eval_query(db, ctx, *left) {
            Err(e) => Err(e),
            Ok(l) => match eval_query(db, ctx, *right) {
                Err(e) => Err(e),
                Ok(r) => match collect(left_join_results(db, ctx, l, r, on)) {
                    Err(e) => Err(e),
                    Ok(truths) => Ok(left_join_rows(l, r, truths, query_arity(db.schema, *right))),
                },
            },
        },
{
    lemma_collect_pointwise::<Truth>();
    lemma_collect_pointwise::<Seq<Truth>>();
}

pub proof fn lemma_eval_aggregate(db: Database, ctx: Row, aggs: Seq<Agg>, input: Box<Query>)
    ensures
        eval_query(db, ctx, Query::Aggregate { aggs, input }) == match eval_query(db, ctx, *input) {
            Err(e) => Err(e),
            Ok(rows) => match collect(agg_args_results(db, ctx, rows, aggs)) {
                Err(e) => Err(e),
                Ok(args) => match agg_row(aggs, args) {
                    Err(e) => Err(e),
                    Ok(row) => Ok(seq![row]),
                },
            },
        },
{
    lemma_collect_pointwise::<Row>();
}

pub proof fn lemma_eval_group_by(db: Database, ctx: Row, keys: Seq<Expr>, aggs: Seq<Agg>, input: Box<Query>)
    ensures
        eval_query(db, ctx, Query::GroupBy { keys, aggs, input }) == match eval_query(db, ctx, *input) {
            Err(e) => Err(e),
            Ok(rows) => match collect(group_input_results(db, ctx, rows, keys, aggs)) {
                Err(e) => Err(e),
                Ok(prepared) => collect(group_results(aggs, prepared.map_values(|p: (Row, Row)| p.0),
                    prepared.map_values(|p: (Row, Row)| p.1))),
            },
        },
{
    lemma_collect_pointwise::<(Row, Row)>();
}

pub proof fn lemma_agg_row(aggs: Seq<Agg>, args: Seq<Row>)
    ensures agg_row(aggs, args) == collect(agg_value_results(aggs, args)),
{
}

pub proof fn lemma_agg_args(db: Database, env: Row, aggs: Seq<Agg>)
    ensures
        agg_args(db, env, aggs) == collect(agg_arg_results(db, env, aggs)),
        fits_agg_args(db, env, aggs) == fits_each(agg_arg_results(db, env, aggs), agg_arg_fs(db, env, aggs)),
{
}

// ------------------------------------------------------------------ domain of one constructor, named

pub proof fn lemma_fits_filter(db: Database, ctx: Row, pred: Pred, input: Box<Query>)
    ensures
        fits_query(db, ctx, Query::Filter { pred, input }) == (fits_query(db, ctx, *input)
            && match eval_query(db, ctx, *input) {
                Err(_) => true,
                Ok(rows) => filter_fits(db, ctx, rows, pred),
            }),
{
    hide(eval_query);
    hide(eval_pred);
    lemma_fits_each_pointwise::<Truth>();
    match eval_query(db, ctx, *input) {
        Err(_) => {},
        Ok(rows) => {
            lemma_filter_fits_each(db, ctx, rows, pred);
        },
    }
}

pub proof fn lemma_fits_left_join(db: Database, ctx: Row, left: Box<Query>, right: Box<Query>, on: Pred)
    ensures
        fits_query(db, ctx, Query::LeftJoin { left, right, on }) == (query_arity(db.schema, *right) <= usize::MAX
            && fits_query(db, ctx, *left) && match eval_query(db, ctx, *left) {
                Err(_) => true,
                Ok(l) => fits_query(db, ctx, *right) && match eval_query(db, ctx, *right) {
                    Err(_) => true,
                    Ok(r) => left_join_fits(db, ctx, l, r, on),
                },
            }),
{
    hide(eval_query);
    hide(eval_pred);
    lemma_fits_each_pointwise::<Truth>();
    lemma_fits_each_pointwise::<Seq<Truth>>();
    match eval_query(db, ctx, *left) {
        Err(_) => {},
        Ok(l) => match eval_query(db, ctx, *right) {
            Err(_) => {},
            Ok(r) => {
                lemma_left_join_fits_each(db, ctx, l, r, on);
            },
        },
    }
}

/// The `GroupBy` case of `fits_query` with the per-row domain named (`group_input_fs`).
pub proof fn lemma_fits_group_by(db: Database, ctx: Row, keys: Seq<Expr>, aggs: Seq<Agg>, input: Box<Query>)
    ensures
        fits_query(db, ctx, Query::GroupBy { keys, aggs, input }) == (fits_query(db, ctx, *input)
            && match eval_query(db, ctx, *input) {
                Err(_) => true,
                Ok(rows) => fits_each(group_input_results(db, ctx, rows, keys, aggs), group_input_fs(db, ctx, rows, keys, aggs))
                    && match collect(group_input_results(db, ctx, rows, keys, aggs)) {
                        Err(_) => true,
                        Ok(prepared) => fits_groups(aggs, prepared.map_values(|p: (Row, Row)| p.0),
                            prepared.map_values(|p: (Row, Row)| p.1)),
                    },
            }),
{
    hide(eval_query);
    lemma_fits_each_pointwise::<(Row, Row)>();
    match eval_query(db, ctx, *input) {
        Err(_) => {},
        Ok(rows) => {
            let fs = group_input_fs(db, ctx, rows, keys, aggs);
            let inline = Seq::new(rows.len(), |i: int| fits_exprs(db, ctx + rows[i], keys)
                && (eval_exprs(db, ctx + rows[i], keys) is Ok ==> fits_agg_args(db, ctx + rows[i], aggs)));
            assert(fs =~= inline);
        },
    }
}

} // verus!
