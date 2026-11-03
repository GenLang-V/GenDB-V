//! Operator helpers over already-evaluated inputs (no AST recursion here). The denotation (`spec::eval`)
//! evaluates children and per-row expressions, then applies one of these; operator laws live next to them.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::int::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::equality::*;
use crate::spec::aggs::avg::*;
use crate::spec::aggs::minmax::*;

verus! {

// ------------------------------------------------------------------ error-strict collection

/// First error in sequence order, otherwise all values (canonical error-strict evaluation).
pub open spec fn collect<T>(rs: Seq<Result<T, SqlError>>) -> Result<Seq<T>, SqlError>
    decreases rs.len(),
{
    if rs.len() == 0 {
        Ok(Seq::empty())
    } else {
        match collect(rs.drop_last()) {
            Err(e) => Err(e),
            Ok(vs) => match rs.last() {
                Err(e) => Err(e),
                Ok(v) => Ok(vs.push(v)),
            },
        }
    }
}

// ------------------------------------------------------------------ row operators (WHERE, cross product, LEFT JOIN)

/// Rows whose truth value is `True` (`truths[i]` belongs to `rows[i]`).
pub open spec fn keep_true(rows: Seq<Row>, truths: Seq<Truth>) -> Seq<Row>
    decreases rows.len(),
{
    if rows.len() == 0 || truths.len() == 0 {
        Seq::empty()
    } else {
        let init = keep_true(rows.drop_last(), truths.drop_last());
        if truths.last() is True { init.push(rows.last()) } else { init }
    }
}

/// Left-major cross product.
pub open spec fn product_rows(left: Seq<Row>, right: Seq<Row>) -> Seq<Row>
    decreases left.len(),
{
    if left.len() == 0 {
        Seq::empty()
    } else {
        product_rows(left.drop_last(), right) + right.map_values(|r: Row| left.last() + r)
    }
}

/// `n` NULLs (the right side of an unmatched LEFT JOIN row).
pub open spec fn null_row(n: nat) -> Row {
    Seq::new(n, |i: int| Val::Null)
}

/// LEFT JOIN rows of one left row: the matching right rows appended, or one NULL-padded row.
pub open spec fn left_join_one(l: Row, right: Seq<Row>, truths: Seq<Truth>, right_arity: nat) -> Seq<Row> {
    let matched = keep_true(right, truths);
    if matched.len() == 0 {
        seq![l + null_row(right_arity)]
    } else {
        matched.map_values(|r: Row| l + r)
    }
}

/// LEFT JOIN over all left rows (`truths[i][j]`: ON condition of left row i with right row j).
pub open spec fn left_join_rows(left: Seq<Row>, right: Seq<Row>, truths: Seq<Seq<Truth>>, right_arity: nat) -> Seq<Row>
    decreases left.len(),
{
    if left.len() == 0 || truths.len() == 0 {
        Seq::empty()
    } else {
        left_join_rows(left.drop_last(), right, truths.drop_last(), right_arity)
            + left_join_one(left.last(), right, truths.last(), right_arity)
    }
}

// ------------------------------------------------------------------ aggregate values

/// Column `j` of every row.
pub open spec fn column(rows: Seq<Row>, j: int) -> Seq<Val> {
    rows.map_values(|r: Row| r[j])
}

/// Number of non-NULL values.
pub open spec fn count_non_null(vs: Seq<Val>) -> nat
    decreases vs.len(),
{
    if vs.len() == 0 { 0 } else { count_non_null(vs.drop_last()) + if vs.last() is Null { 0nat } else { 1nat } }
}

/// Exact sum of the non-NULL integer values (non-integers count as 0; typing excludes them).
pub open spec fn int_sum(vs: Seq<Val>) -> int
    decreases vs.len(),
{
    if vs.len() == 0 {
        0
    } else {
        int_sum(vs.drop_last()) + match vs.last() { Val::Int(x) => x, _ => 0 }
    }
}

/// Exact sum of the non-NULL numeric values as `(coefficient, scale)` at the largest input scale. The
/// accumulation is mathematical, so its value does not depend on the row order.
pub open spec fn num_sum(vs: Seq<Val>) -> (int, nat)
    decreases vs.len(),
{
    if vs.len() == 0 {
        (0, 0)
    } else {
        let acc = num_sum(vs.drop_last());
        match vs.last() {
            Val::Num { coeff, scale } => (num_add_coeff(acc.0, acc.1, coeff, scale), max_nat(acc.1, scale)),
            _ => acc,
        }
    }
}

/// True when every non-NULL value is a numeric of the family `kind` (typing guarantees it).
pub open spec fn all_of_kind(kind: NumKind, vs: Seq<Val>) -> bool
    decreases vs.len(),
{
    vs.len() == 0 || (all_of_kind(kind, vs.drop_last()) && match vs.last() {
        Val::Null => true,
        Val::Int(_) => !(kind is Numeric),
        Val::Num { .. } => kind is Numeric,
        _ => false,
    })
}

/// Final value of one aggregate over its argument values (one per input row of the group; `CountStar`
/// ignores them). Range checks apply only to the final value. MIN/MAX/AVG are defined in `spec::aggs`;
/// `DistinctAgg` applies its inner aggregate to the distinct non-NULL values.
pub open spec fn agg_value(a: Agg, vs: Seq<Val>) -> Result<Val, SqlError>
    decreases a,
{
    match a {
        Agg::CountStar => int_result(IntKind::Int8, vs.len() as int),
        Agg::Count(_) => int_result(IntKind::Int8, count_non_null(vs) as int),
        Agg::Sum { kind, arg } => {
            if !all_of_kind(kind, vs) {
                Err(SqlError::TypeError)
            } else if count_non_null(vs) == 0 {
                Ok(Val::Null)
            } else {
                match kind {
                    // Deviation D3 (as for AVG, `spec::aggs::avg`; recorded, not tested): PostgreSQL's transition
                    // `int4_sum` adds in int64 without an overflow check (numeric.c:6676-6722 at REL_18_3), so a sum
                    // past int64 wraps, which needs at least 2^32 rows; this sum is exact, and only its final value is
                    // range-checked as int8 (22003).
                    NumKind::Int4 => int_result(IntKind::Int8, int_sum(vs)),
                    NumKind::Int8 => num_result(int_sum(vs), 0),
                    NumKind::Numeric => {
                        let s = num_sum(vs);
                        num_result(s.0, s.1)
                    },
                }
            }
        },
        Agg::Min(_) => min_value(vs),
        Agg::Max(_) => max_value(vs),
        Agg::Avg { kind, arg } => avg_value(kind, vs),
        Agg::DistinctAgg(inner) => agg_value(*inner, distinct_vals(vs)),
    }
}

/// All aggregates of one group, left to right (`args[i][j]`: argument of aggregate j in row i).
pub open spec fn agg_row(aggs: Seq<Agg>, args: Seq<Row>) -> Result<Row, SqlError> {
    collect(Seq::new(aggs.len(), |j: int| agg_value(aggs[j], column(args, j))))
}

// ------------------------------------------------------------------ GROUP BY

/// Argument rows (`args[i]`) of the input rows whose key (`keys[i]`) is not distinct from `k`
/// (`spec::equality`), in input order.
pub open spec fn group_members(keys: Seq<Row>, args: Seq<Row>, k: Row) -> Seq<Row>
    decreases keys.len(),
{
    if keys.len() == 0 || args.len() == 0 {
        Seq::empty()
    } else {
        let init = group_members(keys.drop_last(), args.drop_last(), k);
        if row_not_distinct(keys.last(), k) { init.push(args.last()) } else { init }
    }
}

/// GROUP BY output: per class of not-distinct keys (first-occurrence order; the first key represents it) the row
/// `key ++ aggregates`.
pub open spec fn group_rows(aggs: Seq<Agg>, keys: Seq<Row>, args: Seq<Row>) -> Result<Seq<Row>, SqlError> {
    let ks = distinct_rows(keys);
    collect(Seq::new(ks.len(), |g: int|
        match agg_row(aggs, group_members(keys, args, ks[g])) {
            Ok(a) => Ok(ks[g] + a),
            Err(e) => Err(e),
        }))
}

} // verus!
