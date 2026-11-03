//! SQL value equality ("not distinct", PostgreSQL `IS NOT DISTINCT FROM`): the identity used by GROUP BY,
//! SELECT DISTINCT and DISTINCT aggregates. NULL is not distinct from NULL; two non-NULL values are not distinct
//! exactly when `compare` orders them equal, so numerics are compared by value (`1.0` and `1.00` are one class)
//! and text bytewise. A class is represented by its first occurrence in canonical order (reference choice R1 of
//! the VERUS_SQL_COVERAGE design; PostgreSQL's representative depends on the plan and may show another
//! equal-valued numeric scale).
//! Comparisons (`=`, IN) are the three-valued `spec::scalar::cmp_truth`, not this relation. Proofs (an
//! equivalence; structural equality on values of one exact scale): `bridge::equality`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;

verus! {

pub open spec fn val_not_distinct(a: Val, b: Val) -> bool {
    if a is Null || b is Null {
        a is Null && b is Null
    } else {
        compare(a, b) == Some(0int)
    }
}

/// Column by column (rows of different arity are distinct).
pub open spec fn row_not_distinct(r: Row, s: Row) -> bool {
    r.len() == s.len() && forall|i: int| 0 <= i < r.len() ==> val_not_distinct(#[trigger] r[i], s[i])
}

/// Some row of `rows` is not distinct from `r` (recursive, so evaluation can decide it).
pub open spec fn has_not_distinct(rows: Seq<Row>, r: Row) -> bool
    decreases rows.len(),
{
    rows.len() > 0 && (row_not_distinct(rows.last(), r) || has_not_distinct(rows.drop_last(), r))
}

/// One row per not-distinct class, the first occurrence, in first-occurrence order.
pub open spec fn distinct_rows(rows: Seq<Row>) -> Seq<Row>
    decreases rows.len(),
{
    if rows.len() == 0 {
        Seq::empty()
    } else {
        let d = distinct_rows(rows.drop_last());
        if has_not_distinct(d, rows.last()) { d } else { d.push(rows.last()) }
    }
}

/// Some value of `vs` is not distinct from `v`.
pub open spec fn has_val_not_distinct(vs: Seq<Val>, v: Val) -> bool
    decreases vs.len(),
{
    vs.len() > 0 && (val_not_distinct(vs.last(), v) || has_val_not_distinct(vs.drop_last(), v))
}

/// The non-NULL values, one per not-distinct class (first occurrence, first-occurrence order): the input of a
/// DISTINCT aggregate.
pub open spec fn distinct_vals(vs: Seq<Val>) -> Seq<Val>
    decreases vs.len(),
{
    if vs.len() == 0 {
        Seq::empty()
    } else {
        let d = distinct_vals(vs.drop_last());
        if vs.last() is Null || has_val_not_distinct(d, vs.last()) { d } else { d.push(vs.last()) }
    }
}

} // verus!
