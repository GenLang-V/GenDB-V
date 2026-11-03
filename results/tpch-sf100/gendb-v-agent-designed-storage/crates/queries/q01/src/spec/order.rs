//! Top-level `ORDER BY` / `LIMIT` / `OFFSET` as an allowed-output relation that is exact about ties.
//!
//! `ordered_ok(db, oq, out)`: `out` is the body's error, or some permutation of the body's bag, sorted by the
//! keys, sliced by OFFSET/LIMIT. Any order among key-equal rows and any choice among key-equal rows at the
//! LIMIT boundary is allowed; nothing else is. `denote_top` is the canonical deterministic witness (stable
//! insertion sort of the canonical body sequence); `bridge::order::lemma_denote_top_ok` proves
//! `ordered_ok(db, oq, denote_top(db, oq))` for checked statements on well-formed databases.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;

verus! {

/// Comparison of two rows on one key: NULLs are placed by `nulls_first` regardless of direction (PostgreSQL),
/// non-NULL values by `compare`, reversed for DESC.
pub open spec fn key_cmp(k: OrderKey, r1: Row, r2: Row) -> int {
    let a = if k.col < r1.len() { r1[k.col as int] } else { Val::Null };
    let b = if k.col < r2.len() { r2[k.col as int] } else { Val::Null };
    if a is Null && b is Null {
        0
    } else if a is Null {
        if k.nulls_first { -1 } else { 1 }
    } else if b is Null {
        if k.nulls_first { 1 } else { -1 }
    } else {
        let c = match compare(a, b) { Some(c) => c, None => 0 };
        if k.desc { -c } else { c }
    }
}

/// Lexicographic comparison over the keys.
pub open spec fn keys_cmp(keys: Seq<OrderKey>, r1: Row, r2: Row) -> int
    decreases keys.len(),
{
    if keys.len() == 0 {
        0
    } else {
        let c = key_cmp(keys[0], r1, r2);
        if c != 0 { c } else { keys_cmp(keys.drop_first(), r1, r2) }
    }
}

/// `s` is ordered by the keys (key-equal rows in any order).
pub open spec fn sorted_by(keys: Seq<OrderKey>, s: Seq<Row>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> keys_cmp(keys, #[trigger] s[i], #[trigger] s[j]) <= 0
}

/// OFFSET then LIMIT.
pub open spec fn slice_rows(s: Seq<Row>, offset: nat, limit: Option<nat>) -> Seq<Row> {
    let lo = if offset <= s.len() { offset as int } else { s.len() as int };
    let hi = match limit {
        Some(n) => if lo + n <= s.len() { lo + n } else { s.len() as int },
        None => s.len() as int,
    };
    s.subrange(lo, hi)
}

/// The body's rows in canonical order (empty outer context).
pub open spec fn denote_body(db: Database, oq: OrderedQuery) -> Result<Relation, SqlError> {
    eval_query(db, Seq::empty(), oq.body)
}

/// The allowed outputs of a top-level statement.
pub open spec fn ordered_ok(db: Database, oq: OrderedQuery, out: Result<Relation, SqlError>) -> bool {
    match denote_body(db, oq) {
        Err(e) => out == Err::<Relation, SqlError>(e),
        Ok(rows) => exists|p: Seq<Row>| #![trigger sorted_by(oq.keys, p)]
            p.to_multiset() == rows.to_multiset() && sorted_by(oq.keys, p)
                && out == Ok::<Relation, SqlError>(slice_rows(p, oq.offset, oq.limit)),
    }
}

/// Stable insertion of `r` into sorted `s` (after all rows that are not greater).
pub open spec fn insert_sorted(keys: Seq<OrderKey>, s: Seq<Row>, r: Row) -> Seq<Row>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![r]
    } else if keys_cmp(keys, s.last(), r) <= 0 {
        s.push(r)
    } else {
        insert_sorted(keys, s.drop_last(), r).push(s.last())
    }
}

/// Stable insertion sort by the keys.
pub open spec fn sort_rows(keys: Seq<OrderKey>, s: Seq<Row>) -> Seq<Row>
    decreases s.len(),
{
    if s.len() == 0 { s } else { insert_sorted(keys, sort_rows(keys, s.drop_last()), s.last()) }
}

/// Canonical deterministic output of a top-level statement.
pub open spec fn denote_top(db: Database, oq: OrderedQuery) -> Result<Relation, SqlError> {
    match denote_body(db, oq) {
        Err(e) => Err(e),
        Ok(rows) => Ok(slice_rows(sort_rows(oq.keys, rows), oq.offset, oq.limit)),
    }
}

} // verus!
