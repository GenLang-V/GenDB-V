//! Outcome rules (optional author toolkit; nothing here names a query). The fixed claim of the entry states every
//! answer through `spec::order::ordered_ok` of the statement: `Ok(rows)` must be a sorted permutation of the body's
//! rows sliced by OFFSET/LIMIT, and `Err(e)` must be exactly the body's error. These rules take an author's facts
//! about the statement's body (`denote_body(db, oq)`, i.e. `eval_query(db, [], oq.body)`) to that form and back,
//! and relate executable result rows (`Vec<EVal>`) to VERUS_SQL rows (`link::query::view_rows`).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::order::*;
use crate::exec::value::*;
use crate::link::query::view_rows;

/// OFFSET 0 without LIMIT keeps every row (`link::query::lemma_slice_all`).
pub use crate::link::query::lemma_slice_all as lemma_slice_whole;

verus! {

/// An error of the body is exactly the statement's allowed outcome.
pub proof fn lemma_outcome_err(db: Database, oq: OrderedQuery, e: SqlError)
    requires denote_body(db, oq) == Err::<Relation, SqlError>(e),
    ensures ordered_ok(db, oq, Err::<Relation, SqlError>(e)),
{
}

/// An allowed error outcome is exactly the body's error (the claim for `SqlError(e)` fixes `e`).
pub proof fn lemma_outcome_err_exact(db: Database, oq: OrderedQuery, e: SqlError)
    requires ordered_ok(db, oq, Err::<Relation, SqlError>(e)),
    ensures denote_body(db, oq) == Err::<Relation, SqlError>(e),
{
}

/// An allowed row outcome means the body has a value.
pub proof fn lemma_outcome_rows_value(db: Database, oq: OrderedQuery, out: Relation)
    requires ordered_ok(db, oq, Ok::<Relation, SqlError>(out)),
    ensures denote_body(db, oq) is Ok,
{
}

/// A permutation of the body's rows, sorted by the ORDER BY keys, then OFFSET/LIMIT: an allowed output.
pub proof fn lemma_outcome_sorted(db: Database, oq: OrderedQuery, rows: Relation, p: Seq<Row>)
    requires
        denote_body(db, oq) == Ok::<Relation, SqlError>(rows),
        p.to_multiset() == rows.to_multiset(),
        sorted_by(oq.keys, p),
    ensures ordered_ok(db, oq, Ok::<Relation, SqlError>(slice_rows(p, oq.offset, oq.limit))),
{
}

/// Without ORDER BY, OFFSET and LIMIT, any permutation of the body's rows is an allowed output.
pub proof fn lemma_outcome_unordered(db: Database, oq: OrderedQuery, rows: Relation, out: Seq<Row>)
    requires
        denote_body(db, oq) == Ok::<Relation, SqlError>(rows),
        oq.keys.len() == 0,
        oq.offset == 0,
        oq.limit is None,
        out.to_multiset() == rows.to_multiset(),
    ensures ordered_ok(db, oq, Ok::<Relation, SqlError>(out)),
{
    assert(sorted_by(oq.keys, out)) by {
        assert forall|i: int, j: int| 0 <= i < j < out.len() implies keys_cmp(oq.keys, #[trigger] out[i], #[trigger] out[j]) <= 0 by {}
    }
    lemma_slice_whole(out);
}

/// Without ORDER BY, OFFSET and LIMIT, the body's rows in their canonical order are an allowed output.
pub proof fn lemma_outcome_rows(db: Database, oq: OrderedQuery, rows: Relation)
    requires
        denote_body(db, oq) == Ok::<Relation, SqlError>(rows),
        oq.keys.len() == 0,
        oq.offset == 0,
        oq.limit is None,
    ensures ordered_ok(db, oq, Ok::<Relation, SqlError>(rows)),
{
    lemma_outcome_unordered(db, oq, rows, rows);
}

/// Executable result rows: length and elementwise view.
pub proof fn lemma_view_rows(rows: Seq<Vec<EVal>>)
    ensures
        view_rows(rows).len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> #[trigger] view_rows(rows)[i] == view_row(rows[i]@),
{
}

/// Appending one executable row appends its view.
pub proof fn lemma_view_rows_push(rows: Seq<Vec<EVal>>, r: Vec<EVal>)
    ensures view_rows(rows.push(r)) == view_rows(rows).push(view_row(r@)),
{
    assert(view_rows(rows.push(r)) =~= view_rows(rows).push(view_row(r@)));
}

} // verus!
