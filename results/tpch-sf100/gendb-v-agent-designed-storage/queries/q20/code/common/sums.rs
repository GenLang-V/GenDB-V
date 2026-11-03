//! Sums and filters over relations (`link::join::sum_of`, `link::join::keep`): a constant term, the length of a
//! filtered relation, and a term that vanishes outside an index range.
use vstd::prelude::*;
use crate::spec::value::Row;
use crate::link::join::{keep, sum_of};

verus! {

/// A constant term sums to the number of rows times the constant.
pub proof fn lemma_sum_of_const(rows: Seq<Row>, f: spec_fn(Row) -> int, c: int)
    requires forall|i: int| 0 <= i < rows.len() ==> #[trigger] f(rows[i]) == c,
    ensures sum_of(rows, f) == rows.len() * c,
    decreases rows.len(),
{
    if rows.len() > 0 {
        let d = rows.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies #[trigger] f(d[i]) == c by {
            assert(d[i] == rows[i]);
        }
        lemma_sum_of_const(d, f, c);
        assert(f(rows[rows.len() - 1]) == c);
        assert((d.len() + 1) * c == d.len() * c + c) by (nonlinear_arith);
    }
}

/// Filtering never adds rows.
pub proof fn lemma_keep_len(rows: Seq<Row>, f: spec_fn(Row) -> bool)
    ensures keep(rows, f).len() <= rows.len(),
    decreases rows.len(),
{
    if rows.len() > 0 {
        lemma_keep_len(rows.drop_last(), f);
    }
}

} // verus!
