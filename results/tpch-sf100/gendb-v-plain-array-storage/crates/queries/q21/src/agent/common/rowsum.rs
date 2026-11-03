//! Sums over the rows of a relation as sums over row indices: `link::join::sum_of(rows, f)` is the index sum
//! `isum(h, rows.len())` of any `h` with `h(i) == f(rows[i])` (`lemma_sum_rows`), with the index-sum laws used to
//! evaluate nested sums over products (extensionality, scaling by a constant).
use vstd::prelude::*;
use crate::spec::value::Row;
use crate::link::join::sum_of;

verus! {

/// `h(0) + .. + h(m - 1)`.
pub open spec fn isum(h: spec_fn(int) -> int, m: int) -> int
    decreases m,
{
    if m <= 0 { 0 } else { isum(h, m - 1) + h(m - 1) }
}

/// The sum of `f` over the rows is the index sum of any `h` that agrees with `f` on each row.
pub proof fn lemma_sum_rows(rows: Seq<Row>, f: spec_fn(Row) -> int, h: spec_fn(int) -> int)
    requires forall|i: int| 0 <= i < rows.len() ==> #[trigger] h(i) == f(rows[i]),
    ensures sum_of(rows, f) == isum(h, rows.len() as int),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        assert forall|i: int| 0 <= i < ri.len() implies #[trigger] h(i) == f(ri[i]) by {
            assert(ri[i] == rows[i]);
        }
        lemma_sum_rows(ri, f, h);
        assert(rows.last() == rows[rows.len() - 1]);
    }
}

/// Index sums of functions that agree on `0..m` are equal.
pub proof fn lemma_isum_ext(h1: spec_fn(int) -> int, h2: spec_fn(int) -> int, m: int)
    requires forall|i: int| 0 <= i < m ==> #[trigger] h1(i) == h2(i),
    ensures isum(h1, m) == isum(h2, m),
    decreases m,
{
    if m > 0 {
        lemma_isum_ext(h1, h2, m - 1);
    }
}

} // verus!
