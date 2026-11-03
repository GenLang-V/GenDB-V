//! Sums over a relation by a unique key: when a per-row term is zero on every row whose column `c` is not `k`, and
//! at most one row has `k` there (a primary key), the sum of the term is the term of that row, or zero when no row
//! has `k` (`lemma_sum_by_key`). This is how an index or key lookup replaces a join's inner loop in a proof
//! (`link::join::sum_of` over a product, one level at a time).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::link::join::*;

verus! {

/// Column `c` of row `r` (a named projection, used as a trigger).
pub open spec fn colv(r: Row, c: int) -> Val {
    r[c]
}

/// Some row of `rows` has `k` in column `c`.
pub open spec fn has_key(rows: Seq<Row>, c: int, k: Val) -> bool {
    exists|i: int| 0 <= i < rows.len() && #[trigger] colv(rows[i], c) == k
}

/// The index of a row with `k` in column `c` (meaningful when `has_key`).
pub open spec fn key_pos(rows: Seq<Row>, c: int, k: Val) -> int {
    choose|i: int| 0 <= i < rows.len() && #[trigger] colv(rows[i], c) == k
}

/// The row with `k` in column `c` (meaningful when `has_key`).
pub open spec fn key_row(rows: Seq<Row>, c: int, k: Val) -> Row {
    rows[key_pos(rows, c, k)]
}

/// No two rows share a value of column `c`.
pub open spec fn key_unique(rows: Seq<Row>, c: int) -> bool {
    forall|i: int, j: int| 0 <= i < rows.len() && 0 <= j < rows.len() && #[trigger] colv(rows[i], c) == #[trigger] colv(rows[j], c) ==> i == j
}

/// `key_row` has the key, at an index of the relation.
pub proof fn lemma_key_row(rows: Seq<Row>, c: int, k: Val)
    requires has_key(rows, c, k),
    ensures
        0 <= key_pos(rows, c, k) < rows.len(),
        colv(rows[key_pos(rows, c, k)], c) == k,
        key_row(rows, c, k)[c] == k,
{
}

/// Under a unique key, the row holding `k` is `key_row`.
pub proof fn lemma_key_row_unique(rows: Seq<Row>, c: int, k: Val, i: int)
    requires key_unique(rows, c), 0 <= i < rows.len(), colv(rows[i], c) == k,
    ensures has_key(rows, c, k), key_pos(rows, c, k) == i, key_row(rows, c, k) == rows[i],
{
    assert(has_key(rows, c, k));
    lemma_key_row(rows, c, k);
}

/// The sum of a term that is zero off key `k`, over rows with a unique key in column `c`.
pub proof fn lemma_sum_by_key(rows: Seq<Row>, c: int, k: Val, f: spec_fn(Row) -> int)
    requires
        key_unique(rows, c),
        forall|i: int| 0 <= i < rows.len() && f(#[trigger] rows[i]) != 0 ==> colv(rows[i], c) == k,
    ensures
        sum_of(rows, f) == if has_key(rows, c, k) { f(key_row(rows, c, k)) } else { 0 },
{
    if has_key(rows, c, k) {
        let p = key_pos(rows, c, k);
        lemma_key_row(rows, c, k);
        lemma_sum_of_remove(rows, p, f);
        let rest = rows.remove(p);
        assert forall|i: int| 0 <= i < rest.len() implies f(#[trigger] rest[i]) == 0 by {
            let m = if i < p { i } else { i + 1 };
            assert(rest[i] == rows[m]);
            if f(rows[m]) != 0 {
                assert(colv(rows[m], c) == k);
                assert(m == p);
            }
        }
        lemma_sum_of_zero(rest, f);
    } else {
        assert forall|i: int| 0 <= i < rows.len() implies f(#[trigger] rows[i]) == 0 by {
            if f(rows[i]) != 0 {
                assert(colv(rows[i], c) == k);
            }
        }
        lemma_sum_of_zero(rows, f);
    }
}

} // verus!
