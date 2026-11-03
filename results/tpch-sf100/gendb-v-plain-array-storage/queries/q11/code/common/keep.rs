//! Membership and duplicate-freedom of the rows kept by a two-valued condition (`link::join::keep`), from an
//! admitted query's `common::relations`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::link::join::{keep, lemma_keep_push};

verus! {

/// A row is kept exactly when it is an input row satisfying the condition.
pub proof fn lemma_keep_contains(rows: Seq<Row>, f: spec_fn(Row) -> bool, x: Row)
    ensures keep(rows, f).contains(x) <==> (rows.contains(x) && f(x)),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        lemma_keep_contains(ri, f, x);
        let k = keep(rows, f);
        let ki = keep(ri, f);
        assert(rows == ri.push(rows.last()));
        if k.contains(x) {
            let i = choose|i: int| 0 <= i < k.len() && k[i] == x;
            if f(rows.last()) && i == ki.len() {
                assert(rows[rows.len() - 1] == x);
            } else {
                assert(ki[i] == x);
                let j = choose|j: int| 0 <= j < ri.len() && ri[j] == x;
                assert(rows[j] == x);
            }
        }
        if rows.contains(x) && f(x) {
            let j = choose|j: int| 0 <= j < rows.len() && rows[j] == x;
            if j == rows.len() - 1 {
                assert(k[ki.len() as int] == x);
            } else {
                assert(ri[j] == x);
                let i = choose|i: int| 0 <= i < ki.len() && ki[i] == x;
                assert(k[i] == x);
            }
        }
    }
}

/// Keeping rows of a duplicate-free sequence gives a duplicate-free sequence.
pub proof fn lemma_keep_nodup(rows: Seq<Row>, f: spec_fn(Row) -> bool)
    requires rows.no_duplicates(),
    ensures keep(rows, f).no_duplicates(),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let ri = rows.drop_last();
        assert(ri.no_duplicates()) by {
            assert forall|i: int, j: int| 0 <= i < ri.len() && 0 <= j < ri.len() && i != j implies ri[i] != ri[j] by {
                assert(ri[i] == rows[i] && ri[j] == rows[j]);
            }
        }
        lemma_keep_nodup(ri, f);
        let ki = keep(ri, f);
        if f(rows.last()) {
            let k = ki.push(rows.last());
            assert forall|i: int, j: int| 0 <= i < k.len() && 0 <= j < k.len() && i != j implies k[i] != k[j] by {
                if i < ki.len() && j < ki.len() {
                    assert(k[i] == ki[i] && k[j] == ki[j]);
                } else {
                    let m = if i < ki.len() { i } else { j };
                    assert(k[m] == ki[m]);
                    lemma_keep_contains(ri, f, ki[m]);
                    assert(ki.contains(ki[m]));
                    let q = choose|q: int| 0 <= q < ri.len() && ri[q] == ki[m];
                    assert(rows[q] == ri[q]);
                    assert(rows[q] != rows[rows.len() - 1]);
                }
            }
        }
    }
}

} // verus!
