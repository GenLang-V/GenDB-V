//! Facts about the relation operators of the SQL meaning that a join implementation needs: membership and
//! duplicate-freedom of kept rows (`link::join::keep`) and of left-major products (`spec::relation::product_rows`),
//! and the WHERE filter of three-valued truths. (Adapted from the admitted Q2 package's `common::relations`.)
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::*;
use crate::spec::scalar::*;
use crate::spec::relation::*;
use crate::link::join::{keep, lemma_keep_push};
use crate::bridge::relation::{is_concat, lemma_product_rows_elems};

verus! {

// ------------------------------------------------------------------------------------------ kept rows

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

/// The SQL filter keeps the rows whose truth is `True`: with `truths[i] is True` exactly when `f(rows[i])`, it is
/// `keep(rows, f)` (truths may be `False` or `Unknown` otherwise).
pub proof fn lemma_keep_true_is_true(rows: Seq<Row>, truths: Seq<Truth>, f: spec_fn(Row) -> bool)
    requires
        truths.len() == rows.len(),
        forall|i: int| 0 <= i < rows.len() ==> (#[trigger] truths[i] is True) == f(rows[i]),
    ensures keep_true(rows, truths) == keep(rows, f),
    decreases rows.len(),
{
    if rows.len() > 0 {
        let (ri, ti) = (rows.drop_last(), truths.drop_last());
        assert forall|i: int| 0 <= i < ri.len() implies (#[trigger] ti[i] is True) == f(ri[i]) by {
            assert(ti[i] == truths[i] && ri[i] == rows[i]);
        }
        lemma_keep_true_is_true(ri, ti, f);
        assert((truths[rows.len() - 1] is True) == f(rows[rows.len() - 1]));
    }
}

// ------------------------------------------------------------------------------------------ products

/// A row of a product is a concatenation of a left and a right row, and every such concatenation is a row.
pub proof fn lemma_product_contains(a: Seq<Row>, b: Seq<Row>, x: Row)
    ensures product_rows(a, b).contains(x) <==> exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && x == #[trigger] a[i] + #[trigger] b[j],
{
    lemma_product_rows_elems(a, b);
    crate::link::join::lemma_product_index(a, b);
    let p = product_rows(a, b);
    if p.contains(x) {
        let k = choose|k: int| 0 <= k < p.len() && p[k] == x;
        assert(is_concat(p[k], a, b));
    }
    if exists|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && x == #[trigger] a[i] + #[trigger] b[j] {
        let (i, j) = choose|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() && x == #[trigger] a[i] + #[trigger] b[j];
        let nb = b.len() as int;
        assert(0 <= i * nb + j < a.len() * nb) by (nonlinear_arith)
            requires 0 <= i < a.len(), 0 <= j < nb;
        assert(p[i * nb + j] == x);
    }
}

/// Concatenations with a left part of width `w` determine both parts.
pub proof fn lemma_concat_parts(l1: Row, r1: Row, l2: Row, r2: Row, w: nat)
    requires l1.len() == w, l2.len() == w, l1 + r1 == l2 + r2,
    ensures l1 == l2, r1 == r2,
{
    assert(l1 =~= (l1 + r1).subrange(0, w as int));
    assert(l2 =~= (l2 + r2).subrange(0, w as int));
    assert(r1 =~= (l1 + r1).subrange(w as int, (l1 + r1).len() as int));
    assert(r2 =~= (l2 + r2).subrange(w as int, (l2 + r2).len() as int));
}

/// The product of duplicate-free relations (left rows of one width) is duplicate-free.
pub proof fn lemma_product_nodup(a: Seq<Row>, b: Seq<Row>, w: nat)
    requires
        a.no_duplicates(),
        b.no_duplicates(),
        forall|i: int| 0 <= i < a.len() ==> (#[trigger] a[i]).len() == w,
    ensures product_rows(a, b).no_duplicates(),
    decreases a.len(),
{
    if a.len() > 0 {
        let ai = a.drop_last();
        let x = a.last();
        assert(ai.no_duplicates()) by {
            assert forall|i: int, j: int| 0 <= i < ai.len() && 0 <= j < ai.len() && i != j implies ai[i] != ai[j] by {
                assert(ai[i] == a[i] && ai[j] == a[j]);
            }
        }
        assert forall|i: int| 0 <= i < ai.len() implies (#[trigger] ai[i]).len() == w by {
            assert(ai[i] == a[i]);
        }
        lemma_product_nodup(ai, b, w);
        let left = product_rows(ai, b);
        let right = b.map_values(|r: Row| x + r);
        assert(x.len() == w) by { assert(a[a.len() - 1] == x); }
        assert(right.no_duplicates()) by {
            assert forall|i: int, j: int| 0 <= i < right.len() && 0 <= j < right.len() && i != j implies right[i] != right[j] by {
                if right[i] == right[j] {
                    lemma_concat_parts(x, b[i], x, b[j], w);
                }
            }
        }
        lemma_product_rows_elems(ai, b);
        assert forall|i: int, j: int| 0 <= i < left.len() && 0 <= j < right.len() implies left[i] != right[j] by {
            assert(is_concat(left[i], ai, b));
            let (p, q) = choose|p: int, q: int| 0 <= p < ai.len() && 0 <= q < b.len() && left[i] == #[trigger] ai[p] + #[trigger] b[q];
            if left[i] == right[j] {
                lemma_concat_parts(ai[p], b[q], x, b[j], w);
                assert(a[p] == ai[p]);
                assert(a[p] == a[a.len() - 1]);
            }
        }
        vstd::seq_lib::lemma_no_dup_in_concat(left, right);
    }
}

} // verus!
