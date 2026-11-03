//! Sums over a product of relations where each row of one side meets at most one row of the other: an equi-join
//! on a duplicate-free key column (a primary key) turns the inner sum into one term.
//!
//! `pick(b, col, v)` is the row of `b` whose column `col` holds `v` (or -1 when there is none); `at_pick` applies a
//! function to that row (0 when there is none). When `b`'s column `col` is duplicate-free (`col_unique`) and a
//! per-row contribution vanishes unless the join condition holds, the sum over `product_rows(a, b)` is the sum over
//! `a` of the contribution at the picked row of `b` (`lemma_sum_product_right`), or symmetrically over `b` with the
//! picked row of `a` (`lemma_sum_product_left`). Sums are `link::join::sum_of` (bag semantics, left-major order).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::relation::product_rows;
use crate::link::join::{sum_of, lemma_sum_of_zero, lemma_sum_of_remove, lemma_sum_of_product, lemma_sum_of_product_swap,
    lemma_sum_of_ext, lemma_product_index};

verus! {

/// Column `col` of `b` holds pairwise distinct values.
pub open spec fn col_unique(b: Seq<Row>, col: int) -> bool {
    forall|p: int, q: int| 0 <= p < b.len() && 0 <= q < b.len() && #[trigger] b[p][col] == #[trigger] b[q][col] ==> p == q
}

/// Some row of `b` holds `v` at column `col`.
pub open spec fn has_pick(b: Seq<Row>, col: int, v: Val) -> bool {
    exists|q: int| 0 <= q < b.len() && #[trigger] b[q][col] == v
}

/// The row of `b` holding `v` at column `col`, or -1 when there is none.
pub open spec fn pick(b: Seq<Row>, col: int, v: Val) -> int {
    if has_pick(b, col, v) { choose|q: int| 0 <= q < b.len() && #[trigger] b[q][col] == v } else { -1 }
}

/// `h` of the row of `b` holding `v` at column `col`, or 0 when there is none.
pub open spec fn at_pick(b: Seq<Row>, col: int, v: Val, h: spec_fn(Row) -> int) -> int {
    if has_pick(b, col, v) { h(b[pick(b, col, v)]) } else { 0 }
}

/// The picked row holds `v`; on a duplicate-free column it is the only such row.
pub proof fn lemma_pick(b: Seq<Row>, col: int, v: Val)
    ensures
        has_pick(b, col, v) ==> 0 <= pick(b, col, v) < b.len() && b[pick(b, col, v)][col] == v,
        !has_pick(b, col, v) ==> pick(b, col, v) == -1,
        col_unique(b, col) ==> forall|q: int| 0 <= q < b.len() && #[trigger] b[q][col] == v ==> q == pick(b, col, v),
{
    if col_unique(b, col) {
        assert forall|q: int| 0 <= q < b.len() && #[trigger] b[q][col] == v implies q == pick(b, col, v) by {
            assert(has_pick(b, col, v));
            let p = pick(b, col, v);
            assert(b[p][col] == b[q][col]);
        }
    }
}

/// A non-zero `at_pick` comes from an existing row with a non-zero value.
pub proof fn lemma_at_pick_nonzero(b: Seq<Row>, col: int, v: Val, h: spec_fn(Row) -> int)
    requires at_pick(b, col, v, h) != 0,
    ensures
        has_pick(b, col, v),
        0 <= pick(b, col, v) < b.len(),
        b[pick(b, col, v)][col] == v,
        h(b[pick(b, col, v)]) != 0,
        at_pick(b, col, v, h) == h(b[pick(b, col, v)]),
{
    lemma_pick(b, col, v);
}

/// A sum with one possibly non-zero term.
pub proof fn lemma_sum_single(s: Seq<Row>, f: spec_fn(Row) -> int, i0: int)
    requires 0 <= i0 < s.len(), forall|t: int| 0 <= t < s.len() && t != i0 ==> f(#[trigger] s[t]) == 0,
    ensures sum_of(s, f) == f(s[i0]),
{
    lemma_sum_of_remove(s, i0, f);
    let r = s.remove(i0);
    assert forall|t: int| 0 <= t < r.len() implies f(#[trigger] r[t]) == 0 by {
        if t < i0 {
            assert(r[t] == s[t]);
        } else {
            assert(r[t] == s[t + 1]);
        }
    }
    lemma_sum_of_zero(r, f);
}

/// A sum over `b` whose terms vanish off the rows holding `v` at a duplicate-free column is the term of the picked row.
pub proof fn lemma_sum_one_match(b: Seq<Row>, col: int, v: Val, h: spec_fn(Row) -> int)
    requires
        col_unique(b, col),
        forall|q: int| 0 <= q < b.len() && h(#[trigger] b[q]) != 0 ==> b[q][col] == v,
    ensures sum_of(b, h) == at_pick(b, col, v, h),
{
    lemma_pick(b, col, v);
    if has_pick(b, col, v) {
        let q0 = pick(b, col, v);
        assert forall|t: int| 0 <= t < b.len() && t != q0 implies h(#[trigger] b[t]) == 0 by {
            if h(b[t]) != 0 {
                assert(b[t][col] == v);
            }
        }
        lemma_sum_single(b, h, q0);
    } else {
        assert forall|t: int| 0 <= t < b.len() implies h(#[trigger] b[t]) == 0 by {
            if h(b[t]) != 0 {
                assert(b[t][col] == v);
                assert(has_pick(b, col, v));
            }
        }
        lemma_sum_of_zero(b, h);
    }
}

/// The inner sum of a product, joined on a duplicate-free column `col` of the right side: the sum over the left
/// rows of the contribution at the right row holding the left row's value at `xcol`.
pub proof fn lemma_sum_product_right(a: Seq<Row>, b: Seq<Row>, f: spec_fn(Row) -> int, xcol: int, col: int)
    requires
        col_unique(b, col),
        forall|p: int, q: int| 0 <= p < a.len() && 0 <= q < b.len() && f(#[trigger] a[p] + #[trigger] b[q]) != 0
            ==> b[q][col] == a[p][xcol],
    ensures sum_of(product_rows(a, b), f) == sum_of(a, |x: Row| at_pick(b, col, x[xcol], |y: Row| f(x + y))),
{
    lemma_sum_of_product(a, b, f);
    let inner = |x: Row| sum_of(b, |y: Row| f(x + y));
    let outer = |x: Row| at_pick(b, col, x[xcol], |y: Row| f(x + y));
    assert forall|p: int| 0 <= p < a.len() implies inner(#[trigger] a[p]) == outer(a[p]) by {
        let x = a[p];
        let h = |y: Row| f(x + y);
        assert forall|q: int| 0 <= q < b.len() && h(#[trigger] b[q]) != 0 implies b[q][col] == x[xcol] by {
            assert(f(a[p] + b[q]) != 0);
        }
        lemma_sum_one_match(b, col, x[xcol], h);
    }
    lemma_sum_of_ext(a, inner, outer);
}

/// The outer sum of a product, joined on a duplicate-free column `col` of the left side: the sum over the right
/// rows of the contribution at the left row holding the right row's value at `ycol`.
pub proof fn lemma_sum_product_left(a: Seq<Row>, b: Seq<Row>, f: spec_fn(Row) -> int, ycol: int, col: int)
    requires
        col_unique(a, col),
        forall|p: int, q: int| 0 <= p < a.len() && 0 <= q < b.len() && f(#[trigger] a[p] + #[trigger] b[q]) != 0
            ==> a[p][col] == b[q][ycol],
    ensures sum_of(product_rows(a, b), f) == sum_of(b, |y: Row| at_pick(a, col, y[ycol], |x: Row| f(x + y))),
{
    lemma_sum_of_product_swap(a, b, f);
    let inner = |y: Row| sum_of(a, |x: Row| f(x + y));
    let outer = |y: Row| at_pick(a, col, y[ycol], |x: Row| f(x + y));
    assert forall|q: int| 0 <= q < b.len() implies inner(#[trigger] b[q]) == outer(b[q]) by {
        let y = b[q];
        let h = |x: Row| f(x + y);
        assert forall|p: int| 0 <= p < a.len() && h(#[trigger] a[p]) != 0 implies a[p][col] == y[ycol] by {
            assert(f(a[p] + b[q]) != 0);
        }
        lemma_sum_one_match(a, col, y[ycol], h);
    }
    lemma_sum_of_ext(b, inner, outer);
}

/// Every row of a product of relations of uniform widths has the sum of the widths.
pub proof fn lemma_product_widths(a: Seq<Row>, b: Seq<Row>, wa: nat, wb: nat)
    requires
        forall|p: int| 0 <= p < a.len() ==> (#[trigger] a[p]).len() == wa,
        forall|q: int| 0 <= q < b.len() ==> (#[trigger] b[q]).len() == wb,
    ensures forall|k: int| 0 <= k < product_rows(a, b).len() ==> (#[trigger] product_rows(a, b)[k]).len() == wa + wb,
{
    lemma_product_index(a, b);
    let nb = b.len() as int;
    assert forall|k: int| 0 <= k < product_rows(a, b).len() implies (#[trigger] product_rows(a, b)[k]).len() == wa + wb by {
        assert(nb > 0) by (nonlinear_arith) requires 0 <= k < a.len() * nb, a.len() >= 0;
        let i = k / nb;
        let j = k % nb;
        assert(k == i * nb + j && 0 <= j < nb) by (nonlinear_arith) requires nb > 0, i == k / nb, j == k % nb;
        assert(0 <= i < a.len()) by (nonlinear_arith) requires nb > 0, i == k / nb, 0 <= k < a.len() * nb;
        assert(product_rows(a, b)[i * nb + j] == a[i] + b[j]);
    }
}

} // verus!
