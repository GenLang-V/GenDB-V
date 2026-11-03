//! Sums over a left-deep product of four relations `((a x b) x c) x d` (`spec::relation::product_rows`) as nested
//! sums `sum_a sum_b sum_c sum_d f(x ++ y ++ z ++ w)` (`lemma_sum_prod4`), with the inner sums named (`s_d`, `s_cd`,
//! `s_bcd`) so that they can serve as quantifier triggers.
use vstd::prelude::*;
use crate::spec::value::Row;
use crate::spec::relation::product_rows;
use crate::link::join::{sum_of, lemma_sum_of_product, lemma_sum_of_ext};

verus! {

/// `sum_w f(a ++ w)` over `d`.
pub open spec fn s_d(d: Seq<Row>, f: spec_fn(Row) -> int, a: Row) -> int {
    sum_of(d, |w: Row| f(a + w))
}

/// `sum_z sum_w f(a ++ z ++ w)` over `c`, `d`.
pub open spec fn s_cd(c: Seq<Row>, d: Seq<Row>, f: spec_fn(Row) -> int, a: Row) -> int {
    sum_of(c, |z: Row| s_d(d, f, a + z))
}

/// `sum_y sum_z sum_w f(a ++ y ++ z ++ w)` over `b`, `c`, `d`.
pub open spec fn s_bcd(b: Seq<Row>, c: Seq<Row>, d: Seq<Row>, f: spec_fn(Row) -> int, a: Row) -> int {
    sum_of(b, |y: Row| s_cd(c, d, f, a + y))
}

/// A sum over the product of four relations is the nested sum.
pub proof fn lemma_sum_prod4(a: Seq<Row>, b: Seq<Row>, c: Seq<Row>, d: Seq<Row>, f: spec_fn(Row) -> int)
    ensures
        sum_of(product_rows(product_rows(product_rows(a, b), c), d), f) == sum_of(a, |x: Row| s_bcd(b, c, d, f, x)),
{
    let ab = product_rows(a, b);
    let abc = product_rows(ab, c);
    // d level
    lemma_sum_of_product(abc, d, f);
    let h1 = |x: Row| sum_of(d, |w: Row| f(x + w));
    let h2 = |x: Row| s_d(d, f, x);
    assert forall|i: int| 0 <= i < abc.len() implies h1(#[trigger] abc[i]) == h2(abc[i]) by {}
    lemma_sum_of_ext(abc, h1, h2);
    // c level
    lemma_sum_of_product(ab, c, h2);
    let h3 = |x: Row| sum_of(c, |z: Row| h2(x + z));
    let h4 = |x: Row| s_cd(c, d, f, x);
    assert forall|i: int| 0 <= i < ab.len() implies h3(#[trigger] ab[i]) == h4(ab[i]) by {
        let x = ab[i];
        lemma_sum_of_ext(c, |z: Row| h2(x + z), |z: Row| s_d(d, f, x + z));
    }
    lemma_sum_of_ext(ab, h3, h4);
    // b level
    lemma_sum_of_product(a, b, h4);
    let h5 = |x: Row| sum_of(b, |y: Row| h4(x + y));
    let h6 = |x: Row| s_bcd(b, c, d, f, x);
    assert forall|i: int| 0 <= i < a.len() implies h5(#[trigger] a[i]) == h6(a[i]) by {
        let x = a[i];
        lemma_sum_of_ext(b, |y: Row| h4(x + y), |y: Row| s_cd(c, d, f, x + y));
    }
    lemma_sum_of_ext(a, h5, h6);
}

} // verus!
