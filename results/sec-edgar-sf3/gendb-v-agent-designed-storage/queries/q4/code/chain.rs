//! Sums over the kept joined rows, decomposed down to the stored layouts. For any weight `w` of a kept row's
//! output fields (`mini`: sic, tlabel, stmt, cik, value), the sum of `w` over the kept rows is a nested sum over the
//! four tables (`lemma_sum_joined`): sub row, pre row, tag row, num row. The later sections collapse each level
//! onto the stored data the executable code reads.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::relation::product_rows;
use crate::link::join::{sum_of, lemma_sum_of_ext, lemma_sum_of_product_swap, lemma_sum_of_swap, lemma_sum_of_keep, keep};
use crate::agent::sem::*;

verus! {

/// A kept row's output fields: sic, tlabel, stmt, cik, value.
pub open spec fn mini(x: Row) -> Row { seq![x[12], x[36], x[41], x[10], x[7]] }

/// The weight `w` of a joined row when it is kept, else 0.
pub open spec fn wq(b0: Seq<u8>, b1: Seq<u8>, lo: int, hi: int, w: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |x: Row| if qual(b0, b1, lo, hi, x) { w(mini(x)) } else { 0 }
}

// The nested sum over the four tables of a function of the joined row, one named level each.
pub open spec fn fnx(f: spec_fn(Row) -> int, s: Row, t: Row, p: Row) -> spec_fn(Row) -> int { |n: Row| f(n + s + t + p) }
pub open spec fn ftx(db: Database, f: spec_fn(Row) -> int, s: Row, p: Row) -> spec_fn(Row) -> int {
    |t: Row| sum_of(db.tables[1], fnx(f, s, t, p))
}
pub open spec fn fpx(db: Database, f: spec_fn(Row) -> int, s: Row) -> spec_fn(Row) -> int {
    |p: Row| sum_of(db.tables[2], ftx(db, f, s, p))
}
pub open spec fn fsx(db: Database, f: spec_fn(Row) -> int) -> spec_fn(Row) -> int {
    |s: Row| sum_of(db.tables[3], fpx(db, f, s))
}

pub open spec fn nested(db: Database, f: spec_fn(Row) -> int) -> int {
    sum_of(db.tables[0], fsx(db, f))
}

/// The left-deep product's sum as the nested sum: sub outermost, then pre, tag and num.
pub proof fn lemma_sum_joined(db: Database, f: spec_fn(Row) -> int)
    ensures sum_of(joined(db), f) == nested(db, f),
{
    let (num, sub, tag, pre) = (db.tables[1], db.tables[0], db.tables[2], db.tables[3]);
    let p2 = product_rows(num, sub);
    let p3 = product_rows(p2, tag);
    // joined = p3 x pre: pre outermost.
    lemma_sum_of_product_swap(p3, pre, f);
    let inner3 = |p: Row| sum_of(p3, |x: Row| f(x + p));
    // p3 = p2 x tag, then p2 = num x sub.
    let l1 = |p: Row| sum_of(tag, |t: Row| sum_of(p2, |z: Row| f(z + t + p)));
    assert forall|i: int| 0 <= i < pre.len() implies #[trigger] inner3(pre[i]) == l1(pre[i]) by {
        let p = pre[i];
        let g = |x: Row| f(x + p);
        lemma_sum_of_product_swap(p2, tag, g);
        assert((|x: Row| f(x + p)) =~= g);
        let a = |y: Row| sum_of(p2, |x: Row| g(x + y));
        let b = |t: Row| sum_of(p2, |z: Row| f(z + t + p));
        assert forall|j: int| 0 <= j < tag.len() implies #[trigger] a(tag[j]) == b(tag[j]) by {
            let t = tag[j];
            assert((|x: Row| g(x + t)) =~= (|z: Row| f(z + t + p)));
        }
        lemma_sum_of_ext(tag, a, b);
    }
    lemma_sum_of_ext(pre, inner3, l1);
    let l2 = |p: Row| sum_of(tag, |t: Row| sum_of(sub, |s: Row| sum_of(num, |n: Row| f(n + s + t + p))));
    assert forall|i: int| 0 <= i < pre.len() implies #[trigger] l1(pre[i]) == l2(pre[i]) by {
        let p = pre[i];
        let a = |t: Row| sum_of(p2, |z: Row| f(z + t + p));
        let b = |t: Row| sum_of(sub, |s: Row| sum_of(num, |n: Row| f(n + s + t + p)));
        assert forall|j: int| 0 <= j < tag.len() implies #[trigger] a(tag[j]) == b(tag[j]) by {
            let t = tag[j];
            let g = |z: Row| f(z + t + p);
            lemma_sum_of_product_swap(num, sub, g);
            let c = |y: Row| sum_of(num, |x: Row| g(x + y));
            let d = |s: Row| sum_of(num, |n: Row| f(n + s + t + p));
            assert forall|k: int| 0 <= k < sub.len() implies #[trigger] c(sub[k]) == d(sub[k]) by {
                let s = sub[k];
                assert((|x: Row| g(x + s)) =~= (|n: Row| f(n + s + t + p)));
            }
            lemma_sum_of_ext(sub, c, d);
        }
        lemma_sum_of_ext(tag, a, b);
    }
    lemma_sum_of_ext(pre, l1, l2);
    // Swap tag and sub under each pre row.
    let l3 = |p: Row| sum_of(sub, |s: Row| sum_of(tag, |t: Row| sum_of(num, |n: Row| f(n + s + t + p))));
    assert forall|i: int| 0 <= i < pre.len() implies #[trigger] l2(pre[i]) == l3(pre[i]) by {
        let p = pre[i];
        let h = |t: Row, s: Row| sum_of(num, |n: Row| f(n + s + t + p));
        lemma_sum_of_swap(tag, sub, h);
        assert(sum_of(tag, |t: Row| sum_of(sub, |s: Row| h(t, s))) == l2(p)) by {
            let a = |t: Row| sum_of(sub, |s: Row| h(t, s));
            let b = |t: Row| sum_of(sub, |s: Row| sum_of(num, |n: Row| f(n + s + t + p)));
            assert forall|j: int| 0 <= j < tag.len() implies #[trigger] a(tag[j]) == b(tag[j]) by {
                let t = tag[j];
                assert((|s: Row| h(t, s)) =~= (|s: Row| sum_of(num, |n: Row| f(n + s + t + p))));
            }
            lemma_sum_of_ext(tag, a, b);
        }
        assert(sum_of(sub, |s: Row| sum_of(tag, |t: Row| h(t, s))) == l3(p)) by {
            let a = |s: Row| sum_of(tag, |t: Row| h(t, s));
            let b = |s: Row| sum_of(tag, |t: Row| sum_of(num, |n: Row| f(n + s + t + p)));
            assert forall|j: int| 0 <= j < sub.len() implies #[trigger] a(sub[j]) == b(sub[j]) by {
                let s = sub[j];
                assert((|t: Row| h(t, s)) =~= (|t: Row| sum_of(num, |n: Row| f(n + s + t + p))));
            }
            lemma_sum_of_ext(sub, a, b);
        }
    }
    lemma_sum_of_ext(pre, l2, l3);
    // Swap pre and sub.
    let h2 = |p: Row, s: Row| sum_of(tag, |t: Row| sum_of(num, |n: Row| f(n + s + t + p)));
    lemma_sum_of_swap(pre, sub, h2);
    let a3 = |p: Row| sum_of(sub, |s: Row| h2(p, s));
    assert forall|j: int| 0 <= j < pre.len() implies #[trigger] l3(pre[j]) == a3(pre[j]) by {
        let p = pre[j];
        assert((|s: Row| h2(p, s)) =~= (|s: Row| sum_of(tag, |t: Row| sum_of(num, |n: Row| f(n + s + t + p)))));
    }
    lemma_sum_of_ext(pre, l3, a3);
    let b3 = |s: Row| sum_of(pre, |p: Row| h2(p, s));
    let c3 = fsx(db, f);
    assert forall|j: int| 0 <= j < sub.len() implies #[trigger] b3(sub[j]) == c3(sub[j]) by {
        let s = sub[j];
        assert forall|p: Row| #[trigger] ftx(db, f, s, p) =~= (|t: Row| sum_of(num, |n: Row| f(n + s + t + p))) by {
            assert forall|t: Row| #[trigger] fnx(f, s, t, p) =~= (|n: Row| f(n + s + t + p)) by {}
        }
        assert((|p: Row| h2(p, s)) =~= fpx(db, f, s));
    }
    lemma_sum_of_ext(sub, b3, c3);
}

/// The sum of a weight over the kept rows is the nested sum of the weight of the kept joined rows.
pub proof fn lemma_sum_kept(db: Database, b0: Seq<u8>, b1: Seq<u8>, lo: int, hi: int, w: spec_fn(Row) -> int)
    ensures
        sum_of(keep(joined(db), |x: Row| qual(b0, b1, lo, hi, x)), |x: Row| w(mini(x)))
            == nested(db, wq(b0, b1, lo, hi, w)),
{
    let c = |x: Row| qual(b0, b1, lo, hi, x);
    let f = wq(b0, b1, lo, hi, w);
    lemma_sum_of_keep(joined(db), c, f);
    lemma_sum_joined(db, f);
    let k = keep(joined(db), c);
    crate::link::join::lemma_keep_members(joined(db), c);
    assert forall|i: int| 0 <= i < k.len() implies #[trigger] f(k[i]) == w(mini(k[i])) by {}
    lemma_sum_of_ext(k, f, |x: Row| w(mini(x)));
}

} // verus!
