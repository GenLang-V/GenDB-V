//! ORDER BY .. LIMIT n as a top-n selection: a sorted sequence of `min(n, |all|)` distinct rows of `all`, none of
//! the other rows sorting strictly before its last row, is the first `n` rows of some sorted permutation of `all`
//! (`lemma_topk_slice`). The permutation is the selection followed by the stable sort of the remaining rows
//! (`rest_of`); ties at the boundary may go either way, as `ORDER BY` allows.
use vstd::prelude::*;
use crate::spec::value::Row;
use crate::spec::ast::OrderKey;
use crate::spec::order::{keys_cmp, sorted_by, slice_rows, sort_rows};
use crate::bridge::order::{keys_ok, all_keys_ok, lemma_keys_cmp_trans, lemma_sort_rows};
use crate::link::query::lemma_nodup_same_multiset;

verus! {

/// The rows of `all` that are not in `sel`, in `all`'s order.
pub open spec fn rest_of(all: Seq<Row>, sel: Seq<Row>) -> Seq<Row>
    decreases all.len(),
{
    if all.len() == 0 {
        Seq::empty()
    } else {
        let r = rest_of(all.drop_last(), sel);
        if sel.contains(all.last()) { r } else { r.push(all.last()) }
    }
}

/// Membership in `rest_of`, and no duplicates when `all` has none.
pub proof fn lemma_rest_of(all: Seq<Row>, sel: Seq<Row>)
    ensures
        forall|x: Row| #[trigger] rest_of(all, sel).contains(x) <==> all.contains(x) && !sel.contains(x),
        all.no_duplicates() ==> rest_of(all, sel).no_duplicates(),
    decreases all.len(),
{
    if all.len() > 0 {
        let d = all.drop_last();
        let x = all.last();
        lemma_rest_of(d, sel);
        let r = rest_of(d, sel);
        assert forall|y: Row| #[trigger] rest_of(all, sel).contains(y) <==> all.contains(y) && !sel.contains(y) by {
            if all.contains(y) {
                let t = choose|t: int| 0 <= t < all.len() && all[t] == y;
                if t < d.len() {
                    assert(d[t] == y);
                    assert(d.contains(y));
                }
            }
            if d.contains(y) {
                let t = choose|t: int| 0 <= t < d.len() && d[t] == y;
                assert(all[t] == y);
            }
            assert(all[all.len() - 1] == x);
            if !sel.contains(x) {
                assert(rest_of(all, sel) == r.push(x));
                if r.push(x).contains(y) && y != x {
                    let t = choose|t: int| 0 <= t < r.push(x).len() && r.push(x)[t] == y;
                    assert(r[t] == y);
                }
                if r.contains(y) {
                    let t = choose|t: int| 0 <= t < r.len() && r[t] == y;
                    assert(r.push(x)[t] == y);
                }
                assert(r.push(x)[r.len() as int] == x);
            }
        }
        if all.no_duplicates() {
            assert(d.no_duplicates()) by {
                assert forall|a: int, b: int| 0 <= a < d.len() && 0 <= b < d.len() && a != b implies d[a] != d[b] by {
                    assert(d[a] == all[a] && d[b] == all[b]);
                }
            }
            if !sel.contains(x) {
                assert(!d.contains(x)) by {
                    if d.contains(x) {
                        let t = choose|t: int| 0 <= t < d.len() && d[t] == x;
                        assert(all[t] == all[all.len() - 1]);
                    }
                }
                assert(!r.contains(x));
                let rp = r.push(x);
                assert forall|a: int, b: int| 0 <= a < rp.len() && 0 <= b < rp.len() && a != b implies rp[a] != rp[b] by {
                    if a < r.len() && b < r.len() {
                        assert(rp[a] == r[a] && rp[b] == r[b]);
                    } else if a < r.len() {
                        assert(rp[a] == r[a]);
                        assert(r.contains(r[a]));
                    } else if b < r.len() {
                        assert(rp[b] == r[b]);
                        assert(r.contains(r[b]));
                    }
                }
            }
        }
    }
}

/// A sequence without duplicates whose elements all occur in another: no longer than it (by the multisets).
pub proof fn lemma_nodup_len(s: Seq<Row>, t: Seq<Row>)
    requires s.no_duplicates(), t.no_duplicates(), forall|x: Row| s.contains(x) <==> t.contains(x),
    ensures s.len() == t.len(),
{
    lemma_nodup_same_multiset(s, t);
    s.to_multiset_ensures();
    t.to_multiset_ensures();
}

/// Top-n selection: `sel` (sorted, distinct, `min(n, |all|)` rows of `all`, and no other row of `all` sorts strictly
/// before its last row) is `slice_rows(p, 0, Some(n))` of a sorted permutation `p` of `all`.
pub proof fn lemma_topk_slice(keys: Seq<OrderKey>, fams: Seq<int>, all: Seq<Row>, sel: Seq<Row>, n: nat)
    requires
        all.no_duplicates(),
        sel.no_duplicates(),
        all_keys_ok(keys, fams, all),
        forall|i: int| 0 <= i < sel.len() ==> all.contains(#[trigger] sel[i]),
        sel.len() == if n <= all.len() { n as int } else { all.len() as int },
        sorted_by(keys, sel),
        sel.len() > 0 ==> forall|x: Row| #[trigger] all.contains(x) && !sel.contains(x) ==> keys_cmp(keys, sel.last(), x) <= 0,
    ensures
        exists|p: Seq<Row>| #![trigger sorted_by(keys, p)]
            p.to_multiset() == all.to_multiset() && sorted_by(keys, p) && sel == slice_rows(p, 0, Some(n)),
{
    let rest = rest_of(all, sel);
    lemma_rest_of(all, sel);
    assert(all_keys_ok(keys, fams, rest)) by {
        assert forall|i: int| 0 <= i < rest.len() implies keys_ok(keys, fams, #[trigger] rest[i]) by {
            assert(rest.contains(rest[i]));
            let t = choose|t: int| 0 <= t < all.len() && all[t] == rest[i];
        }
    }
    let srt = sort_rows(keys, rest);
    lemma_sort_rows(keys, fams, rest);
    srt.to_multiset_ensures();
    rest.to_multiset_ensures();
    // srt has rest's elements and no duplicates
    assert forall|x: Row| #[trigger] srt.contains(x) <==> rest.contains(x) by {
        assert(srt.to_multiset().count(x) == rest.to_multiset().count(x));
    }
    rest.lemma_multiset_has_no_duplicates();
    srt.lemma_multiset_has_no_duplicates_conv();
    let p = sel + srt;
    // p has no duplicates: sel and srt are disjoint
    assert forall|i: int, j: int| 0 <= i < sel.len() && 0 <= j < srt.len() implies sel[i] != srt[j] by {
        assert(srt.contains(srt[j]));
        assert(sel.contains(sel[i]));
    }
    vstd::seq_lib::lemma_no_dup_in_concat(sel, srt);
    assert forall|x: Row| #[trigger] p.contains(x) <==> all.contains(x) by {
        if p.contains(x) {
            let t = choose|t: int| 0 <= t < p.len() && p[t] == x;
            if t < sel.len() {
                assert(sel[t] == x);
            } else {
                assert(srt[t - sel.len()] == x);
                assert(srt.contains(x));
            }
        }
        if all.contains(x) {
            if sel.contains(x) {
                let t = choose|t: int| 0 <= t < sel.len() && sel[t] == x;
                assert(p[t] == x);
            } else {
                assert(srt.contains(x));
                let t = choose|t: int| 0 <= t < srt.len() && srt[t] == x;
                assert(p[sel.len() + t] == x);
            }
        }
    }
    lemma_nodup_same_multiset(p, all);
    lemma_nodup_len(p, all);
    // p is sorted: every selected row sorts no later than every remaining row
    assert forall|i: int, j: int| 0 <= i < j < p.len() implies keys_cmp(keys, #[trigger] p[i], #[trigger] p[j]) <= 0 by {
        if j < sel.len() {
            assert(p[i] == sel[i] && p[j] == sel[j]);
        } else if i >= sel.len() {
            assert(p[i] == srt[i - sel.len()] && p[j] == srt[j - sel.len()]);
        } else {
            let x = srt[j - sel.len()];
            assert(p[j] == x && p[i] == sel[i]);
            assert(srt.contains(x));
            assert(rest.contains(x));
            let last = sel.last();
            assert(keys_cmp(keys, last, x) <= 0);
            let ti = choose|t: int| 0 <= t < all.len() && all[t] == sel[i];
            assert(all.contains(sel[sel.len() - 1]));
            let tl = choose|t: int| 0 <= t < all.len() && all[t] == last;
            let tx = choose|t: int| 0 <= t < all.len() && all[t] == x;
            if i < sel.len() - 1 {
                assert(keys_cmp(keys, sel[i], sel[sel.len() - 1]) <= 0);
                lemma_keys_cmp_trans(keys, fams, sel[i], last, x);
            }
        }
    }
    assert(sorted_by(keys, p));
    assert(slice_rows(p, 0, Some(n)) =~= sel);
    assert(p.to_multiset() == all.to_multiset() && sorted_by(keys, p) && sel == slice_rows(p, 0, Some(n)));
}

} // verus!
