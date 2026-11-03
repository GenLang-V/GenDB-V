//! Stable top-down merge sort of `(key, payload)` pairs by key (nondecreasing); the output has the input's multiset.
use vstd::prelude::*;
use vstd::multiset::Multiset;

verus! {

pub open spec fn sorted_k(s: Seq<(i128, u64)>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> (#[trigger] s[i]).0 <= (#[trigger] s[j]).0
}

proof fn lemma_push_mset(s: Seq<(i128, u64)>, x: (i128, u64))
    ensures s.push(x).to_multiset() == s.to_multiset().insert(x),
{
    s.to_multiset_ensures();
}

proof fn lemma_sub_push(s: Seq<(i128, u64)>, i: int)
    requires 0 <= i < s.len(),
    ensures s.subrange(0, i + 1).to_multiset() == s.subrange(0, i).to_multiset().insert(s[i]),
{
    assert(s.subrange(0, i + 1) =~= s.subrange(0, i).push(s[i]));
    lemma_push_mset(s.subrange(0, i), s[i]);
}

/// Merge of two sorted sequences.
fn merge(a: Vec<(i128, u64)>, b: Vec<(i128, u64)>) -> (r: Vec<(i128, u64)>)
    requires sorted_k(a@), sorted_k(b@),
    ensures sorted_k(r@), r@.to_multiset() == a@.to_multiset().add(b@.to_multiset()),
{
    let na = a.len();
    let nb = b.len();
    let mut r: Vec<(i128, u64)> = Vec::with_capacity(if na <= usize::MAX - nb { na + nb } else { 0 });
    let mut i: usize = 0;
    let mut j: usize = 0;
    proof {
        broadcast use vstd::multiset::group_multiset_axioms;
        assert(a@.subrange(0, 0) =~= Seq::<(i128, u64)>::empty());
        assert(b@.subrange(0, 0) =~= Seq::<(i128, u64)>::empty());
        assert(r@ =~= Seq::<(i128, u64)>::empty());
        Seq::<(i128, u64)>::empty().to_multiset_ensures();
        assert(Seq::<(i128, u64)>::empty().to_multiset().len() == 0);
        assert(Seq::<(i128, u64)>::empty().to_multiset() =~= Multiset::empty());
        assert(Multiset::<(i128, u64)>::empty().add(Multiset::empty()) =~= Multiset::empty());
    }
    while i < na || j < nb
        invariant
            na == a@.len(), nb == b@.len(), i <= na, j <= nb,
            sorted_k(a@), sorted_k(b@), sorted_k(r@),
            r@.to_multiset() == a@.subrange(0, i as int).to_multiset().add(b@.subrange(0, j as int).to_multiset()),
            r@.len() > 0 && i < na ==> r@.last().0 <= a@[i as int].0,
            r@.len() > 0 && j < nb ==> r@.last().0 <= b@[j as int].0,
        decreases (na - i) + (nb - j),
    {
        let take_a = j >= nb || (i < na && a[i].0 <= b[j].0);
        let ghost old_r = r@;
        if take_a {
            let x = a[i];
            r.push(x);
            proof {
                lemma_sub_push(a@, i as int);
                lemma_push_mset(old_r, x);
                assert(r@ == old_r.push(x));
                assert forall|p: int, q: int| 0 <= p < q < r@.len() implies (#[trigger] r@[p]).0 <= (#[trigger] r@[q]).0 by {
                    if q == r@.len() - 1 && p < old_r.len() {
                        assert(old_r[p].0 <= old_r.last().0 || p == old_r.len() - 1);
                    }
                }
                if i + 1 < na { assert(a@[i as int].0 <= a@[i + 1].0); }
            }
            i = i + 1;
        } else {
            let x = b[j];
            r.push(x);
            proof {
                lemma_sub_push(b@, j as int);
                lemma_push_mset(old_r, x);
                assert(r@ == old_r.push(x));
                assert forall|p: int, q: int| 0 <= p < q < r@.len() implies (#[trigger] r@[p]).0 <= (#[trigger] r@[q]).0 by {
                    if q == r@.len() - 1 && p < old_r.len() {
                        assert(old_r[p].0 <= old_r.last().0 || p == old_r.len() - 1);
                    }
                }
                if j + 1 < nb { assert(b@[j as int].0 <= b@[j + 1].0); }
            }
            j = j + 1;
        }
    }
    proof {
        assert(a@.subrange(0, na as int) =~= a@);
        assert(b@.subrange(0, nb as int) =~= b@);
    }
    r
}

/// Sorted copy of `v[lo, hi)`.
fn sort_range(v: &Vec<(i128, u64)>, lo: usize, hi: usize) -> (r: Vec<(i128, u64)>)
    requires lo <= hi <= v@.len(),
    ensures sorted_k(r@), r@.to_multiset() == v@.subrange(lo as int, hi as int).to_multiset(),
    decreases hi - lo,
{
    if hi - lo == 2 {
        // Two entries: in order, or swapped.
        let mut r: Vec<(i128, u64)> = Vec::with_capacity(2);
        let (x, y) = (v[lo], v[lo + 1]);
        let ghost s = v@.subrange(lo as int, hi as int);
        proof { assert(s =~= seq![x] + seq![y]); }
        if x.0 <= y.0 {
            r.push(x);
            r.push(y);
            proof { assert(r@ =~= s); assert(r@[0] == x && r@[1] == y); }
        } else {
            r.push(y);
            r.push(x);
            proof {
                assert(r@ =~= seq![y] + seq![x]);
                assert(r@[0] == y && r@[1] == x);
                broadcast use vstd::multiset::group_multiset_axioms;
                vstd::seq_lib::lemma_multiset_commutative(seq![y], seq![x]);
                vstd::seq_lib::lemma_multiset_commutative(seq![x], seq![y]);
                assert(seq![y].to_multiset().add(seq![x].to_multiset()) =~= seq![x].to_multiset().add(seq![y].to_multiset()));
                assert(r@.to_multiset() == s.to_multiset());
            }
        }
        r
    } else if hi - lo <= 1 {
        let mut r: Vec<(i128, u64)> = Vec::new();
        if hi > lo {
            r.push(v[lo]);
            proof { assert(r@ =~= v@.subrange(lo as int, hi as int)); }
        } else {
            proof { assert(r@ =~= v@.subrange(lo as int, hi as int)); }
        }
        r
    } else {
        let mid = lo + (hi - lo) / 2;
        let a = sort_range(v, lo, mid);
        let b = sort_range(v, mid, hi);
        let r = merge(a, b);
        proof {
            assert(v@.subrange(lo as int, hi as int) =~= v@.subrange(lo as int, mid as int) + v@.subrange(mid as int, hi as int));
            vstd::seq_lib::lemma_multiset_commutative(v@.subrange(lo as int, mid as int), v@.subrange(mid as int, hi as int));
        }
        r
    }
}

/// `v` sorted by key; the output has `v`'s multiset.
pub fn merge_sort(v: &Vec<(i128, u64)>) -> (r: Vec<(i128, u64)>)
    ensures sorted_k(r@), r@.to_multiset() == v@.to_multiset(),
{
    let r = sort_range(v, 0, v.len());
    proof { assert(v@.subrange(0, v@.len() as int) =~= v@); }
    r
}

} // verus!
