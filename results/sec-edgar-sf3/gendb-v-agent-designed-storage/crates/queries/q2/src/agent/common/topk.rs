//! Top-k under ORDER BY ... LIMIT k as a split of a bag of rows: the `top` rows (sorted, at most `k`) and the `rest`,
//! with every top row not after any rest row. Lemmas: start, insert with room, evict the last top row, reject a row,
//! merge two partial top-k splits (partitioned scans), and the final allowed output (`top` is the LIMIT slice of a
//! sorted permutation of the bag). Generic: any ORDER BY keys whose key values share one family per key.
use vstd::prelude::*;
use vstd::multiset::Multiset;
use crate::spec::value::*;
use crate::spec::ast::OrderKey;
use crate::spec::order::*;
use crate::bridge::order::*;

verus! {

broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms, vstd::seq_lib::lemma_multiset_commutative};

/// `top` and `rest` split the bag `all`; `top` is sorted, at most `k` rows, full whenever `rest` is not empty, and
/// no top row sorts after a rest row.
pub open spec fn topk_ok(keys: Seq<OrderKey>, fams: Seq<int>, k: nat, all: Seq<Row>, top: Seq<Row>, rest: Seq<Row>) -> bool {
    &&& all.to_multiset() == top.to_multiset().add(rest.to_multiset())
    &&& sorted_by(keys, top)
    &&& all_keys_ok(keys, fams, top)
    &&& all_keys_ok(keys, fams, rest)
    &&& top.len() <= k
    &&& (top.len() < k ==> rest.len() == 0)
    &&& forall|i: int, j: int| 0 <= i < top.len() && 0 <= j < rest.len() ==> keys_cmp(keys, #[trigger] top[i], #[trigger] rest[j]) <= 0
}

/// The empty bag.
pub proof fn lemma_topk_empty(keys: Seq<OrderKey>, fams: Seq<int>, k: nat)
    ensures topk_ok(keys, fams, k, Seq::empty(), Seq::empty(), Seq::empty()),
{
    let e = Seq::<Row>::empty();
    assert(e.to_multiset().add(e.to_multiset()) =~= e.to_multiset());
}

/// Every row of a sorted sequence is not after its last row.
pub proof fn lemma_sorted_le_last(keys: Seq<OrderKey>, fams: Seq<int>, s: Seq<Row>, i: int)
    requires sorted_by(keys, s), all_keys_ok(keys, fams, s), 0 <= i < s.len(),
    ensures keys_cmp(keys, s[i], s.last()) <= 0,
{
    if i < s.len() - 1 {
        assert(keys_cmp(keys, s[i], s[s.len() - 1]) <= 0);
    } else {
        assert(s[i] == s.last());
        assert(keys_ok(keys, fams, s[i]));
        lemma_keys_cmp_antisym(keys, fams, s[i], s[i]);
    }
}

/// A row with room in `top`: it is inserted in order.
pub proof fn lemma_topk_insert_room(keys: Seq<OrderKey>, fams: Seq<int>, k: nat, all: Seq<Row>, top: Seq<Row>,
    rest: Seq<Row>, x: Row)
    requires topk_ok(keys, fams, k, all, top, rest), top.len() < k, keys_ok(keys, fams, x),
    ensures topk_ok(keys, fams, k, all.push(x), insert_sorted(keys, top, x), rest),
{
    lemma_insert_sorted(keys, fams, top, x);
    let t2 = insert_sorted(keys, top, x);
    assert(t2.len() == top.len() + 1) by {
        assert(t2.to_multiset().len() == top.to_multiset().insert(x).len());
    }
    assert(all.push(x).to_multiset() =~= t2.to_multiset().add(rest.to_multiset()));
}

/// A row not before the last top row of a full `top`: it joins the rest.
pub proof fn lemma_topk_reject(keys: Seq<OrderKey>, fams: Seq<int>, k: nat, all: Seq<Row>, top: Seq<Row>,
    rest: Seq<Row>, x: Row)
    requires
        topk_ok(keys, fams, k, all, top, rest),
        top.len() == k, k > 0,
        keys_ok(keys, fams, x),
        keys_cmp(keys, top.last(), x) <= 0,
    ensures topk_ok(keys, fams, k, all.push(x), top, rest.push(x)),
{
    let r2 = rest.push(x);
    assert(all.push(x).to_multiset() =~= top.to_multiset().add(r2.to_multiset()));
    assert forall|i: int, j: int| 0 <= i < top.len() && 0 <= j < r2.len() implies keys_cmp(keys, #[trigger] top[i], #[trigger] r2[j]) <= 0 by {
        if j < rest.len() {
            assert(r2[j] == rest[j]);
        } else {
            assert(r2[j] == x);
            lemma_sorted_le_last(keys, fams, top, i);
            lemma_keys_cmp_trans(keys, fams, top[i], top.last(), x);
        }
    }
    assert forall|j: int| 0 <= j < r2.len() implies keys_ok(keys, fams, #[trigger] r2[j]) by {
        if j < rest.len() { assert(r2[j] == rest[j]); }
    }
}

/// A row before the last top row of a full `top`: the last top row moves to the rest, the row is inserted.
pub proof fn lemma_topk_evict(keys: Seq<OrderKey>, fams: Seq<int>, k: nat, all: Seq<Row>, top: Seq<Row>,
    rest: Seq<Row>, x: Row)
    requires
        topk_ok(keys, fams, k, all, top, rest),
        top.len() == k, k > 0,
        keys_ok(keys, fams, x),
        keys_cmp(keys, top.last(), x) > 0,
    ensures topk_ok(keys, fams, k, all.push(x), insert_sorted(keys, top.drop_last(), x), rest.push(top.last())),
{
    let last = top.last();
    let d = top.drop_last();
    assert(top == d.push(last));
    lemma_sorted_prefix(keys, fams, top);
    lemma_insert_sorted(keys, fams, d, x);
    let t2 = insert_sorted(keys, d, x);
    let r2 = rest.push(last);
    assert(t2.len() == d.len() + 1) by {
        assert(t2.to_multiset().len() == d.to_multiset().insert(x).len());
    }
    assert(all.push(x).to_multiset() =~= t2.to_multiset().add(r2.to_multiset()));
    assert(keys_ok(keys, fams, top[top.len() - 1]));
    lemma_keys_cmp_antisym(keys, fams, last, x);
    // Every new top row is `x` or a row of `d`, so it is not after `last`, hence not after any rest row.
    assert forall|i: int| 0 <= i < t2.len() implies keys_cmp(keys, #[trigger] t2[i], last) <= 0 by {
        if t2[i] != x {
            assert(d.contains(t2[i]));
            let m = choose|m: int| 0 <= m < d.len() && d[m] == t2[i];
            assert(top[m] == d[m]);
            lemma_sorted_le_last(keys, fams, top, m);
        }
    }
    assert forall|i: int, j: int| 0 <= i < t2.len() && 0 <= j < r2.len() implies keys_cmp(keys, #[trigger] t2[i], #[trigger] r2[j]) <= 0 by {
        assert(keys_cmp(keys, t2[i], last) <= 0);
        if j < rest.len() {
            assert(r2[j] == rest[j]);
            assert(keys_cmp(keys, top[top.len() - 1], rest[j]) <= 0);
            lemma_keys_cmp_trans(keys, fams, t2[i], last, rest[j]);
        } else {
            assert(r2[j] == last);
        }
    }
    assert forall|j: int| 0 <= j < r2.len() implies keys_ok(keys, fams, #[trigger] r2[j]) by {
        if j < rest.len() { assert(r2[j] == rest[j]); }
    }
}

/// A multiset contained in another of no larger size is equal to it.
pub proof fn lemma_sub_multiset_eq<V>(a: Multiset<V>, b: Multiset<V>)
    requires a.subset_of(b), b.len() <= a.len(),
    ensures a == b,
{
    let d = b.sub(a);
    assert(b =~= a.add(d));
    assert(d.len() == 0);
    assert(d =~= Multiset::empty()) by {
        vstd::multiset::lemma_multiset_empty_len(d);
    }
    assert(a =~= b);
}

/// The bag of a concatenation of three sequences, count by count.
proof fn lemma_count3(a: Seq<Row>, b: Seq<Row>, c: Seq<Row>, v: Row)
    ensures (a + b + c).to_multiset().count(v) == a.to_multiset().count(v) + b.to_multiset().count(v) + c.to_multiset().count(v),
{
    assert((a + b + c).to_multiset() =~= (a + b).to_multiset().add(c.to_multiset()));
    assert((a + b).to_multiset() =~= a.to_multiset().add(b.to_multiset()));
}

/// Position `j` of a concatenation of three sequences.
proof fn lemma_index3(a: Seq<Row>, b: Seq<Row>, c: Seq<Row>, j: int)
    requires 0 <= j < a.len() + b.len() + c.len(),
    ensures
        j < a.len() ==> (a + b + c)[j] == a[j],
        a.len() <= j < a.len() + b.len() ==> (a + b + c)[j] == b[j - a.len()],
        a.len() + b.len() <= j ==> (a + b + c)[j] == c[j - a.len() - b.len()],
{
    if j < a.len() + b.len() {
        assert((a + b + c)[j] == (a + b)[j]);
    }
}

/// Merge of two partial top-k splits: the top-k of the two tops is a top-k of the union.
pub proof fn lemma_topk_merge(keys: Seq<OrderKey>, fams: Seq<int>, k: nat, a: Seq<Row>, ta: Seq<Row>, ra: Seq<Row>,
    b: Seq<Row>, tb: Seq<Row>, rb: Seq<Row>, t: Seq<Row>, r2: Seq<Row>)
    requires
        topk_ok(keys, fams, k, a, ta, ra),
        topk_ok(keys, fams, k, b, tb, rb),
        topk_ok(keys, fams, k, ta + tb, t, r2),
    ensures topk_ok(keys, fams, k, a + b, t, r2 + ra + rb),
{
    let rr = r2 + ra + rb;
    let tab = ta + tb;
    assert(tab.to_multiset() =~= ta.to_multiset().add(tb.to_multiset()));
    assert((a + b).to_multiset() =~= t.to_multiset().add(rr.to_multiset())) by {
        assert forall|v: Row| #[trigger] (a + b).to_multiset().count(v) == t.to_multiset().add(rr.to_multiset()).count(v) by {
            lemma_count3(r2, ra, rb, v);
            assert((a + b).to_multiset() =~= a.to_multiset().add(b.to_multiset()));
            assert(a.to_multiset().count(v) == ta.to_multiset().count(v) + ra.to_multiset().count(v));
            assert(b.to_multiset().count(v) == tb.to_multiset().count(v) + rb.to_multiset().count(v));
            assert(tab.to_multiset().count(v) == t.to_multiset().count(v) + r2.to_multiset().count(v));
            assert(tab.to_multiset().count(v) == ta.to_multiset().count(v) + tb.to_multiset().count(v));
        }
    }
    assert forall|i: int, j: int| 0 <= i < t.len() && 0 <= j < ra.len() implies keys_cmp(keys, #[trigger] t[i], #[trigger] ra[j]) <= 0 by {
        lemma_merge_one(keys, fams, k, ta, ra, tb, tab, t, r2, i, j);
    }
    assert(ta.to_multiset().add(tb.to_multiset()) =~= tb.to_multiset().add(ta.to_multiset()));
    assert forall|i: int, j: int| 0 <= i < t.len() && 0 <= j < rb.len() implies keys_cmp(keys, #[trigger] t[i], #[trigger] rb[j]) <= 0 by {
        lemma_merge_one(keys, fams, k, tb, rb, ta, tab, t, r2, i, j);
    }
    assert forall|j: int| 0 <= j < rr.len() implies keys_ok(keys, fams, #[trigger] rr[j]) by {
        lemma_index3(r2, ra, rb, j);
        if j < r2.len() {
        } else if j < r2.len() + ra.len() {
            assert(keys_ok(keys, fams, ra[j - r2.len()]));
        } else {
            assert(keys_ok(keys, fams, rb[j - r2.len() - ra.len()]));
        }
    }
    assert forall|i: int, j: int| 0 <= i < t.len() && 0 <= j < rr.len() implies keys_cmp(keys, #[trigger] t[i], #[trigger] rr[j]) <= 0 by {
        lemma_index3(r2, ra, rb, j);
        if j < r2.len() {
        } else if j < r2.len() + ra.len() {
            assert(keys_cmp(keys, t[i], ra[j - r2.len()]) <= 0);
        } else {
            assert(keys_cmp(keys, t[i], rb[j - r2.len() - ra.len()]) <= 0);
        }
    }
    if t.len() < k {
        assert(r2.len() == 0);
        assert(t.to_multiset() =~= ta.to_multiset().add(tb.to_multiset()));
        assert(t.to_multiset().len() == ta.to_multiset().len() + tb.to_multiset().len());
        assert(ta.len() < k && tb.len() < k);
        assert(rr.len() == 0);
    }
}

/// One pair of the merge argument. If merged top row `t[i]` were after rest row `x = ra[j]`, every row of the full
/// `ta` would be strictly before `t[i]`, so none is in `r2` and all `k` of them are in `t`: then `t` is `ta` as a bag,
/// and `t[i]`, a row of `ta`, is not after `x`.
proof fn lemma_merge_one(keys: Seq<OrderKey>, fams: Seq<int>, k: nat, ta: Seq<Row>, ra: Seq<Row>, tb: Seq<Row>,
    all2: Seq<Row>, t: Seq<Row>, r2: Seq<Row>, i: int, j: int)
    requires
        sorted_by(keys, ta),
        all_keys_ok(keys, fams, ta),
        all_keys_ok(keys, fams, ra),
        ta.len() <= k,
        ta.len() < k ==> ra.len() == 0,
        forall|p: int, q: int| 0 <= p < ta.len() && 0 <= q < ra.len() ==> keys_cmp(keys, #[trigger] ta[p], #[trigger] ra[q]) <= 0,
        topk_ok(keys, fams, k, all2, t, r2),
        all2.to_multiset() == ta.to_multiset().add(tb.to_multiset()),
        0 <= i < t.len(), 0 <= j < ra.len(),
    ensures keys_cmp(keys, t[i], ra[j]) <= 0,
{
    let x = ra[j];
    let y = t[i];
    assert(keys_ok(keys, fams, y));
    assert(keys_ok(keys, fams, x));
    if keys_cmp(keys, y, x) > 0 {
        lemma_keys_cmp_antisym(keys, fams, y, x);
        // Every row of `ta` is strictly before `y`.
        assert forall|p: int| 0 <= p < ta.len() implies keys_cmp(keys, #[trigger] ta[p], y) < 0 by {
            assert(keys_cmp(keys, ta[p], x) <= 0);
            assert(keys_ok(keys, fams, ta[p]));
            lemma_keys_cmp_trans(keys, fams, ta[p], x, y);
            lemma_keys_cmp_antisym(keys, fams, ta[p], y);
            if keys_cmp(keys, ta[p], y) == 0 {
                lemma_keys_cmp_trans(keys, fams, y, ta[p], x);
            }
        }
        // So every row of `ta` counts in `t` at least as often as in `ta`.
        assert forall|v: Row| ta.to_multiset().count(v) <= #[trigger] t.to_multiset().count(v) by {
            if ta.to_multiset().count(v) > 0 {
                if r2.to_multiset().count(v) > 0 {
                    assert(ta.contains(v));
                    let p = choose|p: int| 0 <= p < ta.len() && ta[p] == v;
                    assert(r2.contains(v));
                    let q = choose|q: int| 0 <= q < r2.len() && r2[q] == v;
                    assert(keys_cmp(keys, t[i], r2[q]) <= 0);
                    lemma_keys_cmp_antisym(keys, fams, ta[p], y);
                }
                assert(all2.to_multiset().count(v) == t.to_multiset().count(v) + r2.to_multiset().count(v));
                assert(all2.to_multiset().count(v) == ta.to_multiset().count(v) + tb.to_multiset().count(v));
            }
        }
        assert(ta.to_multiset().subset_of(t.to_multiset()));
        assert(ta.len() == k);
        assert(t.to_multiset().len() <= ta.to_multiset().len());
        lemma_sub_multiset_eq(ta.to_multiset(), t.to_multiset());
        assert(t.contains(y));
        assert(ta.to_multiset().count(y) > 0);
        assert(ta.contains(y));
        let p = choose|p: int| 0 <= p < ta.len() && ta[p] == y;
        assert(keys_cmp(keys, ta[p], ra[j]) <= 0);
    }
}

/// The final output: `top` followed by the sorted rest is a sorted permutation of the bag, and its first `k` rows
/// are `top`.
pub proof fn lemma_topk_final(keys: Seq<OrderKey>, fams: Seq<int>, k: nat, all: Seq<Row>, top: Seq<Row>, rest: Seq<Row>)
    requires topk_ok(keys, fams, k, all, top, rest),
    ensures ({
        let p = top + sort_rows(keys, rest);
        &&& p.to_multiset() == all.to_multiset()
        &&& sorted_by(keys, p)
        &&& slice_rows(p, 0, Some(k)) == top
    }),
{
    lemma_sort_rows(keys, fams, rest);
    let sr = sort_rows(keys, rest);
    let p = top + sr;
    assert(p.to_multiset() =~= all.to_multiset());
    assert forall|i: int, j: int| 0 <= i < j < p.len() implies keys_cmp(keys, #[trigger] p[i], #[trigger] p[j]) <= 0 by {
        if j < top.len() {
            assert(p[i] == top[i] && p[j] == top[j]);
        } else if i >= top.len() {
            assert(p[i] == sr[i - top.len()] && p[j] == sr[j - top.len()]);
        } else {
            assert(p[i] == top[i] && p[j] == sr[j - top.len()]);
            let v = sr[j - top.len()];
            assert(sr.contains(v));
            assert(sr.to_multiset().count(v) > 0);
            assert(rest.to_multiset().count(v) > 0);
            assert(rest.contains(v));
            let q = choose|q: int| 0 <= q < rest.len() && rest[q] == sr[j - top.len()];
            assert(keys_cmp(keys, top[i], rest[q]) <= 0);
        }
    }
    assert(sr.to_multiset().len() == rest.to_multiset().len());
    assert(sr.len() == rest.len());
    if top.len() == k {
        assert(p.subrange(0, k as int) =~= top);
    } else {
        assert(rest.len() == 0);
        assert(p =~= top);
        assert(p.subrange(0, p.len() as int) =~= top);
    }
}

/// A sorted bag of at most `k` rows is its own top-k.
pub proof fn lemma_topk_self(keys: Seq<OrderKey>, fams: Seq<int>, k: nat, t: Seq<Row>)
    requires sorted_by(keys, t), all_keys_ok(keys, fams, t), t.len() <= k,
    ensures topk_ok(keys, fams, k, t, t, Seq::empty()),
{
    let e = Seq::<Row>::empty();
    assert(t.to_multiset().add(e.to_multiset()) =~= t.to_multiset());
}

} // verus!
