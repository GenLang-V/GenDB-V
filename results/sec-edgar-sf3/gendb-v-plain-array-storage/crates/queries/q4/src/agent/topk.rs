//! HAVING, ORDER BY total_value DESC and LIMIT 500 over the GroupBy rows (`group::g_row` of the fold's `order`).
//!
//! The groups with `COUNT(DISTINCT cik) >= 2` and a sum of at least a threshold `t` (`cand`) are sorted with the
//! statement's own stable insertion sort (`spec::order::sort_rows`, mirrored by `sort_positions`). The witness
//! permutation of all HAVING rows is that sorted list followed by the sorted rows below `t` (`rest`): every row of
//! the first part has a sum of at least `t`, larger than every sum of the second, so the concatenation is sorted;
//! its first 500 rows are the first 500 sorted candidates when there are at least 500 of them or `t` is the
//! smallest `i128` (then `rest` is empty). The threshold is a heuristic (`common::select`).
use vstd::prelude::*;
use vstd::multiset::Multiset;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::numeric::*;
use crate::spec::order::*;
use crate::bridge::order::*;
use crate::link::expr::{lemma_compare_num, lemma_align_same};
use crate::agent::cols::*;
use crate::agent::fold::*;
use crate::agent::group::*;
use crate::agent::sem::*;

verus! {

/// The group ids of `ids` satisfying `f`, in order.
pub open spec fn filt(ids: Seq<usize>, f: spec_fn(usize) -> bool) -> Seq<usize>
    decreases ids.len(),
{
    if ids.len() == 0 {
        Seq::empty()
    } else {
        filt(ids.drop_last(), f) + if f(ids.last()) { seq![ids.last()] } else { Seq::<usize>::empty() }
    }
}

pub proof fn lemma_filt_push(ids: Seq<usize>, x: usize, f: spec_fn(usize) -> bool)
    ensures filt(ids.push(x), f) == if f(x) { filt(ids, f).push(x) } else { filt(ids, f) },
{
    assert(ids.push(x).drop_last() =~= ids);
    assert(filt(ids, f) + seq![x] =~= filt(ids, f).push(x));
    assert(filt(ids, f) + Seq::<usize>::empty() =~= filt(ids, f));
}

/// The elements of a `filt` satisfy `f` and come from `ids`.
pub proof fn lemma_filt_mem(ids: Seq<usize>, f: spec_fn(usize) -> bool)
    ensures forall|t: int| 0 <= t < filt(ids, f).len() ==> f(#[trigger] filt(ids, f)[t]) && ids.contains(filt(ids, f)[t]),
    decreases ids.len(),
{
    if ids.len() > 0 {
        let d = ids.drop_last();
        lemma_filt_mem(d, f);
        assert(d.push(ids.last()) =~= ids);
        lemma_filt_push(d, ids.last(), f);
        assert forall|t: int| 0 <= t < filt(ids, f).len() implies f(#[trigger] filt(ids, f)[t]) && ids.contains(filt(ids, f)[t]) by {
            if t < filt(d, f).len() {
                assert(filt(ids, f)[t] == filt(d, f)[t]);
                let w = choose|w: int| 0 <= w < d.len() && d[w] == filt(d, f)[t];
                assert(ids[w] == d[w]);
            } else {
                assert(ids[ids.len() - 1] == ids.last());
            }
        }
    }
}

/// `keep` of mapped ids is the map of a `filt`.
pub proof fn lemma_keep_ids(ids: Seq<usize>, m: spec_fn(usize) -> Row, h: spec_fn(Row) -> bool)
    ensures crate::link::join::keep(ids.map_values(m), h) == filt(ids, |g: usize| h(m(g))).map_values(m),
    decreases ids.len(),
{
    let f = |g: usize| h(m(g));
    if ids.len() > 0 {
        let d = ids.drop_last();
        lemma_keep_ids(d, m, h);
        assert(ids.map_values(m).drop_last() =~= d.map_values(m));
        assert(ids.map_values(m).last() == m(ids.last()));
        assert(d.push(ids.last()) =~= ids);
        lemma_filt_push(d, ids.last(), f);
        if f(ids.last()) {
            assert(filt(d, f).push(ids.last()).map_values(m) =~= filt(d, f).map_values(m).push(m(ids.last())));
        }
    } else {
        assert(ids.map_values(m) =~= Seq::<Row>::empty());
        assert(filt(ids, f).map_values(m) =~= Seq::<Row>::empty());
    }
}

/// A `filt` by `f` is, as a multiset of mapped rows, the `filt`s by `f && t` and by `f && !t`.
pub proof fn lemma_filt_partition(ids: Seq<usize>, f: spec_fn(usize) -> bool, t: spec_fn(usize) -> bool, m: spec_fn(usize) -> Row)
    ensures
        filt(ids, f).map_values(m).to_multiset()
            == filt(ids, |g: usize| f(g) && t(g)).map_values(m).to_multiset().add(filt(ids, |g: usize| f(g) && !t(g)).map_values(m).to_multiset()),
    decreases ids.len(),
{
    broadcast use vstd::seq_lib::group_seq_properties;
    broadcast use vstd::multiset::group_multiset_axioms;
    let fa = |g: usize| f(g) && t(g);
    let fb = |g: usize| f(g) && !t(g);
    if ids.len() == 0 {
        assert(filt(ids, f).map_values(m) =~= Seq::<Row>::empty());
        assert(filt(ids, fa).map_values(m) =~= Seq::<Row>::empty());
        assert(filt(ids, fb).map_values(m) =~= Seq::<Row>::empty());
        assert(Multiset::<Row>::empty().add(Multiset::<Row>::empty()) =~= Multiset::<Row>::empty());
    } else {
        let d = ids.drop_last();
        let x = ids.last();
        assert(d.push(x) =~= ids);
        lemma_filt_partition(d, f, t, m);
        lemma_filt_push(d, x, f);
        lemma_filt_push(d, x, fa);
        lemma_filt_push(d, x, fb);
        if f(x) {
            assert(filt(d, f).push(x).map_values(m) =~= filt(d, f).map_values(m).push(m(x)));
            let m1 = filt(d, fa).map_values(m).to_multiset();
            let m2 = filt(d, fb).map_values(m).to_multiset();
            if t(x) {
                assert(filt(d, fa).push(x).map_values(m) =~= filt(d, fa).map_values(m).push(m(x)));
                assert(m1.add(m2).insert(m(x)) =~= m1.insert(m(x)).add(m2));
            } else {
                assert(filt(d, fb).push(x).map_values(m) =~= filt(d, fb).map_values(m).push(m(x)));
                assert(m1.add(m2).insert(m(x)) =~= m1.add(m2.insert(m(x))));
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ the sort

/// ORDER BY on two rows whose column 4 is a scale-4 numeric: the larger value first.
pub proof fn lemma_keys_cmp_sum(r1: Row, r2: Row, s1: int, s2: int)
    requires r1.len() > 4, r2.len() > 4, r1[4] == (Val::Num { coeff: s1, scale: 4 }), r2[4] == (Val::Num { coeff: s2, scale: 4 }),
    ensures keys_cmp(order_keys(), r1, r2) == if s1 > s2 { -1int } else if s1 < s2 { 1int } else { 0int },
{
    let ks = order_keys();
    reveal_with_fuel(keys_cmp, 2);
    lemma_compare_num(s1, 4, s2, 4);
    lemma_align_same(s1, 4);
    lemma_align_same(s2, 4);
    assert(max_nat(4, 4) == 4);
    assert(ks.drop_first() =~= Seq::<OrderKey>::empty());
}

/// The family of the ORDER BY key of a group row (numeric).
pub open spec fn row_fams() -> Seq<int> {
    seq![1int]
}

pub proof fn lemma_row_keys_ok(r: Row, s: int)
    requires r.len() > 4, r[4] == (Val::Num { coeff: s, scale: 4 }),
    ensures keys_ok(order_keys(), row_fams(), r),
{
    assert forall|i: int| 0 <= i < order_keys().len() implies #[trigger] key_ok(order_keys()[i], row_fams()[i], r) by {}
}

/// The sort of no rows.
pub proof fn lemma_sort_empty(keys: Seq<OrderKey>, v: Seq<Row>)
    ensures sort_rows(keys, v.take(0)) == Seq::<Row>::empty(),
{
    assert(v.take(0) =~= Seq::<Row>::empty());
}

/// One step of the stable insertion sort.
pub proof fn lemma_sort_step(keys: Seq<OrderKey>, v: Seq<Row>, k: int)
    requires 0 <= k < v.len(),
    ensures sort_rows(keys, v.take(k + 1)) == insert_sorted(keys, sort_rows(keys, v.take(k)), v[k]),
{
    assert(v.take(k + 1).drop_last() =~= v.take(k));
    assert(v.take(k + 1).last() == v[k]);
}

/// Stable insertion: inserting `r` after the last row that is not greater (position `j`).
pub proof fn lemma_insert_at(keys: Seq<OrderKey>, s: Seq<Row>, r: Row, j: int)
    requires
        0 <= j <= s.len(),
        j == 0 || keys_cmp(keys, s[j - 1], r) <= 0,
        forall|q: int| j <= q < s.len() ==> keys_cmp(keys, #[trigger] s[q], r) > 0,
    ensures insert_sorted(keys, s, r) == s.take(j) + seq![r] + s.skip(j),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.take(0) + seq![r] + s.skip(0) =~= seq![r]);
    } else if j == s.len() {
        assert(keys_cmp(keys, s.last(), r) <= 0);
        assert(s.take(j) + seq![r] + s.skip(j) =~= s.push(r));
    } else {
        assert(keys_cmp(keys, s[s.len() - 1], r) > 0);
        let d = s.drop_last();
        assert forall|q: int| j <= q < d.len() implies keys_cmp(keys, #[trigger] d[q], r) > 0 by {
            assert(d[q] == s[q]);
        }
        if j > 0 {
            assert(d[j - 1] == s[j - 1]);
        }
        lemma_insert_at(keys, d, r, j);
        assert((d.take(j) + seq![r] + d.skip(j)).push(s.last()) =~= s.take(j) + seq![r] + s.skip(j));
    }
}

/// Two sorted sequences, every row of the first not above any of the second, concatenate sorted.
pub proof fn lemma_sorted_concat(keys: Seq<OrderKey>, a: Seq<Row>, b: Seq<Row>)
    requires
        sorted_by(keys, a),
        sorted_by(keys, b),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> keys_cmp(keys, #[trigger] a[i], #[trigger] b[j]) <= 0,
    ensures sorted_by(keys, a + b),
{
    let s = a + b;
    assert forall|i: int, j: int| 0 <= i < j < s.len() implies keys_cmp(keys, #[trigger] s[i], #[trigger] s[j]) <= 0 by {
        if j < a.len() {
            assert(s[i] == a[i] && s[j] == a[j]);
        } else if i >= a.len() {
            assert(s[i] == b[i - a.len()] && s[j] == b[j - a.len()]);
        } else {
            assert(s[i] == a[i] && s[j] == b[j - a.len()]);
        }
    }
}

/// The rows at positions `order` of `v`.
#[verifier::opaque]
pub open spec fn ordered_view(v: Seq<Row>, order: Seq<usize>) -> Seq<Row> {
    Seq::new(order.len(), |q: int| v[order[q] as int])
}

pub proof fn lemma_ordered_at(v: Seq<Row>, order: Seq<usize>, q: int)
    requires 0 <= q < order.len(),
    ensures ordered_view(v, order)[q] == v[order[q] as int], ordered_view(v, order).len() == order.len(),
{
    reveal(ordered_view);
}

pub proof fn lemma_ordered_len(v: Seq<Row>, order: Seq<usize>)
    ensures ordered_view(v, order).len() == order.len(),
{
    reveal(ordered_view);
}

/// The ordered view after inserting position `k` at `j`.
pub proof fn lemma_ordered_insert(v: Seq<Row>, order: Seq<usize>, j: int, k: int)
    requires 0 <= j <= order.len(), 0 <= k < v.len(), k <= usize::MAX,
    ensures ({
        let s = ordered_view(v, order);
        ordered_view(v, order.insert(j, k as usize)) == s.take(j) + seq![v[k]] + s.skip(j)
    }),
{
    reveal(ordered_view);
    let s = ordered_view(v, order);
    let o2 = order.insert(j, k as usize);
    let t = s.take(j) + seq![v[k]] + s.skip(j);
    assert(o2.len() == order.len() + 1);
    assert forall|q: int| 0 <= q < o2.len() implies #[trigger] ordered_view(v, o2)[q] == t[q] by {
        if q < j {
            assert(o2[q] == order[q]);
        } else if q == j {
            assert(o2[q] == k as usize);
        } else {
            assert(o2[q] == order[q - 1]);
        }
    }
    assert(ordered_view(v, o2) =~= t);
}

/// The rows of group ids.
pub open spec fn grows(c: Ctx, reps: Seq<(usize, usize)>, sum: Seq<i128>, cnt: Seq<usize>, dcnt: Seq<usize>, ids: Seq<usize>) -> Seq<Row> {
    ids.map_values(|g: usize| g_row(c, reps, sum, cnt, dcnt, g as int))
}

/// Column 4 of a group row is its sum.
pub proof fn lemma_g_row_sum(c: Ctx, reps: Seq<(usize, usize)>, sum: Seq<i128>, cnt: Seq<usize>, dcnt: Seq<usize>, g: int)
    ensures g_row(c, reps, sum, cnt, dcnt, g).len() == 6,
        g_row(c, reps, sum, cnt, dcnt, g)[4] == (Val::Num { coeff: sum[g] as int, scale: 4 }),
        g_row(c, reps, sum, cnt, dcnt, g)[3] == Val::Int(dcnt[g] as int),
{
}

/// ORDER BY sort of the candidate groups `ids` by sum: stable insertion (the spec's `sort_rows`), as positions into
/// `ids`.
pub fn sort_positions(ids: &Vec<usize>, sum: &Vec<i128>, Ghost(c): Ghost<Ctx>, Ghost(reps): Ghost<Seq<(usize, usize)>>,
    Ghost(cnt): Ghost<Seq<usize>>, Ghost(dcnt): Ghost<Seq<usize>>) -> (r: Vec<usize>)
    requires forall|q: int| 0 <= q < ids@.len() ==> (#[trigger] ids@[q] as int) < sum@.len(),
    ensures
        r@.len() == ids@.len(),
        forall|q: int| 0 <= q < r@.len() ==> #[trigger] r@[q] < ids@.len(),
        ordered_view(grows(c, reps, sum@, cnt, dcnt, ids@), r@) == sort_rows(order_keys(), grows(c, reps, sum@, cnt, dcnt, ids@)),
{
    hide(keys_cmp);
    hide(sort_rows);
    hide(insert_sorted);
    let ghost v = grows(c, reps, sum@, cnt, dcnt, ids@);
    let ghost keys = order_keys();
    let len = ids.len();
    let mut out: Vec<usize> = Vec::new();
    let mut k: usize = 0;
    proof {
        lemma_sort_empty(keys, v);
        reveal(ordered_view);
        assert(ordered_view(v, out@) =~= Seq::<Row>::empty());
    }
    while k < len
        invariant
            len == ids@.len(), k <= len, v == grows(c, reps, sum@, cnt, dcnt, ids@), keys == order_keys(),
            forall|q: int| 0 <= q < ids@.len() ==> (#[trigger] ids@[q] as int) < sum@.len(),
            out@.len() == k,
            forall|q: int| 0 <= q < out@.len() ==> #[trigger] out@[q] < len,
            ordered_view(v, out@) == sort_rows(keys, v.take(k as int)),
        decreases len - k,
    {
        let ghost s = ordered_view(v, out@);
        proof {
            lemma_ordered_len(v, out@);
        }
        let sk = sum[ids[k]];
        let mut j: usize = out.len();
        let mut done = false;
        while j > 0 && !done
            invariant
                done ==> j > 0 && keys_cmp(keys, s[j - 1], v[k as int]) <= 0,
                j <= out@.len(), k < len, len == ids@.len(),
                v == grows(c, reps, sum@, cnt, dcnt, ids@), keys == order_keys(),
                s == ordered_view(v, out@), sk == sum@[ids@[k as int] as int],
                forall|q: int| 0 <= q < ids@.len() ==> (#[trigger] ids@[q] as int) < sum@.len(),
                forall|q: int| 0 <= q < out@.len() ==> #[trigger] out@[q] < len,
                forall|q: int| j <= q < s.len() ==> keys_cmp(keys, #[trigger] s[q], v[k as int]) > 0,
            decreases j + (if done { 0int } else { 1int }),
        {
            let p = out[j - 1];
            let sp = sum[ids[p]];
            proof {
                lemma_ordered_at(v, out@, j - 1);
                reveal(keys_cmp);
                lemma_g_row_sum(c, reps, sum@, cnt, dcnt, ids@[p as int] as int);
                lemma_g_row_sum(c, reps, sum@, cnt, dcnt, ids@[k as int] as int);
                lemma_keys_cmp_sum(v[p as int], v[k as int], sp as int, sk as int);
            }
            if sp >= sk {
                done = true;
            } else {
                j = j - 1;
            }
        }
        proof {
            lemma_insert_at(keys, s, v[k as int], j as int);
            lemma_sort_step(keys, v, k as int);
        }
        let ghost before = out@;
        out.insert(j, k);
        proof {
            lemma_ordered_insert(v, before, j as int, k as int);
        }
        k = k + 1;
    }
    proof {
        assert(v.take(len as int) =~= v);
    }
    out
}

} // verus!
