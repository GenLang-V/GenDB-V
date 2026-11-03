//! Group-by of (key, value) entries: sort the entries by key (`sort::sort_range`), then one group per distinct key
//! with its entry count and exact value sum, keys strictly increasing. The absolute value sum of every group is
//! tracked in `u128`; when one exceeds `i128::MAX` the group-by refuses with that key (`Err(key)`), so every
//! running sum fits `i128`. Per-key counts and sums of an entry sequence (`pcount`, `psum`, `pabs`) depend only on
//! its multiset (`lemma_p_perm`).
use vstd::prelude::*;
use crate::spec::numeric::abs;
use super::sort::{KeyOrder, sort_range, sorted_by, all_ok, SortOrder};

verus! {

broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms};

/// One entry: group key and value.
#[derive(Clone, Copy)]
pub struct Entry {
    pub key: u64,
    pub value: i128,
}

/// One group: key, number of entries, exact value sum.
#[derive(Clone, Copy)]
pub struct Group {
    pub key: u64,
    pub count: u64,
    pub sum: i128,
}

/// Sum of `f` over a sequence.
pub open spec fn tsum<T>(s: Seq<T>, f: spec_fn(T) -> int) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { tsum(s.drop_last(), f) + f(s.last()) }
}

pub open spec fn cnt_f(p: u64) -> spec_fn(Entry) -> int {
    |e: Entry| if e.key == p { 1int } else { 0int }
}

pub open spec fn sum_f(p: u64) -> spec_fn(Entry) -> int {
    |e: Entry| if e.key == p { e.value as int } else { 0int }
}

pub open spec fn abs_f(p: u64) -> spec_fn(Entry) -> int {
    |e: Entry| if e.key == p { abs(e.value as int) } else { 0int }
}

/// Number, value sum and absolute value sum of the entries of key `p`.
pub open spec fn pcount(es: Seq<Entry>, p: u64) -> int {
    tsum(es, cnt_f(p))
}

pub open spec fn psum(es: Seq<Entry>, p: u64) -> int {
    tsum(es, sum_f(p))
}

pub open spec fn pabs(es: Seq<Entry>, p: u64) -> int {
    tsum(es, abs_f(p))
}

pub proof fn lemma_tsum_append<T>(a: Seq<T>, b: Seq<T>, f: spec_fn(T) -> int)
    ensures tsum(a + b, f) == tsum(a, f) + tsum(b, f),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        lemma_tsum_append(a, b.drop_last(), f);
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
    }
}

proof fn lemma_tsum_remove<T>(s: Seq<T>, i: int, f: spec_fn(T) -> int)
    requires 0 <= i < s.len(),
    ensures tsum(s, f) == tsum(s.remove(i), f) + f(s[i]),
{
    let a = s.subrange(0, i);
    let b = s.subrange(i + 1, s.len() as int);
    assert(s =~= a + seq![s[i]] + b);
    assert(s.remove(i) =~= a + b);
    lemma_tsum_append(a + seq![s[i]], b, f);
    lemma_tsum_append(a, seq![s[i]], f);
    lemma_tsum_append(a, b, f);
    assert(seq![s[i]].drop_last() =~= Seq::<T>::empty());
    assert(seq![s[i]].last() == s[i]);
    assert(tsum(Seq::<T>::empty(), f) == 0);
    assert(tsum(seq![s[i]], f) == f(s[i]));
    assert(tsum(s, f) == tsum(a + seq![s[i]] + b, f));
    assert(tsum(s.remove(i), f) == tsum(a + b, f));
}

/// The same multiset gives the same sum.
pub proof fn lemma_tsum_perm<T>(a: Seq<T>, b: Seq<T>, f: spec_fn(T) -> int)
    requires a.to_multiset() == b.to_multiset(),
    ensures tsum(a, f) == tsum(b, f),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(b.to_multiset().len() == 0);
        assert(b.len() == 0);
    } else {
        let x = a.last();
        let ai = a.drop_last();
        assert(ai.push(x) =~= a);
        assert(a.to_multiset().count(x) > 0);
        assert(b.contains(x));
        let i = choose|i: int| 0 <= i < b.len() && b[i] == x;
        let bi = b.remove(i);
        assert(bi.to_multiset() =~= b.to_multiset().remove(x));
        assert(ai.to_multiset() =~= a.to_multiset().remove(x));
        lemma_tsum_perm(ai, bi, f);
        lemma_tsum_remove(b, i, f);
    }
}

pub proof fn lemma_p_perm(a: Seq<Entry>, b: Seq<Entry>, p: u64)
    requires a.to_multiset() == b.to_multiset(),
    ensures pcount(a, p) == pcount(b, p), psum(a, p) == psum(b, p), pabs(a, p) == pabs(b, p),
{
    lemma_tsum_perm(a, b, cnt_f(p));
    lemma_tsum_perm(a, b, sum_f(p));
    lemma_tsum_perm(a, b, abs_f(p));
}

/// Absolute sums are non-negative and grow along prefixes.
proof fn lemma_pabs_mono(es: Seq<Entry>, i: int, p: u64)
    requires 0 <= i <= es.len(),
    ensures 0 <= pabs(es.subrange(0, i), p) <= pabs(es, p),
    decreases es.len() - i,
{
    if i < es.len() {
        lemma_pabs_mono(es, i + 1, p);
        lemma_p_push(es, i, p);
        lemma_pabs_nonneg(es.subrange(0, i), p);
    } else {
        assert(es.subrange(0, i) =~= es);
        lemma_pabs_nonneg(es, p);
    }
}

proof fn lemma_pabs_nonneg(es: Seq<Entry>, p: u64)
    ensures pabs(es, p) >= 0,
    decreases es.len(),
{
    if es.len() > 0 {
        lemma_pabs_nonneg(es.drop_last(), p);
    }
}

/// The groups of entries `es`: strictly increasing keys, one per key present, with its count and sum; every key's
/// absolute sum fits `i128`.
pub open spec fn groups_ok(es: Seq<Entry>, gs: Seq<Group>) -> bool {
    &&& forall|a: int, b: int| 0 <= a < b < gs.len() ==> #[trigger] gs[a].key < #[trigger] gs[b].key
    &&& forall|g: int| 0 <= g < gs.len() ==> #[trigger] gs[g].count as int == pcount(es, gs[g].key)
        && gs[g].count > 0 && gs[g].sum as int == psum(es, gs[g].key)
    &&& forall|p: u64| #[trigger] pcount(es, p) > 0 ==> exists|g: int| 0 <= g < gs.len() && gs[g].key == p
    &&& forall|p: u64| #[trigger] pabs(es, p) <= i128::MAX
}

/// `|v|` as `u128`.
fn abs_u128(v: i128) -> (r: u128)
    ensures r as int == abs(v as int),
    no_unwind
{
    if v < 0 { ((-(v + 1)) as u128) + 1 } else { v as u128 }
}

/// One step of the per-key sums.
proof fn lemma_p_push(es: Seq<Entry>, i: int, p: u64)
    requires 0 <= i < es.len(),
    ensures
        pcount(es.subrange(0, i + 1), p) == pcount(es.subrange(0, i), p) + if es[i].key == p { 1int } else { 0int },
        psum(es.subrange(0, i + 1), p) == psum(es.subrange(0, i), p) + if es[i].key == p { es[i].value as int } else { 0int },
        pabs(es.subrange(0, i + 1), p) == pabs(es.subrange(0, i), p) + if es[i].key == p { abs(es[i].value as int) } else { 0int },
{
    assert(es.subrange(0, i + 1).drop_last() =~= es.subrange(0, i));
}

/// Group sorted entries `v` (nondecreasing keys).
fn group_sorted(v: &Vec<Entry>) -> (r: Result<Vec<Group>, u64>)
    requires forall|a: int, b: int| 0 <= a < b < v@.len() ==> #[trigger] v@[a].key <= #[trigger] v@[b].key,
    ensures
        r matches Ok(gs) ==> groups_ok(v@, gs@),
        r matches Err(p) ==> pabs(v@, p) > i128::MAX,
{
    let n = v.len();
    let mut gs: Vec<Group> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(v@.subrange(0, 0) =~= Seq::<Entry>::empty());
    }
    while i < n
        invariant
            n == v@.len(), i <= n,
            forall|a: int, b: int| 0 <= a < b < v@.len() ==> #[trigger] v@[a].key <= #[trigger] v@[b].key,
            forall|a: int, b: int| 0 <= a < b < gs@.len() ==> #[trigger] gs@[a].key < #[trigger] gs@[b].key,
            forall|g: int| 0 <= g < gs@.len() ==> #[trigger] gs@[g].count as int == pcount(v@.subrange(0, i as int), gs@[g].key)
                && gs@[g].count > 0 && gs@[g].sum as int == psum(v@.subrange(0, i as int), gs@[g].key),
            forall|p: u64| #[trigger] pcount(v@.subrange(0, i as int), p) > 0 ==> exists|g: int| 0 <= g < gs@.len() && gs@[g].key == p,
            forall|p: u64| #[trigger] pabs(v@.subrange(0, i as int), p) <= i128::MAX,
            i < n ==> forall|p: u64| p >= v@[i as int].key ==> #[trigger] pcount(v@.subrange(0, i as int), p) == 0
                && pabs(v@.subrange(0, i as int), p) == 0 && psum(v@.subrange(0, i as int), p) == 0,
            i < n ==> forall|g: int| 0 <= g < gs@.len() ==> #[trigger] gs@[g].key < v@[i as int].key,
        decreases n - i,
    {
        let p = v[i].key;
        let mut cnt: u64 = 0;
        let mut sum: i128 = 0;
        let mut ab: u128 = 0;
        let mut j = i;
        proof {
            assert(pcount(v@.subrange(0, i as int), p) == 0);
            assert(v@.subrange(0, i as int) =~= v@.subrange(0, j as int));
        }
        while j < n && v[j].key == p
            invariant
                n == v@.len(), i < n, i <= j <= n, p == v@[i as int].key,
                forall|a: int, b: int| 0 <= a < b < v@.len() ==> #[trigger] v@[a].key <= #[trigger] v@[b].key,
                forall|q: u64| q >= p ==> #[trigger] pcount(v@.subrange(0, i as int), q) == 0
                    && pabs(v@.subrange(0, i as int), q) == 0 && psum(v@.subrange(0, i as int), q) == 0,
                forall|k: int| i <= k < j ==> #[trigger] v@[k].key == p,
                cnt as int == pcount(v@.subrange(0, j as int), p), cnt as int == j - i,
                sum as int == psum(v@.subrange(0, j as int), p),
                ab as int == pabs(v@.subrange(0, j as int), p), ab <= i128::MAX,
                forall|q: u64| q != p ==> #[trigger] pcount(v@.subrange(0, j as int), q) == pcount(v@.subrange(0, i as int), q)
                    && psum(v@.subrange(0, j as int), q) == psum(v@.subrange(0, i as int), q)
                    && pabs(v@.subrange(0, j as int), q) == pabs(v@.subrange(0, i as int), q),
            decreases n - j,
        {
            let val = v[j].value;
            let a = abs_u128(val);
            proof {
                lemma_p_push(v@, j as int, p);
                assert forall|q: u64| q != p implies #[trigger] pcount(v@.subrange(0, j + 1), q) == pcount(v@.subrange(0, i as int), q)
                    && psum(v@.subrange(0, j + 1), q) == psum(v@.subrange(0, i as int), q)
                    && pabs(v@.subrange(0, j + 1), q) == pabs(v@.subrange(0, i as int), q) by {
                    lemma_p_push(v@, j as int, q);
                }
            }
            if ab + a > i128::MAX as u128 {
                proof {
                    lemma_pabs_mono(v@, j + 1, p);
                    assert(v@.subrange(0, n as int) =~= v@);
                }
                return Err(p);
            }
            ab = ab + a;
            proof {
                lemma_psum_bound(v@.subrange(0, j + 1), p);
            }
            sum = sum + val;
            cnt = cnt + 1;
            j = j + 1;
        }
        proof {
            // the next entry (if any) has a larger key
            if j < n {
                assert(v@[j as int].key != p);
                assert(v@[i as int].key <= v@[j as int].key);
                assert forall|q: u64| q >= v@[j as int].key implies #[trigger] pcount(v@.subrange(0, j as int), q) == 0
                    && pabs(v@.subrange(0, j as int), q) == 0 && psum(v@.subrange(0, j as int), q) == 0 by {
                    assert(q != p);
                }
            }
        }
        let ghost gs0 = gs@;
        gs.push(Group { key: p, count: cnt, sum });
        proof {
            let pre = v@.subrange(0, j as int);
            assert forall|g: int| 0 <= g < gs@.len() implies #[trigger] gs@[g].count as int == pcount(pre, gs@[g].key)
                && gs@[g].count > 0 && gs@[g].sum as int == psum(pre, gs@[g].key) by {
                if g < gs0.len() {
                    assert(gs@[g] == gs0[g]);
                    assert(gs0[g].key < p);
                }
            }
            assert forall|p2: u64| #[trigger] pcount(pre, p2) > 0 implies exists|g: int| 0 <= g < gs@.len() && gs@[g].key == p2 by {
                if p2 == p {
                    assert(gs@[gs0.len() as int].key == p);
                } else {
                    let g = choose|g: int| 0 <= g < gs0.len() && gs0[g].key == p2;
                    assert(gs@[g].key == p2);
                }
            }
            assert forall|p2: u64| #[trigger] pabs(pre, p2) <= i128::MAX by {
                if p2 != p {
                    assert(pcount(pre, p2) == pcount(v@.subrange(0, i as int), p2));
                    assert(pabs(pre, p2) == pabs(v@.subrange(0, i as int), p2));
                }
            }
            if j < n {
                assert forall|g: int| 0 <= g < gs@.len() implies #[trigger] gs@[g].key < v@[j as int].key by {
                    if g < gs0.len() {
                        assert(gs@[g] == gs0[g]);
                    }
                }
            }
        }
        i = j;
    }
    proof {
        assert(v@.subrange(0, n as int) =~= v@);
    }
    Ok(gs)
}

/// `|psum| <= pabs`.
proof fn lemma_psum_bound(es: Seq<Entry>, p: u64)
    ensures -pabs(es, p) <= psum(es, p) <= pabs(es, p),
    decreases es.len(),
{
    if es.len() > 0 {
        lemma_psum_bound(es.drop_last(), p);
    }
}

/// The groups of `es` (any order), or the key of a group whose absolute value sum exceeds `i128::MAX`.
pub fn group_by(es: Vec<Entry>) -> (r: Result<Vec<Group>, u64>)
    ensures
        r matches Ok(gs) ==> groups_ok(es@, gs@),
        r matches Err(p) ==> pabs(es@, p) > i128::MAX,
{
    let ghost e0 = es@;
    let n = es.len();
    let mut v = es;
    let mut tmp: Vec<Entry> = v.clone();
    let o = KeyOrder {};
    proof {
        assert(v@.subrange(0, n as int) =~= v@);
        assert forall|q: int| 0 <= q < v@.subrange(0, n as int).len() implies o.ok(#[trigger] v@.subrange(0, n as int)[q]) by {}
    }
    sort_range(&o, &mut v, &mut tmp, 0, n);
    proof {
        assert(v@.subrange(0, n as int) =~= v@);
        assert(e0.subrange(0, n as int) =~= e0);
        assert forall|a: int, b: int| 0 <= a < b < v@.len() implies #[trigger] v@[a].key <= #[trigger] v@[b].key by {
            assert(o.le(v@[a], v@[b]));
        }
    }
    let r = group_sorted(&v);
    proof {
        assert forall|p: u64| #[trigger] pcount(e0, p) == pcount(v@, p) by {
            lemma_p_perm(v@, e0, p);
        }
        assert forall|p: u64| #[trigger] psum(e0, p) == psum(v@, p) by {
            lemma_p_perm(v@, e0, p);
        }
        assert forall|p: u64| #[trigger] pabs(e0, p) == pabs(v@, p) by {
            lemma_p_perm(v@, e0, p);
        }
        if r is Ok {
            let gs = r->Ok_0@;
            assert forall|g: int| 0 <= g < gs.len() implies #[trigger] gs[g].count as int == pcount(e0, gs[g].key)
                && gs[g].count > 0 && gs[g].sum as int == psum(e0, gs[g].key) by {
                assert(pcount(e0, gs[g].key) == pcount(v@, gs[g].key));
                assert(psum(e0, gs[g].key) == psum(v@, gs[g].key));
            }
        }
    }
    r
}

} // verus!
