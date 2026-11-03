//! Exact integer sums over index ranges (`rsum`) and over sequences of any element type (`ssum`): split, extension,
//! zero, bounds for nonnegative terms, and order independence (two sequences with the same multiset have the same
//! sum; a permutation of `0..n` reindexes a range sum).
use vstd::prelude::*;
use vstd::multiset::Multiset;

verus! {

broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms};

/// `f(lo) + .. + f(hi - 1)` (0 when `hi <= lo`).
pub open spec fn rsum(lo: int, hi: int, f: spec_fn(int) -> int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { rsum(lo, hi - 1, f) + f(hi - 1) }
}

/// Sum of `f` over the elements of `s`, in order.
pub open spec fn ssum<A>(s: Seq<A>, f: spec_fn(A) -> int) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { ssum(s.drop_last(), f) + f(s.last()) }
}

/// One more index at the end.
pub proof fn lemma_rsum_step(lo: int, hi: int, f: spec_fn(int) -> int)
    requires lo <= hi,
    ensures rsum(lo, hi + 1, f) == rsum(lo, hi, f) + f(hi),
{
}

/// `rsum(lo, hi) = rsum(lo, mid) + rsum(mid, hi)`.
pub proof fn lemma_rsum_split(lo: int, mid: int, hi: int, f: spec_fn(int) -> int)
    requires lo <= mid <= hi,
    ensures rsum(lo, hi, f) == rsum(lo, mid, f) + rsum(mid, hi, f),
    decreases hi - mid,
{
    if hi > mid {
        lemma_rsum_split(lo, mid, hi - 1, f);
    }
}

/// Equal terms on the range give equal sums.
pub proof fn lemma_rsum_ext(lo: int, hi: int, f: spec_fn(int) -> int, g: spec_fn(int) -> int)
    requires forall|i: int| lo <= i < hi ==> #[trigger] f(i) == g(i),
    ensures rsum(lo, hi, f) == rsum(lo, hi, g),
    decreases hi - lo,
{
    if hi > lo {
        lemma_rsum_ext(lo, hi - 1, f, g);
    }
}

/// Zero terms give a zero sum.
pub proof fn lemma_rsum_zero(lo: int, hi: int, f: spec_fn(int) -> int)
    requires forall|i: int| lo <= i < hi ==> #[trigger] f(i) == 0,
    ensures rsum(lo, hi, f) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_rsum_zero(lo, hi - 1, f);
    }
}

/// Nonnegative terms: the sum is nonnegative and at least any one term.
pub proof fn lemma_rsum_nonneg(lo: int, hi: int, f: spec_fn(int) -> int)
    requires forall|i: int| lo <= i < hi ==> #[trigger] f(i) >= 0,
    ensures
        rsum(lo, hi, f) >= 0,
        forall|i: int| lo <= i < hi ==> #[trigger] f(i) <= rsum(lo, hi, f),
    decreases hi - lo,
{
    if hi > lo {
        lemma_rsum_nonneg(lo, hi - 1, f);
    }
}

/// Nonnegative terms: a sub-range sums to at most the whole range.
pub proof fn lemma_rsum_sub_range(lo: int, a: int, b: int, hi: int, f: spec_fn(int) -> int)
    requires lo <= a <= b <= hi, forall|i: int| lo <= i < hi ==> #[trigger] f(i) >= 0,
    ensures rsum(a, b, f) <= rsum(lo, hi, f),
{
    lemma_rsum_split(lo, a, hi, f);
    lemma_rsum_split(a, b, hi, f);
    lemma_rsum_nonneg(lo, a, f);
    lemma_rsum_nonneg(b, hi, f);
}

/// `|sum| <= sum of |terms|`.
pub proof fn lemma_rsum_abs(lo: int, hi: int, f: spec_fn(int) -> int, g: spec_fn(int) -> int)
    requires forall|i: int| lo <= i < hi ==> #[trigger] g(i) >= f(i) && g(i) >= -f(i),
    ensures rsum(lo, hi, g) >= rsum(lo, hi, f), rsum(lo, hi, g) >= -rsum(lo, hi, f),
    decreases hi - lo,
{
    if hi > lo {
        lemma_rsum_abs(lo, hi - 1, f, g);
    }
}

/// A sequence sum is the range sum over its positions.
pub proof fn lemma_ssum_index<A>(s: Seq<A>, f: spec_fn(A) -> int)
    ensures ssum(s, f) == rsum(0, s.len() as int, |i: int| f(s[i])),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        lemma_ssum_index(d, f);
        lemma_rsum_ext(0, d.len() as int, |i: int| f(d[i]), |i: int| f(s[i]));
    }
}

/// Sum of a concatenation.
pub proof fn lemma_ssum_append<A>(a: Seq<A>, b: Seq<A>, f: spec_fn(A) -> int)
    ensures ssum(a + b, f) == ssum(a, f) + ssum(b, f),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        lemma_ssum_append(a, b.drop_last(), f);
        assert((a + b).drop_last() =~= a + b.drop_last());
    }
}

/// Equal terms on the elements give equal sums.
pub proof fn lemma_ssum_ext<A>(s: Seq<A>, f: spec_fn(A) -> int, g: spec_fn(A) -> int)
    requires forall|i: int| 0 <= i < s.len() ==> f(#[trigger] s[i]) == g(s[i]),
    ensures ssum(s, f) == ssum(s, g),
    decreases s.len(),
{
    if s.len() > 0 {
        let d = s.drop_last();
        assert forall|i: int| 0 <= i < d.len() implies f(#[trigger] d[i]) == g(d[i]) by {
            assert(d[i] == s[i]);
        }
        lemma_ssum_ext(d, f, g);
        assert(s.last() == s[s.len() - 1]);
    }
}

/// Removing one element.
pub proof fn lemma_ssum_remove<A>(s: Seq<A>, i: int, f: spec_fn(A) -> int)
    requires 0 <= i < s.len(),
    ensures ssum(s, f) == ssum(s.remove(i), f) + f(s[i]),
{
    let (a, one, b) = (s.take(i), seq![s[i]], s.skip(i + 1));
    assert(s =~= a + one + b);
    assert(s.remove(i) =~= a + b);
    lemma_ssum_append(a + one, b, f);
    lemma_ssum_append(a, one, f);
    lemma_ssum_append(a, b, f);
    assert(one.drop_last() =~= Seq::<A>::empty());
    assert(ssum(Seq::<A>::empty(), f) == 0);
    assert(one.last() == s[i]);
    assert(ssum(one, f) == ssum(one.drop_last(), f) + f(one.last()));
}

/// Order independence: equal multisets give equal sums.
pub proof fn lemma_ssum_perm<A>(a: Seq<A>, b: Seq<A>, f: spec_fn(A) -> int)
    requires a.to_multiset() == b.to_multiset(),
    ensures ssum(a, f) == ssum(b, f),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(b.len() == b.to_multiset().len());
        assert(b =~= Seq::<A>::empty());
    } else {
        let x = a.last();
        let ai = a.drop_last();
        assert(ai.push(x) =~= a);
        assert(a.to_multiset().count(x) > 0);
        assert(b.to_multiset().count(x) > 0);
        assert(b.contains(x));
        let i = choose|i: int| 0 <= i < b.len() && b[i] == x;
        let bi = b.remove(i);
        assert(bi.to_multiset() =~= b.to_multiset().remove(x));
        assert(ai.to_multiset() =~= a.to_multiset().remove(x));
        lemma_ssum_perm(ai, bi, f);
        lemma_ssum_remove(b, i, f);
    }
}

/// `0, 1, .., n - 1` as positions.
pub open spec fn positions(n: nat) -> Seq<u64> {
    Seq::new(n, |k: int| k as u64)
}

/// Reindexing a range sum through a permutation `p` of `0..n` (same multiset as `positions(n)`).
pub proof fn lemma_rsum_permuted(p: Seq<u64>, n: nat, f: spec_fn(int) -> int)
    requires p.to_multiset() == positions(n).to_multiset(), n <= u64::MAX,
    ensures
        p.len() == n,
        rsum(0, n as int, |t: int| f(p[t] as int)) == rsum(0, n as int, f),
{
    assert(p.len() == p.to_multiset().len());
    assert(positions(n).len() == positions(n).to_multiset().len());
    let g = |k: u64| f(k as int);
    lemma_ssum_perm(p, positions(n), g);
    lemma_ssum_index(p, g);
    lemma_ssum_index(positions(n), g);
    lemma_rsum_ext(0, n as int, |i: int| g(p[i]), |t: int| f(p[t] as int));
    assert forall|i: int| 0 <= i < n implies g(#[trigger] positions(n)[i]) == f(i) by {
        assert(positions(n)[i] == i as u64);
    }
    lemma_rsum_ext(0, n as int, |i: int| g(positions(n)[i]), f);
}

} // verus!
