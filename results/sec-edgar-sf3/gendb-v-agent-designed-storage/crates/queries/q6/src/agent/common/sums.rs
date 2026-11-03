//! Sums of integer functions over index ranges (`isum`) and over index lists (`lsum`), with the laws used to
//! reorganize a sum over a product of tables into the order an algorithm visits it: extensionality, splitting,
//! zero terms, restriction to a sub-range, one nonzero term, pointwise addition, exchange of a double sum, and a
//! duplicate-free list that holds every nonzero index.
use vstd::prelude::*;

verus! {

/// `f(lo) + .. + f(hi - 1)` (0 for an empty range).
pub open spec fn isum(lo: int, hi: int, f: spec_fn(int) -> int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { isum(lo, hi - 1, f) + f(hi - 1) }
}

/// `f(l[0]) + .. + f(l[n - 1])`.
pub open spec fn lsum(l: Seq<int>, f: spec_fn(int) -> int) -> int
    decreases l.len(),
{
    if l.len() == 0 { 0 } else { lsum(l.drop_last(), f) + f(l.last()) }
}

pub proof fn lemma_isum_ext(lo: int, hi: int, f: spec_fn(int) -> int, g: spec_fn(int) -> int)
    requires forall|i: int| lo <= i < hi ==> #[trigger] f(i) == g(i),
    ensures isum(lo, hi, f) == isum(lo, hi, g),
    decreases hi - lo,
{
    if hi > lo {
        lemma_isum_ext(lo, hi - 1, f, g);
    }
}

pub proof fn lemma_isum_split(lo: int, mid: int, hi: int, f: spec_fn(int) -> int)
    requires lo <= mid <= hi,
    ensures isum(lo, hi, f) == isum(lo, mid, f) + isum(mid, hi, f),
    decreases hi - mid,
{
    if hi > mid {
        lemma_isum_split(lo, mid, hi - 1, f);
    }
}

pub proof fn lemma_isum_zero(lo: int, hi: int, f: spec_fn(int) -> int)
    requires forall|i: int| lo <= i < hi ==> #[trigger] f(i) == 0,
    ensures isum(lo, hi, f) == 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_isum_zero(lo, hi - 1, f);
    }
}

/// Only `[a, b)` contributes.
pub proof fn lemma_isum_restrict(lo: int, hi: int, a: int, b: int, f: spec_fn(int) -> int)
    requires
        lo <= a <= b <= hi,
        forall|i: int| lo <= i < hi && !(a <= i < b) ==> #[trigger] f(i) == 0,
    ensures isum(lo, hi, f) == isum(a, b, f),
{
    lemma_isum_split(lo, a, hi, f);
    lemma_isum_split(a, b, hi, f);
    lemma_isum_zero(lo, a, f);
    lemma_isum_zero(b, hi, f);
}

/// Only `t` contributes.
pub proof fn lemma_isum_single(lo: int, hi: int, t: int, f: spec_fn(int) -> int)
    requires
        lo <= t < hi,
        forall|i: int| lo <= i < hi && i != t ==> #[trigger] f(i) == 0,
    ensures isum(lo, hi, f) == f(t),
{
    lemma_isum_restrict(lo, hi, t, t + 1, f);
    assert(isum(t, t + 1, f) == isum(t, t, f) + f(t));
}

pub proof fn lemma_isum_add(lo: int, hi: int, f: spec_fn(int) -> int, g: spec_fn(int) -> int)
    ensures isum(lo, hi, |i: int| f(i) + g(i)) == isum(lo, hi, f) + isum(lo, hi, g),
    decreases hi - lo,
{
    if hi > lo {
        lemma_isum_add(lo, hi - 1, f, g);
    }
}

pub proof fn lemma_isum_mul(lo: int, hi: int, f: spec_fn(int) -> int, c: int)
    ensures isum(lo, hi, |i: int| c * f(i)) == c * isum(lo, hi, f),
    decreases hi - lo,
{
    if hi > lo {
        lemma_isum_mul(lo, hi - 1, f, c);
        assert(c * isum(lo, hi - 1, f) + c * f(hi - 1) == c * (isum(lo, hi - 1, f) + f(hi - 1))) by (nonlinear_arith);
    }
}

/// Exchange of a double sum.
pub proof fn lemma_isum_swap(lo1: int, hi1: int, lo2: int, hi2: int, h: spec_fn(int, int) -> int)
    ensures
        isum(lo1, hi1, |a: int| isum(lo2, hi2, |b: int| h(a, b)))
            == isum(lo2, hi2, |b: int| isum(lo1, hi1, |a: int| h(a, b))),
    decreases hi1 - lo1,
{
    let outer = |a: int| isum(lo2, hi2, |b: int| h(a, b));
    let f2 = |b: int| isum(lo1, hi1, |a: int| h(a, b));
    if hi1 > lo1 {
        let last = hi1 - 1;
        lemma_isum_swap(lo1, last, lo2, hi2, h);
        let ff = |b: int| isum(lo1, last, |a: int| h(a, b));
        let gg = |b: int| h(last, b);
        assert(isum(lo1, hi1, outer) == isum(lo1, last, outer) + outer(last));
        assert(isum(lo1, last, outer) == isum(lo2, hi2, ff));
        lemma_isum_ext(lo2, hi2, |b: int| h(last, b), gg);
        assert(outer(last) == isum(lo2, hi2, gg));
        lemma_isum_add(lo2, hi2, ff, gg);
        let sum_fg = |i: int| ff(i) + gg(i);
        assert forall|b: int| lo2 <= b < hi2 implies #[trigger] sum_fg(b) == f2(b) by {
            let hb = |a: int| h(a, b);
            assert(isum(lo1, hi1, hb) == isum(lo1, last, hb) + hb(last));
            lemma_isum_ext(lo1, last, hb, |a: int| h(a, b));
        }
        lemma_isum_ext(lo2, hi2, sum_fg, f2);
    } else {
        lemma_isum_zero(lo2, hi2, f2);
    }
}

/// The sum over a duplicate-free list of indices of `[lo, hi)` that holds every index with a nonzero term.
pub proof fn lemma_isum_list(lo: int, hi: int, l: Seq<int>, f: spec_fn(int) -> int)
    requires
        l.no_duplicates(),
        forall|t: int| 0 <= t < l.len() ==> lo <= #[trigger] l[t] < hi,
        forall|i: int| lo <= i < hi && #[trigger] f(i) != 0 ==> l.contains(i),
    ensures isum(lo, hi, f) == lsum(l, f),
    decreases l.len(),
{
    if l.len() == 0 {
        lemma_isum_zero(lo, hi, f);
    } else {
        let t = l.last();
        let init = l.drop_last();
        let g = |i: int| if i == t { 0 } else { f(i) };
        let e = |i: int| if i == t { f(t) } else { 0 };
        assert forall|i: int| lo <= i < hi && #[trigger] g(i) != 0 implies init.contains(i) by {
            assert(l.contains(i));
            let k = choose|k: int| 0 <= k < l.len() && l[k] == i;
            assert(k != l.len() - 1);
            assert(init[k] == i);
        }
        assert forall|k: int| 0 <= k < init.len() implies lo <= #[trigger] init[k] < hi by {
            assert(init[k] == l[k]);
        }
        assert(init.no_duplicates()) by {
            assert forall|a: int, b: int| 0 <= a < b < init.len() implies init[a] != init[b] by {
                assert(init[a] == l[a] && init[b] == l[b]);
            }
        }
        lemma_isum_list(lo, hi, init, g);
        assert forall|k: int| 0 <= k < init.len() implies #[trigger] g(init[k]) == f(init[k]) by {
            assert(init[k] == l[k] && l[k] != l[l.len() - 1]);
        }
        lemma_lsum_ext(init, g, f);
        lemma_isum_single(lo, hi, t, e);
        lemma_isum_add(lo, hi, g, e);
        lemma_isum_ext(lo, hi, |i: int| g(i) + e(i), f);
    }
}

pub proof fn lemma_lsum_ext(l: Seq<int>, f: spec_fn(int) -> int, g: spec_fn(int) -> int)
    requires forall|k: int| 0 <= k < l.len() ==> #[trigger] f(l[k]) == g(l[k]),
    ensures lsum(l, f) == lsum(l, g),
    decreases l.len(),
{
    if l.len() > 0 {
        let init = l.drop_last();
        assert forall|k: int| 0 <= k < init.len() implies #[trigger] f(init[k]) == g(init[k]) by {
            assert(init[k] == l[k]);
        }
        lemma_lsum_ext(init, f, g);
        assert(f(l[l.len() - 1]) == g(l[l.len() - 1]));
    }
}

pub proof fn lemma_lsum_append(a: Seq<int>, b: Seq<int>, f: spec_fn(int) -> int)
    ensures lsum(a + b, f) == lsum(a, f) + lsum(b, f),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        lemma_lsum_append(a, b.drop_last(), f);
    }
}

/// The range sum is the list sum of the range's indices in order.
pub proof fn lemma_lsum_range(lo: int, hi: int, f: spec_fn(int) -> int)
    requires lo <= hi,
    ensures lsum(Seq::new((hi - lo) as nat, |t: int| lo + t), f) == isum(lo, hi, f),
    decreases hi - lo,
{
    let l = Seq::new((hi - lo) as nat, |t: int| lo + t);
    if hi > lo {
        lemma_lsum_range(lo, hi - 1, f);
        assert(l.drop_last() =~= Seq::new((hi - 1 - lo) as nat, |t: int| lo + t));
    }
}


/// A range cut at nondecreasing boundaries `b(lo) .. b(hi)`: the sum of the pieces' sums.
pub proof fn lemma_isum_runs(lo: int, hi: int, b: spec_fn(int) -> int, f: spec_fn(int) -> int)
    requires lo <= hi, forall|s: int, t: int| lo <= s <= t <= hi ==> #[trigger] b(s) <= #[trigger] b(t),
    ensures isum(b(lo), b(hi), f) == isum(lo, hi, |s: int| isum(b(s), b(s + 1), f)),
    decreases hi - lo,
{
    if hi > lo {
        lemma_isum_runs(lo, hi - 1, b, f);
        assert(b(lo) <= b(hi - 1) && b(hi - 1) <= b(hi));
        lemma_isum_split(b(lo), b(hi - 1), b(hi), f);
    }
}

/// `tsum` over any element type: `f(s[0]) + .. + f(s[n - 1])`.
pub open spec fn tsum<T>(s: Seq<T>, f: spec_fn(T) -> int) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { tsum(s.drop_last(), f) + f(s.last()) }
}

pub proof fn lemma_tsum_append<T>(a: Seq<T>, b: Seq<T>, f: spec_fn(T) -> int)
    ensures tsum(a + b, f) == tsum(a, f) + tsum(b, f),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        assert((a + b).drop_last() =~= a + b.drop_last());
        lemma_tsum_append(a, b.drop_last(), f);
    }
}

pub proof fn lemma_tsum_ext<T>(s: Seq<T>, f: spec_fn(T) -> int, g: spec_fn(T) -> int)
    requires forall|k: int| 0 <= k < s.len() ==> #[trigger] f(s[k]) == g(s[k]),
    ensures tsum(s, f) == tsum(s, g),
    decreases s.len(),
{
    if s.len() > 0 {
        let init = s.drop_last();
        assert forall|k: int| 0 <= k < init.len() implies #[trigger] f(init[k]) == g(init[k]) by {
            assert(init[k] == s[k]);
        }
        lemma_tsum_ext(init, f, g);
        assert(f(s[s.len() - 1]) == g(s[s.len() - 1]));
    }
}

/// Removing element `i` removes its term.
pub proof fn lemma_tsum_remove<T>(s: Seq<T>, i: int, f: spec_fn(T) -> int)
    requires 0 <= i < s.len(),
    ensures tsum(s, f) == tsum(s.remove(i), f) + f(s[i]),
{
    let (a, one, b) = (s.take(i), seq![s[i]], s.skip(i + 1));
    assert(s =~= a + one + b);
    assert(s.remove(i) =~= a + b);
    lemma_tsum_append(a + one, b, f);
    lemma_tsum_append(a, one, f);
    lemma_tsum_append(a, b, f);
    assert(one.drop_last() =~= Seq::<T>::empty());
    assert(tsum(Seq::<T>::empty(), f) == 0);
    assert(tsum(one, f) == f(s[i]));
}

/// The same multiset gives the same sum.
pub proof fn lemma_tsum_perm<T>(a: Seq<T>, b: Seq<T>, f: spec_fn(T) -> int)
    requires a.to_multiset() == b.to_multiset(),
    ensures tsum(a, f) == tsum(b, f),
    decreases a.len(),
{
    a.to_multiset_ensures();
    b.to_multiset_ensures();
    if a.len() == 0 {
        assert(b.to_multiset().len() == 0);
        assert(b.len() == 0);
    } else {
        let x = a.last();
        let ai = a.drop_last();
        assert(ai.push(x) =~= a);
        ai.to_multiset_ensures();
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


/// A sum of nonnegative terms is nonnegative.
pub proof fn lemma_isum_nonneg(lo: int, hi: int, f: spec_fn(int) -> int)
    requires forall|i: int| lo <= i < hi ==> #[trigger] f(i) >= 0,
    ensures isum(lo, hi, f) >= 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_isum_nonneg(lo, hi - 1, f);
    }
}

/// A zero sum of nonnegative terms has only zero terms.
pub proof fn lemma_isum_zero_terms(lo: int, hi: int, f: spec_fn(int) -> int, t: int)
    requires forall|i: int| lo <= i < hi ==> #[trigger] f(i) >= 0, isum(lo, hi, f) == 0, lo <= t < hi,
    ensures f(t) == 0,
{
    lemma_isum_split(lo, t, hi, f);
    lemma_isum_split(t, t + 1, hi, f);
    lemma_isum_nonneg(lo, t, f);
    lemma_isum_nonneg(t + 1, hi, f);
    assert(isum(t, t + 1, f) == isum(t, t, f) + f(t));
}

/// Pointwise smaller terms give a smaller sum.
pub proof fn lemma_isum_le(lo: int, hi: int, f: spec_fn(int) -> int, g: spec_fn(int) -> int)
    requires forall|i: int| lo <= i < hi ==> #[trigger] f(i) <= g(i),
    ensures isum(lo, hi, f) <= isum(lo, hi, g),
    decreases hi - lo,
{
    if hi > lo {
        lemma_isum_le(lo, hi - 1, f, g);
    }
}

/// The sum over a duplicate-free list of indices of `[lo, hi)` of nonnegative terms is at most the range sum.
pub proof fn lemma_lsum_le_isum(lo: int, hi: int, l: Seq<int>, f: spec_fn(int) -> int)
    requires
        l.no_duplicates(),
        forall|t: int| 0 <= t < l.len() ==> lo <= #[trigger] l[t] < hi,
        forall|i: int| lo <= i < hi ==> #[trigger] f(i) >= 0,
    ensures lsum(l, f) <= isum(lo, hi, f),
{
    let g = |i: int| if l.contains(i) { f(i) } else { 0 };
    assert forall|i: int| lo <= i < hi && #[trigger] g(i) != 0 implies l.contains(i) by {}
    lemma_isum_list(lo, hi, l, g);
    assert forall|k: int| 0 <= k < l.len() implies #[trigger] g(l[k]) == f(l[k]) by {
        assert(l.contains(l[k]));
    }
    lemma_lsum_ext(l, g, f);
    assert forall|i: int| lo <= i < hi implies #[trigger] g(i) <= f(i) by {}
    lemma_isum_le(lo, hi, g, f);
}

/// Telescoping: the sum of the steps of `b` is its total step.
pub proof fn lemma_isum_telescope(lo: int, hi: int, b: spec_fn(int) -> int)
    requires lo <= hi,
    ensures isum(lo, hi, |i: int| b(i + 1) - b(i)) == b(hi) - b(lo),
    decreases hi - lo,
{
    if hi > lo {
        lemma_isum_telescope(lo, hi - 1, b);
    }
}


/// A sum of ones counts the range.
pub proof fn lemma_isum_count(lo: int, hi: int, f: spec_fn(int) -> int)
    requires lo <= hi, forall|i: int| lo <= i < hi ==> #[trigger] f(i) == 1,
    ensures isum(lo, hi, f) == hi - lo,
    decreases hi - lo,
{
    if hi > lo {
        lemma_isum_count(lo, hi - 1, f);
    }
}


/// A sum over `[base, base + n)` read at an offset.
pub proof fn lemma_isum_shift(base: int, n: int, f: spec_fn(int) -> int, g: spec_fn(int) -> int)
    requires 0 <= n, forall|t: int| 0 <= t < n ==> #[trigger] f(base + t) == g(t),
    ensures isum(base, base + n, f) == isum(0, n, g),
    decreases n,
{
    if n > 0 {
        lemma_isum_shift(base, n - 1, f, g);
        assert(f(base + (n - 1)) == g(n - 1));
    }
}

} // verus!
