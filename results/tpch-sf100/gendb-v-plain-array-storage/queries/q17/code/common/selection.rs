//! Selection vectors over row ranges: the rows of `[lo, hi)` satisfying a condition in ascending order
//! (`range_filter`), a further filter of such a list (`seq_filter`), sums over lists and ranges, and the branch-free
//! compaction step that builds them in a preallocated buffer of `u32` offsets (`sel_matches`).
//!
//! Laws: filtering a range filter is the range filter of the conjunction (`lemma_filter_range_filter`); a sum over a
//! range filter is the range sum of the guarded terms (`lemma_sum_range_filter`); range sums of pointwise equal
//! terms are equal (`lemma_range_sum_ext`); range filters stay inside their range (`lemma_range_filter_bounds`).
use vstd::prelude::*;

verus! {

/// Conjunction of two row conditions.
pub open spec fn and_pred(p: spec_fn(int) -> bool, q: spec_fn(int) -> bool) -> spec_fn(int) -> bool {
    |r: int| p(r) && q(r)
}

/// The term `f(r)` where `p(r)` holds, else 0.
pub open spec fn guard(p: spec_fn(int) -> bool, f: spec_fn(int) -> int) -> spec_fn(int) -> int {
    |r: int| if p(r) { f(r) } else { 0 }
}

/// The rows of `[lo, hi)` satisfying `p`, ascending.
pub open spec fn range_filter(lo: int, hi: int, p: spec_fn(int) -> bool) -> Seq<int>
    decreases hi - lo,
{
    if hi <= lo {
        Seq::empty()
    } else {
        let s = range_filter(lo, hi - 1, p);
        if p(hi - 1) { s.push(hi - 1) } else { s }
    }
}

/// The elements of `s` satisfying `q`, in order.
pub open spec fn seq_filter(s: Seq<int>, q: spec_fn(int) -> bool) -> Seq<int>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        let t = seq_filter(s.drop_last(), q);
        if q(s.last()) { t.push(s.last()) } else { t }
    }
}

/// `f` summed over the elements of `s`.
pub open spec fn seq_sum(s: Seq<int>, f: spec_fn(int) -> int) -> int
    decreases s.len(),
{
    if s.len() == 0 { 0 } else { seq_sum(s.drop_last(), f) + f(s.last()) }
}

/// `f` summed over `[lo, hi)`.
pub open spec fn range_sum(lo: int, hi: int, f: spec_fn(int) -> int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { range_sum(lo, hi - 1, f) + f(hi - 1) }
}

/// The first `k` offsets of `sel`, each added to `base`, are the list `s`.
pub open spec fn sel_matches(sel: Seq<u32>, k: int, base: int, s: Seq<int>) -> bool {
    &&& k == s.len()
    &&& k <= sel.len()
    &&& forall|t: int| 0 <= t < k ==> base + (#[trigger] sel[t]) as int == s[t]
}

/// One more element at the end of a filtered list.
pub proof fn lemma_seq_filter_push(s: Seq<int>, x: int, q: spec_fn(int) -> bool)
    ensures seq_filter(s.push(x), q) == if q(x) { seq_filter(s, q).push(x) } else { seq_filter(s, q) },
{
    assert(s.push(x).drop_last() =~= s);
}

/// One more element at the end of a summed list.
pub proof fn lemma_seq_sum_push(s: Seq<int>, x: int, f: spec_fn(int) -> int)
    ensures seq_sum(s.push(x), f) == seq_sum(s, f) + f(x),
{
    assert(s.push(x).drop_last() =~= s);
}

/// A prefix one longer is the shorter prefix and one element.
pub proof fn lemma_take_step(s: Seq<int>, t: int)
    requires 0 <= t < s.len(),
    ensures s.take(t + 1) == s.take(t).push(s[t]),
{
    assert(s.take(t + 1) =~= s.take(t).push(s[t]));
}

/// A range filter lists rows of its range.
pub proof fn lemma_range_filter_bounds(lo: int, hi: int, p: spec_fn(int) -> bool)
    ensures
        forall|t: int| 0 <= t < range_filter(lo, hi, p).len() ==> lo <= #[trigger] range_filter(lo, hi, p)[t] < hi,
    decreases hi - lo,
{
    if hi > lo {
        lemma_range_filter_bounds(lo, hi - 1, p);
        let s = range_filter(lo, hi - 1, p);
        let s2 = range_filter(lo, hi, p);
        assert forall|t: int| 0 <= t < s2.len() implies lo <= #[trigger] s2[t] < hi by {
            if t < s.len() {
                assert(s2[t] == s[t]);
            }
        }
    }
}

/// Filtering a range filter by `q` is the range filter of the conjunction.
pub proof fn lemma_filter_range_filter(lo: int, hi: int, p: spec_fn(int) -> bool, q: spec_fn(int) -> bool)
    ensures seq_filter(range_filter(lo, hi, p), q) == range_filter(lo, hi, and_pred(p, q)),
    decreases hi - lo,
{
    if hi > lo {
        lemma_filter_range_filter(lo, hi - 1, p, q);
        let s = range_filter(lo, hi - 1, p);
        if p(hi - 1) {
            lemma_seq_filter_push(s, hi - 1, q);
        }
    } else {
        assert(range_filter(lo, hi, p) =~= Seq::<int>::empty());
    }
}

/// A sum over a range filter is the range sum of the guarded terms.
pub proof fn lemma_sum_range_filter(lo: int, hi: int, p: spec_fn(int) -> bool, f: spec_fn(int) -> int)
    ensures seq_sum(range_filter(lo, hi, p), f) == range_sum(lo, hi, guard(p, f)),
    decreases hi - lo,
{
    if hi > lo {
        lemma_sum_range_filter(lo, hi - 1, p, f);
        let s = range_filter(lo, hi - 1, p);
        if p(hi - 1) {
            lemma_seq_sum_push(s, hi - 1, f);
        }
    }
}

/// Range sums of terms that agree on the range are equal.
pub proof fn lemma_range_sum_ext(lo: int, hi: int, f: spec_fn(int) -> int, g: spec_fn(int) -> int)
    requires forall|r: int| lo <= r < hi ==> #[trigger] f(r) == g(r),
    ensures range_sum(lo, hi, f) == range_sum(lo, hi, g),
    decreases hi - lo,
{
    if hi > lo {
        lemma_range_sum_ext(lo, hi - 1, f, g);
    }
}

/// Range sums of non-negative terms are non-negative.
pub proof fn lemma_range_sum_nonneg(lo: int, hi: int, f: spec_fn(int) -> int)
    requires forall|r: int| lo <= r < hi ==> #[trigger] f(r) >= 0,
    ensures range_sum(lo, hi, f) >= 0,
    decreases hi - lo,
{
    if hi > lo {
        lemma_range_sum_nonneg(lo, hi - 1, f);
    }
}

/// Compaction step: write `off` at position `k` of the buffer, keep it when `keep`. The listed prefix is unchanged
/// below `k`, and grows by `off` when kept.
pub proof fn lemma_sel_write(sel: Seq<u32>, k: int, base: int, s: Seq<int>, off: u32, keep: bool)
    requires sel_matches(sel, k, base, s), k < sel.len(),
    ensures
        sel_matches(sel.update(k, off), if keep { k + 1 } else { k }, base,
            if keep { s.push(base + off as int) } else { s }),
{
    let sel2 = sel.update(k, off);
    if keep {
        let s2 = s.push(base + off as int);
        assert forall|t: int| 0 <= t < k + 1 implies base + (#[trigger] sel2[t]) as int == s2[t] by {
            if t < k {
                assert(sel2[t] == sel[t]);
            }
        }
    } else {
        assert forall|t: int| 0 <= t < k implies base + (#[trigger] sel2[t]) as int == s[t] by {
            assert(sel2[t] == sel[t]);
        }
    }
}

/// A range filter lists exactly the rows of its range satisfying the condition, ascending, at most one per row.
pub proof fn lemma_range_filter_members(lo: int, hi: int, p: spec_fn(int) -> bool)
    ensures
        range_filter(lo, hi, p).len() <= if hi > lo { hi - lo } else { 0 },
        forall|t: int| 0 <= t < range_filter(lo, hi, p).len() ==>
            lo <= #[trigger] range_filter(lo, hi, p)[t] < hi && p(range_filter(lo, hi, p)[t]),
        forall|t: int, u: int| 0 <= t < u < range_filter(lo, hi, p).len() ==>
            #[trigger] range_filter(lo, hi, p)[t] < #[trigger] range_filter(lo, hi, p)[u],
        forall|r: int| lo <= r < hi && #[trigger] p(r) ==> exists|t: int| 0 <= t < range_filter(lo, hi, p).len()
            && #[trigger] range_filter(lo, hi, p)[t] == r,
    decreases hi - lo,
{
    if hi > lo {
        lemma_range_filter_members(lo, hi - 1, p);
        let s = range_filter(lo, hi - 1, p);
        let s2 = range_filter(lo, hi, p);
        assert forall|t: int| 0 <= t < s2.len() implies lo <= #[trigger] s2[t] < hi && p(s2[t]) by {
            if t < s.len() { assert(s2[t] == s[t]); }
        }
        assert forall|t: int, u: int| 0 <= t < u < s2.len() implies #[trigger] s2[t] < #[trigger] s2[u] by {
            if u < s.len() {
                assert(s2[t] == s[t] && s2[u] == s[u]);
            } else {
                assert(s2[t] == s[t]);
                assert(s2[u] == hi - 1);
            }
        }
        assert forall|r: int| lo <= r < hi && #[trigger] p(r) implies exists|t: int| 0 <= t < s2.len() && #[trigger] s2[t] == r by {
            if r < hi - 1 {
                let t = choose|t: int| 0 <= t < s.len() && #[trigger] s[t] == r;
                assert(s2[t] == s[t]);
            } else {
                assert(s2[s.len() as int] == hi - 1);
            }
        }
    }
}

/// Adjacent range filters concatenate.
pub proof fn lemma_range_filter_concat(lo: int, mid: int, hi: int, p: spec_fn(int) -> bool)
    requires lo <= mid <= hi,
    ensures range_filter(lo, mid, p) + range_filter(mid, hi, p) == range_filter(lo, hi, p),
    decreases hi - mid,
{
    if hi > mid {
        lemma_range_filter_concat(lo, mid, hi - 1, p);
        let a = range_filter(lo, mid, p);
        let b = range_filter(mid, hi - 1, p);
        if p(hi - 1) {
            assert(a + b.push(hi - 1) =~= (a + b).push(hi - 1));
        }
    } else {
        assert(range_filter(mid, hi, p) =~= Seq::<int>::empty());
        assert(range_filter(lo, mid, p) + Seq::<int>::empty() =~= range_filter(lo, mid, p));
    }
}

/// A sum over concatenated lists is the sum of the sums.
pub proof fn lemma_seq_sum_concat(a: Seq<int>, b: Seq<int>, f: spec_fn(int) -> int)
    ensures seq_sum(a + b, f) == seq_sum(a, f) + seq_sum(b, f),
    decreases b.len(),
{
    if b.len() > 0 {
        lemma_seq_sum_concat(a, b.drop_last(), f);
        assert((a + b).drop_last() =~= a + b.drop_last());
        assert((a + b).last() == b.last());
    } else {
        assert(a + b =~= a);
    }
}

/// Range filters by conditions that agree on the range are equal.
pub proof fn lemma_range_filter_ext(lo: int, hi: int, p: spec_fn(int) -> bool, q: spec_fn(int) -> bool)
    requires forall|r: int| lo <= r < hi ==> #[trigger] p(r) == q(r),
    ensures range_filter(lo, hi, p) == range_filter(lo, hi, q),
    decreases hi - lo,
{
    if hi > lo {
        lemma_range_filter_ext(lo, hi - 1, p, q);
    }
}

} // verus!
