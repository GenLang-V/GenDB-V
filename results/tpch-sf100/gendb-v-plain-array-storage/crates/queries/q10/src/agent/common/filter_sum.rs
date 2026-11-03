//! Range sums and list sums: a sum over the integers `lo..hi` of terms that vanish outside a set equals the sum over
//! the ascending list of that set's members (`lemma_filter_sum`).
use vstd::prelude::*;

verus! {

/// `Σ_{lo <= j < hi} f(j)`.
pub open spec fn rsum(f: spec_fn(int) -> int, lo: int, hi: int) -> int
    decreases hi - lo,
{
    if hi <= lo { 0 } else { rsum(f, lo, hi - 1) + f(hi - 1) }
}

/// `Σ_{p < m} f(js[p])`.
pub open spec fn lsum_of(f: spec_fn(int) -> int, js: Seq<int>, m: int) -> int
    decreases m,
{
    if m <= 0 { 0 } else { lsum_of(f, js, m - 1) + f(js[m - 1]) }
}

/// The number of list elements below `b` (a prefix of an ascending list).
pub open spec fn n_below(js: Seq<int>, b: int) -> int
    decreases js.len(),
{
    if js.len() == 0 { 0 } else if js.last() < b { js.len() as int } else { n_below(js.drop_last(), b) }
}

proof fn lemma_n_below(js: Seq<int>, b: int)
    requires forall|p: int, q: int| 0 <= p < q < js.len() ==> #[trigger] js[p] < #[trigger] js[q],
    ensures
        0 <= n_below(js, b) <= js.len(),
        forall|p: int| 0 <= p < n_below(js, b) ==> #[trigger] js[p] < b,
        forall|p: int| n_below(js, b) <= p < js.len() ==> #[trigger] js[p] >= b,
    decreases js.len(),
{
    if js.len() > 0 {
        let d = js.drop_last();
        lemma_n_below(d, b);
        if js.last() < b {
            assert forall|p: int| 0 <= p < js.len() implies #[trigger] js[p] < b by {
                if p < js.len() - 1 { assert(js[p] < js[js.len() - 1]); }
            }
        } else {
            assert forall|p: int| n_below(js, b) <= p < js.len() implies #[trigger] js[p] >= b by {
                if p < js.len() - 1 { assert(d[p] == js[p]); }
            }
            assert forall|p: int| 0 <= p < n_below(js, b) implies #[trigger] js[p] < b by {
                assert(d[p] == js[p]);
            }
        }
    }
}

/// The filter law: `rsum(f, lo, hi)` is the list sum of `f` over `js`, the ascending list of the members of `q` in
/// `lo..hi`, when `f` vanishes outside `q`.
pub proof fn lemma_filter_sum(f: spec_fn(int) -> int, q: spec_fn(int) -> bool, js: Seq<int>, lo: int, hi: int)
    requires
        lo <= hi,
        forall|p: int, r: int| 0 <= p < r < js.len() ==> #[trigger] js[p] < #[trigger] js[r],
        forall|p: int| 0 <= p < js.len() ==> lo <= #[trigger] js[p] < hi,
        forall|j: int| lo <= j < hi && q(j) ==> #[trigger] js.contains(j),
        forall|j: int| lo <= j < hi && !q(j) ==> #[trigger] f(j) == 0,
    ensures rsum(f, lo, hi) == lsum_of(f, js, js.len() as int),
{
    lemma_filter_prefix(f, q, js, lo, hi, hi);
    lemma_n_below(js, hi);
    assert(n_below(js, hi) == js.len());
}

/// The filter law up to `b`: `rsum(f, lo, b)` is the list sum over the list elements below `b`.
proof fn lemma_filter_prefix(f: spec_fn(int) -> int, q: spec_fn(int) -> bool, js: Seq<int>, lo: int, hi: int, b: int)
    requires
        lo <= b <= hi,
        forall|p: int, r: int| 0 <= p < r < js.len() ==> #[trigger] js[p] < #[trigger] js[r],
        forall|p: int| 0 <= p < js.len() ==> lo <= #[trigger] js[p] < hi,
        forall|j: int| lo <= j < hi && q(j) ==> #[trigger] js.contains(j),
        forall|j: int| lo <= j < hi && !q(j) ==> #[trigger] f(j) == 0,
    ensures rsum(f, lo, b) == lsum_of(f, js, n_below(js, b)),
    decreases b - lo,
{
    lemma_n_below(js, b);
    if b > lo {
        lemma_filter_prefix(f, q, js, lo, hi, b - 1);
        lemma_n_below(js, b - 1);
        let m = n_below(js, b - 1);
        if js.contains(b - 1) {
            let p = choose|p: int| 0 <= p < js.len() && js[p] == b - 1;
            assert(p >= m);
            if p > m { assert(js[m] < js[p]); }
            assert(p == m);
            assert(n_below(js, b) == m + 1) by {
                if n_below(js, b) > m + 1 { assert(js[m + 1] > js[m]); assert(js[m + 1] < b); }
                if n_below(js, b) < m + 1 { assert(js[m] < b); }
            }
        } else {
            assert(!q(b - 1));
            assert(n_below(js, b) == m) by {
                if n_below(js, b) > m { assert(js[m] < b); assert(js[m] >= b - 1); assert(js[m] == b - 1); }
                if n_below(js, b) < m { let x = n_below(js, b); assert(js[x] < b - 1); }
            }
        }
    } else {
        assert(n_below(js, b) == 0) by {
            if n_below(js, b) > 0 { assert(js[0] < b); }
        }
    }
}

/// Adjacent range sums add.
pub proof fn lemma_rsum_split(f: spec_fn(int) -> int, lo: int, mid: int, hi: int)
    requires lo <= mid <= hi,
    ensures rsum(f, lo, hi) == rsum(f, lo, mid) + rsum(f, mid, hi),
    decreases hi - mid,
{
    if hi > mid {
        lemma_rsum_split(f, lo, mid, hi - 1);
    }
}

/// List sums of pointwise equal terms are equal.
pub proof fn lemma_lsum_ext(f: spec_fn(int) -> int, g: spec_fn(int) -> int, js: Seq<int>, m: int)
    requires 0 <= m <= js.len(), forall|p: int| 0 <= p < m ==> #[trigger] f(js[p]) == g(js[p]),
    ensures lsum_of(f, js, m) == lsum_of(g, js, m),
    decreases m,
{
    if m > 0 {
        lemma_lsum_ext(f, g, js, m - 1);
    }
}

} // verus!
