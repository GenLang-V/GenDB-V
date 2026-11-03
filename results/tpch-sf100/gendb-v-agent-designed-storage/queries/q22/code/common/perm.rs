//! Sums reindexed over a bijection: for a permutation `rmap` of `[0, n)` (`is_bij`), the sum of `f` over the
//! elements `rmap[0 .. n)` is the sum of `f` over `[0, n)` (`lemma_sum_perm`), so an aggregate may visit the rows in
//! any stored order. Proof: remove the position of `n - 1` and recurse (adapted from the admitted builder module
//! `facts::builder::common::perm`).
use vstd::prelude::*;

verus! {

/// `i` is some element of `rmap`.
pub open spec fn covered(rmap: Seq<int>, i: int) -> bool {
    exists|j: int| 0 <= j < rmap.len() && rmap[j] == i
}

/// `rmap` is a bijection of `[0, n)`.
pub open spec fn is_bij(rmap: Seq<int>, n: int) -> bool {
    &&& rmap.len() == n
    &&& forall|j: int| 0 <= j < n ==> 0 <= #[trigger] rmap[j] < n
    &&& forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b ==> #[trigger] rmap[a] != #[trigger] rmap[b]
    &&& forall|i: int| 0 <= i < n ==> #[trigger] covered(rmap, i)
}

/// Sum of `f` over the elements `rmap[0 .. k)`.
pub open spec fn sum_over(rmap: Seq<int>, f: spec_fn(int) -> int, k: int) -> int
    decreases k,
{
    if k <= 0 { 0 } else { sum_over(rmap, f, k - 1) + f(rmap[k - 1]) }
}

/// Sum of `f` over `[0, k)`.
pub open spec fn sum_range(f: spec_fn(int) -> int, k: int) -> int
    decreases k,
{
    if k <= 0 { 0 } else { sum_range(f, k - 1) + f(k - 1) }
}

proof fn lemma_sum_over_ext(a: Seq<int>, b: Seq<int>, f: spec_fn(int) -> int, k: int)
    requires
        0 <= k,
        k <= a.len(),
        k <= b.len(),
        forall|q: int| 0 <= q < k ==> a[q] == b[q],
    ensures
        sum_over(a, f, k) == sum_over(b, f, k),
    decreases k,
{
    if k > 0 {
        lemma_sum_over_ext(a, b, f, k - 1);
    }
}

proof fn lemma_sum_over_remove(rmap: Seq<int>, f: spec_fn(int) -> int, k: int, j0: int)
    requires
        0 <= j0 < k <= rmap.len(),
    ensures
        sum_over(rmap, f, k) == sum_over(rmap.remove(j0), f, k - 1) + f(rmap[j0]),
    decreases k,
{
    if k - 1 == j0 {
        assert forall|q: int| 0 <= q < k - 1 implies rmap.remove(j0)[q] == rmap[q] by {}
        lemma_sum_over_ext(rmap, rmap.remove(j0), f, k - 1);
    } else {
        lemma_sum_over_remove(rmap, f, k - 1, j0);
        assert(rmap.remove(j0)[k - 2] == rmap[k - 1]);
    }
}

/// Removing the position of `n - 1` leaves a bijection of `[0, n - 1)`.
proof fn lemma_bij_remove(rmap: Seq<int>, n: int, j0: int)
    requires
        is_bij(rmap, n),
        0 <= j0 < n,
        rmap[j0] == n - 1,
    ensures
        is_bij(rmap.remove(j0), n - 1),
{
    let r = rmap.remove(j0);
    assert forall|j: int| 0 <= j < n - 1 implies 0 <= #[trigger] r[j] < n - 1 by {
        let k = if j < j0 { j } else { j + 1 };
        assert(r[j] == rmap[k]);
        assert(rmap[k] != rmap[j0]);
    }
    assert forall|a: int, b: int| 0 <= a < n - 1 && 0 <= b < n - 1 && a != b implies #[trigger] r[a] != #[trigger] r[b] by {
        let ka = if a < j0 { a } else { a + 1 };
        let kb = if b < j0 { b } else { b + 1 };
        assert(r[a] == rmap[ka] && r[b] == rmap[kb]);
    }
    assert forall|i: int| 0 <= i < n - 1 implies #[trigger] covered(r, i) by {
        assert(covered(rmap, i));
        let k = choose|k: int| 0 <= k < rmap.len() && rmap[k] == i;
        assert(k != j0);
        let j = if k < j0 { k } else { k - 1 };
        assert(r[j] == i);
    }
}

/// A sum over the elements of a bijection of `[0, n)` is the sum over `[0, n)`.
pub proof fn lemma_sum_perm(rmap: Seq<int>, n: int, f: spec_fn(int) -> int)
    requires
        is_bij(rmap, n),
    ensures
        sum_over(rmap, f, n) == sum_range(f, n),
    decreases n,
{
    if n > 0 {
        assert(covered(rmap, n - 1));
        let j0 = choose|j: int| 0 <= j < rmap.len() && rmap[j] == n - 1;
        lemma_sum_over_remove(rmap, f, n, j0);
        lemma_bij_remove(rmap, n, j0);
        lemma_sum_perm(rmap.remove(j0), n - 1, f);
    }
}

} // verus!
