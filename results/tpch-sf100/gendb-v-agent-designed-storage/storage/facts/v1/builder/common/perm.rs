//! Row permutations: `check_perm` decides at run time whether a computed stored-to-canonical row map is a
//! bijection of `[0, n)` (so a fast but unproved ordering heuristic can be used, with the identity as the
//! fallback), and `lemma_sum_perm` reindexes a sum over a bijection.
use vstd::prelude::*;
use crate::builder::iface::common::colfmt::*;

verus! {

/// The integer view of a row map vector.
pub open spec fn map_view(v: Seq<u64>) -> Seq<int> {
    Seq::new(v.len(), |j: int| v[j] as int)
}

/// `true` exactly when `v` is a bijection of `[0, n)` (`n == v.len()`).
pub fn check_perm(v: &Vec<u64>) -> (ok: bool)
    ensures
        ok ==> is_perm(map_view(v@), v@.len() as int),
{
    let n = v.len();
    let mut seen: Vec<bool> = vec![false; n];
    let mut inv: Vec<u64> = vec![0u64; n];
    proof {
        assert forall|i: int| 0 <= i < n implies !#[trigger] seen@[i] by {
            assert(vstd::pervasive::cloned(false, seen@[i]));
        }
    }
    let mut j: usize = 0;
    while j < n
        invariant
            n == v@.len(),
            seen@.len() == n,
            inv@.len() == n,
            j <= n,
            forall|a: int| 0 <= a < j ==> (#[trigger] v@[a]) < n && seen@[v@[a] as int],
            forall|i: int| 0 <= i < n && #[trigger] seen@[i] ==> inv@[i] < j && v@[inv@[i] as int] == i,
            forall|a: int, b: int| 0 <= a < j && 0 <= b < j && a != b ==> #[trigger] v@[a] != #[trigger] v@[b],
        decreases n - j,
    {
        let p = v[j];
        if p >= n as u64 || seen[p as usize] {
            return false;
        }
        proof {
            assert forall|a: int| 0 <= a < j implies #[trigger] v@[a] != p by {
                assert(seen@[v@[a] as int]);
            }
        }
        seen[p as usize] = true;
        inv[p as usize] = j as u64;
        j = j + 1;
    }
    let mut i: usize = 0;
    while i < n
        invariant
            n == v@.len(),
            seen@.len() == n,
            inv@.len() == n,
            i <= n,
            forall|a: int| 0 <= a < n ==> (#[trigger] v@[a]) < n,
            forall|k: int| 0 <= k < n && #[trigger] seen@[k] ==> inv@[k] < n && v@[inv@[k] as int] == k,
            forall|k: int| 0 <= k < i ==> #[trigger] seen@[k],
        decreases n - i,
    {
        if !seen[i] {
            return false;
        }
        i = i + 1;
    }
    proof {
        let m = map_view(v@);
        assert forall|k: int| 0 <= k < n implies #[trigger] covered(m, k) by {
            assert(seen@[k]);
            assert(m[inv@[k] as int] == k);
        }
        assert forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b implies #[trigger] m[a] != #[trigger] m[b] by {
            assert(v@[a] != v@[b]);
        }
    }
    true
}

/// Sum of `f` over the canonical rows `rmap[0 .. k)`.
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

/// A sum over the canonical rows a bijection names is the sum over `[0, n)`.
pub proof fn lemma_sum_perm(rmap: Seq<int>, n: int, f: spec_fn(int) -> int)
    requires
        is_perm(rmap, n),
    ensures
        sum_over(rmap, f, n) == sum_range(f, n),
    decreases n,
{
    if n > 0 {
        assert(covered(rmap, n - 1));
        let j0 = choose|j: int| 0 <= j < rmap.len() && rmap[j] == n - 1;
        lemma_sum_over_remove(rmap, f, n, j0);
        lemma_perm_remove_pub(rmap, n, j0);
        lemma_sum_perm(rmap.remove(j0), n - 1, f);
    }
}

/// Removing the stored row of canonical row `n - 1` leaves a bijection of `[0, n - 1)`.
pub proof fn lemma_perm_remove_pub(rmap: Seq<int>, n: int, j0: int)
    requires
        is_perm(rmap, n),
        0 <= j0 < n,
        rmap[j0] == n - 1,
    ensures
        is_perm(rmap.remove(j0), n - 1),
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

} // verus!
