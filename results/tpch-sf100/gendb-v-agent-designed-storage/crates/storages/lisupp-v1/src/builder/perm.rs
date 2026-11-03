//! Run-time bijection check of a row list: `check_perm32` decides whether a computed list of `u32` row positions
//! is a bijection of `[0, n)` (so an unproved ordering heuristic can produce it).
use vstd::prelude::*;
use crate::stores::lisupp::interface::common::colfmt::*;

verus! {

/// The integer view of a `u32` row list.
pub open spec fn map32(v: Seq<u32>) -> Seq<int> {
    Seq::new(v.len(), |j: int| v[j] as int)
}

/// `true` only when `v` is a bijection of `[0, n)` (`n == v.len()`).
pub fn check_perm32(v: &Vec<u32>) -> (ok: bool)
    ensures
        ok ==> is_perm(map32(v@), v@.len() as int),
{
    let n = v.len();
    let mut seen: Vec<bool> = vec![false; n];
    let mut inv: Vec<usize> = vec![0usize; n];
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
        let p = v[j] as usize;
        if p >= n || seen[p] {
            return false;
        }
        proof {
            assert forall|a: int| 0 <= a < j implies #[trigger] v@[a] != v@[j as int] by {
                assert(seen@[v@[a] as int]);
            }
        }
        seen.set(p, true);
        inv.set(p, j);
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
        let m = map32(v@);
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

} // verus!
