//! Row permutations of `u32` positions: `check_perm` decides at run time whether a vector is a bijection of
//! `[0, n)` (`n` its length), so a computed order is used only once checked.
use vstd::prelude::*;

verus! {

/// Row `r` appears in `v`.
pub open spec fn covered_u32(v: Seq<u32>, r: int) -> bool {
    exists|i: int| 0 <= i < v.len() && v[i] == r
}

/// `v` is a bijection of `[0, n)`.
pub open spec fn perm_view_ok(v: Seq<u32>, n: int) -> bool {
    &&& v.len() == n
    &&& forall|i: int| 0 <= i < n ==> #[trigger] v[i] < n
    &&& forall|a: int, b: int| 0 <= a < n && 0 <= b < n && a != b ==> #[trigger] v[a] != #[trigger] v[b]
    &&& forall|r: int| 0 <= r < n ==> #[trigger] covered_u32(v, r)
}

/// `true` exactly when `v` is a bijection of `[0, v.len())`.
pub fn check_perm(v: &Vec<u32>) -> (ok: bool)
    ensures ok ==> perm_view_ok(v@, v@.len() as int),
{
    let n = v.len();
    if n > 0xffff_ffff {
        return false;
    }
    let mut seen: Vec<bool> = vec![false; n];
    let mut inv: Vec<u32> = vec![0u32; n];
    proof {
        assert forall|i: int| 0 <= i < n implies !#[trigger] seen@[i] by {
            assert(seen@[i] == false);
        }
    }
    let mut j: usize = 0;
    while j < n
        invariant
            n == v@.len(),
            seen@.len() == n,
            inv@.len() == n,
            j <= n,
            n <= 0xffff_ffff,
            forall|a: int| 0 <= a < j ==> (#[trigger] v@[a]) < n && seen@[v@[a] as int],
            forall|i: int| 0 <= i < n && #[trigger] seen@[i] ==> inv@[i] < j && v@[inv@[i] as int] == i,
            forall|a: int, b: int| 0 <= a < j && 0 <= b < j && a != b ==> #[trigger] v@[a] != #[trigger] v@[b],
        decreases n - j,
    {
        let p = v[j];
        if p as usize >= n || seen[p as usize] {
            return false;
        }
        proof {
            assert forall|a: int| 0 <= a < j implies #[trigger] v@[a] != p by {
                assert(seen@[v@[a] as int]);
            }
        }
        seen[p as usize] = true;
        inv[p as usize] = j as u32;
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
        assert forall|k: int| 0 <= k < n implies #[trigger] covered_u32(v@, k) by {
            assert(seen@[k]);
            assert(v@[inv@[k] as int] == k);
        }
    }
    true
}

} // verus!
