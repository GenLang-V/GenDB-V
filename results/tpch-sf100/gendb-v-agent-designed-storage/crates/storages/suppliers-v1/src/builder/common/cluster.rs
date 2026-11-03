//! Stored row orders (clustering): a stored-to-canonical row map that stably sorts the canonical rows by a small
//! integer key (counting sort). The sort itself is a heuristic for locality: its output is accepted only when
//! `perm::check_perm` confirms at run time that it is a bijection, and otherwise the identity order is used, so
//! every result is a proved bijection whatever the input.
use vstd::prelude::*;
use crate::builder::iface::common::colfmt::*;
use crate::builder::common::perm::*;

verus! {

/// The identity row map of `n` rows.
pub fn identity_perm(n: usize) -> (v: Vec<u64>)
    ensures
        v@.len() == n,
        is_perm(map_view(v@), n as int),
{
    let mut v: Vec<u64> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            v@.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] v@[j] == j,
        decreases n - i,
    {
        v.push(i as u64);
        i = i + 1;
    }
    proof {
        lemma_identity_perm(n as int);
        assert(map_view(v@) =~= identity_map(n as int));
    }
    v
}

/// A bijection that stably sorts the rows `0 .. key.len()` by `key` (keys below `nkeys`; larger keys sort as
/// `nkeys - 1`), or the identity if that fails.
pub fn counting_perm(key: &Vec<u32>, nkeys: usize) -> (v: Vec<u64>)
    requires 1 <= nkeys < usize::MAX,
    ensures
        v@.len() == key@.len(),
        is_perm(map_view(v@), key@.len() as int),
{
    let n = key.len();
    // counts[k + 1] = rows with key k; then prefix sums give each key's first slot.
    let mut counts: Vec<u64> = vec![0u64; nkeys + 1];
    let mut i: usize = 0;
    while i < n
        invariant
            n == key@.len(),
            1 <= nkeys < usize::MAX,
            counts@.len() == nkeys + 1,
            i <= n,
        decreases n - i,
    {
        let k0 = key[i] as usize;
        let k = if k0 < nkeys { k0 } else { nkeys - 1 };
        let c = counts[k + 1];
        if c < u64::MAX {
            counts[k + 1] = c + 1;
        }
        i = i + 1;
    }
    let mut k: usize = 1;
    while k <= nkeys
        invariant
            1 <= nkeys < usize::MAX,
            counts@.len() == nkeys + 1,
            1 <= k <= nkeys + 1,
        decreases nkeys + 1 - k,
    {
        let a = counts[k - 1];
        let b = counts[k];
        counts[k] = if a <= u64::MAX - b { a + b } else { u64::MAX };
        k = k + 1;
    }
    // Place each row at its key's next free slot.
    let mut v: Vec<u64> = vec![0u64; n];
    let mut i: usize = 0;
    while i < n
        invariant
            n == key@.len(),
            1 <= nkeys < usize::MAX,
            counts@.len() == nkeys + 1,
            v@.len() == n,
            i <= n,
        decreases n - i,
    {
        let k0 = key[i] as usize;
        let k = if k0 < nkeys { k0 } else { nkeys - 1 };
        let pos = counts[k];
        if pos < n as u64 {
            v[pos as usize] = i as u64;
            counts[k] = pos + 1;
        }
        i = i + 1;
    }
    if check_perm(&v) {
        v
    } else {
        identity_perm(n)
    }
}

/// The inverse of a bijection: `inv[v[j]] == j`.
pub fn invert_perm(v: &Vec<u64>) -> (inv: Vec<u64>)
    requires is_perm(map_view(v@), v@.len() as int),
    ensures
        inv@.len() == v@.len(),
        forall|j: int| 0 <= j < v@.len() ==> #[trigger] inv@[v@[j] as int] == j,
        forall|i: int| 0 <= i < v@.len() ==> #[trigger] v@[inv@[i] as int] == i && inv@[i] < v@.len(),
{
    let n = v.len();
    let mut inv: Vec<u64> = vec![0u64; n];
    let ghost m = map_view(v@);
    let mut j: usize = 0;
    while j < n
        invariant
            n == v@.len(),
            m == map_view(v@),
            is_perm(m, n as int),
            inv@.len() == n,
            j <= n,
            forall|a: int| 0 <= a < j ==> #[trigger] inv@[v@[a] as int] == a,
        decreases n - j,
    {
        let p = v[j];
        proof {
            assert(0 <= m[j as int] < n);
            assert forall|a: int| 0 <= a < j implies v@[a] != p by {
                assert(m[a] != m[j as int]);
            }
        }
        inv[p as usize] = j as u64;
        j = j + 1;
    }
    proof {
        assert forall|i: int| 0 <= i < n implies #[trigger] v@[inv@[i] as int] == i && inv@[i] < n by {
            assert(covered(m, i));
            let a = choose|a: int| 0 <= a < m.len() && m[a] == i;
            assert(inv@[v@[a] as int] == a);
        }
    }
    inv
}

} // verus!
