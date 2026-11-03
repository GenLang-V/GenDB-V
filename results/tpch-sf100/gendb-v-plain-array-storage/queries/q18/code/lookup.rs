//! Key lookups in the orders and customer key columns: first the row where dbgen puts the key, checked against
//! the column, then a linear search (any layout). The answer is a row holding the key, or the row count when no
//! row holds it.
use vstd::prelude::*;

verus! {

/// Some row of `keys` holds `k`.
pub open spec fn has_key(keys: Seq<i64>, k: i64) -> bool {
    exists|j: int| 0 <= j < keys.len() && keys[j] == k
}

/// Linear search for `k` in `keys` (`n` when absent).
fn search(keys: &'static [i64], n: usize, k: i64) -> (j: usize)
    requires keys@.len() == n,
    ensures j <= n, j < n ==> keys@[j as int] == k, j == n ==> !has_key(keys@, k),
{
    let mut j: usize = 0;
    while j < n
        invariant keys@.len() == n, j <= n, forall|q: int| 0 <= q < j ==> keys@[q] != k,
        decreases n - j,
    {
        if keys[j] == k {
            return j;
        }
        j = j + 1;
    }
    j
}

/// The orders row of order key `k`: dbgen numbers the `i`-th order (from 1) `32 * (i / 8) + i % 8`, so key `k`
/// with `k % 32 < 8` is order `i = 8 * (k / 32) + k % 32`, at row `i - 1`.
pub fn find_order(okey: &'static [i64], no: usize, k: i64) -> (j: usize)
    requires okey@.len() == no,
    ensures j <= no, j < no ==> okey@[j as int] == k, j == no ==> !has_key(okey@, k),
{
    if k > 0 {
        let ku = k as u64;
        let low = ku % 32;
        if low < 8 {
            let i = (ku / 32) * 8 + low;
            if i >= 1 && i - 1 < no as u64 {
                let g = (i - 1) as usize;
                if okey[g] == k {
                    return g;
                }
            }
        }
    }
    search(okey, no, k)
}

/// The customer row of customer key `k`: dbgen numbers the customers `1, 2, ..`, so key `k` sits at row `k - 1`.
pub fn find_cust(ckey: &'static [i64], nc: usize, k: i64) -> (a: usize)
    requires ckey@.len() == nc,
    ensures a <= nc, a < nc ==> ckey@[a as int] == k, a == nc ==> !has_key(ckey@, k),
{
    if k > 0 && ((k - 1) as u64) < nc as u64 {
        let g = (k - 1) as usize;
        if ckey[g] == k {
            return g;
        }
    }
    search(ckey, nc, k)
}

} // verus!
