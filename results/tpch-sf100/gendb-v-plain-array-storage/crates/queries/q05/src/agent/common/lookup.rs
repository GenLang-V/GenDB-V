//! Position of a key in an `i64` key column, three ways with one contract (some position holding the key, or
//! `None` exactly when the key does not occur): `find_dense` (when the column is known to be consecutive from its
//! first key, the position is `k - keys[0]`, no read), `find_sorted` (binary search, checked by reading the
//! found position, then a linear scan) and `key_lookup::find_key` (a dense guess, then a linear scan). The result
//! never depends on a guess being right; it is only fast when it is. `DenseKeys` / `dense_pos` are the inlined
//! `i64` form of `find_dense` for a dense column that starts at a non-negative key. All are `no_unwind` (usable in
//! worker tasks; `n` is `keys.len()`, passed in because slice `len` is not `no_unwind`).
use vstd::prelude::*;
use crate::agent::common::key_lookup::find_key;

verus! {

/// The column holds `keys[0] + i` at every position `i`.
pub open spec fn is_dense(keys: Seq<i64>) -> bool {
    forall|i: int| 0 <= i < keys.len() ==> #[trigger] keys[i] as int == keys[0] as int + i
}

/// The lookup contract: `Some(i)` holds `k`; `None` means no position holds `k`.
pub open spec fn found_ok(keys: Seq<i64>, k: i64, r: Option<usize>) -> bool {
    &&& r matches Some(i) ==> i < keys.len() && keys[i as int] == k
    &&& r is None ==> forall|i: int| 0 <= i < keys.len() ==> keys[i] != k
}

/// Lookup in a column that is dense when `dense` holds.
pub fn find_dense(keys: &[i64], n: usize, dense: bool, k: i64) -> (r: Option<usize>)
    requires n == keys@.len(), dense ==> is_dense(keys@),
    ensures found_ok(keys@, k, r),
    no_unwind
{
    if dense {
        if n == 0 {
            return None;
        }
        let g: i128 = k as i128 - keys[0] as i128;
        if 0 <= g && g < n as i128 {
            let i = g as usize;
            proof {
                assert(keys@[i as int] as int == keys@[0] as int + i);
            }
            Some(i)
        } else {
            proof {
                assert forall|i: int| 0 <= i < keys@.len() implies keys@[i] != k by {
                    assert(keys@[i] as int == keys@[0] as int + i);
                }
            }
            None
        }
    } else {
        find_key(keys, n, k)
    }
}

/// The fast form of a dense key column: when `ok`, the column is dense, non-empty, starts at the non-negative key
/// `base` and has `n` rows, so the position of a key `k` is `k - base` with plain `i64` arithmetic.
pub struct DenseKeys {
    pub ok: bool,
    pub base: i64,
    pub n: i64,
}

/// `d` describes `keys` when `d.ok` holds.
pub open spec fn dense_keys_ok(d: DenseKeys, keys: Seq<i64>) -> bool {
    d.ok ==> {
        &&& keys.len() > 0
        &&& is_dense(keys)
        &&& d.base == keys[0]
        &&& d.base >= 0
        &&& d.n as int == keys.len()
        &&& d.n as int <= usize::MAX
    }
}

/// The fast form of `keys` (`ok` only when the column is dense, non-empty, starts at a non-negative key and has
/// at most `i64::MAX` rows).
pub fn dense_keys(keys: &[i64], n: usize, dense: bool) -> (d: DenseKeys)
    requires n == keys@.len(), dense ==> is_dense(keys@),
    ensures dense_keys_ok(d, keys@),
{
    if dense && n > 0 && keys[0] >= 0 && n <= i64::MAX as usize {
        DenseKeys { ok: true, base: keys[0], n: n as i64 }
    } else {
        DenseKeys { ok: false, base: 0, n: 0 }
    }
}

/// Lookup in a column whose fast form `d` is `ok`: `k - base` when it is a position, else `None` (no read).
#[inline(always)]
pub fn dense_pos(d: &DenseKeys, k: i64, Ghost(keys): Ghost<Seq<i64>>) -> (r: Option<usize>)
    requires d.ok, dense_keys_ok(*d, keys),
    ensures found_ok(keys, k, r),
    no_unwind
{
    if k >= d.base && k - d.base < d.n {
        let g = k - d.base;
        let i = g as usize;
        proof {
            assert(0 <= g < d.n);
            assert(i as int == g as int);
            assert(i < keys.len());
            assert(keys[i as int] as int == keys[0] as int + i);
            assert(keys[i as int] == k);
        }
        Some(i)
    } else {
        proof {
            assert forall|i: int| 0 <= i < keys.len() implies keys[i] != k by {
                assert(keys[i] as int == keys[0] as int + i);
            }
        }
        None
    }
}

/// Lookup by binary search (exact when the column ascends), checked, then a linear scan.
pub fn find_sorted(keys: &[i64], n: usize, k: i64) -> (r: Option<usize>)
    requires n == keys@.len(),
    ensures found_ok(keys@, k, r),
    no_unwind
{
    let mut lo: usize = 0;
    let mut hi: usize = n;
    while lo < hi
        invariant lo <= hi <= n, n == keys@.len(),
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        if keys[mid] < k { lo = mid + 1; } else { hi = mid; }
    }
    if lo < n && keys[lo] == k {
        return Some(lo);
    }
    find_key(keys, n, k)
}

/// Decides `is_dense` over the positions `[lo, hi)`: every `keys[i] == base + i`.
pub fn dense_range(keys: &[i64], base: i64, lo: usize, hi: usize) -> (r: bool)
    requires lo <= hi <= keys@.len(),
    ensures r == forall|i: int| lo <= i < hi ==> #[trigger] keys@[i] as int == base as int + i,
    no_unwind
{
    let mut bad: usize = 0;
    let mut i = lo;
    while i < hi
        invariant
            lo <= i <= hi <= keys@.len(),
            bad <= i - lo,
            (bad == 0) == forall|x: int| lo <= x < i ==> #[trigger] keys@[x] as int == base as int + x,
        decreases hi - i,
    {
        let ok = keys[i] as i128 == base as i128 + i as i128;
        bad = bad + if ok { 0usize } else { 1usize };
        i = i + 1;
    }
    bad == 0
}

/// The first position whose key is not below `k` when the column ascends (any position up to `n` otherwise; used
/// only to place range boundaries, never for correctness).
pub fn lower_bound(keys: &[i64], n: usize, k: i64) -> (r: usize)
    requires n == keys@.len(),
    ensures r <= n,
{
    let mut lo: usize = 0;
    let mut hi: usize = n;
    while lo < hi
        invariant lo <= hi <= n, n == keys@.len(),
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        if keys[mid] < k { lo = mid + 1; } else { hi = mid; }
    }
    lo
}

} // verus!
