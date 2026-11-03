//! Key order of the stored lineitem rows: a counting sort of the row positions by their key (an unproved
//! heuristic whose indices are checked at run time; `None` when the key range is too wide or a check fails) and
//! the run-time check that a row list is in nondecreasing key order (`check_sorted`, proved).
//!
//! Keys are frame-of-reference values `kb[j / bs] + kc[j]` (`keyidx::fkey`) over uniform blocks of `bs` rows.
use vstd::prelude::*;
use crate::stores::lisupp::interface::common::keyidx::fkey;
use crate::stores::lisupp::interface::common::read::lemma_div_lt;

verus! {

/// Widest key range sorted by counting (2^28 key slots).
pub const MAX_KEY_RANGE: i128 = 268435456;

/// The key column is well shaped: `n` codes, enough bases for `n` rows in blocks of `bs`.
pub open spec fn keys_wf(kc: Seq<u32>, kb: Seq<i64>, bs: int, n: int) -> bool {
    &&& bs >= 1
    &&& kc.len() == n
    &&& kb.len() * bs >= n
}

/// Key of row `j`, decoded exactly in `i128`.
pub fn key_of(kc: &[u32], kb: &[i64], bs: usize, n: usize, j: usize) -> (k: i128)
    requires
        keys_wf(kc@, kb@, bs as int, n as int),
        j < n,
    ensures
        k == fkey(kc@, kb@, bs as int, j as int),
        i64::MIN <= k <= i64::MAX + u32::MAX,
{
    proof {
        lemma_div_lt(j as int, bs as int, kb@.len() as int);
    }
    kb[j / bs] as i128 + kc[j] as i128
}

/// Smallest and largest key of rows `0 .. n` (`n >= 1`).
fn key_bounds(kc: &[u32], kb: &[i64], bs: usize, n: usize) -> (r: (i128, i128))
    requires
        keys_wf(kc@, kb@, bs as int, n as int),
        n >= 1,
    ensures
        i64::MIN <= r.0 <= i64::MAX + u32::MAX,
        i64::MIN <= r.1 <= i64::MAX + u32::MAX,
{
    let mut lo = key_of(kc, kb, bs, n, 0);
    let mut hi = lo;
    let mut j: usize = 1;
    while j < n
        invariant
            keys_wf(kc@, kb@, bs as int, n as int),
            1 <= j <= n,
            i64::MIN <= lo <= i64::MAX + u32::MAX,
            i64::MIN <= hi <= i64::MAX + u32::MAX,
        decreases n - j,
    {
        let k = key_of(kc, kb, bs, n, j);
        if k < lo {
            lo = k;
        }
        if k > hi {
            hi = k;
        }
        j = j + 1;
    }
    (lo, hi)
}

/// The row positions `0 .. n` grouped by key, ascending key, ascending row inside a key (a stable counting sort).
/// Not proved to be sorted or a bijection: the caller checks both. `None` when the key range is wider than
/// `MAX_KEY_RANGE` or a run-time index check fails.
pub fn counting_sort(kc: &[u32], kb: &[i64], bs: usize, n: usize) -> (r: Option<Vec<u32>>)
    requires
        keys_wf(kc@, kb@, bs as int, n as int),
        n <= u32::MAX,
    ensures
        r matches Some(p) ==> p@.len() == n,
{
    if n == 0 {
        return Some(Vec::new());
    }
    let (lo, hi) = key_bounds(kc, kb, bs, n);
    if hi < lo || hi - lo >= MAX_KEY_RANGE {
        return None;
    }
    let range: usize = (hi - lo + 1) as usize;
    // counts[t + 1]: rows of key slot t; then start positions by prefix sums
    let mut counts: Vec<u64> = vec![0u64; range + 1];
    let mut j: usize = 0;
    while j < n
        invariant
            keys_wf(kc@, kb@, bs as int, n as int),
            n <= u32::MAX,
            j <= n,
            counts@.len() == range + 1,
            range as int == hi - lo + 1,
        decreases n - j,
    {
        let k = key_of(kc, kb, bs, n, j);
        if k < lo || k > hi {
            return None;
        }
        let t = (k - lo) as usize;
        let c = counts[t + 1];
        if c >= n as u64 {
            return None;
        }
        counts.set(t + 1, c + 1);
        j = j + 1;
    }
    let mut t: usize = 0;
    while t < range
        invariant
            t <= range,
            counts@.len() == range + 1,
        decreases range - t,
    {
        let s = counts[t + 1] as u128 + counts[t] as u128;
        if s > n as u128 {
            return None;
        }
        counts.set(t + 1, s as u64);
        t = t + 1;
    }
    let mut perm: Vec<u32> = vec![0u32; n];
    let mut j: usize = 0;
    while j < n
        invariant
            keys_wf(kc@, kb@, bs as int, n as int),
            n <= u32::MAX,
            j <= n,
            counts@.len() == range + 1,
            range as int == hi - lo + 1,
            perm@.len() == n,
        decreases n - j,
    {
        let k = key_of(kc, kb, bs, n, j);
        if k < lo || k > hi {
            return None;
        }
        let t = (k - lo) as usize;
        let p = counts[t];
        if p >= n as u64 {
            return None;
        }
        perm.set(p as usize, j as u32);
        counts.set(t, p + 1);
        j = j + 1;
    }
    Some(perm)
}

/// `true` only when the rows listed by `p` have nondecreasing keys.
pub fn check_sorted(kc: &[u32], kb: &[i64], bs: usize, n: usize, p: &Vec<u32>) -> (ok: bool)
    requires
        keys_wf(kc@, kb@, bs as int, n as int),
        p@.len() == n,
    ensures
        ok ==> forall|r: int| 0 <= r < n - 1 ==> (#[trigger] p@[r]) < n && p@[r + 1] < n
            && fkey(kc@, kb@, bs as int, p@[r] as int) <= fkey(kc@, kb@, bs as int, p@[r + 1] as int),
{
    if n <= 1 {
        return true;
    }
    if p[0] as usize >= n {
        return false;
    }
    let mut prev = key_of(kc, kb, bs, n, p[0] as usize);
    let mut r: usize = 1;
    while r < n
        invariant
            keys_wf(kc@, kb@, bs as int, n as int),
            p@.len() == n,
            n >= 2,
            1 <= r <= n,
            p@[r - 1] < n,
            prev == fkey(kc@, kb@, bs as int, p@[r - 1] as int),
            forall|q: int| 0 <= q < r - 1 ==> (#[trigger] p@[q]) < n && p@[q + 1] < n
                && fkey(kc@, kb@, bs as int, p@[q] as int) <= fkey(kc@, kb@, bs as int, p@[q + 1] as int),
        decreases n - r,
    {
        let j = p[r] as usize;
        if j >= n {
            return false;
        }
        let k = key_of(kc, kb, bs, n, j);
        if k < prev {
            return false;
        }
        prev = k;
        r = r + 1;
    }
    true
}

} // verus!
