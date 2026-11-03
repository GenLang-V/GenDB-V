//! The run of an order key in `l_orderkey`, found by search, and the pair checks that make it complete.
//!
//! A *run* of key `k` is a row range `[s, e)` (`run_ok`): every row before `s` has a smaller key (checked on row
//! `s - 1`), row `s` (if any) a key at least `k`, the rows `[s, e)` key `k`, and row `e` (if any) another key. When
//! `l_orderkey` is sorted (`lk_sorted`: every adjacent pair in order), the rows with key `k` are exactly the run, so
//! the run's sums are the key's sums over all rows (`lemma_run_all`). Sortedness is never assumed: the scan tasks
//! check every adjacent pair (`check_pairs`) and the plan concludes it from their results.
//!
//! `run_start` searches forward from a hint `p` in steps of 8 rows (one cache line of keys), falling back to a
//! binary search; any hint is sound, a good one (the end of the previous run) makes it a short forward walk.
use vstd::prelude::*;
use crate::gendb_entry::stores::StoresView;
use crate::agent::cols::*;
use crate::agent::normal::*;
use crate::agent::xcols::*;

verus! {

// ------------------------------------------------------------------------------------------------ specifications

/// The adjacent pairs `(j - 1, j)`, `a <= j < b`, of `keys` are in order.
pub open spec fn pairs_ok(keys: Seq<i64>, a: int, b: int) -> bool {
    forall|j: int| a <= j < b ==> #[trigger] keys[j - 1] <= keys[j]
}

/// `l_orderkey` is sorted (every adjacent pair in order).
pub open spec fn lk_sorted(sv: StoresView) -> bool {
    pairs_ok(lk(sv), 1, n_l(sv))
}

/// `[s, e)` is the run of key `k` in `l_orderkey` (see the module header).
pub open spec fn run_ok(sv: StoresView, k: int, s: int, e: int) -> bool {
    &&& 0 <= s <= e <= n_l(sv)
    &&& s == 0 || (lk(sv)[s - 1] as int) < k
    &&& s == n_l(sv) || (lk(sv)[s] as int) >= k
    &&& forall|y: int| s <= y < e ==> #[trigger] lk(sv)[y] as int == k
    &&& e == n_l(sv) || lk(sv)[e] as int != k
}

// ------------------------------------------------------------------------------------------------ lemmas

/// Sorted keys are monotone between any two rows.
pub proof fn lemma_sorted_mono(sv: StoresView, i: int, j: int)
    requires lk_sorted(sv), 0 <= i <= j < n_l(sv),
    ensures lk(sv)[i] <= lk(sv)[j],
    decreases j - i,
{
    if j > i {
        lemma_sorted_mono(sv, i, j - 1);
        assert(lk(sv)[j - 1] <= lk(sv)[j]);
    }
}

/// On sorted keys, a run holds every row of its key: its sums are the key's sums over all rows.
pub proof fn lemma_run_all(sv: StoresView, k: int, s: int, e: int)
    requires lk_sorted(sv), run_ok(sv, k, s, e),
    ensures
        ksum(sv, k, 0, n_l(sv)) == ksum(sv, k, s, e),
        kcnt(sv, k, 0, n_l(sv)) == kcnt(sv, k, s, e),
        kabs(sv, k, 0, n_l(sv)) == kabs(sv, k, s, e),
{
    let nl = n_l(sv);
    assert forall|i: int| 0 <= i < s implies !#[trigger] lhit(sv, k, i) by {
        lemma_sorted_mono(sv, i, s - 1);
    }
    lemma_k_none(sv, k, 0, s);
    if e < nl {
        // the key after the run is above k
        if e > s {
            assert(lk(sv)[e - 1] <= lk(sv)[e]);
            assert(lk(sv)[e - 1] as int == k);
        }
        assert((lk(sv)[e] as int) > k);
        assert forall|i: int| e <= i < nl implies !#[trigger] lhit(sv, k, i) by {
            lemma_sorted_mono(sv, e, i);
        }
    }
    lemma_k_none(sv, k, e, nl);
    lemma_k_split(sv, k, 0, s, nl);
    lemma_k_split(sv, k, s, e, nl);
}

/// A run's count is at most the key's count over all rows (whatever the order of the keys).
pub proof fn lemma_run_part(sv: StoresView, k: int, s: int, e: int)
    requires 0 <= s <= e <= n_l(sv),
    ensures kcnt(sv, k, s, e) <= kcnt(sv, k, 0, n_l(sv)),
{
    lemma_k_split(sv, k, 0, s, n_l(sv));
    lemma_k_split(sv, k, s, e, n_l(sv));
}

/// Pair checks of adjacent ranges join.
pub proof fn lemma_pairs_join(keys: Seq<i64>, a: int, b: int, c: int)
    requires pairs_ok(keys, a, b), pairs_ok(keys, b, c),
    ensures pairs_ok(keys, a, c),
{
}

// ------------------------------------------------------------------------------------------------ searches

/// The first row `r >= a` whose key is at least `k`, when the keys of `[a, n)` are sorted; any row of `[a, n]`
/// otherwise. The result's neighbours are checked by the caller.
fn lower_bound_from(keys: &[i64], n: usize, k: i64, a: usize) -> (r: usize)
    requires a <= n <= keys@.len(),
    ensures a <= r <= n,
    no_unwind
{
    let mut lo = a;
    let mut hi = n;
    while lo < hi
        invariant a <= lo <= hi <= n, n <= keys@.len(),
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        if keys[mid] < k { lo = mid + 1; } else { hi = mid; }
    }
    lo
}

/// The start of the run of `k`: forward from the hint `p` in steps of 8 rows below `hi`, else a binary search.
/// `None` when the found row does not start a run of `k` (keys out of order).
#[inline(always)]
pub fn run_start(c: &Cols, k: i64, p: usize, hi: usize, Ghost(sv): Ghost<StoresView>) -> (r: Option<usize>)
    requires cols_ok(*c, sv), p <= hi <= c.nl,
    ensures
        r matches Some(s) ==> s <= c.nl
            && (s == 0 || lk(sv)[s - 1] < k)
            && (s == c.nl || lk(sv)[s as int] >= k),
    no_unwind
{
    let lks = c.lk;
    let nl = c.nl;
    let s = if p == 0 || lks[p - 1] < k {
        let mut x = p;
        while hi - x >= 8 && lks[x + 7] < k
            invariant lks@ == lk(sv), nl == lks@.len(), x <= hi <= nl,
            decreases hi - x,
        {
            x = x + 8;
        }
        while x < hi && lks[x] < k
            invariant lks@ == lk(sv), nl == lks@.len(), x <= hi <= nl,
            decreases hi - x,
        {
            x = x + 1;
        }
        if x < hi { x } else { lower_bound_from(lks, nl, k, x) }
    } else {
        lower_bound_from(lks, nl, k, 0)
    };
    // the checks that make `s` a run start whatever the search found
    if (s == 0 || lks[s - 1] < k) && (s == nl || lks[s] >= k) {
        Some(s)
    } else {
        None
    }
}

/// The end of the run of `k` starting at `s`: the first row from `s` with another key.
#[inline(always)]
pub fn run_end(c: &Cols, k: i64, s: usize, Ghost(sv): Ghost<StoresView>) -> (e: usize)
    requires cols_ok(*c, sv), s <= c.nl,
    ensures
        s <= e <= c.nl,
        forall|y: int| s <= y < e ==> #[trigger] lk(sv)[y] == k,
        e == c.nl || lk(sv)[e as int] != k,
    no_unwind
{
    let lks = c.lk;
    let nl = c.nl;
    let mut x = s;
    while x < nl && lks[x] == k
        invariant
            lks@ == lk(sv), nl == lks@.len(), s <= x <= nl,
            forall|y: int| s <= y < x ==> #[trigger] lk(sv)[y] == k,
        decreases nl - x,
    {
        x = x + 1;
    }
    x
}

/// Whether the pairs `(j - 1, j)`, `a <= j < b`, of `l_orderkey` are in order: a count of the out-of-order pairs
/// over the subslice `[a - 1, b)` (no bounds checks, no branch, so it vectorizes).
#[inline(always)]
pub fn check_pairs(c: &Cols, a: usize, b: usize, Ghost(sv): Ghost<StoresView>) -> (r: bool)
    requires cols_ok(*c, sv), 1 <= a, b <= c.nl,
    ensures r ==> pairs_ok(lk(sv), a as int, b as int),
    no_unwind
{
    if a >= b {
        return true;
    }
    let lks = c.lk;
    let (_, tail) = lks.split_at(a - 1);
    let n = b - a;
    let (blk, _) = tail.split_at(n + 1);
    proof {
        assert(blk@ =~= lk(sv).subrange(a - 1, b as int));
    }
    let mut bad: u64 = 0;
    let mut p: usize = 0;
    while p < n
        invariant
            blk@ == lk(sv).subrange(a - 1, b as int), blk@.len() == n + 1, p <= n, bad <= p,
            bad == 0 ==> forall|q: int| 0 <= q < p ==> #[trigger] blk@[q] <= blk@[q + 1],
        decreases n - p,
    {
        let x: u64 = if blk[p] > blk[p + 1] { 1 } else { 0 };
        bad = bad + x;
        p = p + 1;
    }
    proof {
        if bad == 0 {
            assert forall|j: int| a <= j < b implies #[trigger] lk(sv)[j - 1] <= lk(sv)[j] by {
                assert(blk@[j - a] <= blk@[j - a + 1]);
                assert(blk@[j - a] == lk(sv)[j - 1] && blk@[j - a + 1] == lk(sv)[j]);
            }
        }
    }
    bad == 0
}

} // verus!
