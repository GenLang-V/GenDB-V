//! The columns Q4 reads, as whole stored parts (`&'static` slices), and their meaning.
//!
//! `lineitem` (`LCols`): `l_orderkey`, `l_commitdate`, `l_receiptdate` of `nl` rows. A row is *late* when its commit
//! date is before its receipt date; key `k` *has* a late row when some row with `l_orderkey = k` is late (the EXISTS
//! subquery of Q4).
//!
//! `orders` (`OCols`): `o_orderkey`, `o_orderdate` (days since 1970-01-01) and `o_orderpriority` (text: offsets and
//! bytes) of `no` rows. An order is in the window when `dlo <= o_orderdate < dhi` (stored days); it qualifies when it is
//! in the window and its key has a late row.
//!
//! Sortedness (`sorted`) of `l_orderkey` is not assumed; it is checked at run time (`pairs_ok` per row range). On sorted
//! keys the rows of key `k` form one run `[s, e)` (`run_ok`), found by a pointer or a binary search, and `has` is decided
//! inside that run (`lemma_run`).
use vstd::prelude::*;
use crate::link::query::{TextView, text_at, text_wf};

verus! {

/// The `lineitem` columns (`nl` rows).
#[derive(Clone, Copy)]
pub struct LCols {
    pub lk: &'static [i64],
    pub cm: &'static [i32],
    pub rc: &'static [i32],
    pub nl: usize,
}

/// The `orders` columns (`no` rows).
#[derive(Clone, Copy)]
pub struct OCols {
    pub okey: &'static [i64],
    pub odate: &'static [i32],
    pub poff: &'static [i64],
    pub pbytes: &'static [u8],
    pub no: usize,
}

pub open spec fn lcols_wf(l: LCols) -> bool {
    &&& l.lk@.len() == l.nl
    &&& l.cm@.len() == l.nl
    &&& l.rc@.len() == l.nl
}

/// The priority text column of `orders`.
pub open spec fn pview(o: OCols) -> TextView {
    TextView { offsets: o.poff@, bytes: o.pbytes@ }
}

pub open spec fn ocols_wf(o: OCols) -> bool {
    &&& o.okey@.len() == o.no
    &&& o.odate@.len() == o.no
    &&& text_wf(pview(o), o.no as int)
}

/// The priority of order row `i` (UTF-8 bytes).
pub open spec fn prio(o: OCols, i: int) -> Seq<u8> {
    text_at(pview(o), i)
}

/// Row `j` of `lineitem` has key `k` and is late.
pub open spec fn hit_at(l: LCols, k: int, j: int) -> bool {
    l.lk@[j] as int == k && l.cm@[j] < l.rc@[j]
}

/// Some row of `[a, b)` has key `k` and is late.
pub open spec fn has_in(l: LCols, k: int, a: int, b: int) -> bool {
    exists|j: int| a <= j < b && #[trigger] hit_at(l, k, j)
}

/// Key `k` has a late `lineitem` row (EXISTS of Q4).
pub open spec fn has(l: LCols, k: int) -> bool {
    has_in(l, k, 0, l.nl as int)
}

/// Rows `j - 1` and `j` are in key order.
pub open spec fn pair_ok(l: LCols, j: int) -> bool {
    l.lk@[j - 1] <= l.lk@[j]
}

/// Every adjacent pair `(j - 1, j)` with `a < j < b` is in key order.
pub open spec fn pairs_ok(l: LCols, a: int, b: int) -> bool {
    forall|j: int| a < j < b ==> #[trigger] pair_ok(l, j)
}

/// `l_orderkey` does not decrease.
pub open spec fn sorted(l: LCols) -> bool {
    pairs_ok(l, 0, l.nl as int)
}

/// `[s, e)` is the run of key `k` at a boundary of the keys below `k`.
pub open spec fn run_ok(l: LCols, k: int, s: int, e: int) -> bool {
    &&& 0 <= s <= e <= l.nl
    &&& (s == 0 || (l.lk@[s - 1] as int) < k)
    &&& (s == l.nl || (l.lk@[s] as int) >= k)
    &&& forall|j: int| s <= j < e ==> #[trigger] l.lk@[j] as int == k
    &&& (e == l.nl || l.lk@[e] as int != k)
}

/// Sorted keys do not decrease between any two rows.
pub proof fn lemma_sorted_mono(l: LCols, a: int, b: int)
    requires lcols_wf(l), sorted(l), 0 <= a <= b < l.nl,
    ensures l.lk@[a] <= l.lk@[b],
    decreases b - a,
{
    if a < b {
        lemma_sorted_mono(l, a, b - 1);
        assert(pair_ok(l, b));
    }
}

/// On sorted keys, key `k` has a late row exactly when its run does.
pub proof fn lemma_run(l: LCols, k: int, s: int, e: int)
    requires lcols_wf(l), sorted(l), run_ok(l, k, s, e),
    ensures has(l, k) == has_in(l, k, s, e),
{
    if has(l, k) {
        let j = choose|j: int| 0 <= j < l.nl && #[trigger] hit_at(l, k, j);
        if j < s {
            lemma_sorted_mono(l, j, s - 1);
        } else if j >= e {
            // lk[e] > k: it differs from k and is not below lk[e - 1] = k (or lk[s] >= k when e == s).
            if e > s {
                assert(pair_ok(l, e));
                assert(l.lk@[e - 1] as int == k);
            }
            lemma_sorted_mono(l, e, j);
        }
        assert(s <= j < e);
    }
}

/// Runs of `[a, b)` and `[b, c)` checked: `[a, c)` checked.
pub proof fn lemma_pairs_join(l: LCols, a: int, b: int, c: int)
    requires pairs_ok(l, a, b + 1), pairs_ok(l, b, c), a <= b,
    ensures pairs_ok(l, a, c),
{
    assert forall|j: int| a < j < c implies #[trigger] pair_ok(l, j) by {
        if j <= b {
        } else {
        }
    }
}

/// First row `s >= a` whose key is at least `k`, for a start `a` below which (at `a - 1`) the key is below `k`:
/// a binary search that keeps `lk[lo - 1] < k` and `lk[hi] >= k` (the result is a run boundary on any data).
#[inline(always)]
pub fn lower_bound(l: &LCols, k: i64, a: usize) -> (s: usize)
    requires
        lcols_wf(*l),
        a <= l.nl,
        a == 0 || l.lk@[a - 1] < k,
    ensures
        a <= s <= l.nl,
        s == 0 || l.lk@[s - 1] < k,
        s == l.nl || l.lk@[s as int] >= k,
    no_unwind
{
    let mut lo = a;
    let mut hi = l.nl;
    while lo < hi
        invariant
            lcols_wf(*l),
            a <= lo <= hi <= l.nl,
            lo == 0 || l.lk@[lo - 1] < k,
            hi == l.nl || l.lk@[hi as int] >= k,
        decreases hi - lo,
    {
        let m = lo + (hi - lo) / 2;
        if l.lk[m] < k {
            lo = m + 1;
        } else {
            hi = m;
        }
    }
    lo
}

/// End of the run of key `k` starting at `s`.
#[inline(always)]
pub fn run_end(l: &LCols, k: i64, s: usize) -> (e: usize)
    requires lcols_wf(*l), s <= l.nl,
    ensures
        s <= e <= l.nl,
        forall|j: int| s <= j < e ==> #[trigger] l.lk@[j] == k,
        e == l.nl || l.lk@[e as int] != k,
    no_unwind
{
    let mut e = s;
    let nl = l.nl;
    while e < nl && l.lk[e] == k
        invariant
            lcols_wf(*l),
            nl == l.nl,
            s <= e <= nl,
            forall|j: int| s <= j < e ==> #[trigger] l.lk@[j] == k,
        decreases nl - e,
    {
        e = e + 1;
    }
    e
}

/// Whether some row of `[s, e)` is late (all its keys are `k`): `has_in(k, s, e)`.
#[inline(always)]
pub fn run_has_late(l: &LCols, Ghost(k): Ghost<int>, s: usize, e: usize) -> (r: bool)
    requires
        lcols_wf(*l),
        s <= e <= l.nl,
        forall|j: int| s <= j < e ==> #[trigger] l.lk@[j] as int == k,
    ensures r == has_in(*l, k, s as int, e as int),
    no_unwind
{
    // Count the late rows without a branch on the loaded dates.
    let mut n: usize = 0;
    let mut j = s;
    while j < e
        invariant
            lcols_wf(*l),
            s <= j <= e <= l.nl,
            n <= j - s,
            (n > 0) == has_in(*l, k, s as int, j as int),
            forall|x: int| s <= x < e ==> #[trigger] l.lk@[x] as int == k,
        decreases e - j,
    {
        proof {
            assert(l.lk@[j as int] as int == k);
            if has_in(*l, k, s as int, j as int) {
                let x = choose|x: int| s <= x < j && #[trigger] hit_at(*l, k, x);
                assert(s <= x < j + 1 && hit_at(*l, k, x));
            }
            if hit_at(*l, k, j as int) {
                assert(s <= j < j + 1);
            }
            if has_in(*l, k, s as int, j + 1) {
                let x = choose|x: int| s <= x < j + 1 && #[trigger] hit_at(*l, k, x);
                if x < j {
                    assert(s <= x < j && hit_at(*l, k, x));
                }
            }
        }
        n = n + if l.cm[j] < l.rc[j] { 1usize } else { 0usize };
        j = j + 1;
    }
    n > 0
}

/// `has(k)` by a scan of every row (the general path, for keys that are not sorted).
pub fn has_scan(l: &LCols, k: i64) -> (r: bool)
    requires lcols_wf(*l),
    ensures r == has(*l, k as int),
{
    let nl = l.nl;
    let mut j: usize = 0;
    while j < nl
        invariant
            lcols_wf(*l),
            nl == l.nl,
            j <= nl,
            !has_in(*l, k as int, 0, j as int),
        decreases nl - j,
    {
        if l.lk[j] == k && l.cm[j] < l.rc[j] {
            proof {
                assert(hit_at(*l, k as int, j as int));
                assert(0 <= j < nl);
            }
            return true;
        }
        proof {
            if has_in(*l, k as int, 0, j + 1) {
                let x = choose|x: int| 0 <= x < j + 1 && #[trigger] hit_at(*l, k as int, x);
                if x < j {
                    assert(0 <= x < j && hit_at(*l, k as int, x));
                }
            }
        }
        j = j + 1;
    }
    false
}

} // verus!
