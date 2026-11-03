//! Integer keys of rows: the keys `(a[j], b[j], c[j], j)` of rows `j`, sorted with `sort::par_sort` (clustering
//! order, a permutation of the rows), dictionaries of distinct `(a, b)` pairs with a code per row, runs of equal
//! `(k0, k1)` in sorted keys, the first run of every `k0` value (a group directory), and per-run min/max of a
//! column.
use vstd::prelude::*;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use super::sort::{par_sort, Key4, KeyOrder, key4_le, SortOrder, sorted_by, all_ok};
use super::icommon::perm::{ident, is_permutation, lemma_multiset_map, lemma_permutation_facts, position_of};
use super::icommon::runs::{pair_lt, pairs_increasing, group_starts_ok, run_bounds_ok, runs_partition_ok};

verus! {

broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms};

/// The keys of rows `0..n`: `(a[j], b[j], c[j], j)`.
pub open spec fn row_keys(a: Seq<u64>, b: Seq<u64>, c: Seq<u64>) -> Seq<Key4> {
    Seq::new(a.len(), |j: int| Key4 { k0: a[j], k1: b[j], k2: c[j], k3: j as u64 })
}

/// The row (`k3`) of every key.
pub open spec fn key_rows(s: Seq<Key4>) -> Seq<u64> {
    s.map_values(|k: Key4| k.k3)
}

/// The keys of rows `0..n`.
pub fn make_row_keys(a: &Vec<u64>, b: &Vec<u64>, c: &Vec<u64>) -> (r: Vec<Key4>)
    requires a@.len() == b@.len(), a@.len() == c@.len(),
    ensures r@ == row_keys(a@, b@, c@),
{
    let n = a.len();
    let mut r: Vec<Key4> = Vec::with_capacity(n);
    let mut j: usize = 0;
    while j < n
        invariant
            n == a@.len(), a@.len() == b@.len(), a@.len() == c@.len(), j <= n,
            r@ == row_keys(a@, b@, c@).subrange(0, j as int),
        decreases n - j,
    {
        r.push(Key4 { k0: a[j], k1: b[j], k2: c[j], k3: j as u64 });
        j = j + 1;
        proof {
            assert(r@ =~= row_keys(a@, b@, c@).subrange(0, j as int));
        }
    }
    proof {
        assert(r@ =~= row_keys(a@, b@, c@));
    }
    r
}

/// A sequence with the multiset of the row keys holds every row once: its rows are a permutation, and each
/// element is its row's key.
pub proof fn lemma_sorted_keys(s: Seq<Key4>, a: Seq<u64>, b: Seq<u64>, c: Seq<u64>)
    requires
        s.to_multiset() == row_keys(a, b, c).to_multiset(),
        a.len() == b.len(), a.len() == c.len(), a.len() <= u64::MAX,
    ensures
        s.len() == a.len(),
        is_permutation(key_rows(s), a.len()),
        forall|q: int| 0 <= q < s.len() ==> (#[trigger] s[q]).k3 < a.len() && s[q] == row_keys(a, b, c)[s[q].k3 as int],
{
    let keys = row_keys(a, b, c);
    assert(s.len() == s.to_multiset().len());
    assert(keys.len() == keys.to_multiset().len());
    lemma_multiset_map(s, keys, |k: Key4| k.k3);
    assert(keys.map_values(|k: Key4| k.k3) =~= ident(a.len()));
    assert forall|q: int| 0 <= q < s.len() implies (#[trigger] s[q]).k3 < a.len() && s[q] == keys[s[q].k3 as int] by {
        assert(s.contains(s[q]));
        assert(keys.to_multiset().count(s[q]) > 0);
        assert(keys.contains(s[q]));
        let j = choose|j: int| 0 <= j < keys.len() && keys[j] == s[q];
        assert(keys[j].k3 == j as u64);
    }
}

/// The rows' keys sorted lexicographically (clustering order).
pub fn sort_row_keys(a: &Vec<u64>, b: &Vec<u64>, c: &Vec<u64>, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<Vec<Key4>, QueryError>)
    requires a@.len() == b@.len(), a@.len() == c@.len(), 1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(s) ==> sorted_by(KeyOrder {}, s@) && s@.to_multiset() == row_keys(a@, b@, c@).to_multiset(),
        r matches Err(e) ==> e is WorkerFailed,
{
    let keys = make_row_keys(a, b, c);
    let o = KeyOrder {};
    proof {
        assert forall|i: int| 0 <= i < keys@.len() implies o.ok(#[trigger] keys@[i]) by {}
    }
    par_sort(o, keys, workers, dispatch)
}

/// The rows of sorted keys (`k3`), in order.
pub fn rows_of_keys(s: &Vec<Key4>) -> (r: Vec<u64>)
    ensures r@ == key_rows(s@),
{
    let n = s.len();
    let mut r: Vec<u64> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant n == s@.len(), i <= n, r@ == key_rows(s@).subrange(0, i as int),
        decreases n - i,
    {
        r.push(s[i].k3);
        i = i + 1;
        proof {
            assert(r@ =~= key_rows(s@).subrange(0, i as int));
        }
    }
    proof {
        assert(r@ =~= key_rows(s@));
    }
    r
}

/// The `k2` of every key, in order.
pub fn k2_of_keys(s: &Vec<Key4>) -> (r: Vec<u64>)
    ensures r@.len() == s@.len(), forall|i: int| 0 <= i < s@.len() ==> #[trigger] r@[i] == s@[i].k2,
{
    let n = s.len();
    let mut r: Vec<u64> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant n == s@.len(), i <= n, r@.len() == i, forall|t: int| 0 <= t < i ==> #[trigger] r@[t] == s@[t].k2,
        decreases n - i,
    {
        r.push(s[i].k2);
        i = i + 1;
    }
    r
}

// ------------------------------------------------------------------------------------------------ pair dictionary

/// A dictionary of distinct `(a, b)` pairs (strictly increasing) and the pair code of every row.
pub struct PairDict {
    pub first: Vec<u64>,
    pub second: Vec<u64>,
    pub codes: Vec<u64>,
}

/// Dictionary of the distinct `(a[j], b[j])` pairs and every row's pair code.
pub fn build_pair_dict(a: &Vec<u64>, b: &Vec<u64>, Ghost(na): Ghost<int>, Ghost(nb): Ghost<int>, workers: usize,
    dispatch: &mut Dispatch) -> (r: Result<PairDict, QueryError>)
    requires
        a@.len() == b@.len(), 1 <= workers <= MAX_WORKERS,
        forall|j: int| 0 <= j < a@.len() ==> #[trigger] a@[j] < na && b@[j] < nb,
    ensures
        r matches Ok(d) ==> pairs_increasing(d.first@, d.second@) && d.codes@.len() == a@.len()
            && (forall|j: int| 0 <= j < a@.len() ==> (#[trigger] d.codes@[j]) < d.first@.len()
                && d.first@[d.codes@[j] as int] == a@[j] && d.second@[d.codes@[j] as int] == b@[j])
            && (forall|p: int| 0 <= p < d.first@.len() ==> #[trigger] d.first@[p] < na && d.second@[p] < nb),
        r matches Err(e) ==> e is WorkerFailed,
{
    let n = a.len();
    let zeros: Vec<u64> = vec![0u64; n];
    let s = sort_row_keys(a, b, &zeros, workers, dispatch)?;
    proof {
        lemma_sorted_keys(s@, a@, b@, zeros@);
        lemma_permutation_facts(key_rows(s@), n as nat);
    }
    let mut first: Vec<u64> = Vec::new();
    let mut second: Vec<u64> = Vec::new();
    let mut codes: Vec<u64> = vec![0u64; n];
    let mut q: usize = 0;
    while q < n
        invariant
            n == a@.len(), n == b@.len(), n == zeros@.len(), n == s@.len(), q <= n,
            sorted_by(KeyOrder {}, s@),
            forall|t: int| 0 <= t < s@.len() ==> (#[trigger] s@[t]).k3 < n && s@[t] == row_keys(a@, b@, zeros@)[s@[t].k3 as int],
            key_rows(s@).no_duplicates(),
            codes@.len() == n,
            pairs_increasing(first@, second@),
            q > 0 ==> first@.len() > 0 && first@.last() == s@[q - 1].k0 && second@.last() == s@[q - 1].k1,
            q == 0 ==> first@.len() == 0,
            forall|p: int| 0 <= p < q ==> (#[trigger] codes@[s@[p].k3 as int]) < first@.len()
                && first@[codes@[s@[p].k3 as int] as int] == s@[p].k0 && second@[codes@[s@[p].k3 as int] as int] == s@[p].k1,
            forall|j: int| 0 <= j < n ==> #[trigger] a@[j] < na && b@[j] < nb,
            forall|p: int| 0 <= p < first@.len() ==> #[trigger] first@[p] < na && second@[p] < nb,
        decreases n - q,
    {
        let x = s[q];
        let fresh = q == 0 || x.k0 != first[first.len() - 1] || x.k1 != second[second.len() - 1];
        let ghost fb = first@;
        let ghost sb = second@;
        if fresh {
            proof {
                if q > 0 {
                    assert(key4_le(s@[q - 1], s@[q as int]));
                    assert(pair_lt(fb.last(), sb.last(), x.k0, x.k1));
                }
            }
            first.push(x.k0);
            second.push(x.k1);
            proof {
                assert(x == row_keys(a@, b@, zeros@)[x.k3 as int]);
                assert forall|p: int| 0 <= p < first@.len() implies #[trigger] first@[p] < na && second@[p] < nb by {
                    if p == first@.len() - 1 {
                        assert(first@[p] == a@[x.k3 as int] && second@[p] == b@[x.k3 as int]);
                    } else {
                        assert(first@[p] == fb[p] && second@[p] == sb[p]);
                    }
                }
                assert forall|p: int, t: int| 0 <= p < t < first@.len()
                    implies pair_lt(#[trigger] first@[p], second@[p], #[trigger] first@[t], second@[t]) by {
                    if t == first@.len() - 1 && p < t - 1 {
                        assert(pair_lt(fb[p], sb[p], fb.last(), sb.last()));
                    }
                }
            }
        }
        let code = (first.len() - 1) as u64;
        let ghost cb = codes@;
        codes[x.k3 as usize] = code;
        proof {
            assert forall|p: int| 0 <= p < q + 1 implies (#[trigger] codes@[s@[p].k3 as int]) < first@.len()
                && first@[codes@[s@[p].k3 as int] as int] == s@[p].k0 && second@[codes@[s@[p].k3 as int] as int] == s@[p].k1 by {
                if p < q {
                    assert(key_rows(s@)[p] == s@[p].k3 && key_rows(s@)[q as int] == s@[q as int].k3);
                    assert(s@[p].k3 != x.k3);
                    assert(codes@[s@[p].k3 as int] == cb[s@[p].k3 as int]);
                    assert(first@[cb[s@[p].k3 as int] as int] == fb[cb[s@[p].k3 as int] as int]);
                    assert(second@[cb[s@[p].k3 as int] as int] == sb[cb[s@[p].k3 as int] as int]);
                }
            }
        }
        q = q + 1;
    }
    proof {
        assert forall|j: int| 0 <= j < n implies (#[trigger] codes@[j]) < first@.len()
            && first@[codes@[j] as int] == a@[j] && second@[codes@[j] as int] == b@[j] by {
            let p = position_of(key_rows(s@), j);
            assert(key_rows(s@)[p] == s@[p].k3);
            assert(s@[p] == row_keys(a@, b@, zeros@)[j]);
        }
    }
    Ok(PairDict { first, second, codes })
}

// ----------------------------------------------------------------------------------------------------------- runs

/// Runs of equal `(k0, k1)` in sorted keys: run `r` is rows `[start[r], start[r + 1])`, nonempty, with key
/// `(k0[r], k1[r])`; run keys strictly increase.
pub open spec fn runs_ok(s: Seq<Key4>, start: Seq<u64>, k0: Seq<u64>, k1: Seq<u64>) -> bool {
    &&& k1.len() == k0.len()
    &&& runs_partition_ok(start, k0.len() as int, s.len() as int)
    &&& forall|r: int, i: int| 0 <= r < k0.len() && start[r] <= i < start[r + 1]
        ==> (#[trigger] s[i]).k0 == #[trigger] k0[r] && s[i].k1 == k1[r]
    &&& pairs_increasing(k0, k1)
}

/// The runs of sorted keys.
pub struct Runs {
    pub start: Vec<u64>,
    pub k0: Vec<u64>,
    pub k1: Vec<u64>,
}

/// The runs of equal `(k0, k1)` of sorted keys.
#[verifier::spinoff_prover]
pub fn key_runs(s: &Vec<Key4>) -> (r: Runs)
    requires sorted_by(KeyOrder {}, s@),
    ensures runs_ok(s@, r.start@, r.k0@, r.k1@),
{
    let n = s.len();
    let mut start: Vec<u64> = Vec::new();
    let mut k0: Vec<u64> = Vec::new();
    let mut k1: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == s@.len(), i <= n,
            sorted_by(KeyOrder {}, s@),
            k0@.len() == k1@.len(), start@.len() == k0@.len(),
            i == 0 <==> k0@.len() == 0,
            k0@.len() > 0 ==> start@[0] == 0,
            forall|r: int| 0 <= r < k0@.len() ==> #[trigger] start@[r] < i,
            k0@.len() > 0 ==> k0@.last() == s@[i - 1].k0 && k1@.last() == s@[i - 1].k1,
            forall|a: int, b: int| 0 <= a < b < k0@.len() ==> #[trigger] start@[a] < #[trigger] start@[b],
            forall|r: int, t: int| 0 <= r < k0@.len() && start@[r] <= t < (if r + 1 < k0@.len() { start@[r + 1] as int } else { i as int })
                ==> (#[trigger] s@[t]).k0 == #[trigger] k0@[r] && s@[t].k1 == k1@[r],
            pairs_increasing(k0@, k1@),
        decreases n - i,
    {
        let x = s[i];
        let fresh = i == 0 || x.k0 != k0[k0.len() - 1] || x.k1 != k1[k1.len() - 1];
        if fresh {
            let ghost b0 = k0@;
            let ghost b1 = k1@;
            let ghost bs = start@;
            proof {
                if i > 0 {
                    assert(key4_le(s@[i - 1], s@[i as int]));
                    assert(pair_lt(b0.last(), b1.last(), x.k0, x.k1));
                }
            }
            start.push(i as u64);
            k0.push(x.k0);
            k1.push(x.k1);
            proof {
                assert forall|a: int, b: int| 0 <= a < b < k0@.len() implies #[trigger] start@[a] < #[trigger] start@[b] by {
                    assert(start@[a] == bs[a]);
                    if b < k0@.len() - 1 {
                        assert(start@[b] == bs[b]);
                    }
                }
                assert forall|r: int| 0 <= r < k0@.len() implies #[trigger] start@[r] < i + 1 by {
                    if r < k0@.len() - 1 {
                        assert(start@[r] == bs[r]);
                    }
                }
                assert forall|p: int, t: int| 0 <= p < t < k0@.len()
                    implies pair_lt(#[trigger] k0@[p], k1@[p], #[trigger] k0@[t], k1@[t]) by {
                    if t == k0@.len() - 1 && p < t - 1 {
                        assert(pair_lt(b0[p], b1[p], b0.last(), b1.last()));
                    }
                }
                assert forall|r: int, t: int| 0 <= r < k0@.len() && start@[r] <= t < (if r + 1 < k0@.len() { start@[r + 1] as int } else { i + 1 })
                    implies (#[trigger] s@[t]).k0 == #[trigger] k0@[r] && s@[t].k1 == k1@[r] by {
                    if r < k0@.len() - 1 {
                        assert(start@[r] == bs[r]);
                        if r + 1 < b0.len() {
                            assert(start@[r + 1] == bs[r + 1]);
                        }
                    }
                }
            }
        } else {
            proof {
                assert forall|r: int, t: int| 0 <= r < k0@.len() && start@[r] <= t < (if r + 1 < k0@.len() { start@[r + 1] as int } else { i + 1 })
                    implies (#[trigger] s@[t]).k0 == #[trigger] k0@[r] && s@[t].k1 == k1@[r] by {
                    if r == k0@.len() - 1 && t == i {
                        assert(s@[t].k0 == k0@[r]);
                    }
                }
            }
        }
        i = i + 1;
    }
    let ghost bs = start@;
    start.push(n as u64);
    proof {
        assert forall|a: int, b: int| 0 <= a < b <= k0@.len() implies #[trigger] start@[a] < #[trigger] start@[b] by {
            assert(start@[a] == bs[a]);
            if b < k0@.len() {
                assert(start@[b] == bs[b]);
            }
        }
        if k0@.len() == 0 {
            assert(n == 0);
        } else {
            assert(start@[0] == bs[0]);
        }
        assert(start@[k0@.len() as int] == n);
        assert(runs_partition_ok(start@, k0@.len() as int, s@.len() as int));
        assert forall|r: int, t: int| 0 <= r < k0@.len() && start@[r] <= t < start@[r + 1]
            implies (#[trigger] s@[t]).k0 == #[trigger] k0@[r] && s@[t].k1 == k1@[r] by {
            assert(start@[r] == bs[r]);
            if r + 1 < k0@.len() {
                assert(start@[r + 1] == bs[r + 1]);
            }
        }
    }
    Runs { start, k0, k1 }
}

// ------------------------------------------------------------------------------------------------ group directory

/// The first run of every `k0` value `0..=count`, for nondecreasing run keys below `count`.
pub fn group_starts(k0: &Vec<u64>, count: u64) -> (g: Vec<u64>)
    requires
        count < u64::MAX,
        forall|r: int| 0 <= r < k0@.len() ==> #[trigger] k0@[r] < count,
        forall|p: int, q: int| 0 <= p < q < k0@.len() ==> #[trigger] k0@[p] <= #[trigger] k0@[q],
    ensures
        group_starts_ok(g@, k0@, count as int),
{
    let nr = k0.len();
    let mut g: Vec<u64> = Vec::new();
    let mut r: usize = 0;
    let mut u: u64 = 0;
    let total = count + 1;
    while u < total
        invariant
            nr == k0@.len(), r <= nr, u <= total, total == count + 1,
            forall|p: int| 0 <= p < k0@.len() ==> #[trigger] k0@[p] < count,
            forall|p: int, q: int| 0 <= p < q < k0@.len() ==> #[trigger] k0@[p] <= #[trigger] k0@[q],
            g@.len() == u,
            forall|p: int| 0 <= p < r ==> #[trigger] k0@[p] < u,
            forall|w: int| 0 <= w < u ==> #[trigger] g@[w] <= nr,
            forall|w: int, p: int| 0 <= w < u && 0 <= p < nr ==> (p < #[trigger] g@[w] <==> #[trigger] k0@[p] < w),
        decreases total - u,
    {
        while r < nr && k0[r] < u
            invariant
                nr == k0@.len(), r <= nr,
                forall|p: int| 0 <= p < r ==> #[trigger] k0@[p] < u,
            decreases nr - r,
        {
            r = r + 1;
        }
        proof {
            assert forall|p: int| 0 <= p < nr implies (p < r <==> #[trigger] k0@[p] < u) by {
                if p >= r && r < nr {
                    assert(k0@[r as int] >= u);
                    if p > r {
                        assert(k0@[r as int] <= k0@[p]);
                    }
                }
            }
        }
        g.push(r as u64);
        u = u + 1;
    }
    g
}

// ---------------------------------------------------------------------------------------------- per-run min / max

/// Minimum and maximum of `vals[lo..hi]` (nonempty).
fn range_min_max(vals: &Vec<i32>, lo: usize, hi: usize) -> (r: (i32, i32))
    requires lo < hi <= vals@.len(),
    ensures forall|k: int| lo <= k < hi ==> r.0 <= #[trigger] vals@[k] && vals@[k] <= r.1,
{
    let mut mn = vals[lo];
    let mut mx = vals[lo];
    let mut i = lo + 1;
    while i < hi
        invariant
            lo < hi <= vals@.len(), lo < i <= hi,
            forall|k: int| lo <= k < i ==> mn <= #[trigger] vals@[k] && vals@[k] <= mx,
        decreases hi - i,
    {
        let x = vals[i];
        if x < mn { mn = x; }
        if x > mx { mx = x; }
        i = i + 1;
    }
    (mn, mx)
}

/// Minimum and maximum of each run of `vals`.
pub fn run_min_max(vals: &Vec<i32>, start: &Vec<u64>) -> (r: (Vec<i32>, Vec<i32>))
    requires
        runs_partition_ok(start@, start@.len() - 1, vals@.len() as int),
    ensures
        run_bounds_ok(vals@, start@, r.0@, r.1@),
{
    let nr = start.len() - 1;
    let vn = vals.len();
    let mut mins: Vec<i32> = Vec::with_capacity(nr);
    let mut maxs: Vec<i32> = Vec::with_capacity(nr);
    let mut t: usize = 0;
    while t < nr
        invariant
            nr == start@.len() - 1, t <= nr, vn == vals@.len(),
            runs_partition_ok(start@, nr as int, vals@.len() as int),
            mins@.len() == t, maxs@.len() == t,
            forall|w: int, i: int| 0 <= w < t && start@[w] <= i < start@[w + 1]
                ==> #[trigger] mins@[w] <= #[trigger] vals@[i] && vals@[i] <= maxs@[w],
        decreases nr - t,
    {
        assert(start@[t as int] < start@[t + 1] <= start@[nr as int]);
        assert(start@[t as int] < start@[t + 1] <= vn);
        let (mn, mx) = range_min_max(vals, start[t] as usize, start[t + 1] as usize);
        let ghost mb = mins@;
        let ghost xb = maxs@;
        mins.push(mn);
        maxs.push(mx);
        proof {
            assert forall|w: int, i: int| 0 <= w < t + 1 && start@[w] <= i < start@[w + 1]
                implies #[trigger] mins@[w] <= #[trigger] vals@[i] && vals@[i] <= maxs@[w] by {
                if w < t {
                    assert(mins@[w] == mb[w] && maxs@[w] == xb[w]);
                } else {
                    assert(mins@[w] == mn && maxs@[w] == mx);
                }
            }
        }
        t = t + 1;
    }
    proof {
        assert forall|w: int, i: int| 0 <= w < mins@.len() && start@[w] <= i < start@[w + 1]
            implies #[trigger] mins@[w] <= #[trigger] vals@[i] && vals@[i] <= maxs@[w] by {}
    }
    (mins, maxs)
}

} // verus!
