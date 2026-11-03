//! Phase 2 and the output, on the calling thread.
//! - `run_counts` (fast path): `CountTask`s over customer chunks; their histograms add up to the number of customer
//!   rows per c_count (`cnt(ccount == c)`), or `None` when a chunk bails out;
//! - `general_counts` (any storage flags): the c_count of every customer row, serially;
//! - histogram pairs `(c_count, custdist)` from either (`pairs_ok`: distinct values, exact counts, complete);
//! - `output_rows`: the pairs as rows `[c_count, custdist]`, sorted by custdist DESC, c_count DESC (insertion sort).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::numeric::sign;
use crate::spec::order::*;
use crate::exec::value::*;
use crate::link::query::view_rows;
use super::count::*;
use super::common::partition::*;
use super::glue::*;
use super::run::{bounds_ok, make_bounds, lemma_bounds_le};
use super::sql::order_keys;
use super::group::krow;

verus! {

// ------------------------------------------------------------------------------------------------ fast path

/// c_count of every customer row (fast path), as a function.
pub open spec fn ccf(cc: Seq<u32>, cb: Seq<i64>, bs: int, offs: Seq<u32>, kmin: int, nk: int, ls: Seq<Vec<i64>>) -> spec_fn(int) -> int {
    |i: int| ccount(cc, cb, bs, offs, kmin, nk, ls, i)
}

/// A vector of counts as a function.
pub open spec fn ucf(cv: Seq<u64>) -> spec_fn(int) -> int {
    |i: int| cv[i] as int
}

/// A task's histogram entry is a count.
pub proof fn lemma_hcount_cnt(cc: Seq<u32>, cb: Seq<i64>, bs: int, offs: Seq<u32>, kmin: int, nk: int, ls: Seq<Vec<i64>>,
    a: int, m: int, c: int)
    requires a <= m,
    ensures hcount(cc, cb, bs, offs, kmin, nk, ls, a, m, c) == vcount(ccf(cc, cb, bs, offs, kmin, nk, ls), c, a, m),
    decreases m - a,
{
    if m > a {
        lemma_hcount_cnt(cc, cb, bs, offs, kmin, nk, ls, a, m - 1, c);
    }
}

/// The customer key columns are readable at every row.
pub open spec fn ckeys_ok(cc: Seq<u32>, cb: Seq<i64>, bs: int, n_c: int) -> bool {
    &&& bs >= 1
    &&& cc.len() == n_c
    &&& forall|i: int| 0 <= i < n_c ==> #[trigger] (i / bs) < cb.len()
    &&& forall|i: int| 0 <= i < n_c ==> i64::MIN <= #[trigger] ckey(cc, cb, bs, i) <= i64::MAX
}

/// The directory offsets are nondecreasing.
pub open spec fn dir_ok(offs: Seq<u32>, kmin: int, nk: int) -> bool {
    &&& offs.len() == nk + 1
    &&& forall|e: int| 0 <= e < nk ==> #[trigger] offs[e] <= offs[e + 1]
}

/// The phase-2 key ranges: per customer chunk of `make_bounds(n_c, k)` (the chunks of `run_counts`), the keys from
/// its first to its last row. None when a chunk is empty or the ranges are not ascending and disjoint (then no key
/// list is reordered).
pub fn phase2_ranges(cc: &'static [u32], cb: &'static [i64], bs: usize, n_c: usize, k: usize) -> (r: (Vec<i64>, Vec<i64>))
    requires
        1 <= k <= MAX_WORKERS,
    ensures
        ranges_ok(r.0@, r.1@),
        r.0@.len() <= k,
{
    if bs == 0 || cc.len() < n_c {
        return (Vec::new(), Vec::new());
    }
    let ncb = cb.len();
    let bounds = make_bounds(n_c, k);
    let mut lo: Vec<i64> = Vec::new();
    let mut hi: Vec<i64> = Vec::new();
    let mut t: usize = 0;
    while t < k
        invariant
            1 <= k <= MAX_WORKERS,
            bs >= 1, n_c <= cc@.len(), ncb == cb@.len(),
            bounds_ok(bounds@, k as int, n_c as int),
            t <= k,
            lo@.len() == t,
            ranges_ok(lo@, hi@),
        decreases k - t,
    {
        let a = bounds[t];
        let b = bounds[t + 1];
        proof {
            lemma_bounds_le(bounds@, k as int, n_c as int, t as int);
        }
        if a >= b || a / bs >= ncb || (b - 1) / bs >= ncb {
            return (Vec::new(), Vec::new());
        }
        let k0: i128 = cb[a / bs] as i128 + cc[a] as i128;
        let k1: i128 = cb[(b - 1) / bs] as i128 + cc[b - 1] as i128;
        if k0 < i64::MIN as i128 || k1 >= i64::MAX as i128 || k1 < k0 || (t > 0 && hi[t - 1] as i128 > k0) {
            return (Vec::new(), Vec::new());
        }
        let ghost (lo0, hi0) = (lo@, hi@);
        lo.push(k0 as i64);
        hi.push((k1 + 1) as i64);
        proof {
            assert forall|u: int| 0 <= u < lo@.len() implies #[trigger] lo@[u] <= hi@[u] by {
                if u < t { assert(lo@[u] == lo0[u] && hi@[u] == hi0[u]); }
            }
            assert forall|u: int| 0 <= u < lo@.len() - 1 implies #[trigger] hi@[u] <= lo@[u + 1] by {
                if u + 1 < t { assert(hi@[u] == hi0[u] && lo@[u + 1] == lo0[u + 1]); }
            }
        }
        t = t + 1;
    }
    (lo, hi)
}

/// Phase 2 (fast path): histograms of c_count over `k` customer chunks. `None` when a chunk cannot use the fast
/// path (unsorted keys, a wide key range, a count at least `HIST`): the caller uses the general path.
pub fn run_counts(cc: &'static [u32], cb: &'static [i64], bs: usize, n_c: usize, shared: &Arc<Vec<Vec<i64>>>,
    offs: &'static [u32], kmin: i64, nk: usize, k: usize, dispatch: &mut Dispatch, sb: &Arc<Vec<Vec<usize>>>,
    sp: &Arc<Vec<bool>>, blo: &Vec<i64>, bhi: &Vec<i64>)
    -> (r: Result<Option<Vec<u64>>, WorkerFailure>)
    requires
        1 <= k <= MAX_WORKERS,
        sb@.len() == shared@.len(), sp@.len() == shared@.len(),
        ranges_ok(blo@, bhi@),
        forall|i: int| 0 <= i < shared@.len() && #[trigger] sp@[i] ==> segs_ok(shared@[i]@, sb@[i]@, blo@, bhi@),
        ckeys_ok(cc@, cb@, bs as int, n_c as int),
        dir_ok(offs@, kmin as int, nk as int),
        kmin as int + nk as int <= i64::MAX,
    ensures
        r matches Ok(Some(h)) ==> {
            &&& h@.len() == HIST
            &&& forall|c: int| 0 <= c < HIST ==> #[trigger] h@[c] as int
                    == vcount(ccf(cc@, cb@, bs as int, offs@, kmin as int, nk as int, shared@), c, 0, n_c as int)
            &&& forall|i: int| 0 <= i < n_c ==> 0 <= #[trigger] ccount(cc@, cb@, bs as int, offs@, kmin as int, nk as int, shared@, i) < HIST
        },
{
    let ghost lv = shared@;
    let ghost (ccv, cbv, bsi, ofv, kmi, nki) = (cc@, cb@, bs as int, offs@, kmin as int, nk as int);
    let bounds = make_bounds(n_c, k);
    let mut tasks: Vec<CountTask> = Vec::new();
    let mut t: usize = 0;
    while t < k
        invariant
            1 <= k <= MAX_WORKERS,
            ckeys_ok(ccv, cbv, bsi, n_c as int),
            dir_ok(ofv, kmi, nki),
            kmi + nki <= i64::MAX,
            ccv == cc@, cbv == cb@, bsi == bs as int, ofv == offs@, kmi == kmin as int, nki == nk as int,
            shared@ == lv,
            sb@.len() == lv.len(), sp@.len() == lv.len(),
            ranges_ok(blo@, bhi@),
            forall|i: int| 0 <= i < lv.len() && #[trigger] sp@[i] ==> segs_ok(lv[i]@, sb@[i]@, blo@, bhi@),
            bounds_ok(bounds@, k as int, n_c as int),
            t <= k,
            tasks@.len() == t,
            forall|s: int| 0 <= s < t ==> #[trigger] tasks@[s].pre(),
            forall|s: int| 0 <= s < t ==> (#[trigger] tasks@[s]).cc == cc && tasks@[s].cb == cb && tasks@[s].bs == bs
                && tasks@[s].offs == offs && tasks@[s].kmin == kmin && tasks@[s].nk == nk && tasks@[s].lists@ == lv
                && tasks@[s].a == bounds@[s] && tasks@[s].b == bounds@[s + 1],
        decreases k - t,
    {
        let a = bounds[t];
        let b = bounds[t + 1];
        proof {
            lemma_bounds_le(bounds@, k as int, n_c as int, t as int);
        }
        let mut ka: i64 = 0;
        let mut span: usize = 0;
        if a < b {
            assert((a as int) / bsi < cbv.len());
            assert((b as int - 1) / bsi < cbv.len());
            assert(i64::MIN <= ckey(ccv, cbv, bsi, a as int) <= i64::MAX);
            assert(i64::MIN <= ckey(ccv, cbv, bsi, b - 1) <= i64::MAX);
            let k0 = cb[a / bs] + cc[a] as i64;
            let k1 = cb[(b - 1) / bs] + cc[b - 1] as i64;
            let width: i128 = (k1 as i128) - (k0 as i128) + 1;
            if width < 1 || width > 4 * ((b - a) as i128) + 1024 {
                return Ok(None);
            }
            ka = k0;
            span = width as usize;
        }
        // The task's keys lie in phase-2 range t: it reads only segment t of the reordered lists.
        let useg = t < blo.len() && blo[t] <= ka && (ka as i128) + (span as i128) <= bhi[t] as i128;
        let task = CountTask {
            cc, cb, bs, n_c, a, b, ka, span, local: vec![1u8; span], lists: shared.clone(), offs, kmin, nk,
            hist: vec![0u64; HIST], boffs: sb.clone(), parts: sp.clone(), bix: t, useg, lo: Ghost(blo@), hi: Ghost(bhi@),
        };
        proof {
            assert forall|c: int| 0 <= c < HIST implies #[trigger] task.hist@[c] == 0 by {}
        }
        tasks.push(task);
        t = t + 1;
    }
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(f) => return Err(f),
    };
    let mut total: Vec<u64> = vec![0u64; HIST];
    proof {
        assert forall|c: int| 0 <= c < HIST implies #[trigger] total@[c] as int
            == vcount(ccf(ccv, cbv, bsi, ofv, kmi, nki, lv), c, 0, 0) by {}
    }
    let mut t: usize = 0;
    while t < k
        invariant
            t <= k,
            outs@.len() == k,
            tv.len() == k,
            forall|s: int| 0 <= s < k ==> #[trigger] tv[s].post(outs@[s]),
            forall|s: int| 0 <= s < k ==> (#[trigger] tv[s]).cc == cc && tv[s].cb == cb && tv[s].bs == bs
                && tv[s].offs == offs && tv[s].kmin == kmin && tv[s].nk == nk && tv[s].lists@ == lv
                && tv[s].a == bounds@[s] && tv[s].b == bounds@[s + 1],
            ccv == cc@, cbv == cb@, bsi == bs as int, ofv == offs@, kmi == kmin as int, nki == nk as int,
            bounds_ok(bounds@, k as int, n_c as int),
            total@.len() == HIST,
            forall|c: int| 0 <= c < HIST ==> #[trigger] total@[c] as int
                == vcount(ccf(ccv, cbv, bsi, ofv, kmi, nki, lv), c, 0, bounds@[t as int] as int),
            forall|i: int| 0 <= i < bounds@[t as int] ==> 0 <= #[trigger] ccount(ccv, cbv, bsi, ofv, kmi, nki, lv, i) < HIST,
        decreases k - t,
    {
        proof {
            lemma_bounds_le(bounds@, k as int, n_c as int, t as int);
        }
        let ghost (a, b) = (bounds@[t as int] as int, bounds@[t + 1] as int);
        assert(tv[t as int].post(outs@[t as int]));
        if outs[t].bail {
            return Ok(None);
        }
        assert(outs@[t as int].hist@.len() == HIST);
        let ghost total0 = total@;
        let mut c: usize = 0;
        while c < HIST
            invariant
                c <= HIST,
                t < k,
                outs@.len() == k,
                tv[t as int].post(outs@[t as int]),
                !outs@[t as int].bail,
                outs@[t as int].hist@.len() == HIST,
                total@.len() == HIST,
                forall|c2: int| c <= c2 < HIST ==> #[trigger] total@[c2] == total0[c2],
                forall|c2: int| 0 <= c2 < c ==> #[trigger] total@[c2] as int == total0[c2] + outs@[t as int].hist@[c2],
            decreases HIST - c,
        {
            let v = outs[t].hist[c];
            if total[c] > u64::MAX - v {
                return Ok(None);
            }
            total.set(c, total[c] + v);
            c = c + 1;
        }
        proof {
            assert forall|c2: int| 0 <= c2 < HIST implies #[trigger] total@[c2] as int
                == vcount(ccf(ccv, cbv, bsi, ofv, kmi, nki, lv), c2, 0, b) by {
                lemma_hcount_cnt(ccv, cbv, bsi, ofv, kmi, nki, lv, a, b, c2);
                lemma_cnt_split(veq(ccf(ccv, cbv, bsi, ofv, kmi, nki, lv), c2), 0, a, b);
                assert(outs@[t as int].hist@[c2] as int == hcount(ccv, cbv, bsi, ofv, kmi, nki, lv, a, b, c2));
            }
        }
        t = t + 1;
    }
    Ok(Some(total))
}

// ------------------------------------------------------------------------------------------------ general path

/// Occurrences of `v` in all lists, counted.
fn likes_of(lists: &Vec<Vec<i64>>, v: i64, Ghost(bound): Ghost<int>) -> (r: u64)
    requires likes(lists@, v as int) <= bound <= u64::MAX,
    ensures r as int == likes(lists@, v as int),
{
    let mut total: u64 = 0;
    let mut t: usize = 0;
    while t < lists.len()
        invariant
            t <= lists@.len(),
            likes(lists@, v as int) <= bound <= u64::MAX,
            total as int == cnt_lists(lists@, v as int, t as int),
        decreases lists@.len() - t,
    {
        let l = &lists[t];
        let mut u: usize = 0;
        let ghost base = total as int;
        proof {
            lemma_cnt_lists_mono(lists@, v as int, t as int + 1, lists@.len() as int);
            lemma_cnt_seq_mono(l@, v as int, 0, l@.len() as int);
        }
        while u < l.len()
            invariant
                t < lists@.len(),
                l@ == lists@[t as int]@,
                u <= l@.len(),
                total as int == base + cnt_seq(l@, v as int, u as int),
                base + cnt_seq(l@, v as int, l@.len() as int) <= bound <= u64::MAX,
            decreases l@.len() - u,
        {
            proof { lemma_cnt_seq_mono(l@, v as int, u + 1, l@.len() as int); }
            if l[u] == v {
                total = total + 1;
            }
            u = u + 1;
        }
        t = t + 1;
    }
    total
}

/// Prefix counts over the lists grow with the prefix.
pub proof fn lemma_cnt_lists_mono(ls: Seq<Vec<i64>>, v: int, t1: int, t2: int)
    requires 0 <= t1 <= t2,
    ensures cnt_lists(ls, v, t1) <= cnt_lists(ls, v, t2),
    decreases t2,
{
    if t1 < t2 {
        lemma_cnt_lists_mono(ls, v, t1, t2 - 1);
    }
}

/// Prefix counts over a list grow with the prefix.
pub proof fn lemma_cnt_seq_mono(s: Seq<i64>, v: int, m1: int, m2: int)
    requires 0 <= m1 <= m2,
    ensures cnt_seq(s, v, m1) <= cnt_seq(s, v, m2),
    decreases m2,
{
    if m1 < m2 {
        lemma_cnt_seq_mono(s, v, m1, m2 - 1);
    }
}

/// Rows of `keys[0 .. n]` equal to `v`, counted.
fn key_count(keys: &[i64], n: usize, v: i64) -> (r: u64)
    requires n <= keys@.len(),
    ensures r as int == vcount(kcf(keys@), v as int, 0, n as int),
{
    let mut c: u64 = 0;
    let mut q: usize = 0;
    while q < n
        invariant
            q <= n <= keys@.len(),
            c as int == vcount(kcf(keys@), v as int, 0, q as int),
            c <= q,
        decreases n - q,
    {
        if keys[q] == v {
            c = c + 1;
        }
        q = q + 1;
    }
    c
}

/// The number of orders rows with key `v`, by the directory (mode 1) or by scanning the stored keys.
pub open spec fn tot_ok(dir: bool, offs: Seq<u32>, kmin: int, nk: int, keys: Seq<i64>, n_o: int, tot: spec_fn(int) -> int) -> bool {
    &&& dir ==> dir_ok(offs, kmin, nk) && forall|v: int| #[trigger] dtotal(offs, kmin, nk, v) == tot(v)
    &&& !dir ==> keys.len() == n_o && forall|v: int| #![trigger tot(v)] vcount(kcf(keys), v, 0, n_o) == tot(v)
}

/// The c_count of every customer row: `tot(k) - likes(k)` for its key `k` (general path, serial).
pub fn general_counts(cc: &[u32], cb: &[i64], bs: usize, n_c: usize, lists: &Vec<Vec<i64>>, dir: bool, offs: &[u32],
    kmin: i64, nk: usize, keys: &[i64], n_o: usize, Ghost(tot): Ghost<spec_fn(int) -> int>) -> (cv: Vec<u64>)
    requires
        ckeys_ok(cc@, cb@, bs as int, n_c as int),
        tot_ok(dir, offs@, kmin as int, nk as int, keys@, n_o as int, tot),
        forall|v: int| #![trigger tot(v)] 0 <= likes(lists@, v) <= tot(v) <= n_o,
    ensures
        cv@.len() == n_c,
        forall|i: int| 0 <= i < n_c ==> #[trigger] cv@[i] as int
            == tot(ckey(cc@, cb@, bs as int, i)) - likes(lists@, ckey(cc@, cb@, bs as int, i)),
{
    let mut cv: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    while i < n_c
        invariant
            i <= n_c,
            ckeys_ok(cc@, cb@, bs as int, n_c as int),
            tot_ok(dir, offs@, kmin as int, nk as int, keys@, n_o as int, tot),
            forall|v: int| #![trigger tot(v)] 0 <= likes(lists@, v) <= tot(v) <= n_o,
            cv@.len() == i,
            forall|q: int| 0 <= q < i ==> #[trigger] cv@[q] as int
                == tot(ckey(cc@, cb@, bs as int, q)) - likes(lists@, ckey(cc@, cb@, bs as int, q)),
        decreases n_c - i,
    {
        assert((i as int) / (bs as int) < cb@.len());
        assert(i64::MIN <= ckey(cc@, cb@, bs as int, i as int) <= i64::MAX);
        let key = cb[i / bs] + cc[i] as i64;
        let ghost kv = key as int;
        assert(0 <= likes(lists@, kv) <= tot(kv) <= n_o);
        let total: u64 = if dir {
            if key >= kmin && ((key as i128) - (kmin as i128)) < nk as i128 {
                let e = ((key as i128) - (kmin as i128)) as usize;
                assert(offs@[e as int] <= offs@[e + 1]);
                assert(dtotal(offs@, kmin as int, nk as int, kv) == tot(kv));
                (offs[e + 1] - offs[e]) as u64
            } else {
                assert(dtotal(offs@, kmin as int, nk as int, kv) == tot(kv));
                0
            }
        } else {
            assert(vcount(kcf(keys@), kv, 0, n_o as int) == tot(kv));
            key_count(keys, n_o, key)
        };
        assert(total as int == tot(kv));
        let lk = likes_of(lists, key, Ghost(n_o as int));
        cv.push(total - lk);
        i = i + 1;
    }
    cv
}

// ------------------------------------------------------------------------------------------------ pairs

/// `(c, h)` pairs of the values `f(0 .. n)`: distinct `c`, `h` the exact positive count of `c`, every value present.
pub open spec fn pairs_ok(pairs: Seq<(u64, u64)>, f: spec_fn(int) -> int, n: int) -> bool {
    &&& forall|j: int| 0 <= j < pairs.len() ==> (#[trigger] pairs[j]).1 as int == vcount(f, pairs[j].0 as int, 0, n)
            && pairs[j].1 > 0
    &&& forall|j1: int, j2: int| 0 <= j1 < pairs.len() && 0 <= j2 < pairs.len() && j1 != j2 ==>
            #[trigger] pairs[j1].0 != #[trigger] pairs[j2].0
    &&& forall|c: int| #![trigger vcount(f, c, 0, n)] vcount(f, c, 0, n) > 0 ==>
            exists|j: int| 0 <= j < pairs.len() && pairs[j].0 as int == c
}

/// The pairs of a histogram over `0 .. HIST` (fast path).
pub fn pairs_from_hist(hist: &Vec<u64>, Ghost(f): Ghost<spec_fn(int) -> int>, Ghost(n): Ghost<int>) -> (pairs: Vec<(u64, u64)>)
    requires
        hist@.len() == HIST,
        forall|c: int| 0 <= c < HIST ==> #[trigger] hist@[c] as int == vcount(f, c, 0, n),
        forall|i: int| 0 <= i < n ==> 0 <= #[trigger] f(i) < HIST,
    ensures pairs_ok(pairs@, f, n),
{
    let mut pairs: Vec<(u64, u64)> = Vec::new();
    let mut c: usize = 0;
    while c < HIST
        invariant
            c <= HIST,
            hist@.len() == HIST,
            forall|c2: int| 0 <= c2 < HIST ==> #[trigger] hist@[c2] as int == vcount(f, c2, 0, n),
            forall|j: int| 0 <= j < pairs@.len() ==> (#[trigger] pairs@[j]).1 as int == vcount(f, pairs@[j].0 as int, 0, n)
                && pairs@[j].1 > 0 && pairs@[j].0 < c,
            forall|j1: int, j2: int| 0 <= j1 < pairs@.len() && 0 <= j2 < pairs@.len() && j1 != j2 ==>
                #[trigger] pairs@[j1].0 != #[trigger] pairs@[j2].0,
            forall|c2: int| 0 <= c2 < c && vcount(f, c2, 0, n) > 0 ==>
                exists|j: int| 0 <= j < pairs@.len() && #[trigger] pairs@[j].0 as int == c2,
        decreases HIST - c,
    {
        if hist[c] > 0 {
            let ghost old = pairs@;
            pairs.push((c as u64, hist[c]));
            proof {
                assert(pairs@[old.len() as int].0 as int == c);
                assert forall|j: int| 0 <= j < pairs@.len() implies (#[trigger] pairs@[j]).1 as int == vcount(f, pairs@[j].0 as int, 0, n)
                    && pairs@[j].1 > 0 && pairs@[j].0 < c + 1 by {
                    if j < old.len() { assert(pairs@[j] == old[j]); }
                }
                assert forall|j1: int, j2: int| 0 <= j1 < pairs@.len() && 0 <= j2 < pairs@.len() && j1 != j2 implies
                    #[trigger] pairs@[j1].0 != #[trigger] pairs@[j2].0 by {
                    if j1 < old.len() && j2 < old.len() {
                        assert(pairs@[j1] == old[j1] && pairs@[j2] == old[j2]);
                    } else if j1 < old.len() {
                        assert(pairs@[j1] == old[j1]);
                    } else {
                        assert(pairs@[j2] == old[j2]);
                    }
                }
                assert forall|c2: int| 0 <= c2 < c + 1 && vcount(f, c2, 0, n) > 0 implies
                    exists|j: int| 0 <= j < pairs@.len() && #[trigger] pairs@[j].0 as int == c2 by {
                    if c2 < c {
                        let j = choose|j: int| 0 <= j < old.len() && #[trigger] old[j].0 as int == c2;
                        assert(pairs@[j] == old[j]);
                    } else {
                        assert(pairs@[old.len() as int].0 as int == c2);
                    }
                }
            }
        }
        c = c + 1;
    }
    proof {
        assert forall|c2: int| #![trigger vcount(f, c2, 0, n)] vcount(f, c2, 0, n) > 0 implies
            exists|j: int| 0 <= j < pairs@.len() && pairs@[j].0 as int == c2 by {
            let i = lemma_vcount_pos(f, c2, 0, n);
            assert(0 <= f(i) < HIST);
        }
    }
    pairs
}

/// The pairs of the values `cv[0 .. n]` (general path, linear search per value).
pub fn pairs_from_vals(cv: &Vec<u64>) -> (pairs: Vec<(u64, u64)>)
    ensures pairs_ok(pairs@, ucf(cv@), cv@.len() as int),
{
    let ghost f = ucf(cv@);
    let n = cv.len();
    let mut pairs: Vec<(u64, u64)> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == cv@.len(),
            f == ucf(cv@),
            i <= n,
            forall|j: int| 0 <= j < pairs@.len() ==> (#[trigger] pairs@[j]).1 as int == vcount(f, pairs@[j].0 as int, 0, i as int)
                && pairs@[j].1 > 0,
            forall|j1: int, j2: int| 0 <= j1 < pairs@.len() && 0 <= j2 < pairs@.len() && j1 != j2 ==>
                #[trigger] pairs@[j1].0 != #[trigger] pairs@[j2].0,
            forall|c: int| #![trigger vcount(f, c, 0, i as int)] vcount(f, c, 0, i as int) > 0 ==>
                exists|j: int| 0 <= j < pairs@.len() && pairs@[j].0 as int == c,
            pairs@.len() <= i,
        decreases n - i,
    {
        let v = cv[i];
        let mut j: usize = 0;
        while j < pairs.len() && pairs[j].0 != v
            invariant
                j <= pairs@.len(),
                forall|j2: int| 0 <= j2 < j ==> #[trigger] pairs@[j2].0 != v,
            decreases pairs@.len() - j,
        {
            j = j + 1;
        }
        let ghost old = pairs@;
        proof {
            assert forall|c: int| #![trigger vcount(f, c, 0, i + 1)] true implies
                vcount(f, c, 0, i + 1) == vcount(f, c, 0, i as int) + if f(i as int) == c { 1int } else { 0int } by {}
        }
        if j < pairs.len() {
            let (c0, h0) = pairs[j];
            assert(h0 as int == vcount(f, c0 as int, 0, i as int));
            proof { lemma_cnt_le(veq(f, c0 as int), 0, i as int); }
            pairs.set(j, (c0, h0 + 1));
            proof {
                assert forall|j2: int| 0 <= j2 < pairs@.len() implies (#[trigger] pairs@[j2]).1 as int
                    == vcount(f, pairs@[j2].0 as int, 0, i + 1) && pairs@[j2].1 > 0 by {
                    if j2 != j { assert(pairs@[j2] == old[j2]); }
                }
                assert forall|j1: int, j2: int| 0 <= j1 < pairs@.len() && 0 <= j2 < pairs@.len() && j1 != j2 implies
                    #[trigger] pairs@[j1].0 != #[trigger] pairs@[j2].0 by {
                    assert(pairs@[j1].0 == old[j1].0 && pairs@[j2].0 == old[j2].0);
                }
                assert forall|c: int| #![trigger vcount(f, c, 0, i + 1)] vcount(f, c, 0, i + 1) > 0 implies
                    exists|j2: int| 0 <= j2 < pairs@.len() && pairs@[j2].0 as int == c by {
                    if vcount(f, c, 0, i as int) > 0 {
                        let j2 = choose|j2: int| 0 <= j2 < old.len() && old[j2].0 as int == c;
                        assert(pairs@[j2].0 == old[j2].0);
                    } else {
                        assert(pairs@[j as int].0 as int == c);
                    }
                }
            }
        } else {
            pairs.push((v, 1));
            proof {
                assert forall|j1: int, j2: int| 0 <= j1 < pairs@.len() && 0 <= j2 < pairs@.len() && j1 != j2 implies
                    #[trigger] pairs@[j1].0 != #[trigger] pairs@[j2].0 by {
                    if j1 < old.len() && j2 < old.len() {
                        assert(pairs@[j1] == old[j1] && pairs@[j2] == old[j2]);
                    } else if j1 < old.len() {
                        assert(pairs@[j1] == old[j1]);
                    } else {
                        assert(pairs@[j2] == old[j2]);
                    }
                }
                assert(vcount(f, v as int, 0, i as int) == 0) by {
                    if vcount(f, v as int, 0, i as int) > 0 {
                        let j2 = choose|j2: int| 0 <= j2 < old.len() && old[j2].0 as int == v as int;
                    }
                }
                assert forall|j2: int| 0 <= j2 < pairs@.len() implies (#[trigger] pairs@[j2]).1 as int
                    == vcount(f, pairs@[j2].0 as int, 0, i + 1) && pairs@[j2].1 > 0 by {
                    if j2 < old.len() { assert(pairs@[j2] == old[j2]); }
                }
                assert forall|c: int| #![trigger vcount(f, c, 0, i + 1)] vcount(f, c, 0, i + 1) > 0 implies
                    exists|j2: int| 0 <= j2 < pairs@.len() && pairs@[j2].0 as int == c by {
                    if vcount(f, c, 0, i as int) > 0 {
                        let j2 = choose|j2: int| 0 <= j2 < old.len() && old[j2].0 as int == c;
                        assert(pairs@[j2] == old[j2]);
                    } else {
                        assert(pairs@[old.len() as int].0 as int == c);
                    }
                }
            }
        }
        i = i + 1;
    }
    pairs
}

// ------------------------------------------------------------------------------------------------ output

/// The output row of a pair: `[c_count, custdist]`.
pub open spec fn prow(e: (u64, u64)) -> Row {
    seq![Val::Int(e.0 as int), Val::Int(e.1 as int)]
}

/// `e1` sorts before (or with) `e2`: custdist DESC, then c_count DESC.
pub open spec fn before(e1: (u64, u64), e2: (u64, u64)) -> bool {
    e1.1 > e2.1 || (e1.1 == e2.1 && e1.0 >= e2.0)
}

/// `before(e1, e2)`.
fn before_exec(e1: (u64, u64), e2: (u64, u64)) -> (r: bool)
    ensures r == before(e1, e2),
{
    e1.1 > e2.1 || (e1.1 == e2.1 && e1.0 >= e2.0)
}

/// The ORDER BY comparison of two output rows.
pub proof fn lemma_keys_cmp_rows(e1: (u64, u64), e2: (u64, u64))
    ensures (keys_cmp(order_keys(), prow(e1), prow(e2)) <= 0) == before(e1, e2),
{
    let (r1, r2) = (prow(e1), prow(e2));
    let ks = order_keys();
    let d = ks.drop_first();
    let d2 = d.drop_first();
    assert(d2 =~= Seq::<OrderKey>::empty());
    assert(ks[0] == OrderKey { col: 1, desc: true, nulls_first: true });
    assert(d[0] == OrderKey { col: 0, desc: true, nulls_first: true });
    assert(r1[1] == Val::Int(e1.1 as int) && r2[1] == Val::Int(e2.1 as int));
    assert(r1[0] == Val::Int(e1.0 as int) && r2[0] == Val::Int(e2.0 as int));
    let c1 = key_cmp(ks[0], r1, r2);
    let c2 = key_cmp(d[0], r1, r2);
    assert(compare(Val::Int(e1.1 as int), Val::Int(e2.1 as int)) == Some(sign(e1.1 as int - e2.1 as int)));
    assert(compare(Val::Int(e1.0 as int), Val::Int(e2.0 as int)) == Some(sign(e1.0 as int - e2.0 as int)));
    assert(c1 == -sign(e1.1 as int - e2.1 as int));
    assert(c2 == -sign(e1.0 as int - e2.0 as int));
    assert(keys_cmp(d2, r1, r2) == 0);
    assert(keys_cmp(d, r1, r2) == if c2 != 0 { c2 } else { keys_cmp(d2, r1, r2) });
    assert(keys_cmp(ks, r1, r2) == if c1 != 0 { c1 } else { keys_cmp(d, r1, r2) });
}

/// `before` is transitive.
proof fn lemma_before_trans(a: (u64, u64), b: (u64, u64), c: (u64, u64))
    requires before(a, b), before(b, c),
    ensures before(a, c),
{
}

/// The pairs sorted (custdist DESC, c_count DESC), as output rows.
pub fn output_rows(pairs: &Vec<(u64, u64)>) -> (r: (Vec<Vec<EVal>>, Ghost<Seq<(u64, u64)>>))
    requires
        forall|j: int| 0 <= j < pairs@.len() ==> #[trigger] pairs@[j].0 <= i64::MAX && pairs@[j].1 <= i64::MAX,
        forall|j1: int, j2: int| 0 <= j1 < pairs@.len() && 0 <= j2 < pairs@.len() && j1 != j2 ==>
            #[trigger] pairs@[j1].0 != #[trigger] pairs@[j2].0,
    ensures
        r.1@.len() == pairs@.len(),
        forall|e: (u64, u64)| #[trigger] r.1@.contains(e) <==> pairs@.contains(e),
        forall|j1: int, j2: int| 0 <= j1 < r.1@.len() && 0 <= j2 < r.1@.len() && j1 != j2 ==>
            #[trigger] r.1@[j1].0 != #[trigger] r.1@[j2].0,
        forall|j1: int, j2: int| 0 <= j1 < j2 < r.1@.len() ==> before(#[trigger] r.1@[j1], #[trigger] r.1@[j2]),
        view_rows(r.0@) == r.1@.map_values(|e: (u64, u64)| prow(e)),
{
    broadcast use vstd::seq_lib::group_to_multiset_ensures;
    let n = pairs.len();
    let mut sorted: Vec<(u64, u64)> = Vec::new();
    let mut i: usize = 0;
    proof {
        assert(pairs@.subrange(0, 0) =~= Seq::<(u64, u64)>::empty());
        assert(sorted@ =~= Seq::<(u64, u64)>::empty());
    }
    while i < n
        invariant
            n == pairs@.len(),
            i <= n,
            forall|j1: int, j2: int| 0 <= j1 < n && 0 <= j2 < n && j1 != j2 ==> #[trigger] pairs@[j1].0 != #[trigger] pairs@[j2].0,
            sorted@.len() == i,
            sorted@.to_multiset() == pairs@.subrange(0, i as int).to_multiset(),
            forall|j1: int, j2: int| 0 <= j1 < sorted@.len() && 0 <= j2 < sorted@.len() && j1 != j2 ==>
                #[trigger] sorted@[j1].0 != #[trigger] sorted@[j2].0,
            forall|j1: int, j2: int| 0 <= j1 < j2 < sorted@.len() ==> before(#[trigger] sorted@[j1], #[trigger] sorted@[j2]),
        decreases n - i,
    {
        let e = pairs[i];
        let mut pos: usize = 0;
        while pos < sorted.len() && before_exec(sorted[pos], e)
            invariant
                pos <= sorted@.len(),
                forall|j: int| 0 <= j < pos ==> before(#[trigger] sorted@[j], e),
            decreases sorted@.len() - pos,
        {
            pos = pos + 1;
        }
        let ghost old = sorted@;
        proof {
            // `e`'s value is new among the sorted pairs (they are the pairs `0 .. i`, values distinct).
            assert forall|j: int| 0 <= j < old.len() implies #[trigger] old[j].0 != e.0 by {
                assert(old.contains(old[j]));
                vstd::seq_lib::to_multiset_contains(old, old[j]);
                vstd::seq_lib::to_multiset_contains(pairs@.subrange(0, i as int), old[j]);
                assert(pairs@.subrange(0, i as int).contains(old[j]));
                let q = choose|q: int| 0 <= q < i && #[trigger] pairs@.subrange(0, i as int)[q] == old[j];
                assert(pairs@[q] == old[j]);
            }
        }
        sorted.insert(pos, e);
        proof {
            assert(sorted@ == old.insert(pos as int, e));
            assert(pairs@.subrange(0, i + 1) =~= pairs@.subrange(0, i as int).push(e));
            vstd::seq_lib::to_multiset_insert(old, pos as int, e);
            vstd::seq_lib::to_multiset_build(pairs@.subrange(0, i as int), e);
            assert(sorted@.to_multiset() == pairs@.subrange(0, i + 1).to_multiset());
            assert forall|j1: int, j2: int| 0 <= j1 < sorted@.len() && 0 <= j2 < sorted@.len() && j1 != j2 implies
                #[trigger] sorted@[j1].0 != #[trigger] sorted@[j2].0 by {
                let o1 = if j1 < pos { j1 } else { j1 - 1 };
                let o2 = if j2 < pos { j2 } else { j2 - 1 };
                if j1 != pos && j2 != pos {
                    assert(sorted@[j1] == old[o1] && sorted@[j2] == old[o2]);
                } else if j1 == pos {
                    assert(sorted@[j2] == old[o2]);
                } else {
                    assert(sorted@[j1] == old[o1]);
                }
            }
            if pos < old.len() {
                assert(!before(old[pos as int], e));
                assert(before(e, old[pos as int]));
            }
            assert forall|j1: int, j2: int| 0 <= j1 < j2 < sorted@.len() implies before(#[trigger] sorted@[j1], #[trigger] sorted@[j2]) by {
                if j2 < pos {
                    assert(sorted@[j1] == old[j1] && sorted@[j2] == old[j2]);
                } else if j2 == pos {
                    assert(sorted@[j1] == old[j1]);
                } else if j1 < pos {
                    assert(sorted@[j1] == old[j1] && sorted@[j2] == old[j2 - 1]);
                    assert(before(old[j1], e));
                    if pos as int == j2 - 1 {
                        lemma_before_trans(old[j1], e, old[j2 - 1]);
                    } else {
                        assert(before(old[pos as int], old[j2 - 1]));
                        lemma_before_trans(e, old[pos as int], old[j2 - 1]);
                        lemma_before_trans(old[j1], e, old[j2 - 1]);
                    }
                } else if j1 == pos {
                    assert(sorted@[j2] == old[j2 - 1]);
                    if pos as int != j2 - 1 {
                        assert(before(old[pos as int], old[j2 - 1]));
                        lemma_before_trans(e, old[pos as int], old[j2 - 1]);
                    }
                } else {
                    assert(sorted@[j1] == old[j1 - 1] && sorted@[j2] == old[j2 - 1]);
                }
            }
        }
        i = i + 1;
    }
    proof {
        assert(pairs@.subrange(0, n as int) =~= pairs@);
        assert forall|e: (u64, u64)| #[trigger] sorted@.contains(e) <==> pairs@.contains(e) by {
            vstd::seq_lib::to_multiset_contains(sorted@, e);
            vstd::seq_lib::to_multiset_contains(pairs@, e);
        }
    }
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut q: usize = 0;
    while q < n
        invariant
            q <= n,
            sorted@.len() == n,
            forall|e: (u64, u64)| #[trigger] sorted@.contains(e) <==> pairs@.contains(e),
            forall|j: int| 0 <= j < n ==> #[trigger] pairs@[j].0 <= i64::MAX && pairs@[j].1 <= i64::MAX,
            n == pairs@.len(),
            rows@.len() == q,
            view_rows(rows@) == sorted@.subrange(0, q as int).map_values(|e: (u64, u64)| prow(e)),
        decreases n - q,
    {
        let (c, h) = sorted[q];
        proof {
            assert(sorted@.contains(sorted@[q as int]));
            let j = choose|j: int| 0 <= j < pairs@.len() && pairs@[j] == sorted@[q as int];
            assert(pairs@[j].0 <= i64::MAX && pairs@[j].1 <= i64::MAX);
        }
        let mut row: Vec<EVal> = Vec::new();
        row.push(EVal::Int(c as i64));
        row.push(EVal::Int(h as i64));
        let ghost old_rows = rows@;
        let ghost rv = row;
        rows.push(row);
        proof {
            crate::link::outcome::lemma_view_rows_push(old_rows, rv);
            assert(crate::exec::value::view_row(rv@) =~= prow(sorted@[q as int]));
            assert(sorted@.subrange(0, q + 1).map_values(|e: (u64, u64)| prow(e))
                =~= sorted@.subrange(0, q as int).map_values(|e: (u64, u64)| prow(e)).push(prow(sorted@[q as int])));
        }
        q = q + 1;
    }
    proof {
        assert(sorted@.subrange(0, n as int) =~= sorted@);
    }
    (rows, Ghost(sorted@))
}

} // verus!
