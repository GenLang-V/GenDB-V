//! Phase 2 over the customer rows, in worker tasks over row ranges `[a, b)` (`CountTask`): per customer row `i`
//! with key `k`, `c_count(i) = total(k) - likes(k)`, where `total(k)` is the number of orders rows with o_custkey `k`
//! (the length of directory entry `k - kmin` of storage `orders_custidx`, `dtotal`) and `likes(k)` the number of
//! LIKE-matching orders rows with that key (occurrences of `k` in the phase-1 key lists, `cnt_lists`); the task
//! returns the histogram of `c_count` over its rows for values below `H`.
//!
//! Fast-path task: the matches of the keys `ka .. ka + span` are counted into a local array first (customer rows
//! sorted by key make `[ka, ka + span)` the key range of `[a, b)`), so a row costs O(1). The array (one u8 per key)
//! comes from the calling thread with any content and is zeroed here. When `useg`, the task's key range lies in the
//! phase-2 range `bix` and of a reordered list (`parts[t]`) it reads only segment `bix` (`common::partition`). A
//! row outside that range, a count reaching `H`, or a local counter at `u8::MAX` sets `bail`; the caller then uses
//! the general path.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::work::put;
use super::common::partition::*;

use super::scan::grp;

verus! {

/// Histogram size of the fast path.
pub const HIST: usize = 256;

/// Occurrences of `k` in `s[0 .. m]`.
pub open spec fn cnt_seq(s: Seq<i64>, k: int, m: int) -> nat
    decreases m,
{
    if m <= 0 { 0 } else { cnt_seq(s, k, m - 1) + if s[m - 1] == k { 1nat } else { 0nat } }
}

/// Occurrences of `k` in the lists `ls[0 .. t]`.
pub open spec fn cnt_lists(ls: Seq<Vec<i64>>, k: int, t: int) -> nat
    decreases t,
{
    if t <= 0 { 0 } else { cnt_lists(ls, k, t - 1) + cnt_seq(ls[t - 1]@, k, ls[t - 1]@.len() as int) }
}

/// Occurrences of `k` in all the lists.
pub open spec fn likes(ls: Seq<Vec<i64>>, k: int) -> nat {
    cnt_lists(ls, k, ls.len() as int)
}

/// Customer key of row `i` (FOR codes `cc`, bases `cb`, groups of `bs` rows).
pub open spec fn ckey(cc: Seq<u32>, cb: Seq<i64>, bs: int, i: int) -> int {
    cb[i / bs] + cc[i]
}

/// Orders rows with key `k`: the length of its directory entry (0 outside the directory's keys).
pub open spec fn dtotal(offs: Seq<u32>, kmin: int, nk: int, k: int) -> int {
    if kmin <= k < kmin + nk { offs[k - kmin + 1] - offs[k - kmin] } else { 0 }
}

/// c_count of customer row `i`.
pub open spec fn ccount(cc: Seq<u32>, cb: Seq<i64>, bs: int, offs: Seq<u32>, kmin: int, nk: int, ls: Seq<Vec<i64>>, i: int) -> int {
    dtotal(offs, kmin, nk, ckey(cc, cb, bs, i)) - likes(ls, ckey(cc, cb, bs, i))
}

/// Customer rows `a .. m` with c_count `c`.
pub open spec fn hcount(cc: Seq<u32>, cb: Seq<i64>, bs: int, offs: Seq<u32>, kmin: int, nk: int, ls: Seq<Vec<i64>>,
    a: int, m: int, c: int) -> nat
    decreases m - a,
{
    if m <= a {
        0
    } else {
        hcount(cc, cb, bs, offs, kmin, nk, ls, a, m - 1, c)
            + if ccount(cc, cb, bs, offs, kmin, nk, ls, m - 1) == c { 1nat } else { 0nat }
    }
}

/// One phase-2 task over the customer rows `[a, b)`.
pub struct CountTask {
    pub cc: &'static [u32],
    pub cb: &'static [i64],
    pub bs: usize,
    pub n_c: usize,
    pub a: usize,
    pub b: usize,
    pub ka: i64,
    pub span: usize,
    pub local: Vec<u8>,
    pub lists: Arc<Vec<Vec<i64>>>,
    pub offs: &'static [u32],
    pub kmin: i64,
    pub nk: usize,
    pub hist: Vec<u64>,
    /// Segment offsets and reordered flags of the lists, this task's phase-2 range, whether its keys lie in that
    /// range, and the phase-2 key ranges.
    pub boffs: Arc<Vec<Vec<usize>>>,
    pub parts: Arc<Vec<bool>>,
    pub bix: usize,
    pub useg: bool,
    pub lo: Ghost<Seq<i64>>,
    pub hi: Ghost<Seq<i64>>,
}

/// The histogram of the task and whether it bailed out.
pub struct CountOut {
    pub hist: Vec<u64>,
    pub bail: bool,
}

pub open spec fn count_pre(t: CountTask) -> bool {
    &&& t.a <= t.b <= t.n_c
    &&& t.bs >= 1
    &&& t.cc@.len() == t.n_c
    &&& forall|i: int| 0 <= i < t.n_c ==> #[trigger] (i / (t.bs as int)) < t.cb@.len()
    &&& forall|i: int| 0 <= i < t.n_c ==> i64::MIN <= #[trigger] ckey(t.cc@, t.cb@, t.bs as int, i) <= i64::MAX
    &&& t.local@.len() == t.span
    &&& t.boffs@.len() == t.lists@.len()
    &&& t.parts@.len() == t.lists@.len()
    &&& t.useg ==> t.bix < t.lo@.len() && t.lo@[t.bix as int] <= t.ka && t.ka + t.span <= t.hi@[t.bix as int]
    &&& t.useg ==> forall|i: int| 0 <= i < t.lists@.len() && #[trigger] t.parts@[i] ==>
            segs_ok(t.lists@[i]@, t.boffs@[i]@, t.lo@, t.hi@)
    &&& t.hist@.len() == HIST
    &&& forall|c: int| 0 <= c < HIST ==> #[trigger] t.hist@[c] == 0
    &&& t.offs@.len() == t.nk + 1
    &&& forall|e: int| 0 <= e < t.nk ==> #[trigger] t.offs@[e] <= t.offs@[e + 1]
    &&& t.kmin as int + t.nk as int <= i64::MAX
}

/// Unless it bailed: entry `c` of the histogram is the number of rows of `[a, b)` with c_count `c`.
pub open spec fn count_post(t: CountTask, o: CountOut) -> bool {
    &&& o.hist@.len() == HIST
    &&& !o.bail ==> forall|c: int| 0 <= c < HIST ==> #[trigger] o.hist@[c] as int
            == hcount(t.cc@, t.cb@, t.bs as int, t.offs@, t.kmin as int, t.nk as int, t.lists@, t.a as int, t.b as int, c)
    &&& !o.bail ==> forall|i: int| t.a <= i < t.b ==>
            0 <= #[trigger] ccount(t.cc@, t.cb@, t.bs as int, t.offs@, t.kmin as int, t.nk as int, t.lists@, i) < HIST
}

/// A prefix count is a range count from 0.
pub proof fn lemma_cnt_seq_rng(s: Seq<i64>, k: int, m: int)
    requires 0 <= m,
    ensures cnt_seq(s, k, m) == cnt_rng(s, k, 0, m),
    decreases m,
{
    if m > 0 {
        lemma_cnt_seq_rng(s, k, m - 1);
    }
}

/// Of a list cut into segments, segment `bix` counts every key `ka + d` of a key range inside range `bix`.
pub proof fn lemma_seg_keys(l: Seq<i64>, bo: Seq<usize>, lo: Seq<i64>, hi: Seq<i64>, bix: int, ka: int, span: int)
    requires segs_ok(l, bo, lo, hi), 0 <= bix < lo.len(), lo[bix] <= ka, ka + span <= hi[bix],
    ensures
        bo[bix] <= bo[bix + 1] <= l.len(),
        forall|d: int| 0 <= d < span ==> #[trigger] cnt_rng(l, ka + d, bo[bix] as int, bo[bix + 1] as int)
            == cnt_seq(l, ka + d, l.len() as int),
{
    lemma_seg_count(l, bo, lo, hi, bix);
    assert forall|d: int| 0 <= d < span implies #[trigger] cnt_rng(l, ka + d, bo[bix] as int, bo[bix + 1] as int)
        == cnt_seq(l, ka + d, l.len() as int) by {
        lemma_cnt_seq_rng(l, ka + d, l.len() as int);
    }
}

/// A whole list counts every key.
pub proof fn lemma_whole_keys(l: Seq<i64>, ka: int, span: int)
    ensures
        forall|d: int| 0 <= d < span ==> #[trigger] cnt_rng(l, ka + d, 0, l.len() as int) == cnt_seq(l, ka + d, l.len() as int),
{
    assert forall|d: int| 0 <= d < span implies #[trigger] cnt_rng(l, ka + d, 0, l.len() as int)
        == cnt_seq(l, ka + d, l.len() as int) by {
        lemma_cnt_seq_rng(l, ka + d, l.len() as int);
    }
}

/// Occurrences of `k` among the lists `ls[0 .. t]` and the range `ls[t][u0 .. u]`.
pub open spec fn seg_partial(ls: Seq<Vec<i64>>, k: int, t: int, u0: int, u: int) -> int {
    cnt_lists(ls, k, t) + if t < ls.len() { cnt_rng(ls[t]@, k, u0, u) as int } else { 0 }
}

/// Occurrences of `ka + d` among the lists `ls[0 .. t]` and the prefix `ls[t][0 .. u]`.
pub open spec fn partial_cnt(ls: Seq<Vec<i64>>, k: int, t: int, u: int) -> int {
    cnt_lists(ls, k, t) + if t < ls.len() { cnt_seq(ls[t]@, k, u) as int } else { 0 }
}

impl WorkerTask for CountTask {
    type Output = CountOut;

    open spec fn pre(&self) -> bool {
        count_pre(*self)
    }

    open spec fn post(&self, out: CountOut) -> bool {
        count_post(*self, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.a as u64, self.b as u64)
    }

    fn run(self) -> (out: CountOut) {
        let ghost task = self;
        let CountTask { cc, cb, bs, n_c, a, b, ka, span, local, lists, offs, kmin, nk, hist, boffs, parts, bix, useg, lo, hi } = self;
        let ghost (ccv, cbv, bsi, ofv, kmi, nki, lsv) = (cc@, cb@, bs as int, offs@, kmin as int, nk as int, lists@);
        let mut local = local;
        let mut hist = hist;
        // Zero the counters.
        let mut z: usize = 0;
        while z < span
            invariant
                z <= span, local@.len() == span,
                forall|d: int| 0 <= d < z ==> #[trigger] local@[d] == 0,
            decreases span - z,
        {
            put(&mut local, z, 0u8);
            z = z + 1;
        }
        // Matches per key of the range.
        let nl = lists.len();
        let mut t: usize = 0;
        while t < nl
            invariant
                count_pre(task), task.lists@ == lsv, lists@ == lsv, nl == lsv.len(),
                task.span == span, task.ka == ka, task.boffs == boffs, task.parts == parts, task.bix == bix,
                task.useg == useg, task.lo == lo, task.hi == hi,
                t <= nl,
                hist@.len() == HIST,
                local@.len() == span,
                forall|d: int| 0 <= d < span ==> #[trigger] local@[d] as int == cnt_lists(lsv, ka + d, t as int),
            decreases nl - t,
        {
            let l: &Vec<i64> = &lists[t];
            let ghost lt = lsv[t as int]@;
            // Of a reordered list, only this task's segment.
            let (u0, m) = if useg && parts[t] {
                let bo: &Vec<usize> = &boffs[t];
                let bl = bo.len();
                proof {
                    lemma_seg_count(lsv[t as int]@, bo@, lo@, hi@, bix as int);
                    assert(bix + 1 < bl);
                }
                (bo[bix], bo[bix + 1])
            } else {
                (0, l.len())
            };
            proof {
                if useg && parts@[t as int] {
                    lemma_seg_keys(lt, boffs@[t as int]@, lo@, hi@, bix as int, ka as int, span as int);
                } else {
                    lemma_whole_keys(lt, ka as int, span as int);
                }
            }
            let mut u: usize = u0;
            while u < m
                invariant
                    count_pre(task), task.lists@ == lsv, lists@ == lsv, nl == lsv.len(),
                    task.span == span, task.ka == ka,
                    t < nl,
                    hist@.len() == HIST,
                    l@ == lsv[t as int]@, lt == l@,
                    u0 <= u <= m <= l@.len(),
                    forall|d: int| 0 <= d < span ==> #[trigger] cnt_rng(lt, ka + d, u0 as int, m as int)
                        == cnt_seq(lt, ka + d, lt.len() as int),
                    local@.len() == span,
                    forall|d: int| 0 <= d < span ==> #[trigger] local@[d] as int == seg_partial(lsv, ka + d, t as int, u0 as int, u as int),
                decreases m - u,
            {
                let x = l[u];
                if x >= ka && ((x as i128) - (ka as i128)) < span as i128 {
                    let d = ((x as i128) - (ka as i128)) as usize;
                    let v = local[d];
                    if v == u8::MAX {
                        return CountOut { hist, bail: true };
                    }
                    put(&mut local, d, v + 1);
                }
                proof {
                    assert forall|d: int| 0 <= d < span implies #[trigger] local@[d] as int
                        == seg_partial(lsv, ka + d, t as int, u0 as int, u + 1) by {
                        assert(cnt_rng(lt, ka + d, u0 as int, u + 1)
                            == cnt_rng(lt, ka + d, u0 as int, u as int) + if lt[u as int] as int == ka + d { 1nat } else { 0nat });
                    }
                }
                u = u + 1;
            }
            proof {
                assert forall|d: int| 0 <= d < span implies #[trigger] local@[d] as int
                    == cnt_lists(lsv, ka + d, t + 1) by {
                    assert(cnt_lists(lsv, ka + d, t + 1) == cnt_lists(lsv, ka + d, t as int)
                        + cnt_seq(lsv[t as int]@, ka + d, lsv[t as int]@.len() as int));
                    assert(cnt_rng(lt, ka + d, u0 as int, m as int) == cnt_seq(lt, ka + d, lt.len() as int));
                }
            }
            t = t + 1;
        }
        proof {
            assert forall|d: int| 0 <= d < span implies #[trigger] local@[d] as int == likes(lsv, ka + d) by {
                assert(cnt_lists(lsv, ka + d, nl as int) == likes(lsv, ka + d));
            }
        }
        // The histogram of the rows.
        let mut i = a;
        while i < b
            invariant
                count_pre(task), task.lists@ == lsv, lists@ == lsv,
                task.cc == cc, task.cb == cb, task.bs == bs, task.a == a, task.b == b, task.span == span, task.ka == ka,
                task.offs == offs, task.kmin == kmin, task.nk == nk,
                ccv == cc@, cbv == cb@, bsi == bs as int, ofv == offs@, kmi == kmin as int, nki == nk as int,
                local@.len() == span,
                forall|d: int| 0 <= d < span ==> #[trigger] local@[d] as int == likes(lsv, ka + d),
                a <= i <= b,
                hist@.len() == HIST,
                forall|c: int| 0 <= c < HIST ==> #[trigger] hist@[c] as int
                    == hcount(ccv, cbv, bsi, ofv, kmi, nki, lsv, a as int, i as int, c),
                forall|q: int| a <= q < i ==> 0 <= #[trigger] ccount(ccv, cbv, bsi, ofv, kmi, nki, lsv, q) < HIST,
            decreases b - i,
        {
            assert((i as int) / bsi < cbv.len());
            assert(i64::MIN <= ckey(ccv, cbv, bsi, i as int) <= i64::MAX);
            let key = cb[grp(i, bs)] + cc[i] as i64;
            if !(key >= ka && ((key as i128) - (ka as i128)) < span as i128) {
                return CountOut { hist, bail: true };
            }
            let lk = local[((key as i128) - (ka as i128)) as usize] as u64;
            let total: u64 = if key >= kmin && ((key as i128) - (kmin as i128)) < nk as i128 {
                let e = ((key as i128) - (kmin as i128)) as usize;
                assert(ofv[e as int] <= ofv[e + 1]);
                (offs[e + 1] - offs[e]) as u64
            } else {
                0
            };
            assert(total as int == dtotal(ofv, kmi, nki, key as int));
            if lk > total {
                return CountOut { hist, bail: true };
            }
            let c = total - lk;
            if c >= HIST as u64 {
                return CountOut { hist, bail: true };
            }
            assert(c as int == ccount(ccv, cbv, bsi, ofv, kmi, nki, lsv, i as int));
            let h = hist[c as usize];
            proof {
                lemma_hcount_bound(ccv, cbv, bsi, ofv, kmi, nki, lsv, a as int, i as int, c as int);
            }
            let ghost old_hist = hist@;
            put(&mut hist, c as usize, h + 1);
            proof {
                assert forall|c2: int| 0 <= c2 < HIST implies #[trigger] hist@[c2] as int
                    == hcount(ccv, cbv, bsi, ofv, kmi, nki, lsv, a as int, i + 1, c2) by {
                    if c2 != c { assert(hist@[c2] == old_hist[c2]); }
                }
            }
            i = i + 1;
        }
        CountOut { hist, bail: false }
    }
}

/// A histogram count never exceeds the number of rows.
pub proof fn lemma_hcount_bound(cc: Seq<u32>, cb: Seq<i64>, bs: int, offs: Seq<u32>, kmin: int, nk: int, ls: Seq<Vec<i64>>,
    a: int, m: int, c: int)
    requires a <= m,
    ensures hcount(cc, cb, bs, offs, kmin, nk, ls, a, m, c) <= m - a,
    decreases m - a,
{
    if m > a {
        lemma_hcount_bound(cc, cb, bs, offs, kmin, nk, ls, a, m - 1, c);
    }
}

} // verus!
