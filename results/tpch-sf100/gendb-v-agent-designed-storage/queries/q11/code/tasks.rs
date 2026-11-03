//! The parallel pieces of the plan: row ranges aligned to ps_partkey changes (`bounds_ok`, `task_bounds`), one
//! scan task per range (`ScanTask`: `scan::scan_range`, then the range's groups sorted by SUM descending,
//! `scan_sort`); `filt` names the groups whose SUM exceeds a bound, in order. With aligned ranges over sorted rows, the rows
//! of a key lie in one range, so a range's group SUM is the whole table's (`lemma_outside`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::{WorkerTask, MAX_WORKERS};
use super::tables::*;
use super::rows::*;
use super::groups::*;
use super::scan::*;
use super::bitmap::bm_ok;
use super::common::msort::{desc, seg, msort};

verus! {

// ------------------------------------------------------------------------------------------------ ranges

/// Task ranges `b[k] .. b[k + 1]` cover `0 .. n` in order; an inner bound never splits a key's rows.
pub open spec fn bounds_ok(t: Tabs, b: Seq<usize>, nt: int, n: int) -> bool {
    &&& b.len() == nt + 1
    &&& b[0] == 0
    &&& b[nt] == n
    &&& forall|k: int| 0 <= k < nt ==> #[trigger] b[k] <= b[k + 1]
    &&& forall|k: int| 0 < k < nt ==> #[trigger] b[k] == 0 || b[k] == n || rkey(t, b[k] - 1) != rkey(t, b[k] as int)
}

/// A key's rows in an aligned range `lo .. hi` of sorted rows: none outside it.
pub proof fn lemma_outside(t: Tabs, name: Seq<u8>, n: int, lo: int, hi: int, k: int)
    requires
        sorted_rows(t, 0, n), 0 <= lo <= hi <= n,
        kcnt(t, name, k, lo, hi) > 0,
        lo == 0 || lo == n || rkey(t, lo - 1) != rkey(t, lo),
        hi == 0 || hi == n || rkey(t, hi - 1) != rkey(t, hi),
    ensures
        ksum(t, name, k, 0, n) == ksum(t, name, k, lo, hi),
        kcnt(t, name, k, 0, n) == kcnt(t, name, k, lo, hi),
        kcnt(t, name, k, 0, lo) == 0,
        rkey(t, lo) <= k,
        hi < n ==> k < rkey(t, hi),
{
    lemma_kwit(t, name, k, lo, hi);
    let r = choose|r: int| lo <= r < hi && rowq(t, name, r) && #[trigger] rkey(t, r) == k;
    assert(rkey(t, lo) <= rkey(t, r));
    if lo > 0 {
        assert(rkey(t, lo - 1) <= rkey(t, lo));
        assert forall|x: int| 0 <= x < lo implies #[trigger] rkey(t, x) != k by {
            assert(rkey(t, x) <= rkey(t, lo - 1));
        }
    }
    lemma_knone(t, name, k, 0, lo);
    if hi < n {
        assert(rkey(t, hi - 1) <= rkey(t, hi));
        assert(rkey(t, r) <= rkey(t, hi - 1));
        assert forall|x: int| hi <= x < n implies #[trigger] rkey(t, x) != k by {
            assert(rkey(t, hi) <= rkey(t, x));
        }
    }
    lemma_knone(t, name, k, hi, n);
    lemma_split(t, name, k, 0, lo, n);
    lemma_split(t, name, k, lo, hi, n);
}

/// The key of row `r` from the handles.
pub fn row_key(c: &PSCols, r: usize, Ghost(t): Ghost<Tabs>) -> (k: i64)
    requires pscols_ok(*c, t.ps), super::nf::tabs_typed(t), r < c.n,
    ensures k as int == rkey(t, r as int),
{
    assert(ps_row_ok(*c, t.ps[r as int], r as int));
    proof { lemma_grp_bound(c.n as int, c.bs as int, c.ng as int, r as int); }
    c.key_b[r / c.bs] + c.key_c[r] as i64
}

/// `nt` ranges of about `n / nt` rows each, each inner bound moved up to the next change of ps_partkey.
pub fn task_bounds(c: &PSCols, nt: usize, Ghost(t): Ghost<Tabs>) -> (b: Vec<usize>)
    requires pscols_ok(*c, t.ps), super::nf::tabs_typed(t), 1 <= nt <= MAX_WORKERS,
    ensures bounds_ok(t, b@, nt as int, c.n as int),
{
    let n = c.n;
    let mut b: Vec<usize> = Vec::new();
    b.push(0);
    let mut k: usize = 1;
    while k <= nt
        invariant
            pscols_ok(*c, t.ps), super::nf::tabs_typed(t), n == c.n, 1 <= nt <= MAX_WORKERS,
            1 <= k <= nt + 1, b@.len() == k, b@[0] == 0,
            forall|j: int| 0 <= j < k - 1 ==> #[trigger] b@[j] <= b@[j + 1],
            forall|j: int| 0 <= j < k ==> #[trigger] b@[j] <= n,
            forall|j: int| 0 < j < k && j < nt ==> #[trigger] b@[j] == 0 || b@[j] == n || rkey(t, b@[j] - 1) != rkey(t, b@[j] as int),
            k == nt + 1 ==> b@[nt as int] == n,
        decreases nt + 1 - k,
    {
        let prev = b[k - 1];
        let step = n / nt;
        proof {
            assert(step * k <= n) by (nonlinear_arith) requires step == n / nt, k <= nt, nt >= 1, n >= 0;
        }
        let mut x: usize = if k == nt { n } else { step * k };
        if x < prev { x = prev; }
        if x > n { x = n; }
        while x > 0 && x < n && row_key(c, x, Ghost(t)) == row_key(c, x - 1, Ghost(t))
            invariant pscols_ok(*c, t.ps), super::nf::tabs_typed(t), n == c.n, prev <= x <= n, k == nt ==> x == n,
            decreases n - x,
        {
            x = x + 1;
        }
        b.push(x);
        k = k + 1;
    }
    b
}

// ------------------------------------------------------------------------------------------------ scan tasks

/// One range's scan result.
pub struct ScanOut {
    pub keys: Vec<i64>,
    pub sums: Vec<i128>,
    pub len: usize,
    pub total: i128,
    pub mass: u128,
    pub status: u8,
}

/// What a range's scan result states (buffers of `cap` slots).
pub open spec fn scan_out_ok(t: Tabs, name: Seq<u8>, lo: int, hi: int, cap: int, lb: i128, o: ScanOut) -> bool {
    &&& o.keys@.len() == cap && o.sums@.len() == cap
    &&& o.status == SCAN_OK || o.status == SCAN_FULL || o.status == SCAN_OVER
    &&& o.status == SCAN_OK ==> o.len <= cap && scan_ok(t, name, lo, hi, o.keys@, o.sums@, o.len as int, o.total, o.mass, lb)
    &&& o.status == SCAN_FULL ==> cap < hi - lo
    &&& o.status == SCAN_OVER ==> tabs(t, name, lo, hi) > MAXM
}

/// The scan of rows `lo .. hi` (calling thread or worker; `mask` is scratch of `CHUNK_WORDS` words).
pub fn scan_one(c: &PSCols, fl: &Vec<u8>, smin: i64, range: usize, lo: usize, hi: usize, keys: Vec<i64>, sums: Vec<i128>,
    lb: i128, mask: &mut Vec<u64>, touch: bool, bm: &Vec<u64>, use_bm: bool, Ghost(t): Ghost<Tabs>, Ghost(name): Ghost<Seq<u8>>)
    -> (o: ScanOut)
    requires
        scan_env(*c, fl@, smin, range, t, name), lo <= hi <= c.n, keys@.len() == sums@.len(),
        use_bm ==> bm_ok(bm@, c.n as int, t, name),
        old(mask)@.len() == CHUNK_WORDS,
    ensures scan_out_ok(t, name, lo as int, hi as int, keys@.len() as int, lb, o), final(mask)@.len() == CHUNK_WORDS,
    no_unwind
{
    let mut keys = keys;
    let mut sums = sums;
    let (a, status) = scan_range(c, fl, smin, range, lo, hi, &mut keys, &mut sums, lb, mask, touch, bm, use_bm, Ghost(t), Ghost(name));
    ScanOut { keys, sums, len: a.len, total: a.total, mass: a.mass, status }
}

/// A range's scan with its emitted groups also as `(key, SUM)` pairs sorted by SUM descending (`out[0 .. m]`,
/// a permutation of `filt` of the groups above the scan's bound); `tmp` is the sort's scratch, handed back so that
/// it is freed on the calling thread after the join.
pub struct TaskOut {
    pub s: ScanOut,
    pub out: Vec<(i64, i128)>,
    pub m: usize,
    pub tmp: Vec<(i64, i128)>,
}

/// What a range's sorted scan result states (buffers of `cap` slots).
pub open spec fn task_out_ok(t: Tabs, name: Seq<u8>, lo: int, hi: int, cap: int, lb: i128, o: TaskOut) -> bool {
    &&& scan_out_ok(t, name, lo, hi, cap, lb, o.s)
    &&& o.s.status == SCAN_OK ==> sorted_out(o.s, o.out@, o.m as int, lb)
}

/// `out[0 .. m]`: the groups of `s` above `lb`, sorted by SUM descending.
pub open spec fn sorted_out(s: ScanOut, out: Seq<(i64, i128)>, m: int, lb: i128) -> bool {
    &&& 0 <= m <= out.len()
    &&& desc(out.subrange(0, m))
    &&& out.subrange(0, m).to_multiset() == filt(s.keys@, s.sums@, s.len as int, lb).to_multiset()
}

/// The scan of rows `lo .. hi`, then its groups sorted by SUM descending (calling thread or worker).
pub fn scan_sort(c: &PSCols, fl: &Vec<u8>, smin: i64, range: usize, lo: usize, hi: usize, keys: Vec<i64>, sums: Vec<i128>,
    out: Vec<(i64, i128)>, tmp: Vec<(i64, i128)>, lb: i128, mask: &mut Vec<u64>, touch: bool, bm: &Vec<u64>, use_bm: bool,
    Ghost(t): Ghost<Tabs>, Ghost(name): Ghost<Seq<u8>>) -> (o: TaskOut)
    requires
        scan_env(*c, fl@, smin, range, t, name), lo <= hi <= c.n, keys@.len() == sums@.len(),
        use_bm ==> bm_ok(bm@, c.n as int, t, name),
        out@.len() == keys@.len(), tmp@.len() == keys@.len(), old(mask)@.len() == CHUNK_WORDS,
    ensures task_out_ok(t, name, lo as int, hi as int, keys@.len() as int, lb, o), final(mask)@.len() == CHUNK_WORDS,
    no_unwind
{
    let s = scan_one(c, fl, smin, range, lo, hi, keys, sums, lb, mask, touch, bm, use_bm, Ghost(t), Ghost(name));
    let mut out = out;
    let mut tmp = tmp;
    let mut m: usize = 0;
    if s.status == SCAN_OK {
        m = filter_groups(&s.keys, &s.sums, s.len, lb, &mut out);
        let ghost f = out@.subrange(0, m as int);
        msort(&mut out, &mut tmp, 0, m);
        proof {
            assert(seg(out@, 0, m as int) == out@.subrange(0, m as int));
        }
    }
    TaskOut { s, out, m, tmp }
}

pub struct ScanTask {
    pub c: PSCols,
    pub fl: Arc<Vec<u8>>,
    pub smin: i64,
    pub range: usize,
    pub lo: usize,
    pub hi: usize,
    pub keys: Vec<i64>,
    pub sums: Vec<i128>,
    pub out: Vec<(i64, i128)>,
    pub tmp: Vec<(i64, i128)>,
    pub mask: Vec<u64>,
    pub lb: i128,
    /// Touch the payload cache lines while building masks (`scan::chunk_mask`).
    pub touch: bool,
    /// The qualifying-row bitmap (`bitmap::bm_ok`), read instead of the supplier codes when `use_bm`.
    pub bm: Arc<Vec<u64>>,
    pub use_bm: bool,
    pub t: Ghost<Tabs>,
    pub name: Ghost<Seq<u8>>,
}

impl WorkerTask for ScanTask {
    type Output = TaskOut;

    open spec fn pre(&self) -> bool {
        &&& scan_env(self.c, self.fl@, self.smin, self.range, self.t@, self.name@)
        &&& self.lo <= self.hi <= self.c.n
        &&& self.keys@.len() == self.sums@.len()
        &&& self.out@.len() == self.keys@.len()
        &&& self.tmp@.len() == self.keys@.len()
        &&& self.mask@.len() == CHUNK_WORDS
        &&& self.use_bm ==> bm_ok(self.bm@, self.c.n as int, self.t@, self.name@)
    }

    open spec fn post(&self, o: TaskOut) -> bool {
        task_out_ok(self.t@, self.name@, self.lo as int, self.hi as int, self.keys@.len() as int, self.lb, o)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (o: TaskOut) {
        let ScanTask { c, fl, smin, range, lo, hi, keys, sums, out, tmp, mask, lb, touch, bm, use_bm, t, name } = self;
        let f: &Vec<u8> = &*fl;
        let b: &Vec<u64> = &*bm;
        let mut mask = mask;
        scan_sort(&c, f, smin, range, lo, hi, keys, sums, out, tmp, lb, &mut mask, touch, b, use_bm, t, name)
    }
}

// ------------------------------------------------------------------------------------------------ filter tasks

/// The groups `0 .. n` of `keys/sums` whose SUM exceeds `thr`, in order.
pub open spec fn filt(keys: Seq<i64>, sums: Seq<i128>, n: int, thr: i128) -> Seq<(i64, i128)>
    decreases n,
{
    if n <= 0 { Seq::empty() } else if sums[n - 1] > thr {
        filt(keys, sums, n - 1, thr).push((keys[n - 1], sums[n - 1]))
    } else {
        filt(keys, sums, n - 1, thr)
    }
}

/// `filt` has at most `n` elements, each a group `i < n` above `thr`.
pub proof fn lemma_filt_members(keys: Seq<i64>, sums: Seq<i128>, n: int, thr: i128)
    requires 0 <= n <= keys.len(), n <= sums.len(),
    ensures
        filt(keys, sums, n, thr).len() <= n,
        forall|x: int| 0 <= x < filt(keys, sums, n, thr).len() ==>
            exists|i: int| 0 <= i < n && #[trigger] filt(keys, sums, n, thr)[x] == (keys[i], sums[i]) && sums[i] > thr,
    decreases n,
{
    if n > 0 {
        lemma_filt_members(keys, sums, n - 1, thr);
        let f0 = filt(keys, sums, n - 1, thr);
        let f = filt(keys, sums, n, thr);
        assert forall|x: int| 0 <= x < f.len() implies
            exists|i: int| 0 <= i < n && #[trigger] f[x] == (keys[i], sums[i]) && sums[i] > thr by {
            if x < f0.len() {
                assert(f[x] == f0[x]);
                let i = choose|i: int| 0 <= i < n - 1 && #[trigger] f0[x] == (keys[i], sums[i]) && sums[i] > thr;
            } else {
                assert(f[x] == (keys[n - 1], sums[n - 1]));
            }
        }
    }
}

/// Every group `i < n` above `thr` is in `filt`.
pub proof fn lemma_filt_complete(keys: Seq<i64>, sums: Seq<i128>, n: int, thr: i128, i: int)
    requires 0 <= i < n <= keys.len(), n <= sums.len(), sums[i] > thr,
    ensures filt(keys, sums, n, thr).contains((keys[i], sums[i])),
    decreases n,
{
    let f0 = filt(keys, sums, n - 1, thr);
    let f = filt(keys, sums, n, thr);
    if i < n - 1 {
        lemma_filt_complete(keys, sums, n - 1, thr, i);
        let x = choose|x: int| 0 <= x < f0.len() && f0[x] == (keys[i], sums[i]);
        if sums[n - 1] > thr {
            assert(f[x] == f0[x]);
        }
    } else {
        assert(f[f0.len() as int] == (keys[i], sums[i]));
    }
}

/// Strictly increasing keys stay strictly increasing in `filt`.
pub proof fn lemma_filt_sorted(keys: Seq<i64>, sums: Seq<i128>, n: int, thr: i128)
    requires
        0 <= n <= keys.len(), n <= sums.len(),
        forall|i: int, j: int| 0 <= i < j < n ==> #[trigger] keys[i] < #[trigger] keys[j],
    ensures
        forall|x: int, y: int| 0 <= x < y < filt(keys, sums, n, thr).len() ==>
            #[trigger] filt(keys, sums, n, thr)[x].0 < #[trigger] filt(keys, sums, n, thr)[y].0,
    decreases n,
{
    if n > 0 {
        lemma_filt_sorted(keys, sums, n - 1, thr);
        lemma_filt_members(keys, sums, n - 1, thr);
        let f0 = filt(keys, sums, n - 1, thr);
        let f = filt(keys, sums, n, thr);
        assert forall|x: int, y: int| 0 <= x < y < f.len() implies #[trigger] f[x].0 < #[trigger] f[y].0 by {
            assert(f[x] == f0[x]);
            if y < f0.len() {
                assert(f[y] == f0[y]);
            } else {
                let i = choose|i: int| 0 <= i < n - 1 && #[trigger] f0[x] == (keys[i], sums[i]) && sums[i] > thr;
                assert(keys[i] < keys[n - 1]);
            }
        }
    }
}

/// Writes the groups `0 .. n` above `thr` to `out[0 .. m]`; returns `m`.
pub fn filter_groups(keys: &Vec<i64>, sums: &Vec<i128>, n: usize, thr: i128, out: &mut Vec<(i64, i128)>) -> (m: usize)
    requires n <= keys@.len(), n <= sums@.len(), n <= old(out)@.len(),
    ensures
        final(out)@.len() == old(out)@.len(),
        m <= final(out)@.len(),
        final(out)@.subrange(0, m as int) == filt(keys@, sums@, n as int, thr),
    no_unwind
{
    let mut m: usize = 0;
    let mut i: usize = 0;
    while i < n
        invariant
            n <= keys@.len(), n <= sums@.len(), n <= out@.len(), out@.len() == old(out)@.len(),
            i <= n, m <= i,
            out@.subrange(0, m as int) == filt(keys@, sums@, i as int, thr),
        decreases n - i,
    {
        let s = sums[i];
        if s > thr {
            let ghost o0 = out@;
            crate::gendb_entry::work::put(out, m, (keys[i], s));
            proof {
                assert(out@.subrange(0, m + 1) =~= o0.subrange(0, m as int).push((keys@[i as int], s)));
            }
            m = m + 1;
        }
        i = i + 1;
    }
    m
}

} // verus!
