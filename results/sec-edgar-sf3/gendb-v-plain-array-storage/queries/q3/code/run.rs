//! The scan of all num rows: `ntask` scan tasks over contiguous row ranges (`scan`), each with dense per-rank
//! accumulators, then `nm` merge tasks over contiguous rank ranges, each adding the scan outputs of its ranks in
//! task order. Result: for every rank, the total `rsum` over all num rows (as `Wide`) and whether any row counted.
//! The path needs fewer than 2^33 num rows, so every partial and total sum fits `i128`.
use vstd::prelude::*;
use crate::spec::numeric::*;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS, fork_join, WorkerTask};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::agent::common::wide::*;
use crate::agent::keys::*;
use crate::agent::scan::*;
use std::sync::Arc;

verus! {

/// The totals over the rows `0..m`.
pub open spec fn totals_ok(num: &NumCols, sub: &SubCols, p0: Seq<u8>, tot: Seq<Wide>, seen: Seq<bool>, m: int) -> bool {
    let nq = sub.qlist(sub.n as int).len();
    &&& tot.len() == nq && seen.len() == nq
    &&& forall|id: int| 0 <= id < nq ==> #[trigger] wval(tot[id]) == rsum(num, p0, rank_key(sub, id), 0, m)
    &&& forall|id: int| 0 <= id < nq ==> #[trigger] seen[id] == (rcnt(num, p0, rank_key(sub, id), 0, m) > 0)
}

/// Every total in the exact range of `Wide`.
pub proof fn lemma_tot_in_range(num: &NumCols, p0: Seq<u8>, key: Seq<u8>, m: int)
    requires num.wf(), 0 <= m <= num.n,
    ensures -wide_limit() <= rsum(num, p0, key, 0, m) <= wide_limit(),
{
    lemma_rsum_bound(num, p0, key, 0, m);
    assert(pow10(28) == 10000000000000000000000000000) by (compute);
    assert(m <= 0xffff_ffff_ffff_ffff);
    assert(m * (pow10(28) - 1) <= 0xffff_ffff_ffff_ffff * (pow10(28) - 1)) by (nonlinear_arith)
        requires m <= 0xffff_ffff_ffff_ffffint, pow10(28) >= 1;
}

/// The row range of task `t` of a round over `start..end` split in `chunk`-row pieces.
pub open spec fn piece_lo(start: int, end: int, chunk: int, t: int) -> int {
    if start + t * chunk < end { start + t * chunk } else { end }
}

/// The pieces start at `start`, do not decrease, stay inside `start..end`, and the `nt`-th ends at `end` when
/// `nt` pieces cover the rows.
proof fn lemma_pieces(start: int, end: int, chunk: int, t: int, nt: int)
    requires start < end, chunk >= 1, 0 <= t, end - start < nt * chunk,
    ensures
        piece_lo(start, end, chunk, 0) == start,
        start <= piece_lo(start, end, chunk, t) <= piece_lo(start, end, chunk, t + 1) <= end,
        piece_lo(start, end, chunk, nt) == end,
        piece_lo(start, end, chunk, t + 1) - piece_lo(start, end, chunk, t) <= chunk,
{
    assert(t * chunk <= (t + 1) * chunk) by (nonlinear_arith) requires chunk >= 1, t >= 0;
    assert((t + 1) * chunk == t * chunk + chunk) by (nonlinear_arith);
    assert(t * chunk >= 0) by (nonlinear_arith) requires chunk >= 1, t >= 0;
    assert(0 * chunk == 0);
}

/// Zero totals for `nq` ranks.
fn zero_totals(nq: usize) -> (r: (Vec<Wide>, Vec<bool>))
    ensures
        r.0@.len() == nq, r.1@.len() == nq,
        forall|id: int| 0 <= id < nq ==> #[trigger] wval(r.0@[id]) == 0,
        forall|id: int| 0 <= id < nq ==> !#[trigger] r.1@[id],
{
    let mut tot: Vec<Wide> = Vec::with_capacity(nq);
    let mut seen: Vec<bool> = Vec::with_capacity(nq);
    let mut k: usize = 0;
    while k < nq
        invariant
            k <= nq, tot@.len() == k, seen@.len() == k,
            forall|id: int| 0 <= id < k ==> #[trigger] wval(tot@[id]) == 0,
            forall|id: int| 0 <= id < k ==> !#[trigger] seen@[id],
        decreases nq - k,
    {
        tot.push(wide_zero());
        seen.push(false);
        k = k + 1;
    }
    (tot, seen)
}

/// The task of rows `lo..hi`, with fresh scratch, sharing the key structure.
fn new_task(num: &NumCols, sub: &SubCols, p0: &'static [u8], p0_len: usize, lo: usize, hi: usize, nq: usize,
    keys: &Arc<Keys>) -> (task: ScanTask)
    requires
        num.wf(), sub.wf(), p0_len == p0@.len(),
        nq == sub.qlist(sub.n as int).len(), 3 * nq + 3 < usize::MAX,
        keys_inv((**keys).view(), sub, nq as int),
        lo <= hi <= num.n, hi - lo <= 0x2_0000_0000int,
    ensures
        task.pre(), task.num == *num, task.sub == *sub, task.p0 == p0, task.lo == lo, task.hi == hi,
{
    let out = ScanOut {
        acc: vec![0i128; nq + 1],
        seen: vec![0u8; nq + 1],
        sel: vec![0usize; BLK],
    };
    proof {
        assert forall|i: int| 0 <= i < out.acc@.len() implies #[trigger] out.acc@[i] == 0 by {
            assert(cloned(0i128, out.acc@[i]));
        }
        assert forall|i: int| 0 <= i < out.seen@.len() implies #[trigger] out.seen@[i] == 0 by {
            assert(cloned(0u8, out.seen@[i]));
        }
    }
    ScanTask { num: *num, sub: *sub, p0, p0_len, lo, hi, keys: keys.clone(), out }
}

/// What a round's tasks cover: task `i` reads `num`, `sub`, `p0` and rows `piece_lo(i) .. piece_lo(i + 1)`.
pub open spec fn round_tasks(tv: Seq<ScanTask>, num: &NumCols, sub: &SubCols, p0: &'static [u8], start: int, end: int, chunk: int) -> bool {
    forall|i: int| 0 <= i < tv.len() ==> {
        &&& (#[trigger] tv[i]).num == *num && tv[i].sub == *sub && tv[i].p0 == p0
        &&& tv[i].lo == piece_lo(start, end, chunk, i)
        &&& tv[i].hi == piece_lo(start, end, chunk, i + 1)
    }
}

/// No counted row: zero sum.
pub proof fn lemma_rcnt_zero(nc: &NumCols, p0: Seq<u8>, key: Seq<u8>, lo: int, i: int)
    requires rcnt(nc, p0, key, lo, i) == 0,
    ensures rsum(nc, p0, key, lo, i) == 0,
    decreases i - lo,
{
    if i > lo {
        lemma_rcnt_nonneg(nc, p0, key, lo, i - 1);
        lemma_rcnt_zero(nc, p0, key, lo, i - 1);
    }
}

/// The largest partial sum of a row range of fewer than 2^33 rows.
pub open spec fn part_limit() -> int {
    0x2_0000_0000int * 9999999999999999999999999999int
}

/// A sum over fewer than 2^33 rows is within `part_limit`, which is inside `i128`.
proof fn lemma_part_bound(nc: &NumCols, p0: Seq<u8>, key: Seq<u8>, lo: int, hi: int)
    requires nc.wf(), 0 <= lo <= hi <= nc.n, hi - lo <= 0x2_0000_0000,
    ensures
        -part_limit() <= rsum(nc, p0, key, lo, hi) <= part_limit(),
        part_limit() + 10000000000000000000000000000int < 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffffint,
{
    lemma_rsum_bound(nc, p0, key, lo, hi);
    assert(pow10(28) == 10000000000000000000000000000) by (compute);
    let d = hi - lo;
    assert(d * (pow10(28) - 1) <= 0x2_0000_0000int * 9999999999999999999999999999int) by (nonlinear_arith)
        requires 0 <= d <= 0x2_0000_0000int, pow10(28) == 10000000000000000000000000000int;
}

/// The merge of the ranks `a..b`: the outputs of the scan tasks `tv` (rows `0..n` in `chunk`-row pieces), added
/// rank by rank in task order. `tot` and `seen` are its scratch of `b - a` entries.
pub struct MergeTask {
    pub outs: Arc<Vec<ScanOut>>,
    pub tv: Ghost<Seq<ScanTask>>,
    pub num: NumCols,
    pub sub: SubCols,
    pub p0: &'static [u8],
    pub n: usize,
    pub chunk: usize,
    pub a: usize,
    pub b: usize,
    pub tot: Vec<i128>,
    pub seen: Vec<bool>,
}

/// The totals of the ranks `a..b` (entry `k` is rank `a + k`).
pub struct MergeOut {
    pub tot: Vec<i128>,
    pub seen: Vec<bool>,
}

impl MergeTask {
    pub open spec fn nq(&self) -> int {
        self.sub.qlist(self.sub.n as int).len() as int
    }

    /// Entries `k` of `j0..j1` hold the totals of the rows `0..m`.
    pub open spec fn upto(&self, tot: Seq<i128>, seen: Seq<bool>, j0: int, j1: int, m: int) -> bool {
        &&& forall|k: int| j0 <= k < j1 ==> #[trigger] tot[k] as int
            == rsum(&self.num, self.p0@, rank_key(&self.sub, self.a + k), 0, m)
        &&& forall|k: int| j0 <= k < j1 ==> #[trigger] seen[k]
            == (rcnt(&self.num, self.p0@, rank_key(&self.sub, self.a + k), 0, m) > 0)
    }
}

impl WorkerTask for MergeTask {
    type Output = MergeOut;

    open spec fn pre(&self) -> bool {
        &&& self.num.wf()
        &&& self.n == self.num.n && 0 < self.n < 0x2_0000_0000
        &&& self.chunk >= 1
        &&& self.tv@.len() == (*self.outs)@.len() && 1 <= self.tv@.len() <= MAX_WORKERS
        &&& self.n < self.tv@.len() * self.chunk
        &&& round_tasks(self.tv@, &self.num, &self.sub, self.p0, 0, self.n as int, self.chunk as int)
        &&& forall|i: int| 0 <= i < self.tv@.len() ==> #[trigger] self.tv@[i].post((*self.outs)@[i])
        &&& self.a <= self.b <= self.nq()
        &&& self.tot@.len() == self.b - self.a && self.seen@.len() == self.b - self.a
    }

    open spec fn post(&self, out: MergeOut) -> bool {
        &&& out.tot@.len() == self.b - self.a && out.seen@.len() == self.b - self.a
        &&& self.upto(out.tot@, out.seen@, 0, self.b - self.a, self.n as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.a as u64, self.b as u64)
    }

    fn run(self) -> (out: MergeOut) {
        let ghost t0 = self;
        let MergeTask { outs, tv, num, sub, p0, n, chunk, a, b, tot, seen } = self;
        let outs: &Vec<ScanOut> = &*outs;
        let mut tot = tot;
        let mut seen = seen;
        let m = b - a;
        let mut k: usize = 0;
        while k < m
            invariant k <= m, m == b - a, tot@.len() == m, seen@.len() == m,
                t0.a == a, t0.num == num, t0.sub == sub, t0.p0 == p0,
                t0.upto(tot@, seen@, 0, k as int, 0),
            decreases m - k,
        {
            tot[k] = 0;
            seen[k] = false;
            k = k + 1;
        }
        let nt = outs.len();
        let mut t: usize = 0;
        proof {
            lemma_pieces(0, n as int, chunk as int, 0, nt as int);
        }
        while t < nt
            invariant
                t0.pre(), t0.a == a, t0.b == b, t0.num == num, t0.sub == sub, t0.p0 == p0, t0.n == n,
                t0.chunk == chunk, t0.tv == tv, *t0.outs == *outs,
                nt == outs@.len(), t <= nt, m == b - a, tot@.len() == m, seen@.len() == m,
                t0.upto(tot@, seen@, 0, m as int, piece_lo(0, n as int, chunk as int, t as int)),
            decreases nt - t,
        {
            let o = &outs[t];
            let ghost lo = piece_lo(0, n as int, chunk as int, t as int);
            let ghost hi = piece_lo(0, n as int, chunk as int, t + 1);
            proof {
                lemma_pieces(0, n as int, chunk as int, t as int, nt as int);
                assert(tv@[t as int].post(outs@[t as int]));
                assert(tv@[t as int].lo == lo && tv@[t as int].hi == hi);
                assert(tv@[t as int].sub == sub && tv@[t as int].num == num && tv@[t as int].p0 == p0);
            }
            let mut k: usize = 0;
            while k < m
                invariant
                    t0.pre(), t0.a == a, t0.b == b, t0.num == num, t0.sub == sub, t0.p0 == p0, t0.n == n,
                    m == b - a, k <= m, tot@.len() == m, seen@.len() == m,
                    tv@[t as int].post(*o), tv@[t as int].lo == lo, tv@[t as int].hi == hi,
                    tv@[t as int].sub == sub, tv@[t as int].num == num, tv@[t as int].p0 == p0,
                    0 <= lo <= hi <= n,
                    t0.upto(tot@, seen@, 0, k as int, hi),
                    t0.upto(tot@, seen@, k as int, m as int, lo),
                decreases m - k,
            {
                let ghost key = rank_key(&sub, a + k);
                proof {
                    lemma_rsum_split(&num, p0@, key, 0, lo, hi);
                    lemma_part_bound(&num, p0@, key, 0, lo);
                    lemma_part_bound(&num, p0@, key, 0, hi);
                    lemma_rcnt_nonneg(&num, p0@, key, 0, lo);
                    lemma_rcnt_nonneg(&num, p0@, key, lo, hi);
                    assert(o.acc@[a + k] as int == rsum(&num, p0@, key, lo, hi));
                    assert((o.seen@[a + k] != 0) == (rcnt(&num, p0@, key, lo, hi) > 0));
                }
                let v = o.acc[a + k];
                let x = tot[k];
                tot[k] = x + v;
                let s = seen[k] || o.seen[a + k] != 0;
                seen[k] = s;
                k = k + 1;
            }
            t = t + 1;
        }
        proof {
            lemma_pieces(0, n as int, chunk as int, 0, nt as int);
        }
        MergeOut { tot, seen }
    }
}

/// The scan tasks of the rows `0..n` in `chunk`-row pieces.
fn scan_tasks(num: &NumCols, sub: &SubCols, p0: &'static [u8], p0_len: usize, nq: usize, ntask: usize, chunk: usize,
    keys: &Arc<Keys>) -> (tasks: Vec<ScanTask>)
    requires
        num.wf(), sub.wf(), p0_len == p0@.len(), nq == sub.qlist(sub.n as int).len(), 3 * nq + 3 < usize::MAX,
        keys_inv((**keys).view(), sub, nq as int),
        0 < num.n < 0x2_0000_0000, 1 <= ntask <= 64, 1 <= chunk <= 0x2_0000_0000, num.n < ntask * chunk,
    ensures
        tasks@.len() == ntask,
        forall|i: int| 0 <= i < ntask ==> (#[trigger] tasks@[i]).pre(),
        round_tasks(tasks@, num, sub, p0, 0, num.n as int, chunk as int),
{
    let n = num.n;
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut t: usize = 0;
    while t < ntask
        invariant
            num.wf(), sub.wf(), p0_len == p0@.len(), nq == sub.qlist(sub.n as int).len(), 3 * nq + 3 < usize::MAX,
            keys_inv((**keys).view(), sub, nq as int), n == num.n,
            0 < n < 0x2_0000_0000, 1 <= ntask <= 64, 1 <= chunk <= 0x2_0000_0000, n < ntask * chunk,
            t <= ntask, tasks@.len() == t,
            forall|i: int| 0 <= i < t ==> (#[trigger] tasks@[i]).pre(),
            round_tasks(tasks@, num, sub, p0, 0, n as int, chunk as int),
        decreases ntask - t,
    {
        proof {
            assert((t as int) * (chunk as int) <= 64 * 0x2_0000_0000int) by (nonlinear_arith)
                requires t <= 64, chunk <= 0x2_0000_0000int, t >= 0, chunk >= 0;
            assert((t as int + 1) * (chunk as int) <= 65 * 0x2_0000_0000int) by (nonlinear_arith)
                requires t <= 64, chunk <= 0x2_0000_0000int, t >= 0, chunk >= 0;
            lemma_pieces(0, n as int, chunk as int, t as int, ntask as int);
        }
        let tc: u64 = (t as u64) * (chunk as u64);
        let tc1: u64 = (t as u64 + 1) * (chunk as u64);
        let lo = if tc < n as u64 { tc as usize } else { n };
        let hi = if tc1 < n as u64 { tc1 as usize } else { n };
        assert(lo as int == piece_lo(0, n as int, chunk as int, t as int));
        assert(hi as int == piece_lo(0, n as int, chunk as int, t as int + 1));
        let task = new_task(num, sub, p0, p0_len, lo, hi, nq, keys);
        tasks.push(task);
        t = t + 1;
    }
    tasks
}

/// The merge tasks of the ranks `0..nq` in `mchunk`-rank pieces.
fn merge_tasks(outs: &Arc<Vec<ScanOut>>, Ghost(tv): Ghost<Seq<ScanTask>>, num: &NumCols, sub: &SubCols,
    p0: &'static [u8], chunk: usize, nq: usize, nm: usize, mchunk: usize) -> (mts: Vec<MergeTask>)
    requires
        num.wf(), 0 < num.n < 0x2_0000_0000, chunk >= 1,
        tv.len() == (**outs)@.len(), 1 <= tv.len() <= MAX_WORKERS, num.n < tv.len() * chunk,
        round_tasks(tv, num, sub, p0, 0, num.n as int, chunk as int),
        forall|i: int| 0 <= i < tv.len() ==> #[trigger] tv[i].post((**outs)@[i]),
        nq == sub.qlist(sub.n as int).len(), 0 < nq, 1 <= nm <= 64, mchunk >= 1, nq < nm * mchunk,
    ensures
        mts@.len() == nm,
        forall|m: int| 0 <= m < nm ==> (#[trigger] mts@[m]).pre() && mts@[m].num == *num && mts@[m].sub == *sub
            && mts@[m].p0 == p0 && mts@[m].n == num.n
            && mts@[m].a == piece_lo(0, nq as int, mchunk as int, m)
            && mts@[m].b == piece_lo(0, nq as int, mchunk as int, m + 1),
{
    let mut mts: Vec<MergeTask> = Vec::new();
    let mut m: usize = 0;
    while m < nm
        invariant
            num.wf(), 0 < num.n < 0x2_0000_0000, chunk >= 1,
            tv.len() == (**outs)@.len(), 1 <= tv.len() <= MAX_WORKERS, num.n < tv.len() * chunk,
            round_tasks(tv, num, sub, p0, 0, num.n as int, chunk as int),
            forall|i: int| 0 <= i < tv.len() ==> #[trigger] tv[i].post((**outs)@[i]),
            nq == sub.qlist(sub.n as int).len(), 0 < nq, 1 <= nm <= 64, mchunk >= 1, nq < nm * mchunk,
            m <= nm, mts@.len() == m,
            forall|j: int| 0 <= j < m ==> (#[trigger] mts@[j]).pre() && mts@[j].num == *num && mts@[j].sub == *sub
                && mts@[j].p0 == p0 && mts@[j].n == num.n
                && mts@[j].a == piece_lo(0, nq as int, mchunk as int, j)
                && mts@[j].b == piece_lo(0, nq as int, mchunk as int, j + 1),
        decreases nm - m,
    {
        proof {
            lemma_pieces(0, nq as int, mchunk as int, m as int, nm as int);
            assert((m as int) * (mchunk as int) >= 0) by (nonlinear_arith) requires m >= 0, mchunk >= 0;
            assert((m as int + 1) * (mchunk as int) <= 65 * 0xffff_ffff_ffff_ffffint) by (nonlinear_arith)
                requires m < 64, mchunk <= 0xffff_ffff_ffff_ffffint, mchunk >= 0;
            assert((m as int) * (mchunk as int) <= (m as int + 1) * (mchunk as int)) by (nonlinear_arith)
                requires m >= 0, mchunk >= 0;
        }
        let mc: u128 = (m as u128) * (mchunk as u128);
        let mc1: u128 = (m as u128 + 1) * (mchunk as u128);
        let a = if mc < nq as u128 { mc as usize } else { nq };
        let b = if mc1 < nq as u128 { mc1 as usize } else { nq };
        assert(a as int == piece_lo(0, nq as int, mchunk as int, m as int));
        assert(b as int == piece_lo(0, nq as int, mchunk as int, m as int + 1));
        let mt = MergeTask {
            outs: outs.clone(), tv: Ghost(tv), num: *num, sub: *sub, p0, n: num.n, chunk, a, b,
            tot: vec![0i128; b - a], seen: vec![false; b - a],
        };
        mts.push(mt);
        m = m + 1;
    }
    mts
}

/// Scan every num row: the totals of every rank.
pub fn run_scan(num: &NumCols, sub: &SubCols, p0: &'static [u8], p0_len: usize, nq: usize, bits: u64, workers: usize,
    dispatch: &mut Dispatch) -> (r: Result<(Vec<Wide>, Vec<bool>), WorkerFailure>)
    requires
        num.wf(), sub.wf(), p0_len == p0@.len(), num.n < 0x2_0000_0000,
        nq == sub.qlist(sub.n as int).len(),
        1 <= bits <= 30, pow2i(bits as nat) + nq + 1 < usize::MAX, 3 * nq + 3 < usize::MAX,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok((tot, seen)) ==> totals_ok(num, sub, p0@, tot@, seen@, num.n as int),
{
    let n = num.n;
    if n == 0 || nq == 0 {
        // No row or no qualifying sub: every total is the empty sum.
        let (tot, seen) = zero_totals(nq);
        return Ok((tot, seen));
    }
    proof {
        vstd::bits::lemma_usize_pow2_no_overflow(bits as nat);
        vstd::bits::lemma_usize_shl_is_mul(1, bits as usize);
    }
    let pslots = (1usize << (bits as usize)) + nq + 1;
    let mut keys = Keys {
        bits,
        nslots: pslots,
        table: vec![0u64; pslots],
        bloom: vec![0u64; 0x4000],
        kw: vec![0u64; 3 * nq + 3],
        qsub: vec![0u32; nq + 1],
    };
    proof {
        assert(keys.table@.len() == pslots);
        assert(keys.kw@.len() == 3 * nq + 3);
        assert(keys_shape(keys.view(), sub));
        assert forall|s: int| 0 <= s < keys.table@.len() implies #[trigger] keys.table@[s] == 0 by {
            assert(cloned(0u64, keys.table@[s]));
        }
    }
    build_keys(&mut keys, sub);
    let keys = Arc::new(keys);
    // The scan: `ntask` row pieces of `chunk` rows.
    let ntask: usize = if n < 0x3_0000 { 1 } else { workers };
    let chunk = n / ntask + 1;
    proof {
        assert(chunk as int <= 0x2_0000_0000int);
        assert(n < ntask * chunk) by (nonlinear_arith) requires chunk == n / ntask + 1, ntask >= 1;
    }
    let tasks = scan_tasks(num, sub, p0, p0_len, nq, ntask, chunk, &keys);
    let ghost tv = tasks@;
    let outs: Vec<ScanOut> = if ntask == 1 {
        let mut tasks = tasks;
        let task = tasks.pop().unwrap();
        assert(task == tv[0]);
        let o = task.run();
        let mut v: Vec<ScanOut> = Vec::new();
        v.push(o);
        v
    } else {
        match fork_join(dispatch, tasks) {
            Ok(v) => v,
            Err(e) => return Err(e),
        }
    };
    // The merge: `nm` rank pieces of `mchunk` ranks.
    let nm: usize = if ntask == 1 || nq < 0x1000 { 1 } else if ntask < 16 { ntask } else { 16 };
    let mchunk = nq / nm + 1;
    proof {
        assert(nq < nm * mchunk) by (nonlinear_arith) requires mchunk == nq / nm + 1, nm >= 1;
    }
    let outs = Arc::new(outs);
    let mts = merge_tasks(&outs, Ghost(tv), num, sub, p0, chunk, nq, nm, mchunk);
    let ghost mv = mts@;
    let mouts: Vec<MergeOut> = if nm == 1 {
        let mut mts = mts;
        let mt = mts.pop().unwrap();
        assert(mt == mv[0]);
        let o = mt.run();
        let mut v: Vec<MergeOut> = Vec::new();
        v.push(o);
        v
    } else {
        match fork_join(dispatch, mts) {
            Ok(v) => v,
            Err(e) => return Err(e),
        }
    };
    // The pieces in rank order.
    let mut tot: Vec<Wide> = Vec::with_capacity(nq);
    let mut seen: Vec<bool> = Vec::with_capacity(nq);
    let mut m: usize = 0;
    proof {
        lemma_pieces(0, nq as int, mchunk as int, 0, nm as int);
    }
    while m < nm
        invariant
            num.wf(), nq == sub.qlist(sub.n as int).len(), 0 < nq, mchunk >= 1, nm >= 1, nq < nm * mchunk,
            mouts@.len() == nm, mv.len() == nm, m <= nm,
            forall|j: int| 0 <= j < nm ==> (#[trigger] mv[j]).post(mouts@[j]) && mv[j].num == *num && mv[j].sub == *sub
                && mv[j].p0 == p0 && mv[j].n == num.n
                && mv[j].a == piece_lo(0, nq as int, mchunk as int, j)
                && mv[j].b == piece_lo(0, nq as int, mchunk as int, j + 1),
            tot@.len() == piece_lo(0, nq as int, mchunk as int, m as int), seen@.len() == tot@.len(),
            forall|id: int| 0 <= id < tot@.len() ==> #[trigger] wval(tot@[id]) == rsum(num, p0@, rank_key(sub, id), 0, num.n as int),
            forall|id: int| 0 <= id < seen@.len() ==> #[trigger] seen@[id] == (rcnt(num, p0@, rank_key(sub, id), 0, num.n as int) > 0),
        decreases nm - m,
    {
        let mo = &mouts[m];
        proof {
            lemma_pieces(0, nq as int, mchunk as int, m as int, nm as int);
            assert(mv[m as int].post(mouts@[m as int]));
        }
        let len = mo.tot.len();
        let mut k: usize = 0;
        while k < len
            invariant
                num.wf(), nq == sub.qlist(sub.n as int).len(),
                mv[m as int].post(*mo), mv[m as int].num == *num, mv[m as int].sub == *sub, mv[m as int].p0 == p0,
                mv[m as int].n == num.n, len == mo.tot@.len(), k <= len,
                tot@.len() == mv[m as int].a + k, seen@.len() == tot@.len(),
                forall|id: int| 0 <= id < tot@.len() ==> #[trigger] wval(tot@[id]) == rsum(num, p0@, rank_key(sub, id), 0, num.n as int),
                forall|id: int| 0 <= id < seen@.len() ==> #[trigger] seen@[id] == (rcnt(num, p0@, rank_key(sub, id), 0, num.n as int) > 0),
            decreases len - k,
        {
            proof {
                let id = mv[m as int].a + k;
                assert(mo.tot@[k as int] as int == rsum(num, p0@, rank_key(sub, id), 0, num.n as int));
                lemma_tot_in_range(num, p0@, rank_key(sub, id), num.n as int);
            }
            let ghost tot0 = tot@;
            let ghost seen0 = seen@;
            tot.push(wide_add_i128(wide_zero(), mo.tot[k]));
            seen.push(mo.seen[k]);
            proof {
                assert forall|id: int| 0 <= id < tot@.len() implies #[trigger] wval(tot@[id]) == rsum(num, p0@, rank_key(sub, id), 0, num.n as int) by {
                    if id < tot0.len() {
                        assert(tot@[id] == tot0[id]);
                    }
                }
                assert forall|id: int| 0 <= id < seen@.len() implies #[trigger] seen@[id] == (rcnt(num, p0@, rank_key(sub, id), 0, num.n as int) > 0) by {
                    if id < seen0.len() {
                        assert(seen@[id] == seen0[id]);
                    }
                }
            }
            k = k + 1;
        }
        m = m + 1;
    }
    proof {
        lemma_pieces(0, nq as int, mchunk as int, 0, nm as int);
    }
    Ok((tot, seen))
}

} // verus!
