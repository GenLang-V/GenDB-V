//! The parallel path: the dictionary, a cost-balanced split of the rows into task ranges, one scan task per range,
//! the merge of their groups and the distinct counts over id ranges. `Ok(None)` sends the query to the serial
//! path (`serial_groups`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::agent::cols::*;
use crate::agent::spec::*;
use crate::agent::dict::*;
use crate::agent::kernel::*;
use crate::agent::merge::*;
use crate::agent::distinct::*;
use crate::agent::serial::final_ok;
use crate::agent::common::bytes::eq_ranges;

verus! {

/// One table of the dictionary, filled by a worker task (`fill_part`) into zeroed slots.
pub struct PartTask {
    pub c: Cols,
    pub nids: usize,
    pub pbits: u64,
    pub p: usize,
    pub mask: usize,
    pub slots: Vec<u32>,
}

impl WorkerTask for PartTask {
    type Output = Vec<u32>;

    open spec fn pre(&self) -> bool {
        &&& cols_wf(self.c)
        &&& self.nids <= self.c.m && self.nids < 0x1000_0000
        &&& self.pbits <= 6 && self.mask < 0x1000_0000
        &&& part_ok(self.mask, self.nids, self.slots@)
    }

    open spec fn post(&self, out: Vec<u32>) -> bool {
        part_ok(self.mask, self.nids, out@)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.p as u64, self.p as u64)
    }

    fn run(self) -> (out: Vec<u32>) {
        let mut slots = self.slots;
        fill_part(&self.c, self.nids, self.pbits, self.p, self.mask, &mut slots);
        slots
    }
}

/// Tables of the dictionary built in parallel (`1 << DICT_PBITS` of them) when the call has this many workers.
pub const DICT_PBITS: u64 = 3;

/// The dictionary in `1 << pbits` tables, one worker task each.
fn build_dict_par(c: &Cols, pbits: u64, dispatch: &mut Dispatch) -> (r: Result<Dict, WorkerFailure>)
    requires cols_wf(*c), 1 <= pbits <= 6,
    ensures r matches Ok(d) ==> dict_wf(*c, d),
{
    let nids = dict_ids(c);
    let mask = table_mask(nids, pbits);
    proof { assert((1u64 << pbits) <= 64) by (bit_vector) requires pbits <= 6u64; }
    let np = (1u64 << pbits) as usize;
    let mut tasks: Vec<PartTask> = Vec::new();
    let mut p: usize = 0;
    while p < np
        invariant
            cols_wf(*c), nids <= c.m, nids < 0x1000_0000, pbits <= 6, mask < 0x1000_0000, np <= 64, p <= np,
            tasks@.len() == p,
            forall|q: int| 0 <= q < p ==> (#[trigger] tasks@[q]).pre() && tasks@[q].mask == mask && tasks@[q].nids == nids,
        decreases np - p,
    {
        let slots = vec![0u32; mask + 1];
        proof {
            assert forall|s: int| 0 <= s < slots@.len() implies #[trigger] slots@[s] <= nids by {
                assert(slots@[s] == 0);
            }
        }
        tasks.push(PartTask { c: *c, nids, pbits, p, mask, slots });
        p = p + 1;
    }
    let ghost tk = tasks@;
    let parts = match fork_join(dispatch, tasks) {
        Ok(v) => v,
        Err(e) => return Err(e),
    };
    proof {
        assert forall|q: int| 0 <= q < parts@.len() implies #[trigger] part_ok(mask, nids, parts@[q]@) by {
            assert(tk[q].post(parts@[q]));
        }
    }
    Ok(Dict { parts, pbits, mask, nids })
}

/// Rows per task at least (fewer rows run on fewer tasks).
pub const MIN_ROWS: usize = 65536;

/// Number of sampled segments for the cost estimate.
pub const NSEG: usize = 512;

/// Sampled rows per segment.
pub const SAMPLES: usize = 4;

/// Most scan tasks (beyond this the scan is bound by memory bandwidth and spawning costs more than it saves).
pub const MAX_TASKS: usize = 32;

/// Whether rows `i` and `i + 1` have different adsh values (a sample of the dictionary lookups a range needs).
fn adsh_changes(c: &Cols, i: usize) -> bool
    requires cols_wf(*c), i + 1 < c.n,
{
    proof {
        assert(0 <= c.adsh_off@[i as int] <= c.adsh_off@[i + 1] <= c.adsh@.len());
        assert(0 <= c.adsh_off@[i + 1] <= c.adsh_off@[i + 2] <= c.adsh@.len());
    }
    let a0 = c.adsh_off[i] as usize;
    let a1 = c.adsh_off[i + 1] as usize;
    let a2 = c.adsh_off[i + 2] as usize;
    !eq_ranges(c.adsh, c.adsh_len, a0, a1, c.adsh, c.adsh_len, a1, a2)
}

/// `x * y / z` for `z > 0`, and its bound when `y <= z`.
fn mul_div(x: usize, y: usize, z: usize) -> (r: usize)
    requires z > 0, y <= z,
    ensures r as int == (x as int) * (y as int) / (z as int), r <= x,
{
    proof {
        assert((x as int) * (y as int) <= (x as int) * (z as int)) by (nonlinear_arith) requires y <= z, x >= 0;
        assert((x as int) * (y as int) / (z as int) <= x) by (nonlinear_arith)
            requires (x as int) * (y as int) <= (x as int) * (z as int), z > 0, x >= 0, y >= 0;
        assert((x as int) * (y as int) <= 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffffu128) by (nonlinear_arith)
            requires x <= 0xffff_ffff_ffff_ffffu64, y <= 0xffff_ffff_ffff_ffffu64;
    }
    ((x as u128) * (y as u128) / (z as u128)) as usize
}

/// Bounds of `nt` task ranges (`b[0] = 0 <= b[1] <= .. <= b[nt] = n`) balancing an estimated cost: a sampled adsh
/// change costs a dictionary lookup. Later tasks are spawned first, so they get a larger share (`7 * nt + t`).
/// Also, per task, whether its range has a segment where most sampled rows change adsh (it gets a large cache).
pub fn plan_ranges(c: &Cols, nt: usize) -> (r: (Vec<usize>, Vec<bool>))
    requires cols_wf(*c), 1 <= nt <= MAX_WORKERS,
    ensures
        r.0@.len() == nt + 1, r.0@[0] == 0, r.0@[nt as int] == c.n,
        forall|k: int| 0 <= k < nt ==> #[trigger] r.0@[k] <= r.0@[k + 1],
        forall|k: int| 0 <= k <= nt ==> #[trigger] r.0@[k] <= c.n,
        r.1@.len() == nt,
{
    let n = c.n;
    let nseg: usize = if n >= NSEG * 64 { NSEG } else { 1 };
    // Segment `s` is rows [starts[s], starts[s + 1]); its cost: rows * (8 + 12 * sampled adsh changes of 8).
    let mut starts: Vec<usize> = Vec::new();
    let mut costs: Vec<u64> = Vec::new();
    let mut dense: Vec<bool> = Vec::new();
    let mut total: u64 = 0;
    let mut s: usize = 0;
    while s < nseg
        invariant
            cols_wf(*c), n == c.n, 1 <= nseg <= NSEG, s <= nseg, starts@.len() == s, costs@.len() == s, dense@.len() == s,
            total <= s * 0x1_0000_0000_0000,
            forall|k: int| 0 <= k < s ==> #[trigger] starts@[k] <= n,
            forall|k: int| 0 <= k < s ==> #[trigger] costs@[k] <= 0x1_0000_0000_0000,
        decreases nseg - s,
    {
        let lo = mul_div(n, s, nseg);
        let hi = mul_div(n, s + 1, nseg);
        proof {
            assert((n as int) * (s as int) <= (n as int) * (s + 1)) by (nonlinear_arith) requires n >= 0;
            assert((n as int) * (s as int) / (nseg as int) <= (n as int) * (s + 1) / (nseg as int)) by (nonlinear_arith)
                requires (n as int) * (s as int) <= (n as int) * (s + 1), nseg > 0;
        }
        let len = hi - lo;
        let step = len / 8;
        assert(2 * step <= len);
        let mut changes: u64 = 0;
        let mut off = step;
        let mut p: usize = 0;
        while p < SAMPLES && off < len
            invariant cols_wf(*c), n == c.n, lo <= hi <= n, len == hi - lo, p <= SAMPLES, changes <= p, 2 * step <= len,
            decreases 8 - p,
        {
            let i = lo + off;
            if i + 1 < n && adsh_changes(c, i) {
                changes = changes + 1;
            }
            if len - off <= 2 * step {
                p = SAMPLES;
            } else {
                off = off + 2 * step;
                p = p + 1;
            }
        }
        let rows = if len > 0xffff_ffff { 0xffff_ffffu64 } else { len as u64 };
        let r8 = rows >> 8u64;
        proof {
            assert(r8 <= 0xff_ffff) by (bit_vector) requires rows <= 0xffff_ffffu64, r8 == rows >> 8u64;
            assert(r8 * (40 + 45 * changes) <= 0xff_ffff * 220) by (nonlinear_arith)
                requires r8 <= 0xff_ffff, changes <= 4;
        }
        let cost = r8 * (40 + 45 * changes) + 1;
        starts.push(lo);
        costs.push(cost);
        dense.push(changes >= 2);
        total = total + cost;
        s = s + 1;
    }
    let mut b: Vec<usize> = Vec::new();
    b.push(0);
    let mut t: usize = 1;
    let mut seg: usize = 0;
    let mut acc: u64 = 0;
    proof {
        assert((nt as u64) * (7 * nt as u64) <= 64 * 448) by (nonlinear_arith) requires nt <= 64;
        assert((nt as u64) * (nt as u64 - 1) <= 64 * 64) by (nonlinear_arith) requires 1 <= nt <= 64;
        assert((nt as u64) * (7 * nt as u64) >= 7) by (nonlinear_arith) requires nt >= 1;
    }
    let wtotal: u64 = (nt as u64) * (7 * nt as u64) + (nt as u64) * (nt as u64 - 1) / 2;
    while t < nt
        invariant
            cols_wf(*c), n == c.n, 1 <= nseg <= NSEG, costs@.len() == nseg, starts@.len() == nseg,
            forall|k: int| 0 <= k < nseg ==> #[trigger] starts@[k] <= n,
            total <= nseg * 0x1_0000_0000_0000, 1 <= t <= nt, nt <= 64, wtotal >= 3,
            forall|k: int| 0 <= k < nseg ==> #[trigger] costs@[k] <= 0x1_0000_0000_0000,
            wtotal == (nt as u64) * (7 * nt as u64) + (nt as u64) * (nt as u64 - 1) / 2,
            b@.len() == t, b@[0] == 0,
            forall|k: int| 0 <= k < t - 1 ==> #[trigger] b@[k] <= b@[k + 1],
            forall|k: int| 0 <= k < t ==> #[trigger] b@[k] <= n,
            seg <= nseg,
        decreases nt - t,
    {
        let tw = t as u64;
        proof {
            assert(tw * (7 * nt as u64) <= 64 * 448) by (nonlinear_arith) requires tw <= 64, nt <= 64;
            assert(tw * (tw - 1) <= 64 * 64) by (nonlinear_arith) requires 1 <= tw <= 64;
        }
        let wt: u64 = tw * (7 * nt as u64) + tw * (tw - 1) / 2;
        proof {
            assert(total <= 512 * 0x1_0000_0000_0000);
            assert(wt <= 64 * 448 + 64 * 64);
            assert((total as u128) * (wt as u128) <= 512 * 0x1_0000_0000_0000 * (64 * 448 + 64 * 64)) by (nonlinear_arith)
                requires total <= 512 * 0x1_0000_0000_0000, wt <= 64 * 448 + 64 * 64;
        }
        let target = (total as u128 * wt as u128 / wtotal as u128) as u64;
        if acc > target {
            acc = target;
        }
        while seg < nseg && costs[seg] <= target - acc
            invariant seg <= nseg, costs@.len() == nseg, acc <= target,
                forall|k: int| 0 <= k < nseg ==> #[trigger] costs@[k] <= 0x1_0000_0000_0000,
            decreases nseg - seg,
        {
            acc = acc + costs[seg];
            seg = seg + 1;
        }
        let bound = if seg < nseg { starts[seg] } else { n };
        let last = b[t - 1];
        let nb = if bound < last { last } else { bound };
        b.push(nb);
        t = t + 1;
    }
    b.push(n);
    // Task `t` is dense when a dense segment starts in its range (task bounds are segment starts or `n`).
    let mut flags: Vec<bool> = Vec::new();
    let mut t: usize = 0;
    let mut seg: usize = 0;
    while t < nt
        invariant
            b@.len() == nt + 1, t <= nt, flags@.len() == t, seg <= nseg, starts@.len() == nseg, dense@.len() == nseg,
        decreases nt - t,
    {
        let mut f = false;
        while seg < nseg && starts[seg] < b[t + 1]
            invariant seg <= nseg, starts@.len() == nseg, dense@.len() == nseg, t < nt, b@.len() == nt + 1,
            decreases nseg - seg,
        {
            if starts[seg] >= b[t] && dense[seg] {
                f = true;
            }
            seg = seg + 1;
        }
        flags.push(f);
        t = t + 1;
    }
    (b, flags)
}

/// The single range of all rows (no plan needed for one task).
fn one_range(c: &Cols) -> (r: (Vec<usize>, Vec<bool>))
    ensures
        r.0@.len() == 2, r.0@[0] == 0, r.0@[1] == c.n, r.1@.len() == 1,
{
    let mut b: Vec<usize> = Vec::new();
    b.push(0);
    b.push(c.n);
    let mut f: Vec<bool> = Vec::new();
    f.push(true);
    (b, f)
}

/// Fresh per-task buffers.
fn fresh_acc(c: &Cols) -> (a: Acc)
    ensures fresh(*c, a),
{
    Acc {
        rep: vec![0usize; GCAP],
        cnt: vec![0u64; GCAP],
        sum: vec![0i128; GCAP],
        scodes: vec![0u64; GCAP],
        rcodes: vec![0u64; GCAP],
        hint: vec![0u8; 64],
        mask: vec![0u16; c.m],
    }
}

/// Entries of the lookup cache (2-way, a power of two) of a dense task and of any other task.
pub const CACHE_BIG: usize = 16384;
/// Entries of the lookup cache of a single task scanning every row.
pub const CACHE_ONE: usize = 65536;
pub const CACHE_SMALL: usize = 4;

/// A fresh (empty) lookup cache of `entries` entries.
fn fresh_cache(c: &Cols, entries: usize) -> (cache: Vec<u64>)
    requires 2 <= entries <= 0x100_0000,
    ensures cache_ok(*c, cache@),
{
    let cache = vec![0u64; 4 * entries];
    proof { lemma_cache_empty(*c, cache@); }
    cache
}

/// One scan task per range `[b[k], b[k + 1])`; dense tasks (`dense[k]`) get a large lookup cache.
fn make_tasks(c: &Cols, Ghost(t): Ghost<Seq<Row>>, dict: &Arc<Dict>, b: &Vec<usize>, dense: &Vec<bool>, nt: usize)
    -> (tasks: Vec<ScanTask>)
    requires
        cols_wf(*c), corr(*c, t), dict_wf(*c, **dict), 1 <= nt <= MAX_WORKERS, dense@.len() == nt,
        b@.len() == nt + 1, forall|k: int| 0 <= k < nt ==> #[trigger] b@[k] <= b@[k + 1],
        forall|k: int| 0 <= k <= nt ==> #[trigger] b@[k] <= c.n,
    ensures
        tasks@.len() == nt,
        forall|k: int| 0 <= k < nt ==> (#[trigger] tasks@[k]).pre() && tasks@[k].lo == b@[k]
            && tasks@[k].hi == b@[k + 1] && tasks@[k].c == *c && tasks@[k].t@ == t,
{
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut k: usize = 0;
    while k < nt
        invariant
            cols_wf(*c), corr(*c, t), dict_wf(*c, **dict), 1 <= nt <= MAX_WORKERS, k <= nt, dense@.len() == nt,
            b@.len() == nt + 1, forall|k2: int| 0 <= k2 < nt ==> #[trigger] b@[k2] <= b@[k2 + 1],
            forall|k2: int| 0 <= k2 <= nt ==> #[trigger] b@[k2] <= c.n,
            tasks@.len() == k,
            forall|k2: int| 0 <= k2 < k ==> (#[trigger] tasks@[k2]).pre() && tasks@[k2].lo == b@[k2]
                && tasks@[k2].hi == b@[k2 + 1] && tasks@[k2].c == *c && tasks@[k2].t@ == t,
        decreases nt - k,
    {
        proof { assert(b@[k as int] <= b@[k + 1]); assert(b@[k + 1] <= c.n); }
        let acc = fresh_acc(c);
        let cache = fresh_cache(c, if nt == 1 { CACHE_ONE } else if dense[k] { CACHE_BIG } else { CACHE_SMALL });
        tasks.push(ScanTask { c: *c, dict: dict.clone(), t: Ghost(t), lo: b[k], hi: b[k + 1], acc, cache });
        k = k + 1;
    }
    tasks
}

/// Runs the scan tasks (on this thread when there is one); `Ok(None)` when some range did not scan completely.
fn run_scans(c: &Cols, Ghost(t): Ghost<Seq<Row>>, tasks: Vec<ScanTask>, b: &Vec<usize>, nt: usize, dispatch: &mut Dispatch)
    -> (r: Result<Option<Vec<ScanOut>>, WorkerFailure>)
    requires
        cols_wf(*c), corr(*c, t), 1 <= nt <= MAX_WORKERS, tasks@.len() == nt,
        b@.len() == nt + 1, b@[0] == 0, b@[nt as int] == c.n,
        forall|k: int| 0 <= k < nt ==> #[trigger] b@[k] <= b@[k + 1],
        forall|k: int| 0 <= k < nt ==> (#[trigger] tasks@[k]).pre() && tasks@[k].lo == b@[k]
            && tasks@[k].hi == b@[k + 1] && tasks@[k].c == *c && tasks@[k].t@ == t,
    ensures
        r matches Ok(Some(outs)) ==> tasks_ok(*c, t, b@, outs@),
{
    let ghost tk = tasks@;
    let mut tasks = tasks;
    let outs: Vec<ScanOut> = if nt == 1 {
        let task = tasks.pop().unwrap();
        proof { assert(task == tk[0]); }
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
    let mut k: usize = 0;
    while k < nt
        invariant
            outs@.len() == nt, tk.len() == nt, k <= nt,
            forall|k2: int| 0 <= k2 < nt ==> #[trigger] tk[k2].post(outs@[k2]),
            forall|k2: int| 0 <= k2 < k ==> (#[trigger] outs@[k2]).status == ST_OK,
        decreases nt - k,
    {
        if outs[k].status != ST_OK {
            return Ok(None);
        }
        k = k + 1;
    }
    proof {
        assert forall|k2: int| 0 <= k2 < outs@.len() implies (#[trigger] outs@[k2]).status == ST_OK
            && out_ok(*c, t, b@[k2] as int, b@[k2 + 1] as int, outs@[k2].ng as int, outs@[k2].acc) by {
            assert(tk[k2].post(outs@[k2]));
        }
    }
    Ok(Some(outs))
}

/// Distinct counts of the `ng` global groups over all ids, by `nk` count tasks over id ranges.
fn count_all(outs: Arc<Vec<ScanOut>>, maps: Arc<Vec<Vec<usize>>>, ng: usize, m: usize, nt: usize, dispatch: &mut Dispatch)
    -> (r: Result<Vec<u64>, WorkerFailure>)
    requires count_inputs(outs@, maps@, ng as int, m as int), 1 <= nt <= MAX_WORKERS,
    ensures
        r matches Ok(dcnt) ==> dcnt@.len() == ng
            && forall|g: int| 0 <= g < ng ==> #[trigger] dcnt@[g] == idcount(outs@, maps@, g, 0, m as int),
{
    let nk: usize = if nt < 8 { nt } else { 8 };
    let mut ct: Vec<CountTask> = Vec::new();
    let mut q: usize = 0;
    while q < nk
        invariant
            count_inputs(outs@, maps@, ng as int, m as int), 1 <= nk <= 8, q <= nk,
            ct@.len() == q,
            forall|q2: int| 0 <= q2 < q ==> (#[trigger] ct@[q2]).pre() && ct@[q2].lo == (m as int) * q2 / (nk as int)
                && ct@[q2].hi == (m as int) * (q2 + 1) / (nk as int) && ct@[q2].outs@ == outs@ && ct@[q2].maps@ == maps@
                && ct@[q2].ng == ng,
        decreases nk - q,
    {
        let lo = mul_div(m, q, nk);
        let hi = mul_div(m, q + 1, nk);
        proof { lemma_split_point(m as int, nk as int, q as int); }
        ct.push(CountTask { outs: outs.clone(), maps: maps.clone(), ng, m: Ghost(m as int), lo, hi, out: vec![0u64; 64] });
        q = q + 1;
    }
    let ghost cq = ct@;
    let res: Vec<Vec<u64>> = if nk == 1 {
        let task = ct.pop().unwrap();
        proof { assert(task == cq[0]); }
        let r = task.run();
        let mut v: Vec<Vec<u64>> = Vec::new();
        v.push(r);
        v
    } else {
        match fork_join(dispatch, ct) {
            Ok(v) => v,
            Err(e) => return Err(e),
        }
    };
    let mut dcnt: Vec<u64> = vec![0u64; ng];
    let mut q: usize = 0;
    while q < nk
        invariant
            res@.len() == nk, cq.len() == nk, q <= nk, 1 <= nk <= 8, ng <= 64,
            forall|q2: int| 0 <= q2 < nk ==> #[trigger] cq[q2].post(res@[q2]),
            forall|q2: int| 0 <= q2 < nk ==> (#[trigger] cq[q2]).lo == (m as int) * q2 / (nk as int)
                && cq[q2].hi == (m as int) * (q2 + 1) / (nk as int) && cq[q2].outs@ == outs@ && cq[q2].maps@ == maps@
                && cq[q2].ng == ng,
            dcnt@.len() == ng,
            forall|g: int| 0 <= g < ng ==> #[trigger] dcnt@[g] == idcount(outs@, maps@, g, 0, (m as int) * (q as int) / (nk as int)),
        decreases nk - q,
    {
        let rq = &res[q];
        proof { assert(cq[q as int].post(res@[q as int])); }
        let mut g: usize = 0;
        while g < ng
            invariant
                res@.len() == nk, q < nk, 1 <= nk <= 8, rq@.len() == 64, dcnt@.len() == ng, g <= ng, ng <= 64,
                rq == res@[q as int], cq[q as int].ng == ng,
                forall|g2: int| 0 <= g2 < ng ==> #[trigger] rq@[g2] == idcount(outs@, maps@, g2, (m as int) * (q as int) / (nk as int), (m as int) * (q + 1) / (nk as int)),
                forall|g2: int| 0 <= g2 < g ==> #[trigger] dcnt@[g2] == idcount(outs@, maps@, g2, 0, (m as int) * (q + 1) / (nk as int)),
                forall|g2: int| g <= g2 < ng ==> #[trigger] dcnt@[g2] == idcount(outs@, maps@, g2, 0, (m as int) * (q as int) / (nk as int)),
            decreases ng - g,
        {
            proof {
                lemma_split_point(m as int, nk as int, q as int);
                lemma_idcount_split(outs@, maps@, g as int, 0, (m as int) * (q as int) / (nk as int), (m as int) * (q + 1) / (nk as int));
                lemma_idcount_le(outs@, maps@, g as int, 0, (m as int) * (q + 1) / (nk as int));
            }
            let v = dcnt[g] + rq[g];
            dcnt.set(g, v);
            g = g + 1;
        }
        q = q + 1;
    }
    proof {
        assert((m as int) * (nk as int) / (nk as int) == m as int) by (nonlinear_arith) requires nk >= 1;
    }
    Ok(dcnt)
}

/// Scans and merges: the task outputs (range bounds `b`) and the merged global groups.
fn scan_and_merge(c: &Cols, Ghost(t): Ghost<Seq<Row>>, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<Option<(Vec<usize>, Vec<ScanOut>, Merged)>, WorkerFailure>)
    requires
        cols_wf(*c), corr(*c, t), 1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(Some((b, outs, mg))) ==> {
            &&& tasks_ok(*c, t, b@, outs@)
            &&& 1 <= outs@.len() <= MAX_WORKERS
            &&& merged_ok(t, c.n as int, c.n as int, mg.rep@, mg.cnt@, mg.sum@)
            &&& mg.maps@.len() == outs@.len()
            &&& maps_ok(t, mg.rep@, outs@, mg.maps@, outs@.len() as int)
        },
{
    let n = c.n;
    let dict = if workers >= 8 {
        match build_dict_par(c, DICT_PBITS, dispatch) {
            Ok(d) => Arc::new(d),
            Err(e) => return Err(e),
        }
    } else {
        Arc::new(build_dict(c))
    };
    let mut nt = if workers < MAX_TASKS { workers } else { MAX_TASKS };
    if n / MIN_ROWS < nt {
        nt = n / MIN_ROWS;
    }
    if nt == 0 {
        nt = 1;
    }
    let (b, dense) = if nt == 1 { one_range(c) } else { plan_ranges(c, nt) };
    let tasks = make_tasks(c, Ghost(t), &dict, &b, &dense, nt);
    let outs = match run_scans(c, Ghost(t), tasks, &b, nt, dispatch) {
        Ok(Some(o)) => o,
        Ok(None) => return Ok(None),
        Err(e) => return Err(e),
    };
    let mg = match merge_groups(c, Ghost(t), &outs, &b) {
        Some(mg) => mg,
        None => return Ok(None),
    };
    Ok(Some((b, outs, mg)))
}

/// The groups of the whole table by the parallel path; `Ok(None)` when it cannot run (see module doc).
pub fn fast_groups(c: &Cols, Ghost(t): Ghost<Seq<Row>>, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Option<Groups>, WorkerFailure>)
    requires
        cols_wf(*c), corr(*c, t), sub_distinct(*c), 1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(Some(gs)) ==> final_ok(t, c.n as int, c.n as int, gs),
{
    let (b, outs, mg) = match scan_and_merge(c, Ghost(t), workers, dispatch) {
        Ok(Some(x)) => x,
        Ok(None) => return Ok(None),
        Err(e) => return Err(e),
    };
    let nt = outs.len();
    let ng = mg.rep.len();
    let ghost maps_v = mg.maps@;
    let ghost outs_v = outs@;
    proof { lemma_count_inputs(*c, t, b@, outs@, mg.rep@, maps_v); }
    let outs = Arc::new(outs);
    let maps = Arc::new(mg.maps);
    let dcnt = match count_all(outs, maps, ng, c.m, nt, dispatch) {
        Ok(d) => d,
        Err(e) => return Err(e),
    };
    let gs = Groups { rep: mg.rep, cnt: mg.cnt, sum: mg.sum, dcnt };
    proof { lemma_fast_final(*c, t, b@, outs_v, gs, maps_v); }
    Ok(Some(gs))
}

proof fn lemma_count_inputs(c: Cols, t: Seq<Row>, b: Seq<usize>, outs: Seq<ScanOut>, rep: Seq<usize>, maps: Seq<Vec<usize>>)
    requires
        tasks_ok(c, t, b, outs), maps.len() == outs.len(), maps_ok(t, rep, outs, maps, outs.len() as int), rep.len() <= 64,
    ensures
        count_inputs(outs, maps, rep.len() as int, c.m as int),
{
    assert forall|k2: int| 0 <= k2 < outs.len() implies {
        &&& (#[trigger] outs[k2]).ng <= GCAP
        &&& outs[k2].acc.mask@.len() == c.m
        &&& maps[k2]@.len() == GCAP
        &&& forall|lg: int| 0 <= lg < outs[k2].ng ==> #[trigger] maps[k2]@[lg] < rep.len()
    } by {
        assert(out_ok(c, t, b[k2] as int, b[k2 + 1] as int, outs[k2].ng as int, outs[k2].acc));
        assert(map_ok(t, rep, outs[k2], maps[k2]@));
    }
}

proof fn lemma_fast_final(c: Cols, t: Seq<Row>, b: Seq<usize>, outs: Seq<ScanOut>, gs: Groups, maps: Seq<Vec<usize>>)
    requires
        cols_wf(c), corr(c, t), tasks_ok(c, t, b, outs), sub_distinct(c),
        merged_ok(t, c.n as int, c.n as int, gs.rep@, gs.cnt@, gs.sum@),
        maps.len() == outs.len(), maps_ok(t, gs.rep@, outs, maps, outs.len() as int),
        gs.dcnt@.len() == gs.rep@.len(),
        forall|g: int| 0 <= g < gs.rep@.len() ==> #[trigger] gs.dcnt@[g] == idcount(outs, maps, g, 0, c.m as int),
    ensures
        final_ok(t, c.n as int, c.n as int, gs),
{
    assert forall|g: int| 0 <= g < gs.rep@.len() implies #[trigger] gs.dcnt@[g] == aset_r(t, gkey(t, gs.rep@, g), 0, c.n as int).len() by {
        lemma_idcount_aset(c, t, b, outs, gs.rep@, gs.cnt@, gs.sum@, maps, g);
    }
}

/// Range split points `m * q / nk`, nondecreasing, within `[0, m]`, and their executable form.
proof fn lemma_split_point(m: int, nk: int, q: int)
    requires m >= 0, nk >= 1, 0 <= q < nk,
    ensures
        m / nk * q + (m % nk) * q / nk == m * q / nk,
        m / nk * (q + 1) + (m % nk) * (q + 1) / nk == m * (q + 1) / nk,
        0 <= m * q / nk <= m * (q + 1) / nk <= m,
{
    assert(m == m / nk * nk + m % nk) by (nonlinear_arith) requires nk >= 1;
    assert(m * q == (m / nk * q) * nk + (m % nk) * q) by (nonlinear_arith) requires m == m / nk * nk + m % nk;
    assert(m * q / nk == m / nk * q + (m % nk) * q / nk) by (nonlinear_arith)
        requires m * q == (m / nk * q) * nk + (m % nk) * q, nk >= 1, m % nk >= 0, q >= 0;
    assert(m * (q + 1) == (m / nk * (q + 1)) * nk + (m % nk) * (q + 1)) by (nonlinear_arith) requires m == m / nk * nk + m % nk;
    assert(m * (q + 1) / nk == m / nk * (q + 1) + (m % nk) * (q + 1) / nk) by (nonlinear_arith)
        requires m * (q + 1) == (m / nk * (q + 1)) * nk + (m % nk) * (q + 1), nk >= 1, m % nk >= 0, q >= 0;
    assert(m * q / nk <= m * (q + 1) / nk) by (nonlinear_arith) requires m >= 0, nk >= 1, q >= 0;
    assert(m * (q + 1) / nk <= m) by (nonlinear_arith) requires m >= 0, nk >= 1, q + 1 <= nk;
    assert(0 <= m * q / nk) by (nonlinear_arith) requires m >= 0, nk >= 1, q >= 0;
}

/// At most one id per position.
proof fn lemma_idcount_le(outs: Seq<ScanOut>, maps: Seq<Vec<usize>>, g: int, lo: int, hi: int)
    requires lo <= hi,
    ensures idcount(outs, maps, g, lo, hi) <= hi - lo,
    decreases hi - lo,
{
    if hi > lo {
        lemma_idcount_le(outs, maps, g, lo, hi - 1);
    }
}

} // verus!
