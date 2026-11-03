//! Query: the top 100 `num` rows (by value DESC, sub.name, tag) with `uom = $1`, a `sub` row of the same
//! `adsh` with `fy = $2`, whose value is the maximum of their `(adsh, tag)` group among the `uom = $1` rows.
//!
//! Plan (every step is exact for every threshold; the thresholds are heuristics):
//! 1. scan `num` in parallel row ranges for `uom = $1` (at most `MAX_TASKS` jobs; `fork_join` spawns the last
//!    job first, so later jobs scan more rows), each job keeping its rows above a rising coefficient threshold
//!    (`scan`); the largest job threshold `T` gives the exact candidate list at `T`;
//! 2. the last job also builds the index of the `sub` rows with `fy = $2` by `adsh` (`subtable`), overlapping
//!    the spawn of the other workers;
//! 3. zoom: for a threshold `t2 >= T` (about the 2048th, 8192nd, ... largest coefficient) keep the candidates
//!    at `t2` with a matching `sub` row that are the maximum of their group (`rank::body_rows`; a larger member
//!    of the group is a candidate at `t2` too), until at least 100 answer rows exist or `t2 = T`;
//! 4. sort those answer rows by ORDER BY and keep the first 100; every other answer row is below `t2` and sorts
//!    after them.
//! If `T` leaves fewer than 100 answer rows, a serial scan collects every candidate (threshold `i128::MIN`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::Answer;
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::{QueryError, WorkerFailure};
use crate::gendb_entry::stores::Stores;
use crate::gendb_params::Params;
use crate::link::query::{text_wf, view_rows, TextCol};
use crate::stores::flat_num::interface as ni;
use crate::stores::flat_sub::interface as si;

pub mod answer;
pub mod group;
pub mod order;
pub mod rank;
pub mod scan;
pub mod select;
pub mod sem;
pub mod spec;
pub mod subtable;

use crate::agent::answer::*;
use crate::agent::order::ans_rows;
use crate::agent::rank::*;
use crate::agent::scan::*;
use crate::agent::select::kth_largest;
use crate::agent::spec::*;
use crate::agent::subtable::*;
use crate::gendb_entry::work::TaskBuffer;
use crate::agent::sem::lits_ok;

verus! {

/// LIMIT of the statement.
pub const LIMIT: usize = 100;

/// Buffer slots of a scan task: a lone task, and each of several tasks (the merged list stays short).
pub const SERIAL_CAP: usize = 2048;
pub const TASK_CAP: usize = 256;

/// Partition weights: task `t` of `T` scans rows in proportion to `SPREAD * T - (T - 1 - t)`, so tasks spawned
/// earlier (thread creation is serial, from the last task) scan more rows.
pub const SPREAD: usize = 4;

/// Rows per task below which fewer tasks are used.
pub const MIN_TASK_ROWS: usize = 65536;

/// First zoom target (candidates above the zoom threshold): about one candidate in ten is an answer row.
pub const FIRST_TARGET: usize = 2048;

/// Most scan tasks: the scan is bound by memory bandwidth beyond this, and each thread costs a serial spawn.
pub const MAX_TASKS: usize = 32;

/// Size of the coefficient sample the zoom selects from.
pub const ZOOM_SAMPLE: usize = 4096;

/// The `num` columns the scan reads (whole parts).
pub struct NumScan {
    pub uom: TextCol,
    pub value: &'static [i128],
}

pub open spec fn num_scan_ok(s: NumScan, c: Ctx) -> bool {
    &&& s.uom@ == uom_view(c.np)
    &&& s.value@ == coeff_seq(c.np)
}

/// Candidate rows of all of `num` at threshold `thr` with their coefficients.
pub struct Cands {
    pub rows: Vec<usize>,
    pub coeffs: Vec<i128>,
    pub thr: i128,
}

pub open spec fn cands_ok(e: Cands, c: Ctx) -> bool {
    &&& e.rows@.len() == e.coeffs@.len()
    &&& lists(c, e.rows@, e.coeffs@, e.rows@.len() as int, cands(c, 0, c.n, e.thr as int))
}

/// The partition weight of task `t` of `tasks`. `fork_join` spawns the last task first, so later tasks start
/// earlier and scan more rows; the last job (which builds the `sub` index first) somewhat fewer.
fn task_weight(tasks: usize, t: usize) -> (w: usize)
    requires 1 <= tasks <= MAX_WORKERS, t < tasks,
    ensures 0 < w <= 256,
{
    if t + 1 == tasks && tasks > 1 {
        SPREAD * tasks * 3 / 4
    } else {
        SPREAD * tasks - (tasks - 1 - t)
    }
}

/// About `n * w / total` (at most `n`): the rows of a task of weight `w`.
fn share(n: usize, total: usize, w: usize) -> (r: usize)
    ensures r <= n,
{
    if total == 0 || w > total {
        return n;
    }
    let q = n / total;
    proof {
        assert(q * w <= q * total) by (nonlinear_arith) requires w <= total, q >= 0;
        assert(q * total <= n) by (nonlinear_arith) requires q == n / total, total > 0;
    }
    q * w
}

/// The tasks cover `0..n` in order: task `t` starts where task `t - 1` ends.
pub open spec fn tasks_cover(ts: Seq<ScanTask>, n: int) -> bool {
    &&& ts.len() >= 1
    &&& ts[0].lo == 0
    &&& ts[ts.len() - 1].hi == n
    &&& forall|t: int| 0 < t < ts.len() ==> #[trigger] ts[t].lo == ts[t - 1].hi
}

/// One worker job: a scan range and, for the last job, the build of the `sub` index (overlapping the spawn of
/// the other workers and their scans).
pub struct Job {
    pub scan: ScanTask,
    pub plan: Option<TablePlan>,
}

pub struct JobOut {
    pub scan: ScanOut,
    pub built: Option<Built>,
}

impl WorkerTask for Job {
    type Output = JobOut;

    open spec fn pre(&self) -> bool {
        &&& scan_inputs_ok(self.scan)
        &&& (self.plan matches Some(p) ==> plan_ok(p, self.scan.ctx@))
    }

    open spec fn post(&self, out: JobOut) -> bool {
        &&& scan_out_ok(self.scan.ctx@, self.scan.lo as int, self.scan.hi as int, out.scan)
        &&& (self.plan matches Some(p) ==> (out.built matches Some(b) && built_ok(b, p.cap, self.scan.ctx@)))
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.scan.lo as u64, self.scan.hi as u64)
    }

    fn run(self) -> (out: JobOut) {
        let Job { scan, plan } = self;
        let built = match plan {
            Some(p) => Some(build_planned(p, scan.ctx)),
            None => None,
        };
        JobOut { scan: scan_range(scan), built }
    }
}

/// The scan outputs of the jobs in order, and the built index of the last job.
fn split_outs(v: Vec<JobOut>) -> (r: (Vec<ScanOut>, Option<Built>))
    requires v@.len() >= 1,
    ensures
        r.0@.len() == v@.len(),
        forall|q: int| 0 <= q < v@.len() ==> #[trigger] r.0@[q] == v@[q].scan,
        r.1 == v@[v@.len() - 1].built,
{
    let ghost orig = v@;
    let n = v.len();
    let mut v = v;
    let mut outs: Vec<ScanOut> = Vec::new();
    let mut built: Option<Built> = None;
    let mut k: usize = 0;
    while k < n
        invariant
            n == orig.len(), n >= 1,
            k <= n,
            v@ == orig.subrange(k as int, n as int),
            outs@.len() == k,
            forall|q: int| 0 <= q < k ==> #[trigger] outs@[q] == orig[q].scan,
            k == n ==> built == orig[n - 1].built,
        decreases n - k,
    {
        let x = v.remove(0);
        proof {
            assert(x == orig[k as int]);
            assert(v@ =~= orig.subrange(k + 1, n as int));
        }
        let JobOut { scan, built: b } = x;
        if k + 1 == n {
            built = b;
        }
        outs.push(scan);
        k = k + 1;
    }
    (outs, built)
}

/// Parallel scan: the exact candidates at `e.thr` (`None` when a task could not raise its threshold), and the
/// index of the `sub` members, built by the last job (the first spawned).
fn scan_parallel(s: &NumScan, param: &'static [u8], n: usize, workers: usize, plan: TablePlan,
    dispatch: &mut Dispatch, Ghost(c): Ghost<Ctx>) -> (r: Result<(Option<Cands>, SubTable), WorkerFailure>)
    requires
        1 <= workers <= MAX_WORKERS,
        ctx_ok(c),
        c.n == n as int,
        param@ == c.pv,
        num_scan_ok(*s, c),
        plan_ok(plan, c),
    ensures
        r matches Ok((oe, t)) ==> table_wf(t, c) && (oe matches Some(e) ==> cands_ok(e, c)),
{
    let mut tasks: usize = n / MIN_TASK_ROWS;
    if tasks > workers {
        tasks = workers;
    }
    if tasks > MAX_TASKS {
        tasks = MAX_TASKS;
    }
    if tasks < 1 {
        tasks = 1;
    }
    let cap: usize = if tasks == 1 { SERIAL_CAP } else { TASK_CAP };
    let mut total_weight: usize = 0;
    let mut q: usize = 0;
    while q < tasks
        invariant 1 <= tasks <= MAX_WORKERS, q <= tasks, total_weight <= 256 * q,
        decreases tasks - q,
    {
        total_weight = total_weight + task_weight(tasks, q);
        q = q + 1;
    }
    let plen = param.len();
    let tcap = plan.cap;
    let sadsh = TextCol { offsets: plan.adsh.offsets, bytes: plan.adsh.bytes };
    let m = plan.m;
    let mut plan_opt: Option<TablePlan> = Some(plan);
    let mut list: Vec<Job> = Vec::new();
    let mut lo: usize = 0;
    let mut t: usize = 0;
    while t < tasks
        invariant
            1 <= tasks <= MAX_WORKERS,
            t <= tasks,
            list@.len() == t,
            lo <= n,
            t == 0 ==> lo == 0,
            t < tasks ==> (plan_opt matches Some(p) && plan_ok(p, c) && p.cap == tcap),
            t > 0 ==> list@[t - 1].scan.hi == lo && list@[0].scan.lo == 0,
            t == tasks ==> (list@[t - 1].plan matches Some(p) && p.cap == tcap),
            t == tasks ==> lo == n,
            forall|q: int| 0 < q < t ==> #[trigger] list@[q].scan.lo == list@[q - 1].scan.hi,
            forall|q: int| 0 <= q < t ==> (#[trigger] list@[q]).pre() && list@[q].scan.ctx@ == c,
            ctx_ok(c), c.n == n as int, param@ == c.pv, plen == param@.len(), num_scan_ok(*s, c),
            cap >= 1,
        decreases tasks - t,
    {
        let size: usize = share(n, total_weight, task_weight(tasks, t));
        let hi = if t + 1 == tasks { n } else if n - lo > size { lo + size } else { n };
        let task = ScanTask {
            lo, hi,
            uom: TextCol { offsets: s.uom.offsets, bytes: s.uom.bytes },
            value: s.value, param, plen, cap,
            rows: vec![0usize; cap],
            coeffs: vec![0i128; cap],
            scratch: vec![0i128; SAMPLE],
            ctx: Ghost(c),
        };
        let jp: Option<TablePlan> = if t + 1 == tasks { plan_opt.take() } else { None };
        list.push(Job { scan: task, plan: jp });
        lo = hi;
        t = t + 1;
    }
    let ghost jl = list@;
    let ghost tl = list@.map_values(|j: Job| j.scan);
    let jouts: Vec<JobOut> = if tasks == 1 {
        let job = list.pop().unwrap();
        let o = job.run();
        let mut v: Vec<JobOut> = Vec::new();
        v.push(o);
        v
    } else {
        match fork_join(dispatch, list) {
            Ok(v) => v,
            Err(e) => return Err(e),
        }
    };
    proof {
        assert(jouts@.len() == jl.len());
        assert(jl[tasks - 1].post(jouts@[tasks - 1]));
    }
    let (outs, built) = split_outs(jouts);
    let table = match built {
        Some(b) => finish_table(b, tcap, sadsh, m, Ghost(c)),
        None => {
            proof {
                assert(false);
            }
            return Ok((None, finish_table(Built { slots: Vec::new(), hashes: Vec::new(), overflow: TaskBuffer::new(0, 0usize) }, tcap, sadsh, m, Ghost(c))));
        },
    };
    proof {
        assert(tasks_cover(tl, n as int)) by {
            assert forall|q: int| 0 < q < tl.len() implies #[trigger] tl[q].lo == tl[q - 1].hi by {
                assert(jl[q].scan.lo == jl[q - 1].scan.hi);
            }
        }
        assert forall|q: int| 0 <= q < outs@.len() implies
            #[trigger] scan_out_ok(c, tl[q].lo as int, tl[q].hi as int, outs@[q]) by {
            assert(jl[q].post(jouts@[q]));
            assert(jl[q].pre());
        }
        assert forall|q: int| 0 <= q < tl.len() implies #[trigger] tl[q].lo <= tl[q].hi by {
            assert(jl[q].pre());
        }
    }
    // The exact threshold: the largest task threshold.
    let count = outs.len();
    let mut thr: i128 = i128::MIN;
    let mut k: usize = 0;
    while k < count
        invariant
            count == outs@.len(),
            k <= count,
            table_wf(table, c),
            forall|q: int| 0 <= q < k ==> (#[trigger] outs@[q]).ok && outs@[q].thr <= thr,
        decreases count - k,
    {
        if !outs[k].ok {
            return Ok((None, table));
        }
        if outs[k].thr > thr {
            thr = outs[k].thr;
        }
        k = k + 1;
    }
    let mut rows: Vec<usize> = Vec::new();
    let mut coeffs: Vec<i128> = Vec::new();
    let ghost mut cur: int = 0;
    let mut k: usize = 0;
    while k < count
        invariant
            count == outs@.len(),
            count == tl.len(),
            tasks_cover(tl, n as int),
            k <= count,
            ctx_ok(c),
            forall|q: int| 0 <= q < count ==> (#[trigger] outs@[q]).ok && outs@[q].thr <= thr,
            forall|q: int| 0 <= q < count ==> #[trigger] scan_out_ok(c, tl[q].lo as int, tl[q].hi as int, outs@[q]),
            forall|q: int| 0 <= q < count ==> #[trigger] tl[q].lo <= tl[q].hi,
            table_wf(table, c),
            k < count ==> cur == tl[k as int].lo,
            k == count ==> cur == n,
            rows@.len() == coeffs@.len(),
            lists(c, rows@, coeffs@, rows@.len() as int, cands(c, 0, cur, thr as int)),
        decreases count - k,
    {
        let o = &outs[k];
        let len = o.len;
        let ghost lo_k = tl[k as int].lo as int;
        let ghost hi_k = tl[k as int].hi as int;
        let ghost src = cands(c, lo_k, hi_k, o.thr as int);
        let ghost f = ge_thr(c, thr as int);
        let ghost base = cands(c, 0, cur, thr as int);
        proof {
            assert(scan_out_ok(c, lo_k, hi_k, outs@[k as int]));
        }
        let mut j: usize = 0;
        while j < len
            invariant
                lists(c, o.rows@, o.coeffs@, len as int, src),
                f == ge_thr(c, thr as int),
                j <= len,
                rows@.len() == coeffs@.len(),
                lists(c, rows@, coeffs@, rows@.len() as int, base + src.subrange(0, j as int).filter(f)),
            decreases len - j,
        {
            proof {
                lemma_filter_push(src.subrange(0, j as int), src[j as int], f);
                assert(src.subrange(0, j as int + 1) =~= src.subrange(0, j as int).push(src[j as int]));
            }
            if o.coeffs[j] >= thr {
                rows.push(o.rows[j]);
                coeffs.push(o.coeffs[j]);
                proof {
                    assert(base + src.subrange(0, j as int).filter(f).push(src[j as int])
                        =~= (base + src.subrange(0, j as int).filter(f)).push(src[j as int]));
                }
            }
            j = j + 1;
        }
        proof {
            assert(src.subrange(0, len as int) =~= src);
            lemma_cands_raise(c, lo_k, hi_k, o.thr as int, thr as int);
            lemma_cands_append(c, 0, lo_k, hi_k, thr as int);
            if k + 1 < count {
                assert(tl[k + 1].lo == tl[k as int].hi);
            }
            cur = hi_k;
        }
        k = k + 1;
    }
    Ok((Some(Cands { rows, coeffs, thr }), table))
}

/// Serial scan collecting every candidate (threshold `i128::MIN`).
fn scan_serial(s: &NumScan, param: &'static [u8], n: usize, Ghost(c): Ghost<Ctx>) -> (e: Cands)
    requires
        ctx_ok(c),
        c.n == n as int,
        param@ == c.pv,
        num_scan_ok(*s, c),
    ensures
        cands_ok(e, c),
        e.thr == i128::MIN,
{
    let plen = param.len();
    let mut rows: Vec<usize> = Vec::new();
    let mut coeffs: Vec<i128> = Vec::new();
    proof {
        lemma_num_text_wf(c);
    }
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            ctx_ok(c),
            c.n == n as int,
            text_wf(s.uom@, c.n),
            s.value@.len() == c.n,
            param@ == c.pv,
            plen == param@.len(),
            num_scan_ok(*s, c),
            rows@.len() == coeffs@.len(),
            lists(c, rows@, coeffs@, rows@.len() as int, cands(c, 0, i as int, i128::MIN as int)),
        decreases n - i,
    {
        proof {
            assert(0 <= s.uom@.offsets[i as int] <= s.uom@.offsets[i + 1] <= s.uom@.bytes.len());
        }
        let hit = text_is(&s.uom, i, param, plen, Ghost(c.n));
        if hit {
            rows.push(i);
            coeffs.push(s.value[i]);
        }
        proof {
            lemma_cands_step(c, 0, i as int, i128::MIN as int);
        }
        i = i + 1;
    }
    Cands { rows, coeffs, thr: i128::MIN }
}

/// Byte equality of two slices of `len` bytes each.
fn slices_eq(x: &[u8], y: &[u8], len: usize) -> (r: bool)
    requires x@.len() == len, y@.len() == len,
    ensures r == (x@ == y@),
{
    let mut k: usize = 0;
    while k < len
        invariant
            x@.len() == len, y@.len() == len, k <= len,
            forall|q: int| 0 <= q < k ==> x@[q] == y@[q],
        decreases len - k,
    {
        if x[k] != y[k] {
            return false;
        }
        k = k + 1;
    }
    proof {
        assert(x@ =~= y@);
    }
    true
}

/// About the `target`-th largest coefficient (`1 <= target < coeffs.len()`), from an even sample when the list
/// is long.
fn zoom_threshold(coeffs: &Vec<i128>, target: usize) -> (r: i128)
    requires 1 <= target < coeffs@.len(),
{
    let len = coeffs.len();
    if len <= 2 * ZOOM_SAMPLE {
        return kth_largest(coeffs, target);
    }
    let step = len / ZOOM_SAMPLE;
    let mut sample: Vec<i128> = Vec::new();
    let mut k: usize = 0;
    while k < ZOOM_SAMPLE
        invariant
            len == coeffs@.len(), len > 2 * ZOOM_SAMPLE, step == len / ZOOM_SAMPLE, k <= ZOOM_SAMPLE,
            sample@.len() == k,
        decreases ZOOM_SAMPLE - k,
    {
        proof {
            assert(k * step < len) by (nonlinear_arith)
                requires k < ZOOM_SAMPLE, step == len / ZOOM_SAMPLE, len > 2 * ZOOM_SAMPLE;
        }
        sample.push(coeffs[k * step]);
        k = k + 1;
    }
    let mut t = target / step;
    if t < 1 {
        t = 1;
    }
    if t > ZOOM_SAMPLE {
        t = ZOOM_SAMPLE;
    }
    kth_largest(&sample, t)
}

/// The answer rows at threshold `t2` (`t2` returned): `cands(0, n, t2)` restricted to `body_ok`, with their
/// `sub` rows and coefficients.
pub open spec fn picked_ok(c: Ctx, b: (Vec<usize>, Vec<usize>, Vec<i128>, i128)) -> bool {
    &&& entries(c, b.0@, b.1@, b.2@, cands(c, 0, c.n, b.3 as int).filter(body_p(c)))
    &&& (b.0@.len() >= LIMIT || b.3 == i128::MIN)
}

/// The zoom: the answer rows at some threshold `t2 >= e.thr` with at least `LIMIT` rows or `t2 = i128::MIN`;
/// `None` (only when `e.thr > i128::MIN`) when even `t2 = e.thr` leaves fewer than `LIMIT` rows.
fn pick(e: &Cands, table: &SubTable, adsh: &TextCol, cols: &RankCols, Ghost(c): Ghost<Ctx>)
    -> (r: Option<(Vec<usize>, Vec<usize>, Vec<i128>, i128)>)
    requires
        ctx_ok(c),
        sub_key(c),
        table_wf(*table, c),
        adsh@ == adsh_view(c.np),
        cols.tag@ == tag_view(c.np),
        cols.name@ == sname_view(c.sp),
        cands_ok(*e, c),
    ensures
        r matches Some(b) ==> picked_ok(c, b),
        e.thr == i128::MIN ==> r is Some,
{
    let len = e.rows.len();
    let thr = e.thr;
    let mut target: usize = FIRST_TARGET;
    loop
        invariant
            ctx_ok(c),
            sub_key(c),
            table_wf(*table, c),
            adsh@ == adsh_view(c.np),
            cols.tag@ == tag_view(c.np),
            cols.name@ == sname_view(c.sp),
            cands_ok(*e, c),
            len == e.rows@.len(), len == e.coeffs@.len(),
            thr == e.thr,
            target >= 1,
        decreases len - (if target < len { target } else { len }),
    {
        let t2: i128 = if len <= target {
            thr
        } else {
            let x = zoom_threshold(&e.coeffs, target);
            if x > thr { x } else { thr }
        };
        let b = body_rows(&e.rows, &e.coeffs, thr, t2, table, adsh, cols, Ghost(c));
        if b.0.len() >= LIMIT || t2 == i128::MIN {
            return Some((b.0, b.1, b.2, t2));
        }
        if t2 == thr || len <= target {
            return None;
        }
        target = if target > len / 4 { len } else { target * 4 };
    }
}

/// The columns the query reads (whole parts).
pub struct Columns {
    pub uom: TextCol,
    pub value: &'static [i128],
    pub adsh: TextCol,
    pub tag: TextCol,
    pub sadsh: TextCol,
    pub sfy: &'static [i32],
    pub sfy_valid: &'static [u8],
    pub sname: TextCol,
}

pub open spec fn columns_ok(k: Columns, c: Ctx) -> bool {
    &&& k.uom@ == uom_view(c.np)
    &&& k.value@ == coeff_seq(c.np)
    &&& k.adsh@ == adsh_view(c.np)
    &&& k.tag@ == tag_view(c.np)
    &&& k.sadsh@ == sadsh_view(c.sp)
    &&& k.sfy@ == fy_seq(c.sp)
    &&& k.sfy_valid@ == fy_valid_seq(c.sp)
    &&& k.sname@ == sname_view(c.sp)
}

/// Read the whole parts the query uses.
#[verifier::spinoff_prover]
fn read_columns(stores: &mut Stores, n: usize, m: usize, Ghost(c): Ghost<Ctx>) -> (k: Columns)
    requires
        ctx_ok(c),
        c.np == old(stores)@.flat_num,
        c.sp == old(stores)@.flat_sub,
        c.n == n as int,
        c.m == m as int,
    ensures
        final(stores)@ == old(stores)@,
        columns_ok(k, c),
{
    proof {
        reveal(ctx_ok);
        lemma_num_text_wf(c);
    }
    let n1 = stores.flat_num.part_len(ni::UOM_OFFSETS);
    let m1 = stores.flat_sub.part_len(si::ADSH_OFFSETS);
    let uom_off = stores.flat_num.extent_i64(ni::UOM_OFFSETS, 0, n1);
    let uom_blen = stores.flat_num.part_len(ni::UOM_BYTES);
    let uom_bytes = stores.flat_num.extent_u8(ni::UOM_BYTES, 0, uom_blen);
    let value = stores.flat_num.extent_i128(ni::VALUE, 0, n);
    let adsh_off = stores.flat_num.extent_i64(ni::ADSH_OFFSETS, 0, n1);
    let adsh_blen = stores.flat_num.part_len(ni::ADSH_BYTES);
    let adsh_bytes = stores.flat_num.extent_u8(ni::ADSH_BYTES, 0, adsh_blen);
    let tag_off = stores.flat_num.extent_i64(ni::TAG_OFFSETS, 0, n1);
    let tag_blen = stores.flat_num.part_len(ni::TAG_BYTES);
    let tag_bytes = stores.flat_num.extent_u8(ni::TAG_BYTES, 0, tag_blen);
    let sadsh_off = stores.flat_sub.extent_i64(si::ADSH_OFFSETS, 0, m1);
    let sadsh_blen = stores.flat_sub.part_len(si::ADSH_BYTES);
    let sadsh_bytes = stores.flat_sub.extent_u8(si::ADSH_BYTES, 0, sadsh_blen);
    let sfy = stores.flat_sub.extent_i32(si::FY, 0, m);
    let sfy_valid = stores.flat_sub.extent_u8(si::FY_VALIDITY, 0, m);
    let sname_off = stores.flat_sub.extent_i64(si::NAME_OFFSETS, 0, m1);
    let sname_blen = stores.flat_sub.part_len(si::NAME_BYTES);
    let sname_bytes = stores.flat_sub.extent_u8(si::NAME_BYTES, 0, sname_blen);
    proof {
        assert(uom_off@ =~= uom_view(c.np).offsets);
        assert(uom_bytes@ =~= uom_view(c.np).bytes);
        assert(value@ =~= coeff_seq(c.np));
        assert(adsh_off@ =~= adsh_view(c.np).offsets);
        assert(adsh_bytes@ =~= adsh_view(c.np).bytes);
        assert(tag_off@ =~= tag_view(c.np).offsets);
        assert(tag_bytes@ =~= tag_view(c.np).bytes);
        assert(sadsh_off@ =~= sadsh_view(c.sp).offsets);
        assert(sadsh_bytes@ =~= sadsh_view(c.sp).bytes);
        assert(sfy@ =~= fy_seq(c.sp));
        assert(sfy_valid@ =~= fy_valid_seq(c.sp));
        assert(sname_off@ =~= sname_view(c.sp).offsets);
        assert(sname_bytes@ =~= sname_view(c.sp).bytes);
    }
    Columns {
        uom: TextCol { offsets: uom_off, bytes: uom_bytes },
        value,
        adsh: TextCol { offsets: adsh_off, bytes: adsh_bytes },
        tag: TextCol { offsets: tag_off, bytes: tag_bytes },
        sadsh: TextCol { offsets: sadsh_off, bytes: sadsh_bytes },
        sfy,
        sfy_valid,
        sname: TextCol { offsets: sname_off, bytes: sname_bytes },
    }
}

/// The produced rows are an allowed output for every database bound to the parts.
#[verifier::spinoff_prover]
proof fn lemma_final(sv: crate::gendb_entry::stores::StoresView, c: Ctx, ps: Seq<crate::spec::ast::Literal>,
    b: (Vec<usize>, Vec<usize>, Vec<i128>, i128), out: Vec<Vec<crate::exec::value::EVal>>)
    requires
        ctx_ok(c),
        c.np == sv.flat_num,
        c.sp == sv.flat_sub,
        lits_ok(c, ps[0], ps[1]),
        ps.len() == 2,
        picked_ok(c, b),
        view_rows(out@) == crate::spec::order::sort_rows(crate::agent::sem::order_keys(), ans_rows(c, b.0@, b.1@, b.2@)).take(
            if b.0@.len() < 100 { b.0@.len() as int } else { 100 }),
    ensures
        crate::gendb_entry::answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Rows(out))),
{
    assert forall|db2: crate::spec::value::Database| #[trigger] crate::gendb_entry::bound_db(sv, db2) implies
        crate::gendb_entry::outcome_ok(db2, crate::query::query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(out))) by {
        lemma_bound(sv, db2, c);
        lemma_answer(db2, c, ps, b.0@, b.1@, b.2@, b.3 as int, view_rows(out@));
    }
}

/// The context of the call is well formed, its `sub` key holds, and the binding is in range.
proof fn lemma_context(sv: crate::gendb_entry::stores::StoresView, db: crate::spec::value::Database, c: Ctx,
    nrels: Seq<Seq<crate::spec::value::Row>>, srels: Seq<Seq<crate::spec::value::Row>>, ps: Seq<crate::spec::ast::Literal>)
    requires
        crate::gendb_entry::bound_db(sv, db),
        nrels == crate::stores::flat_num::declaration::stored_relations(db),
        srels == crate::stores::flat_sub::declaration::stored_relations(db),
        c.np == sv.flat_num,
        c.sp == sv.flat_sub,
        c.n == nrels[0].len(),
        c.m == srels[0].len(),
        crate::query::param_domain(ps),
        ps == seq![crate::spec::ast::Literal::Text(c.pv), (crate::spec::ast::Literal::Int { v: c.fy, kind: crate::spec::int::IntKind::Int4 })],
    ensures
        ctx_ok(c),
        sub_key(c),
        lits_ok(c, ps[0], ps[1]),
{
    reveal(ctx_ok);
    assert(ni::parts_wf(c.np, c.n));
    assert(si::parts_wf(c.sp, c.m));
    lemma_bound(sv, db, c);
    lemma_lits(ps, c.pv, c.fy);
}

#[verifier::spinoff_prover]
pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        crate::gendb_entry::stores_ready(old(stores)@),
        crate::query::param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        crate::gendb_entry::answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost db = choose|db: crate::spec::value::Database| #[trigger] crate::gendb_entry::bound_db(stores@, db);
    let ghost nrels = crate::stores::flat_num::declaration::stored_relations(db);
    let ghost srels = crate::stores::flat_sub::declaration::stored_relations(db);
    let n = ni::stored_rows(&stores.flat_num, Ghost(nrels));
    let m = si::stored_rows(&stores.flat_sub, Ghost(srels));
    let fy = params.p1;
    let param: &'static [u8] = params.p0;
    let ghost c = Ctx { np: stores.flat_num@, n: n as int, sp: stores.flat_sub@, m: m as int, pv: param@, fy: fy as int };
    proof {
        lemma_context(sv, db, c, nrels, srels, params@);
        lemma_num_text_wf(c);
    }
    let k = read_columns(stores, n, m, Ghost(c));
    let scan = NumScan { uom: TextCol { offsets: k.uom.offsets, bytes: k.uom.bytes }, value: k.value };
    let cols = RankCols {
        tag: TextCol { offsets: k.tag.offsets, bytes: k.tag.bytes },
        name: TextCol { offsets: k.sname.offsets, bytes: k.sname.bytes },
    };
    let plan = plan_table(TextCol { offsets: k.sadsh.offsets, bytes: k.sadsh.bytes }, k.sfy, k.sfy_valid, m, fy, Ghost(c));
    let mut picked: Option<(Vec<usize>, Vec<usize>, Vec<i128>, i128)> = None;
    let table = match scan_parallel(&scan, param, n, workers, plan, dispatch, Ghost(c)) {
        Err(e) => return Err(QueryError::WorkerFailed(e)),
        Ok((None, t)) => t,
        Ok((Some(e), t)) => {
            picked = pick(&e, &t, &k.adsh, &cols, Ghost(c));
            t
        },
    };
    let b = match picked {
        Some(b) => b,
        None => {
            let e = scan_serial(&scan, param, n, Ghost(c));
            match pick(&e, &table, &k.adsh, &cols, Ghost(c)) {
                Some(b) => b,
                None => {
                    proof {
                        assert(false);
                    }
                    (Vec::new(), Vec::new(), Vec::new(), i128::MIN)
                },
            }
        },
    };
    let ghost bb = b;
    let (brows, bsubs, bcoeffs, t2) = b;
    proof {
        lemma_picked_bounds(c, bb);
    }
    let order = sort_positions(&brows, &bsubs, &bcoeffs, &cols, Ghost(n as int), Ghost(m as int), Ghost(c));
    let out = answer_rows(&order, &brows, &bsubs, &bcoeffs, &cols, LIMIT, Ghost(n as int), Ghost(m as int), Ghost(c));
    proof {
        lemma_final(sv, c, params@, bb, out);
    }
    Ok(Answer::Rows(out))
}

/// The picked rows are rows of `num` with rows of `sub`.
proof fn lemma_picked_bounds(c: Ctx, b: (Vec<usize>, Vec<usize>, Vec<i128>, i128))
    requires picked_ok(c, b),
    ensures
        b.0@.len() == b.1@.len(), b.0@.len() == b.2@.len(),
        forall|q: int| 0 <= q < b.0@.len() ==> #[trigger] b.0@[q] < c.n,
        forall|q: int| 0 <= q < b.1@.len() ==> #[trigger] b.1@[q] < c.m,
{
    let s = cands(c, 0, c.n, b.3 as int);
    let top = s.filter(body_p(c));
    assert forall|q: int| 0 <= q < b.0@.len() implies #[trigger] b.0@[q] < c.n by {
        lemma_filter_source(s, body_p(c), q);
        let j = choose|j: int| 0 <= j < s.len() && s[j] == top[q];
        lemma_cands_range(c, 0, c.n, b.3 as int, j);
    }
    assert forall|q: int| 0 <= q < b.1@.len() implies #[trigger] b.1@[q] < c.m by {
        assert(sub_match(c, top[q], b.1@[q] as int));
    }
}

} // verus!
