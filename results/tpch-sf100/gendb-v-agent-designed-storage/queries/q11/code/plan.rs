//! The fast plan, for partsupp stored sorted by ps_partkey (key index kind 1) and a supplier key range that fits a
//! flag array: flag the qualifying suppliers; estimate a pruning bound from sample ranges; scan aligned row ranges
//! in parallel (`tasks::ScanTask`: the range's groups with a SUM above the bound, sorted by SUM descending in the
//! task; a range whose group buffers were too small is rescanned on the calling thread with room for every row); add
//! the ranges' totals and masses (Capacity beyond `i128`); compute the HAVING threshold (rerun without pruning when
//! the bound was above it); collect each range's sorted prefix above the threshold in range order
//! (`collect::append_task`). The outcome (`plan_ok`) is either the result pairs (`finish::res_ok`, cut into
//! descending runs) or a proof that the statement leaves its capacity domain.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::numeric::abs;
use crate::link::expr::{fits_i128, i128_max};
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::QueryError;
use super::tables::*;
use super::nf::*;
use super::rows::*;
use super::groups::*;
use super::scan::*;
use super::supp::*;
use super::tasks::*;
use super::collect::*;
use super::finish::*;
use super::bitmap::*;
use super::common::msort::{runs_ok, desc, seg};

verus! {

/// Group buffers are allocated with at least this many slots (`i64`/`i128`: over 32 MiB), so the allocator maps fresh
/// zero pages for them instead of clearing reused memory on the calling thread; workers touch only the slots they
/// fill. `LAZY_PAIRS` is the same for `(i64, i128)` slots (32 bytes each).
pub const LAZY_SLOTS: usize = 4_200_000;
/// At most this many scan ranges (one per worker). Measured at 64 workers with the chunked mask kernel: 64 ranges
/// 33.7 ms, 48 ranges 34.5 ms, 32 ranges 38.6 ms.
pub const MAX_SCAN_TASKS: usize = 64;
pub const LAZY_PAIRS: usize = 1_100_000;

/// The statement leaves its capacity domain (`finish::lemma_final_cap`).
pub open spec fn cap_cond(t: Tabs, name: Seq<u8>, pc: int) -> bool {
    let n = n_of(t);
    tabs(t, name, 0, n) > i128_max()
        || (tabs(t, name, 0, n) <= i128_max() && tsum(t, name, 0, n) != 0 && !fits_i128(tsum(t, name, 0, n) * pc))
}

/// A plan's outcome: Capacity, or the result pairs.
pub struct PlanOut {
    pub cap: bool,
    pub res: Vec<(i64, i128)>,
    /// The result cut into descending runs.
    pub runs: Vec<usize>,
}

pub open spec fn plan_ok(t: Tabs, name: Seq<u8>, pc: int, o: PlanOut) -> bool {
    &&& o.cap ==> cap_cond(t, name, pc)
    &&& !o.cap ==> tabs(t, name, 0, n_of(t)) <= i128_max() && res_ok(t, name, o.res@, pc) && runs_ok(o.res@, o.runs@)
}

/// Sorted adjacent keys: all keys sorted.
proof fn lemma_sorted(c: PSCols, t: Tabs)
    requires pscols_ok(c, t.ps), tabs_typed(t), c.kind == 1,
    ensures sorted_rows(t, 0, n_of(t)),
{
    let n = n_of(t);
    assert forall|a: int, b: int| 0 <= a <= b < n implies #[trigger] rkey(t, a) <= #[trigger] rkey(t, b) by {
        lemma_sorted_step(c, t, a, b);
    }
}

proof fn lemma_sorted_step(c: PSCols, t: Tabs, a: int, b: int)
    requires pscols_ok(c, t.ps), tabs_typed(t), c.kind == 1, 0 <= a <= b < n_of(t),
    ensures rkey(t, a) <= rkey(t, b),
    decreases b - a,
{
    assert(ps_row_ok(c, t.ps[b], b));
    if a < b {
        lemma_sorted_step(c, t, a, b - 1);
        assert(ps_row_ok(c, t.ps[b - 1], b - 1));
        assert(fv32(c.key_c@, c.key_b@, c.bs as int, b - 1) <= fv32(c.key_c@, c.key_b@, c.bs as int, b - 1 + 1));
    }
}

/// A range's scan after the fix-up: its groups (also sorted by SUM in `out[0 .. m]`), or a mass beyond `i128`.
pub open spec fn fixed_ok(t: Tabs, name: Seq<u8>, lo: int, hi: int, lb: i128, o: TaskOut) -> bool {
    &&& o.s.status == SCAN_OK || o.s.status == SCAN_OVER
    &&& o.s.status == SCAN_OK ==> o.s.len <= o.s.keys@.len() && o.s.len <= o.s.sums@.len()
            && scan_ok(t, name, lo, hi, o.s.keys@, o.s.sums@, o.s.len as int, o.s.total, o.s.mass, lb)
            && sorted_out(o.s, o.out@, o.m as int, lb)
    &&& o.s.status == SCAN_OVER ==> tabs(t, name, lo, hi) > MAXM
}

/// The mass of a range bounds the whole table's.
proof fn lemma_mass_part(t: Tabs, name: Seq<u8>, n: int, lo: int, hi: int)
    requires 0 <= lo <= hi <= n,
    ensures tabs(t, name, 0, n) >= tabs(t, name, lo, hi),
{
    lemma_split(t, name, 0, 0, lo, n);
    lemma_split(t, name, 0, lo, hi, n);
    lemma_bounds(t, name, 0, 0, lo);
    lemma_bounds(t, name, 0, hi, n);
}

/// The scan tasks of the ranges `b[k] .. b[k + 1]`.
fn make_tasks(c: &PSCols, fla: &Arc<Vec<u8>>, smin: i64, range: usize, b: &Vec<usize>, nt: usize, lb: i128, touch: bool,
    bma: &Arc<Vec<u64>>, use_bm: bool, Ghost(t): Ghost<Tabs>, Ghost(name): Ghost<Seq<u8>>) -> (tasks: Vec<ScanTask>)
    requires
        1 <= nt <= MAX_WORKERS, c.n == n_of(t),
        bounds_ok(t, b@, nt as int, n_of(t)), scan_env(*c, fla@, smin, range, t, name),
        use_bm ==> bm_ok(bma@, c.n as int, t, name),
    ensures
        tasks@.len() == nt,
        forall|i: int| 0 <= i < nt ==> (#[trigger] tasks@[i]).pre() && tasks@[i].lo == b@[i] && tasks@[i].hi == b@[i + 1]
            && tasks@[i].t@ == t && tasks@[i].name@ == name && tasks@[i].lb == lb,
{
    hide(tabs);
    hide(tsum);
    hide(ksum);
    hide(kcnt);
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut k: usize = 0;
    while k < nt
        invariant
            1 <= nt <= MAX_WORKERS, k <= nt, c.n == n_of(t),
            bounds_ok(t, b@, nt as int, n_of(t)), scan_env(*c, fla@, smin, range, t, name),
            use_bm ==> bm_ok(bma@, c.n as int, t, name),
            tasks@.len() == k,
            forall|i: int| 0 <= i < k ==> (#[trigger] tasks@[i]).pre() && tasks@[i].lo == b@[i] && tasks@[i].hi == b@[i + 1]
                && tasks@[i].t@ == t && tasks@[i].name@ == name && tasks@[i].lb == lb,
        decreases nt - k,
    {
        let lo = b[k];
        let hi = b[k + 1];
        assert(b@[k as int] <= b@[k + 1]);
        proof { lemma_bound_le(t, b@, nt as int, n_of(t), k as int + 1); }
        // Without pruning every group is kept (about one per 27 rows); with pruning few groups pass the bound (a
        // range that overflows its buffers is rescanned). Either way the buffers are at least `LAZY_SLOTS` long, so
        // the allocator maps fresh zero pages (no clearing on the calling thread) and a worker touches only the slots
        // it fills.
        let want = if lb == i128::MIN { (hi - lo) / 12 + 1024 } else { (hi - lo) / 256 + 2048 };
        let cap = if want > LAZY_SLOTS { want } else { LAZY_SLOTS };
        let f2 = fla.clone();
        let b2 = bma.clone();
        tasks.push(ScanTask { c: *c, fl: f2, smin, range, lo, hi, keys: vec![0i64; cap], sums: vec![0i128; cap],
            out: vec![(0i64, 0i128); cap], tmp: vec![(0i64, 0i128); cap], mask: vec![0u64; CHUNK_WORDS], lb, touch, bm: b2, use_bm,
            t: Ghost(t), name: Ghost(name) });
        k = k + 1;
    }
    tasks
}

/// Rescans, on the calling thread, the ranges whose group buffers were too small (room for one group per row).
fn fix_scans(c: &PSCols, fl: &Vec<u8>, smin: i64, range: usize, b: &Vec<usize>, nt: usize, outs: &mut Vec<TaskOut>, lb: i128,
    touch: bool, bm: &Vec<u64>, use_bm: bool, Ghost(tk): Ghost<Seq<ScanTask>>, Ghost(t): Ghost<Tabs>, Ghost(name): Ghost<Seq<u8>>)
    requires
        1 <= nt <= MAX_WORKERS, c.n == n_of(t),
        bounds_ok(t, b@, nt as int, n_of(t)), scan_env(*c, fl@, smin, range, t, name),
        use_bm ==> bm_ok(bm@, c.n as int, t, name),
        old(outs)@.len() == nt, tk.len() == nt,
        forall|i: int| 0 <= i < nt ==> #[trigger] tk[i].lo == b@[i] && tk[i].hi == b@[i + 1] && tk[i].t@ == t && tk[i].name@ == name
            && tk[i].lb == lb,
        forall|i: int| 0 <= i < nt ==> #[trigger] tk[i].post(old(outs)@[i]),
    ensures
        final(outs)@.len() == nt,
        forall|i: int| 0 <= i < nt ==> fixed_ok(t, name, b@[i] as int, b@[i + 1] as int, lb, #[trigger] final(outs)@[i]),
{
    hide(tabs);
    hide(tsum);
    hide(ksum);
    hide(kcnt);
    hide(groups_ok);
    let ghost o0 = outs@;
    let mut k: usize = 0;
    while k < nt
        invariant
            1 <= nt <= MAX_WORKERS, k <= nt, c.n == n_of(t),
            bounds_ok(t, b@, nt as int, n_of(t)), scan_env(*c, fl@, smin, range, t, name),
            use_bm ==> bm_ok(bm@, c.n as int, t, name),
            outs@.len() == nt, tk.len() == nt, o0.len() == nt,
            forall|i: int| 0 <= i < nt ==> #[trigger] tk[i].lo == b@[i] && tk[i].hi == b@[i + 1] && tk[i].t@ == t && tk[i].name@ == name
                && tk[i].lb == lb,
            forall|i: int| 0 <= i < nt ==> #[trigger] tk[i].post(o0[i]),
            forall|i: int| k <= i < nt ==> #[trigger] outs@[i] == o0[i],
            forall|i: int| 0 <= i < k ==> fixed_ok(t, name, b@[i] as int, b@[i + 1] as int, lb, #[trigger] outs@[i]),
        decreases nt - k,
    {
        assert(tk[k as int].post(o0[k as int]));
        assert(outs@[k as int] == o0[k as int]);
        if outs[k].s.status == SCAN_FULL {
            let lo = b[k];
            let hi = b[k + 1];
            proof { lemma_bound_le(t, b@, nt as int, n_of(t), k as int + 1); }
            assert(b@[k as int] <= b@[k + 1]);
            let n = hi - lo;
            let mut mask: Vec<u64> = vec![0u64; CHUNK_WORDS];
            let o2 = scan_sort(c, fl, smin, range, lo, hi, vec![0i64; n], vec![0i128; n], vec![(0i64, 0i128); n],
                vec![(0i64, 0i128); n], lb, &mut mask, touch, bm, use_bm, Ghost(t), Ghost(name));
            crate::gendb_entry::work::put(outs, k, o2);
        }
        k = k + 1;
    }
}

/// The ranges' totals and masses: `(over, total, mass)`; `over` when some range's or the whole mass exceeds `i128`.
fn sum_scans(outs: &Vec<TaskOut>, b: &Vec<usize>, nt: usize, Ghost(lb): Ghost<i128>, Ghost(t): Ghost<Tabs>, Ghost(name): Ghost<Seq<u8>>)
    -> (r: (bool, i128, u128))
    requires
        1 <= nt <= MAX_WORKERS,
        bounds_ok(t, b@, nt as int, n_of(t)),
        outs@.len() == nt,
        forall|i: int| 0 <= i < nt ==> fixed_ok(t, name, b@[i] as int, b@[i + 1] as int, lb, #[trigger] outs@[i]),
    ensures
        r.0 ==> tabs(t, name, 0, n_of(t)) > i128_max(),
        !r.0 ==> r.1 as int == tsum(t, name, 0, n_of(t)) && r.2 as int == tabs(t, name, 0, n_of(t)) && r.2 <= MAXM
            && forall|i: int| 0 <= i < nt ==> (#[trigger] outs@[i]).s.status == SCAN_OK,
{
    hide(ksum);
    hide(kcnt);
    hide(groups_ok);
    let ghost n = n_of(t);
    assert(MAXM as int == i128_max());
    let mut total: i128 = 0;
    let mut mass: u128 = 0;
    let mut k: usize = 0;
    while k < nt
        invariant
            1 <= nt <= MAX_WORKERS, k <= nt, n == n_of(t),
            bounds_ok(t, b@, nt as int, n),
            outs@.len() == nt,
            forall|i: int| 0 <= i < nt ==> fixed_ok(t, name, b@[i] as int, b@[i + 1] as int, lb, #[trigger] outs@[i]),
            forall|i: int| 0 <= i < k ==> (#[trigger] outs@[i]).s.status == SCAN_OK,
            total as int == tsum(t, name, 0, b@[k as int] as int),
            mass as int == tabs(t, name, 0, b@[k as int] as int),
            mass <= MAXM,
            MAXM as int == i128_max(),
        decreases nt - k,
    {
        proof {
            lemma_bound_le(t, b@, nt as int, n, k as int + 1);
            assert(b@[k as int] <= b@[k + 1]);
            lemma_split(t, name, 0, 0, b@[k as int] as int, b@[k + 1] as int);
        }
        let o = &outs[k].s;
        assert(fixed_ok(t, name, b@[k as int] as int, b@[k + 1] as int, lb, outs@[k as int]));
        if o.status == SCAN_OVER {
            proof { lemma_mass_part(t, name, n, b@[k as int] as int, b@[k + 1] as int); }
            return (true, 0, 0);
        }
        if o.mass > MAXM - mass {
            proof { lemma_mass_part(t, name, n, 0, b@[k + 1] as int); }
            return (true, 0, 0);
        }
        proof {
            lemma_bounds(t, name, 0, 0, b@[k + 1] as int);
        }
        mass = mass + o.mass;
        total = total + o.total;
        k = k + 1;
    }
    assert(b@[nt as int] == n);
    (false, total, mass)
}

/// Collects, in range order, each range's sorted groups with a SUM above `thr` (a prefix of its `out`); returns
/// the pairs and their cut into the ranges' descending runs.
fn collect_all(outs: &Vec<TaskOut>, nt: usize, thr: i128, Ghost(b): Ghost<Seq<usize>>, Ghost(lb): Ghost<i128>,
    Ghost(t): Ghost<Tabs>, Ghost(name): Ghost<Seq<u8>>)
    -> (r: (Vec<(i64, i128)>, Vec<usize>))
    requires
        1 <= nt <= MAX_WORKERS, lb <= thr,
        sorted_rows(t, 0, n_of(t)), bounds_ok(t, b, nt as int, n_of(t)),
        outs@.len() == nt,
        forall|i: int| 0 <= i < nt ==> fixed_ok(t, name, b[i] as int, b[i + 1] as int, lb, #[trigger] outs@[i]),
        forall|i: int| 0 <= i < nt ==> (#[trigger] outs@[i]).s.status == SCAN_OK,
    ensures acc_ok(t, name, b, nt as int, r.0@, thr), runs_ok(r.0@, r.1@),
{
    hide(acc_ok);
    hide(ksum);
    hide(kcnt);
    hide(tsum);
    hide(tabs);
    let mut res: Vec<(i64, i128)> = Vec::new();
    let mut runs: Vec<usize> = Vec::new();
    runs.push(0);
    proof { reveal(acc_ok); lemma_acc_start(t, name, b, thr); }
    let mut k: usize = 0;
    while k < nt
        invariant
            1 <= nt <= MAX_WORKERS, k <= nt, lb <= thr,
            sorted_rows(t, 0, n_of(t)), bounds_ok(t, b, nt as int, n_of(t)),
            outs@.len() == nt,
            forall|i: int| 0 <= i < nt ==> fixed_ok(t, name, b[i] as int, b[i + 1] as int, lb, #[trigger] outs@[i]),
            forall|i: int| 0 <= i < nt ==> (#[trigger] outs@[i]).s.status == SCAN_OK,
            acc_ok(t, name, b, k as int, res@, thr),
            runs@.len() == k + 1, runs@[0] == 0, runs@[k as int] == res@.len(),
            forall|i: int| 0 <= i < k ==> #[trigger] runs@[i] <= runs@[i + 1],
            forall|i: int| 0 <= i < k ==> desc(#[trigger] seg(res@, runs@[i] as int, runs@[i + 1] as int)),
        decreases nt - k,
    {
        let o = &outs[k];
        assert(fixed_ok(t, name, b[k as int] as int, b[k + 1] as int, lb, outs@[k as int]));
        let ghost g = o.s;
        let ghost r0 = res@;
        assert(scan_ok(t, name, b[k as int] as int, b[k + 1] as int, g.keys@, g.sums@, g.len as int, g.total, g.mass, lb));
        let mk = prefix_above(&o.out, o.m, thr);
        proof {
            let full = o.out@.subrange(0, o.m as int);
            assert(groups_ok(t, name, b[k as int] as int, b[k + 1] as int, g.keys@, g.sums@, g.len as int, lb));
            assert forall|x: int| 0 <= x < mk implies #[trigger] full[x].1 > thr by {
                assert(full[x] == o.out@[x]);
            }
            if mk < o.m {
                assert(full[mk as int] == o.out@[mk as int]);
            }
            lemma_prefix_filt(g.keys@, g.sums@, g.len as int, lb, thr, full, mk as int);
            assert(full.subrange(0, mk as int) =~= o.out@.subrange(0, mk as int));
        }
        append_task(&mut res, &o.out, mk, Ghost(t), Ghost(name), Ghost(b), Ghost(nt as int), Ghost(k as int),
            Ghost(g.keys@), Ghost(g.sums@), Ghost(g.len as int), Ghost(thr), Ghost(lb));
        proof {
            let p = o.out@.subrange(0, mk as int);
            assert(seg(res@, r0.len() as int, res@.len() as int) =~= p);
            assert(desc(p)) by {
                let full = o.out@.subrange(0, o.m as int);
                assert forall|x: int, y: int| 0 <= x < y < p.len() implies #[trigger] p[x].1 >= #[trigger] p[y].1 by {
                    assert(p[x] == full[x] && p[y] == full[y]);
                }
            }
            assert forall|i: int| 0 <= i < k implies desc(#[trigger] seg(res@, runs@[i] as int, runs@[i + 1] as int)) by {
                lemma_runs_prefix(runs@, k as int, i);
                assert(seg(res@, runs@[i] as int, runs@[i + 1] as int) =~= seg(r0, runs@[i] as int, runs@[i + 1] as int));
            }
        }
        runs.push(res.len());
        k = k + 1;
    }
    (res, runs)
}

/// Bounds below the last stay below it.
proof fn lemma_runs_prefix(runs: Seq<usize>, k: int, i: int)
    requires 0 <= i < k < runs.len(), forall|x: int| 0 <= x < k ==> #[trigger] runs[x] <= runs[x + 1],
    ensures runs[i + 1] <= runs[k],
    decreases k - i,
{
    if i + 1 < k {
        lemma_runs_prefix(runs, k, i + 1);
    }
}

/// The scans, totals, filters and collection over the ranges `b` with the pruning bound `lb`. `None` when the HAVING
/// threshold turned out below `lb` (some dropped group might pass): the caller reruns with `lb = i128::MIN`.
fn run_ranges(c: &Cols, fla: &Arc<Vec<u8>>, smin: i64, range: usize, b: &Vec<usize>, nt: usize, p1: i128, lb: i128, touch: bool,
    bma: &Arc<Vec<u64>>, use_bm: bool, dispatch: &mut Dispatch, Ghost(t): Ghost<Tabs>, Ghost(name): Ghost<Seq<u8>>)
    -> (r: Result<Option<PlanOut>, QueryError>)
    requires
        use_bm ==> bm_ok(bma@, c.ps.n as int, t, name),
        cols_ok(*c, t), tabs_typed(t), keys_unique(t),
        sorted_rows(t, 0, n_of(t)),
        scan_env(c.ps, fla@, smin, range, t, name),
        1 <= nt <= MAX_WORKERS,
        bounds_ok(t, b@, nt as int, n_of(t)),
    ensures
        r matches Ok(Some(o)) ==> plan_ok(t, name, p1 as int, o),
        r matches Ok(None) ==> lb > i128::MIN,
        r matches Err(e) ==> e is WorkerFailed,
{
    hide(ksum);
    hide(kcnt);
    hide(res_ok);
    let tasks = make_tasks(&c.ps, fla, smin, range, b, nt, lb, touch, bma, use_bm, Ghost(t), Ghost(name));
    let ghost tk = tasks@;
    let mut outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(f) => { return Err(QueryError::WorkerFailed(f)); },
    };
    fix_scans(&c.ps, &**fla, smin, range, b, nt, &mut outs, lb, touch, &**bma, use_bm, Ghost(tk), Ghost(t), Ghost(name));
    let (over, total, mass) = sum_scans(&outs, b, nt, Ghost(lb), Ghost(t), Ghost(name));
    if over {
        return Ok(Some(PlanOut { cap: true, res: Vec::new(), runs: Vec::new() }));
    }
    assert(MAXM as int == i128_max());
    // The HAVING threshold: `S > thr` exactly when `S * 10^10 > T * $2`.
    let x = match total.checked_mul(p1) {
        Some(x) => x,
        None => {
            assert(total != 0);
            return Ok(Some(PlanOut { cap: true, res: Vec::new(), runs: Vec::new() }));
        },
    };
    let thr = thr_of(x);
    if thr < lb {
        return Ok(None);
    }
    let (res, runs) = collect_all(&outs, nt, thr, Ghost(b@), Ghost(lb), Ghost(t), Ghost(name));
    proof {
        lemma_acc_end(t, name, b@, nt as int, res@, thr, p1 as int);
    }
    Ok(Some(PlanOut { cap: false, res, runs }))
}

/// Sample row ranges of the pruning bound estimate, and their length in rows (65536 rows: about 2600 qualifying
/// rows, an estimate within about 2.6% (one standard deviation) of the threshold against the bound's 12.5% margin).
/// Fewer samples shorten the serial setup before the scan (measured: 32 ranges took about 0.8 ms).
pub const SAMPLES: usize = 8;
pub const SAMPLE_ROWS: usize = 8192;

/// A pruning bound for the HAVING threshold, estimated from the totals of `SAMPLES` sample row ranges (7/8 of the
/// estimated threshold; `i128::MIN`, no pruning, for small tables or a non-positive estimate). Any value is sound:
/// `run_ranges` checks the bound against the exact threshold (and reruns without pruning when it was too high).
fn sample_bound(c: &PSCols, fl: &Vec<u8>, smin: i64, range: usize, p1: i128, Ghost(t): Ghost<Tabs>, Ghost(name): Ghost<Seq<u8>>)
    -> (lb: i128)
    requires scan_env(*c, fl@, smin, range, t, name),
{
    let n = c.n;
    let len: usize = SAMPLE_ROWS;
    if n < 64 * len {
        return i128::MIN;
    }
    let step = n / SAMPLES;
    let mut mask: Vec<u64> = vec![0u64; CHUNK_WORDS];
    let none: Vec<u64> = Vec::new();
    let mut tot: i128 = 0;
    let mut k: usize = 0;
    while k < SAMPLES
        invariant scan_env(*c, fl@, smin, range, t, name), n == c.n, n >= 64 * len, len == SAMPLE_ROWS, step == n / SAMPLES,
            k <= SAMPLES, mask@.len() == CHUNK_WORDS,
            -(k as int) * 0x1_0000_0000_0000_0000_0000_0000_0000 <= tot <= (k as int) * 0x1_0000_0000_0000_0000_0000_0000_0000,
        decreases SAMPLES - k,
    {
        proof {
            assert(step * k + len <= n) by (nonlinear_arith) requires step == n / 8, k < 8, n >= 64 * 8192, len == 8192;
        }
        let lo = step * k;
        let o = scan_one(c, fl, smin, range, lo, lo + len, Vec::new(), Vec::new(), i128::MAX, &mut mask, false, &none, false,
            Ghost(t), Ghost(name));
        if o.status != SCAN_OK {
            return i128::MIN;
        }
        // Each sample total is below 2^113 per row times 8192 rows.
        if o.total > 0x1_0000_0000_0000_0000_0000_0000_0000 || o.total < -0x1_0000_0000_0000_0000_0000_0000_0000 {
            return i128::MIN;
        }
        tot = tot + o.total;
        k = k + 1;
    }
    let per_row = tot / (SAMPLES * len) as i128;
    let est = match per_row.checked_mul(n as i128) {
        Some(e) => e,
        None => { return i128::MIN; },
    };
    let x = match est.checked_mul(p1) {
        Some(x) => x,
        None => { return i128::MIN; },
    };
    let thr = thr_of(x);
    if thr <= 0 {
        return i128::MIN;
    }
    thr - thr / 8
}

/// The fast plan.
pub fn fast_plan(c: &Cols, ix: &SuppIdx, nk: &Vec<i64>, smin: i64, range: usize, p1: i128, workers: usize,
    dispatch: &mut Dispatch, Ghost(t): Ghost<Tabs>, Ghost(name): Ghost<Seq<u8>>) -> (r: Result<PlanOut, QueryError>)
    requires
        idx_ok(*ix, t),
        cols_ok(*c, t), tabs_typed(t), keys_unique(t), nkeys_ok(t, name, nk@),
        c.ps.kind == 1,
        range < RANGE_LIM,
        forall|j: int| 0 <= j < t.s.len() ==> smin <= #[trigger] crate::link::expr::ival(t.s[j][0]) < smin + range,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(o) ==> plan_ok(t, name, p1 as int, o),
        r matches Err(e) ==> e is WorkerFailed,
{
    hide(ksum);
    hide(kcnt);
    hide(res_ok);
    proof { lemma_sorted(c.ps, t); }
    let fl = supplier_flags(&c.s, nk, smin, range, Ghost(t), Ghost(name));
    let fla: Arc<Vec<u8>> = Arc::new(fl);
    assert(scan_env(c.ps, fla@, smin, range, t, name));
    let np = c.ps.n;
    let nt: usize = if np < 1_000_000 { 1 } else if workers > MAX_SCAN_TASKS { MAX_SCAN_TASKS } else { workers };
    // Touching the payload lines early pays off while a few threads leave memory bandwidth idle (measured: one thread
    // -18%, 32 threads +5% in the scan).
    let touch = nt < 32;
    // One thread: mark the qualifying rows from the ps_suppkey index (about 3.2M rows of 80M) instead of a flag
    // lookup per row; many threads share the memory bandwidth and scan the supplier codes in parallel.
    let use_bm = nt == 1 && ix.ok;
    let bm: Vec<u64> = if use_bm { row_bitmap(ix, &*fla, smin, range, np, Ghost(t), Ghost(name)) } else { Vec::new() };
    let bma: Arc<Vec<u64>> = Arc::new(bm);
    let b = task_bounds(&c.ps, nt, Ghost(t));
    let lb = sample_bound(&c.ps, &*fla, smin, range, p1, Ghost(t), Ghost(name));
    match run_ranges(c, &fla, smin, range, &b, nt, p1, lb, touch, &bma, use_bm, dispatch, Ghost(t), Ghost(name)) {
        Err(e) => Err(e),
        Ok(Some(o)) => Ok(o),
        Ok(None) => {
            // The bound was above the exact threshold: rerun keeping every group.
            match run_ranges(c, &fla, smin, range, &b, nt, p1, i128::MIN, touch, &bma, use_bm, dispatch, Ghost(t), Ghost(name)) {
                Err(e) => Err(e),
                Ok(Some(o)) => Ok(o),
                Ok(None) => {
                    assert(false);
                    Err(QueryError::Malformed)
                },
            }
        },
    }
}

/// Every bound is at most `n`.
proof fn lemma_bound_le(t: Tabs, b: Seq<usize>, nt: int, n: int, k: int)
    requires bounds_ok(t, b, nt, n), 0 <= k <= nt,
    ensures b[k] <= n,
    decreases nt - k,
{
    if k < nt {
        lemma_bound_le(t, b, nt, n, k + 1);
        assert(b[k] <= b[k + 1]);
    }
}

} // verus!
