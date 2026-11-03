//! Per-chunk accumulation over the sub-runs of `pre` (one worker task per chunk of sub-runs `[lo, hi)`): for every
//! live group code `g` (non-NULL stmt), the rows (`runs::run_rows`), the sub-runs (`runs::run_count`, the distinct
//! filings of the group) and the exact line sum (`runs::run_vals`). Groups that are not live keep 0 and their
//! lines are never read.
use vstd::prelude::*;
use crate::gendb_entry::parallel::{Dispatch, WorkerTask, fork_join, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::gendb_entry::work::{filled, put};
use crate::stores::pre::interface::common::text::subslice;
use super::runs::*;

verus! {

/// Largest block summed in `i64`: `2^30` values of at most `2^31` in absolute value stay below `2^61`.
pub const BLOCK: usize = 0x4000_0000;

/// Exact sum of `line[a..b)`, in `i64` blocks of at most `BLOCK` values added into an `i128`.
pub fn line_sum(line: &'static [i32], a: usize, b: usize) -> (r: i128)
    requires a <= b <= line@.len(), b - a <= 0x1_0000_0000_0000_0000,
    ensures r as int == line_total(line@, a as int, b as int),
    no_unwind
{
    let ghost l = line@;
    let mut total: i128 = 0;
    let mut lo = a;
    proof { lemma_line_total_bound(l, a as int, b as int); }
    while lo < b
        invariant
            a <= lo <= b <= l.len(), l == line@, b - a <= 0x1_0000_0000_0000_0000,
            total as int == line_total(l, a as int, lo as int),
        decreases b - lo,
    {
        let hi = if b - lo > BLOCK { lo + BLOCK } else { b };
        let s = subslice(line, lo, hi);
        let m = hi - lo;
        let mut acc: i64 = 0;
        let mut i: usize = 0;
        while i < m
            invariant
                i <= m, m == hi - lo, m <= BLOCK, lo + m <= l.len(), s@ == l.subrange(lo as int, hi as int),
                acc as int == line_total(l, lo as int, lo + i),
                -0x8000_0000 * i <= acc <= 0x8000_0000 * i,
            decreases m - i,
        {
            proof {
                assert(s@[i as int] == l[lo + i]);
                assert(line_total(l, lo as int, lo + i + 1) == line_total(l, lo as int, lo + i) + l[lo + i] as int);
            }
            acc = acc + s[i] as i64;
            i = i + 1;
        }
        proof {
            lemma_line_total_split(l, a as int, lo as int, hi as int);
            lemma_line_total_bound(l, a as int, hi as int);
            assert(0x8000_0000 * (hi - a) <= 0x8000_0000 * 0x1_0000_0000_0000_0000int) by (nonlinear_arith)
                requires hi - a <= 0x1_0000_0000_0000_0000int;
        }
        total = total + acc as i128;
        lo = hi;
    }
    total
}

/// Width (rows) of the blocks `run_sum` reads at once: full blocks inside the run, then one masked block.
pub const W: usize = 32;

/// `line_total(l, p, p + min(j, len))`: the masked prefix of one block.
pub open spec fn masked_total(l: Seq<i32>, p: int, j: int, len: int) -> int {
    line_total(l, p, p + if j < len { j } else { len })
}

/// Exact sum of `line[a..b)` for a run of at most `BLOCK` rows, branch-light: full blocks of `W` rows, then the
/// tail as one block of `W` rows with the rows past `b` masked to 0 (when `W` rows remain in `line`).
#[inline(always)]
pub fn run_sum(line: &'static [i32], n: usize, a: usize, b: usize) -> (r: i64)
    requires a <= b <= n, n == line@.len(), b - a <= BLOCK,
    ensures r as int == line_total(line@, a as int, b as int),
    no_unwind
{
    let ghost l = line@;
    let mut acc: i64 = 0;
    let mut p = a;
    while b - p >= W
        invariant
            a <= p <= b <= n, n == l.len(), l == line@, b - a <= BLOCK,
            acc as int == line_total(l, a as int, p as int),
            -0x8000_0000 * (p - a) <= acc <= 0x8000_0000 * (p - a),
        decreases b - p,
    {
        let blk = subslice(line, p, p + W);
        let mut j: usize = 0;
        while j < W
            invariant
                j <= W, p + W <= b <= n, n == l.len(), l == line@, a <= p, b - a <= BLOCK,
                blk@ == l.subrange(p as int, p + W),
                acc as int == line_total(l, a as int, p + j),
                -0x8000_0000 * (p + j - a) <= acc <= 0x8000_0000 * (p + j - a),
            decreases W - j,
        {
            proof { assert(blk@[j as int] == l[p + j]); }
            acc = acc + blk[j] as i64;
            j = j + 1;
        }
        p = p + W;
    }
    if n - p >= W {
        let len = b - p;
        let blk = subslice(line, p, p + W);
        let mut t: i64 = 0;
        let mut j: usize = 0;
        while j < W
            invariant
                j <= W, p + W <= n, n == l.len(), l == line@, len == b - p, len < W,
                blk@ == l.subrange(p as int, p + W),
                t as int == masked_total(l, p as int, j as int, len as int),
                -0x8000_0000 * j <= t <= 0x8000_0000 * j,
            decreases W - j,
        {
            proof {
                assert(blk@[j as int] == l[p + j]);
            }
            let v = blk[j] as i64;
            t = t + if j < len { v } else { 0 };
            j = j + 1;
        }
        proof {
            lemma_line_total_split(l, a as int, p as int, b as int);
        }
        acc + t
    } else {
        while p < b
            invariant
                a <= p <= b <= n, n == l.len(), l == line@, b - a <= BLOCK,
                acc as int == line_total(l, a as int, p as int),
                -0x8000_0000 * (p - a) <= acc <= 0x8000_0000 * (p - a),
            decreases b - p,
        {
            acc = acc + line[p] as i64;
            p = p + 1;
        }
        acc
    }
}

/// The facts a chunk task needs about the run layout: `ns` runs with strictly increasing starts over the `line`
/// rows, every group code below `ng`.
pub open spec fn layout_ok(start: Seq<u64>, sub_group: Seq<u64>, line: Seq<i32>, ns: int, ng: int) -> bool {
    &&& starts_ok(start, ns)
    &&& start[0] == 0
    &&& sub_group.len() == ns
    &&& line.len() == start[ns]
    &&& forall|s: int| 0 <= s < ns ==> #[trigger] sub_group[s] < ng
}

/// One chunk `[lo, hi)` of sub-runs and its zeroed per-group outputs.
pub struct ChunkTask {
    pub start: &'static [u64],
    pub sub_group: &'static [u64],
    pub line: &'static [i32],
    pub live: Vec<bool>,
    pub ns: usize,
    pub ng: usize,
    pub nrows: usize,
    pub lo: usize,
    pub hi: usize,
    pub cnt: Vec<u64>,
    pub nf: Vec<u64>,
    pub sum: Vec<i128>,
}

/// The chunk outputs of runs `[lo, hi)`: per live group, rows, runs and line sum.
pub open spec fn chunk_out_ok(start: Seq<u64>, sub_group: Seq<u64>, line: Seq<i32>, live: Seq<bool>, ng: int,
    lo: int, hi: int, cnt: Seq<u64>, nf: Seq<u64>, sum: Seq<i128>) -> bool
{
    &&& cnt.len() == ng && nf.len() == ng && sum.len() == ng
    &&& forall|g: int| 0 <= g < ng && #[trigger] live[g] ==> {
        &&& cnt[g] as int == run_rows(start, sub_group, g, lo, hi)
        &&& nf[g] as int == run_count(sub_group, g, lo, hi)
        &&& sum[g] as int == run_vals(start, sub_group, line, g, lo, hi)
    }
}

impl WorkerTask for ChunkTask {
    type Output = (Vec<u64>, Vec<u64>, Vec<i128>);

    open spec fn pre(&self) -> bool {
        &&& layout_ok(self.start@, self.sub_group@, self.line@, self.ns as int, self.ng as int)
        &&& self.live@.len() == self.ng
        &&& self.line@.len() == self.nrows
        &&& self.lo <= self.hi <= self.ns
        &&& self.cnt@ == Seq::new(self.ng as nat, |_i: int| 0u64)
        &&& self.nf@ == Seq::new(self.ng as nat, |_i: int| 0u64)
        &&& self.sum@ == Seq::new(self.ng as nat, |_i: int| 0i128)
    }

    open spec fn post(&self, out: Self::Output) -> bool {
        chunk_out_ok(self.start@, self.sub_group@, self.line@, self.live@, self.ng as int, self.lo as int,
            self.hi as int, out.0@, out.1@, out.2@)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: Self::Output) {
        let ghost (st, sg, l, lv) = (self.start@, self.sub_group@, self.line@, self.live@);
        let ghost (ns, ng, lo) = (self.ns as int, self.ng as int, self.lo as int);
        let mut cnt = self.cnt;
        let mut nf = self.nf;
        let mut sum = self.sum;
        let mut s = self.lo;
        while s < self.hi
            invariant
                self.pre(), st == self.start@, sg == self.sub_group@, l == self.line@, lv == self.live@,
                ns == self.ns, ng == self.ng, lo == self.lo, lo <= s <= self.hi,
                chunk_out_ok(st, sg, l, lv, ng, lo, s as int, cnt@, nf@, sum@),
            decreases self.hi - s,
        {
            let g = self.sub_group[s] as usize;
            proof {
                assert(sg[s as int] < ng);
                assert forall|h: int| 0 <= h < ng implies
                    run_rows(st, sg, h, lo, s + 1) == run_rows(st, sg, h, lo, s as int) + if sg[s as int] == h { st[s + 1] - st[s as int] } else { 0 }
                    && run_count(sg, h, lo, s + 1) == run_count(sg, h, lo, s as int) + if sg[s as int] == h { 1int } else { 0 }
                    && run_vals(st, sg, l, h, lo, s + 1) == run_vals(st, sg, l, h, lo, s as int)
                        + if sg[s as int] == h { line_total(l, st[s as int] as int, st[s + 1] as int) } else { 0 } by {}
            }
            if self.live[g] {
                let a = self.start[s] as usize;
                let b = self.start[s + 1] as usize;
                proof {
                    assert(st[s as int] < st[s + 1]);
                    assert(st[s + 1] <= st[ns]) by { if s + 1 < ns { assert(st[s + 1] < st[ns]); } }
                    lemma_runs_bound(st, sg, l, ns, g as int, lo, s + 1);
                    if lo > 0 { assert(st[0] < st[lo]); }
                    assert(0x8000_0000 * (st[s + 1] - st[lo]) <= 0x8000_0000 * 0x1_0000_0000_0000_0000int) by (nonlinear_arith)
                        requires st[s + 1] - st[lo] <= 0x1_0000_0000_0000_0000int;
                    assert(-0x8000_0000 * (st[s + 1] - st[lo]) >= -0x8000_0000 * 0x1_0000_0000_0000_0000int) by (nonlinear_arith)
                        requires st[s + 1] - st[lo] <= 0x1_0000_0000_0000_0000int;
                    assert(sg[s as int] == g as int);
                    assert(sum@[g as int] as int == run_vals(st, sg, l, g as int, lo, s as int));
                    assert(run_vals(st, sg, l, g as int, lo, s + 1) == run_vals(st, sg, l, g as int, lo, s as int)
                        + line_total(l, st[s as int] as int, st[s + 1] as int));
                }
                let c = cnt[g] + (b - a) as u64;
                put(&mut cnt, g, c);
                let f = nf[g] + 1;
                put(&mut nf, g, f);
                let x = sum[g] + if b - a <= BLOCK { run_sum(self.line, self.nrows, a, b) as i128 } else { line_sum(self.line, a, b) };
                put(&mut sum, g, x);
            }
            s = s + 1;
        }
        (cnt, nf, sum)
    }
}

/// Largest number of chunk tasks of one call.
pub const MAX_TASKS: usize = 32;

/// Below this many rows one serial chunk is faster than spawning threads.
pub const SERIAL_ROWS: usize = 200_000;

/// `live[g]`: group code `g` has a non-NULL stmt key.
pub fn live_flags(group_stmt: &'static [u64], ng: usize) -> (v: Vec<bool>)
    requires group_stmt@.len() == ng,
    ensures v@.len() == ng, forall|g: int| 0 <= g < ng ==> #[trigger] v@[g] == (group_stmt@[g] != 0),
{
    let mut v: Vec<bool> = filled(ng, false);
    let mut g: usize = 0;
    while g < ng
        invariant
            g <= ng, v@.len() == ng, group_stmt@.len() == ng,
            forall|h: int| 0 <= h < g ==> #[trigger] v@[h] == (group_stmt@[h] != 0),
        decreases ng - g,
    {
        put(&mut v, g, group_stmt[g] != 0);
        g = g + 1;
    }
    v
}

/// Boundary `k` of the chunks `tv`: 0, then the end of each chunk.
pub open spec fn bound_at(tv: Seq<ChunkTask>, k: int) -> int {
    if k == 0 { 0 } else { tv[k - 1].hi as int }
}

/// The chunks cover the sub-runs `[0, ns)` in order, each over the same layout.
pub open spec fn chunks_ok(tv: Seq<ChunkTask>, start: Seq<u64>, sub_group: Seq<u64>, line: Seq<i32>,
    live: Seq<bool>, ns: int, ng: int) -> bool
{
    &&& forall|k: int| 0 <= k < tv.len() ==> {
        &&& #[trigger] tv[k].pre()
        &&& tv[k].start@ == start && tv[k].sub_group@ == sub_group && tv[k].line@ == line
        &&& tv[k].live@ == live && tv[k].ng == ng
        &&& tv[k].lo == bound_at(tv, k)
    }
    &&& tv.len() > 0 ==> tv[tv.len() - 1].hi == ns
}

/// One task run on the calling thread (no thread spawned): the output vector `fork_join` would return.
fn run_here(tasks: Vec<ChunkTask>) -> (outs: Vec<(Vec<u64>, Vec<u64>, Vec<i128>)>)
    requires tasks@.len() == 1, tasks@[0].pre(),
    ensures outs@.len() == 1, tasks@[0].post(outs@[0]),
{
    let mut tasks = tasks;
    let task = tasks.pop().unwrap();
    let out = task.run();
    let mut outs = Vec::new();
    outs.push(out);
    outs
}

/// Per live group: rows, sub-runs and exact line sum of all sub-runs, computed by up to `workers` chunk tasks
/// and merged on the calling thread.
pub fn accumulate(start: &'static [u64], sub_group: &'static [u64], line: &'static [i32],
    group_stmt: &'static [u64], ns: usize, ng: usize, n: usize, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<(Vec<u64>, Vec<u64>, Vec<i128>), WorkerFailure>)
    requires
        layout_ok(start@, sub_group@, line@, ns as int, ng as int),
        line@.len() == n,
        group_stmt@.len() == ng,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(o) ==> chunk_out_ok(start@, sub_group@, line@, Seq::new(ng as nat, |g: int| group_stmt@[g] != 0),
            ng as int, 0, ns as int, o.0@, o.1@, o.2@),
{
    let ghost live_s = Seq::new(ng as nat, |g: int| group_stmt@[g] != 0);
    let tasks_n: usize = if n < SERIAL_ROWS || ns == 0 { 1 } else if workers < MAX_TASKS { workers } else { MAX_TASKS };
    let chunk = ns / tasks_n;
    let mut tasks: Vec<ChunkTask> = Vec::new();
    let mut lo: usize = 0;
    let mut t: usize = 0;
    while t < tasks_n
        invariant
            1 <= tasks_n <= MAX_WORKERS, t <= tasks_n, tasks@.len() == t, lo <= ns,
            layout_ok(start@, sub_group@, line@, ns as int, ng as int), line@.len() == n, group_stmt@.len() == ng,
            live_s == Seq::new(ng as nat, |g: int| group_stmt@[g] != 0),
            forall|k: int| 0 <= k < tasks@.len() ==> {
                &&& #[trigger] tasks@[k].pre()
                &&& tasks@[k].start@ == start@ && tasks@[k].sub_group@ == sub_group@ && tasks@[k].line@ == line@
                &&& tasks@[k].live@ == live_s && tasks@[k].ng == ng
                &&& tasks@[k].lo == bound_at(tasks@, k)
            },
            lo == bound_at(tasks@, t as int),
            forall|k: int| 0 <= k < tasks@.len() && k + 1 == tasks_n ==> #[trigger] tasks@[k].hi == ns,
        decreases tasks_n - t,
    {
        let hi = if t + 1 == tasks_n || ns - lo < chunk { ns } else { lo + chunk };
        let live = live_flags(group_stmt, ng);
        assert(live@ =~= live_s);
        let task = ChunkTask {
            start, sub_group, line, live, ns, ng, nrows: n, lo, hi,
            cnt: filled(ng, 0u64), nf: filled(ng, 0u64), sum: filled(ng, 0i128),
        };
        let ghost before = tasks@;
        tasks.push(task);
        proof {
            assert(tasks@[t as int] == task);
            assert forall|k: int| 0 <= k < tasks@.len() implies tasks@[k].lo == bound_at(tasks@, k) by {
                if k < t { assert(tasks@[k] == before[k]); assert(before[k].pre()); }
                if 0 < k <= t { assert(tasks@[k - 1] == before[k - 1]); }
            }
            assert(bound_at(tasks@, t + 1) == hi);
            assert forall|k: int| 0 <= k < tasks@.len() && k + 1 == tasks_n implies #[trigger] tasks@[k].hi == ns by {
                if k < t { assert(tasks@[k] == before[k]); }
            }
        }
        lo = hi;
        t = t + 1;
    }
    let ghost tv = tasks@;
    assert(tv[tasks_n - 1].hi == ns);
    assert(chunks_ok(tv, start@, sub_group@, line@, live_s, ns as int, ng as int));
    let outs = if tasks_n == 1 {
        run_here(tasks)
    } else {
        match fork_join(dispatch, tasks) {
            Ok(o) => o,
            Err(e) => return Err(e),
        }
    };
    let nt = outs.len();
    let mut cnt: Vec<u64> = filled(ng, 0u64);
    let mut nf: Vec<u64> = filled(ng, 0u64);
    let mut sum: Vec<i128> = filled(ng, 0i128);
    let mut g: usize = 0;
    while g < ng
        invariant
            g <= ng, nt == tv.len(), nt == outs@.len(), nt >= 1,
            layout_ok(start@, sub_group@, line@, ns as int, ng as int), line@.len() == n,
            chunks_ok(tv, start@, sub_group@, line@, live_s, ns as int, ng as int),
            forall|k: int| 0 <= k < nt ==> #[trigger] tv[k].post(outs@[k]),
            cnt@.len() == ng, nf@.len() == ng, sum@.len() == ng,
            live_s == Seq::new(ng as nat, |h: int| group_stmt@[h] != 0), group_stmt@.len() == ng,
            forall|h: int| 0 <= h < g && #[trigger] live_s[h] ==> {
                &&& cnt@[h] as int == run_rows(start@, sub_group@, h, 0, ns as int)
                &&& nf@[h] as int == run_count(sub_group@, h, 0, ns as int)
                &&& sum@[h] as int == run_vals(start@, sub_group@, line@, h, 0, ns as int)
            },
        decreases ng - g,
    {
        if group_stmt[g] != 0 {
            let ghost gi = g as int;
            let mut c: u64 = 0;
            let mut f: u64 = 0;
            let mut x: i128 = 0;
            let mut k: usize = 0;
            while k < nt
                invariant
                    k <= nt, nt == tv.len(), nt == outs@.len(), gi == g, g < ng, live_s.len() == ng, live_s[gi],
                    layout_ok(start@, sub_group@, line@, ns as int, ng as int), line@.len() == n,
                    chunks_ok(tv, start@, sub_group@, line@, live_s, ns as int, ng as int),
                    forall|j: int| 0 <= j < nt ==> #[trigger] tv[j].post(outs@[j]),
                    c as int == run_rows(start@, sub_group@, gi, 0, bound_at(tv, k as int)),
                    f as int == run_count(sub_group@, gi, 0, bound_at(tv, k as int)),
                    x as int == run_vals(start@, sub_group@, line@, gi, 0, bound_at(tv, k as int)),
                decreases nt - k,
            {
                proof {
                    let (b0, b1) = (bound_at(tv, k as int), bound_at(tv, k + 1));
                    assert(tv[k as int].pre());
                    assert(tv[k as int].post(outs@[k as int]));
                    assert(b0 == tv[k as int].lo && b1 == tv[k as int].hi);
                    lemma_runs_split(start@, sub_group@, line@, gi, 0, b0, b1);
                    lemma_runs_bound(start@, sub_group@, line@, ns as int, gi, 0, b1);
                    assert(start@[b1] <= start@[ns as int]) by { if b1 < ns { assert(start@[b1] < start@[ns as int]); } }
                    assert(0x8000_0000 * (start@[b1] - start@[0]) <= 0x8000_0000 * 0x1_0000_0000_0000_0000int) by (nonlinear_arith)
                        requires start@[b1] - start@[0] <= 0x1_0000_0000_0000_0000int;
                    assert(-0x8000_0000 * (start@[b1] - start@[0]) >= -0x8000_0000 * 0x1_0000_0000_0000_0000int) by (nonlinear_arith)
                        requires start@[b1] - start@[0] <= 0x1_0000_0000_0000_0000int;
                }
                let o = &outs[k];
                c = c + o.0[g];
                f = f + o.1[g];
                x = x + o.2[g];
                k = k + 1;
            }
            proof {
                assert(bound_at(tv, nt as int) == ns);
            }
            put(&mut cnt, g, c);
            put(&mut nf, g, f);
            put(&mut sum, g, x);
        }
        g = g + 1;
    }
    Ok((cnt, nf, sum))
}

} // verus!
