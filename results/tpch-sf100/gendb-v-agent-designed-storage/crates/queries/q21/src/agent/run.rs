//! Running the scan: the stored orders rows `[0, n_o)` split into at most `workers` contiguous ranges, one
//! `kernel::ScanTask` each (`make_tasks`), joined by `fork_join`. The ranges meet end to start, so do the tasks'
//! lineitem ranges (`model::lemma_merge_unique`). Each task returns its counting rows as an event list (one slot
//! index per counting row, in a buffer allocated here with lazily zeroed pages), so the caller neither fills nor
//! sums one counter vector per task: `merge_counts` adds the events (`add_hits`) and scans here the rows a task left
//! when its buffer ran short. The per-slot sums are the counts over `[0, L(n_o))`, and the lines past `L(n_o)` have
//! no order (`lemma_merge_end`), so they are the counts over every lineitem row. Without the co-clustering flag, one
//! l_orderkey run per stored order (`runs::runs_model`, `runs::runs_aligned`) or a dense slot map the serial fallback
//! counts (`kernel::count_fallback`).
//!
//! Balance: only orders with status `F` hold counting lines. Orders are stored by date and `F` orders are the old
//! ones, so the split puts `workers - 1` equal ranges before a guess of where `F` orders end (`guess_f_end`, a binary
//! search over groups that assumes this; it only steers the split, never the result) and one tail range after it,
//! which mostly scans status codes and also checks the slot names (`side::names_increasing`).
use vstd::prelude::*;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::WorkerFailure;
use super::common::fill::{fill_usize, fill_u32, copy_usize};
use super::side::*;
use super::common::occ::*;
use super::wscan::scan_range;
use super::model::*;
use super::kernel::*;
use super::supp::*;
use super::runs::*;
use std::sync::Arc;

verus! {

/// A copy of the map (the tables are shared).
fn share_map(m: &SuppMap) -> (r: SuppMap)
    ensures r == *m,
{
    SuppMap { ns: m.ns, skeys: Arc::clone(&m.skeys), dense: m.dense, kmin: m.kmin, range: m.range, slots: Arc::clone(&m.slots),
        bits: Arc::clone(&m.bits) }
}

/// Whether some stored orders row of group `g` has status index `f`.
fn group_has_f(c: &Cols, k: Ghost<int>, g: usize, f: u64) -> bool
    requires cols_ok(*c, k@), g < c.os_bases@.len(),
{
    let a = match g.checked_mul(c.bs_o) {
        Some(x) => x,
        None => return false,
    };
    if a >= c.n_o {
        return false;
    }
    let b = if c.bs_o <= c.n_o - a { a + c.bs_o } else { c.n_o };
    seg_has_f(c, k, g, a, b, f)
}

/// A guess of where the orders with status index `f` end, assuming they are a prefix of the groups (a binary search
/// over groups). Only the split uses it.
fn guess_f_end(c: &Cols, k: Ghost<int>, f: u64) -> (e: usize)
    requires cols_ok(*c, k@),
    ensures e <= c.n_o,
{
    let ng = c.os_bases.len();
    let mut lo: usize = 0;
    let mut hi: usize = ng;
    while lo < hi
        invariant
            cols_ok(*c, k@),
            ng == c.os_bases@.len(),
            lo <= hi <= ng,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        if group_has_f(c, k, mid, f) {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    match lo.checked_mul(c.bs_o) {
        Some(x) => if x < c.n_o { x } else { c.n_o },
        None => c.n_o,
    }
}

/// The task ranges chain from 0 to `n`.
pub open spec fn chained(tasks: Seq<ScanTask>, n: int) -> bool {
    &&& tasks.len() >= 1
    &&& tasks[0].q0 == 0
    &&& tasks[tasks.len() - 1].q1 == n
    &&& forall|i: int| 0 <= i < tasks.len() - 1 ==> #[trigger] tasks[i].q1 == tasks[i + 1].q0
}

/// Boundary `i` of `m` equal ranges over `[0, b)`.
pub open spec fn eqb(b: int, m: int, i: int) -> int {
    if i >= m { b } else { b / m * i }
}

proof fn lemma_eqb(b: int, m: int, i: int, j: int)
    requires 0 <= b, m >= 1, 0 <= i <= j <= m,
    ensures 0 <= eqb(b, m, i) <= eqb(b, m, j) <= b, eqb(b, m, 0) == 0,
{
    let w = b / m;
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(b, m);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(b, m);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(b, m);
    assert(w * m <= b) by (nonlinear_arith) requires m * w + b % m == b, b % m >= 0;
    assert(w * i <= w * j) by (nonlinear_arith) requires i <= j, w >= 0;
    assert(w * j <= w * m) by (nonlinear_arith) requires j <= m, w >= 0;
    assert(w * i >= 0) by (nonlinear_arith) requires i >= 0, w >= 0;
    if m > 0 {
        assert(eqb(b, m, 0) == w * 0);
    }
}

/// Smallest event buffer (u32 entries, 34 MB): above the allocator's largest mmap threshold (32 MB), so it is
/// always a fresh lazily zeroed mapping.
pub const LAZY_CAP: usize = 8_500_000;

/// One task over `[q0, q1)`, with an event buffer of one entry per 64 orders plus 1024 (about three times the
/// counting rows of TPC-H data; a short buffer only leaves rows to the caller), and at least `LAZY_CAP` entries.
/// With `names`, the task also decides `names_inc` of the slot rows `srows`.
fn make_task(c: &Cols, nk: usize, sm: &SuppMap, f: u64, q0: usize, q1: usize, names: bool, sc: &SCols,
    srows: Vec<usize>) -> (t: ScanTask)
    requires
        cols_ok(*c, nk as int),
        keys_distinct(*c),
        lines_clustered(*c),
        runs_model(*c),
        runs_aligned(*c),
        smap_ok(*sm),
        sm.dense,
        sm.range <= 0x400_0000,
        q0 <= q1 <= c.n_o,
        names ==> scols_ok(*sc),
        names ==> forall|t: int| 0 <= t < srows@.len() ==> #[trigger] srows@[t] < sc.n_s,
    ensures
        t.pre(),
        t.cols == *c,
        t.sm.skeys@ == sm.skeys@,
        t.f == f,
        t.q0 == q0,
        t.q1 == q1,
        t.names == names,
        t.sc == *sc,
        t.srows@ == srows@,
{
    // At least LAZY_CAP entries: an allocation that large is mapped lazily (zero pages on first touch, in the
    // worker), so the calling thread neither zeroes nor faults it in; only the entries written are touched.
    let need = (q1 - q0) / 64 + 1024;
    let cap = if need < LAZY_CAP { LAZY_CAP } else { need };
    let ns = srows.len();
    ScanTask { cols: *c, nk, sm: share_map(sm), f, q0, q1, buf: fill_u32(cap, 0u32), cap, names, sc: *sc, srows, ns }
}

/// The scan tasks over orders `[0, n_o)`: with `m` tasks, `m - 1` equal ranges before the guessed end `a_end` of the
/// `F` orders (at least 65536 orders each), then the tail `[a_end, n_o)`, where mostly status codes are scanned
/// (one task over all orders when `m` is 1). The tail task also decides `names_inc` of the slot rows `srows`, so
/// their name reads overlap the scan of the other tasks.
fn make_tasks(c: &Cols, nk: usize, sm: &SuppMap, f: u64, workers: usize, sc: &SCols, srows: &Vec<usize>)
    -> (tasks: Vec<ScanTask>)
    requires
        cols_ok(*c, nk as int),
        keys_distinct(*c),
        lines_clustered(*c),
        runs_model(*c),
        runs_aligned(*c),
        smap_ok(*sm),
        sm.dense,
        sm.range <= 0x400_0000,
        1 <= workers <= MAX_WORKERS,
        scols_ok(*sc),
        forall|t: int| 0 <= t < srows@.len() ==> #[trigger] srows@[t] < sc.n_s,
    ensures
        tasks@.len() <= MAX_WORKERS,
        chained(tasks@, c.n_o as int),
        tasks@.last().names && tasks@.last().sc == *sc && tasks@.last().srows@ == srows@,
        forall|i: int| 0 <= i < tasks@.len() ==> {
            &&& (#[trigger] tasks@[i]).pre()
            &&& tasks@[i].cols == *c
            &&& tasks@[i].sm.skeys@ == sm.skeys@
            &&& tasks@[i].f == f
        },
{
    let n = c.n_o;
    let gend = guess_f_end(c, Ghost(nk as int), f);
    let g: usize = if gend > 0 { gend } else { n };
    // Front tasks: m1 equal ranges over [0, a_end).
    let cap = g / 65536 + 1;
    let m1: usize = if workers - 1 < cap { workers - 1 } else { cap };
    // The tail task also checks the names and scans the status codes past g, so it takes about two fifths of a
    // share of the rows before g (0, 0.4 and 0.8 measured alike at 32 workers): the front tasks split
    // [0, g - 2 g / (5 m1 + 2)).
    let tail_share: usize = if m1 == 0 { 0 } else {
        match (g / (5 * m1 + 2)).checked_mul(2) {
            Some(x) => x,
            None => 0,
        }
    };
    let a_end: usize = if m1 == 0 { 0 } else if tail_share <= g { g - tail_share } else { g };
    let w = if m1 == 0 { 0 } else { a_end / m1 };
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut t: usize = 0;
    while t < m1
        invariant
            cols_ok(*c, nk as int),
            keys_distinct(*c),
            lines_clustered(*c),
            runs_model(*c),
            runs_aligned(*c),
            smap_ok(*sm),
            sm.dense,
            sm.range <= 0x400_0000,
            n == c.n_o,
            a_end <= n,
            m1 <= workers - 1,
            workers <= MAX_WORKERS,
            m1 > 0 ==> w == a_end / m1,
            t <= m1,
            tasks@.len() == t,
            t > 0 ==> tasks@[t - 1].q1 == (if t == m1 { a_end as int } else { eqb(a_end as int, m1 as int, t as int) }),
            t > 0 ==> tasks@[0].q0 == 0,
            forall|i: int| 0 <= i < t - 1 ==> #[trigger] tasks@[i].q1 == tasks@[i + 1].q0,
            forall|i: int| 0 <= i < t ==> {
                &&& (#[trigger] tasks@[i]).pre()
                &&& tasks@[i].cols == *c
                &&& tasks@[i].sm.skeys@ == sm.skeys@
                &&& tasks@[i].f == f
            },
        decreases m1 - t,
    {
        proof {
            lemma_eqb(a_end as int, m1 as int, t as int, t + 1);
            lemma_eqb(a_end as int, m1 as int, 0, t as int);
        }
        let q0 = w * t;
        let q1 = if t + 1 == m1 { a_end } else { w * (t + 1) };
        let task = make_task(c, nk, sm, f, q0, q1, false, sc, Vec::new());
        let ghost old = tasks@;
        tasks.push(task);
        proof {
            assert forall|i: int| 0 <= i < tasks@.len() - 1 implies #[trigger] tasks@[i].q1 == tasks@[i + 1].q0 by {
                if i < t - 1 {
                    assert(tasks@[i] == old[i] && tasks@[i + 1] == old[i + 1]);
                } else {
                    assert(tasks@[i] == old[t - 1]);
                }
            }
        }
        t = t + 1;
    }
    // The tail task, which also checks the names.
    let ghost front = tasks@;
    let task = make_task(c, nk, sm, f, a_end, n, true, sc, copy_usize(srows));
    tasks.push(task);
    proof {
        assert forall|i: int| 0 <= i < tasks@.len() - 1 implies #[trigger] tasks@[i].q1 == tasks@[i + 1].q0 by {
            if i < m1 - 1 {
                assert(tasks@[i] == front[i] && tasks@[i + 1] == front[i + 1]);
            } else {
                assert(tasks@[i] == front[m1 - 1]);
            }
        }
        if m1 == 0 {
            assert(tasks@[0].q0 == 0);
        }
    }
    tasks
}

/// Rows the caller scans per buffer when a task left rows to it.
pub const REST_CAP: usize = 65536;

/// Adds the event list `buf[0 .. used)` (the counts of `[a, b)`) to the per-slot counts of `[0, a)`.
fn add_hits(c: &Cols, f: u64, Ghost(ks): Ghost<Seq<i64>>, sums: &mut Vec<usize>, buf: &Vec<u32>, used: usize,
    Ghost(a): Ghost<int>, Ghost(b): Ghost<int>)
    requires
        0 <= a <= b <= c.n_l,
        used <= buf@.len(),
        counts_ok(*c, f as int, ks, old(sums)@, 0, a),
        hits_ok(*c, f as int, ks, buf@.subrange(0, used as int), a, b),
    ensures
        counts_ok(*c, f as int, ks, final(sums)@, 0, b),
{
    let ghost v = buf@.subrange(0, used as int);
    let ghost s0 = sums@;
    let ns = sums.len();
    proof {
        assert forall|t: int| 0 <= t < ks.len() implies #[trigger] sums@[t] as int
            == cnt(*c, f as int, ks[t] as int, 0, a) + occ(v.subrange(0, 0), t) by {
            lemma_occ_empty(v.subrange(0, 0), t);
        }
    }
    let mut i: usize = 0;
    while i < used
        invariant
            0 <= a <= b <= c.n_l,
            used <= buf@.len(),
            v == buf@.subrange(0, used as int),
            ns == ks.len(),
            sums@.len() == ns,
            i <= used,
            hits_ok(*c, f as int, ks, v, a, b),
            forall|t: int| 0 <= t < ks.len() ==> #[trigger] sums@[t] as int
                == cnt(*c, f as int, ks[t] as int, 0, a) + occ(v.subrange(0, i as int), t),
        decreases used - i,
    {
        let h = buf[i] as usize;
        proof {
            assert(v[i as int] == buf@[i as int]);
            assert((v[i as int] as int) < ks.len());
            let hh = h as int;
            lemma_occ_step(v, i as int, hh);
            lemma_occ_prefix(v, i + 1, hh);
            lemma_cnt_split(*c, f as int, ks[hh] as int, 0, a, b);
            lemma_cnt_bound(*c, f as int, ks[hh] as int, 0, b);
        }
        let x = sums[h] + 1;
        sums[h] = x;
        proof {
            assert forall|t: int| 0 <= t < ks.len() implies #[trigger] sums@[t] as int
                == cnt(*c, f as int, ks[t] as int, 0, a) + occ(v.subrange(0, i + 1), t) by {
                lemma_occ_step(v, i as int, t);
            }
        }
        i = i + 1;
    }
    proof {
        assert(v.subrange(0, used as int) =~= v);
        assert forall|t: int| 0 <= t < ks.len() implies #[trigger] sums@[t] as int == cnt(*c, f as int, ks[t] as int, 0, b) by {
            lemma_cnt_split(*c, f as int, ks[t] as int, 0, a, b);
        }
    }
}

/// Adds one task output (the counts of its rows `[lo, hi)`) to the per-slot counts of `[0, lo)`: its event list,
/// then the rows it left, scanned here one buffer at a time.
fn merge_one(c: &Cols, nk: usize, sm: &SuppMap, f: u64, sums: &mut Vec<usize>, o: &ScanOut)
    requires
        cols_ok(*c, nk as int),
        keys_distinct(*c),
        lines_clustered(*c),
        runs_model(*c),
        runs_aligned(*c),
        smap_ok(*sm),
        sm.dense,
        sm.range <= 0x400_0000,
        o.lo <= o.mid <= o.hi <= c.n_l,
        o.used <= o.buf@.len(),
        hits_ok(*c, f as int, sm.skeys@, o.buf@.subrange(0, o.used as int), o.lo as int, o.mid as int),
        counts_ok(*c, f as int, sm.skeys@, old(sums)@, 0, o.lo as int),
        o.mid < o.hi ==> cur_ok(*c, o.rc as int, o.rs as int, o.mid as int),
    ensures
        counts_ok(*c, f as int, sm.skeys@, final(sums)@, 0, o.hi as int),
{
    let ghost k = sm.skeys@;
    add_hits(c, f, Ghost(k), sums, &o.buf, o.used, Ghost(o.lo as int), Ghost(o.mid as int));
    let mut pos = o.mid;
    let mut rc = o.rc;
    let mut rs = o.rs;
    while pos < o.hi
        invariant
            cols_ok(*c, nk as int),
            keys_distinct(*c),
            lines_clustered(*c),
            runs_model(*c),
            runs_aligned(*c),
            smap_ok(*sm),
            sm.dense,
            sm.range <= 0x400_0000,
            k == sm.skeys@,
            o.mid <= pos <= o.hi <= c.n_l,
            counts_ok(*c, f as int, k, sums@, 0, pos as int),
            pos < o.hi ==> cur_ok(*c, rc as int, rs as int, pos as int),
        decreases o.hi - pos,
    {
        let rb0 = fill_u32(REST_CAP, 0u32);
        let (rb, ru, stop, rc2, rs2) = scan_range(c, Ghost(nk as int), sm, f, pos, o.hi, rc, rs, rb0, REST_CAP);
        add_hits(c, f, Ghost(k), sums, &rb, ru, Ghost(pos as int), Ghost(stop as int));
        pos = stop;
        rc = rc2;
        rs = rs2;
    }
}

/// Per-slot sums of the task outputs: the counts over every stored lineitem row. Rows a task left (its buffer ran
/// short) are scanned here.
fn merge_counts(c: &Cols, nk: usize, sm: &SuppMap, f: u64, tv: Ghost<Seq<ScanTask>>, outs: &Vec<ScanOut>) -> (sums: Vec<usize>)
    requires
        cols_ok(*c, nk as int),
        keys_distinct(*c),
        lines_clustered(*c),
        runs_model(*c),
        runs_aligned(*c),
        smap_ok(*sm),
        sm.dense,
        sm.range <= 0x400_0000,
        chained(tv@, c.n_o as int),
        outs@.len() == tv@.len(),
        forall|i: int| 0 <= i < tv@.len() ==> {
            &&& (#[trigger] tv@[i]).post(outs@[i])
            &&& tv@[i].cols == *c
            &&& tv@[i].sm.skeys@ == sm.skeys@
            &&& tv@[i].f == f
        },
    ensures
        counts_ok(*c, f as int, sm.skeys@, sums@, 0, c.n_l as int),
{
    let ghost nt = tv@.len() as int;
    let ghost k = sm.skeys@;
    let n_out = outs.len();
    let ns = sm.ns;
    let mut sums: Vec<usize> = fill_usize(ns, 0usize);
    let mut t: usize = 0;
    let ghost mut hi: int = 0;
    proof {
        if c.n_l > 0 {
            lemma_rpos_bound(*c, lkey(*c, 0));
        }
        assert(merge_inv(*c, 0, 0));
        assert(tv@[0].q0 == 0);
        assert forall|s: int| 0 <= s < k.len() implies #[trigger] sums@[s] as int == cnt(*c, f as int, k[s] as int, 0, 0) by {}
    }
    while t < n_out
        invariant
            cols_ok(*c, nk as int),
            keys_distinct(*c),
            lines_clustered(*c),
            runs_model(*c),
            runs_aligned(*c),
            smap_ok(*sm),
            sm.dense,
            sm.range <= 0x400_0000,
            n_out == nt == outs@.len(),
            nt == tv@.len(),
            k == sm.skeys@,
            ns == k.len(),
            chained(tv@, c.n_o as int),
            t <= nt,
            forall|i: int| 0 <= i < nt ==> {
                &&& (#[trigger] tv@[i]).post(outs@[i])
                &&& tv@[i].cols == *c
                &&& tv@[i].sm.skeys@ == k
                &&& tv@[i].f == f
            },
            0 <= hi <= c.n_l,
            t < nt ==> merge_inv(*c, tv@[t as int].q0 as int, hi),
            t == nt ==> merge_inv(*c, c.n_o as int, hi),
            counts_ok(*c, f as int, k, sums@, 0, hi),
        decreases nt - t,
    {
        let o = &outs[t];
        let ghost task = tv@[t as int];
        proof {
            assert(task.post(outs@[t as int]));
            assert(*o == outs@[t as int]);
            lemma_merge_unique(*c, task.q0 as int, hi, o.lo as int);
        }
        merge_one(c, nk, sm, f, &mut sums, o);
        proof {
            hi = o.hi as int;
            assert(merge_inv(*c, task.q1 as int, hi));
            if t + 1 < nt {
                assert(0 <= t < tv@.len() - 1);
                assert(tv@[t as int].q1 == tv@[t + 1].q0);
            } else {
                assert(tv@[tv@.len() - 1].q1 == c.n_o);
            }
        }
        t = t + 1;
    }
    proof {
        assert forall|s: int| 0 <= s < k.len() implies #[trigger] sums@[s] as int == cnt(*c, f as int, k[s] as int, 0, c.n_l as int) by {
            lemma_merge_end(*c, f as int, k[s] as int, hi);
            lemma_cnt_split(*c, f as int, k[s] as int, 0, hi, c.n_l as int);
        }
    }
    sums
}

/// The counts over every stored lineitem row, with `names_inc` of the slot rows `srows`: parallel scan tasks when
/// the lineitem rows follow the orders and the slot map is dense (the tail task also checks the names, overlapping
/// the scan), else the serial fallback.
pub fn count_all(c: &Cols, nk: usize, sm: &SuppMap, f: u64, runs: bool, workers: usize, dispatch: &mut Dispatch,
    sc: &SCols, srows: &Vec<usize>) -> (r: Result<(Vec<usize>, bool), WorkerFailure>)
    requires
        cols_ok(*c, nk as int),
        keys_distinct(*c),
        runs ==> lines_clustered(*c) && runs_model(*c) && runs_aligned(*c),
        smap_ok(*sm),
        1 <= workers <= MAX_WORKERS,
        scols_ok(*sc),
        forall|t: int| 0 <= t < srows@.len() ==> #[trigger] srows@[t] < sc.n_s,
    ensures
        r matches Ok(v) ==> counts_ok(*c, f as int, sm.skeys@, v.0@, 0, c.n_l as int) && v.1 == names_inc(*sc, srows@),
{
    if !runs || !sm.dense || sm.range > 0x400_0000 {
        let inc = names_increasing(sc, srows, srows.len());
        return Ok((count_fallback(c, Ghost(nk as int), sm, f), inc));
    }
    let tasks = make_tasks(c, nk, sm, f, workers, sc, srows);
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    let last = outs.len() - 1;
    proof {
        assert(tv[last as int].post(outs@[last as int]));
    }
    let inc = outs[last].inc;
    Ok((merge_counts(c, nk, sm, f, Ghost(tv), &outs), inc))
}

} // verus!
