//! Query: per (s.name, p.stmt, n.tag, p.plabel), the SUM and COUNT of the `num` values with `uom = $1` joined to
//! the `sub` row of their adsh with `fy = $3` and to the `pre` rows of their (adsh, tag, version) with
//! `stmt = $2`; the 200 groups with the largest sums.
//!
//! Plan (all structures are built inside the call; the flat storages are read as whole parts):
//! 1. index the `sub` members (`fy = $3`) by adsh (`subidx`, serial: 86K rows);
//! 2. scan `pre` in parallel row ranges for the entries: `stmt = $2` and an adsh with a member (`prescan`); each
//!    entry carries its join-key hash, group-key hash and partition, the top `pbits` bits of its tag's hash;
//! 3. per partition, in parallel, the distinct join keys (member, tag, version) of its entries (`kgbuild`);
//! 4. scan `num` in parallel row ranges: a row with `uom = $1`, a member and a join key of its tag's partition
//!    gives one item (partition, key, value) (`numscan`);
//! 5. per partition, in parallel: merge its items into its keys' accumulators (`merge`), then group its entries
//!    by (name, tag, plabel), adding each entry's key accumulator to its group (`groups`);
//! 6. flatten the groups (`collect`); a COUNT beyond int8 is SQL error 22003, else a SUM mass beyond `i128` is
//!    Capacity (`errs`); otherwise select the candidates at or above about the 200th largest sum, sort them by
//!    the statement's insertion sort and return the first 200 (`topk`).
//! The proof: `sem`/`nf`/`sums` state the statement's meaning on the flat parts as `ctx::gacc` per group key;
//! each step above proves its output against those definitions.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::Answer;
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::{QueryError, WorkerFailure};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_params::Params;
use crate::exec::value::{EVal, view_row};
use crate::link::query::{view_rows, TextCol};
use crate::spec::value::{Row, Val, Database, Relation, SqlError};
use crate::spec::ast::Literal;
use crate::spec::int::IntKind;
use crate::stores::flat_num::interface as ni;
use crate::stores::flat_sub::interface as si;
use crate::stores::flat_pre::interface as pi;

pub mod common;
pub mod ctx;
pub mod sem;
pub mod nf;
pub mod sums;
pub mod subidx;
pub mod keys;
pub mod prescan;
pub mod kg;
pub mod plists;
pub mod kgbuild;
pub mod numscan;
pub mod merge;
pub mod groups;
pub mod topk;
pub mod errs;
pub mod collect;
pub mod cols;
pub mod select;

use crate::agent::common::chain::NONE;
use crate::agent::common::satacc::*;
use crate::agent::common::lazy::*;
use crate::agent::ctx::*;
use crate::agent::sem::*;
use crate::agent::subidx::*;
use crate::agent::keys::*;
use crate::agent::prescan::*;
use crate::agent::kg::*;
use crate::agent::plists::*;
use crate::agent::kgbuild::*;
use crate::agent::numscan::*;
use crate::agent::merge::*;
use crate::agent::groups::*;
use crate::agent::topk::*;
use crate::agent::errs::*;
use crate::agent::collect::*;
use crate::agent::cols::*;
use crate::agent::select::kth_largest;

verus! {

/// Rows per task below which fewer tasks are used.
pub const MIN_TASK_ROWS: usize = 65536;

/// The number of row-range tasks for `n` rows.
fn task_count(n: usize, workers: usize) -> (t: usize)
    requires 1 <= workers <= MAX_WORKERS,
    ensures 1 <= t <= workers,
{
    let mut t = n / MIN_TASK_ROWS;
    if t > workers {
        t = workers;
    }
    if t < 1 {
        t = 1;
    }
    t
}

/// The partition exponent: one partition on one worker (one pass over the entries and items, in row order);
/// otherwise at least `workers` partitions, and at least 16 (so each partition's tables stay cache-resident on
/// its worker), at most 64.
fn part_bits(workers: usize) -> (b: u64)
    requires 1 <= workers <= MAX_WORKERS,
    ensures b <= MAX_PBITS,
{
    if workers == 1 {
        return 0;
    }
    let mut b: u64 = 4;
    while b < MAX_PBITS && (1usize << b) < workers
        invariant b <= MAX_PBITS,
        decreases MAX_PBITS - b,
    {
        b = b + 1;
    }
    b
}

/// The number of partitions, `2^pbits`.
fn part_count(pbits: u64) -> (np: usize)
    requires pbits <= MAX_PBITS,
    ensures np as int == pow2u(pbits), 1 <= np <= 64,
{
    proof {
        lemma_pow2u(pbits);
    }
    let np = 1usize << pbits;
    proof {
        assert(np as int == ((1u64 << pbits) as int)) by (bit_vector) requires pbits <= 6, np == 1usize << pbits;
    }
    np
}

/// Task `t` of `nt` over `n` rows starts at `bound(n, nt, t)`.
pub open spec fn bound(n: int, nt: int, t: int) -> int {
    if t >= nt { n } else { (n / nt) * t }
}

proof fn lemma_range_bound(n: int, nt: int, t: int)
    requires 0 <= n, 1 <= nt, 0 <= t < nt,
    ensures 0 <= bound(n, nt, t) <= bound(n, nt, t + 1) <= n,
{
    let ch = n / nt;
    assert(0 <= ch);
    assert(ch * nt <= n) by (nonlinear_arith) requires ch == n / nt, nt >= 1, n >= 0;
    assert(ch * t <= ch * (t + 1)) by (nonlinear_arith) requires ch >= 0, t >= 0;
    assert(ch * (t + 1) <= ch * nt) by (nonlinear_arith) requires ch >= 0, t + 1 <= nt;
    assert(0 <= ch * t) by (nonlinear_arith) requires ch >= 0, t >= 0;
}

/// The row range `[lo, hi)` of task `t`.
fn range_of(n: usize, nt: usize, t: usize) -> (r: (usize, usize))
    requires 1 <= nt, t < nt,
    ensures r.0 as int == bound(n as int, nt as int, t as int), r.1 as int == bound(n as int, nt as int, t + 1),
        r.0 <= r.1 <= n,
{
    proof {
        lemma_range_bound(n as int, nt as int, t as int);
    }
    let ch = n / nt;
    let lo = ch * t;
    let hi = if t + 1 == nt { n } else { ch * (t + 1) };
    (lo, hi)
}

/// Run the tasks: one after another on the calling thread when there are more than `workers` (or one), else
/// each on its own thread.
fn run_tasks<T: WorkerTask>(dispatch: &mut Dispatch, tasks: Vec<T>, workers: usize) -> (r: Result<Vec<T::Output>, WorkerFailure>)
    requires tasks@.len() <= MAX_WORKERS, forall|i: int| 0 <= i < tasks@.len() ==> #[trigger] tasks@[i].pre(),
    ensures r matches Ok(outs) ==> outs@.len() == tasks@.len() && forall|i: int| 0 <= i < tasks@.len() ==> #[trigger] tasks@[i].post(outs@[i]),
{
    let nt = tasks.len();
    if nt <= 1 || nt > workers {
        let ghost orig = tasks@;
        let mut tasks = tasks;
        let mut v: Vec<T::Output> = Vec::new();
        let mut i: usize = 0;
        while i < nt
            invariant
                nt == orig.len(), i <= nt, tasks@ == orig.subrange(i as int, nt as int), v@.len() == i,
                forall|j: int| 0 <= j < orig.len() ==> #[trigger] orig[j].pre(),
                forall|j: int| 0 <= j < i ==> #[trigger] orig[j].post(v@[j]),
            decreases nt - i,
        {
            let task = tasks.remove(0);
            proof {
                assert(task == orig[i as int]);
                assert(tasks@ =~= orig.subrange(i + 1, nt as int));
            }
            let o = task.run();
            v.push(o);
            i = i + 1;
        }
        Ok(v)
    } else {
        fork_join(dispatch, tasks)
    }
}

fn tcol(t: &TextCol) -> (r: TextCol)
    ensures r@ == t@,
{
    TextCol { offsets: t.offsets, bytes: t.bytes }
}

/// Phase 2: the entries of `pre`, in parallel row ranges.
fn launch_pre(k: &Cols, sub: &Arc<SubIdx>, p1: &'static [u8], pbits: u64, q: usize, workers: usize, dispatch: &mut Dispatch,
    Ghost(c): Ghost<Ctx>) -> (r: Result<(Vec<PreOut>, Ghost<Seq<int>>), WorkerFailure>)
    requires
        ctx_ok(c), sub_key(c), cols_ok(*k, c), sub_idx_wf(**sub, c), p1@ == c.stmt, pbits <= MAX_PBITS, q as int == c.q,
        1 <= workers <= MAX_WORKERS,
    ensures r matches Ok((pres, b)) ==> pres_ok(pres@, c, pbits, b@),
{
    let nt = task_count(q, workers);
    let ghost b = Seq::new((nt + 1) as nat, |t: int| bound(q as int, nt as int, t));
    let p1len = p1.len();
    let mut list: Vec<PreTask> = Vec::new();
    let mut t: usize = 0;
    while t < nt
        invariant
            ctx_ok(c), sub_key(c), cols_ok(*k, c), sub_idx_wf(**sub, c), p1@ == c.stmt, p1len == p1@.len(),
            pbits <= MAX_PBITS, q as int == c.q, 1 <= nt <= MAX_WORKERS, t <= nt,
            b == Seq::new((nt + 1) as nat, |t: int| bound(q as int, nt as int, t)),
            list@.len() == t,
            forall|i: int| 0 <= i < t ==> (#[trigger] list@[i]).pre() && list@[i].lo as int == b[i] && list@[i].hi as int == b[i + 1]
                && list@[i].pbits == pbits && list@[i].ctx@ == c,
        decreases nt - t,
    {
        let (lo, hi) = range_of(q, nt, t);
        let cap = lazy_cap(hi - lo, 8);
        let cap1 = lazy_cap(hi - lo, 1);
        let task = PreTask {
            lo, hi,
            stmt: tcol(&k.pstmt), stmtv: k.pstmtv, adsh: tcol(&k.padsh), tag: tcol(&k.ptag), ver: tcol(&k.pver),
            plabel: tcol(&k.plabel), plabelv: k.plabelv, name: tcol(&k.sname),
            p1, p1len, pbits,
            sub: sub.clone(),
            ek: vec![0usize; cap], es: vec![0usize; cap], ekh: vec![0u64; cap], egh: vec![0u64; cap], ep: vec![0u8; cap1],
            ctx: Ghost(c),
        };
        list.push(task);
        t = t + 1;
    }
    let ghost tl = list@;
    match run_tasks(dispatch, list, workers) {
        Err(e) => Err(e),
        Ok(pres) => {
            proof {
                reveal(pres_ok);
                assert forall|t2: int| 0 <= t2 < nt implies #[trigger] b[t2] <= b[t2 + 1] by {
                    lemma_range_bound(q as int, nt as int, t2);
                }
                assert forall|t2: int| 0 <= t2 < pres@.len() implies pre_out_ok(#[trigger] pres@[t2], c, pbits, b[t2], b[t2 + 1]) by {
                    assert(tl[t2].post(pres@[t2]));
                }
                assert(b[0] == 0) by {
                    assert(bound(q as int, nt as int, 0) == 0) by (nonlinear_arith) requires nt >= 1;
                }
            }
            Ok((pres, Ghost(b)))
        },
    }
}

/// Phase 3: the join-key index of every partition, in parallel.
fn launch_build(pres: &Arc<Vec<PreOut>>, cnt: &Vec<usize>, k: &Cols, pbits: u64, np: usize, workers: usize, dispatch: &mut Dispatch,
    Ghost(c): Ghost<Ctx>, Ghost(b): Ghost<Seq<int>>) -> (r: Result<Vec<KgPart>, WorkerFailure>)
    requires
        ctx_ok(c), cols_ok(*k, c), pres_ok((**pres)@, c, pbits, b), pbits <= MAX_PBITS, np as int == pow2u(pbits),
        cnt@.len() == np, forall|p: int| 0 <= p < np ==> #[trigger] cnt@[p] as int == plist(c, pbits, p, 0, c.q).len(),
        c.q < NONE,
    ensures r matches Ok(kgs) ==> kgs_ok(kgs@, c, pbits),
{
    proof {
        lemma_pow2u(pbits);
        lemma_views_wf(c);
    }
    let mut list: Vec<BuildTask> = Vec::new();
    let mut p: usize = 0;
    while p < np
        invariant
            ctx_ok(c), cols_ok(*k, c), pres_ok((**pres)@, c, pbits, b), pbits <= MAX_PBITS, np as int == pow2u(pbits),
            cnt@.len() == np, forall|p2: int| 0 <= p2 < np ==> #[trigger] cnt@[p2] as int == plist(c, pbits, p2, 0, c.q).len(),
            c.q < NONE, p <= np, np <= 64,
            list@.len() == p,
            forall|i: int| 0 <= i < p ==> (#[trigger] list@[i]).pre() && list@[i].p as int == i && list@[i].pbits == pbits
                && list@[i].ctx@ == c,
        decreases np - p,
    {
        proof {
            lemma_views_wf(c);
            lemma_plist_len(c, pbits, p as int, 0, c.q);
        }
        let c0 = cnt[p];
        let acap = lazy_cap(if c0 <= usize::MAX / 64 { c0 * 64 } else { c0 }, 1);
        let part = kg_new(c0, acap);
        let task = BuildTask { p, pbits, pres: pres.clone(), bounds: Ghost(b), padsh: tcol(&k.padsh), ptag: tcol(&k.ptag), pver: tcol(&k.pver), part, ctx: Ghost(c) };
        list.push(task);
        p = p + 1;
    }
    let ghost tl = list@;
    match run_tasks(dispatch, list, workers) {
        Err(e) => Err(e),
        Ok(kgs) => {
            proof {
                assert forall|p2: int| 0 <= p2 < kgs@.len() implies kg_wf(#[trigger] kgs@[p2], c, pbits, p2, plist(c, pbits, p2, 0, c.q)) by {
                    assert(tl[p2].post(kgs@[p2]));
                }
            }
            Ok(kgs)
        },
    }
}

/// Rows between two weight samples of the num scan.
pub const SAMPLE_ROWS: usize = 8192;

/// Task bounds over `n` rows that split the sampled work `w` (one weight per `SAMPLE_ROWS` rows) evenly:
/// `nt + 1` nondecreasing positions from 0 to `n`.
fn split_bounds(w: &Vec<u32>, n: usize, nt: usize) -> (b: Vec<usize>)
    requires 1 <= nt <= MAX_WORKERS,
    ensures
        b@.len() == nt + 1, b@[0] == 0, b@[nt as int] == n,
        forall|t: int| 0 <= t < nt ==> #[trigger] b@[t] <= b@[t + 1],
        forall|t: int| 0 <= t <= nt ==> #[trigger] b@[t] <= n,
{
    let mut total: u64 = 0;
    let mut j: usize = 0;
    while j < w.len()
        decreases w.len() - j,
    {
        let x = w[j] as u64;
        total = if total > u64::MAX - x { u64::MAX } else { total + x };
        j = j + 1;
    }
    let mut b: Vec<usize> = Vec::new();
    b.push(0);
    let mut acc: u64 = 0;
    let mut pos: usize = 0;
    let mut t: usize = 1;
    j = 0;
    while j < w.len()
        invariant
            1 <= nt <= MAX_WORKERS, 1 <= t <= nt, b@.len() == t, b@[0] == 0, pos <= n,
            forall|i: int| 0 <= i < b@.len() ==> #[trigger] b@[i] <= pos,
            forall|i: int| 0 <= i < b@.len() - 1 ==> #[trigger] b@[i] <= b@[i + 1],
        decreases w.len() - j,
    {
        let x = w[j] as u64;
        acc = if acc > u64::MAX - x { u64::MAX } else { acc + x };
        pos = if n - pos >= SAMPLE_ROWS { pos + SAMPLE_ROWS } else { n };
        proof {
            assert((acc as u128) * (nt as u128) <= u64::MAX as u128 * 64) by (nonlinear_arith)
                requires nt <= 64, acc <= u64::MAX;
        }
        let lhs = (acc as u128) * (nt as u128);
        let mut go = true;
        while go
            invariant
                1 <= nt <= MAX_WORKERS, 1 <= t <= nt, b@.len() == t, b@[0] == 0, pos <= n,
                forall|i: int| 0 <= i < b@.len() ==> #[trigger] b@[i] <= pos,
                forall|i: int| 0 <= i < b@.len() - 1 ==> #[trigger] b@[i] <= b@[i + 1],
            decreases nt - t + (if go { 1int } else { 0int }),
        {
            if t >= nt {
                go = false;
            } else {
                proof {
                    assert((total as u128) * (t as u128) <= u64::MAX as u128 * 64) by (nonlinear_arith)
                        requires t <= 64, total <= u64::MAX;
                }
                let rhs = (total as u128) * (t as u128);
                if lhs >= rhs {
                    b.push(pos);
                    t = t + 1;
                } else {
                    go = false;
                }
            }
        }
        j = j + 1;
    }
    while t < nt
        invariant
            1 <= nt <= MAX_WORKERS, 1 <= t <= nt, b@.len() == t, b@[0] == 0, pos <= n,
            forall|i: int| 0 <= i < b@.len() ==> #[trigger] b@[i] <= n,
            forall|i: int| 0 <= i < b@.len() - 1 ==> #[trigger] b@[i] <= b@[i + 1],
        decreases nt - t,
    {
        b.push(n);
        t = t + 1;
    }
    let ghost b0 = b@;
    b.push(n);
    proof {
        assert(b0[nt - 1] <= n);
        assert forall|i: int| 0 <= i < nt implies #[trigger] b@[i] <= b@[i + 1] by {
            if i < nt - 1 {
                assert(b0[i] <= b0[i + 1]);
            }
        }
    }
    b
}

/// The sampled work of the num scan: a row that joins costs far more than one the filters drop.
fn num_weights(k: &Cols, sub: &SubIdx, kgs: &Vec<KgPart>, p0: &'static [u8], pbits: u64, n: usize, Ghost(c): Ghost<Ctx>)
    -> (w: Vec<u32>)
    requires
        ctx_ok(c), sub_key(c), cols_ok(*k, c), sub_idx_wf(*sub, c), kgs_ok(kgs@, c, pbits), p0@ == c.uom,
        pbits <= MAX_PBITS, n as int == c.n,
{
    let p0len = p0.len();
    let mut w: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            ctx_ok(c), sub_key(c), cols_ok(*k, c), sub_idx_wf(*sub, c), kgs_ok(kgs@, c, pbits), p0@ == c.uom,
            p0len == p0@.len(), pbits <= MAX_PBITS, n as int == c.n,
        decreases n - i,
    {
        proof {
            lemma_views_wf(c);
        }
        let a = text_of(&k.nadsh, i, Ghost(c.n));
        let al = text_len(&k.nadsh, i, Ghost(c.n));
        let wt: u32 = if !sub_maybe(sub, crate::agent::common::bytes::sig(a, al), Ghost(c)) {
            1
        } else {
            let (_p, g) = row_item(i, &k.nadsh, &k.nuom, &k.ntag, &k.nver, p0, p0len, pbits, sub, kgs, &k.padsh, &k.ptag, &k.pver, Ghost(c));
            if g == NONE { 4 } else { 24 }
        };
        w.push(wt);
        i = if n - i > SAMPLE_ROWS { i + SAMPLE_ROWS } else { n };
    }
    w
}

/// The row bounds of the `nt` num-scan tasks.
fn num_bounds(k: &Cols, sub: &SubIdx, kgs: &Vec<KgPart>, p0: &'static [u8], pbits: u64, n: usize, nt: usize,
    Ghost(c): Ghost<Ctx>) -> (b: Vec<usize>)
    requires
        ctx_ok(c), sub_key(c), cols_ok(*k, c), sub_idx_wf(*sub, c), kgs_ok(kgs@, c, pbits), p0@ == c.uom,
        pbits <= MAX_PBITS, n as int == c.n, 1 <= nt <= MAX_WORKERS,
    ensures
        b@.len() == nt + 1, b@[0] == 0, b@[nt as int] == n,
        forall|t: int| 0 <= t < nt ==> #[trigger] b@[t] <= b@[t + 1],
        forall|t: int| 0 <= t <= nt ==> #[trigger] b@[t] <= n,
{
    if nt == 1 {
        let mut v: Vec<usize> = Vec::new();
        v.push(0);
        v.push(n);
        v
    } else {
        let w = num_weights(k, sub, kgs, p0, pbits, n, Ghost(c));
        split_bounds(&w, n, nt)
    }
}

/// Phase 4: the items of `num`, in parallel row ranges.
fn launch_num(k: &Cols, sub: &Arc<SubIdx>, kgs: &Arc<Vec<KgPart>>, p0: &'static [u8], pbits: u64, n: usize, workers: usize,
    dispatch: &mut Dispatch, Ghost(c): Ghost<Ctx>) -> (r: Result<(Vec<NumOut>, Ghost<Seq<int>>), WorkerFailure>)
    requires
        ctx_ok(c), sub_key(c), cols_ok(*k, c), sub_idx_wf(**sub, c), kgs_ok((**kgs)@, c, pbits), p0@ == c.uom,
        pbits <= MAX_PBITS, n as int == c.n, 1 <= workers <= MAX_WORKERS,
    ensures r matches Ok((nouts, b)) ==> nouts_ok(nouts@, c, pbits, (**kgs)@, b@),
{
    let nt = task_count(n, workers);
    let bv = num_bounds(k, &**sub, &**kgs, p0, pbits, n, nt, Ghost(c));
    let ghost b = Seq::new((nt + 1) as nat, |t: int| bv@[t] as int);
    let p0len = p0.len();
    let mut list: Vec<NumTask> = Vec::new();
    let mut t: usize = 0;
    while t < nt
        invariant
            ctx_ok(c), sub_key(c), cols_ok(*k, c), sub_idx_wf(**sub, c), kgs_ok((**kgs)@, c, pbits), p0@ == c.uom,
            p0len == p0@.len(), pbits <= MAX_PBITS, n as int == c.n, 1 <= nt <= MAX_WORKERS, t <= nt,
            b == Seq::new((nt + 1) as nat, |t: int| bv@[t] as int),
            bv@.len() == nt + 1, bv@[0] == 0, bv@[nt as int] == n,
            forall|t: int| 0 <= t < nt ==> #[trigger] bv@[t] <= bv@[t + 1],
            forall|t: int| 0 <= t <= nt ==> #[trigger] bv@[t] <= n,
            list@.len() == t,
            forall|i: int| 0 <= i < t ==> (#[trigger] list@[i]).pre() && list@[i].lo as int == b[i] && list@[i].hi as int == b[i + 1]
                && list@[i].s.pbits == pbits && list@[i].ctx@ == c && (*list@[i].s.kgs)@ == (**kgs)@,
        decreases nt - t,
    {
        let lo = bv[t];
        let hi = bv[t + 1];
        let cap1 = lazy_cap(hi - lo, 1);
        let cap8 = lazy_cap(hi - lo, 8);
        let cap16 = lazy_cap(hi - lo, 16);
        let task = NumTask {
            lo, hi,
            s: NumScan {
                adsh: tcol(&k.nadsh), uom: tcol(&k.nuom), tag: tcol(&k.ntag), ver: tcol(&k.nver), value: k.nval,
                p0, p0len, pbits,
                sub: sub.clone(), kgs: kgs.clone(),
                padsh: tcol(&k.padsh), ptag: tcol(&k.ptag), pver: tcol(&k.pver),
            },
            ip: vec![0u8; cap1], ig: vec![0usize; cap8], iv: vec![0i128; cap16],
            bi: vec![0usize; BLK], bp: vec![0usize; BLK], bh: vec![0u64; BLK], bc: vec![0usize; BLK],
            ctx: Ghost(c),
        };
        proof {
            reveal(scan_ok);
        }
        list.push(task);
        t = t + 1;
    }
    let ghost tl = list@;
    match run_tasks(dispatch, list, workers) {
        Err(e) => Err(e),
        Ok(nouts) => {
            proof {
                reveal(nouts_ok);
                assert forall|t2: int| 0 <= t2 < nt implies #[trigger] b[t2] <= b[t2 + 1] by {
                    assert(bv@[t2] <= bv@[t2 + 1]);
                }
                assert forall|t2: int| 0 <= t2 < nouts@.len() implies num_out_ok(#[trigger] nouts@[t2], c, pbits, (**kgs)@, b[t2], b[t2 + 1]) by {
                    assert(tl[t2].post(nouts@[t2]));
                }
                assert(b[0] == 0);
                assert(b[nt as int] == n);
            }
            Ok((nouts, Ghost(b)))
        },
    }
}

/// Phase 5: the groups of every partition, in parallel.
fn launch_groups(pres: &Arc<Vec<PreOut>>, nouts: &Arc<Vec<NumOut>>, kgs: &Arc<Vec<KgPart>>, k: &Cols, pbits: u64, np: usize,
    workers: usize, dispatch: &mut Dispatch, Ghost(c): Ghost<Ctx>, Ghost(pb): Ghost<Seq<int>>, Ghost(nb): Ghost<Seq<int>>) -> (r: Result<Vec<GrpTab>, WorkerFailure>)
    requires
        ctx_ok(c), cols_ok(*k, c), pres_ok((**pres)@, c, pbits, pb), nouts_ok((**nouts)@, c, pbits, (**kgs)@, nb),
        kgs_ok((**kgs)@, c, pbits), pbits <= MAX_PBITS, np as int == pow2u(pbits), c.q < NONE,
    ensures r matches Ok(tabs) ==> tabs@.len() == np
        && forall|p: int| 0 <= p < np ==> grp_wf(#[trigger] tabs@[p], c, pbits, p, plist(c, pbits, p, 0, c.q)),
{
    let kv: &Vec<KgPart> = &*kgs;
    proof {
        lemma_pow2u(pbits);
        lemma_views_wf(c);
    }
    let mut list: Vec<GroupTask> = Vec::new();
    let mut p: usize = 0;
    while p < np
        invariant
            ctx_ok(c), cols_ok(*k, c), pres_ok((**pres)@, c, pbits, pb), nouts_ok((**nouts)@, c, pbits, (**kgs)@, nb),
            kgs_ok((**kgs)@, c, pbits), pbits <= MAX_PBITS, np as int == pow2u(pbits), c.q < NONE, p <= np, np <= 64,
            kv@ == (**kgs)@,
            list@.len() == p,
            forall|i: int| 0 <= i < p ==> (#[trigger] list@[i]).pre() && list@[i].p as int == i && list@[i].pbits == pbits
                && list@[i].ctx@ == c,
        decreases np - p,
    {
        let kp = &kv[p];
        proof {
            assert(kg_wf(kv@[p as int], c, pbits, p as int, plist(c, pbits, p as int, 0, c.q)));
            lemma_kg_facts(*kp, c, pbits, p as int, plist(c, pbits, p as int, 0, c.q));
            lemma_views_wf(c);
            lemma_plist_len(c, pbits, p as int, 0, c.q);
        }
        // Zeroed by the worker (`GroupTask::run`); lazily allocated here.
        let mut accs: Vec<Acc> = vec![(0u64, 0i128, 0u128); lazy_cap(kp.nkg, 48)];
        accs.truncate(kp.nkg);
        let tab = grp_new(kp.nent);
        let task = GroupTask {
            p, pbits, pres: pres.clone(), pbounds: Ghost(pb), nouts: nouts.clone(), nbounds: Ghost(nb), kgs: kgs.clone(),
            name: tcol(&k.sname), tag: tcol(&k.ptag), plabel: tcol(&k.plabel), plabelv: k.plabelv,
            accs, tab, ctx: Ghost(c),
        };
        list.push(task);
        p = p + 1;
    }
    let ghost tl = list@;
    match run_tasks(dispatch, list, workers) {
        Err(e) => Err(e),
        Ok(tabs) => {
            proof {
                assert forall|p2: int| 0 <= p2 < np implies grp_wf(#[trigger] tabs@[p2], c, pbits, p2, plist(c, pbits, p2, 0, c.q)) by {
                    assert(tl[p2].post(tabs@[p2]));
                }
            }
            Ok(tabs)
        },
    }
}

/// The bytes of a slice as a vector.
fn copy_bytes(x: &[u8]) -> (v: Vec<u8>)
    ensures v@ == x@,
{
    let mut v: Vec<u8> = Vec::new();
    let n = x.len();
    let mut k: usize = 0;
    while k < n
        invariant n == x@.len(), k <= n, v@ == x@.subrange(0, k as int),
        decreases n - k,
    {
        v.push(x[k]);
        proof {
            assert(v@ =~= x@.subrange(0, k as int + 1));
        }
        k = k + 1;
    }
    proof {
        assert(x@.subrange(0, n as int) =~= x@);
    }
    v
}

/// The output row of group `x` (pre row `kx`, member `sx`).
fn out_row(kx: usize, sx: usize, sum: i128, cnt: u64, k: &Cols, p1: &'static [u8], Ghost(c): Ghost<Ctx>) -> (row: Vec<EVal>)
    requires
        ctx_ok(c), cols_ok(*k, c), p1@ == c.stmt, pre_ok(c, kx as int), sx as int == esub(c, kx as int),
        cnt as int <= crate::spec::limits::int8_max(),
    ensures view_row(row@) == grow(gkey(c, kx as int), sum as int, cnt as int),
{
    proof {
        lemma_views_wf(c);
        lemma_sub_for(c, p_adsh(c, kx as int));
    }
    let nb = text_of(&k.sname, sx, Ghost(c.m));
    let tb = text_of(&k.ptag, kx, Ghost(c.q));
    let mut row: Vec<EVal> = Vec::new();
    row.push(EVal::Text(copy_bytes(nb)));
    row.push(EVal::Text(copy_bytes(p1)));
    row.push(EVal::Text(copy_bytes(tb)));
    if k.plabelv[kx] != 0 {
        let lb = text_of(&k.plabel, kx, Ghost(c.q));
        row.push(EVal::Text(copy_bytes(lb)));
    } else {
        row.push(EVal::Null);
    }
    row.push(EVal::Num { coeff: sum, scale: 4 });
    row.push(EVal::Int(cnt as i64));
    proof {
        assert(view_row(row@) =~= grow(gkey(c, kx as int), sum as int, cnt as int));
    }
    row
}

/// The context of the call: the parts are well formed, `sub`'s key holds, and the binding is in range.
proof fn lemma_context(sv: StoresView, db: Database, c: Ctx, ps: Seq<Literal>)
    requires
        crate::gendb_entry::bound_db(sv, db),
        c.np == sv.flat_num, c.sp == sv.flat_sub, c.pp == sv.flat_pre,
        c.n == crate::stores::flat_num::declaration::stored_relations(db)[0].len(),
        c.m == crate::stores::flat_sub::declaration::stored_relations(db)[0].len(),
        c.q == crate::stores::flat_pre::declaration::stored_relations(db)[0].len(),
        crate::query::param_domain(ps),
        ps == seq![Literal::Text(c.uom), Literal::Text(c.stmt), Literal::Int { v: c.fy, kind: IntKind::Int4 }],
    ensures
        ctx_ok(c),
        sub_key(c),
        lits_ok(c, ps),
{
    reveal(ctx_ok);
    assert(ni::parts_wf(c.np, c.n));
    assert(si::parts_wf(c.sp, c.m));
    assert(pi::parts_wf(c.pp, c.q));
    lemma_bound(sv, db, c);
    assert(ps[2] == Literal::Int { v: c.fy, kind: IntKind::Int4 });
}

/// The answer for every database bound to the parts: SQL error 22003 (a group count beyond int8).
proof fn lemma_answer_err(sv: StoresView, c: Ctx, ps: Seq<Literal>, key: Row)
    requires
        ctx_ok(c), c.np == sv.flat_num, c.sp == sv.flat_sub, c.pp == sv.flat_pre, lits_ok(c, ps),
        gacc(c, 0, key, c.q) > crate::spec::limits::int8_max(),
    ensures crate::gendb_entry::answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::SqlError(SqlError::NumericValueOutOfRange))),
{
    assert forall|db2: Database| #[trigger] crate::gendb_entry::bound_db(sv, db2) implies
        crate::gendb_entry::outcome_ok(db2, crate::query::query_spec_at(ps), Ok::<Answer, QueryError>(Answer::SqlError(SqlError::NumericValueOutOfRange))) by {
        lemma_bound(sv, db2, c);
        lemma_query_shape(ps);
        lemma_count_err(db2, c, ps, key);
    }
}

/// The answer for every database bound to the parts: Capacity (a group mass beyond `i128`, counts within int8).
proof fn lemma_answer_cap(sv: StoresView, c: Ctx, ps: Seq<Literal>, key: Row)
    requires
        ctx_ok(c), c.np == sv.flat_num, c.sp == sv.flat_sub, c.pp == sv.flat_pre, lits_ok(c, ps),
        forall|k: Row| #[trigger] gacc(c, 0, k, c.q) <= crate::spec::limits::int8_max(),
        gacc(c, 2, key, c.q) > crate::link::expr::i128_max(),
    ensures crate::gendb_entry::answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Capacity)),
{
    assert forall|db2: Database| #[trigger] crate::gendb_entry::bound_db(sv, db2) implies
        crate::gendb_entry::outcome_ok(db2, crate::query::query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
        lemma_bound(sv, db2, c);
        lemma_query_shape(ps);
        lemma_mass_cap(db2, c, ps, key);
    }
}

/// The answer for every database bound to the parts: the produced rows.
proof fn lemma_answer_rows(sv: StoresView, c: Ctx, ps: Seq<Literal>, gl: Seq<Row>, fv: Seq<i128>, fc: Seq<u64>,
    thr: i128, cand: Seq<usize>, sv2: Seq<usize>, out: Vec<Vec<EVal>>)
    requires
        ctx_ok(c), c.np == sv.flat_num, c.sp == sv.flat_sub, c.pp == sv.flat_pre, lits_ok(c, ps),
        gl.len() == fv.len(), gl.len() == fc.len(), gl.len() <= usize::MAX,
        gl.no_duplicates(),
        forall|k: Row| #[trigger] gl.contains(k) <==> gacc(c, 0, k, c.q) > 0,
        forall|i: int| 0 <= i < gl.len() ==> #[trigger] fc[i] as int == gacc(c, 0, gl[i], c.q),
        forall|i: int| 0 <= i < gl.len() ==> #[trigger] fv[i] as int == gacc(c, 1, gl[i], c.q),
        forall|i: int| 0 <= i < gl.len() ==> (#[trigger] gl[i]).len() == 4,
        forall|k: Row| #[trigger] gacc(c, 0, k, c.q) <= crate::spec::limits::int8_max(),
        forall|k: Row| #[trigger] gacc(c, 2, k, c.q) <= crate::link::expr::i128_max(),
        cand == cidx(fv, thr, gl.len() as int),
        rows_at(grows_of(gl, fv, fc), sv2) == crate::spec::order::sort_rows(order_keys(), rows_at(grows_of(gl, fv, fc), cand)),
        cand.len() >= LIMIT || cand.len() == gl.len(),
        view_rows(out@) == rows_at(grows_of(gl, fv, fc), sv2).take(if sv2.len() < LIMIT { sv2.len() as int } else { LIMIT as int }),
    ensures crate::gendb_entry::answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Rows(out))),
{
    assert forall|db2: Database| #[trigger] crate::gendb_entry::bound_db(sv, db2) implies
        crate::gendb_entry::outcome_ok(db2, crate::query::query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(out))) by {
        lemma_bound(sv, db2, c);
        lemma_final_rows(db2, c, ps, gl, fv, fc, thr, cand, sv2, view_rows(out@));
    }
}

/// A group with no match has no mass.
proof fn lemma_no_match(c: Ctx, key: Row)
    requires gacc(c, 0, key, c.q) == 0,
    ensures gacc(c, 2, key, c.q) <= 0,
{
    lemma_gacc_nonneg(c, 2, key, c.q);
    if gacc(c, 2, key, c.q) > 0 {
        lemma_gacc_mass_count(c, key, c.q);
    }
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
    let ghost db = choose|db: Database| #[trigger] crate::gendb_entry::bound_db(stores@, db);
    let ghost nrels = crate::stores::flat_num::declaration::stored_relations(db);
    let ghost srels = crate::stores::flat_sub::declaration::stored_relations(db);
    let ghost prels = crate::stores::flat_pre::declaration::stored_relations(db);
    let n = ni::stored_rows(&stores.flat_num, Ghost(nrels));
    let m = si::stored_rows(&stores.flat_sub, Ghost(srels));
    let q = pi::stored_rows(&stores.flat_pre, Ghost(prels));
    let p0: &'static [u8] = params.p0;
    let p1: &'static [u8] = params.p1;
    let p2: i64 = params.p2;
    let ghost c = Ctx { np: stores.flat_num@, n: n as int, sp: stores.flat_sub@, m: m as int, pp: stores.flat_pre@, q: q as int,
        uom: p0@, stmt: p1@, fy: p2 as int };
    proof {
        lemma_context(sv, db, c, params@);
        lemma_views_wf(c);
        reveal(ctx_ok);
    }
    let lm = stores.flat_sub.part_len(si::ADSH_OFFSETS);
    let lq = stores.flat_pre.part_len(pi::ADSH_OFFSETS);
    proof {
        assert(lm as int == c.m + 1);
        assert(lq as int == c.q + 1);
    }
    let k = read_cols(stores, Ghost(c));
    let sub = Arc::new(build_sub(tcol(&k.sadsh), k.sfy, k.sfyv, m, p2, Ghost(c)));
    let pbits = part_bits(workers);
    let np = part_count(pbits);
    // 2. entries
    let (pres, Ghost(pb)) = match launch_pre(&k, &sub, p1, pbits, q, workers, dispatch, Ghost(c)) {
        Err(e) => return Err(QueryError::WorkerFailed(e)),
        Ok(x) => x,
    };
    let cnt = count_parts(&pres, np, Ghost(c), Ghost(pbits), Ghost(pb));
    let pres = Arc::new(pres);
    // 3. join keys
    let kgs = match launch_build(&pres, &cnt, &k, pbits, np, workers, dispatch, Ghost(c), Ghost(pb)) {
        Err(e) => return Err(QueryError::WorkerFailed(e)),
        Ok(x) => x,
    };
    let kgs = Arc::new(kgs);
    // 4. items
    let (nouts, Ghost(nb)) = match launch_num(&k, &sub, &kgs, p0, pbits, n, workers, dispatch, Ghost(c)) {
        Err(e) => return Err(QueryError::WorkerFailed(e)),
        Ok(x) => x,
    };
    let nouts = Arc::new(nouts);
    // 5. groups
    let tabs = match launch_groups(&pres, &nouts, &kgs, &k, pbits, np, workers, dispatch, Ghost(c), Ghost(pb), Ghost(nb)) {
        Err(e) => return Err(QueryError::WorkerFailed(e)),
        Ok(x) => x,
    };
    // 6. the answer
    let (f, Ghost(gl)) = flatten(&tabs, Ghost(c), Ghost(pbits));
    let (status, idx) = check_caps(&f, Ghost(c), Ghost(gl));
    if status == 1 {
        proof {
            lemma_answer_err(sv, c, params@, gl[idx as int]);
        }
        return Ok(Answer::SqlError(SqlError::NumericValueOutOfRange));
    }
    if status == 2 {
        proof {
            lemma_answer_cap(sv, c, params@, gl[idx as int]);
        }
        return Ok(Answer::Capacity);
    }
    let out = top_rows(&f, &k, p1, Ghost(c), Ghost(gl), Ghost(sv), Ghost(params@));
    Ok(Answer::Rows(out))
}

/// Status 1: a group count beyond int8 (group `idx`); 2: no such count and a group mass beyond `i128` (group
/// `idx`); 0: every count and mass inside.
fn check_caps(f: &Flat, Ghost(c): Ghost<Ctx>, Ghost(gl): Ghost<Seq<Row>>) -> (r: (u8, usize))
    requires flat_ok(*f, c, gl),
    ensures
        r.0 == 1 ==> r.1 < gl.len() && gacc(c, 0, gl[r.1 as int], c.q) > crate::spec::limits::int8_max(),
        r.0 == 2 ==> r.1 < gl.len() && gacc(c, 2, gl[r.1 as int], c.q) > crate::link::expr::i128_max()
            && forall|key: Row| #[trigger] gacc(c, 0, key, c.q) <= crate::spec::limits::int8_max(),
        r.0 != 1 && r.0 != 2 ==> forall|j: int| 0 <= j < gl.len() ==> (#[trigger] f.fa@[j]).0 < CCAP && f.fa@[j].2 < MCAP,
{
    let ng = f.fa.len();
    let mut mi: usize = NONE;
    let mut i: usize = 0;
    while i < ng
        invariant
            flat_ok(*f, c, gl), ng == gl.len(), i <= ng,
            forall|j: int| 0 <= j < i ==> (#[trigger] f.fa@[j]).0 < CCAP,
            mi == NONE ==> forall|j: int| 0 <= j < i ==> (#[trigger] f.fa@[j]).2 < MCAP,
            mi != NONE ==> mi < i && f.fa@[mi as int].2 == MCAP,
        decreases ng - i,
    {
        let a = f.fa[i];
        proof {
            assert(elem_ok(*f, c, gl, i as int));
        }
        if a.0 == CCAP {
            return (1, i);
        }
        if a.2 == MCAP && mi == NONE {
            mi = i;
        }
        i = i + 1;
    }
    if mi != NONE {
        proof {
            assert(elem_ok(*f, c, gl, mi as int));
            assert forall|key: Row| #[trigger] gacc(c, 0, key, c.q) <= crate::spec::limits::int8_max() by {
                if gacc(c, 0, key, c.q) > 0 {
                    assert(gl.contains(key));
                    let t = choose|t: int| 0 <= t < gl.len() && gl[t] == key;
                    assert(elem_ok(*f, c, gl, t));
                    assert(f.fa@[t].0 < CCAP);
                }
            }
        }
        return (2, mi);
    }
    (0, 0)
}

/// The exact sums and counts of the groups (every count and mass inside).
fn exact_vals(f: &Flat, Ghost(c): Ghost<Ctx>, Ghost(gl): Ghost<Seq<Row>>) -> (r: (Vec<i128>, Vec<u64>))
    requires
        flat_ok(*f, c, gl),
        forall|j: int| 0 <= j < gl.len() ==> (#[trigger] f.fa@[j]).0 < CCAP && f.fa@[j].2 < MCAP,
    ensures
        r.0@.len() == gl.len(), r.1@.len() == gl.len(),
        forall|j: int| 0 <= j < gl.len() ==> #[trigger] r.1@[j] as int == gacc(c, 0, gl[j], c.q)
            && (r.1@[j] as int) <= crate::spec::limits::int8_max(),
        forall|j: int| 0 <= j < gl.len() ==> #[trigger] r.0@[j] as int == gacc(c, 1, gl[j], c.q),
        forall|key: Row| #[trigger] gacc(c, 0, key, c.q) <= crate::spec::limits::int8_max(),
        forall|key: Row| #[trigger] gacc(c, 2, key, c.q) <= crate::link::expr::i128_max(),
{
    let ng = f.fa.len();
    let mut fv: Vec<i128> = Vec::with_capacity(ng);
    let mut fc: Vec<u64> = Vec::with_capacity(ng);
    let mut i: usize = 0;
    while i < ng
        invariant
            flat_ok(*f, c, gl), ng == gl.len(), i <= ng, fv@.len() == i, fc@.len() == i,
            forall|j: int| 0 <= j < gl.len() ==> (#[trigger] f.fa@[j]).0 < CCAP && f.fa@[j].2 < MCAP,
            forall|j: int| 0 <= j < i ==> #[trigger] fc@[j] as int == gacc(c, 0, gl[j], c.q)
                && (fc@[j] as int) <= crate::spec::limits::int8_max(),
            forall|j: int| 0 <= j < i ==> #[trigger] fv@[j] as int == gacc(c, 1, gl[j], c.q),
        decreases ng - i,
    {
        let a = f.fa[i];
        proof {
            assert(elem_ok(*f, c, gl, i as int));
        }
        fv.push(a.1);
        fc.push(a.0);
        i = i + 1;
    }
    proof {
        assert forall|key: Row| #[trigger] gacc(c, 0, key, c.q) <= crate::spec::limits::int8_max() by {
            if gacc(c, 0, key, c.q) > 0 {
                assert(gl.contains(key));
                let t = choose|t: int| 0 <= t < gl.len() && gl[t] == key;
                assert(elem_ok(*f, c, gl, t));
            }
        }
        assert forall|key: Row| #[trigger] gacc(c, 2, key, c.q) <= crate::link::expr::i128_max() by {
            if gacc(c, 0, key, c.q) > 0 {
                assert(gl.contains(key));
                let t = choose|t: int| 0 <= t < gl.len() && gl[t] == key;
                assert(elem_ok(*f, c, gl, t));
            } else {
                lemma_gacc_nonneg(c, 0, key, c.q);
                lemma_no_match(c, key);
            }
        }
    }
    (fv, fc)
}

/// The first 200 groups by sum, descending, as result rows (every count and mass inside).
fn top_rows(f: &Flat, k: &Cols, p1: &'static [u8], Ghost(c): Ghost<Ctx>, Ghost(gl): Ghost<Seq<Row>>, Ghost(sv): Ghost<StoresView>,
    Ghost(ps): Ghost<Seq<Literal>>) -> (out: Vec<Vec<EVal>>)
    requires
        flat_ok(*f, c, gl), ctx_ok(c), cols_ok(*k, c), p1@ == c.stmt,
        c.np == sv.flat_num, c.sp == sv.flat_sub, c.pp == sv.flat_pre, lits_ok(c, ps),
        forall|j: int| 0 <= j < gl.len() ==> (#[trigger] f.fa@[j]).0 < CCAP && f.fa@[j].2 < MCAP,
    ensures crate::gendb_entry::answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::Rows(out))),
{
    let (fv, fc) = exact_vals(f, Ghost(c), Ghost(gl));
    let ng = fv.len();
    proof {
        assert forall|j: int| 0 <= j < gl.len() implies (#[trigger] gl[j]).len() == 4 by {
            assert(elem_ok(*f, c, gl, j));
        }
    }
    // Candidates at or above about the 200th largest sum (all groups when the heuristic leaves fewer than 200).
    let mut thr: i128 = if ng <= LIMIT { i128::MIN } else { kth_largest(&fv, LIMIT) };
    let mut cand = split_cands(&fv, ng, thr);
    if cand.len() < LIMIT && cand.len() < ng {
        thr = i128::MIN;
        cand = split_cands(&fv, ng, thr);
        proof {
            lemma_cidx_all(fv@, ng as int);
        }
    }
    proof {
        if thr == i128::MIN {
            lemma_cidx_all(fv@, ng as int);
        }
    }
    let ghost ar = grows_of(gl, fv@, fc@);
    proof {
        lemma_split_bag(ar, fv@, thr, ng as int);
        assert forall|j: int| 0 <= j < ar.len() implies row_shape(#[trigger] ar[j]) && sum_at(ar[j]) == fv@[j] as int by {}
    }
    let sv2 = sort_cands(&cand, &fv, Ghost(ar));
    let nout = if sv2.len() < LIMIT { sv2.len() } else { LIMIT };
    let mut out: Vec<Vec<EVal>> = Vec::new();
    let mut r: usize = 0;
    while r < nout
        invariant
            flat_ok(*f, c, gl), ng == gl.len(), fv@.len() == ng, fc@.len() == ng, ctx_ok(c), cols_ok(*k, c), p1@ == c.stmt,
            forall|j: int| 0 <= j < ng ==> #[trigger] fc@[j] as int == gacc(c, 0, gl[j], c.q)
                && (fc@[j] as int) <= crate::spec::limits::int8_max(),
            ar == grows_of(gl, fv@, fc@),
            nout <= sv2@.len(),
            forall|t: int| 0 <= t < sv2@.len() ==> (#[trigger] sv2@[t] as int) < ar.len(),
            r <= nout,
            view_rows(out@) == rows_at(ar, sv2@).take(r as int),
        decreases nout - r,
    {
        let x = sv2[r];
        proof {
            assert(elem_ok(*f, c, gl, x as int));
        }
        let row = out_row(f.fk[x], f.fs[x], fv[x], fc[x], k, p1, Ghost(c));
        let ghost before = out@;
        out.push(row);
        proof {
            assert(view_rows(out@) =~= view_rows(before).push(view_row(row@)));
            assert(rows_at(ar, sv2@).take(r as int + 1) =~= rows_at(ar, sv2@).take(r as int).push(ar[x as int]));
        }
        r = r + 1;
    }
    proof {
        lemma_answer_rows(sv, c, ps, gl, fv@, fc@, thr, cand@, sv2@, out);
    }
    out
}

/// At threshold `i128::MIN` every index is a candidate.
proof fn lemma_cidx_all(fv: Seq<i128>, n: int)
    requires 0 <= n <= fv.len(),
    ensures cidx(fv, i128::MIN, n).len() == n,
    decreases n,
{
    if n > 0 {
        lemma_cidx_all(fv, n - 1);
    }
}

} // verus!
