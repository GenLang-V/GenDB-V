//! The parallel phases: each splits its row range into contiguous task ranges (`bounds`), runs the tasks with
//! `fork_join` (or on the calling thread when one task suffices), and concatenates the outputs in task order,
//! finishing on the calling thread any task that stopped early because its buffer filled up. The concatenation
//! of consecutive ranges is the output of the whole range (`lemma_cands_ok_append`, `lemma_contrib_split`; the tag
//! pairs are a set-like output, `lemma_pairs_union`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::link::query::TextCol;
use crate::agent::common::buf::Buf;
use crate::agent::common::chains::NONE;
use crate::agent::cols::*;
use crate::agent::pre::*;
use crate::agent::tagres::*;
use crate::agent::scan::*;
use crate::agent::fold::{Rec, flat, lemma_flat_push};

verus! {

/// Contiguous ranges covering `0..n`, one per task.
pub open spec fn covers(b: Seq<(usize, usize)>, n: int) -> bool {
    &&& b.len() >= 1
    &&& b[0].0 == 0
    &&& b[b.len() - 1].1 == n
    &&& forall|t: int| 0 <= t < b.len() ==> (#[trigger] b[t]).0 <= b[t].1 && b[t].1 <= n
    &&& forall|t: int| 0 < t < b.len() ==> #[trigger] b[t].0 == b[t - 1].1
}

/// The number of tasks for `n` rows: at most `workers`, about `min_rows` rows each at least.
pub fn task_count(n: usize, workers: usize, min_rows: usize) -> (t: usize)
    requires 1 <= workers <= MAX_WORKERS, min_rows > 0,
    ensures 1 <= t <= workers,
{
    let by_rows = n / min_rows;
    if by_rows < workers { by_rows + 1 } else { workers }
}

/// `tasks` contiguous ranges of about equal size covering `0..n`.
pub fn bounds(n: usize, tasks: usize) -> (b: Vec<(usize, usize)>)
    requires 1 <= tasks <= MAX_WORKERS,
    ensures b@.len() == tasks, covers(b@, n as int),
{
    let chunk = n / tasks;
    let mut b: Vec<(usize, usize)> = Vec::new();
    let mut lo: usize = 0;
    let mut t: usize = 0;
    proof {
        assert(chunk * tasks <= n) by (nonlinear_arith) requires chunk == n / tasks, tasks > 0;
    }
    while t < tasks
        invariant
            1 <= tasks <= MAX_WORKERS, t <= tasks, b@.len() == t, chunk * tasks <= n,
            lo == chunk * t, t < tasks ==> lo <= n,
            t > 0 ==> b@[0].0 == 0,
            t > 0 ==> b@[t - 1].1 == if t == tasks { n } else { lo },
            forall|u: int| 0 <= u < t ==> (#[trigger] b@[u]).0 <= b@[u].1 && b@[u].1 <= n,
            forall|u: int| 0 < u < t ==> #[trigger] b@[u].0 == b@[u - 1].1,
        decreases tasks - t,
    {
        proof {
            assert(chunk * (t + 1) <= chunk * tasks) by (nonlinear_arith) requires t + 1 <= tasks, chunk >= 0;
            assert(chunk * (t + 1) == chunk * t + chunk) by (nonlinear_arith);
        }
        let hi = if t + 1 == tasks { n } else { lo + chunk };
        b.push((lo, hi));
        lo = lo + chunk;
        t = t + 1;
    }
    b
}

// ------------------------------------------------------------------------------------------------ P1

pub fn clone_pre_scan(p: &PreScan) -> (r: PreScan)
    ensures
        r.p_adsh@ == p.p_adsh@ && r.p_stmt@ == p.p_stmt@ && r.p_stmtv@ == p.p_stmtv@ && r.p_tag@ == p.p_tag@
            && r.p_ver@ == p.p_ver@ && r.stmt@ == p.stmt@ && r.stmt_len == p.stmt_len && *r.sx == *p.sx,
{
    PreScan {
        p_adsh: tc(&p.p_adsh), p_stmt: tc(&p.p_stmt), p_stmtv: p.p_stmtv, p_tag: tc(&p.p_tag), p_ver: tc(&p.p_ver),
        stmt: p.stmt, stmt_len: p.stmt_len, sx: p.sx.clone(),
    }
}

/// Append one pre task's candidates (finishing its range on the calling thread when it stopped early).
fn collect_pre(p: &PreScan, all: &mut Vec<(usize, usize, u64)>, o: PreOut, lo: usize, hi: usize, Ghost(c): Ghost<Ctx>)
    requires
        pre_scan_ok(p, c), lo <= hi, (hi as int) <= c.npre,
        o.out.wf(), lo <= o.stopped <= hi, cands_ok(c, o.out.view(), lo as int, o.stopped as int),
        cands_ok(c, old(all)@, 0, lo as int),
    ensures cands_ok(c, final(all)@, 0, hi as int),
{
    let PreOut { out, stopped } = o;
    let ghost a0 = all@;
    let mut v = out.into_vec();
    let ghost v0 = v@;
    all.append(&mut v);
    proof {
        lemma_cands_ok_append(c, a0, v0, 0, lo as int, stopped as int);
    }
    if stopped < hi {
        let mut rest = crate::agent::pre::scan_serial(p, stopped, hi, Ghost(c));
        let ghost a1 = all@;
        let ghost r0 = rest@;
        all.append(&mut rest);
        proof {
            lemma_cands_ok_append(c, a1, r0, 0, stopped as int, hi as int);
        }
    }
}

/// The candidate pre rows of the whole table.
pub fn run_pre(p: &PreScan, np: usize, workers: usize, dispatch: &mut Dispatch, Ghost(c): Ghost<Ctx>)
    -> (r: Result<Vec<(usize, usize, u64)>, WorkerFailure>)
    requires pre_scan_ok(p, c), np as int == c.npre, 1 <= workers <= MAX_WORKERS,
    ensures r matches Ok(v) ==> cands_ok(c, v@, 0, c.npre),
{
    let tasks = task_count(np, workers, 131072);
    let b = bounds(np, tasks);
    let mut list: Vec<PreTask> = Vec::new();
    let mut t: usize = 0;
    while t < tasks
        invariant
            pre_scan_ok(p, c), np as int == c.npre, b@.len() == tasks, covers(b@, np as int), 1 <= tasks <= MAX_WORKERS,
            t <= tasks, list@.len() == t,
            forall|u: int| 0 <= u < t ==> (#[trigger] list@[u]).pre() && list@[u].lo == b@[u].0 && list@[u].hi == b@[u].1
                && list@[u].ctx@ == c,
        decreases tasks - t,
    {
        let (lo, hi) = b[t];
        let cap = (hi - lo) / 16 + 1024;
        let scan = clone_pre_scan(p);
        proof {
            lemma_pre_scan_copy(p, &scan, c);
        }
        let task = PreTask { lo, hi, scan, out: Buf::new(cap, (0, 0, 0)), ctx: Ghost(c) };
        list.push(task);
        t = t + 1;
    }
    let ghost tl = list@;
    let outs: Vec<PreOut> = if tasks == 1 {
        let task = list.pop().unwrap();
        proof {
            assert(task == tl[0]);
        }
        let o = task.run();
        let mut v: Vec<PreOut> = Vec::new();
        v.push(o);
        v
    } else {
        match fork_join(dispatch, list) {
            Ok(v) => v,
            Err(e) => return Err(e),
        }
    };
    // Concatenate in task order, finishing tasks that stopped early.
    let mut all: Vec<(usize, usize, u64)> = Vec::new();
    let mut outs = outs;
    let ghost ov = outs@;
    let mut u: usize = 0;
    proof {
        assert(cands_in(c, 0, 0) =~= Seq::<int>::empty());
    }
    while u < tasks
        invariant
            pre_scan_ok(p, c), np as int == c.npre, b@.len() == tasks, covers(b@, np as int), u <= tasks,
            ov.len() == tasks, outs@ == ov.subrange(u as int, tasks as int),
            forall|w: int| 0 <= w < tasks ==> #[trigger] tl[w].post(ov[w]) && tl[w].lo == b@[w].0 && tl[w].hi == b@[w].1
                && tl[w].ctx@ == c,
            cands_ok(c, all@, 0, if u == 0 { 0 } else { b@[u - 1].1 as int }),
        decreases tasks - u,
    {
        let o = outs.remove(0);
        proof {
            assert(o == ov[u as int]);
            assert(outs@ =~= ov.subrange(u + 1, tasks as int));
        }
        let (lo, hi) = b[u];
        proof {
            assert(tl[u as int].post(ov[u as int]));
            if u > 0 {
                assert(b@[u as int].0 == b@[u - 1].1);
            }
        }
        collect_pre(p, &mut all, o, lo, hi, Ghost(c));
        u = u + 1;
    }
    Ok(all)
}

// ------------------------------------------------------------------------------------------------ P2

pub fn clone_tag_scan(t: &TagScan) -> (r: TagScan)
    ensures r.t_tag@ == t.t_tag@ && r.t_ver@ == t.t_ver@ && r.t_abs@ == t.t_abs@ && *r.sl == *t.sl,
{
    TagScan { t_tag: tc(&t.t_tag), t_ver: tc(&t.t_ver), t_abs: t.t_abs, sl: t.sl.clone() }
}

/// The meeting `(slot, tag row)` pairs of the whole tag table, in tag row order.
pub fn run_tag(ts: &TagScan, nt: usize, workers: usize, dispatch: &mut Dispatch, Ghost(c): Ghost<Ctx>)
    -> (r: Result<Vec<(usize, usize)>, WorkerFailure>)
    requires tag_scan_ok(ts, c), nt as int == c.nt, 1 <= workers <= MAX_WORKERS,
    ensures r matches Ok(v) ==> hits_ok(&*ts.sl, c, v@, 0, c.nt, c.nt),
{
    let tasks = task_count(nt, workers, 32768);
    let b = bounds(nt, tasks);
    let mut list: Vec<TagTask> = Vec::new();
    let mut t: usize = 0;
    while t < tasks
        invariant
            tag_scan_ok(ts, c), nt as int == c.nt, b@.len() == tasks, covers(b@, nt as int), 1 <= tasks <= MAX_WORKERS,
            t <= tasks, list@.len() == t,
            forall|u: int| 0 <= u < t ==> (#[trigger] list@[u]).pre() && list@[u].lo == b@[u].0 && list@[u].hi == b@[u].1
                && list@[u].ctx@ == c && *list@[u].scan.sl == *ts.sl,
        decreases tasks - t,
    {
        let (lo, hi) = b[t];
        let scan = clone_tag_scan(ts);
        proof {
            lemma_tag_scan_copy(ts, &scan, c);
        }
        let task = TagTask { lo, hi, scan, out: Buf::new(hi - lo, (0, 0)), ctx: Ghost(c) };
        list.push(task);
        t = t + 1;
    }
    let ghost tl = list@;
    let outs: Vec<Buf<(usize, usize)>> = if tasks == 1 {
        let task = list.pop().unwrap();
        proof {
            assert(task == tl[0]);
        }
        let o = task.run();
        let mut v: Vec<Buf<(usize, usize)>> = Vec::new();
        v.push(o);
        v
    } else {
        match fork_join(dispatch, list) {
            Ok(v) => v,
            Err(e) => return Err(e),
        }
    };
    let mut all: Vec<(usize, usize)> = Vec::new();
    let mut outs = outs;
    let ghost ov = outs@;
    let mut u: usize = 0;
    while u < tasks
        invariant
            tag_scan_ok(ts, c), nt as int == c.nt, b@.len() == tasks, covers(b@, nt as int), u <= tasks,
            ov.len() == tasks, outs@ == ov.subrange(u as int, tasks as int),
            forall|w: int| 0 <= w < tasks ==> #[trigger] tl[w].post(ov[w]) && tl[w].lo == b@[w].0 && tl[w].hi == b@[w].1
                && tl[w].ctx@ == c && *tl[w].scan.sl == *ts.sl,
            hits_ok(&*ts.sl, c, all@, 0, if u == 0 { 0 } else { b@[u - 1].1 as int }, if u == 0 { 0 } else { b@[u - 1].1 as int }),
        decreases tasks - u,
    {
        let o = outs.remove(0);
        proof {
            assert(o == ov[u as int]);
            assert(outs@ =~= ov.subrange(u + 1, tasks as int));
            assert(tl[u as int].post(ov[u as int]));
            if u > 0 {
                assert(b@[u as int].0 == b@[u - 1].1);
            }
        }
        let ghost a0 = all@;
        let mut v = o.into_vec();
        let ghost v0 = v@;
        all.append(&mut v);
        proof {
            let lo = b@[u as int].0 as int;
            lemma_hits_union(&*ts.sl, c, a0, v0, 0, lo, b@[u as int].1 as int);
        }
        u = u + 1;
    }
    Ok(all)
}

pub fn clone_ver_scan(v: &VerScan) -> (r: VerScan)
    ensures
        *r.cx == *v.cx && *r.sl == *v.sl && r.tvrow@ == v.tvrow@ && r.hits@ == v.hits@ && r.t_tag@ == v.t_tag@
            && r.t_ver@ == v.t_ver@,
{
    VerScan {
        cx: v.cx.clone(), sl: v.sl.clone(), tvrow: v.tvrow.clone(), hits: v.hits.clone(), t_tag: tc(&v.t_tag),
        t_ver: tc(&v.t_ver),
    }
}

/// Answers for candidates `0..lo` followed by answers for `lo..` are answers for all of them.
proof fn lemma_answers_append(x: &Cands, c: Ctx, a: Seq<usize>, v: Seq<usize>, lo: int)
    requires
        a.len() == lo, forall|e: int| 0 <= e < a.len() ==> tag_answer(x, c, e, #[trigger] a[e]),
        forall|q: int| 0 <= q < v.len() ==> tag_answer(x, c, lo + q, #[trigger] v[q]),
    ensures forall|e: int| 0 <= e < (a + v).len() ==> tag_answer(x, c, e, #[trigger] (a + v)[e]),
{
    assert forall|e: int| 0 <= e < (a + v).len() implies tag_answer(x, c, e, #[trigger] (a + v)[e]) by {
        if e < a.len() {
            assert((a + v)[e] == a[e]);
        } else {
            assert((a + v)[e] == v[e - lo]);
            assert(tag_answer(x, c, lo + (e - lo), v[e - lo]));
        }
    }
}

/// The tag row of every candidate (parallel over candidate ranges).
pub fn run_ver(vs: &VerScan, workers: usize, dispatch: &mut Dispatch, Ghost(c): Ghost<Ctx>)
    -> (r: Result<Vec<usize>, WorkerFailure>)
    requires ver_scan_ok(vs, c), 1 <= workers <= MAX_WORKERS,
    ensures r matches Ok(v) ==> tagrow_ok(&*vs.cx, c, v@),
{
    let n = vs.cx.list.len();
    let tasks = task_count(n, workers, 8192);
    let b = bounds(n, tasks);
    let mut list: Vec<VerTask> = Vec::new();
    let mut t: usize = 0;
    while t < tasks
        invariant
            ver_scan_ok(vs, c), n == vs.cx.list@.len(), b@.len() == tasks, covers(b@, n as int), 1 <= tasks <= MAX_WORKERS,
            t <= tasks, list@.len() == t,
            forall|u: int| 0 <= u < t ==> (#[trigger] list@[u]).pre() && list@[u].lo == b@[u].0 && list@[u].hi == b@[u].1
                && list@[u].ctx@ == c && *list@[u].scan.cx == *vs.cx,
        decreases tasks - t,
    {
        let (lo, hi) = b[t];
        let scan = clone_ver_scan(vs);
        proof {
            lemma_ver_scan_copy(vs, &scan, c);
        }
        let out: Vec<usize> = vec![NONE; hi - lo];
        let task = VerTask { lo, hi, scan, out, ctx: Ghost(c) };
        list.push(task);
        t = t + 1;
    }
    let ghost tl = list@;
    let outs: Vec<Vec<usize>> = if tasks == 1 {
        let task = list.pop().unwrap();
        proof {
            assert(task == tl[0]);
        }
        let o = task.run();
        let mut v: Vec<Vec<usize>> = Vec::new();
        v.push(o);
        v
    } else {
        match fork_join(dispatch, list) {
            Ok(v) => v,
            Err(e) => return Err(e),
        }
    };
    let mut all: Vec<usize> = Vec::with_capacity(n);
    let mut outs = outs;
    let ghost ov = outs@;
    let mut u: usize = 0;
    while u < tasks
        invariant
            ver_scan_ok(vs, c), n == vs.cx.list@.len(), b@.len() == tasks, covers(b@, n as int), u <= tasks,
            ov.len() == tasks, outs@ == ov.subrange(u as int, tasks as int),
            forall|w: int| 0 <= w < tasks ==> #[trigger] tl[w].post(ov[w]) && tl[w].lo == b@[w].0 && tl[w].hi == b@[w].1
                && tl[w].ctx@ == c && *tl[w].scan.cx == *vs.cx,
            all@.len() == if u == 0 { 0 } else { b@[u - 1].1 as int },
            forall|e: int| 0 <= e < all@.len() ==> tag_answer(&*vs.cx, c, e, #[trigger] all@[e]),
        decreases tasks - u,
    {
        let o = outs.remove(0);
        proof {
            assert(o == ov[u as int]);
            assert(outs@ =~= ov.subrange(u + 1, tasks as int));
            assert(tl[u as int].post(ov[u as int]));
            if u > 0 {
                assert(b@[u as int].0 == b@[u - 1].1);
            }
        }
        let ghost a0 = all@;
        let mut v = o;
        let ghost v0 = v@;
        all.append(&mut v);
        proof {
            lemma_answers_append(&*vs.cx, c, a0, v0, b@[u as int].0 as int);
        }
        u = u + 1;
    }
    proof {
        assert(all@.len() == n);
    }
    Ok(all)
}

// ------------------------------------------------------------------------------------------------ P4

pub fn clone_num_scan(s: &NumScan) -> (r: NumScan)
    ensures
        r.n_uom@ == s.n_uom@ && r.n_adsh@ == s.n_adsh@ && r.n_tag@ == s.n_tag@ && r.n_ver@ == s.n_ver@ && r.n_val@ == s.n_val@
            && r.uom@ == s.uom@ && r.uom_len == s.uom_len && *r.sx == *s.sx && *r.ex == *s.ex,
{
    NumScan {
        n_uom: tc(&s.n_uom), n_adsh: tc(&s.n_adsh), n_tag: tc(&s.n_tag), n_ver: tc(&s.n_ver), n_val: s.n_val,
        uom: s.uom, uom_len: s.uom_len, sx: s.sx.clone(), ex: s.ex.clone(), adsh_first: s.adsh_first,
    }
}

/// A scan task's output for its range (hidden; `lemma_scan_done`).
#[verifier::opaque]
pub open spec fn scan_done(c: Ctx, ents: Seq<(usize, usize, usize)>, o: ScanOut, lo: int, hi: int) -> bool {
    o.out.wf() && lo <= o.stopped <= hi && o.out.view() == contrib(c, ents, lo, o.stopped as int)
}

proof fn lemma_scan_done(c: Ctx, ents: Seq<(usize, usize, usize)>, o: ScanOut, lo: int, hi: int)
    requires scan_done(c, ents, o, lo, hi),
    ensures o.out.wf() && lo <= o.stopped <= hi && o.out.view() == contrib(c, ents, lo, o.stopped as int),
{
    reveal(scan_done);
}

/// Add one scan task's records as segments (finishing its range on the calling thread when it stopped early).
fn collect_scan(s: &NumScan, segs: &mut Vec<Vec<Rec>>, o: ScanOut, lo: usize, hi: usize, Ghost(c): Ghost<Ctx>)
    requires
        num_scan_ok(s, c), lo <= hi, (hi as int) <= c.n,
        o.out.wf(), lo <= o.stopped <= hi, o.out.view() == contrib(c, s.ex.list@, lo as int, o.stopped as int),
        flat(old(segs)@) == contrib(c, s.ex.list@, 0, lo as int),
    ensures flat(final(segs)@) == contrib(c, s.ex.list@, 0, hi as int),
{
    let ghost ents = s.ex.list@;
    let ScanOut { out, stopped } = o;
    let v = out.into_vec();
    let ghost s0 = segs@;
    segs.push(v);
    proof {
        lemma_flat_push(s0, v);
        lemma_contrib_split(c, ents, 0, lo as int, stopped as int);
    }
    if stopped < hi {
        let rest = crate::agent::scan::scan_serial(s, stopped, hi, Ghost(c));
        let ghost s1 = segs@;
        segs.push(rest);
        proof {
            lemma_flat_push(s1, rest);
            lemma_contrib_split(c, ents, 0, stopped as int, hi as int);
        }
    }
}

/// The contribution records of the whole num table, as consecutive segments.
pub fn run_scan(s: &NumScan, n: usize, workers: usize, dispatch: &mut Dispatch, Ghost(c): Ghost<Ctx>)
    -> (r: Result<Vec<Vec<Rec>>, WorkerFailure>)
    requires num_scan_ok(s, c), n as int == c.n, 1 <= workers <= MAX_WORKERS,
    ensures r matches Ok(v) ==> flat(v@) == contrib(c, s.ex.list@, 0, c.n),
{    hide(contrib);
    let ghost ents = s.ex.list@;
    let tasks = task_count(n, workers, 262144);
    let b = bounds(n, tasks);
    let mut list: Vec<ScanTask> = Vec::new();
    let mut t: usize = 0;
    while t < tasks
        invariant
            num_scan_ok(s, c), n as int == c.n, b@.len() == tasks, covers(b@, n as int), 1 <= tasks <= MAX_WORKERS,
            t <= tasks, list@.len() == t, ents == s.ex.list@,
            forall|u: int| 0 <= u < t ==> (#[trigger] list@[u]).pre() && list@[u].lo == b@[u].0 && list@[u].hi == b@[u].1
                && list@[u].ctx@ == c && list@[u].scan.ex.list@ == ents,
        decreases tasks - t,
    {
        let (lo, hi) = b[t];
        let cap = (hi - lo) / 16 + 4096;
        let scan = clone_num_scan(s);
        proof {
            lemma_num_scan_copy(s, &scan, c);
        }
        let task = ScanTask { lo, hi, scan, out: Buf::new(cap, (0, 0, 0)), sc: scratch_new(), ctx: Ghost(c) };
        list.push(task);
        t = t + 1;
    }
    let ghost tl = list@;
    let outs: Vec<ScanOut> = if tasks == 1 {
        let task = list.pop().unwrap();
        proof {
            assert(task == tl[0]);
        }
        let o = task.run();
        let mut v: Vec<ScanOut> = Vec::new();
        v.push(o);
        v
    } else {
        match fork_join(dispatch, list) {
            Ok(v) => v,
            Err(e) => return Err(e),
        }
    };
    let mut all: Vec<Vec<Rec>> = Vec::new();
    let mut outs = outs;
    let ghost ov = outs@;
    proof {
        assert forall|w: int| 0 <= w < tasks implies #[trigger] scan_done(c, ents, ov[w], b@[w].0 as int, b@[w].1 as int) by {
            assert(tl[w].post(ov[w]));
            reveal(scan_done);
        }
    }
    let mut u: usize = 0;
    proof {
        reveal(contrib);
        assert(flat(all@) =~= contrib(c, ents, 0, 0));
    }
    while u < tasks
        invariant
            num_scan_ok(s, c), n as int == c.n, b@.len() == tasks, covers(b@, n as int), u <= tasks, ents == s.ex.list@,
            ov.len() == tasks, outs@ == ov.subrange(u as int, tasks as int),
            forall|w: int| 0 <= w < tasks ==> #[trigger] scan_done(c, ents, ov[w], b@[w].0 as int, b@[w].1 as int),
            flat(all@) == contrib(c, ents, 0, if u == 0 { 0 } else { b@[u - 1].1 as int }),
        decreases tasks - u,
    {
        let o = outs.remove(0);
        proof {
            assert(o == ov[u as int]);
            assert(outs@ =~= ov.subrange(u + 1, tasks as int));
        }
        let (lo, hi) = b[u];
        proof {
            lemma_scan_done(c, ents, o, lo as int, hi as int);
            if u > 0 {
                assert(b@[u as int].0 == b@[u - 1].1);
            }
        }
        collect_scan(s, &mut all, o, lo, hi, Ghost(c));
        u = u + 1;
    }
    Ok(all)
}

} // verus!
