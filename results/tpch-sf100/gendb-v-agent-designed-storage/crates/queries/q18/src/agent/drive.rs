//! Running the kernels. The fast path (`run_fast`, cluster flag set): split the orders into at most `workers` ranges
//! of about equal lineitem rows, cut at order runs (`plan_bounds`), run one `kernel::Chunk` per range with
//! `fork_join` (on the calling thread for one range), and merge the ranges' top-100 buffers in range order
//! (`topk_insert` of every row, then `common::topk::lemma_topk_absorb`). The general path (`run_general`): one chunk
//! over all orders with lineitem scans. The run path (`run_runs`, run directory present): the same, with chunks cut
//! at sampled run starts (`plan_runs`) and scanned run by run (`scan::scan_runs`). Each gives `run_ok`: the top 100 of all groups (`qspec::gseq(0, o_n)`).
//! `emit` writes the result rows.
use vstd::prelude::*;
use vstd::slice::slice_to_vec;
use crate::spec::value::*;
use crate::exec::value::{EVal, view_row};
use crate::link::query::view_rows;
use crate::gendb_entry::parallel::{Dispatch, WorkerTask, fork_join, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::gendb_entry::work::filled;
use crate::stores::custpart::interface::common::read as cr;
use super::common::topk::*;
use super::model::*;
use super::qspec::*;
use super::cand::*;
use super::kernel::*;
use super::plan::*;
use super::answer::lemma_gseq_wf;
use super::scan::lemma_rs_mono;

verus! {

/// A run's result: the top-100 buffer.
pub struct RunOut {
    pub buf: Vec<Cand>,
    pub len: usize,
}

/// Every buffered candidate's customer row is a stored row.
pub open spec fn cpos_ok(m: M, buf: Seq<Cand>, len: int) -> bool {
    forall|i: int| 0 <= i < len ==> (#[trigger] buf[i]).cpos < m.c_n
}

pub open spec fn run_ok(m: M, p: QP, r: RunOut) -> bool {
    &&& r.buf@.len() == K
    &&& r.len <= K
    &&& topk_ok(q18_keys(), q18_fams(), K as nat, cands_view(m, r.buf@, r.len as int), gseq(m, p, 0, m.o_n))
    &&& cpos_ok(m, r.buf@, r.len as int)
}

/// One task's run, on the calling thread.
fn run_one(task: Chunk) -> (out: ChunkOut)
    requires task.pre(),
    ensures task.post(out),
{
    task.run()
}

/// The zero candidate (buffer filler).
fn zero_cand() -> Cand {
    Cand { q: 0, okey: 0, ck: 0, cpos: 0, date: 0, tp: 0, sum: 0 }
}

/// The general path: one chunk over every order, scanning the lineitems.
pub fn run_general(c: Cols, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: RunOut)
    requires cols_ok(c, m, p), model_ok(m),
    ensures run_ok(m, p, r),
{
    let task = Chunk { cols: c, o_lo: 0, o_hi: c.o_n, l_lo: 0, l_hi: 0, fast: false, runs: false, r_lo: 0, r_hi: 0, qm: 0, kmin: 0,
        long: false, buf: filled(K, zero_cand()), m: Ghost(m), p: Ghost(p) };
    let ghost tv = task;
    let out = run_one(task);
    proof {
        assert(chunk_post(tv, out));
    }
    RunOut { buf: out.buf, len: out.len }
}

/// Rows of a range of groups, followed by rows of a later range's top 100, are distinct with their keys in families.
pub proof fn lemma_merge_wf(m: M, p: QP, lo: int, mid: int, hi: int, l: Seq<Row>, i: int)
    requires
        model_ok(m),
        0 <= lo <= mid <= hi <= m.o_n,
        topk_ok(q18_keys(), q18_fams(), K as nat, l, gseq(m, p, mid, hi)),
        0 <= i <= l.len(),
    ensures
        rel_wf(q18_keys(), q18_fams(), gseq(m, p, lo, mid) + l.subrange(0, i)),
{
    let a = gseq(m, p, lo, mid);
    let b = l.subrange(0, i);
    lemma_gseq_wf(m, p, lo, mid);
    lemma_gseq_contains(m, p, lo, mid);
    lemma_gseq_contains(m, p, mid, hi);
    assert(b.no_duplicates());
    assert forall|x: int, y: int| 0 <= x < a.len() && 0 <= y < b.len() implies a[x] != b[y] by {
        assert(a.contains(a[x]));
        assert(gseq(m, p, mid, hi).contains(l[y]));
        let q1 = choose|q: int| lo <= q < mid && good(m, p, q) && a[x] == grow(m, p, q);
        let q2 = choose|q: int| mid <= q < hi && good(m, p, q) && l[y] == grow(m, p, q);
        if a[x] == b[y] {
            assert(grow(m, p, q1)[2] == grow(m, p, q2)[2]);
            assert(okey(m, q1) == okey(m, q2));
        }
    }
    vstd::seq_lib::lemma_no_dup_in_concat(a, b);
    assert forall|t: int| 0 <= t < (a + b).len() implies crate::bridge::order::keys_ok(q18_keys(), q18_fams(), #[trigger] (a + b)[t]) by {
        if t < a.len() {
            assert((a + b)[t] == a[t]);
        } else {
            assert((a + b)[t] == l[t - a.len()]);
        }
    }
}

/// The chunk boundaries of the orders `[o0, pe)` and their lineitems `[l0, lp)`: `bo[k]`, `bl[k]`.
pub open spec fn bounds_ok(m: M, bo: Seq<usize>, bl: Seq<usize>, n: int, o0: int, l0: int, pe: int, lp: int) -> bool {
    &&& bo.len() == n && bl.len() == n
    &&& n >= 1 && bo[0] == o0 && bl[0] == l0
    &&& forall|k: int| 0 <= k < n ==> lb_ok(m, #[trigger] bo[k] as int, bl[k] as int) && bo[k] <= pe && bl[k] <= lp
    &&& forall|k: int| 0 <= k < n - 1 ==> #[trigger] bo[k] <= bo[k + 1] && bl[k] <= bl[k + 1]
}

/// Chunk boundaries: `ntasks` ranges of about equal lineitem rows, cut at order runs.
fn plan_bounds(c: &Cols, ntasks: usize, o0: usize, l0: usize, pe: usize, lp: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>)
    -> (r: (Vec<usize>, Vec<usize>))
    requires
        cols_ok(*c, m, p), model_ok(m), m.cluster == 1, c.idx_ok,
        1 <= ntasks <= MAX_WORKERS,
        lb_ok(m, o0 as int, l0 as int), lb_ok(m, pe as int, lp as int),
        o0 <= pe <= m.o_n, l0 <= lp <= m.l_n,
    ensures
        bounds_ok(m, r.0@, r.1@, ntasks + 1, o0 as int, l0 as int, pe as int, lp as int),
        r.0@[ntasks as int] == pe, r.1@[ntasks as int] == lp,
{
    let mut bo: Vec<usize> = Vec::new();
    let mut bl: Vec<usize> = Vec::new();
    bo.push(o0);
    bl.push(l0);
    let span = lp - l0;
    let step = span / ntasks;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(span as int, ntasks as int);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(span as int, ntasks as int);
        assert(ntasks * step == step * ntasks) by (nonlinear_arith);
    }
    let mut i: usize = 1;
    while i < ntasks
        invariant
            cols_ok(*c, m, p), model_ok(m), m.cluster == 1, c.idx_ok,
            1 <= i <= ntasks <= MAX_WORKERS,
            lb_ok(m, pe as int, lp as int),
            o0 <= pe <= m.o_n, l0 <= lp <= m.l_n,
            span == lp - l0,
            step * ntasks <= span,
            bounds_ok(m, bo@, bl@, i as int, o0 as int, l0 as int, pe as int, lp as int),
        decreases ntasks - i,
    {
        proof {
            assert(step * i <= step * ntasks) by (nonlinear_arith) requires i <= ntasks, step >= 0;
        }
        let row = l0 + step * i;
        let prev_o = bo[i - 1];
        let prev_l = bl[i - 1];
        let (o, l) = if row < lp {
            boundary(c, row, prev_o, prev_l, pe, lp, Ghost(m), Ghost(p))
        } else {
            (prev_o, prev_l)
        };
        let ghost bo0 = bo@;
        let ghost bl0 = bl@;
        bo.push(o);
        bl.push(l);
        proof {
            assert(bo@[i as int] == o && bl@[i as int] == l);
            assert forall|k: int| 0 <= k < i + 1 implies lb_ok(m, #[trigger] bo@[k] as int, bl@[k] as int) && bo@[k] <= pe && bl@[k] <= lp by {
                if k < i {
                    assert(bo@[k] == bo0[k] && bl@[k] == bl0[k]);
                }
            }
            assert forall|k: int| 0 <= k < i + 1 - 1 implies #[trigger] bo@[k] <= bo@[k + 1] && bl@[k] <= bl@[k + 1] by {
                if k < i - 1 {
                    assert(bo@[k] == bo0[k] && bl@[k] == bl0[k] && bo@[k + 1] == bo0[k + 1] && bl@[k + 1] == bl0[k + 1]);
                } else {
                    assert(bo@[k] == bo0[k] && bl@[k] == bl0[k]);
                }
            }
        }
        i = i + 1;
    }
    let ghost bo0 = bo@;
    let ghost bl0 = bl@;
    bo.push(pe);
    bl.push(lp);
    proof {
        assert forall|k: int| 0 <= k < ntasks + 1 implies lb_ok(m, #[trigger] bo@[k] as int, bl@[k] as int) && bo@[k] <= pe && bl@[k] <= lp by {
            if k < ntasks {
                assert(bo@[k] == bo0[k] && bl@[k] == bl0[k]);
            }
        }
        assert forall|k: int| 0 <= k < ntasks implies #[trigger] bo@[k] <= bo@[k + 1] && bl@[k] <= bl@[k + 1] by {
            assert(bo@[k] == bo0[k] && bl@[k] == bl0[k]);
            if k < ntasks - 1 {
                assert(bo@[k + 1] == bo0[k + 1] && bl@[k + 1] == bl0[k + 1]);
            }
        }
    }
    (bo, bl)
}

/// Merge the top 100 `obuf` of the groups of `[lo, hi)` into the top 100 `fin` of the groups of `[o0, lo)`.
fn merge_one(fin: &mut Vec<Cand>, flen: usize, obuf: &Vec<Cand>, olen: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>,
    Ghost(o0): Ghost<int>, Ghost(lo): Ghost<int>, Ghost(hi): Ghost<int>) -> (r: usize)
    requires
        model_ok(m),
        0 <= o0 <= lo <= hi <= m.o_n,
        old(fin)@.len() == K,
        flen <= K,
        topk_ok(q18_keys(), q18_fams(), K as nat, cands_view(m, old(fin)@, flen as int), gseq(m, p, o0, lo)),
        cpos_ok(m, old(fin)@, flen as int),
        obuf@.len() == K,
        olen <= K,
        topk_ok(q18_keys(), q18_fams(), K as nat, cands_view(m, obuf@, olen as int), gseq(m, p, lo, hi)),
        cpos_ok(m, obuf@, olen as int),
    ensures
        final(fin)@.len() == K,
        r <= K,
        topk_ok(q18_keys(), q18_fams(), K as nat, cands_view(m, final(fin)@, r as int), gseq(m, p, o0, hi)),
        cpos_ok(m, final(fin)@, r as int),
{
    let ghost a = gseq(m, p, o0, lo);
    let ghost lv = cands_view(m, obuf@, olen as int);
    let mut flen = flen;
    let mut i: usize = 0;
    proof {
        assert(a + cands_view(m, obuf@, 0) =~= a);
    }
    while i < olen
        invariant
            model_ok(m),
            0 <= o0 <= lo <= hi <= m.o_n,
            obuf@.len() == K, olen <= K,
            lv == cands_view(m, obuf@, olen as int),
            topk_ok(q18_keys(), q18_fams(), K as nat, lv, gseq(m, p, lo, hi)),
            cpos_ok(m, obuf@, olen as int),
            a == gseq(m, p, o0, lo),
            i <= olen,
            fin@.len() == K,
            flen <= K,
            topk_ok(q18_keys(), q18_fams(), K as nat, cands_view(m, fin@, flen as int), a + cands_view(m, obuf@, i as int)),
            cpos_ok(m, fin@, flen as int),
        decreases olen - i,
    {
        let cand = obuf[i];
        let ghost all = a + cands_view(m, obuf@, i as int);
        let ghost fb = fin@;
        let ghost fl = flen;
        proof {
            lemma_view_push(m, obuf@, i as int);
            assert(all.push(cand_row(m, cand)) =~= a + cands_view(m, obuf@, i + 1));
            assert(cands_view(m, obuf@, i + 1) =~= lv.subrange(0, i + 1));
            lemma_merge_wf(m, p, o0, lo, hi, lv, i + 1);
        }
        flen = topk_insert(fin, flen, cand, Ghost(m), Ghost(all));
        proof {
            assert forall|t: int| 0 <= t < flen implies (#[trigger] fin@[t]).cpos < m.c_n by {
                if fin@[t] != cand {
                    let u = choose|u: int| 0 <= u < fl && fin@[t] == fb[u];
                }
            }
        }
        i = i + 1;
    }
    proof {
        lemma_gseq_split(m, p, o0, lo, hi);
        lemma_gseq_wf(m, p, o0, hi);
        lemma_gseq_wf(m, p, lo, hi);
        lemma_topk_absorb(q18_keys(), q18_fams(), K as nat, cands_view(m, fin@, flen as int), a, lv, gseq(m, p, lo, hi));
    }
    flen
}

/// The tasks' results: each satisfies its task's postcondition over the boundaries `bo`.
#[verifier::opaque]
pub open spec fn outs_ok(m: M, p: QP, tv: Seq<Chunk>, outs: Seq<ChunkOut>, bo: Seq<usize>, n: int) -> bool {
    &&& outs.len() == n
    &&& tv.len() == n
    &&& forall|k: int| 0 <= k < n ==> (#[trigger] tv[k]).post(outs[k])
        && tv[k].o_lo == bo[k] && tv[k].o_hi == bo[k + 1] && tv[k].m@ == m && tv[k].p@ == p
}

/// Task `t`'s result.
proof fn lemma_outs_at(m: M, p: QP, tv: Seq<Chunk>, outs: Seq<ChunkOut>, bo: Seq<usize>, n: int, t: int)
    requires outs_ok(m, p, tv, outs, bo, n), 0 <= t < n,
    ensures
        outs.len() == n,
        chunk_post(tv[t], outs[t]),
        tv[t].o_lo == bo[t], tv[t].o_hi == bo[t + 1], tv[t].m@ == m, tv[t].p@ == p,
{
    reveal(outs_ok);
    assert(tv[t].post(outs[t]));
}

/// Consecutive boundaries are ordered below the end.
proof fn lemma_bounds_at(m: M, bo: Seq<usize>, bl: Seq<usize>, n: int, o0: int, l0: int, pe: int, lp: int, t: int)
    requires bounds_ok(m, bo, bl, n, o0, l0, pe, lp), 0 <= t < n - 1,
    ensures o0 <= bo[t] <= bo[t + 1] <= pe,
    decreases t,
{
    assert(bo[t] <= bo[t + 1]);
    assert(lb_ok(m, bo[t + 1] as int, bl[t + 1] as int) && bo[t + 1] <= pe);
    if t > 0 {
        lemma_bounds_at(m, bo, bl, n, o0, l0, pe, lp, t - 1);
    }
}

/// The fast path over the co-clustered layout, with at most `workers` threads.
pub fn run_fast(c: Cols, workers: usize, dispatch: &mut Dispatch, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>)
    -> (r: Result<RunOut, WorkerFailure>)
    requires
        cols_ok(c, m, p), model_ok(m), m.cluster == 1, c.idx_ok,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(ro) ==> run_ok(m, p, ro),
{
    let pe = c.o_n;
    let lp = lb_search(&c, pe, Ghost(m), Ghost(p));
    proof {
        assert forall|t: int| 0 <= t < m.l_n implies #[trigger] lpos(m, t) >= 0 by {
            crate::agent::facts::lemma_opos(m, lkey(m, t));
        }
        assert(lb_ok(m, 0, 0));
    }
    let ntasks = workers;
    let (bo, bl) = plan_bounds(&c, ntasks, 0, 0, pe, lp, Ghost(m), Ghost(p));
    let mut tasks: Vec<Chunk> = Vec::new();
    let mut t: usize = 0;
    while t < ntasks
        invariant
            cols_ok(c, m, p), model_ok(m), m.cluster == 1, c.idx_ok,
            t <= ntasks <= MAX_WORKERS,
            bounds_ok(m, bo@, bl@, ntasks + 1, 0, 0, pe as int, lp as int),
            bo@[ntasks as int] == pe, bl@[ntasks as int] == lp,
            pe == m.o_n, lp <= m.l_n,
            tasks.len() == t,
            forall|k: int| 0 <= k < t ==> (#[trigger] tasks@[k]).pre()
                && tasks@[k].o_lo == bo@[k] && tasks@[k].o_hi == bo@[k + 1] && tasks@[k].m@ == m && tasks@[k].p@ == p,
        decreases ntasks - t,
    {
        proof {
            assert(bo@[t as int] <= bo@[t + 1]);
            assert(bl@[t as int] <= bl@[t + 1]);
            assert(lb_ok(m, bo@[t as int] as int, bl@[t as int] as int));
            assert(lb_ok(m, bo@[t + 1] as int, bl@[t + 1] as int));
            lemma_bounds_at(m, bo@, bl@, ntasks + 1, 0, 0, pe as int, lp as int, t as int);
        }
        let task = Chunk {
            cols: c, o_lo: bo[t], o_hi: bo[t + 1], l_lo: bl[t], l_hi: bl[t + 1], fast: true, runs: false, r_lo: 0, r_hi: 0,
            qm: 0, kmin: 0, long: false, buf: filled(K, zero_cand()), m: Ghost(m), p: Ghost(p),
        };
        tasks.push(task);
        t = t + 1;
    }
    finish(tasks, &bo, &bl, ntasks, pe, lp, dispatch, Ghost(m), Ghost(p))
}

/// Run the tasks (`fork_join`, or on the calling thread for one task) and merge their top-100 buffers in range order.
fn finish(tasks: Vec<Chunk>, bo: &Vec<usize>, bl: &Vec<usize>, ntasks: usize, pe: usize, lp: usize, dispatch: &mut Dispatch,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: Result<RunOut, WorkerFailure>)
    requires
        model_ok(m),
        1 <= ntasks <= MAX_WORKERS,
        bounds_ok(m, bo@, bl@, ntasks + 1, 0, 0, pe as int, lp as int),
        bo@[ntasks as int] == pe,
        pe == m.o_n,
        tasks.len() == ntasks,
        forall|k: int| 0 <= k < ntasks ==> (#[trigger] tasks@[k]).pre()
            && tasks@[k].o_lo == bo@[k] && tasks@[k].o_hi == bo@[k + 1] && tasks@[k].m@ == m && tasks@[k].p@ == p,
    ensures
        r matches Ok(ro) ==> run_ok(m, p, ro),
{
    let mut tasks = tasks;
    let ghost tv = tasks@;
    let outs = if ntasks == 1 {
        let task = tasks.pop().unwrap();
        proof {
            assert(task == tv[0]);
        }
        let out = run_one(task);
        let mut v: Vec<ChunkOut> = Vec::new();
        v.push(out);
        proof {
            assert(v@ =~= seq![out]);
        }
        v
    } else {
        match fork_join(dispatch, tasks) {
            Ok(o) => o,
            Err(e) => {
                return Err(e);
            },
        }
    };
    proof {
        reveal(outs_ok);
        assert(outs_ok(m, p, tv, outs@, bo@, ntasks as int));
    }
    // merge the ranges' top-100 buffers in range order
    let mut fin: Vec<Cand> = filled(K, zero_cand());
    let mut flen: usize = 0;
    proof {
        lemma_topk_empty(q18_keys(), q18_fams(), K as nat);
        lemma_gseq_empty(m, p, 0);
        assert(cands_view(m, fin@, 0) =~= Seq::<Row>::empty());
    }
    let mut t: usize = 0;
    while t < ntasks
        invariant
            model_ok(m),
            t <= ntasks <= MAX_WORKERS,
            bounds_ok(m, bo@, bl@, ntasks + 1, 0, 0, pe as int, lp as int),
            bo@[ntasks as int] == pe,
            pe == m.o_n,
            outs_ok(m, p, tv, outs@, bo@, ntasks as int),
            fin@.len() == K,
            flen <= K,
            topk_ok(q18_keys(), q18_fams(), K as nat, cands_view(m, fin@, flen as int), gseq(m, p, 0, bo@[t as int] as int)),
            cpos_ok(m, fin@, flen as int),
        decreases ntasks - t,
    {
        proof {
            lemma_outs_at(m, p, tv, outs@, bo@, ntasks as int, t as int);
            lemma_bounds_at(m, bo@, bl@, ntasks + 1, 0, 0, pe as int, lp as int, t as int);
        }
        let ghost lo = bo@[t as int] as int;
        let ghost hi = bo@[t + 1] as int;
        flen = merge_one(&mut fin, flen, &outs[t].buf, outs[t].len, Ghost(m), Ghost(p), Ghost(0), Ghost(lo), Ghost(hi));
        t = t + 1;
    }
    Ok(RunOut { buf: fin, len: flen })
}

/// The largest zone maximum: an upper bound of every l_quantity (mode 1).
fn zone_max(c: &Cols, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (qm: i128)
    requires cols_ok(*c, m, p), rcols_ok(*c, m), model_ok(m), runs_ok(m), m.r_mode == 1,
    ensures
        i64::MIN <= qm <= i64::MAX,
        forall|j: int| 0 <= j < m.l_n ==> #[trigger] lqty(m, j) <= qm,
{
    reveal(runs_ok);
    let mut qm: i64 = i64::MIN;
    let mut g: usize = 0;
    while g < c.qz_n
        invariant
            cols_ok(*c, m, p), rcols_ok(*c, m),
            g <= m.qz.len(),
            forall|h: int| 0 <= h < g ==> m.qz[h] <= qm,
        decreases m.qz.len() - g,
    {
        if c.qz[g] > qm {
            qm = c.qz[g];
        }
        g = g + 1;
    }
    proof {
        assert forall|j: int| 0 <= j < m.l_n implies #[trigger] lqty(m, j) <= qm by {
            lemma_block_bound(j, m.l_bs, m.l_n, m.l_nb);
            assert(lqty(m, j) <= m.qz[j / m.l_bs]);
        }
    }
    qm as i128
}

/// The chunk boundaries of the run path: `bounds_ok` boundaries whose lineitem rows `bl[k]` start run `br[k]`.
pub open spec fn rbounds_ok(m: M, bo: Seq<usize>, bl: Seq<usize>, br: Seq<usize>, n: int, pe: int, lp: int) -> bool {
    &&& bounds_ok(m, bo, bl, n, 0, 0, pe, lp)
    &&& runs_at_ok(m, bl, br, n)
}

/// Sample `b` is the start row of run `b * stride`, a row of the table.
proof fn lemma_sample(m: M, b: int)
    requires model_ok(m), runs_ok(m), m.r_mode == 1, 0 <= b < m.r_starts.len(),
    ensures
        b * m.r_stride < nruns(m),
        rs(m, b * m.r_stride) == m.r_starts[b],
        m.r_starts[b] < m.l_n,
{
    reveal(runs_ok);
    assert(crate::stores::liruns::interface::start_ok(m.r_lens, m.r_starts, m.r_stride, b));
    let rr = b * m.r_stride;
    lemma_rs_mono(m, rr + 1, nruns(m));
    assert(rs(m, rr + 1) == rs(m, rr) + m.r_lens[rr]);
    assert(m.r_lens[rr] >= 1 && run_same_m(m, rr));
}

/// One more boundary `(o, l)` after the last one keeps the boundaries ordered.
proof fn lemma_bpush(m: M, bo: Seq<usize>, bl: Seq<usize>, n: int, pe: int, lp: int, o: usize, l: usize)
    requires
        bounds_ok(m, bo, bl, n, 0, 0, pe, lp),
        lb_ok(m, o as int, l as int), o <= pe, l <= lp,
        bo[n - 1] <= o, bl[n - 1] <= l,
    ensures
        bounds_ok(m, bo.push(o), bl.push(l), n + 1, 0, 0, pe, lp),
{
    let (bo2, bl2) = (bo.push(o), bl.push(l));
    assert forall|k: int| 0 <= k < n + 1 implies lb_ok(m, #[trigger] bo2[k] as int, bl2[k] as int) && bo2[k] <= pe && bl2[k] <= lp by {
        if k < n {
            assert(bo2[k] == bo[k] && bl2[k] == bl[k]);
        }
    }
    assert forall|k: int| 0 <= k < n + 1 - 1 implies #[trigger] bo2[k] <= bo2[k + 1] && bl2[k] <= bl2[k + 1] by {
        assert(bo2[k] == bo[k] && bl2[k] == bl[k]);
        if k < n - 1 {
            assert(bo2[k + 1] == bo[k + 1] && bl2[k + 1] == bl[k + 1]);
        }
    }
}

/// The run part of `rbounds_ok`.
pub open spec fn runs_at_ok(m: M, bl: Seq<usize>, br: Seq<usize>, n: int) -> bool {
    &&& br.len() == n && br[0] == 0
    &&& forall|k: int| 0 <= k < n ==> #[trigger] br[k] <= nruns(m) && rs(m, br[k] as int) == bl[k]
    &&& forall|k: int| 0 <= k < n - 1 ==> #[trigger] br[k] <= br[k + 1]
}

/// One more run boundary `r` (starting row `l`) after the last one.
proof fn lemma_rpush_runs(m: M, bl: Seq<usize>, br: Seq<usize>, n: int, l: usize, r: usize)
    requires
        runs_at_ok(m, bl, br, n), bl.len() == n, n >= 1,
        br[n - 1] <= r, r <= nruns(m), rs(m, r as int) == l,
    ensures
        runs_at_ok(m, bl.push(l), br.push(r), n + 1),
{
    let (bl2, br2) = (bl.push(l), br.push(r));
    assert forall|k: int| 0 <= k < n + 1 implies #[trigger] br2[k] <= nruns(m) && rs(m, br2[k] as int) == bl2[k] by {
        if k < n {
            assert(br2[k] == br[k] && bl2[k] == bl[k]);
        }
    }
    assert forall|k: int| 0 <= k < n + 1 - 1 implies #[trigger] br2[k] <= br2[k + 1] by {
        assert(br2[k] == br[k]);
        if k < n - 1 {
            assert(br2[k + 1] == br[k + 1]);
        }
    }
}

/// One more boundary `(o, l, r)` after the last one keeps the run boundaries ordered.
proof fn lemma_rpush(m: M, bo: Seq<usize>, bl: Seq<usize>, br: Seq<usize>, n: int, pe: int, lp: int, o: usize, l: usize,
    r: usize)
    requires
        rbounds_ok(m, bo, bl, br, n, pe, lp),
        lb_ok(m, o as int, l as int), o <= pe, l <= lp,
        bo[n - 1] <= o, bl[n - 1] <= l, br[n - 1] <= r,
        r <= nruns(m), rs(m, r as int) == l,
    ensures
        rbounds_ok(m, bo.push(o), bl.push(l), br.push(r), n + 1, pe, lp),
{
    assert(runs_at_ok(m, bl, br, n));
    lemma_bpush(m, bo, bl, n, pe, lp, o, l);
    lemma_rpush_runs(m, bl, br, n, l, r);
    assert(runs_at_ok(m, bl.push(l), br.push(r), n + 1));
}

/// Chunk boundaries at sampled run starts: `ntasks` ranges of about equal run counts.
fn plan_runs(c: &Cols, ntasks: usize, pe: usize, lp: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>)
    -> (r: (Vec<usize>, Vec<usize>, Vec<usize>))
    requires
        cols_ok(*c, m, p), rcols_ok(*c, m), model_ok(m), runs_ok(m), m.r_mode == 1, m.cluster == 1, c.idx_ok,
        1 <= ntasks <= MAX_WORKERS,
        lb_ok(m, pe as int, lp as int),
        pe == m.o_n, lp == m.l_n,
        c.r_stride <= usize::MAX,
    ensures
        rbounds_ok(m, r.0@, r.1@, r.2@, ntasks + 1, pe as int, lp as int),
        r.0@[ntasks as int] == pe, r.1@[ntasks as int] == lp, r.2@[ntasks as int] == nruns(m),
{
    let mut bo: Vec<usize> = Vec::new();
    let mut bl: Vec<usize> = Vec::new();
    let mut br: Vec<usize> = Vec::new();
    bo.push(0);
    bl.push(0);
    br.push(0);
    proof {
        assert forall|t: int| 0 <= t < m.l_n implies #[trigger] lpos(m, t) >= 0 by {
            crate::agent::facts::lemma_opos(m, lkey(m, t));
        }
        assert(lb_ok(m, 0, 0));
        assert(rs(m, 0) == 0);
    }
    let stride = c.r_stride as usize;
    let per = c.r_sn / ntasks;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(c.r_sn as int, ntasks as int);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(c.r_sn as int, ntasks as int);
        assert(per * ntasks == ntasks * per) by (nonlinear_arith);
    }
    let mut i: usize = 1;
    while i < ntasks
        invariant
            cols_ok(*c, m, p), rcols_ok(*c, m), model_ok(m), runs_ok(m), m.r_mode == 1, m.cluster == 1, c.idx_ok,
            1 <= i <= ntasks <= MAX_WORKERS,
            lb_ok(m, pe as int, lp as int),
            pe == m.o_n, lp == m.l_n,
            stride as int == m.r_stride,
            per * ntasks <= c.r_sn,
            rbounds_ok(m, bo@, bl@, br@, i as int, pe as int, lp as int),
        decreases ntasks - i,
    {
        proof {
            assert(per * i <= per * ntasks) by (nonlinear_arith) requires i <= ntasks, per >= 0;
        }
        let b = per * i;
        let prev_o = bo[i - 1];
        let prev_l = bl[i - 1];
        let prev_r = br[i - 1];
        let mut nxt = (prev_o, prev_l, prev_r);
        if b < c.r_sn {
            proof {
                lemma_sample(m, b as int);
            }
            let rr = b * stride;
            let t = c.r_starts[b];
            proof {
                assert(prev_l <= lp);
            }
            if rr >= prev_r {
                let (o, l) = boundary(c, t as usize, prev_o, prev_l, pe, lp, Ghost(m), Ghost(p));
                if l == t as usize {
                    nxt = (o, l, rr);
                }
            }
        }
        let ghost bo0 = bo@;
        let ghost bl0 = bl@;
        let ghost br0 = br@;
        bo.push(nxt.0);
        bl.push(nxt.1);
        br.push(nxt.2);
        proof {
            lemma_rpush(m, bo0, bl0, br0, i as int, pe as int, lp as int, nxt.0, nxt.1, nxt.2);
            assert(bo@ == bo0.push(nxt.0) && bl@ == bl0.push(nxt.1) && br@ == br0.push(nxt.2));
        }
        i = i + 1;
    }
    let ghost bo0 = bo@;
    let ghost bl0 = bl@;
    let ghost br0 = br@;
    bo.push(pe);
    bl.push(lp);
    br.push(c.r_n);
    proof {
        reveal(runs_ok);
        lemma_rpush(m, bo0, bl0, br0, ntasks as int, pe as int, lp as int, pe, lp, c.r_n);
        assert(bo@ == bo0.push(pe) && bl@ == bl0.push(lp) && br@ == br0.push(c.r_n));
    }
    (bo, bl, br)
}

/// Consecutive run boundaries are ordered below the run count.
proof fn lemma_rbounds_at(m: M, bo: Seq<usize>, bl: Seq<usize>, br: Seq<usize>, n: int, pe: int, lp: int, t: int)
    requires rbounds_ok(m, bo, bl, br, n, pe, lp), 0 <= t < n - 1,
    ensures
        br[t] <= br[t + 1] <= nruns(m),
        rs(m, br[t] as int) == bl[t], rs(m, br[t + 1] as int) == bl[t + 1],
{
    assert(br[t] <= br[t + 1]);
    assert(br[t] <= nruns(m) && rs(m, br[t] as int) == bl[t]);
    assert(br[t + 1] <= nruns(m) && rs(m, br[t + 1] as int) == bl[t + 1]);
}

/// The run path over the run directory, with at most `workers` threads (the row scan when the lineitem rows do not
/// all belong to orders or the stride does not fit `usize`).
pub fn run_runs(c: Cols, workers: usize, dispatch: &mut Dispatch, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>)
    -> (r: Result<RunOut, WorkerFailure>)
    requires
        cols_ok(c, m, p), rcols_ok(c, m), lcols_ok(c, m), model_ok(m), runs_ok(m), long_ok(m), m.r_mode == 1, m.cluster == 1, c.idx_ok,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(ro) ==> run_ok(m, p, ro),
{
    let pe = c.o_n;
    let lp = lb_search(&c, pe, Ghost(m), Ghost(p));
    proof {
        reveal(runs_ok);
    }
    if lp != c.l_n || c.r_stride > usize::MAX as u64 {
        return run_fast(c, workers, dispatch, Ghost(m), Ghost(p));
    }
    let qm = zone_max(&c, Ghost(m), Ghost(p));
    let kmin = super::scan::kmin_of(qm, c.thr);
    // the run permutation by length serves when only the longest runs may be above `$1`
    let long = c.lg_mode == 1 && kmin as u64 >= c.lg_max;
    let ntasks = workers;
    let (bo, bl, br) = plan_runs(&c, ntasks, pe, lp, Ghost(m), Ghost(p));
    let mut tasks: Vec<Chunk> = Vec::new();
    let mut t: usize = 0;
    while t < ntasks
        invariant
            cols_ok(c, m, p), rcols_ok(c, m), model_ok(m), runs_ok(m), m.r_mode == 1, m.cluster == 1, c.idx_ok,
            t <= ntasks <= MAX_WORKERS,
            rbounds_ok(m, bo@, bl@, br@, ntasks + 1, pe as int, lp as int),
            bo@[ntasks as int] == pe, bl@[ntasks as int] == lp,
            pe == m.o_n, lp == m.l_n,
            i64::MIN <= qm <= i64::MAX,
            forall|j: int| 0 <= j < m.l_n ==> #[trigger] lqty(m, j) <= qm,
            super::scan::kmin_ok(qm as int, c.thr as int, kmin as int),
            long ==> super::scan::long_use_ok(m, kmin as int),
            lcols_ok(c, m),
            tasks.len() == t,
            forall|k: int| 0 <= k < t ==> (#[trigger] tasks@[k]).pre()
                && tasks@[k].o_lo == bo@[k] && tasks@[k].o_hi == bo@[k + 1] && tasks@[k].m@ == m && tasks@[k].p@ == p,
        decreases ntasks - t,
    {
        proof {
            assert(bo@[t as int] <= bo@[t + 1]);
            assert(bl@[t as int] <= bl@[t + 1]);
            assert(lb_ok(m, bo@[t as int] as int, bl@[t as int] as int));
            assert(lb_ok(m, bo@[t + 1] as int, bl@[t + 1] as int));
            lemma_bounds_at(m, bo@, bl@, ntasks + 1, 0, 0, pe as int, lp as int, t as int);
            lemma_rbounds_at(m, bo@, bl@, br@, ntasks + 1, pe as int, lp as int, t as int);
        }
        let task = Chunk {
            cols: c, o_lo: bo[t], o_hi: bo[t + 1], l_lo: bl[t], l_hi: bl[t + 1], fast: true, runs: true,
            r_lo: br[t], r_hi: br[t + 1], qm, kmin, long, buf: filled(K, zero_cand()), m: Ghost(m), p: Ghost(p),
        };
        tasks.push(task);
        t = t + 1;
    }
    finish(tasks, &bo, &bl, ntasks, pe, lp, dispatch, Ghost(m), Ghost(p))
}

// ------------------------------------------------------------------------------------------------ output rows

/// The dates of the groups are SQL dates (inside `i32`).
pub proof fn lemma_dates(m: M, p: QP, buf: Seq<Cand>, len: int)
    requires
        model_ok(m),
        0 <= len <= buf.len(),
        topk_ok(q18_keys(), q18_fams(), K as nat, cands_view(m, buf, len), gseq(m, p, 0, m.o_n)),
    ensures
        forall|i: int| 0 <= i < len ==> i32::MIN <= #[trigger] buf[i].date <= i32::MAX,
{
    lemma_gseq_contains(m, p, 0, m.o_n);
    assert forall|i: int| 0 <= i < len implies i32::MIN <= #[trigger] buf[i].date <= i32::MAX by {
        let v = cands_view(m, buf, len);
        assert(v[i] == cand_row(m, buf[i]));
        assert(gseq(m, p, 0, m.o_n).contains(v[i]));
        let q = choose|q: int| 0 <= q < m.o_n && good(m, p, q) && v[i] == grow(m, p, q);
        assert(v[i][3] == Val::Date(buf[i].date as int));
        assert(grow(m, p, q)[3] == Val::Date(odate(m, q)));
        assert(crate::spec::datetime::date_valid(odate(m, q)));
    }
}

/// The output row of candidate `cd`.
fn cand_out(c: &Cols, cd: Cand, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (row: Vec<EVal>)
    requires
        cols_ok(*c, m, p), model_ok(m),
        cd.cpos < m.c_n,
        i32::MIN <= cd.date <= i32::MAX,
    ensures view_row(row@) == cand_row(m, cd),
{
    proof {
        assert(crate::stores::custpart::interface::common::colfmt::text_range_ok(m.c_name_o, m.c_name_y, cd.cpos as int));
    }
    let name = slice_to_vec(cr::text_slice(c.c_name_o, c.c_name_y, cd.cpos));
    let row = vec![EVal::Text(name), EVal::Int(cd.ck), EVal::Int(cd.okey), EVal::Date(cd.date as i32),
        EVal::Num { coeff: cd.tp as i128, scale: 2 }, EVal::Num { coeff: cd.sum, scale: 2 }];
    proof {
        assert(view_row(row@) =~= cand_row(m, cd));
    }
    row
}

/// The result rows of a top-100 buffer.
pub fn emit(c: &Cols, buf: &Vec<Cand>, len: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (rows: Vec<Vec<EVal>>)
    requires
        cols_ok(*c, m, p), model_ok(m),
        len <= buf@.len(),
        cpos_ok(m, buf@, len as int),
        forall|i: int| 0 <= i < len ==> i32::MIN <= #[trigger] buf@[i].date <= i32::MAX,
    ensures
        view_rows(rows@) == cands_view(m, buf@, len as int),
{
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            cols_ok(*c, m, p), model_ok(m),
            len <= buf@.len(),
            cpos_ok(m, buf@, len as int),
            forall|k: int| 0 <= k < len ==> i32::MIN <= #[trigger] buf@[k].date <= i32::MAX,
            i <= len,
            view_rows(rows@) == cands_view(m, buf@, i as int),
        decreases len - i,
    {
        let cd = buf[i];
        let row = cand_out(c, cd, Ghost(m), Ghost(p));
        proof {
            crate::link::outcome::lemma_view_rows_push(rows@, row);
        }
        rows.push(row);
        proof {
            lemma_view_push(m, buf@, i as int);
        }
        i = i + 1;
    }
    rows
}

} // verus!
