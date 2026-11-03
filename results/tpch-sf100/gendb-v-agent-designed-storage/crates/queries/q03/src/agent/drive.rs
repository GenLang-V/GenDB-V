//! Running the kernels. The fast path (`run_fast`, cluster flag set): plan the window of orders that can be groups
//! (`plan`), split it into at most `workers` order ranges with their lineitem runs, run one `kernel::Chunk` per range
//! with `fork_join`, and merge the ranges' top-10 buffers in range order (`topk_insert` of every row, then
//! `common::topk::lemma_topk_absorb`). The general path (`run_general`): one chunk over all orders with lineitem
//! scans. Either gives `run_ok`: the top 10 of all groups (`qspec::gseq(0, o_n)`) inside the SUM capacity
//! condition, or a group whose revenue mass leaves `i128`. `emit` writes the result rows.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::link::expr::i128_max;
use crate::exec::value::{EVal, view_row};
use crate::link::query::view_rows;
use crate::gendb_entry::parallel::{Dispatch, WorkerTask, fork_join, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::gendb_entry::work::filled;
use super::common::isum::*;
use super::common::topk::*;
use super::model::*;
use super::qspec::*;
use super::kernel::*;
use super::plan::*;
use super::select::*;
use super::common::bitset::bits_eq_u8;
use std::sync::Arc;

verus! {

/// Most workers for which the calling thread builds the customer bit set.
pub const BM_MAX_WORKERS: usize = 8;

/// A run's result: the top-10 buffer, or (`ovf`) an order whose revenue mass leaves `i128`.
pub struct RunOut {
    pub buf: Vec<Cand>,
    pub len: usize,
    pub ovf: bool,
    pub ovf_q: usize,
}

pub open spec fn run_ok(m: M, p: QP, r: RunOut) -> bool {
    &&& r.buf@.len() == 10
    &&& r.len <= 10
    &&& r.ovf ==> 0 <= r.ovf_q < m.o_n && good(m, p, r.ovf_q as int) && labs(m, p, r.ovf_q as int) > i128_max()
    &&& !r.ovf ==> topk_ok(q3_keys(), q3_fams(), 10, cands_view(r.buf@, r.len as int), gseq(m, p, 0, m.o_n)) && caps_ok(m, p)
}

/// The general path: one chunk over every order, scanning the lineitems.
pub fn run_general(c: Cols, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: RunOut)
    requires cols_ok(c, m, p), model_ok(m),
    ensures run_ok(m, p, r),
{
    let zero = Cand { okey: 0, rev: 0, date: 0, sp: 0 };
    let task = Chunk {
        cols: c, o_lo: 0, o_hi: c.o_n, l_lo: 0, l_hi: 0, fast: false, buf: filled(10, zero), sel: Vec::new(),
        bm: Arc::new(Vec::new()), use_bm: false, m: Ghost(m), p: Ghost(p),
    };
    let ghost tv = task;
    let out = task.run();
    proof {
        assert(chunk_post(tv, out));
    }
    RunOut { buf: out.buf, len: out.len, ovf: out.ovf, ovf_q: out.ovf_q }
}

/// No order before the window start or after the cut is a group.
pub proof fn lemma_outside(m: M, p: QP, o0: int, l0: int, pe: int)
    requires
        model_ok(m), m.cluster == 1,
        lb_ok(m, o0, l0),
        shipped_by(m, p, l0),
        cut_ok(m, p, pe),
        0 <= o0 <= pe,
    ensures
        forall|q: int| 0 <= q < m.o_n && (q < o0 || q >= pe) ==> !#[trigger] good(m, p, q),
        gseq(m, p, 0, m.o_n) == gseq(m, p, o0, pe),
{
    assert forall|q: int| 0 <= q < m.o_n && (q < o0 || q >= pe) implies !#[trigger] good(m, p, q) by {
        if q < o0 {
            assert forall|j: int| 0 <= j < m.l_n implies #[trigger] lcnt_f(m, p, q)(j) == 0 by {
                if lkey(m, j) == okey(m, q) {
                    lemma_lpos_key(m, q, j);
                    assert(j < l0);
                }
            }
            lemma_isum_zero(m.l_n, lcnt_f(m, p, q));
        }
    }
    lemma_gseq_none(m, p, 0, o0);
    lemma_gseq_none(m, p, pe, m.o_n);
    lemma_gseq_split(m, p, 0, o0, m.o_n);
    lemma_gseq_split(m, p, o0, pe, m.o_n);
    assert(Seq::<Row>::empty() + gseq(m, p, o0, pe) + Seq::<Row>::empty() =~= gseq(m, p, o0, pe));
}

/// Rows of a range of groups, followed by rows of a later range's top 10, are distinct with their keys in families.
pub proof fn lemma_merge_wf(m: M, p: QP, lo: int, mid: int, hi: int, l: Seq<Row>, i: int)
    requires
        model_ok(m),
        0 <= lo <= mid <= hi <= m.o_n,
        topk_ok(q3_keys(), q3_fams(), 10, l, gseq(m, p, mid, hi)),
        0 <= i <= l.len(),
    ensures
        rel_wf(q3_keys(), q3_fams(), gseq(m, p, lo, mid) + l.subrange(0, i)),
{
    let a = gseq(m, p, lo, mid);
    let b = l.subrange(0, i);
    lemma_gseq_wf_range(m, p, lo, mid);
    lemma_gseq_contains(m, p, lo, mid);
    lemma_gseq_contains(m, p, mid, hi);
    assert(b.no_duplicates());
    assert forall|x: int, y: int| 0 <= x < a.len() && 0 <= y < b.len() implies a[x] != b[y] by {
        assert(a.contains(a[x]));
        assert(gseq(m, p, mid, hi).contains(l[y]));
        let q1 = choose|q: int| lo <= q < mid && good(m, p, q) && a[x] == grow(m, p, q);
        let q2 = choose|q: int| mid <= q < hi && good(m, p, q) && l[y] == grow(m, p, q);
        if a[x] == b[y] {
            assert(grow(m, p, q1)[0] == grow(m, p, q2)[0]);
            assert(okey(m, q1) == okey(m, q2));
        }
    }
    vstd::seq_lib::lemma_no_dup_in_concat(a, b);
    assert forall|t: int| 0 <= t < (a + b).len() implies crate::bridge::order::keys_ok(q3_keys(), q3_fams(), #[trigger] (a + b)[t]) by {
        if t < a.len() {
            assert((a + b)[t] == a[t]);
        } else {
            assert((a + b)[t] == l[t - a.len()]);
        }
    }
}

/// One more row of a range's top 10, merged.
proof fn lemma_view_push(buf: Seq<Cand>, i: int)
    requires 0 <= i < buf.len(),
    ensures cands_view(buf, i + 1) == cands_view(buf, i).push(cand_row(buf[i])),
{
    assert(cands_view(buf, i + 1) =~= cands_view(buf, i).push(cand_row(buf[i])));
}

/// The chunk boundaries of the window `[o0, pe)` (orders) and `[l0, lp)` (lineitems): `bo[k]`, `bl[k]`.
pub open spec fn bounds_ok(m: M, bo: Seq<usize>, bl: Seq<usize>, n: int, o0: int, l0: int, pe: int, lp: int) -> bool {
    &&& bo.len() == n && bl.len() == n
    &&& n >= 1 && bo[0] == o0 && bl[0] == l0
    &&& forall|k: int| 0 <= k < n ==> lb_ok(m, #[trigger] bo[k] as int, bl[k] as int) && bo[k] <= pe && bl[k] <= lp
    &&& forall|k: int| 0 <= k < n - 1 ==> #[trigger] bo[k] <= bo[k + 1] && bl[k] <= bl[k + 1]
}

/// Chunk boundaries: `workers` ranges of about equal lineitem rows, cut at order runs.
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

/// Merge the top 10 `obuf` of the groups of `[lo, hi)` into the top 10 `fin` of the groups of `[o0, lo)`.
fn merge_one(fin: &mut Vec<Cand>, flen: usize, obuf: &Vec<Cand>, olen: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>,
    Ghost(o0): Ghost<int>, Ghost(lo): Ghost<int>, Ghost(hi): Ghost<int>) -> (r: usize)
    requires
        model_ok(m),
        0 <= o0 <= lo <= hi <= m.o_n,
        old(fin)@.len() == 10,
        flen <= 10,
        topk_ok(q3_keys(), q3_fams(), 10, cands_view(old(fin)@, flen as int), gseq(m, p, o0, lo)),
        obuf@.len() == 10,
        olen <= 10,
        topk_ok(q3_keys(), q3_fams(), 10, cands_view(obuf@, olen as int), gseq(m, p, lo, hi)),
    ensures
        final(fin)@.len() == 10,
        r <= 10,
        topk_ok(q3_keys(), q3_fams(), 10, cands_view(final(fin)@, r as int), gseq(m, p, o0, hi)),
{
    let ghost a = gseq(m, p, o0, lo);
    let ghost lv = cands_view(obuf@, olen as int);
    let mut flen = flen;
    let mut i: usize = 0;
    proof {
        assert(a + cands_view(obuf@, 0) =~= a);
    }
    while i < olen
        invariant
            model_ok(m),
            0 <= o0 <= lo <= hi <= m.o_n,
            obuf@.len() == 10, olen <= 10,
            lv == cands_view(obuf@, olen as int),
            topk_ok(q3_keys(), q3_fams(), 10, lv, gseq(m, p, lo, hi)),
            a == gseq(m, p, o0, lo),
            i <= olen,
            fin@.len() == 10,
            flen <= 10,
            topk_ok(q3_keys(), q3_fams(), 10, cands_view(fin@, flen as int), a + cands_view(obuf@, i as int)),
        decreases olen - i,
    {
        let cand = obuf[i];
        let ghost all = a + cands_view(obuf@, i as int);
        proof {
            lemma_view_push(obuf@, i as int);
            assert(all.push(cand_row(cand)) =~= a + cands_view(obuf@, i + 1));
            assert(cands_view(obuf@, i + 1) =~= lv.subrange(0, i + 1));
            lemma_merge_wf(m, p, o0, lo, hi, lv, i + 1);
        }
        flen = topk_insert(fin, flen, cand, Ghost(all));
        i = i + 1;
    }
    proof {
        lemma_gseq_split(m, p, o0, lo, hi);
        lemma_gseq_wf_range(m, p, o0, hi);
        lemma_gseq_wf_range(m, p, lo, hi);
        lemma_topk_absorb(q3_keys(), q3_fams(), 10, cands_view(fin@, flen as int), a, lv, gseq(m, p, lo, hi));
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

/// Consecutive boundaries are ordered below the cut.
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
    let pe = orders_cut(&c, Ghost(m), Ghost(p));
    let lp = lb_search(&c, pe, Ghost(m), Ghost(p));
    let t0 = window_start(&c, lp, Ghost(m), Ghost(p));
    let mut o0 = pe;
    let mut l0 = lp;
    if t0 < lp {
        let k = lkey_at(&c, t0, Ghost(m), Ghost(p));
        match find_order(&c, k, Ghost(m), Ghost(p)) {
            Some(o) => {
                if o <= pe {
                    o0 = o;
                    l0 = run_start(&c, t0, Ghost(m), Ghost(p), Ghost(o as int));
                } else {
                    o0 = 0;
                    l0 = 0;
                }
            },
            None => {
                o0 = 0;
                l0 = 0;
            },
        }
    }
    proof {
        if o0 == 0 && l0 == 0 {
            assert forall|t: int| 0 <= t < m.l_n implies #[trigger] lpos(m, t) >= 0 by {
                crate::agent::facts::lemma_opos(m, lkey(m, t));
            }
        }
        // lb_ok of the cut and of the start bound the start below the cut
        if l0 > lp {
            assert(lpos(m, lp as int) < o0);
        }
        lemma_outside(m, p, o0 as int, l0 as int, pe as int);
    }
    let ntasks = workers;
    let (bo, bl) = plan_bounds(&c, ntasks, o0, l0, pe, lp, Ghost(m), Ghost(p));
    let zero = Cand { okey: 0, rev: 0, date: 0, sp: 0 };
    // the bit set of the segment's customers, shared by the tasks (worth its serial build only for few workers)
    let use_bm = c.seg_fast && workers <= BM_MAX_WORKERS && c.c_n <= 0xffff_0000;
    let bm: Arc<Vec<u64>> = Arc::new(if use_bm { bits_eq_u8(c.c_seg_c, c.c_n, c.segc) } else { Vec::new() });
    let mut tasks: Vec<Chunk> = Vec::new();
    let mut t: usize = 0;
    while t < ntasks
        invariant
            cols_ok(c, m, p), model_ok(m), m.cluster == 1,
            t <= ntasks <= MAX_WORKERS,
            bounds_ok(m, bo@, bl@, ntasks + 1, o0 as int, l0 as int, pe as int, lp as int),
            bo@[ntasks as int] == pe, bl@[ntasks as int] == lp,
            o0 <= pe <= m.o_n, lp <= m.l_n,
            use_bm ==> bm_ok(bm@, m, c),
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
        }
        let task = Chunk {
            cols: c, o_lo: bo[t], o_hi: bo[t + 1], l_lo: bl[t], l_hi: bl[t + 1], fast: true,
            buf: filled(10, zero), sel: filled(BATCH, 0usize), bm: bm.clone(), use_bm, m: Ghost(m), p: Ghost(p),
        };
        tasks.push(task);
        t = t + 1;
    }
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => {
            return Err(e);
        },
    };
    proof {
        reveal(outs_ok);
        assert(outs_ok(m, p, tv, outs@, bo@, ntasks as int));
    }
    // merge the ranges' top-10 buffers in range order
    let mut fin: Vec<Cand> = filled(10, zero);
    let mut flen: usize = 0;
    proof {
        lemma_topk_empty(q3_keys(), q3_fams(), 10);
        lemma_gseq_empty(m, p, o0 as int);
        assert(cands_view(fin@, 0) =~= Seq::<Row>::empty());
    }
    let mut t: usize = 0;
    while t < ntasks
        invariant
            model_ok(m),
            t <= ntasks <= MAX_WORKERS,
            bounds_ok(m, bo@, bl@, ntasks + 1, o0 as int, l0 as int, pe as int, lp as int),
            bo@[ntasks as int] == pe,
            o0 <= pe <= m.o_n,
            outs_ok(m, p, tv, outs@, bo@, ntasks as int),
            fin@.len() == 10,
            flen <= 10,
            topk_ok(q3_keys(), q3_fams(), 10, cands_view(fin@, flen as int), gseq(m, p, o0 as int, bo@[t as int] as int)),
            forall|q: int| o0 <= q < bo@[t as int] && #[trigger] good(m, p, q) ==> labs(m, p, q) <= i128_max(),
        decreases ntasks - t,
    {
        proof {
            lemma_outs_at(m, p, tv, outs@, bo@, ntasks as int, t as int);
            lemma_bounds_at(m, bo@, bl@, ntasks + 1, o0 as int, l0 as int, pe as int, lp as int, t as int);
        }
        if outs[t].ovf {
            let q = outs[t].ovf_q;
            return Ok(RunOut { buf: fin, len: flen, ovf: true, ovf_q: q });
        }
        let ghost lo = bo@[t as int] as int;
        let ghost hi = bo@[t + 1] as int;
        flen = merge_one(&mut fin, flen, &outs[t].buf, outs[t].len, Ghost(m), Ghost(p), Ghost(o0 as int), Ghost(lo), Ghost(hi));
        t = t + 1;
    }
    proof {
        assert(bo@[t as int] == pe);
        assert forall|q: int| 0 <= q < m.o_n && #[trigger] good(m, p, q) implies labs(m, p, q) <= i128_max() by {
            assert(o0 <= q < pe);
        }
    }
    Ok(RunOut { buf: fin, len: flen, ovf: false, ovf_q: 0 })
}

/// The result rows of a top-10 buffer whose dates are SQL dates.
pub fn emit(buf: &Vec<Cand>, len: usize) -> (rows: Vec<Vec<EVal>>)
    requires
        len <= buf@.len(),
        forall|i: int| 0 <= i < len ==> i32::MIN <= #[trigger] buf@[i].date <= i32::MAX,
    ensures
        view_rows(rows@) == cands_view(buf@, len as int),
{
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            len <= buf@.len(),
            forall|k: int| 0 <= k < len ==> i32::MIN <= #[trigger] buf@[k].date <= i32::MAX,
            i <= len,
            view_rows(rows@) == cands_view(buf@, i as int),
        decreases len - i,
    {
        let cnd = buf[i];
        let row = vec![EVal::Int(cnd.okey), EVal::Num { coeff: cnd.rev, scale: 4 }, EVal::Date(cnd.date as i32), EVal::Int(cnd.sp)];
        proof {
            assert(view_row(row@) =~= cand_row(cnd));
            crate::link::outcome::lemma_view_rows_push(rows@, row);
        }
        rows.push(row);
        proof {
            lemma_view_push(buf@, i as int);
        }
        i = i + 1;
    }
    rows
}

/// The dates of a top 10 of the groups are SQL dates (inside `i32`).
pub proof fn lemma_dates(m: M, p: QP, buf: Seq<Cand>, len: int)
    requires
        model_ok(m),
        0 <= len <= buf.len(),
        topk_ok(q3_keys(), q3_fams(), 10, cands_view(buf, len), gseq(m, p, 0, m.o_n)),
    ensures
        forall|i: int| 0 <= i < len ==> i32::MIN <= #[trigger] buf[i].date <= i32::MAX,
{
    lemma_gseq_contains(m, p, 0, m.o_n);
    assert forall|i: int| 0 <= i < len implies i32::MIN <= #[trigger] buf[i].date <= i32::MAX by {
        let v = cands_view(buf, len);
        assert(v[i] == cand_row(buf[i]));
        assert(gseq(m, p, 0, m.o_n).contains(v[i]));
        let q = choose|q: int| 0 <= q < m.o_n && good(m, p, q) && v[i] == grow(m, p, q);
        assert(v[i][2] == Val::Date(buf[i].date as int));
        assert(grow(m, p, q)[2] == Val::Date(odate(m, q)));
        assert(crate::spec::datetime::date_valid(odate(m, q)));
    }
}

} // verus!
