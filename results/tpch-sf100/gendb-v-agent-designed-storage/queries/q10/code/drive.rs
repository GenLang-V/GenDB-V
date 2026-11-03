//! The fast path (co-clustered layout, orders key index, customer rows addressable in `u32`, at most `MAX_NP`
//! customer partitions): plan the orders window and its lineitem rows (`plan`), split it into at most `workers`
//! order ranges with their lineitem runs and run one phase-1 task per range (`phase1::Chunk`, records per order,
//! partitioned by customer); when every task's mass fits and the total mass is at most `i64::MAX`, split the
//! customer partitions into at most `workers` ranges and run one phase-2 task per range (`phase2::Agg`, accumulate
//! per partition and keep the range's top 20); then merge the ranges' top 20 in range order. `None`: the fast path
//! does not apply (the general path runs).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::link::expr::i128_max;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::gendb_entry::work::filled;
use super::common::isum::*;
use super::common::topk::*;
use super::common::zeroed::*;
use super::model::*;
use super::qspec::*;
use super::kernel::*;
use super::recs::*;
use super::cand::*;
use super::plan::*;
use super::phase1::*;
use super::runs::CH_SLOTS;
use super::phase2::*;
use super::part::*;
use super::general::{RunOut, run_ok};

verus! {

/// Rows of a range of groups followed by rows of a later range's top K are distinct with their keys in families.
pub proof fn lemma_merge_wf(m: M, p: QP, lo: int, mid: int, hi: int, l: Seq<Row>, i: int)
    requires
        model_ok(m),
        0 <= lo <= mid <= hi <= m.c_n,
        topk_ok(q10_keys(), q10_fams(), K as nat, l, gseq(m, p, mid, hi)),
        0 <= i <= l.len(),
    ensures
        rel_wf(q10_keys(), q10_fams(), gseq(m, p, lo, mid) + l.subrange(0, i)),
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
        let c1 = choose|c: int| lo <= c < mid && good(m, p, c) && a[x] == grow(m, p, c);
        let c2 = choose|c: int| mid <= c < hi && good(m, p, c) && l[y] == grow(m, p, c);
        if a[x] == b[y] {
            assert(grow(m, p, c1)[0] == grow(m, p, c2)[0]);
            assert(ckey(m, c1) == ckey(m, c2));
        }
    }
    vstd::seq_lib::lemma_no_dup_in_concat(a, b);
    assert forall|t: int| 0 <= t < (a + b).len() implies crate::bridge::order::keys_ok(q10_keys(), q10_fams(), #[trigger] (a + b)[t]) by {
        if t < a.len() {
            assert((a + b)[t] == a[t]);
        } else {
            assert((a + b)[t] == l[t - a.len()]);
        }
    }
}

/// Merge the top K `obuf` of the groups of `[lo, hi)` into the top K `fin` of the groups of `[c0, lo)`.
fn merge_one(fin: &mut Vec<Cand>, flen: usize, obuf: &Vec<Cand>, olen: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>,
    Ghost(c0): Ghost<int>, Ghost(lo): Ghost<int>, Ghost(hi): Ghost<int>) -> (r: usize)
    requires
        model_ok(m),
        0 <= c0 <= lo <= hi <= m.c_n,
        old(fin)@.len() == K,
        flen <= K,
        topk_ok(q10_keys(), q10_fams(), K as nat, cands_view(m, old(fin)@, flen as int), gseq(m, p, c0, lo)),
        cands_good(m, p, old(fin)@, flen as int),
        obuf@.len() == K,
        olen <= K,
        topk_ok(q10_keys(), q10_fams(), K as nat, cands_view(m, obuf@, olen as int), gseq(m, p, lo, hi)),
        cands_good(m, p, obuf@, olen as int),
    ensures
        final(fin)@.len() == K,
        r <= K,
        topk_ok(q10_keys(), q10_fams(), K as nat, cands_view(m, final(fin)@, r as int), gseq(m, p, c0, hi)),
        cands_good(m, p, final(fin)@, r as int),
{
    let ghost a = gseq(m, p, c0, lo);
    let ghost lv = cands_view(m, obuf@, olen as int);
    let mut flen = flen;
    let mut i: usize = 0;
    proof {
        assert(a + cands_view(m, obuf@, 0) =~= a);
    }
    while i < olen
        invariant
            model_ok(m),
            0 <= c0 <= lo <= hi <= m.c_n,
            obuf@.len() == K, olen <= K,
            lv == cands_view(m, obuf@, olen as int),
            topk_ok(q10_keys(), q10_fams(), K as nat, lv, gseq(m, p, lo, hi)),
            cands_good(m, p, obuf@, olen as int),
            a == gseq(m, p, c0, lo),
            i <= olen,
            fin@.len() == K,
            flen <= K,
            topk_ok(q10_keys(), q10_fams(), K as nat, cands_view(m, fin@, flen as int), a + cands_view(m, obuf@, i as int)),
            cands_good(m, p, fin@, flen as int),
        decreases olen - i,
    {
        let cand = obuf[i];
        let ghost all = a + cands_view(m, obuf@, i as int);
        proof {
            lemma_view_push(m, obuf@, i as int);
            assert(all.push(cand_row(m, cand)) =~= a + cands_view(m, obuf@, i + 1));
            assert(cands_view(m, obuf@, i + 1) =~= lv.subrange(0, i + 1));
            lemma_merge_wf(m, p, c0, lo, hi, lv, i + 1);
        }
        let ghost f0 = fin@;
        let ghost l0 = flen;
        flen = topk_insert(fin, flen, cand, Ghost(m), Ghost(all));
        proof {
            lemma_cands_good_insert(m, p, f0, l0 as int, fin@, flen as int, cand);
        }
        i = i + 1;
    }
    proof {
        lemma_gseq_split(m, p, c0, lo, hi);
        lemma_gseq_wf_range(m, p, c0, hi);
        lemma_gseq_wf_range(m, p, lo, hi);
        lemma_topk_absorb(q10_keys(), q10_fams(), K as nat, cands_view(m, fin@, flen as int), a, lv, gseq(m, p, lo, hi));
    }
    flen
}

/// Phase-1 tasks: task `k` covers the orders `[bo[k], bo[k + 1])` of model `m`, window `p`.
#[verifier::opaque]
pub open spec fn tasks1_ok(m: M, p: QP, tv: Seq<Chunk>, bo: Seq<usize>, n: int) -> bool {
    &&& tv.len() == n
    &&& forall|k: int| 0 <= k < n ==> (#[trigger] tv[k]).o_lo == bo[k] && tv[k].o_hi == bo[k + 1] && tv[k].m@ == m && tv[k].p@ == p
}

/// Phase-2 tasks: task `w` covers the partitions `[pa[w], pa[w + 1])` of model `m`, window `p`.
#[verifier::opaque]
pub open spec fn tasks2_ok(m: M, p: QP, tv: Seq<Agg>, pa: Seq<usize>, n: int) -> bool {
    &&& tv.len() == n
    &&& forall|w: int| 0 <= w < n ==> (#[trigger] tv[w]).pa == pa[w] && tv[w].pb == pa[w + 1] && tv[w].m@ == m && tv[w].p@ == p
}

/// The partition range boundaries: nondecreasing from 0 to `np`.
pub open spec fn pa_ok(pa: Seq<usize>, n: int, np: int) -> bool {
    &&& pa.len() == n + 1
    &&& n >= 1
    &&& pa[0] == 0
    &&& pa[n] == np
    &&& forall|w: int| 0 <= w < n ==> #[trigger] pa[w] <= pa[w + 1]
}

/// The boundaries below `w` stay below the last.
proof fn lemma_pa_at(pa: Seq<usize>, n: int, np: int, w: int)
    requires pa_ok(pa, n, np), 0 <= w <= n,
    ensures pa[w] <= np,
    decreases n - w,
{
    if w < n {
        lemma_pa_at(pa, n, np, w + 1);
    }
}

/// Every customer's absolute revenue is bounded by the records' total mass.
proof fn lemma_caps(m: M, p: QP, outs: Seq<ChunkOut>, bo: Seq<usize>, nk: int, np: int)
    requires
        model_ok(m),
        outs_ok(m, p, outs, bo, nk, np),
        np * PW >= m.c_n,
        window_ok(m, p, bo[0] as int, bo[nk] as int),
        msum(outs, nk) <= i64::MAX,
    ensures caps_ok(m, p),
{
    assert forall|c: int| 0 <= c < m.c_n && #[trigger] good(m, p, c) implies cabs(m, p, c) <= i128_max() by {
        lemma_cabs_bound(m, p, outs, bo, nk, np, nk, c);
        let (a, b) = (bo[0] as int, bo[nk] as int);
        assert forall|q: int| 0 <= q < m.o_n && (q < a || q >= b) implies #[trigger] cabs_f(m, p, c)(q) == 0 by {
            assert(!odok(m, p, q));
        }
        lemma_dsum_whole(cabs_f(m, p, c), a, b, m.o_n);
    }
}

/// The phase-1 tasks: task `t` covers the orders `[bo[t], bo[t + 1])` and lineitems `[bl[t], bl[t + 1])`, with
/// `np` segments of twice its share of the orders plus 64 slots (a full segment sends the general path); `None` when
/// the buffers would not be addressable.
fn make_tasks1(c: Cols, ntasks: usize, np: usize, bo: &Vec<usize>, bl: &Vec<usize>, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>,
    Ghost(qs): Ghost<int>, Ghost(ls): Ghost<int>, Ghost(qe): Ghost<int>, Ghost(le): Ghost<int>) -> (r: Option<Vec<Chunk>>)
    requires
        cols_ok(c, m, p), model_ok(m), m.cluster == 1, m.c_n <= u32::MAX + 1, m.c_n <= MAX_CUST,
        1 <= np <= MAX_NP, np * PW >= m.c_n,
        1 <= ntasks <= MAX_WORKERS,
        bounds_ok(m, bo@, bl@, ntasks + 1, qs, ls, qe, le),
        qe <= m.o_n, le <= m.l_n,
    ensures
        r matches Some(tasks) ==> {
            &&& tasks.len() == ntasks
            &&& forall|k: int| 0 <= k < ntasks ==> (#[trigger] tasks@[k]).pre()
                && tasks@[k].o_lo == bo@[k] && tasks@[k].o_hi == bo@[k + 1] && tasks@[k].m@ == m && tasks@[k].p@ == p
                && tasks@[k].np == np
        },
{
    let mut tasks: Vec<Chunk> = Vec::new();
    let mut t: usize = 0;
    while t < ntasks
        invariant
            cols_ok(c, m, p), model_ok(m), m.cluster == 1, m.c_n <= u32::MAX + 1, m.c_n <= MAX_CUST,
            1 <= np <= MAX_NP, np * PW >= m.c_n,
            t <= ntasks <= MAX_WORKERS,
            bounds_ok(m, bo@, bl@, ntasks + 1, qs, ls, qe, le),
            qe <= m.o_n, le <= m.l_n,
            tasks.len() == t,
            forall|k: int| 0 <= k < t ==> (#[trigger] tasks@[k]).pre()
                && tasks@[k].o_lo == bo@[k] && tasks@[k].o_hi == bo@[k + 1] && tasks@[k].m@ == m && tasks@[k].p@ == p
                && tasks@[k].np == np,
        decreases ntasks - t,
    {
        proof {
            lemma_bounds_get(m, bo@, bl@, ntasks + 1, qs, ls, qe, le, t as int);
            lemma_bounds_get(m, bo@, bl@, ntasks + 1, qs, ls, qe, le, t + 1);
        }
        let orders = (bo[t + 1] - bo[t]) as u64;
        let share = orders / (np as u64);
        if share > 0xffff_ffffu64 {
            return None;
        }
        let cap64: u64 = share + share / 4 + 64;
        proof {
            assert(cap64 * np <= 0x2_0000_0040 * 4096) by (nonlinear_arith)
                requires cap64 <= 0x2_0000_0040, np <= 4096;
        }
        if cap64 > 0xffff_ffffu64 || cap64 * (np as u64) > usize::MAX as u64 {
            return None;
        }
        let cap = cap64 as usize;
        let slots = cap * np;
        proof {
            assert(slots == np * cap) by (nonlinear_arith) requires slots == cap * np;
        }
        let task = Chunk {
            cols: c, o_lo: bo[t], o_hi: bo[t + 1], l_lo: bl[t], l_hi: bl[t + 1], np, cap,
            rp: zeroed_u64(slots), cnt: filled(np, 0usize),
            gt: filled(CH_SLOTS, (0i64, 0i64, 0u64, 0u64)),
            m: Ghost(m), p: Ghost(p),
        };
        tasks.push(task);
        t = t + 1;
    }
    Some(tasks)
}

/// The phase-1 outputs, when no task is `big`, recorded the window `[qs, qe)` with a total mass inside `i64`.
fn check_outs(outs: &Vec<ChunkOut>, ntasks: usize, np: usize, Ghost(tv): Ghost<Seq<Chunk>>, bo: &Vec<usize>, bl: &Vec<usize>,
    Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(qs): Ghost<int>, Ghost(ls): Ghost<int>, Ghost(qe): Ghost<int>,
    Ghost(le): Ghost<int>) -> (ok: bool)
    requires
        model_ok(m),
        1 <= np, np * PW >= m.c_n,
        1 <= ntasks <= MAX_WORKERS,
        outs.len() == ntasks,
        tasks1_ok(m, p, tv, bo@, ntasks as int),
        forall|i: int| 0 <= i < ntasks ==> #[trigger] tv[i].post(outs@[i]),
        forall|i: int| 0 <= i < ntasks ==> (#[trigger] tv[i]).np == np,
        bounds_ok(m, bo@, bl@, ntasks + 1, qs, ls, qe, le),
        bo@[ntasks as int] == qe,
        window_ok(m, p, qs, qe),
    ensures
        ok ==> {
            &&& outs_ok(m, p, outs@, bo@, ntasks as int, np as int)
            &&& msum(outs@, ntasks as int) <= i64::MAX
            &&& window_ok(m, p, bo@[0] as int, bo@[ntasks as int] as int)
            &&& caps_ok(m, p)
        },
{
    let mut total: u64 = 0;
    let mut k: usize = 0;
    while k < ntasks
        invariant
            k <= ntasks <= MAX_WORKERS,
            outs.len() == ntasks,
            total as int == msum(outs@, k as int),
            total <= i64::MAX,
            forall|i: int| 0 <= i < k ==> !(#[trigger] outs@[i]).big,
        decreases ntasks - k,
    {
        if outs[k].big {
            return false;
        }
        let mk = outs[k].mass;
        if mk > 0x7fff_ffff_ffff_ffffu64 - total {
            return false;
        }
        total = total + mk;
        k = k + 1;
    }
    proof {
        reveal(tasks1_ok);
        lemma_bounds_get(m, bo@, bl@, ntasks + 1, qs, ls, qe, le, 0);
        let ov = outs@;
        let bv = bo@;
        assert forall|i: int| 0 <= i < ntasks implies #[trigger] out_at(m, p, ov, bv, np as int, i) by {
            assert(tv[i].post(ov[i]));
            assert(chunk_post(tv[i], ov[i]));
            assert(!outs@[i].big);
            assert(tv[i].np == np);
            lemma_bounds_get(m, bo@, bl@, ntasks + 1, qs, ls, qe, le, i);
        }
        assert(outs_ok(m, p, ov, bv, ntasks as int, np as int));
        lemma_caps(m, p, outs@, bo@, ntasks as int, np as int);
    }
    true
}

/// The partition ranges of `n2` phase-2 tasks: `pa[w] = w * np / n2`.
fn part_ranges(np: usize, n2: usize) -> (pa: Vec<usize>)
    requires 1 <= n2 <= np <= MAX_NP, n2 <= MAX_WORKERS,
    ensures pa_ok(pa@, n2 as int, np as int),
{
    let mut pa: Vec<usize> = Vec::new();
    let mut w: usize = 0;
    while w <= n2
        invariant
            1 <= n2 <= np <= MAX_NP, n2 <= MAX_WORKERS,
            w <= n2 + 1, pa.len() == w,
            forall|i: int| 0 <= i < w ==> #[trigger] pa@[i] as int == i * np / (n2 as int),
        decreases n2 + 1 - w,
    {
        proof {
            assert(w * np <= (MAX_WORKERS + 1) * MAX_NP) by (nonlinear_arith)
                requires w <= n2 + 1, np <= MAX_NP, n2 <= MAX_WORKERS;
        }
        pa.push(w * np / n2);
        w = w + 1;
    }
    proof {
        assert forall|i: int| 0 <= i < n2 implies #[trigger] pa@[i] <= pa@[i + 1] by {
            assert(i * np <= (i + 1) * np) by (nonlinear_arith) requires np >= 0, i >= 0;
            vstd::arithmetic::div_mod::lemma_div_is_ordered(i * np, (i + 1) * np, n2 as int);
        }
        assert(pa@[0] == 0 * np / (n2 as int));
        assert(pa@[n2 as int] == np) by {
            assert(n2 * np == np * n2) by (nonlinear_arith);
            vstd::arithmetic::div_mod::lemma_div_multiples_vanish(np as int, n2 as int);
        }
    }
    pa
}

/// The phase-2 tasks: task `w` covers the partitions `[pa[w], pa[w + 1])`.
fn make_tasks2(c: Cols, n2: usize, np: usize, pa: &Vec<usize>, shared: &Arc<Vec<ChunkOut>>, ntasks: usize,
    Ghost(bo): Ghost<Seq<usize>>, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (tasks2: Vec<Agg>)
    requires
        cols_ok(c, m, p), model_ok(m), m.c_n <= u32::MAX + 1,
        1 <= np <= MAX_NP, np * PW >= m.c_n,
        n2 <= MAX_WORKERS,
        pa_ok(pa@, n2 as int, np as int),
        shared@.len() == ntasks,
        ntasks >= 1,
        outs_ok(m, p, shared@, bo, ntasks as int, np as int),
        window_ok(m, p, bo[0] as int, bo[ntasks as int] as int),
        msum(shared@, ntasks as int) <= i64::MAX,
    ensures
        tasks2.len() == n2,
        forall|i: int| 0 <= i < n2 ==> (#[trigger] tasks2@[i]).pre()
            && tasks2@[i].pa == pa@[i] && tasks2@[i].pb == pa@[i + 1] && tasks2@[i].m@ == m && tasks2@[i].p@ == p,
{
    let mut tasks2: Vec<Agg> = Vec::new();
    let zero = Cand { cpos: 0, rev: 0 };
    let mut w: usize = 0;
    while w < n2
        invariant
            cols_ok(c, m, p), model_ok(m), m.c_n <= u32::MAX + 1,
            1 <= np <= MAX_NP, np * PW >= m.c_n,
            w <= n2 <= MAX_WORKERS,
            pa_ok(pa@, n2 as int, np as int),
            shared@.len() == ntasks,
            ntasks >= 1,
            outs_ok(m, p, shared@, bo, ntasks as int, np as int),
            window_ok(m, p, bo[0] as int, bo[ntasks as int] as int),
            msum(shared@, ntasks as int) <= i64::MAX,
            tasks2.len() == w,
            forall|i: int| 0 <= i < w ==> (#[trigger] tasks2@[i]).pre()
                && tasks2@[i].pa == pa@[i] && tasks2@[i].pb == pa@[i + 1] && tasks2@[i].m@ == m && tasks2@[i].p@ == p,
        decreases n2 - w,
    {
        proof {
            lemma_pa_at(pa@, n2 as int, np as int, w + 1);
        }
        let task = Agg {
            cols: c, pa: pa[w], pb: pa[w + 1], np, outs: shared.clone(), nk: ntasks,
            acc: zeroed_i64(PW), flg: zeroed_u8(PW), buf: filled(K, zero), bo: Ghost(bo), m: Ghost(m), p: Ghost(p),
        };
        tasks2.push(task);
        w = w + 1;
    }
    tasks2
}

/// Merge the tasks' top K in range order: the top K of every group.
fn merge_all(outs2: &Vec<AggOut>, n2: usize, np: usize, pa: &Vec<usize>, Ghost(tv2): Ghost<Seq<Agg>>, Ghost(m): Ghost<M>,
    Ghost(p): Ghost<QP>) -> (r: (Vec<Cand>, usize))
    requires
        model_ok(m),
        np * PW >= m.c_n,
        outs2.len() == n2,
        pa_ok(pa@, n2 as int, np as int),
        tasks2_ok(m, p, tv2, pa@, n2 as int),
        forall|i: int| 0 <= i < n2 ==> #[trigger] tv2[i].post(outs2@[i]),
    ensures
        r.0@.len() == K,
        r.1 <= K,
        topk_ok(q10_keys(), q10_fams(), K as nat, cands_view(m, r.0@, r.1 as int), gseq(m, p, 0, m.c_n)),
        cands_good(m, p, r.0@, r.1 as int),
{
    let zero = Cand { cpos: 0, rev: 0 };
    let mut fin: Vec<Cand> = filled(K, zero);
    let mut flen: usize = 0;
    proof {
        lemma_topk_empty(q10_keys(), q10_fams(), K as nat);
        lemma_gseq_empty(m, p, 0);
        assert(plo(m, 0) == 0);
        assert(cands_view(m, fin@, 0) =~= Seq::<Row>::empty());
    }
    let mut w: usize = 0;
    while w < n2
        invariant
            model_ok(m),
            np * PW >= m.c_n,
            w <= n2,
            outs2.len() == n2,
            pa_ok(pa@, n2 as int, np as int),
            tasks2_ok(m, p, tv2, pa@, n2 as int),
            forall|i: int| 0 <= i < n2 ==> #[trigger] tv2[i].post(outs2@[i]),
            fin@.len() == K,
            flen <= K,
            topk_ok(q10_keys(), q10_fams(), K as nat, cands_view(m, fin@, flen as int), gseq(m, p, 0, plo(m, pa@[w as int] as int))),
            cands_good(m, p, fin@, flen as int),
        decreases n2 - w,
    {
        let ghost lo = plo(m, pa@[w as int] as int);
        let ghost hi = plo(m, pa@[w + 1] as int);
        proof {
            reveal(tasks2_ok);
            lemma_plo_mono(m, pa@[w as int] as int, pa@[w + 1] as int);
            assert(tv2[w as int].post(outs2@[w as int]));
            assert(agg_post(tv2[w as int], outs2@[w as int]));
        }
        flen = merge_one(&mut fin, flen, &outs2[w].buf, outs2[w].len, Ghost(m), Ghost(p), Ghost(0), Ghost(lo), Ghost(hi));
        w = w + 1;
    }
    proof {
        assert(plo(m, np as int) == m.c_n);
    }
    (fin, flen)
}

/// Most tasks of one phase.
pub const TASK_CAP: usize = 32;

/// The fast path, with at most `workers` threads per phase; `None` when it does not apply.
pub fn run_fast(c: Cols, workers: usize, dispatch: &mut Dispatch, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>)
    -> (r: Result<Option<RunOut>, WorkerFailure>)
    requires
        cols_ok(c, m, p), model_ok(m), m.cluster == 1, c.idx_ok,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(Some(ro)) ==> run_ok(m, p, ro),
{
    if c.c_n as u64 > MAX_CUST || c.c_n > MAX_NP * PW {
        return Ok(None);
    }
    // customer partitions of PW rows
    let np: usize = if c.c_n == 0 { 1 } else { (c.c_n - 1) / PW + 1 };
    proof {
        if c.c_n > 0 {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(c.c_n - 1, PW as int);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(c.c_n - 1, PW as int);
            assert(np * PW >= c.c_n) by (nonlinear_arith)
                requires np == (c.c_n - 1) / (PW as int) + 1, PW * ((c.c_n - 1) / (PW as int)) + (c.c_n - 1) % (PW as int) == c.c_n - 1,
                    (c.c_n - 1) % (PW as int) < PW;
            assert(np <= MAX_NP) by (nonlinear_arith)
                requires np == (c.c_n - 1) / (PW as int) + 1, c.c_n <= MAX_NP * PW,
                    PW * ((c.c_n - 1) / (PW as int)) + (c.c_n - 1) % (PW as int) == c.c_n - 1,
                    (c.c_n - 1) % (PW as int) >= 0;
        }
    }
    // phase 1: records per order of the window, partitioned by customer
    let (qs, qe) = orders_window(&c, Ghost(m), Ghost(p));
    let ls = lb_search(&c, qs, Ghost(m), Ghost(p));
    let le = lb_search(&c, qe, Ghost(m), Ghost(p));
    proof {
        if ls > le {
            assert(lpos(m, le as int) >= qe);
            assert(lpos(m, le as int) < qs);
        }
    }
    // at most TASK_CAP tasks per phase: beyond one task per physical core, hyperthread siblings and page-fault
    // contention cost more than they add
    let ntasks = if workers < TASK_CAP { workers } else { TASK_CAP };
    let (bo, bl) = plan_bounds(&c, ntasks, qs, ls, qe, le, Ghost(m), Ghost(p));
    let tasks = match make_tasks1(c, ntasks, np, &bo, &bl, Ghost(m), Ghost(p), Ghost(qs as int), Ghost(ls as int),
        Ghost(qe as int), Ghost(le as int)) {
        Some(t) => t,
        None => {
            return Ok(None);
        },
    };
    let ghost tv = tasks@;
    proof {
        reveal(tasks1_ok);
        assert(tasks1_ok(m, p, tv, bo@, ntasks as int));
        lemma_bounds_get(m, bo@, bl@, ntasks + 1, qs as int, ls as int, qe as int, le as int, ntasks as int);
    }
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => {
            return Err(e);
        },
    };
    if !check_outs(&outs, ntasks, np, Ghost(tv), &bo, &bl, Ghost(m), Ghost(p), Ghost(qs as int), Ghost(ls as int),
        Ghost(qe as int), Ghost(le as int)) {
        return Ok(None);
    }
    // phase 2: accumulate per partition, top K per range of partitions
    let n2: usize = if ntasks < np { ntasks } else { np };
    let pa = part_ranges(np, n2);
    let shared = Arc::new(outs);
    let tasks2 = make_tasks2(c, n2, np, &pa, &shared, ntasks, Ghost(bo@), Ghost(m), Ghost(p));
    let ghost tv2 = tasks2@;
    proof {
        reveal(tasks2_ok);
        assert(tasks2_ok(m, p, tv2, pa@, n2 as int));
    }
    let outs2 = match fork_join(dispatch, tasks2) {
        Ok(o) => o,
        Err(e) => {
            return Err(e);
        },
    };
    let (fin, flen) = merge_all(&outs2, n2, np, &pa, Ghost(tv2), Ghost(m), Ghost(p));
    Ok(Some(RunOut { buf: fin, len: flen, ovf: false, ovf_c: 0 }))
}

} // verus!
