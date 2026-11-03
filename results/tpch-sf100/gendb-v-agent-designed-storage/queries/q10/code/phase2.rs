//! Phase 2 of the fast path: one task per range of customer partitions `[pa, pb)` (`part`). Per partition it adds
//! the records of that partition's segment of every phase-1 output (shared, read-only, `Arc`) into an accumulator
//! of `PW` slots (`acc[i]`: revenue of customer `plo(pp) + i`, `flg[i]`: 1 when some record names it), which stays
//! in the core's L2 cache. The phase-1 tasks' ranges are consecutive and cover the orders window, so after all
//! segments a customer's accumulator is its revenue `csum` and its flag says `ccnt > 0`; all partial sums stay
//! inside `i64` because the records' total mass is at most `i64::MAX`. Then it scans the partition's customers into
//! the task's top 20 of groups (flagged customers whose nation exists) by revenue DESC, resetting the accumulator
//! for the next partition.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::work::put;
use super::common::isum::*;
use super::common::topk::*;
use super::model::*;
use super::qspec::*;
use super::kernel::*;
use super::recs::*;
use super::cand::*;
use super::part::*;
use super::plan::window_ok;
use super::phase1::ChunkOut;

verus! {

/// Total mass of the first `k` phase-1 outputs.
pub open spec fn msum(outs: Seq<ChunkOut>, k: int) -> int
    decreases k,
{
    if k <= 0 { 0 } else { msum(outs, k - 1) + outs[k - 1].mass as int }
}

/// Customer rows of partition `pp` in output `k`, their revenues and their number.
pub open spec fn krc(outs: Seq<ChunkOut>, k: int, pp: int) -> Seq<u32> { seg(rcv(outs[k].rp@), pp, outs[k].cap as int) }
pub open spec fn krr(outs: Seq<ChunkOut>, k: int, pp: int) -> Seq<i64> { seg(rrv(outs[k].rp@), pp, outs[k].cap as int) }
pub open spec fn kn(outs: Seq<ChunkOut>, k: int, pp: int) -> int { outs[k].cnt@[pp] as int }

/// Task `k` recorded the orders `[bo[k], bo[k + 1])` in `np` partitions with a mass inside `i64`.
pub open spec fn out_at(m: M, p: QP, outs: Seq<ChunkOut>, bo: Seq<usize>, np: int, k: int) -> bool {
    &&& bo[k] <= bo[k + 1]
    &&& !outs[k].big
    &&& outs[k].mass <= i64::MAX
    &&& parts_ok(m, p, rcv(outs[k].rp@), rrv(outs[k].rp@), outs[k].cnt@, outs[k].cap as int, np, bo[k] as int, bo[k + 1] as int,
        outs[k].mass as int)
}

/// The phase-1 outputs: task `k` recorded the orders `[bo[k], bo[k + 1])`.
pub open spec fn outs_ok(m: M, p: QP, outs: Seq<ChunkOut>, bo: Seq<usize>, nk: int, np: int) -> bool {
    &&& outs.len() == nk
    &&& bo.len() == nk + 1
    &&& forall|k: int| 0 <= k < nk ==> #[trigger] out_at(m, p, outs, bo, np, k)
}

/// A phase-2 task over the partitions `[pa, pb)`.
pub struct Agg {
    pub cols: Cols,
    pub pa: usize,
    pub pb: usize,
    pub np: usize,
    pub outs: Arc<Vec<ChunkOut>>,
    pub nk: usize,
    pub acc: Vec<i64>,
    pub flg: Vec<u8>,
    pub buf: Vec<Cand>,
    pub bo: Ghost<Seq<usize>>,
    pub m: Ghost<M>,
    pub p: Ghost<QP>,
}

/// A task's top-20 buffer.
pub struct AggOut {
    pub buf: Vec<Cand>,
    pub len: usize,
}

pub open spec fn agg_pre(t: Agg) -> bool {
    let m = t.m@;
    let p = t.p@;
    let outs = t.outs@;
    &&& cols_ok(t.cols, m, p)
    &&& model_ok(m)
    &&& t.pa <= t.pb <= t.np
    &&& 1 <= t.np <= MAX_NP
    &&& t.np * PW >= m.c_n
    &&& m.c_n <= u32::MAX + 1
    &&& t.acc@.len() >= PW
    &&& forall|i: int| 0 <= i < t.acc@.len() ==> #[trigger] t.acc@[i] == 0
    &&& t.flg@.len() >= PW
    &&& forall|i: int| 0 <= i < t.flg@.len() ==> #[trigger] t.flg@[i] == 0
    &&& t.buf@.len() == K
    &&& t.nk >= 1
    &&& outs.len() == t.nk
    &&& outs_ok(m, p, outs, t.bo@, t.nk as int, t.np as int)
    &&& window_ok(m, p, t.bo@[0] as int, t.bo@[t.nk as int] as int)
    &&& msum(outs, t.nk as int) <= i64::MAX
}

pub open spec fn agg_post(t: Agg, out: AggOut) -> bool {
    let m = t.m@;
    let p = t.p@;
    &&& out.buf@.len() == K
    &&& out.len <= K
    &&& topk_ok(q10_keys(), q10_fams(), K as nat, cands_view(m, out.buf@, out.len as int),
        gseq(m, p, plo(m, t.pa as int), plo(m, t.pb as int)))
    &&& cands_good(m, p, out.buf@, out.len as int)
}

// ------------------------------------------------------------------------------------------------ lemmas

/// Masses are nonnegative and their prefix sums nondecreasing.
pub proof fn lemma_msum_mono(outs: Seq<ChunkOut>, a: int, b: int)
    requires 0 <= a <= b,
    ensures 0 <= msum(outs, a) <= msum(outs, b),
    decreases b,
{
    if b > 0 {
        if a < b {
            lemma_msum_mono(outs, a, b - 1);
        } else {
            lemma_msum_mono(outs, a - 1, b - 1);
        }
    }
}

/// The accumulator of customer `c` after the records `[0, i)` of partition `pp` of task `k` (and every record of
/// the earlier tasks).
pub open spec fn acc_at(m: M, p: QP, outs: Seq<ChunkOut>, bo: Seq<usize>, k: int, pp: int, i: int, c: int) -> int {
    dsum(csum_f(m, p, c), bo[0] as int, bo[k] as int) + rsum(krc(outs, k, pp), krr(outs, k, pp), i, c)
}

/// The record count of customer `c` after the records `[0, i)` of partition `pp` of task `k`.
pub open spec fn cnt_at(m: M, p: QP, outs: Seq<ChunkOut>, bo: Seq<usize>, k: int, pp: int, i: int, c: int) -> int {
    dsum(chit_f(m, p, c), bo[0] as int, bo[k] as int) + rcnt(krc(outs, k, pp), i, c)
}

/// Customer `c`'s accumulator and flag after the records `[0, i)` of partition `pp` of task `k`.
pub open spec fn acc_ok_at(m: M, p: QP, outs: Seq<ChunkOut>, bo: Seq<usize>, k: int, pp: int, i: int, clo: int,
    acc: Seq<i64>, flg: Seq<u8>, c: int) -> bool {
    &&& acc[c - clo] as int == acc_at(m, p, outs, bo, k, pp, i, c)
    &&& flg[c - clo] as int == if cnt_at(m, p, outs, bo, k, pp, i, c) > 0 { 1int } else { 0int }
    &&& abs(acc_at(m, p, outs, bo, k, pp, i, c)) <= msum(outs, k) + rabs(krr(outs, k, pp), i)
    &&& cnt_at(m, p, outs, bo, k, pp, i, c) >= 0
}

/// The aggregation invariant over the customers `[clo, chi)` of partition `pp`.
pub open spec fn acc_inv(m: M, p: QP, outs: Seq<ChunkOut>, bo: Seq<usize>, k: int, pp: int, i: int, clo: int, chi: int,
    acc: Seq<i64>, flg: Seq<u8>) -> bool {
    forall|c: int| clo <= c < chi ==> #[trigger] acc_ok_at(m, p, outs, bo, k, pp, i, clo, acc, flg, c)
}

/// Customer `c`'s accumulator and flag at the start of task `k`.
pub open spec fn start_at(m: M, p: QP, outs: Seq<ChunkOut>, bo: Seq<usize>, k: int, clo: int,
    acc: Seq<i64>, flg: Seq<u8>, c: int) -> bool {
    &&& acc[c - clo] as int == dsum(csum_f(m, p, c), bo[0] as int, bo[k] as int)
    &&& flg[c - clo] as int == if dsum(chit_f(m, p, c), bo[0] as int, bo[k] as int) > 0 { 1int } else { 0int }
    &&& abs(dsum(csum_f(m, p, c), bo[0] as int, bo[k] as int)) <= msum(outs, k)
    &&& dsum(chit_f(m, p, c), bo[0] as int, bo[k] as int) >= 0
}

/// The accumulators of customers `[clo, chi)` at the start of task `k`: every record of the earlier tasks added.
pub open spec fn start_inv(m: M, p: QP, outs: Seq<ChunkOut>, bo: Seq<usize>, k: int, clo: int, chi: int,
    acc: Seq<i64>, flg: Seq<u8>) -> bool {
    forall|c: int| clo <= c < chi ==> #[trigger] start_at(m, p, outs, bo, k, clo, acc, flg, c)
}

/// The start of task `k` is the state after its first 0 records.
proof fn lemma_task_start(m: M, p: QP, outs: Seq<ChunkOut>, bo: Seq<usize>, k: int, pp: int, clo: int, chi: int,
    acc: Seq<i64>, flg: Seq<u8>)
    requires start_inv(m, p, outs, bo, k, clo, chi, acc, flg),
    ensures acc_inv(m, p, outs, bo, k, pp, 0, clo, chi, acc, flg),
{
    assert forall|c: int| clo <= c < chi implies #[trigger] acc_ok_at(m, p, outs, bo, k, pp, 0, clo, acc, flg, c) by {
        assert(start_at(m, p, outs, bo, k, clo, acc, flg, c));
    }
}

/// Partition `pp` of task `k`: its records name customers of `[plo(pp), plo(pp + 1))` and sum to their revenue.
proof fn lemma_out_part(m: M, p: QP, outs: Seq<ChunkOut>, bo: Seq<usize>, nk: int, np: int, k: int, pp: int)
    requires outs_ok(m, p, outs, bo, nk, np), 0 <= k < nk, 0 <= pp < np,
    ensures
        precs_ok(m, p, krc(outs, k, pp), krr(outs, k, pp), kn(outs, k, pp), bo[k] as int, bo[k + 1] as int,
            outs[k].mass as int, plo(m, pp), plo(m, pp + 1)),
        bo[k] <= bo[k + 1],
        outs[k].mass <= i64::MAX,
        outs[k].cap >= 0,
        pp * outs[k].cap + outs[k].cap <= outs[k].rp@.len(),
        pp < outs[k].cnt@.len(),
        0 <= pp * outs[k].cap,
{
    assert(out_at(m, p, outs, bo, np, k));
    let o = outs[k];
    assert(part_ok(m, p, rcv(o.rp@), rrv(o.rp@), o.cnt@, o.cap as int, pp, bo[k] as int, bo[k + 1] as int, o.mass as int));
    lemma_seg_slots(pp, pp, o.cap as int, np);
}

/// After every record of partition `pp` of task `k`, the state is the start of task `k + 1`.
proof fn lemma_task_end(m: M, p: QP, outs: Seq<ChunkOut>, bo: Seq<usize>, nk: int, np: int, k: int, pp: int,
    acc: Seq<i64>, flg: Seq<u8>)
    requires
        model_ok(m),
        outs_ok(m, p, outs, bo, nk, np),
        0 <= k < nk,
        0 <= pp < np,
        acc_inv(m, p, outs, bo, k, pp, kn(outs, k, pp), plo(m, pp), plo(m, pp + 1), acc, flg),
    ensures start_inv(m, p, outs, bo, k + 1, plo(m, pp), plo(m, pp + 1), acc, flg),
{
    let o = outs[k];
    let (clo, chi) = (plo(m, pp), plo(m, pp + 1));
    lemma_out_part(m, p, outs, bo, nk, np, k, pp);
    assert(msum(outs, k + 1) == msum(outs, k) + o.mass as int);
    assert forall|c: int| clo <= c < chi implies #[trigger] start_at(m, p, outs, bo, k + 1, clo, acc, flg, c) by {
        assert(acc_ok_at(m, p, outs, bo, k, pp, kn(outs, k, pp), clo, acc, flg, c));
        assert(rsum(krc(outs, k, pp), krr(outs, k, pp), kn(outs, k, pp), c) == dsum(csum_f(m, p, c), bo[k] as int, bo[k + 1] as int));
        lemma_dsum_join(csum_f(m, p, c), bo[0] as int, bo[k] as int, bo[k + 1] as int);
        lemma_dsum_join(chit_f(m, p, c), bo[0] as int, bo[k] as int, bo[k + 1] as int);
    }
}

/// One record of partition `pp` of task `k`: the accumulator of its customer grows by its revenue, and every partial
/// sum stays bounded by the masses so far.
proof fn lemma_record_step(m: M, p: QP, outs: Seq<ChunkOut>, bo: Seq<usize>, k: int, pp: int, i: int, clo: int, chi: int,
    acc: Seq<i64>, flg: Seq<u8>, acc2: Seq<i64>, flg2: Seq<u8>)
    requires
        0 <= i,
        0 <= clo <= chi,
        acc.len() >= chi - clo, flg.len() >= chi - clo,
        acc_inv(m, p, outs, bo, k, pp, i, clo, chi, acc, flg),
        ({
            let cp = krc(outs, k, pp)[i] as int;
            let rv = krr(outs, k, pp)[i];
            &&& clo <= cp < chi
            &&& acc2 == acc.update(cp - clo, (acc[cp - clo] + rv) as i64)
            &&& acc[cp - clo] + rv == (acc[cp - clo] + rv) as i64
            &&& flg2 == flg.update(cp - clo, 1u8)
        }),
    ensures acc_inv(m, p, outs, bo, k, pp, i + 1, clo, chi, acc2, flg2),
{
    let (rc, rr) = (krc(outs, k, pp), krr(outs, k, pp));
    assert forall|c: int| clo <= c < chi implies #[trigger] acc_ok_at(m, p, outs, bo, k, pp, i + 1, clo, acc2, flg2, c) by {
        lemma_rec_step(rc, rr, i, c);
        assert(acc_ok_at(m, p, outs, bo, k, pp, i, clo, acc, flg, c));
    }
}

/// While adding a record, the new partial sum stays inside `i64`.
proof fn lemma_record_fits(m: M, p: QP, outs: Seq<ChunkOut>, bo: Seq<usize>, nk: int, np: int, k: int, pp: int, i: int,
    acc: Seq<i64>, flg: Seq<u8>)
    requires
        model_ok(m),
        outs_ok(m, p, outs, bo, nk, np),
        msum(outs, nk) <= i64::MAX,
        0 <= k < nk,
        0 <= pp < np,
        0 <= i < kn(outs, k, pp),
        acc_inv(m, p, outs, bo, k, pp, i, plo(m, pp), plo(m, pp + 1), acc, flg),
    ensures ({
        let cp = krc(outs, k, pp)[i] as int;
        &&& plo(m, pp) <= cp < plo(m, pp + 1)
        &&& i64::MIN <= acc[cp - plo(m, pp)] + krr(outs, k, pp)[i] <= i64::MAX
    }),
{
    let (rc, rr) = (krc(outs, k, pp), krr(outs, k, pp));
    let o = outs[k];
    let cp = rc[i] as int;
    lemma_out_part(m, p, outs, bo, nk, np, k, pp);
    assert(acc_ok_at(m, p, outs, bo, k, pp, i, plo(m, pp), acc, flg, cp));
    lemma_rec_step(rc, rr, i, cp);
    lemma_rabs_mono(rr, i + 1, kn(outs, k, pp));
    lemma_msum_mono(outs, k + 1, nk);
    assert(msum(outs, k + 1) == msum(outs, k) + o.mass as int);
}

/// After every task: the accumulator is the customer's revenue, its flag says whether it has a counted order.
proof fn lemma_acc_final(m: M, p: QP, a: int, b: int, c: int)
    requires
        model_ok(m),
        window_ok(m, p, a, b),
    ensures
        dsum(csum_f(m, p, c), a, b) == csum(m, p, c),
        (dsum(chit_f(m, p, c), a, b) > 0) == (ccnt(m, p, c) > 0),
{
    assert forall|q: int| 0 <= q < m.o_n && (q < a || q >= b) implies #[trigger] csum_f(m, p, c)(q) == 0 by {
        assert(!odok(m, p, q));
    }
    assert forall|q: int| 0 <= q < m.o_n && (q < a || q >= b) implies #[trigger] chit_f(m, p, c)(q) == 0 by {
        assert(!odok(m, p, q));
    }
    lemma_dsum_whole(csum_f(m, p, c), a, b, m.o_n);
    lemma_dsum_whole(chit_f(m, p, c), a, b, m.o_n);
    lemma_ccnt_pos(m, p, c);
}

/// Every customer's absolute revenue over the recorded orders is bounded by the masses.
pub proof fn lemma_cabs_bound(m: M, p: QP, outs: Seq<ChunkOut>, bo: Seq<usize>, nk: int, np: int, k: int, c: int)
    requires
        model_ok(m),
        outs_ok(m, p, outs, bo, nk, np),
        np * PW >= m.c_n,
        0 <= k <= nk,
        0 <= c < m.c_n,
    ensures dsum(cabs_f(m, p, c), bo[0] as int, bo[k] as int) <= msum(outs, k),
    decreases k,
{
    if k > 0 {
        lemma_cabs_bound(m, p, outs, bo, nk, np, k - 1, c);
        let o = outs[k - 1];
        let pp = c / (PW as int);
        lemma_part_of(m, c, np);
        lemma_out_part(m, p, outs, bo, nk, np, k - 1, pp);
        assert(rsum(krc(outs, k - 1, pp), krr(outs, k - 1, pp), kn(outs, k - 1, pp), c)
            == dsum(csum_f(m, p, c), bo[k - 1] as int, bo[k] as int));
        assert(msum(outs, k) == msum(outs, k - 1) + o.mass as int);
        lemma_dsum_join(cabs_f(m, p, c), bo[0] as int, bo[k - 1] as int, bo[k] as int);
    }
}

/// The group rows of a range of customers are distinct and their ORDER BY keys are in their families.
pub proof fn lemma_gseq_wf_range(m: M, p: QP, lo: int, hi: int)
    requires model_ok(m), 0 <= lo, hi <= m.c_n,
    ensures rel_wf(q10_keys(), q10_fams(), gseq(m, p, lo, hi)),
{
    lemma_gseq_nodup(m, p, lo, hi);
    lemma_gseq_contains(m, p, lo, hi);
    let s = gseq(m, p, lo, hi);
    assert forall|i: int| 0 <= i < s.len() implies crate::bridge::order::keys_ok(q10_keys(), q10_fams(), #[trigger] s[i]) by {
        assert(s.contains(s[i]));
        let c = choose|c: int| lo <= c < hi && good(m, p, c) && s[i] == grow(m, p, c);
        lemma_cand_cmp(m, Cand { cpos: 0, rev: 0 }, Cand { cpos: 0, rev: 0 });
        assert(s[i] == crow_rev(m, c, csum(m, p, c)));
        assert forall|t: int| 0 <= t < q10_keys().len() implies #[trigger] crate::bridge::order::key_ok(q10_keys()[t], q10_fams()[t], s[i]) by {}
    }
}

/// Slot `o` of the accumulators is clear.
pub open spec fn clear_at(acc: Seq<i64>, flg: Seq<u8>, o: int) -> bool {
    acc[o] == 0 && flg[o] == 0
}

/// The top-K scan over the accumulated customers `[clo, chi)` (slot `x - clo` holds customer `x`'s revenue and
/// flag), continuing the top K of the groups of `[tlo, clo)`; every slot `[0, PW)` is cleared on the way.
pub fn scan_part(c: &Cols, tlo: usize, clo: usize, chi: usize, acc: &mut Vec<i64>, flg: &mut Vec<u8>, buf: &mut Vec<Cand>,
    len0: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (len: usize)
    requires
        cols_ok(*c, m, p), model_ok(m),
        tlo <= clo <= chi <= m.c_n,
        chi - clo <= PW,
        old(acc)@.len() >= PW,
        old(flg)@.len() >= PW,
        forall|x: int| clo <= x < chi ==> {
            &&& #[trigger] old(acc)@[x - clo] as int == csum(m, p, x)
            &&& (old(flg)@[x - clo] != 0) == (ccnt(m, p, x) > 0)
        },
        old(buf)@.len() == K,
        len0 <= K,
        topk_ok(q10_keys(), q10_fams(), K as nat, cands_view(m, old(buf)@, len0 as int), gseq(m, p, tlo as int, clo as int)),
        cands_good(m, p, old(buf)@, len0 as int),
    ensures
        final(acc)@.len() == old(acc)@.len(),
        final(flg)@.len() == old(flg)@.len(),
        forall|o: int| 0 <= o < PW ==> #[trigger] clear_at(final(acc)@, final(flg)@, o),
        final(buf)@.len() == K,
        len <= K,
        topk_ok(q10_keys(), q10_fams(), K as nat, cands_view(m, final(buf)@, len as int), gseq(m, p, tlo as int, chi as int)),
        cands_good(m, p, final(buf)@, len as int),
    no_unwind
{
    let mut len = len0;
    let mut cc = clo;
    while cc < chi
        invariant
            cols_ok(*c, m, p), model_ok(m),
            tlo <= clo <= cc <= chi <= m.c_n,
            chi - clo <= PW,
            acc@.len() == old(acc)@.len(), flg@.len() == old(flg)@.len(),
            old(acc)@.len() >= PW, old(flg)@.len() >= PW,
            forall|o: int| cc - clo <= o < chi - clo ==> #[trigger] acc@[o] == old(acc)@[o] && flg@[o] == old(flg)@[o],
            forall|x: int| clo <= x < chi ==> {
                &&& #[trigger] old(acc)@[x - clo] as int == csum(m, p, x)
                &&& (old(flg)@[x - clo] != 0) == (ccnt(m, p, x) > 0)
            },
            forall|o: int| 0 <= o < cc - clo ==> #[trigger] clear_at(acc@, flg@, o),
            buf@.len() == K,
            len <= K,
            topk_ok(q10_keys(), q10_fams(), K as nat, cands_view(m, buf@, len as int), gseq(m, p, tlo as int, cc as int)),
            cands_good(m, p, buf@, len as int),
        decreases chi - cc,
    {
        let o = cc - clo;
        let ghost before = gseq(m, p, tlo as int, cc as int);
        proof {
            lemma_gseq_step(m, p, tlo as int, cc as int);
            lemma_gseq_wf_range(m, p, tlo as int, cc as int + 1);
            assert(old(acc)@[cc - clo] as int == csum(m, p, cc as int));
            assert(acc@[o as int] == old(acc)@[o as int] && flg@[o as int] == old(flg)@[o as int]);
        }
        if flg[o] != 0 {
            let rev = acc[o] as i128;
            let cand = Cand { cpos: cc, rev };
            proof {
                assert(cand_row(m, cand) =~= grow(m, p, cc as int));
            }
            if cannot_enter(buf, len, rev) {
                proof {
                    if good(m, p, cc as int) {
                        lemma_skip_full(m, buf@, len as int, before, cand);
                    }
                }
            } else {
                match nat_ok_at(c, cc, Ghost(m), Ghost(p)) {
                    Some(_) => {
                        let ghost b0 = buf@;
                        let ghost l0 = len;
                        len = topk_insert(buf, len, cand, Ghost(m), Ghost(before));
                        proof {
                            lemma_cands_good_insert(m, p, b0, l0 as int, buf@, len as int, cand);
                        }
                    },
                    None => {},
                }
            }
        }
        let ghost (a1, f1) = (acc@, flg@);
        put(acc, o, 0);
        put(flg, o, 0);
        proof {
            assert forall|t: int| 0 <= t < cc + 1 - clo implies #[trigger] clear_at(acc@, flg@, t) by {
                if t < o {
                    assert(clear_at(a1, f1, t));
                }
            }
            assert forall|t: int| cc + 1 - clo <= t < chi - clo implies #[trigger] acc@[t] == old(acc)@[t] && flg@[t] == old(flg)@[t] by {
                assert(a1[t] == old(acc)@[t] && f1[t] == old(flg)@[t]);
            }
        }
        cc = cc + 1;
    }
    let mut o = chi - clo;
    while o < PW
        invariant
            chi - clo <= o <= PW,
            acc@.len() == old(acc)@.len(), flg@.len() == old(flg)@.len(),
            old(acc)@.len() >= PW, old(flg)@.len() >= PW,
            forall|t: int| 0 <= t < o ==> #[trigger] clear_at(acc@, flg@, t),
        decreases PW - o,
    {
        let ghost (a1, f1) = (acc@, flg@);
        put(acc, o, 0);
        put(flg, o, 0);
        proof {
            assert forall|t: int| 0 <= t < o + 1 implies #[trigger] clear_at(acc@, flg@, t) by {
                if t < o {
                    assert(clear_at(a1, f1, t));
                }
            }
        }
        o = o + 1;
    }
    len
}

impl WorkerTask for Agg {
    type Output = AggOut;

    open spec fn pre(&self) -> bool {
        agg_pre(*self)
    }

    open spec fn post(&self, out: AggOut) -> bool {
        agg_post(*self, out)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.pa as u64, self.pb as u64)
    }

    fn run(self) -> (out: AggOut) {
        let Agg { cols, pa, pb, np, outs, nk, acc, flg, buf, bo: gbo, m: gm, p: gp } = self;
        let ghost m = gm@;
        let ghost p = gp@;
        let ghost bo = gbo@;
        let c = cols;
        let mut acc = acc;
        let mut flg = flg;
        let mut buf = buf;
        let mut len: usize = 0;
        let mut pp = pa;
        proof {
            lemma_topk_empty(q10_keys(), q10_fams(), K as nat);
            lemma_gseq_empty(m, p, plo(m, pa as int));
            assert(cands_view(m, buf@, 0) =~= Seq::<Row>::empty());
            assert forall|o: int| 0 <= o < PW implies #[trigger] clear_at(acc@, flg@, o) by {}
        }
        while pp < pb
            invariant
                cols_ok(c, m, p), model_ok(m),
                pa <= pp <= pb <= np, 1 <= np <= MAX_NP, np * PW >= m.c_n,
                m.c_n <= u32::MAX + 1,
                acc@.len() >= PW,
                flg@.len() >= PW,
                forall|o: int| 0 <= o < PW ==> #[trigger] clear_at(acc@, flg@, o),
                outs@.len() == nk,
                nk >= 1,
                outs_ok(m, p, outs@, bo, nk as int, np as int),
                window_ok(m, p, bo[0] as int, bo[nk as int] as int),
                msum(outs@, nk as int) <= i64::MAX,
                buf@.len() == K,
                len <= K,
                topk_ok(q10_keys(), q10_fams(), K as nat, cands_view(m, buf@, len as int),
                    gseq(m, p, plo(m, pa as int), plo(m, pp as int))),
                cands_good(m, p, buf@, len as int),
            decreases pb - pp,
        {
            let clo: usize = if pp * PW < c.c_n { pp * PW } else { c.c_n };
            let chi: usize = if (pp + 1) * PW < c.c_n { (pp + 1) * PW } else { c.c_n };
            proof {
                assert(clo == plo(m, pp as int) && chi == plo(m, pp + 1));
                lemma_plo_mono(m, pa as int, pp as int);
                lemma_plo_mono(m, pp as int, pp + 1);
                assert(chi - clo <= PW);
                assert forall|x: int| clo <= x < chi implies #[trigger] start_at(m, p, outs@, bo, 0, clo as int, acc@, flg@, x) by {
                    assert(clear_at(acc@, flg@, x - clo));
                }
            }
            let mut k: usize = 0;
            while k < nk
                invariant
                    cols_ok(c, m, p), model_ok(m),
                    pp < np, 1 <= np <= MAX_NP, np * PW >= m.c_n,
                    clo == plo(m, pp as int), chi == plo(m, pp + 1), clo <= chi <= m.c_n, chi - clo <= PW,
                    acc@.len() >= PW,
                    flg@.len() >= PW,
                    outs@.len() == nk,
                    outs_ok(m, p, outs@, bo, nk as int, np as int),
                    msum(outs@, nk as int) <= i64::MAX,
                    k <= nk,
                    start_inv(m, p, outs@, bo, k as int, clo as int, chi as int, acc@, flg@),
                decreases nk - k,
            {
                proof {
                    lemma_out_part(m, p, outs@, bo, nk as int, np as int, k as int, pp as int);
                    lemma_task_start(m, p, outs@, bo, k as int, pp as int, clo as int, chi as int, acc@, flg@);
                }
                let rp: &Vec<u64> = &outs[k].rp;
                let cap = outs[k].cap;
                let n = outs[k].cnt[pp];
                let rlen = rp.len();
                proof {
                    assert(pp * cap + cap <= rlen);
                }
                let base = pp * cap;
                let mut i: usize = 0;
                while i < n
                    invariant
                        cols_ok(c, m, p), model_ok(m),
                        pp < np, 1 <= np <= MAX_NP, np * PW >= m.c_n,
                        clo == plo(m, pp as int), chi == plo(m, pp + 1), clo <= chi <= m.c_n, chi - clo <= PW,
                        acc@.len() >= PW,
                        flg@.len() >= PW,
                        outs@.len() == nk,
                        outs_ok(m, p, outs@, bo, nk as int, np as int),
                        msum(outs@, nk as int) <= i64::MAX,
                        k < nk,
                        rp@ == outs@[k as int].rp@,
                        cap == outs@[k as int].cap,
                        base == pp * cap,
                        n == kn(outs@, k as int, pp as int),
                        n <= cap,
                        base + cap <= rp@.len(),
                        rlen == rp@.len(),
                        i <= n,
                        acc_inv(m, p, outs@, bo, k as int, pp as int, i as int, clo as int, chi as int, acc@, flg@),
                    decreases n - i,
                {
                    let ghost acc0 = acc@;
                    let ghost flg0 = flg@;
                    proof {
                        lemma_record_fits(m, p, outs@, bo, nk as int, np as int, k as int, pp as int, i as int, acc@, flg@);
                        assert(krc(outs@, k as int, pp as int)[i as int] == rcv(rp@)[base + i]);
                        assert(krr(outs@, k as int, pp as int)[i as int] == rrv(rp@)[base + i]);
                    }
                    let (cp, rv) = unpack(rp[base + i]);
                    let o = cp - clo;
                    let v = acc[o] + rv;
                    put(&mut acc, o, v);
                    put(&mut flg, o, 1);
                    proof {
                        lemma_record_step(m, p, outs@, bo, k as int, pp as int, i as int, clo as int, chi as int, acc0, flg0, acc@, flg@);
                    }
                    i = i + 1;
                }
                proof {
                    lemma_task_end(m, p, outs@, bo, nk as int, np as int, k as int, pp as int, acc@, flg@);
                }
                k = k + 1;
            }
            proof {
                assert forall|x: int| clo <= x < chi implies {
                    &&& #[trigger] acc@[x - clo] as int == csum(m, p, x)
                    &&& (flg@[x - clo] != 0) == (ccnt(m, p, x) > 0)
                } by {
                    assert(start_at(m, p, outs@, bo, nk as int, clo as int, acc@, flg@, x));
                    lemma_acc_final(m, p, bo[0] as int, bo[nk as int] as int, x);
                }
                lemma_plo_mono(m, 0, pa as int);
            }
            let tlo: usize = if pa * PW < c.c_n { pa * PW } else { c.c_n };
            len = scan_part(&c, tlo, clo, chi, &mut acc, &mut flg, &mut buf, len, Ghost(m), Ghost(p));
            pp = pp + 1;
        }
        AggOut { buf, len }
    }
}

} // verus!
