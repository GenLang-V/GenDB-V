//! The worker tasks of the fast plan.
//!
//! - `P1Task`: pass 1 over a range of lineitem blocks (`pass1::block_pass`): the saturated bound sums of its rows,
//!   applied to the slot bytes directly (`bcap == 0`) or through key-range buckets of `bcap` pending entries that are
//!   flushed when full (each flush touches one key range of the bytes, so the bytes stay in cache).
//! - `MTask`: for a range of key slots, the bound sum over every pass-1 task (`u`; `SAT` when some task saturated)
//!   and a histogram of those values (a heuristic input for the candidate threshold; nothing is proved of it).
//! - `XTask`: for a range of candidate slots, the exact revenue of the slot's key from the rows the l_suppkey key
//!   index lists for it (`keyidx::key_range`), which are exactly the rows of that key (`lemma_index_sum`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::link::query::*;
use crate::link::expr::ival;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::work::put;
use crate::stores::lisupp::interface::common::colfmt as lc;
use crate::stores::lisupp::interface::common::keyidx as lk;
use super::group::*;
use super::model::*;
use super::general::{kr, row_vals, lemma_hit_row};
use super::answer::lemma_acc_perm;
use super::pass1::*;
use super::common::bits::lemma_shr_mono;

verus! {

// ------------------------------------------------------------------------------------------------ pass 1

pub struct P1Task {
    pub c: Li,
    pub w: Win,
    pub g_lo: usize,
    pub g_hi: usize,
    pub acc: Vec<u8>,
    /// Bucket entries (`cnt.len() * bcap`; empty in direct mode).
    pub buf: Vec<u32>,
    /// Entries per bucket (one per bucket of `2^sh` slots; any values, zeroed by the task).
    pub cnt: Vec<usize>,
    pub sh: u32,
    pub bcap: usize,
}

pub struct P1Out {
    pub acc: Vec<u8>,
    pub ok: bool,
}

/// What a pass-1 task's output states of its rows `[a, b)`.
pub open spec fn p1_ok(o: P1Out, c: Li, w: Win, a: int, b: int) -> bool {
    &&& o.acc@.len() >= w.cap
    &&& o.ok ==> acc_ok(o.acc@, w, xs_of(c), a, b) && rows_fast(w, xs_of(c), a, b)
}

/// Zero bound sums are the bound sums of no row.
proof fn lemma_acc_zero(acc: Seq<u8>, w: Win, xs: Seq<Row>, r0: int)
    requires
        acc.len() >= w.cap,
        forall|t: int| 0 <= t < acc.len() ==> #[trigger] acc[t] == 0,
        0 <= r0 <= xs.len(),
    ensures acc_ok(acc, w, xs, r0, r0), rows_fast(w, xs, r0, r0),
{
    let g = qb(w.lo as int, w.hi as int, w.qs as nat);
    assert forall|t: int| 0 <= t < w.cap implies #[trigger] acc[t] as int == sat(gsum(g, xs.subrange(r0, r0), kr(w.kmin + t), 0)) by {
        lemma_empty(g, xs, r0, kr(w.kmin + t), 0);
    }
}

impl WorkerTask for P1Task {
    type Output = P1Out;

    open spec fn pre(&self) -> bool {
        &&& kern_ok(self.c, self.w)
        &&& self.g_lo <= self.g_hi <= self.c.nb
        &&& self.acc@.len() >= self.w.cap
        &&& forall|t: int| 0 <= t < self.acc@.len() ==> #[trigger] self.acc@[t] == 0
    }

    open spec fn post(&self, out: P1Out) -> bool {
        p1_ok(out, self.c, self.w, rs(self.c, self.g_lo as int), rs(self.c, self.g_hi as int))
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.g_lo as u64, self.g_hi as u64)
    }

    fn run(self) -> (out: P1Out) {
        let P1Task { c, w, g_lo, g_hi, acc, buf, cnt, sh, bcap } = self;
        let mut acc = acc;
        let mut buf = buf;
        let mut cnt = cnt;
        let ghost xs = xs_of(c);
        let ghost r0 = rs(c, g_lo as int);
        // the buckets' shape (else the task fails and the query takes the general plan)
        let nbk = cnt.len();
        proof {
            assert(nbk as u128 * bcap as u128 <= 0xFFFF_FFFF_FFFF_FFFF * 0xFFFF_FFFF_FFFF_FFFFu128) by (nonlinear_arith)
                requires nbk <= 0xFFFF_FFFF_FFFF_FFFFu64, bcap <= 0xFFFF_FFFF_FFFF_FFFFu64;
        }
        if !(w.cap >= 1 && w.cap <= 0x100_0000 && sh < 32 && nbk >= 1 && (((w.cap - 1) as u32) >> sh) as usize <= nbk - 1
            && nbk as u128 * bcap as u128 == buf.len() as u128)
        {
            return P1Out { acc, ok: false };
        }
        let mut i: usize = 0;
        while i < nbk
            invariant nbk == cnt@.len(), i <= nbk, forall|b: int| 0 <= b < i ==> #[trigger] cnt@[b] == 0,
            decreases nbk - i,
        {
            put(&mut cnt, i, 0);
            i = i + 1;
        }
        proof {
            lemma_rs_mono(c, g_lo as int, g_hi as int);
            assert forall|t: int| 0 <= t < w.cap implies #[trigger] bko(t, sh) < cnt@.len() by {
                lemma_shr_mono(t as u32, (w.cap - 1) as u32, sh);
            }
            lemma_bk_init(acc@, buf@, cnt@, sh, bcap as int, w, xs, r0);
            lemma_acc_zero(acc@, w, xs, r0);
        }
        let ghost mut pend = Seq::new(cnt@.len(), |b: int| Seq::<u32>::empty());
        let mut b = g_lo;
        let mut ok = true;
        while ok && b < g_hi
            invariant
                kern_ok(c, w),
                xs == xs_of(c),
                g_lo <= b <= g_hi <= c.nb,
                r0 == rs(c, g_lo as int),
                0 <= r0 <= rs(c, b as int),
                ok ==> bk_ok(acc@, buf@, cnt@, sh, bcap as int, pend, w, xs, r0, rs(c, b as int)),
                ok ==> rows_fast(w, xs, r0, rs(c, b as int)),
                acc@.len() >= w.cap,
            decreases g_hi - b, (ok as int),
        {
            proof {
                lemma_rs_mono(c, g_lo as int, b as int);
                lemma_rs_mono(c, b as int, b + 1);
            }
            let (bok, Ghost(p2)) = block_pass(&c, &w, &mut acc, &mut buf, &mut cnt, sh, bcap, b, Ghost(r0), Ghost(pend));
            if bok {
                proof {
                    pend = p2;
                }
                b = b + 1;
            } else {
                ok = false;
            }
        }
        if !ok {
            return P1Out { acc, ok: false };
        }
        flush_all(&mut acc, &buf, &mut cnt, sh, bcap, Ghost(pend), Ghost(w), Ghost(xs), Ghost(r0), Ghost(rs(c, g_hi as int)));
        P1Out { acc, ok: true }
    }
}

// ------------------------------------------------------------------------------------------------ merge

/// The bound sum of a slot whose sum some task saturated.
pub const SAT: u16 = 0xFFFF;

/// Histogram buckets of the merged bound sums (values from `HB` up share the last bucket).
pub const HB: usize = 8192;

/// The pass-1 outputs: task `i` covered the rows `[bnds[i], bnds[i + 1])`, all ok.
pub open spec fn outs_ok(outs: Seq<P1Out>, bnds: Seq<int>, c: Li, w: Win) -> bool {
    &&& bnds.len() == outs.len() + 1
    &&& bnds[0] == 0
    &&& bnds[outs.len() as int] == c.n
    &&& forall|i: int| 0 <= i < outs.len() ==> bnds[i] <= #[trigger] bnds[i + 1]
    &&& forall|i: int| 0 <= i < outs.len() ==> (#[trigger] outs[i]).ok && p1_ok(outs[i], c, w, bnds[i], bnds[i + 1])
}

/// The merged bound sum of slot `t`: not saturated, it is the bound sum over every row.
pub open spec fn u_ok(u: u16, w: Win, xs: Seq<Row>, t: int) -> bool {
    u != SAT ==> u as int == gsum(qb(w.lo as int, w.hi as int, w.qs as nat), xs, kr(w.kmin + t), 0)
}

pub struct MTask {
    pub outs: Arc<Vec<P1Out>>,
    pub nt: usize,
    pub w: Win,
    pub t_lo: usize,
    pub t_hi: usize,
    pub u: Vec<u16>,
    pub hist: Vec<u32>,
    pub top: Vec<u32>,
    pub bnds: Ghost<Seq<int>>,
    pub c: Ghost<Li>,
}

/// A merge task's output: the merged cells `u` of its slots, their histogram, and its local candidates: with `ok`,
/// every slot of `u` at least `tq` is among the first `ntop` entries of `top` (at most `LK`).
pub struct MOut {
    pub u: Vec<u16>,
    pub hist: Vec<u32>,
    pub top: Vec<u32>,
    pub ntop: usize,
    pub tq: usize,
    pub ok: bool,
}

/// Local candidates per merge task, at most.
pub const LK: usize = 8;

/// Slot `t` is among the first `n` entries of `top`.
pub open spec fn listed(top: Seq<u32>, n: int, t: int) -> bool {
    exists|i: int| 0 <= i < n && top[i] == t
}

/// The local candidate facts of a merge task over the slots `[t_lo, t_hi)`.
pub open spec fn local_ok(o: MOut, t_lo: int, t_hi: int) -> bool {
    &&& o.top@.len() <= LK
    &&& o.ntop <= o.top@.len()
    &&& 1 <= o.tq <= HB + 1
    &&& forall|i: int| 0 <= i < o.ntop ==> t_lo <= #[trigger] o.top@[i] < t_hi
    &&& o.ok ==> forall|t: int| t_lo <= t < t_hi && #[trigger] o.u@[t - t_lo] >= o.tq ==> listed(o.top@, o.ntop as int, t)
}

/// One more task's saturated bound sum `x` of slot `t`: below 255 it is exact and adds to the prefix's sum.
proof fn lemma_merge_step(o: P1Out, c: Li, w: Win, a: int, b: int, t: int, s: int)
    requires
        o.ok, p1_ok(o, c, w, a, b),
        0 <= a <= b <= c.n,
        0 <= t < w.cap,
        o.acc@[t] < 255,
        s == gsum(qb(w.lo as int, w.hi as int, w.qs as nat), xs_of(c).subrange(0, a), kr(w.kmin + t), 0),
    ensures
        s + o.acc@[t] == gsum(qb(w.lo as int, w.hi as int, w.qs as nat), xs_of(c).subrange(0, b), kr(w.kmin + t), 0),
{
    let g = qb(w.lo as int, w.hi as int, w.qs as nat);
    lemma_split(g, xs_of(c), 0, a, b, kr(w.kmin + t), 0);
}

/// Flag bit of a merge cell: some task saturated the slot.
pub const MFLAG: u16 = 0x8000;

/// A merge cell `s` of slot `t` after the first `i` tasks (rows `[0, bv[i])`): without the flag it is the exact
/// bound sum (at most `254 i`); with the flag, the low bits stay at most `254 i`.
pub open spec fn mcell(s: u16, i: int, w: Win, xs: Seq<Row>, bv: Seq<int>, t: int) -> bool {
    &&& s < MFLAG ==> s <= 254 * i
        && s as int == gsum(qb(w.lo as int, w.hi as int, w.qs as nat), xs.subrange(0, bv[i]), kr(w.kmin + t), 0)
    &&& s >= MFLAG ==> s - MFLAG <= 254 * i
}

/// Setting the flag of a cell below `2 * MFLAG`.
proof fn lemma_flag(s: u16)
    by (bit_vector)
    ensures (s | 0x8000u16) == (if s < 0x8000u16 { (s + 0x8000u16) as u16 } else { s }),
{
}

/// Adds task `i`'s bytes of the slots `[t_lo, t_hi)` into the merge cells (`MFLAG` for a saturated byte). A function
/// of its own so that `u` and `a` are distinct parameters: the compiler then keeps their buffers apart and
/// vectorizes the loop.
fn merge_bytes(a: &Vec<u8>, u: &mut Vec<u16>, t_lo: usize, t_hi: usize, Ghost(o): Ghost<P1Out>, Ghost(i): Ghost<int>,
    Ghost(w): Ghost<Win>, Ghost(cv): Ghost<Li>, Ghost(bv): Ghost<Seq<int>>)
    requires
        0 <= i < 64,
        a@ == o.acc@,
        o.ok && p1_ok(o, cv, w, bv[i], bv[i + 1]),
        0 <= bv[i] <= bv[i + 1] <= cv.n,
        t_lo <= t_hi <= w.cap,
        old(u)@.len() == t_hi - t_lo,
        forall|t2: int| t_lo <= t2 < t_hi ==> #[trigger] mcell(old(u)@[t2 - t_lo], i, w, xs_of(cv), bv, t2),
    ensures
        final(u)@.len() == t_hi - t_lo,
        forall|t2: int| t_lo <= t2 < t_hi ==> #[trigger] mcell(final(u)@[t2 - t_lo], i + 1, w, xs_of(cv), bv, t2),
    no_unwind
{
    let ghost xs = xs_of(cv);
    let n = t_hi - t_lo;
    // always true (`p1_ok` and the precondition); checked once so no element access needs its own check
    if a.len() < t_hi || u.len() < n {
        proof {
            assert(a@.len() >= w.cap);
        }
        return;
    }
    let mut j: usize = 0;
    while j < n
        invariant
            0 <= i < 64,
            a@ == o.acc@,
            o.ok && p1_ok(o, cv, w, bv[i], bv[i + 1]),
            0 <= bv[i] <= bv[i + 1] <= cv.n,
            xs == xs_of(cv),
            t_lo <= t_hi <= w.cap,
            n == t_hi - t_lo,
            t_hi <= a@.len(),
            u@.len() == n,
            j <= n,
            forall|t2: int| t_lo <= t2 < t_lo + j ==> #[trigger] mcell(u@[t2 - t_lo], i + 1, w, xs, bv, t2),
            forall|t2: int| t_lo + j <= t2 < t_hi ==> #[trigger] mcell(u@[t2 - t_lo], i, w, xs, bv, t2),
        decreases n - j,
    {
        let t = t_lo + j;
        let x = a[t];
        let cur = u[j];
        proof {
            assert(t as int - t_lo as int == j as int);
            assert(mcell(u@[t as int - t_lo as int], i, w, xs, bv, t as int));
            assert(mcell(cur, i, w, xs, bv, t as int));
            lemma_flag(cur);
        }
        let nv: u16 = if x == 255 { cur | MFLAG } else { cur + x as u16 };
        proof {
            if x != 255 && cur < MFLAG {
                lemma_merge_step(o, cv, w, bv[i], bv[i + 1], t as int, cur as int);
            }
            assert(mcell(nv, i + 1, w, xs, bv, t as int));
        }
        u[j] = nv;
        j = j + 1;
    }
}

/// The local candidates of a merge task: a threshold `tq` from the histogram (at most about `LK` cells at or above
/// it; a heuristic), then every slot whose cell is at least `tq` (`ok` false when more than `LK` are).
fn local_top(u: &Vec<u16>, hist: &Vec<u32>, top: Vec<u32>, t_lo: usize, t_hi: usize) -> (r: (Vec<u32>, usize, usize, bool))
    requires
        t_lo <= t_hi,
        u@.len() == t_hi - t_lo,
        hist@.len() == HB + 1,
        top@.len() <= LK,
    ensures
        r.0@.len() == top@.len(),
        r.1 <= top@.len(),
        1 <= r.2 <= HB + 1,
        forall|i: int| 0 <= i < r.1 ==> t_lo <= #[trigger] r.0@[i] < t_hi,
        r.3 ==> forall|t: int| t_lo <= t < t_hi && #[trigger] u@[t - t_lo] >= r.2 ==> listed(r.0@, r.1 as int, t),
    no_unwind
{
    let lk = top.len();
    let mut tq: usize = HB + 1;
    let mut cnt: u64 = 0;
    let mut go = true;
    while go && tq > 1
        invariant 1 <= tq <= HB + 1, cnt <= lk, lk <= LK, hist@.len() == HB + 1,
        decreases tq, (go as int),
    {
        let h = hist[tq - 1] as u64;
        if cnt + h > lk as u64 {
            go = false;
        } else {
            cnt = cnt + h;
            tq = tq - 1;
        }
    }
    let mut top = top;
    let mut ntop: usize = 0;
    let mut ok = true;
    let n = t_hi - t_lo;
    let mut j: usize = 0;
    while j < n
        invariant
            t_lo <= t_hi, n == t_hi - t_lo, u@.len() == n,
            1 <= tq <= HB + 1,
            top@.len() == lk,
            lk <= LK,
            ntop <= lk,
            j <= n,
            t_hi <= usize::MAX,
            forall|i: int| 0 <= i < ntop ==> t_lo <= #[trigger] top@[i] < t_hi,
            ok ==> forall|t: int| t_lo <= t < t_lo + j && #[trigger] u@[t - t_lo] >= tq ==> listed(top@, ntop as int, t),
        decreases n - j,
    {
        if u[j] as usize >= tq {
            if ntop < lk && t_lo + j <= u32::MAX as usize {
                let ghost top0 = top@;
                put(&mut top, ntop, (t_lo + j) as u32);
                proof {
                    if ok {
                        assert forall|t: int| t_lo <= t < t_lo + j + 1 && #[trigger] u@[t - t_lo] >= tq implies listed(top@, ntop + 1, t) by {
                            if t == t_lo + j {
                                assert(top@[ntop as int] == t);
                            } else {
                                assert(listed(top0, ntop as int, t));
                                let i = choose|i: int| 0 <= i < ntop && top0[i] == t;
                                assert(top@[i] == t);
                            }
                        }
                    }
                }
                ntop = ntop + 1;
            } else {
                ok = false;
            }
        }
        j = j + 1;
    }
    (top, ntop, tq, ok)
}

impl WorkerTask for MTask {
    type Output = MOut;

    open spec fn pre(&self) -> bool {
        &&& self.nt == self.outs@.len()
        &&& 1 <= self.nt <= 64
        &&& outs_ok(self.outs@, self.bnds@, self.c@, self.w)
        &&& li_shape(self.c@)
        &&& self.t_lo <= self.t_hi <= self.w.cap
        &&& self.u@.len() == self.t_hi - self.t_lo
        &&& forall|k: int| 0 <= k < self.u@.len() ==> #[trigger] self.u@[k] == 0
        &&& self.hist@.len() == HB + 1
        &&& self.top@.len() <= LK
    }

    open spec fn post(&self, out: MOut) -> bool {
        &&& out.u@.len() == self.t_hi - self.t_lo
        &&& out.hist@.len() == HB + 1
        &&& forall|t: int| self.t_lo <= t < self.t_hi ==> u_ok(#[trigger] out.u@[t - self.t_lo], self.w, xs_of(self.c@), t)
        &&& local_ok(out, self.t_lo as int, self.t_hi as int)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.t_lo as u64, self.t_hi as u64)
    }

    /// Task by task, each task's bytes of the slot range added into `u` (a sequential pass per task; `MFLAG` marks
    /// a saturated byte); then `SAT` for flagged cells and the histogram.
    fn run(self) -> (out: MOut) {
        let MTask { outs, nt, w, t_lo, t_hi, u, hist, top, bnds, c } = self;
        let ghost bv = bnds@;
        let ghost cv = c@;
        let ghost xs = xs_of(cv);
        let ghost ov = outs@;
        let ghost g = qb(w.lo as int, w.hi as int, w.qs as nat);
        let mut u = u;
        let mut hist = hist;
        let n = t_hi - t_lo;
        proof {
            assert forall|t2: int| t_lo <= t2 < t_hi implies #[trigger] mcell(u@[t2 - t_lo], 0, w, xs, bv, t2) by {
                assert(u@[t2 - t_lo] == 0);
                assert(bv[0] == 0);
                lemma_empty(g, xs, 0, kr(w.kmin + t2), 0);
                assert(xs.subrange(0, 0) =~= xs.subrange(0, 0));
            }
        }
        let mut i: usize = 0;
        while i < nt
            invariant
                nt == ov.len(), 1 <= nt <= 64,
                outs@ == ov,
                outs_ok(ov, bv, cv, w),
                xs == xs_of(cv),
                g == qb(w.lo as int, w.hi as int, w.qs as nat),
                t_lo <= t_hi <= w.cap,
                n == t_hi - t_lo,
                u@.len() == n,
                hist@.len() == HB + 1,
                i <= nt,
                forall|t2: int| t_lo <= t2 < t_hi ==> #[trigger] mcell(u@[t2 - t_lo], i as int, w, xs, bv, t2),
            decreases nt - i,
        {
            let ghost o = ov[i as int];
            proof {
                assert(o.ok && p1_ok(o, cv, w, bv[i as int], bv[i + 1]));
                assert(bv[i as int] <= bv[i + 1]);
                lemma_bnds_mono(bv, ov.len() as int, 0, i as int);
                lemma_bnds_mono(bv, ov.len() as int, i + 1, ov.len() as int);
            }
            let a: &Vec<u8> = &outs[i].acc;
            merge_bytes(a, &mut u, t_lo, t_hi, Ghost(o), Ghost(i as int), Ghost(w), Ghost(cv), Ghost(bv));
            i = i + 1;
        }
        proof {
            assert(xs.subrange(0, bv[nt as int]) =~= xs);
        }
        let mut t: usize = t_lo;
        while t < t_hi
            invariant
                nt == ov.len(), 1 <= nt <= 64,
                outs_ok(ov, bv, cv, w),
                xs == xs_of(cv),
                xs.subrange(0, bv[nt as int]) == xs,
                t_lo <= t <= t_hi <= w.cap,
                n == t_hi - t_lo,
                u@.len() == n,
                hist@.len() == HB + 1,
                forall|t2: int| t_lo <= t2 < t ==> u_ok(#[trigger] u@[t2 - t_lo], w, xs, t2),
                forall|t2: int| t <= t2 < t_hi ==> #[trigger] mcell(u@[t2 - t_lo], nt as int, w, xs, bv, t2),
            decreases t_hi - t,
        {
            let s = u[t - t_lo];
            proof {
                assert(mcell(s, nt as int, w, xs, bv, t as int));
            }
            let v: u16 = if s >= MFLAG { SAT } else { s };
            put(&mut u, t - t_lo, v);
            let hb = if (v as usize) < HB { v as usize } else { HB };
            let cur = hist[hb];
            let nh = if cur < u32::MAX { cur + 1 } else { cur };
            put(&mut hist, hb, nh);
            t = t + 1;
        }
        let (top, ntop, tq, ok) = local_top(&u, &hist, top, t_lo, t_hi);
        MOut { u, hist, top, ntop, tq, ok }
    }
}

/// Task boundaries are nondecreasing.
pub proof fn lemma_bnds_mono(bnds: Seq<int>, nt: int, a: int, b: int)
    requires
        bnds.len() == nt + 1,
        forall|i: int| 0 <= i < nt ==> bnds[i] <= #[trigger] bnds[i + 1],
        0 <= a <= b <= nt,
    ensures bnds[a] <= bnds[b],
    decreases b - a,
{
    if a < b {
        lemma_bnds_mono(bnds, nt, a, b - 1);
        assert(bnds[b - 1] <= bnds[(b - 1) + 1]);
    }
}

// ------------------------------------------------------------------------------------------------ exact sums

/// The stored rows in index order (position `p` holds stored row `irow(p)`).
pub open spec fn ys_of(c: Li) -> Seq<Row> {
    lc::stored_rows(xs_of(c), lk::idx_map(c.ic@, c.ib@, c.bs as int, c.n as int))
}

/// No row of `[a, b)` belongs to group `k`: its accumulators are zero.
pub proof fn lemma_no_hits(g: QuerySpec, ys: Seq<Row>, a: int, b: int, k: Row)
    requires
        0 <= a <= b <= ys.len(),
        forall|p: int| a <= p < b ==> !hit(g, #[trigger] ys[p], k),
    ensures
        gsum(g, ys.subrange(a, b), k, 0) == 0,
        gcount(g, ys.subrange(a, b), k) == 0,
    decreases b - a,
{
    if b > a {
        lemma_no_hits(g, ys, a, b - 1, k);
        lemma_range_step(g, ys, a, b - 1, k, 0);
    } else {
        lemma_empty(g, ys, a, k, 0);
    }
}

/// What the exact tasks need of the stored rows: the key index (kind 2, block size `bs`), the slots, the fast
/// row facts.
pub open spec fn ix_ok(c: Li, w: Win, bs: usize) -> bool {
    &&& kern_ok(c, w)
    &&& bs as int == c.bs as int
    &&& c.kind == 2
    &&& lk::keyidx_ok(c.supp@, c.supp_base@, c.ic@, c.ib@, bs as int, 2, c.n as int)
    &&& rows_fast(w, xs_of(c), 0, c.n as int)
}

/// The revenue of group `kr(k)` over the stored rows is its revenue over the index positions `[lo, hi)` that hold
/// exactly the rows of key `k`.
pub proof fn lemma_index_sum(c: Li, w: Win, bs: usize, k: int, lo: int, hi: int)
    requires
        ix_ok(c, w, bs),
        0 <= lo <= hi <= c.n,
        forall|p: int| 0 <= p < c.n ==> (lo <= p < hi <==> #[trigger] lk::fkey(c.supp@, c.supp_base@, bs as int,
            lk::irow(2, c.ic@, c.ib@, bs as int, p)) == k),
    ensures ({
        let g = qg(w.lo as int, w.hi as int);
        &&& gsum(g, xs_of(c), kr(k), 0) == gsum(g, ys_of(c).subrange(lo, hi), kr(k), 0)
        &&& gcount(g, xs_of(c), kr(k)) == gcount(g, ys_of(c).subrange(lo, hi), kr(k))
        &&& forall|p: int| lo <= p < hi ==> (#[trigger] key_of(ys_of(c)[p])) == kr(k)
    }),
{
    let g = qg(w.lo as int, w.hi as int);
    let n = c.n as int;
    let xs = xs_of(c);
    let ys = ys_of(c);
    let m = lk::idx_map(c.ic@, c.ib@, bs as int, n);
    assert(lc::is_perm(m, n));
    lc::lemma_stored_rows_multiset(xs, m);
    lemma_acc_perm(g, ys, xs, kr(k));
    assert forall|p: int| 0 <= p < n implies #[trigger] key_of(ys[p]) == kr(lk::fkey(c.supp@, c.supp_base@, bs as int,
        lk::irow(2, c.ic@, c.ib@, bs as int, p))) by {
        let j = m[p];
        assert(0 <= j < n);
        assert(lk::irow(2, c.ic@, c.ib@, bs as int, p) == j);
        assert(ys[p] == xs[j]);
        lemma_hit_row(c, w.lo as int, w.hi as int, j, k);
    }
    assert forall|p: int| 0 <= p < n && !(lo <= p < hi) implies !hit(g, #[trigger] ys[p], kr(k)) by {
        super::pass1::lemma_kr_inj(lk::fkey(c.supp@, c.supp_base@, bs as int, lk::irow(2, c.ic@, c.ib@, bs as int, p)), k);
    }
    assert forall|p: int| lo <= p < hi implies (#[trigger] key_of(ys[p])) == kr(k) by {}
    lemma_no_hits(g, ys, 0, lo, kr(k));
    lemma_no_hits(g, ys, hi, n, kr(k));
    lemma_split(g, ys, 0, lo, n, kr(k), 0);
    lemma_split(g, ys, lo, hi, n, kr(k), 0);
    assert(ys.subrange(0, n) =~= ys);
}

pub struct XTask {
    pub c: Li,
    pub w: Win,
    pub bs: usize,
    pub cand: Arc<Vec<u32>>,
    pub c_lo: usize,
    pub c_hi: usize,
    pub ex: Vec<i128>,
}

pub struct XOut {
    pub ex: Vec<i128>,
}

/// The exact revenue of the slot's key, from the index positions of that key.
fn slot_sum(c: &Li, w: &Win, bs: usize, t: u32) -> (r: i128)
    requires ix_ok(*c, *w, bs), (t as int) < w.cap,
    ensures r == gsum(qg(w.lo as int, w.hi as int), xs_of(*c), kr(w.kmin + t), 0),
    no_unwind
{
    let ghost g = qg(w.lo as int, w.hi as int);
    let ghost ys = ys_of(*c);
    let k = w.kmin as i128 + t as i128;
    let (lo, hi) = lk::key_range(c.supp, c.supp_base, c.ic, c.ib, bs, 2, c.n, k);
    proof {
        lemma_index_sum(*c, *w, bs, k as int, lo as int, hi as int);
        lemma_empty(g, ys, lo as int, kr(k as int), 0);
    }
    let mut sum: i128 = 0;
    let mut p = lo;
    while p < hi
        invariant
            ix_ok(*c, *w, bs),
            g == qg(w.lo as int, w.hi as int),
            ys == ys_of(*c),
            lo <= p <= hi <= c.n,
            forall|p2: int| lo <= p2 < hi ==> (#[trigger] key_of(ys[p2])) == kr(k as int),
            sum == gsum(g, ys.subrange(lo as int, p as int), kr(k as int), 0),
            0 <= sum <= (p - lo) * 0x400_0000_0000,
            p <= 0x1_0000_0000_0000_0000,
        decreases hi - p,
    {
        proof {
            lk::lemma_irow_bound(c.supp@, c.supp_base@, c.ic@, c.ib@, bs as int, 2, c.n as int, p as int);
            crate::stores::lisupp::interface::common::read::lemma_div_lt(p as int, bs as int, c.ib@.len() as int);
        }
        let j = (c.ib[p / bs] as u128 + c.ic[p] as u128) as usize;
        proof {
            let m = lk::idx_map(c.ic@, c.ib@, bs as int, c.n as int);
            assert(m[p as int] == j);
            assert(ys[p as int] == xs_of(*c)[j as int]);
            lemma_hit_row(*c, w.lo as int, w.hi as int, j as int, k as int);
            lemma_range_step(g, ys, lo as int, p as int, kr(k as int), 0);
            assert(fast_row(w.lo as int, w.hi as int, xs_of(*c)[j as int]));
            crate::stores::lisupp::interface::common::read::lemma_div_lt(j as int, bs as int, c.nb as int);
        }
        let blk = j / bs;
        // the zone map: a row of a block whose dates miss the window does not qualify
        let live = c.ship_base[blk] <= w.hi && c.ship_zmax[blk] >= w.lo;
        let sd: i128 = if live { row_vals(c, j).3 } else { i128::MAX };
        proof {
            if !live {
                assert(ship_v(*c, j as int) <= c.ship_zmax@[j as int / c.bs as int]);
                assert(ship_v(*c, j as int) >= c.ship_base@[j as int / c.bs as int]);
            }
        }
        if live && w.lo as i128 <= sd && sd <= w.hi as i128 {
            let (_sk, pr, ds, _sd) = row_vals(c, j);
            let v = pr * (100 - ds);
            proof {
                assert(0 < v < 0x400_0000_0000);
                assert(sum + v <= (p + 1 - lo) * 0x400_0000_0000) by (nonlinear_arith)
                    requires sum <= (p - lo) * 0x400_0000_0000, v < 0x400_0000_0000;
                assert((p + 1 - lo) * 0x400_0000_0000 <= 0x1_0000_0000_0000_0000 * 0x400_0000_0000) by (nonlinear_arith)
                    requires p + 1 - lo <= 0x1_0000_0000_0000_0000, lo >= 0;
            }
            sum = sum + v;
        } else {
            proof {
                assert(sum <= (p + 1 - lo) * 0x400_0000_0000) by (nonlinear_arith)
                    requires sum <= (p - lo) * 0x400_0000_0000;
            }
        }
        p = p + 1;
    }
    sum
}

impl WorkerTask for XTask {
    type Output = XOut;

    open spec fn pre(&self) -> bool {
        &&& ix_ok(self.c, self.w, self.bs)
        &&& self.c_lo <= self.c_hi <= self.cand@.len()
        &&& forall|i: int| 0 <= i < self.cand@.len() ==> (#[trigger] self.cand@[i] as int) < self.w.cap
        &&& self.ex@.len() == self.c_hi - self.c_lo
    }

    open spec fn post(&self, out: XOut) -> bool {
        &&& out.ex@.len() == self.c_hi - self.c_lo
        &&& forall|i: int| self.c_lo <= i < self.c_hi ==> #[trigger] out.ex@[i - self.c_lo]
                == gsum(qg(self.w.lo as int, self.w.hi as int), xs_of(self.c), kr(self.w.kmin + self.cand@[i]), 0)
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.c_lo as u64, self.c_hi as u64)
    }

    fn run(self) -> (out: XOut) {
        let XTask { c, w, bs, cand, c_lo, c_hi, ex } = self;
        let mut ex = ex;
        let mut i = c_lo;
        while i < c_hi
            invariant
                ix_ok(c, w, bs),
                c_lo <= i <= c_hi <= cand@.len(),
                forall|i2: int| 0 <= i2 < cand@.len() ==> (#[trigger] cand@[i2] as int) < w.cap,
                ex@.len() == c_hi - c_lo,
                forall|i2: int| c_lo <= i2 < i ==> #[trigger] ex@[i2 - c_lo]
                    == gsum(qg(w.lo as int, w.hi as int), xs_of(c), kr(w.kmin + cand@[i2]), 0),
            decreases c_hi - i,
        {
            let t = cand[i];
            let v = slot_sum(&c, &w, bs, t);
            put(&mut ex, i - c_lo, v);
            i = i + 1;
        }
        XOut { ex }
    }
}

} // verus!
