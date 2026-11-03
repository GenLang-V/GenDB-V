//! The live-order kernel: one worker task over stored orders `[pa, pb)` whose lineitem runs are found through the
//! run starts of storage `li_okruns` (`st`: run `k` is stored lineitem rows `[st[k], st[k + 1])`).
//!
//! - Alignment: run `p` belongs to stored orders row `p` (`aligned`) when its first row carries that order's key.
//!   The task checks this at its two ends only; under co-clustering the order positions of consecutive runs strictly
//!   increase, so every run between is aligned too (`lemma_aligned_range`), and `st[p]` splits the stored lineitem
//!   rows at orders position `p` (`lemma_split_aligned`).
//! - Per batch of orders (at most the buffer length, inside one orders block): `gather` writes every order's map
//!   value (`ov`) without branching, `compact` lists the live ones (`lp`, `vbuf`; every order between two listed
//!   ones is dead), and `touch_runs` reads the first and last supplier code of every listed run so the batch's
//!   cache misses overlap.
//! - Phase 1: `collect` checks the rows of each listed run against the supplier map without branching and writes
//!   the hits into the hit list (`hits`); the rows of the dead orders between runs are quiet (`lemma_gap_quiet`).
//!   `hits::drain` then adds the hits to the accumulators. A run that spans two lineitem blocks or does not fit
//!   the list goes, after a drain, through the general path (`slow_order`: `kernel::fast_line` per row).
//! Invariant: the cursor row `j` is the run start of the next order position, and the accumulators hold the rows
//! `[ja, j)` (`ScanCtx::acc_ok`); inside a batch they hold `[ja, jf)` and the hit list the rows `[jf, jc)`.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::stores::facts::interface::cluster::{order_pos, lemma_clustered_le, lemma_order_pos_at, lemma_order_pos_bound};
use crate::agent::q5spec::*;
use crate::agent::chain::*;
use crate::agent::common::forview::*;
use crate::agent::common::sums::*;
use crate::agent::cmap::*;
use crate::agent::setup::{run_l, runs_wf};
use crate::agent::kernel::*;
use crate::agent::hits::*;
use crate::gendb_entry::parallel::WorkerTask;

verus! {

/// Run `p` of the run starts begins with the key of stored orders row `p`.
pub open spec fn aligned(t: ScanCtx, p: int) -> bool {
    &&& 0 <= p < t.n_o
    &&& p < t.st@.len() - 1
    &&& t.lrows@[t.st@[p] as int][0] == t.orows@[p][0]
}

/// Every order position of `[a, b]` is aligned.
pub open spec fn aligned_on(t: ScanCtx, a: int, b: int) -> bool {
    forall|p: int| a <= p <= b ==> #[trigger] aligned(t, p)
}

/// The order position of stored lineitem row `j` is `p < n_o` exactly when the row carries `p`'s key.
proof fn lemma_op_key(t: ScanCtx, j: int, p: int)
    requires t.wf(), 0 <= j < t.n_l, 0 <= p < t.n_o,
    ensures (t.op(j) == p) <==> (t.lrows@[j][0] == t.orows@[p][0]),
{
    let k = t.lrows@[j][0];
    lemma_fkf(t.orows@, k, 0);
    if t.lrows@[j][0] == t.orows@[p][0] {
        assert forall|q: int| 0 <= q < t.orows@.len() && q != p implies #[trigger] t.orows@[q][0] != k by {
            if t.orows@[q][0] == k {
                assert(t.orows@[q][0] == t.orows@[p][0]);
            }
        }
        lemma_order_pos_at(t.orows@, k, p);
    }
}

/// Run starts never decrease.
proof fn lemma_st_mono(t: ScanCtx, a: int, b: int)
    requires t.wf(), 0 <= a <= b < t.st@.len(),
    ensures t.st@[a] <= t.st@[b],
    decreases b - a,
{
    if a < b {
        lemma_st_mono(t, a, b - 1);
        assert(run_l(t.lrows@, t.st@, b - 1));
    }
}

/// The order position of the first row of run `k`.
pub open spec fn fpos(t: ScanCtx, k: int) -> int {
    t.op(t.st@[k] as int)
}

/// Consecutive runs: their order positions never decrease, and strictly increase from a position inside the table.
proof fn lemma_run_step(t: ScanCtx, k: int)
    requires t.wf(), t.clustered, 0 <= k, k + 2 < t.st@.len(),
    ensures
        fpos(t, k) <= fpos(t, k + 1),
        fpos(t, k) < t.n_o ==> fpos(t, k) < fpos(t, k + 1),
{
    let st = t.st@;
    let l = t.lrows@;
    assert(run_l(l, st, k));
    assert(run_l(l, st, k + 1));
    let a = st[k] as int;
    let b = st[k + 1] as int;
    assert(l[b - 1][0] == l[a][0]);
    lemma_clustered_le(l, t.orows@, a, b);
    lemma_order_pos_bound(t.orows@, l[a][0]);
    if fpos(t, k) < t.n_o && fpos(t, k) == fpos(t, k + 1) {
        let q = fpos(t, k);
        lemma_op_key(t, a, q);
        lemma_op_key(t, b, q);
        assert(l[b][0] == l[a][0]);
    }
}

/// Order positions of runs never decrease.
proof fn lemma_fpos_mono(t: ScanCtx, a: int, b: int)
    requires t.wf(), t.clustered, 0 <= a <= b < t.st@.len() - 1,
    ensures fpos(t, a) <= fpos(t, b),
{
    lemma_st_mono(t, a, b);
    assert(run_l(t.lrows@, t.st@, b));
    lemma_clustered_le(t.lrows@, t.orows@, t.st@[a] as int, t.st@[b] as int);
}

/// An aligned run starts at its order's position.
proof fn lemma_fpos_aligned(t: ScanCtx, p: int)
    requires t.wf(), aligned(t, p),
    ensures fpos(t, p) == p,
{
    assert(run_l(t.lrows@, t.st@, p));
    lemma_op_key(t, t.st@[p] as int, p);
}

/// Upward from an aligned run, below an aligned run: `fpos(k) >= k`.
proof fn lemma_up(t: ScanCtx, p1: int, p2: int, k: int)
    requires t.wf(), t.clustered, aligned(t, p1), aligned(t, p2), p1 <= k <= p2,
    ensures fpos(t, k) >= k,
    decreases k - p1,
{
    if k == p1 {
        lemma_fpos_aligned(t, p1);
    } else {
        lemma_up(t, p1, p2, k - 1);
        lemma_fpos_mono(t, k - 1, p2);
        lemma_fpos_aligned(t, p2);
        lemma_run_step(t, k - 1);
    }
}

/// Downward from an aligned run: `fpos(k) <= k`.
proof fn lemma_down(t: ScanCtx, p1: int, p2: int, k: int)
    requires t.wf(), t.clustered, aligned(t, p1), aligned(t, p2), p1 <= k <= p2,
    ensures fpos(t, k) <= k,
    decreases p2 - k,
{
    if k == p2 {
        lemma_fpos_aligned(t, p2);
    } else {
        lemma_down(t, p1, p2, k + 1);
        lemma_fpos_mono(t, k + 1, p2);
        lemma_fpos_aligned(t, p2);
        lemma_run_step(t, k);
    }
}

/// Every run between two aligned runs is aligned: their order positions strictly increase and start and end at
/// the runs' indices, so they are exactly the indices.
pub proof fn lemma_aligned_range(t: ScanCtx, p1: int, p2: int)
    requires t.wf(), t.clustered, aligned(t, p1), aligned(t, p2), p1 <= p2,
    ensures aligned_on(t, p1, p2),
{
    assert forall|k: int| p1 <= k <= p2 implies #[trigger] aligned(t, k) by {
        lemma_up(t, p1, p2, k);
        lemma_down(t, p1, p2, k);
        assert(run_l(t.lrows@, t.st@, k));
        lemma_op_key(t, t.st@[k] as int, k);
    }
}

/// The first row of an aligned run splits the stored lineitem rows at its order's position.
pub proof fn lemma_split_aligned(t: ScanCtx, p: int)
    requires t.wf(), t.clustered, aligned(t, p),
    ensures t.split_at(p, t.st@[p] as int),
{
    let st = t.st@;
    let l = t.lrows@;
    let s = st[p] as int;
    assert(run_l(l, st, p));
    lemma_fpos_aligned(t, p);
    if p > 0 {
        assert(run_l(l, st, p - 1));
        assert(l[s - 1][0] == l[st[p - 1] as int][0]);
        lemma_clustered_le(l, t.orows@, s - 1, s);
        lemma_op_key(t, s - 1, p);
    } else {
        assert(st[0] == 0);
    }
    assert forall|j: int| 0 <= j < t.n_l implies (j < s <==> #[trigger] t.op(j) < p) by {
        if j >= s {
            lemma_clustered_le(l, t.orows@, s, j);
        } else {
            lemma_clustered_le(l, t.orows@, j, s - 1);
        }
    }
}

/// Whether run `p` is aligned (one key compare).
pub fn check_aligned(t: &ScanCtx, p: usize) -> (r: bool)
    requires t.wf(),
    ensures r ==> aligned(*t, p as int),
    no_unwind
{
    if p < t.n_o && p < t.st_n - 1 {
        let a = t.st[p] as usize;
        proof {
            assert(run_l(t.lrows@, t.st@, p as int));
        }
        let lk = get32(t.lk_c, t.lk_b, t.ldiv, t.n_l, a);
        let ok = get32(t.ok_c, t.ok_b, t.odiv, t.n_o, p);
        proof {
            assert(t.lrow_ok(a as int));
            assert(t.orow_ok(p as int));
        }
        lk == ok
    } else {
        false
    }
}

/// Rows `[x, y)` between the splits at order positions `q0 <= q1` belong to orders of `[q0, q1)`, all dead
/// (`ov == 0`): every accumulator is unchanged over them.
proof fn lemma_quiet_gap(t: ScanCtx, qkey: Seq<i64>, qgrp: Seq<usize>, ms: Seq<Vec<u64>>, cmd: Div, sms: Seq<Vec<u64>>, smd: Div,
    q0: int, q1: int, ja: int, x: int, y: int, cnt: Seq<usize>, sum: Seq<i128>, abs: Seq<u128>, ovf: Seq<bool>)
    requires
        t.wf(), qlist_ok(t.rs@, t.prm@, qkey, qgrp, t.qrow@, t.gnames@),
        map_ok(t, qkey, ms, cmd, sms, smd, true), t.cdense,
        0 <= q0 <= q1 <= t.n_o,
        t.split_at(q0, x), t.split_at(q1, y), 0 <= ja <= x,
        forall|q: int| q0 <= q < q1 ==> #[trigger] ov(t, ms, cmd.bs as int, q) == 0,
        cnt.len() == t.gnames@.len() && sum.len() == t.gnames@.len() && abs.len() == t.gnames@.len() && ovf.len() == t.gnames@.len(),
        forall|gi: int| 0 <= gi < t.gnames@.len() ==> #[trigger] t.acc_ok(gi, ja, x, cnt[gi], sum[gi], abs[gi], ovf[gi]),
    ensures
        x <= y,
        forall|gi: int| 0 <= gi < t.gnames@.len() ==> #[trigger] t.acc_ok(gi, ja, y, cnt[gi], sum[gi], abs[gi], ovf[gi]),
{
    if y < x {
        assert(t.op(y) < q0);
        assert(t.op(y) >= q1);
    }
    // every row of the gap has a dead key
    assert forall|j: int| x <= j < y implies key_dead(t.rs@, t.prm@, (#[trigger] t.lrows@[j])[0]) by {
        let q = t.op(j);
        assert(q0 <= q < q1);
        lemma_op_key(t, j, q);
        assert(ov(t, ms, cmd.bs as int, q) == 0);
        lemma_ov(t, qkey, qgrp, ms, cmd, sms, smd, q);
    }
    assert forall|gi: int| 0 <= gi < t.gnames@.len() implies #[trigger] t.acc_ok(gi, ja, y, cnt[gi], sum[gi], abs[gi], ovf[gi]) by {
        assert(t.acc_ok(gi, ja, x, cnt[gi], sum[gi], abs[gi], ovf[gi]));
        assert forall|m: int| #[trigger] t.lsum(gi, m, ja, y) == t.lsum(gi, m, ja, x) by {
            let f = contrib_fn(t.rs@, t.prm@, gkey(t.gnames@, gi), m);
            assert forall|j: int| x <= j < y implies f(#[trigger] t.lrows@[j]) == 0 by {
                assert(key_dead(t.rs@, t.prm@, t.lrows@[j][0]));
                assert(line_mult(t.rs@, t.prm@, gkey(t.gnames@, gi), t.lrows@[j]) == 0);
            }
            lemma_sum_range_zero(t.lrows@, f, x, y);
            lemma_sum_range_split(t.lrows@, f, ja, x, y);
        }
        assert(t.lsum(gi, 0, ja, y) == t.lsum(gi, 0, ja, x));
        assert(t.lsum(gi, 1, ja, y) == t.lsum(gi, 1, ja, x));
        assert(t.lsum(gi, 2, ja, y) == t.lsum(gi, 2, ja, x));
    }
}

/// The listed live orders of a batch starting at `qa`: entry `k` is order `lp[k]` with map value `vb[k]`;
/// positions strictly increase; `gap_lo(k)` is where the dead orders before entry `k` begin.
pub open spec fn gap_lo(lp: Seq<usize>, qa: int, k: int) -> int {
    if k == 0 { qa } else { lp[k - 1] as int + 1 }
}

pub open spec fn listed_ok(t: ScanCtx, ms: Seq<Vec<u64>>, cw: int, lp: Seq<usize>, vb: Seq<u8>, qa: int, n: int, hi: int) -> bool {
    &&& 0 <= n <= lp.len() && n <= vb.len()
    &&& forall|k: int| 0 <= k < n ==> qa <= #[trigger] lp[k] && gap_lo(lp, qa, k) <= lp[k] < hi
    &&& forall|k: int| 0 <= k < n ==> #[trigger] vb[k] as u64 == ov(t, ms, cw, lp[k] as int) && vb[k] != 0
    &&& forall|k: int, q: int| 0 <= k < n && gap_lo(lp, qa, k) <= q < #[trigger] lp[k] ==> #[trigger] ov(t, ms, cw, q) == 0
    &&& forall|q: int| gap_lo(lp, qa, n) <= q < hi ==> #[trigger] ov(t, ms, cw, q) == 0
}

/// The map value an order's gathered map word `w` and nibble index `o` give: the nibble when `o < 16`, else 0.
pub open spec fn ov_of(w: u64, o: u8) -> u64 {
    if o < 16 { nib(w, o as u64) } else { 0 }
}

/// The customer map word of row `c`: word `w = c / 16` is entry `w - ch * cw` of chunk `ch = w / cw`.
proof fn lemma_map_index(cw: int, c: int, w: int, ch: int)
    requires cw >= 1, c >= 0, w == c / 16, ch == w / cw,
    ensures w - ch * cw == w % cw, 0 <= w - ch * cw < cw,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(w, cw);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(w, cw);
    assert(cw * ch == ch * cw) by (nonlinear_arith);
}

/// One element of the gather pass: inside orders block `blk` (bases `db`, `cb` hoisted), the date `d` and customer
/// key `ck` are the row's; the customer map word at `(c / 16) / cw, (c / 16) % cw` is read by shift and mask, and
/// the nibble index `c % 16` (or 16 when the order is out of the window or has no customer row) gives `ov`.
proof fn lemma_gather_one(t: ScanCtx, qkey: Seq<i64>, ms: Seq<Vec<u64>>, cmd: Div, sms: Seq<Vec<u64>>, smd: Div,
    p: int, blk: int, d: int, ck: int, ok: bool, c: usize, w: usize, ch: usize, word: u64, o: u8)
    requires
        t.wf(), map_ok(t, qkey, ms, cmd, sms, smd, true), t.n_c >= 1,
        0 <= p < t.n_o, p / (t.odiv.bs as int) == blk,
        d == t.od_b@[blk] + t.od_c@[p], ck == t.oc_b@[blk] + t.oc_c@[p],
        ok == (t.lo_day <= d < t.hi_day && 1 <= ck <= t.n_c),
        c as int == (if ok { ck - 1 } else { 0 }),
        w as int == c as int / 16, ch as int == w as int / (cmd.bs as int),
        word == ms[ch as int]@[w as int - ch as int * cmd.bs as int],
        o == (if ok { (c % 16) as u8 } else { 16u8 }),
    ensures
        ov_of(word, o) == ov(t, ms, cmd.bs as int, p),
{
    let cw = cmd.bs as int;
    let bs = t.odiv.bs as int;
    assert(fv16(t.od_c@, t.od_b@, bs, p) == d);
    assert(fv32(t.oc_c@, t.oc_b@, bs, p) == ck);
    lemma_map_index(cw, c as int, w as int, ch as int);
    if ok {
        assert(cmap_val(ms, cw, c as int) == nib(word, (c as int % 16) as u64));
    }
}

/// The inline supplier check of stored lineitem row `j` of live order `p` (map value `v != 0` or not) failed: the
/// supplier key `sk` is no supplier row's (`!okk`), or the supplier's map value `sv` differs from the order's.
/// Then the row takes part in no group (the miss branch of `kernel::fast_line`).
proof fn lemma_line_miss_h(t: ScanCtx, qkey: Seq<i64>, qgrp: Seq<usize>, ms: Seq<Vec<u64>>, cmd: Div, sms: Seq<Vec<u64>>, smd: Div,
    j: int, p: int, v: u64, sk: int, okk: bool, sv: u64)
    requires
        t.wf(), qlist_ok(t.rs@, t.prm@, qkey, qgrp, t.qrow@, t.gnames@),
        map_ok(t, qkey, ms, cmd, sms, smd, true), t.cdense, t.sdense,
        0 <= j < t.n_l, 0 <= p < t.n_o, t.lrows@[j][0] == t.orows@[p][0],
        v == ov(t, ms, cmd.bs as int, p),
        sk == fv32(t.ls_c@, t.ls_b@, t.ldiv.bs as int, j),
        okk == (1 <= sk <= t.n_s),
        okk ==> sv == cmap_val(sms, smd.bs as int, sk - 1),
        !(okk && sv == v),
    ensures
        forall|gi: int| 0 <= gi < t.gnames@.len() ==> #[trigger] line_mult(t.rs@, t.prm@, gkey(t.gnames@, gi), t.lrows@[j]) == 0,
{
    let rs = t.rs@;
    let prm = t.prm@;
    let gn = t.gnames@;
    let l = t.lrows@[j];
    assert(t.lrow_ok(j));
    lemma_ov(t, qkey, qgrp, ms, cmd, sms, smd, p);
    if v == 0 {
        assert forall|gi: int| 0 <= gi < gn.len() implies #[trigger] line_mult(rs, prm, gkey(gn, gi), l) == 0 by {
            assert(key_dead(rs, prm, t.orows@[p][0]));
        }
    } else {
        let qq = (v - 1) as int;
        let oi = t.omap@[p];
        let ci = fv32(t.oc_c@, t.oc_b@, t.odiv.bs as int, p) - 1;
        let cnk = qkey[qq];
        if !okk {
            assert forall|i: int| 0 <= i < rs.s.len() implies #[trigger] rs.s[i][0] != l[2] by {
                assert(t.srow_ok(i));
            }
        } else {
            let s0 = sk - 1;
            let snk = fv8(t.sn_c@, t.sn_b@, t.sdiv.bs as int, s0);
            assert(t.srow_ok(s0));
            assert(cmap_val(sms, smd.bs as int, s0) == qvl(qkey, snk));
            lemma_qvl(qkey, snk);
            lemma_qvl(qkey, cnk as int);
            assert(snk != cnk as int);
            assert(rs.s[s0][0] == l[2] && rs.s[s0][3] != Val::Int(cnk as int));
        }
        assert forall|gi: int| 0 <= gi < gn.len() implies #[trigger] line_mult(rs, prm, gkey(gn, gi), l) == 0 by {
            lemma_line_miss(rs, prm, qkey, qgrp, t.qrow@, gn, l, oi, ci, qq, cnk, gkey(gn, gi));
        }
    }
}

/// One step of phase 0: order `p` (map value `v`) is written at entry `n`; the list grows when `v != 0`.
proof fn lemma_list_step(t: ScanCtx, ms: Seq<Vec<u64>>, cw: int, lp0: Seq<usize>, vb0: Seq<u8>, lp1: Seq<usize>, vb1: Seq<u8>,
    qa: int, n: int, p: int, v: u64)
    requires
        listed_ok(t, ms, cw, lp0, vb0, qa, n, p),
        0 <= qa <= p < usize::MAX, 0 <= n < lp0.len(), n < vb0.len(),
        lp1 == lp0.update(n, p as usize), vb1 == vb0.update(n, v as u8),
        v == ov(t, ms, cw, p), v < 16,
    ensures
        listed_ok(t, ms, cw, lp1, vb1, qa, if v != 0 { n + 1 } else { n }, p + 1),
{
    assert forall|k: int| 0 <= k <= n implies #[trigger] gap_lo(lp1, qa, k) == gap_lo(lp0, qa, k) by {
        if k > 0 {
            assert(lp1[k - 1] == lp0[k - 1]);
        }
    }
    let n2 = if v != 0 { n + 1 } else { n };
    assert(lp1[n] as int == p);
    assert forall|k: int| 0 <= k < n2 implies qa <= #[trigger] lp1[k] && gap_lo(lp1, qa, k) <= lp1[k] < p + 1 by {
        if k < n {
            assert(lp1[k] == lp0[k]);
        } else {
            assert(gap_lo(lp0, qa, n) <= p);
        }
    }
    assert forall|k: int| 0 <= k < n2 implies #[trigger] vb1[k] as u64 == ov(t, ms, cw, lp1[k] as int) && vb1[k] != 0 by {
        if k < n {
            assert(lp1[k] == lp0[k] && vb1[k] == vb0[k]);
        }
    }
    assert forall|k: int, q: int| 0 <= k < n2 && gap_lo(lp1, qa, k) <= q < #[trigger] lp1[k]
        implies #[trigger] ov(t, ms, cw, q) == 0 by {
        if k < n {
            assert(lp1[k] == lp0[k]);
            assert(gap_lo(lp0, qa, k) <= q < lp0[k]);
        } else {
            assert(gap_lo(lp0, qa, n) <= q < p);
        }
    }
    if v != 0 {
        assert(gap_lo(lp1, qa, n + 1) == p + 1);
    } else {
        assert forall|q: int| gap_lo(lp1, qa, n) <= q < p + 1 implies #[trigger] ov(t, ms, cw, q) == 0 by {
            if q < p {
                assert(gap_lo(lp0, qa, n) <= q < p);
            }
        }
    }
}

/// The supplier check of stored lineitem row `j` of live order `p` (map value `v != 0`) succeeded: the row takes
/// part once in the order's group `qgrp[v - 1]` (the hit branch of `kernel::fast_line`).
proof fn lemma_line_hit_h(t: ScanCtx, qkey: Seq<i64>, qgrp: Seq<usize>, ms: Seq<Vec<u64>>, cmd: Div, sms: Seq<Vec<u64>>, smd: Div,
    j: int, p: int, v: u64, sk: int, sv: u64)
    requires
        t.wf(), qlist_ok(t.rs@, t.prm@, qkey, qgrp, t.qrow@, t.gnames@),
        map_ok(t, qkey, ms, cmd, sms, smd, true), t.cdense, t.sdense,
        0 <= j < t.n_l, 0 <= p < t.n_o, t.lrows@[j][0] == t.orows@[p][0],
        v == ov(t, ms, cmd.bs as int, p), v != 0,
        sk == fv32(t.ls_c@, t.ls_b@, t.ldiv.bs as int, j), 1 <= sk <= t.n_s,
        sv == cmap_val(sms, smd.bs as int, sk - 1), sv == v,
    ensures
        0 <= v - 1 < qgrp.len(),
        hit_in(t, j, qgrp[v - 1] as int),
{
    let rs = t.rs@;
    let prm = t.prm@;
    let gn = t.gnames@;
    let l = t.lrows@[j];
    assert(t.lrow_ok(j));
    lemma_ov(t, qkey, qgrp, ms, cmd, sms, smd, p);
    let qq = (v - 1) as int;
    let oi = t.omap@[p];
    let ci = fv32(t.oc_c@, t.oc_b@, t.odiv.bs as int, p) - 1;
    let cnk = qkey[qq];
    let s = sk - 1;
    let snk = fv8(t.sn_c@, t.sn_b@, t.sdiv.bs as int, s);
    let g = qgrp[qq];
    assert(t.srow_ok(s));
    assert(cmap_val(sms, smd.bs as int, s) == qvl(qkey, snk));
    lemma_qvl(qkey, snk);
    lemma_qvl(qkey, cnk as int);
    assert(snk == cnk as int);
    assert forall|gi: int| 0 <= gi < gn.len() implies
        #[trigger] line_mult(rs, prm, gkey(gn, gi), l) == if gi == g as int { 1int } else { 0int } by {
        lemma_line_hit(rs, prm, qkey, qgrp, t.qrow@, gn, l, oi, ci, qq, cnk, s, gkey(gn, gi));
        lemma_gkey_eq(gn, gi, g as int);
    }
}

/// The rows of the dead orders `[q0, q1)` between the splits `x` and `y` take part in no group.
proof fn lemma_gap_quiet(t: ScanCtx, qkey: Seq<i64>, qgrp: Seq<usize>, ms: Seq<Vec<u64>>, cmd: Div, sms: Seq<Vec<u64>>, smd: Div,
    q0: int, q1: int, x: int, y: int)
    requires
        t.wf(), qlist_ok(t.rs@, t.prm@, qkey, qgrp, t.qrow@, t.gnames@),
        map_ok(t, qkey, ms, cmd, sms, smd, true), t.cdense,
        0 <= q0 <= q1 <= t.n_o,
        t.split_at(q0, x), t.split_at(q1, y),
        forall|q: int| q0 <= q < q1 ==> #[trigger] ov(t, ms, cmd.bs as int, q) == 0,
    ensures
        x <= y,
        forall|j: int| x <= j < y ==> #[trigger] quiet(t, j),
{
    if y < x {
        assert(t.op(y) < q0);
        assert(t.op(y) >= q1);
    }
    assert forall|j: int| x <= j < y implies #[trigger] quiet(t, j) by {
        let q = t.op(j);
        assert(q0 <= q < q1);
        lemma_op_key(t, j, q);
        assert(ov(t, ms, cmd.bs as int, q) == 0);
        lemma_ov(t, qkey, qgrp, ms, cmd, sms, smd, q);
        assert(key_dead(t.rs@, t.prm@, t.lrows@[j][0]));
        assert forall|gi: int| 0 <= gi < t.gnames@.len() implies
            #[trigger] line_mult(t.rs@, t.prm@, gkey(t.gnames@, gi), t.lrows@[j]) == 0 by {
        }
    }
}

/// Phase 0a: the map value of every order `[qa, qa + len)` of orders block `blk` (date and customer bases `db`,
/// `cb` hoisted), branch free: `vt[x] = ov(qa + x)`.
#[inline(never)]
fn gather(Ghost(t): Ghost<ScanCtx>, Ghost(qkey): Ghost<Seq<i64>>, Ghost(sms): Ghost<Seq<Vec<u64>>>, Ghost(smd): Ghost<Div>,
    od_c: &[u16], oc_c: &[u32], db: i64, cb: i64, lo: i64, hi: i64, nc: usize,
    ms: &Vec<Vec<u64>>, cmd: Div, qa: usize, len: usize, Ghost(blk): Ghost<int>, vt: &mut Vec<u8>)
    requires
        t.wf(), map_ok(t, qkey, ms@, cmd, sms, smd, true), t.n_c >= 1, cmd.p2,
        od_c == t.od_c, oc_c == t.oc_c, lo == t.lo_day, hi == t.hi_day, nc == t.n_c,
        0 <= blk, blk * (t.odiv.bs as int) <= qa, qa + len <= blk * (t.odiv.bs as int) + t.odiv.bs as int,
        qa + len <= t.n_o, blk < t.od_b@.len(), blk < t.oc_b@.len(),
        db == t.od_b@[blk], cb == t.oc_b@[blk],
        len <= old(vt)@.len(),
    ensures
        final(vt)@.len() == old(vt)@.len(),
        forall|x: int| 0 <= x < len ==> (#[trigger] final(vt)@[x]) as u64 == ov(t, ms@, cmd.bs as int, qa + x) && final(vt)@[x] < 16,
    no_unwind
{
    let ghost cw = cmd.bs as int;
    let ghost bs = t.odiv.bs as int;
    let ghost vlen = vt@.len();
    let cbs = cmd.bs;
    let mut i: usize = 0;
    while i < len
        invariant
            vt@.len() == vlen,
            t.wf(), map_ok(t, qkey, ms@, cmd, sms, smd, true), t.n_c >= 1, cmd.p2, cw == cmd.bs as int, cbs == cmd.bs,
            od_c == t.od_c, oc_c == t.oc_c, lo == t.lo_day, hi == t.hi_day, nc == t.n_c, bs == t.odiv.bs as int,
            0 <= blk, blk * bs <= qa, qa + len <= blk * bs + bs, qa + len <= t.n_o,
            blk < t.od_b@.len(), blk < t.oc_b@.len(), db == t.od_b@[blk], cb == t.oc_b@[blk],
            len <= vt@.len(), i <= len,
            forall|x: int| 0 <= x < i ==> (#[trigger] vt@[x]) as u64 == ov(t, ms@, cw, qa + x) && vt@[x] < 16,
        decreases len - i,
    {
        let p = qa + i;
        proof {
            lemma_in_blk(p as int, bs, blk);
            assert(fv16(t.od_c@, t.od_b@, bs, p as int) == db + t.od_c@[p as int]);
            assert(fv32(t.oc_c@, t.oc_b@, bs, p as int) == cb + t.oc_c@[p as int]);
        }
        let d = od_c[p] as i64 + db;
        let ck = oc_c[p] as i64 + cb;
        let ok = lo <= d && d < hi && 1 <= ck && (ck as u64) <= (nc as u64);
        let c: usize = if ok { (ck - 1) as usize } else { 0 };
        let w = c / 16;
        let ch = shr_div(cmd, w);
        proof {
            lemma_map_index(cw, c as int, w as int, ch as int);
            assert(cmap_has(ms@, cw, c as int));
            lemma_shift_ok((c % 16) as u64);
        }
        let word = ms[ch][w - ch * cbs];
        let wv = if ok { word } else { 0u64 };
        let v = (wv >> (((c % 16) as u64) << 2u64)) & 15u64;
        proof {
            lemma_nib_lt16(wv, (c % 16) as u64);
            if ok {
                assert(v == cmap_val(ms@, cw, c as int));
            } else {
                lemma_nib_zero((c % 16) as u64);
            }
            assert(v == ov(t, ms@, cw, p as int));
        }
        let ghost vt0 = vt@;
        vt[i] = v as u8;
        proof {
            assert forall|x: int| 0 <= x < i + 1 implies (#[trigger] vt@[x]) as u64 == ov(t, ms@, cw, qa + x) && vt@[x] < 16 by {
                if x < i {
                    assert(vt@[x] == vt0[x]);
                }
            }
        }
        i = i + 1;
    }
}

/// Phase 0b: the live orders of `[qa, qa + len)` (map value `vt[x] != 0`) and their map values, branch free.
#[inline(never)]
fn compact(Ghost(t): Ghost<ScanCtx>, Ghost(ms): Ghost<Seq<Vec<u64>>>, Ghost(cw): Ghost<int>,
    vt: &Vec<u8>, qa: usize, len: usize, lp: &mut Vec<usize>, vb: &mut Vec<u8>) -> (n: usize)
    requires
        len <= vt@.len(), len <= old(lp)@.len(), old(vb)@.len() == old(lp)@.len(), qa + len < usize::MAX,
        forall|x: int| 0 <= x < len ==> (#[trigger] vt@[x]) as u64 == ov(t, ms, cw, qa + x) && vt@[x] < 16,
    ensures
        final(lp)@.len() == old(lp)@.len(), final(vb)@.len() == old(vb)@.len(), n <= len,
        listed_ok(t, ms, cw, final(lp)@, final(vb)@, qa as int, n as int, qa + len),
    no_unwind
{
    let ghost lplen = lp@.len();
    let mut n: usize = 0;
    let mut i: usize = 0;
    while i < len
        invariant
            lp@.len() == lplen,
            len <= vt@.len(), len <= lp@.len(), vb@.len() == lp@.len(), qa + len < usize::MAX,
            forall|x: int| 0 <= x < len ==> (#[trigger] vt@[x]) as u64 == ov(t, ms, cw, qa + x) && vt@[x] < 16,
            n <= i <= len,
            listed_ok(t, ms, cw, lp@, vb@, qa as int, n as int, qa + i),
        decreases len - i,
    {
        let p = qa + i;
        let v = vt[i];
        let ghost lp0 = lp@;
        let ghost vb0 = vb@;
        lp[n] = p;
        vb[n] = v;
        let n2 = if v != 0 { n + 1 } else { n };
        proof {
            assert(vt@[i as int] as u64 == ov(t, ms, cw, qa + i));
            assert(lp@ == lp0.update(n as int, p));
            assert(vb@ == vb0.update(n as int, v));
            assert((v as u64) as u8 == v);
            lemma_list_step(t, ms, cw, lp0, vb0, lp@, vb@, qa as int, n as int, p as int, v as u64);
        }
        n = n2;
        i = i + 1;
    }
    n
}

/// The touch pass: the first and last supplier code of every listed run, so the batch's cache misses overlap
/// (the result is returned so the reads stay).
#[inline(never)]
fn touch_runs(Ghost(t): Ghost<ScanCtx>, st: &[u32], st_n: usize, ls_c: &[u32], nl: usize, lp: &Vec<usize>, n: usize) -> (r: u32)
    requires t.wf(), st == t.st, st_n == t.st_n, ls_c == t.ls_c, nl == t.n_l, n <= lp@.len(),
    no_unwind
{
    let mut touch: u32 = 0;
    let mut k: usize = 0;
    while k < n
        invariant t.wf(), st == t.st, st_n == t.st_n, ls_c == t.ls_c, nl == t.n_l, n <= lp@.len(), k <= n,
        decreases n - k,
    {
        let p = lp[k];
        if st_n > 0 && p < st_n - 1 {
            let a = st[p] as usize;
            let b = st[p + 1] as usize;
            let bl = if b > a { b - 1 } else { a };
            if bl < nl {
                touch = touch ^ ls_c[a] ^ ls_c[bl];
            }
        }
        k = k + 1;
    }
    touch
}

/// Phase 1 for the listed orders `[k0, ...)`: the rows of each order whose run lies in one lineitem block and
/// fits the free entries of the hit list are checked against the supplier map without branching, and the hits are
/// listed (`hits_ok` from the flushed row `jf` to the returned cursor). Stops at the first order that does not
/// fit (the caller drains the list and takes that order on the general path).
#[inline(never)]
fn collect(Ghost(t): Ghost<ScanCtx>, Ghost(qkey): Ghost<Seq<i64>>, Ghost(ms): Ghost<Seq<Vec<u64>>>, Ghost(cmd): Ghost<Div>,
    st: &[u32], ls_c: &[u32], ls_b: &[i64], ldiv: Div, ns: usize, sms: &Vec<Vec<u64>>, smd: Div,
    lp: &Vec<usize>, vb: &Vec<u8>, qgrp: &Vec<usize>, k0: usize, n: usize,
    Ghost(qa): Ghost<int>, Ghost(qb): Ghost<int>, Ghost(pa): Ghost<int>, Ghost(pb): Ghost<int>,
    hb: &mut Vec<usize>, hg: &mut Vec<usize>, h0: usize, Ghost(jf): Ghost<int>, Ghost(jc0): Ghost<int>)
    -> (r: (usize, usize, Ghost<int>))
    requires
        t.wf(), t.clustered, t.cdense, t.sdense, t.n_s >= 1,
        qlist_ok(t.rs@, t.prm@, qkey, qgrp@, t.qrow@, t.gnames@),
        map_ok(t, qkey, ms, cmd, sms@, smd, true),
        st == t.st, ls_c == t.ls_c, ls_b == t.ls_b, ldiv == t.ldiv, ldiv.p2, smd.p2, ns == t.n_s,
        aligned_on(t, pa, pb), 0 <= pa <= qa < qb <= pb, pb < t.n_o,
        listed_ok(t, ms, cmd.bs as int, lp@, vb@, qa, n as int, qb),
        k0 <= n,
        old(hb)@.len() == old(hg)@.len(),
        t.split_at(gap_lo(lp@, qa, k0 as int), jc0),
        hits_ok(t, old(hb)@, old(hg)@, h0 as int, jf, jc0),
    ensures
        k0 <= r.0 <= n,
        final(hb)@.len() == old(hb)@.len(), final(hg)@.len() == old(hg)@.len(),
        t.split_at(gap_lo(lp@, qa, r.0 as int), r.2@),
        hits_ok(t, final(hb)@, final(hg)@, r.1 as int, jf, r.2@),
    no_unwind
{
    let ghost cw = cmd.bs as int;
    let ghost sw_ = smd.bs as int;
    let hcap = hb.len();
    let lbs = ldiv.bs;
    let sbs = smd.bs;
    let nl_ = 0usize;
    let mut k = k0;
    let mut h = h0;
    let mut done = false;
    let ghost mut jc: int = jc0;
    while k < n && !done
        invariant
            t.wf(), t.clustered, t.cdense, t.sdense, t.n_s >= 1,
            qlist_ok(t.rs@, t.prm@, qkey, qgrp@, t.qrow@, t.gnames@),
            map_ok(t, qkey, ms, cmd, sms@, smd, true), cw == cmd.bs as int,
            st == t.st, ls_c == t.ls_c, ls_b == t.ls_b, ldiv == t.ldiv, ldiv.p2, smd.p2, ns == t.n_s,
            lbs == ldiv.bs, sbs == smd.bs,
            aligned_on(t, pa, pb), 0 <= pa <= qa < qb <= pb, pb < t.n_o,
            listed_ok(t, ms, cw, lp@, vb@, qa, n as int, qb),
            k0 <= k <= n,
            hcap == hb@.len(), hb@.len() == hg@.len(),
            t.split_at(gap_lo(lp@, qa, k as int), jc),
            hits_ok(t, hb@, hg@, h as int, jf, jc),
        decreases n - k, if done { 0int } else { 1int },
    {
        let p = lp[k];
        let v = vb[k] as u64;
        proof {
            assert(gap_lo(lp@, qa, k as int) <= lp@[k as int] < qb);
            assert(aligned(t, p as int));
            assert(aligned(t, p as int + 1));
            lemma_split_aligned(t, p as int);
            lemma_split_aligned(t, p as int + 1);
            assert(run_l(t.lrows@, t.st@, p as int));
        }
        let a = st[p] as usize;
        let b = st[p + 1] as usize;
        let lblk = shr_div(ldiv, a);
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(a as int, lbs as int);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(a as int, lbs as int);
            assert(lbs * lblk == lblk * lbs) by (nonlinear_arith);
            lemma_block_index(a as int, lbs as int, t.ls_b@.len() as int);
        }
        let lrem = lbs - (a - lblk * lbs);
        if b - a > lrem || b - a > hcap - h {
            done = true;
        } else {
            proof {
                // the dead orders before `p`: their rows are quiet
                let q0 = gap_lo(lp@, qa, k as int);
                assert forall|q: int| q0 <= q < p implies #[trigger] ov(t, ms, cw, q) == 0 by {
                    assert(gap_lo(lp@, qa, k as int) <= q < lp@[k as int]);
                }
                lemma_gap_quiet(t, qkey, qgrp@, ms, cmd, sms@, smd, q0, p as int, jc, a as int);
                lemma_hits_extend(t, hb@, hg@, h as int, jf, jc, a as int);
                assert(vb@[k as int] as u64 == ov(t, ms, cw, p as int) && vb@[k as int] != 0);
                lemma_ov(t, qkey, qgrp@, ms, cmd, sms@, smd, p as int);
            }
            let g = qgrp[(v - 1) as usize];
            let sbase = ls_b[lblk];
            let mut j = a;
            while j < b
                invariant
                    t.wf(), t.cdense, t.sdense, t.n_s >= 1,
                    qlist_ok(t.rs@, t.prm@, qkey, qgrp@, t.qrow@, t.gnames@),
                    map_ok(t, qkey, ms, cmd, sms@, smd, true), cw == cmd.bs as int,
                    ls_c == t.ls_c, ls_b == t.ls_b, ldiv == t.ldiv, smd.p2, ns == t.n_s, sbs == smd.bs, lbs == ldiv.bs,
                    lblk * lbs <= a, a + lrem == lblk * lbs + lbs, lblk < t.ls_b@.len(), sbase == t.ls_b@[lblk as int],
                    b - a <= lrem, a <= j <= b, b <= t.n_l, p < t.n_o,
                    t.split_at(p as int, a as int), t.split_at(p as int + 1, b as int),
                    v == ov(t, ms, cw, p as int), v != 0, 0 <= v - 1 < qgrp@.len(), g == qgrp@[v - 1],
                    hcap == hb@.len(), hb@.len() == hg@.len(), h + (b - j) <= hcap,
                    hits_ok(t, hb@, hg@, h as int, jf, j as int),
                decreases b - j,
            {
                proof {
                    assert(t.op(j as int) >= p);
                    assert(t.op(j as int) < p + 1);
                    lemma_op_key(t, j as int, p as int);
                    lemma_in_blk(j as int, lbs as int, lblk as int);
                    assert(t.lrow_ok(j as int));
                    assert(fv32(t.ls_c@, t.ls_b@, lbs as int, j as int) == sbase + t.ls_c@[j as int]);
                }
                let sk = ls_c[j] as i64 + sbase;
                let okk = 1 <= sk && (sk as u64) <= (ns as u64);
                let si: usize = if okk { (sk - 1) as usize } else { 0 };
                let sw = si / 16;
                let sch = shr_div(smd, sw);
                proof {
                    lemma_map_index(sbs as int, si as int, sw as int, sch as int);
                    assert(cmap_has(sms@, sbs as int, si as int));
                    lemma_shift_ok((si % 16) as u64);
                }
                let swd = sms[sch][sw - sch * sbs];
                let sv = (swd >> (((si % 16) as u64) << 2u64)) & 15u64;
                let sv2 = if okk { sv } else { 16u64 };
                let ghost hb0 = hb@;
                let ghost hg0 = hg@;
                hb[h] = j;
                hg[h] = g;
                let hit = sv2 == v;
                proof {
                    lemma_nib_lt16(swd, (si % 16) as u64);
                    if okk {
                        assert(sv == cmap_val(sms@, sbs as int, sk - 1));
                    }
                    if hit {
                        lemma_line_hit_h(t, qkey, qgrp@, ms, cmd, sms@, smd, j as int, p as int, v, sk as int, sv);
                    } else {
                        lemma_line_miss_h(t, qkey, qgrp@, ms, cmd, sms@, smd, j as int, p as int, v, sk as int, okk, sv);
                        assert forall|gi: int| 0 <= gi < t.gnames@.len() implies
                            #[trigger] line_mult(t.rs@, t.prm@, gkey(t.gnames@, gi), t.lrows@[j as int]) == 0 by {}
                    }
                    lemma_hits_push(t, hb0, hg0, hb@, hg@, h as int, jf, j as int, g, hit);
                }
                h = if hit { h + 1 } else { h };
                j = j + 1;
            }
            proof {
                jc = b as int;
                assert(gap_lo(lp@, qa, k as int + 1) == p + 1);
            }
            k = k + 1;
        }
    }
    (k, h, Ghost(jc))
}

/// The general path for listed order `k` (its run spans two lineitem blocks or does not fit the hit list): the
/// dead orders before it are skipped, its rows are checked one by one (`kernel::fast_line`) and accumulated. The
/// accumulators move from rows `[ja, jc)` to `[ja, b)`, `b` the end of the order's run.
fn slow_order(t: &ScanCtx, qkey: &Vec<i64>, qgrp: &Vec<usize>, ms: &Vec<Vec<u64>>, cmd: Div, sms: &Vec<Vec<u64>>, smd: Div,
    lp: &Vec<usize>, vb: &Vec<u8>, k: usize, n: usize,
    Ghost(qa): Ghost<int>, Ghost(qb): Ghost<int>, Ghost(pa): Ghost<int>, Ghost(pb): Ghost<int>,
    ja: usize, Ghost(jc): Ghost<int>,
    cnt: &mut Vec<usize>, sum: &mut Vec<i128>, abs: &mut Vec<u128>, ovf: &mut Vec<bool>) -> (b: usize)
    requires
        t.wf(), t.clustered, t.cdense, t.sdense, t.n_c >= 1, t.n_s >= 1,
        qlist_ok(t.rs@, t.prm@, qkey@, qgrp@, t.qrow@, t.gnames@),
        map_ok(*t, qkey@, ms@, cmd, sms@, smd, true),
        aligned_on(*t, pa, pb), 0 <= pa <= qa < qb <= pb, pb < t.n_o,
        listed_ok(*t, ms@, cmd.bs as int, lp@, vb@, qa, n as int, qb),
        k < n, ja <= jc,
        t.split_at(gap_lo(lp@, qa, k as int), jc),
        old(cnt)@.len() == t.gnames@.len() && old(sum)@.len() == t.gnames@.len()
            && old(abs)@.len() == t.gnames@.len() && old(ovf)@.len() == t.gnames@.len(),
        forall|gi: int| 0 <= gi < t.gnames@.len() ==>
            #[trigger] t.acc_ok(gi, ja as int, jc, old(cnt)@[gi], old(sum)@[gi], old(abs)@[gi], old(ovf)@[gi]),
    ensures
        jc <= b,
        t.split_at(gap_lo(lp@, qa, k as int + 1), b as int),
        final(cnt)@.len() == t.gnames@.len() && final(sum)@.len() == t.gnames@.len()
            && final(abs)@.len() == t.gnames@.len() && final(ovf)@.len() == t.gnames@.len(),
        forall|gi: int| 0 <= gi < t.gnames@.len() ==>
            #[trigger] t.acc_ok(gi, ja as int, b as int, final(cnt)@[gi], final(sum)@[gi], final(abs)@[gi], final(ovf)@[gi]),
    no_unwind
{
    let ghost rs = t.rs@;
    let ghost prm = t.prm@;
    let ghost gn = t.gnames@;
    let ghost ng = gn.len();
    let ghost cw = cmd.bs as int;
    let p = lp[k];
    let v = vb[k] as u64;
    proof {
        assert(gap_lo(lp@, qa, k as int) <= lp@[k as int] < qb);
        assert(aligned(*t, p as int));
        assert(aligned(*t, p as int + 1));
        lemma_split_aligned(*t, p as int);
        lemma_split_aligned(*t, p as int + 1);
        assert(run_l(t.lrows@, t.st@, p as int));
    }
    let a = t.st[p] as usize;
    let b = t.st[p + 1] as usize;
    proof {
        let q0 = gap_lo(lp@, qa, k as int);
        assert forall|q: int| q0 <= q < p implies #[trigger] ov(*t, ms@, cw, q) == 0 by {
            assert(gap_lo(lp@, qa, k as int) <= q < lp@[k as int]);
        }
        lemma_quiet_gap(*t, qkey@, qgrp@, ms@, cmd, sms@, smd, q0, p as int, ja as int, jc, a as int,
            old(cnt)@, old(sum)@, old(abs)@, old(ovf)@);
        assert(vb@[k as int] as u64 == ov(*t, ms@, cw, p as int));
    }
    let mut jj = a;
    while jj < b
        invariant
            t.wf(),
            qlist_ok(rs, prm, qkey@, qgrp@, t.qrow@, gn),
            map_ok(*t, qkey@, ms@, cmd, sms@, smd, true),
            t.cdense, t.sdense, t.n_s >= 1,
            rs == t.rs@, prm == t.prm@, gn == t.gnames@, ng == gn.len(),
            ja <= a <= jj <= b, b <= t.n_l, p < t.n_o,
            t.split_at(p as int, a as int), t.split_at(p as int + 1, b as int),
            v == ov(*t, ms@, cmd.bs as int, p as int),
            ng == cnt@.len() && ng == sum@.len() && ng == abs@.len() && ng == ovf@.len(),
            forall|gi: int| 0 <= gi < ng ==>
                #[trigger] t.acc_ok(gi, ja as int, jj as int, cnt@[gi], sum@[gi], abs@[gi], ovf@[gi]),
        decreases b - jj,
    {
        proof {
            assert(t.op(jj as int) >= p);
            assert(t.op(jj as int) < p + 1);
            lemma_op_key(*t, jj as int, p as int);
        }
        let (hit, g) = fast_line(t, qkey, qgrp, ms, cmd, sms, smd, jj, p, v);
        acc_line(t, cnt, sum, abs, ovf, ja, jj, hit, g);
        jj = jj + 1;
    }
    proof {
        assert(gap_lo(lp@, qa, k as int + 1) == p + 1);
    }
    b
}

/// The task on the live-order path.
pub fn scan_live(task: ScanTask) -> (out: ScanOut)
    requires
        task.pre(),
        task.ctx.clustered, task.use_map, task.ctx.cdense, task.ctx.sdense,
        task.ctx.n_c >= 1, task.ctx.n_s >= 1, task.vbuf@.len() >= 1, task.lp@.len() == task.vbuf@.len(),
        task.obuf@.len() == task.vbuf@.len(),
        aligned(task.ctx, task.pa as int), aligned(task.ctx, task.pb as int),
        task.hb@.len() == task.hg@.len(), task.cmd.p2, task.smd.p2, task.ctx.ldiv.p2,
    ensures task.post(out),
    no_unwind
{
    let ScanTask { ctx, qkey, qgrp, cm, cmd, sm, smd, use_map, vbuf, lp, obuf, hb, hg, pa, pb, cnt, sum, abs, ovf } = task;
    let t = ctx;
    let ms: &Vec<Vec<u64>> = &*cm;
    let sms: &Vec<Vec<u64>> = &*sm;
    let ghost rs = t.rs@;
    let ghost prm = t.prm@;
    let ghost gn = t.gnames@;
    let ghost ng = gn.len();
    let ghost cw = cmd.bs as int;
    let mut cnt = cnt;
    let mut sum = sum;
    let mut abs = abs;
    let mut ovf = ovf;
    let mut vbuf = vbuf;
    let mut lp = lp;
    let mut obuf = obuf;
    let mut hb = hb;
    let mut hg = hg;
    let hcap = hb.len();
    let ob = vbuf.len();
    let nl = t.n_l;
    let nc = t.n_c;
    let obs = t.odiv.bs;
    let cbs = cmd.bs;
    let lbs = t.ldiv.bs;
    let ns = t.n_s;
    let sbs = smd.bs;
    let lo = t.lo_day;
    let hi = t.hi_day;
    let ghost bs = t.odiv.bs as int;
    let ja = t.st[pa] as usize;
    let jb = t.st[pb] as usize;
    proof {
        lemma_aligned_range(t, pa as int, pb as int);
        lemma_split_aligned(t, pa as int);
        lemma_split_aligned(t, pb as int);
        lemma_st_mono(t, pa as int, pb as int);
        assert(run_l(t.lrows@, t.st@, pb as int));
        assert forall|gi: int| 0 <= gi < ng implies
            #[trigger] t.acc_ok(gi, ja as int, ja as int, cnt@[gi], sum@[gi], abs@[gi], ovf@[gi]) by {
            assert forall|m: int| #[trigger] t.lsum(gi, m, ja as int, ja as int) == 0 by {
                lemma_sum_range_empty(t.lrows@, contrib_fn(rs, prm, gkey(gn, gi), m), ja as int);
            }
        }
    }
    let mut touch: u32 = 0;
    let mut j = ja;
    let mut qa = pa;
    while qa < pb
        invariant
            t.wf(),
            qlist_ok(rs, prm, qkey@, qgrp@, t.qrow@, gn),
            map_ok(t, qkey@, ms@, cmd, sms@, smd, true),
            t.clustered, t.cdense, t.sdense, t.n_c >= 1, t.n_s >= 1,
            rs == t.rs@, prm == t.prm@, gn == t.gnames@, ng == gn.len(), cw == cmd.bs as int,
            ob == vbuf@.len(), ob == lp@.len(), ob >= 1, nl == t.n_l,
            ob == obuf@.len(), nc == t.n_c, obs == t.odiv.bs, bs == obs as int,
            hcap == hb@.len(), hb@.len() == hg@.len(), cmd.p2, smd.p2, t.ldiv.p2,
            cbs == cmd.bs, lo == t.lo_day, hi == t.hi_day, lbs == t.ldiv.bs, ns == t.n_s, sbs == smd.bs,
            pa <= qa <= pb, pb < t.n_o,
            aligned_on(t, pa as int, pb as int),
            j as int == t.st@[qa as int] as int,
            ja as int == t.st@[pa as int] as int, jb as int == t.st@[pb as int] as int,
            ja <= j,
            t.split_at(qa as int, j as int),
            ng == cnt@.len() && ng == sum@.len() && ng == abs@.len() && ng == ovf@.len(),
            forall|gi: int| 0 <= gi < ng ==>
                #[trigger] t.acc_ok(gi, ja as int, j as int, cnt@[gi], sum@[gi], abs@[gi], ovf@[gi]),
        decreases pb - qa,
    {
        // the batch: at most `ob` orders, inside the orders block of `qa` (one date and one customer key base)
        let blk = div_of(t.odiv, qa);
        proof {
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(qa as int, bs);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(qa as int, bs);
            assert(bs * blk == blk * bs) by (nonlinear_arith);
            lemma_block_index(qa as int, bs, t.od_b@.len() as int);
            lemma_block_index(qa as int, bs, t.oc_b@.len() as int);
        }
        let rem = obs - (qa - blk * obs);
        let mut qb = pb;
        if qb - qa > ob {
            qb = qa + ob;
        }
        if qb - qa > rem {
            qb = qa + rem;
        }
        let db = t.od_b[blk];
        let cb = t.oc_b[blk];
        // ---- phase 0: the map value of every order of the batch, then the live ones
        gather(Ghost(t), Ghost(qkey@), Ghost(sms@), Ghost(smd), t.od_c, t.oc_c, db, cb, lo, hi, nc, ms, cmd,
            qa, qb - qa, Ghost(blk as int), &mut obuf);
        let n = compact(Ghost(t), Ghost(ms@), Ghost(cw), &obuf, qa, qb - qa, &mut lp, &mut vbuf);
        // ---- touch: the first and last supplier code of every listed run, so the batch's misses overlap
        touch = touch ^ touch_runs(Ghost(t), t.st, t.st_n, t.ls_c, nl, &lp, n);
        // ---- phase 1: the listed orders' hit rows into hb/hg, drained into the accumulators
        let ghost mut jf: int = j as int;
        let ghost mut jc: int = j as int;
        proof {
            lemma_hits_empty(t, hb@, hg@, j as int);
        }
        let mut h: usize = 0;
        let mut k: usize = 0;
        while k < n
            invariant
                t.wf(),
                qlist_ok(rs, prm, qkey@, qgrp@, t.qrow@, gn),
                map_ok(t, qkey@, ms@, cmd, sms@, smd, true),
                t.clustered, t.cdense, t.sdense, t.n_c >= 1, t.n_s >= 1, cmd.p2, smd.p2, t.ldiv.p2,
                rs == t.rs@, prm == t.prm@, gn == t.gnames@, ng == gn.len(), cw == cmd.bs as int,
                lbs == t.ldiv.bs, ns == t.n_s, sbs == smd.bs, nl == t.n_l,
                pa <= qa < qb <= pb, pb < t.n_o,
                aligned_on(t, pa as int, pb as int),
                listed_ok(t, ms@, cw, lp@, vbuf@, qa as int, n as int, qb as int),
                k <= n, ja <= jf, jf <= jc, ja as int == t.st@[pa as int] as int,
                hcap == hb@.len(), hb@.len() == hg@.len(),
                t.split_at(gap_lo(lp@, qa as int, k as int), jc),
                hits_ok(t, hb@, hg@, h as int, jf, jc),
                ng == cnt@.len() && ng == sum@.len() && ng == abs@.len() && ng == ovf@.len(),
                forall|gi: int| 0 <= gi < ng ==>
                    #[trigger] t.acc_ok(gi, ja as int, jf, cnt@[gi], sum@[gi], abs@[gi], ovf@[gi]),
            decreases n - k,
        {
            let (k2, h2, Ghost(jc2)) = collect(Ghost(t), Ghost(qkey@), Ghost(ms@), Ghost(cmd), t.st, t.ls_c, t.ls_b,
                t.ldiv, ns, sms, smd, &lp, &vbuf, &qgrp, k, n, Ghost(qa as int), Ghost(qb as int),
                Ghost(pa as int), Ghost(pb as int), &mut hb, &mut hg, h, Ghost(jf), Ghost(jc));
            k = k2;
            h = h2;
            proof {
                jc = jc2;
            }
            if k < n {
                // order `lp[k]` does not fit the list: drain it, then take the order on the general path
                drain(Ghost(t), t.le_c, t.le_b, t.ld_c, t.ld_b, t.ldiv, &hb, &hg, h, Ghost(ja as int), Ghost(jf), Ghost(jc),
                    &mut cnt, &mut sum, &mut abs, &mut ovf);
                h = 0;
                proof {
                    jf = jc;
                    lemma_hits_empty(t, hb@, hg@, jc);
                }
                let b = slow_order(&t, &qkey, &qgrp, ms, cmd, sms, smd, &lp, &vbuf, k, n, Ghost(qa as int), Ghost(qb as int),
                    Ghost(pa as int), Ghost(pb as int), ja, Ghost(jc), &mut cnt, &mut sum, &mut abs, &mut ovf);
                proof {
                    jc = b as int;
                    jf = b as int;
                    lemma_hits_empty(t, hb@, hg@, b as int);
                }
                k = k + 1;
            }
        }
        drain(Ghost(t), t.le_c, t.le_b, t.ld_c, t.ld_b, t.ldiv, &hb, &hg, h, Ghost(ja as int), Ghost(jf), Ghost(jc),
            &mut cnt, &mut sum, &mut abs, &mut ovf);
        // ---- the dead orders after the last listed one
        let ghost qc: int = gap_lo(lp@, qa as int, n as int);
        proof {
            assert(aligned(t, qb as int));
            lemma_split_aligned(t, qb as int);
            assert(run_l(t.lrows@, t.st@, qb as int));
        }
        let e = t.st[qb] as usize;
        proof {
            assert forall|q: int| qc <= q < qb implies #[trigger] ov(t, ms@, cw, q) == 0 by {}
            lemma_quiet_gap(t, qkey@, qgrp@, ms@, cmd, sms@, smd, qc, qb as int, ja as int, jc, e as int,
                cnt@, sum@, abs@, ovf@);
        }
        j = e;
        qa = qb;
    }
    ScanOut { ja, jb, cnt, sum, abs, ovf, touch }
}

} // verus!
