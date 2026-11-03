//! The fast plan: bound sums, candidates, exact sums of the candidates.
//!
//! 1. Guards: the l_suppkey key index is a permutation (kind 2); the keys span at most `2^28` slots (`kmin` and
//!    `kmax` are the keys at the first and last index positions).
//! 2. Pass 1 (`tasks::P1Task`, one task per range of blocks, about equal estimated work each): per task and slot,
//!    the saturated bound sum (`u8`). Serial tasks (one worker) apply the units through key-range buckets, parallel
//!    tasks directly (`pass1`).
//! 3. Merge (`tasks::MTask`, one task per range of slots): per slot, the bound sum over all rows (`SAT` when a task
//!    saturated); per task a local threshold `tq` and the (few) slots at or above it.
//! 4. Candidates: `tau` is the largest local threshold, so every slot of bound sum at least `tau` is listed; the
//!    listed slots at least `tau` are the candidates, every other slot's bound sum is below `tau` (`flags[t] == 0`).
//!    When a task's list overflowed, a global histogram threshold (about `KMAX` slots) and a scan of every slot.
//! 5. Exact sums of the candidates through the key index (`tasks::XTask`); `M` is their largest.
//! 6. Check: `tau <= 1` or `(tau - 1) * 2^qs < M`. Then no other slot can reach `M`: a group's revenue is below
//!    `2^qs` times its bound sum (`lemma_bsums`). Else a second round with every slot whose bound may reach `M`.
//! 7. The hit supplier rows: the supplier key ranges of the candidates of sum `M`, as an increasing list
//!    (`supplier_hits_list`), so the emit visits only those rows instead of a flag per supplier row.
//!
//! Any failed guard or check returns `None` (the caller then takes the general plan).
//!
//! Costs (TPC-H SF100, 3-month window: ~46M rows in ~720 blocks scanned, ~22.7M qualifying): pass 1 dominates and,
//! with many workers, is bound by memory traffic from the node holding the lineitem pages; with one worker by the
//! random byte updates of the 1 MB slot array (bucketing them cut ~265-300 to ~190-220 ms). Buffers are allocated on
//! the calling thread from the heap (see `split_blocks`), and the calling thread reads only small task outputs.
use vstd::prelude::*;
use vstd::arithmetic::power2::pow2;
use std::sync::Arc;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::link::query::*;
use crate::link::expr::i128_max;
use crate::gendb_entry::parallel::{Dispatch, fork_join, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::gendb_entry::work::put;
use crate::stores::lisupp::interface::common::colfmt as lc;
use crate::stores::lisupp::interface::common::keyidx as lk;
use crate::stores::suppliers::interface::common::keyidx as sk;
use super::group::*;
use super::model::*;
use super::answer::*;
use super::emit::*;
use super::general::*;
use super::pass1::*;
use super::tasks::*;
use super::common::bits::lemma_shr_le;

verus! {

// ------------------------------------------------------------------------------------------------ specification

/// What the plans read of the stored lineitem rows.
pub open spec fn li_full(c: Li) -> bool {
    &&& li_vals_ok(c)
    &&& forall|j: int| 0 <= j < c.n ==> #[trigger] ship_v(c, j) <= c.ship_zmax@[j / c.bs as int]
    &&& lk::keyidx_ok(c.supp@, c.supp_base@, c.ic@, c.ib@, c.bs as int, c.kind, c.n as int)
}

/// A plan's outcome: every group inside `i128`, `M` the largest group sum (or no group), and the supplier rows whose
/// key is a group of sum `M` (`hits_ok`: a flag per row, or on the fast path the increasing list of those rows).
pub open spec fn plan_ok(c: Li, s: Su, lo: i64, hi: i64, m: i128, hits: Hits) -> bool {
    let g = qg(lo as int, hi as int);
    let xs = xs_of(c);
    &&& group_caps(g, xs)
    &&& is_max(g, xs, m as int) || no_groups(g, xs)
    &&& hits_ok(hits, s, g, xs, m as int)
}

/// The row ranges of block bounds.
pub open spec fn bnds_of(c: Li, gb: Seq<usize>) -> Seq<int> {
    Seq::new(gb.len(), |i: int| rs(c, gb[i] as int))
}

/// Increasing bounds from `0` to `n` in `parts` steps.
pub open spec fn splits(r: Seq<usize>, parts: int, n: int) -> bool {
    &&& r.len() == parts + 1
    &&& r[0] == 0
    &&& r[parts] == n
    &&& forall|i: int| 0 <= i < parts ==> r[i] <= #[trigger] r[i + 1]
}

/// The bound sum of slot `t` is below `tau`.
pub open spec fn small(w: Win, xs: Seq<Row>, t: int, tau: int) -> bool {
    gsum(qb(w.lo as int, w.hi as int, w.qs as nat), xs, kr(w.kmin + t), 0) < tau
}

/// The candidate flags: an unflagged slot has a bound sum below `tau`; a flagged slot is a candidate.
pub open spec fn flags_ok(flags: Seq<u8>, cand: Seq<u32>, w: Win, xs: Seq<Row>, tau: int) -> bool {
    &&& flags.len() == w.cap
    &&& forall|t: int| 0 <= t < w.cap && #[trigger] flags[t] == 0 ==> small(w, xs, t, tau)
    &&& forall|t: int| 0 <= t < w.cap && #[trigger] flags[t] != 0 ==> exists|a: int| 0 <= a < cand.len() && cand[a] == t
    &&& forall|a: int| 0 <= a < cand.len() ==> (#[trigger] cand[a] as int) < w.cap
}

/// The exact sums of the candidates.
pub open spec fn tot_ok(tot: Seq<i128>, cand: Seq<u32>, w: Win, xs: Seq<Row>) -> bool {
    &&& tot.len() == cand.len()
    &&& forall|a: int| 0 <= a < cand.len() ==> #[trigger] tot[a] == gsum(qg(w.lo as int, w.hi as int), xs, kr(w.kmin + cand[a]), 0)
}

/// Everything the final derivation needs.
pub open spec fn facts(c: Li, w: Win, flags: Seq<u8>, cand: Seq<u32>, tot: Seq<i128>, tau: int, m: int) -> bool {
    &&& kern_ok(c, w)
    &&& rows_fast(w, xs_of(c), 0, c.n as int)
    &&& flags_ok(flags, cand, w, xs_of(c), tau)
    &&& tot_ok(tot, cand, w, xs_of(c))
    &&& m >= 0
    &&& forall|a: int| 0 <= a < cand.len() ==> #[trigger] tot[a] <= m
    &&& m > 0 ==> exists|a: int| 0 <= a < cand.len() && tot[a] == m
    &&& tau >= 1
    &&& (tau - 1) * pow2(w.qs as nat) <= m
}

// ------------------------------------------------------------------------------------------------ lemmas

/// Per group: every qualifying row has a revenue in `(0, 2^42)` and a bound unit `q >= 1` with
/// `revenue < 2^qs * q`; so the count, the revenue and the bound sum bound each other.
pub proof fn lemma_bsums(w: Win, xs: Seq<Row>, k: Row, i: int)
    requires rows_fast(w, xs, 0, xs.len() as int), 0 <= i <= xs.len(), w.qs < 64,
    ensures ({
        let g = qg(w.lo as int, w.hi as int);
        let gb = qb(w.lo as int, w.hi as int, w.qs as nat);
        let s = xs.subrange(0, i);
        &&& gcount(g, s, k) <= gsum(g, s, k, 0)
        &&& gsum(g, s, k, 0) <= 0x400_0000_0000 * gcount(g, s, k)
        &&& gcount(g, s, k) <= gsum(gb, s, k, 0)
        &&& gsum(g, s, k, 0) + gcount(g, s, k) <= pow2(w.qs as nat) * gsum(gb, s, k, 0)
    }),
    decreases i,
{
    let g = qg(w.lo as int, w.hi as int);
    let gb = qb(w.lo as int, w.hi as int, w.qs as nat);
    let p = pow2(w.qs as nat) as int;
    if i == 0 {
        lemma_empty(g, xs, 0, k, 0);
        lemma_empty(gb, xs, 0, k, 0);
    } else {
        lemma_bsums(w, xs, k, i - 1);
        lemma_range_step(g, xs, 0, i - 1, k, 0);
        lemma_range_step(gb, xs, 0, i - 1, k, 0);
        let x = xs[i - 1];
        assert(hit(g, x, k) == hit(gb, x, k));
        if hit(g, x, k) {
            assert(fast_row(w.lo as int, w.hi as int, x));
            let r = rev_of(x);
            vstd::arithmetic::power2::lemma_pow2_pos(w.qs as nat);
            vstd::arithmetic::div_mod::lemma_fundamental_div_mod(r, p);
            vstd::arithmetic::div_mod::lemma_mod_pos_bound(r, p);
            let q = qv_of(x, w.qs as nat);
            assert(q == r / p + 1);
            assert(r / p >= 0) by (nonlinear_arith) requires r > 0, p > 0, r == p * (r / p) + r % p, 0 <= r % p < p;
            assert(r + 1 <= p * q) by (nonlinear_arith) requires r == p * (r / p) + r % p, 0 <= r % p < p, q == r / p + 1;
            let s0 = xs.subrange(0, i - 1);
            let (c0, a0, b0) = (gcount(g, s0, k) as int, gsum(g, s0, k, 0), gsum(gb, s0, k, 0));
            assert(a0 + c0 + r + 1 <= p * (b0 + q)) by (nonlinear_arith)
                requires a0 + c0 <= p * b0, r + 1 <= p * q;
        }
    }
}

/// The whole relation as its prefix.
pub proof fn lemma_bsums_all(w: Win, xs: Seq<Row>, k: Row)
    requires rows_fast(w, xs, 0, xs.len() as int), w.qs < 64,
    ensures ({
        let g = qg(w.lo as int, w.hi as int);
        let gb = qb(w.lo as int, w.hi as int, w.qs as nat);
        &&& gcount(g, xs, k) <= gsum(g, xs, k, 0)
        &&& gsum(g, xs, k, 0) <= 0x400_0000_0000 * gcount(g, xs, k)
        &&& gcount(g, xs, k) <= gsum(gb, xs, k, 0)
        &&& gsum(g, xs, k, 0) + gcount(g, xs, k) <= pow2(w.qs as nat) * gsum(gb, xs, k, 0)
    }),
{
    lemma_bsums(w, xs, k, xs.len() as int);
    assert(xs.subrange(0, xs.len() as int) =~= xs);
}

/// A group with a row has the key of a slot.
pub proof fn lemma_slot(c: Li, w: Win, k: Row) -> (t: int)
    requires kern_ok(c, w), gcount(qg(w.lo as int, w.hi as int), xs_of(c), k) > 0,
    ensures 0 <= t < w.cap, k == kr(w.kmin + t),
{
    let g = qg(w.lo as int, w.hi as int);
    let xs = xs_of(c);
    lemma_count_witness(g, xs, k);
    let i = choose|i: int| 0 <= i < xs.len() && #[trigger] hit(g, xs[i], k);
    lemma_hit_row(c, w.lo as int, w.hi as int, i, supp_v(c, i));
    assert(w.kmin <= supp_v(c, i) < w.kmin + w.cap);
    supp_v(c, i) - w.kmin
}

/// An unflagged slot's group, when it has a row, has a revenue below `M`.
pub proof fn lemma_unflagged(c: Li, w: Win, flags: Seq<u8>, cand: Seq<u32>, tot: Seq<i128>, tau: int, m: int, t: int)
    requires
        facts(c, w, flags, cand, tot, tau, m),
        0 <= t < w.cap,
        flags[t] == 0,
        gcount(qg(w.lo as int, w.hi as int), xs_of(c), kr(w.kmin + t)) > 0,
    ensures gsum(qg(w.lo as int, w.hi as int), xs_of(c), kr(w.kmin + t), 0) < m,
{
    let g = qg(w.lo as int, w.hi as int);
    let gb = qb(w.lo as int, w.hi as int, w.qs as nat);
    let xs = xs_of(c);
    let k = kr(w.kmin + t);
    lemma_bsums_all(w, xs, k);
    assert(small(w, xs, t, tau));
    let b = gsum(gb, xs, k, 0);
    let p = pow2(w.qs as nat) as int;
    vstd::arithmetic::power2::lemma_pow2_pos(w.qs as nat);
    assert(b <= tau - 1);
    assert(tau >= 2);
    assert(p * b <= p * (tau - 1)) by (nonlinear_arith) requires b <= tau - 1, p > 0;
    assert((tau - 1) * p == p * (tau - 1)) by (nonlinear_arith);
}

/// Every group with a row has a revenue of at most `M`.
pub proof fn lemma_all_le(c: Li, w: Win, flags: Seq<u8>, cand: Seq<u32>, tot: Seq<i128>, tau: int, m: int)
    requires facts(c, w, flags, cand, tot, tau, m),
    ensures forall|k: Row| #[trigger] gcount(qg(w.lo as int, w.hi as int), xs_of(c), k) > 0
        ==> gsum(qg(w.lo as int, w.hi as int), xs_of(c), k, 0) <= m,
{
    let g = qg(w.lo as int, w.hi as int);
    let xs = xs_of(c);
    assert forall|k: Row| #[trigger] gcount(g, xs, k) > 0 implies gsum(g, xs, k, 0) <= m by {
        let t = lemma_slot(c, w, k);
        if flags[t] == 0 {
            lemma_unflagged(c, w, flags, cand, tot, tau, m, t);
        } else {
            let a = choose|a: int| 0 <= a < cand.len() && cand[a] == t;
            assert(tot[a] <= m);
        }
    }
}

/// `M` is the largest group revenue, or there is no group.
pub proof fn lemma_max(c: Li, w: Win, flags: Seq<u8>, cand: Seq<u32>, tot: Seq<i128>, tau: int, m: int)
    requires facts(c, w, flags, cand, tot, tau, m),
    ensures
        is_max(qg(w.lo as int, w.hi as int), xs_of(c), m) || no_groups(qg(w.lo as int, w.hi as int), xs_of(c)),
        group_caps(qg(w.lo as int, w.hi as int), xs_of(c)),
{
    let g = qg(w.lo as int, w.hi as int);
    let xs = xs_of(c);
    lemma_all_le(c, w, flags, cand, tot, tau, m);
    if m > 0 {
        let a = choose|a: int| 0 <= a < cand.len() && tot[a] == m;
        let k = kr(w.kmin + cand[a]);
        lemma_bsums_all(w, xs, k);
        assert(gsum(g, xs, k, 0) == m);
        assert(gcount(g, xs, k) > 0);
        assert(is_max(g, xs, m));
    } else {
        assert forall|k: Row| #[trigger] gcount(g, xs, k) == 0 by {
            lemma_bsums_all(w, xs, k);
        }
    }
    assert forall|j: int| 0 <= j < xs.len() && qual_of(w.lo as int, w.hi as int, #[trigger] xs[j])
        implies abs(rev_of(xs[j])) <= 0x400_0000_0000 by {
        assert(fast_row(w.lo as int, w.hi as int, xs[j]));
    }
    assert(xs.len() * 0x400_0000_0000 <= i128_max()) by (nonlinear_arith) requires xs.len() <= 0x1_0000_0000_0000_0000;
    lemma_caps_bound(w.lo as int, w.hi as int, xs, 0x400_0000_0000);
}

/// The group of key `key`: without a slot, no row; an unflagged slot is not a group of sum `M`; a candidate is one
/// exactly when its exact sum is `M > 0`.
pub proof fn lemma_key_hit(c: Li, w: Win, flags: Seq<u8>, cand: Seq<u32>, tot: Seq<i128>, tau: int, m: int, key: int)
    requires facts(c, w, flags, cand, tot, tau, m),
    ensures ({
        let g = qg(w.lo as int, w.hi as int);
        let xs = xs_of(c);
        let t = key - w.kmin;
        let h = gcount(g, xs, kr(key)) > 0 && gsum(g, xs, kr(key), 0) == m;
        &&& !(0 <= t < w.cap) ==> !h
        &&& 0 <= t < w.cap && flags[t] == 0 ==> !h
        &&& forall|a: int| 0 <= a < cand.len() && cand[a] == t ==> (h == (m > 0 && #[trigger] tot[a] == m))
    }),
{
    let g = qg(w.lo as int, w.hi as int);
    let xs = xs_of(c);
    let t = key - w.kmin;
    let k = kr(key);
    lemma_bsums_all(w, xs, k);
    if gcount(g, xs, k) > 0 {
        let t2 = lemma_slot(c, w, k);
        lemma_kr_inj(key, w.kmin + t2);
        if flags[t] == 0 {
            lemma_unflagged(c, w, flags, cand, tot, tau, m, t);
        }
    }
    assert forall|a: int| 0 <= a < cand.len() && cand[a] == t implies
        ((gcount(g, xs, k) > 0 && gsum(g, xs, k, 0) == m) == (m > 0 && #[trigger] tot[a] == m)) by {
        assert(kr(w.kmin + cand[a]) == k);
    }
}

/// Block ranges cover the rows: `rs(nb) == n`.
pub proof fn lemma_rs_end(c: Li)
    requires li_shape(c),
    ensures rs(c, c.nb as int) == c.n, rs(c, 0) == 0,
{
}

/// Pass-1 outputs cover every row with the fast row fact.
pub proof fn lemma_fast_prefix(outs: Seq<P1Out>, bnds: Seq<int>, c: Li, w: Win, i: int)
    requires outs_ok(outs, bnds, c, w), 0 <= i <= outs.len(),
    ensures rows_fast(w, xs_of(c), 0, bnds[i]),
    decreases i,
{
    if i > 0 {
        lemma_fast_prefix(outs, bnds, c, w, i - 1);
        assert(outs[i - 1].ok && p1_ok(outs[i - 1], c, w, bnds[i - 1], bnds[(i - 1) + 1]));
        assert(bnds[i - 1] <= bnds[(i - 1) + 1]);
        let xs = xs_of(c);
        assert forall|j: int| 0 <= j < bnds[i] implies fast_row(w.lo as int, w.hi as int, #[trigger] xs[j]) by {
            if j < bnds[i - 1] {
            } else {
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ helpers

/// Runs the tasks: on worker threads, or in order on the calling thread when `workers == 1`.
fn run_all<T: WorkerTask>(tasks: Vec<T>, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<T::Output>, WorkerFailure>)
    requires
        tasks.len() <= MAX_WORKERS,
        forall|i: int| 0 <= i < tasks.len() ==> #[trigger] tasks@[i].pre(),
    ensures
        r matches Ok(outs) ==> outs.len() == tasks.len()
            && forall|i: int| 0 <= i < tasks.len() ==> #[trigger] tasks@[i].post(outs@[i]),
{
    if workers > 1 {
        return fork_join(dispatch, tasks);
    }
    let ghost orig = tasks@;
    let n = tasks.len();
    let mut tasks = tasks;
    let mut rev: Vec<T::Output> = Vec::new();
    while tasks.len() > 0
        invariant
            n == orig.len(),
            tasks@ == orig.subrange(0, tasks.len() as int),
            rev.len() + tasks.len() == n,
            forall|i: int| 0 <= i < orig.len() ==> #[trigger] orig[i].pre(),
            forall|k: int| 0 <= k < rev.len() ==> orig[n - 1 - k].post(#[trigger] rev@[k]),
        decreases tasks.len(),
    {
        let tk = tasks.pop().unwrap();
        let o = tk.run();
        rev.push(o);
    }
    let mut outs: Vec<T::Output> = Vec::new();
    while rev.len() > 0
        invariant
            n == orig.len(),
            outs.len() + rev.len() == n,
            forall|k: int| 0 <= k < rev.len() ==> orig[n - 1 - k].post(#[trigger] rev@[k]),
            forall|i: int| 0 <= i < outs.len() ==> orig[i].post(#[trigger] outs@[i]),
        decreases rev.len(),
    {
        let o = rev.pop().unwrap();
        outs.push(o);
    }
    proof {
        assert forall|i: int| 0 <= i < orig.len() implies #[trigger] orig[i].post(outs@[i]) by {}
    }
    Ok(outs)
}

/// `n` split into `parts` nearly equal steps.
fn split_even(n: usize, parts: usize) -> (r: Vec<usize>)
    requires 1 <= parts <= 64,
    ensures splits(r@, parts as int, n as int),
{
    let step = n / parts;
    let step = if step < usize::MAX { step + 1 } else { step };
    let mut r: Vec<usize> = Vec::new();
    r.push(0);
    let mut cur: usize = 0;
    let mut i: usize = 1;
    while i < parts
        invariant
            1 <= i <= parts,
            r@.len() == i,
            r@[0] == 0,
            r@[i - 1] == cur,
            cur <= n,
            forall|j: int| 0 <= j < i - 1 ==> r@[j] <= #[trigger] r@[j + 1],
        decreases parts - i,
    {
        cur = if n - cur > step { cur + step } else { n };
        r.push(cur);
        i = i + 1;
    }
    r.push(n);
    r
}

/// The estimated pass-1 work of block `g` (`0` when its zone misses the window), in 1/1024 of a full block: with many
/// workers the scan is bound by memory traffic, about the same for every block whose zone meets the window (the
/// columns' cache lines are read even at a low hit density), plus the share of rows whose ship date may fall in the
/// window (their bound-sum updates).
fn block_weight(c: &Li, g: usize, lo: i64, hi: i64) -> (w: u32)
    requires li_shape(*c), g < c.nb,
    ensures w <= 1024,
{
    let sb = c.ship_base[g] as i128;
    let sz = c.ship_zmax[g] as i128;
    if sb > hi as i128 || sz < lo as i128 {
        return 0;
    }
    let a = if sb > lo as i128 { sb } else { lo as i128 };
    let e = if sz < hi as i128 { sz } else { hi as i128 };
    let span = sz - sb + 1;
    if span <= 0 || e < a {
        return 1024;
    }
    let part = ((e - a + 1) * 504) / span;
    if part > 504 { 1024 } else { (520 + part) as u32 }
}

/// Block bounds of `nch` tasks with about equal estimated work each (`block_weight`); and the count of blocks whose
/// zone meets the window.
fn split_blocks(c: &Li, lo: i64, hi: i64, nch: usize) -> (r: (Vec<usize>, u64))
    requires li_shape(*c), 1 <= nch <= 64,
    ensures splits(r.0@, nch as int, c.nb as int), r.1 <= c.nb,
{
    let nb = c.nb;
    // The capacity (31 MB, just below glibc's 32 MiB cap of the dynamic mmap threshold) is deliberate: freeing this
    // first large buffer of a call raises that threshold (and the trim threshold to twice it), so the pass-1
    // accumulators that follow come from (and return to) the heap instead of fresh pages that every worker would
    // fault in again on each call.
    let mut wts: Vec<u32> = Vec::with_capacity(7_800_000);
    let mut total: u128 = 0;
    let mut live: u64 = 0;
    let mut g: usize = 0;
    while g < nb
        invariant li_shape(*c), nb == c.nb, g <= nb, wts@.len() == g, live <= g, total <= 1024 * g,
            forall|i: int| 0 <= i < g ==> #[trigger] wts@[i] <= 1024,
        decreases nb - g,
    {
        let wv = block_weight(c, g, lo, hi);
        wts.push(wv);
        total = total + wv as u128;
        if wv > 0 {
            live = live + 1;
        }
        g = g + 1;
    }
    let mut bnds: Vec<usize> = Vec::new();
    bnds.push(0);
    let mut done: u128 = 0;
    let mut g: usize = 0;
    let mut t: usize = 1;
    while t < nch
        invariant
            li_shape(*c), nb == c.nb, wts@.len() == nb,
            forall|i: int| 0 <= i < nb ==> #[trigger] wts@[i] <= 1024,
            1 <= t <= nch, nch <= 64,
            g <= nb, done <= 1024 * g, total <= 1024 * nb,
            bnds@.len() == t,
            bnds@[0] == 0,
            forall|i: int| 0 <= i < t - 1 ==> bnds@[i] <= #[trigger] bnds@[i + 1],
            forall|i: int| 0 <= i < t ==> #[trigger] bnds@[i] <= g,
        decreases nch - t,
    {
        proof {
            assert(total * t as u128 <= 1024 * 0x1_0000_0000_0000_0000 * 64) by (nonlinear_arith)
                requires total <= 1024 * 0x1_0000_0000_0000_0000, t <= 64;
        }
        let goal = (total * t as u128) / nch as u128;
        while g < nb && done < goal
            invariant
                li_shape(*c), nb == c.nb, wts@.len() == nb,
                forall|i: int| 0 <= i < nb ==> #[trigger] wts@[i] <= 1024,
                g <= nb, done <= 1024 * g,
                bnds@.len() == t,
                forall|i: int| 0 <= i < t ==> #[trigger] bnds@[i] <= g,
            decreases nb - g,
        {
            done = done + wts[g] as u128;
            g = g + 1;
        }
        bnds.push(g);
        t = t + 1;
    }
    bnds.push(nb);
    (bnds, live)
}

/// The key at index position `p`.
fn key_pos(c: &Li, bs: usize, p: usize) -> (k: i128)
    requires li_full(*c), c.kind == 2, bs as int == c.bs as int, p < c.n,
    ensures k == lk::fkey(c.supp@, c.supp_base@, bs as int, lk::irow(2, c.ic@, c.ib@, bs as int, p as int)),
{
    proof {
        lk::lemma_irow_bound(c.supp@, c.supp_base@, c.ic@, c.ib@, bs as int, 2, c.n as int, p as int);
        crate::stores::lisupp::interface::common::read::lemma_div_lt(p as int, bs as int, c.ib@.len() as int);
    }
    let j = (c.ib[p / bs] as u128 + c.ic[p] as u128) as usize;
    let (k, _, _, _) = row_vals(c, j);
    k
}

/// Every stored key lies between the keys at the first and last index positions.
proof fn lemma_keys_range(c: Li, bs: int, kmin: int, kmax: int)
    requires
        li_full(c), c.kind == 2, bs == c.bs as int, c.n >= 1,
        kmin == lk::fkey(c.supp@, c.supp_base@, bs, lk::irow(2, c.ic@, c.ib@, bs, 0)),
        kmax == lk::fkey(c.supp@, c.supp_base@, bs, lk::irow(2, c.ic@, c.ib@, bs, c.n - 1)),
    ensures forall|j: int| 0 <= j < c.n ==> kmin <= #[trigger] supp_v(c, j) <= kmax,
{
    let n = c.n as int;
    let m = lk::idx_map(c.ic@, c.ib@, bs, n);
    assert forall|j: int| 0 <= j < n implies kmin <= #[trigger] supp_v(c, j) <= kmax by {
        assert(lc::covered(m, j));
        let p = choose|p: int| 0 <= p < m.len() && m[p] == j;
        lk::lemma_sorted_le(c.supp@, c.supp_base@, c.ic@, c.ib@, bs, 2, n, 0, p);
        lk::lemma_sorted_le(c.supp@, c.supp_base@, c.ic@, c.ib@, bs, 2, n, p, n - 1);
        assert(lk::irow(2, c.ic@, c.ib@, bs, p) == j);
    }
}

/// The position of slot `t` among the candidates, when found.
fn find_cand(cand: &Arc<Vec<u32>>, t: u32) -> (r: Option<usize>)
    ensures r matches Some(a) ==> a < cand@.len() && cand@[a as int] == t,
{
    let mut lo: usize = 0;
    let mut hi: usize = cand.len();
    while lo < hi
        invariant lo <= hi <= cand@.len(),
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        if cand[mid] < t {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }
    if lo < cand.len() && cand[lo] == t { Some(lo) } else { None }
}

// ------------------------------------------------------------------------------------------------ stages

/// Candidates kept by the threshold (about).
pub const KMAX: u64 = 64;

/// Guards and the window: the slots, the bound unit and the block bounds of the pass-1 tasks.
fn prepare(c: &Li, lo: i64, hi: i64, nch: usize) -> (r: Option<(Win, Vec<usize>, usize, u128)>)
    requires li_full(*c), 1 <= nch <= 64,
    ensures r matches Some(t) ==> {
        &&& kern_ok(*c, t.0)
        &&& t.0.lo == lo && t.0.hi == hi
        &&& t.0.qs <= 40
        &&& 1 <= t.0.cap <= 0x1000_0000
        &&& splits(t.1@, nch as int, c.nb as int)
        &&& t.2 as int == c.bs as int
        &&& c.kind == 2
        &&& lk::keyidx_ok(c.supp@, c.supp_base@, c.ic@, c.ib@, t.2 as int, 2, c.n as int)
        &&& t.3 == pow2(t.0.qs as nat) && t.3 <= 0x100_0000_0000
    },
{
    if c.kind != 2 || c.n == 0 || c.bs > 0x1_0000_0000 || c.bs > usize::MAX as u64 {
        return None;
    }
    let bs = c.bs as usize;
    let kmin = key_pos(c, bs, 0);
    let kmax = key_pos(c, bs, c.n - 1);
    if !(-0x4000_0000_0000_0000 <= kmin && kmin <= 0x4000_0000_0000_0000 && kmin <= kmax && kmax - kmin < 0x1000_0000) {
        return None;
    }
    proof {
        lemma_keys_range(*c, bs as int, kmin as int, kmax as int);
    }
    let cap = (kmax - kmin + 1) as usize;
    let (gb, total) = split_blocks(c, lo, hi, nch);
    // the bound unit: about 16 units per key and chunk at an average revenue of 2.2e8
    proof {
        assert(total as u128 * c.bs as u128 <= 0x1_0000_0000_0000_0000 * 0x1_0000_0000) by (nonlinear_arith)
            requires total <= 0x1_0000_0000_0000_0000, c.bs <= 0x1_0000_0000;
    }
    let rows_chunk: u128 = (total as u128 * c.bs as u128) / nch as u128;
    let mut qs: u64 = 0;
    let mut p2: u128 = 1;
    proof {
        vstd::arithmetic::power2::lemma2_to64();
    }
    proof {
        assert(p2 * 16 * (cap as u128) <= 0x100_0000_0000 * 16 * 0x1000_0000) by (nonlinear_arith)
            requires p2 <= 0x100_0000_0000, cap <= 0x1000_0000;
    }
    while qs < 40 && p2 * 16 * (cap as u128) < rows_chunk * 220_000_000
        invariant
            p2 * 16 * (cap as u128) <= 0x100_0000_0000 * 16 * 0x1000_0000,
            qs <= 40,
            p2 == pow2(qs as nat),
            p2 <= 0x100_0000_0000,
            cap <= 0x1000_0000,
            rows_chunk <= 0x1_0000_0000_0000_0000_0000_0000,
        decreases 40 - qs,
    {
        proof {
            vstd::arithmetic::power2::lemma_pow2_unfold((qs + 1) as nat);
            if qs + 1 < 40 {
                vstd::arithmetic::power2::lemma_pow2_strictly_increases((qs + 1) as nat, 40);
            }
            vstd::arithmetic::power2::lemma2_to64_rest();
        }
        p2 = p2 * 2;
        qs = qs + 1;
        proof {
            assert(p2 * 16 * (cap as u128) <= 0x100_0000_0000 * 16 * 0x1000_0000) by (nonlinear_arith)
                requires p2 <= 0x100_0000_0000, cap <= 0x1000_0000;
        }
    }
    let w = Win { lo, hi, kmin: kmin as i64, cap, qs };
    Some((w, gb, bs, p2))
}

/// Pass 1: the saturated bound sums of the chunks; `None` when a chunk's guard failed.
fn pass1(c: &Li, w: Win, gb: &Vec<usize>, nch: usize, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<Option<Vec<P1Out>>, WorkerFailure>)
    requires
        kern_ok(*c, w),
        w.cap <= 0x1000_0000,
        splits(gb@, nch as int, c.nb as int),
        1 <= workers <= MAX_WORKERS,
        1 <= nch <= 64,
    ensures r matches Ok(Some(outs)) ==> outs@.len() == nch && outs_ok(outs@, bnds_of(*c, gb@), *c, w),
{
    // Buckets of `2^sh` slots, at most 64 (16 KB of slot bytes each for a million slots). Serial tasks (one worker)
    // collect `BCAP` entries per bucket before applying them, so the slot bytes they touch stay in cache: measured
    // 260-290 -> ~190 ms at one worker. Parallel tasks apply every unit directly: their buffers would be zeroed on
    // the calling thread, which costs more than it saves (measured).
    let mut sh: u32 = 0;
    while sh < 24 && (w.cap >> sh) >= 64
        invariant sh <= 24,
        decreases 24 - sh,
    {
        sh = sh + 1;
    }
    proof {
        lemma_shr_le(w.cap as u64, sh as u64);
    }
    let nbk: usize = ((w.cap as u64 >> sh as u64) + 1) as usize;
    let bcap: usize = if workers == 1 && nbk <= 64 { BCAP } else { 0 };
    proof {
        assert(nbk * bcap <= 64 * 2048) by (nonlinear_arith) requires bcap == 0 || (nbk <= 64 && bcap == 2048);
    }
    let mut tasks: Vec<P1Task> = Vec::new();
    let mut t: usize = 0;
    while t < nch
        invariant
            kern_ok(*c, w),
            splits(gb@, nch as int, c.nb as int),
            1 <= nch <= 64,
            t <= nch,
            nbk * bcap <= 64 * 2048,
            tasks@.len() == t,
            forall|i: int| 0 <= i < t ==> (#[trigger] tasks@[i]).pre() && tasks@[i].c == *c && tasks@[i].w == w
                && tasks@[i].g_lo == gb@[i] && tasks@[i].g_hi == gb@[i + 1],
        decreases nch - t,
    {
        proof {
            assert(gb@[t as int] <= gb@[t + 1]);
            assert(gb@[t + 1] <= c.nb) by {
                lemma_splits_le(gb@, nch as int, c.nb as int, t + 1);
            }
        }
        // one byte per slot, zeroed on the calling thread (heap memory reused across calls, see `split_blocks`)
        let acc: Vec<u8> = vec![0u8; w.cap];
        let buf: Vec<u32> = vec![0u32; nbk * bcap];
        let cnt: Vec<usize> = vec![0usize; nbk];
        tasks.push(P1Task { c: *c, w, g_lo: gb[t], g_hi: gb[t + 1], acc, buf, cnt, sh, bcap });
        t = t + 1;
    }
    let ghost tv = tasks@;
    let outs = match run_all(tasks, workers, dispatch) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    let mut i: usize = 0;
    while i < nch
        invariant
            outs@.len() == nch,
            i <= nch,
            forall|i2: int| 0 <= i2 < i ==> (#[trigger] outs@[i2]).ok,
        decreases nch - i,
    {
        if !outs[i].ok {
            return Ok(None);
        }
        i = i + 1;
    }
    proof {
        let bn = bnds_of(*c, gb@);
        lemma_rs_end(*c);
        assert forall|i2: int| 0 <= i2 < nch implies bn[i2] <= #[trigger] bn[i2 + 1] by {
            assert(gb@[i2] <= gb@[i2 + 1]);
            lemma_rs_mono(*c, gb@[i2] as int, gb@[i2 + 1] as int);
        }
        assert forall|i2: int| 0 <= i2 < nch implies (#[trigger] outs@[i2]).ok && p1_ok(outs@[i2], *c, w, bn[i2], bn[i2 + 1]) by {
            assert(tv[i2].post(outs@[i2]));
        }
    }
    Ok(Some(outs))
}

/// Split bounds stay below the end.
pub proof fn lemma_splits_le(r: Seq<usize>, parts: int, n: int, i: int)
    requires splits(r, parts, n), 0 <= i <= parts,
    ensures r[i] <= n,
    decreases parts - i,
{
    if i < parts {
        lemma_splits_le(r, parts, n, i + 1);
    }
}

/// The merged bound sums of every slot, per merge task; the threshold `tau`.
fn merge(c: &Li, w: Win, outs: Vec<P1Out>, gb: Ghost<Seq<usize>>, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<(Vec<MOut>, Vec<usize>), WorkerFailure>)
    requires
        kern_ok(*c, w),
        1 <= outs@.len() <= 64,
        outs_ok(outs@, bnds_of(*c, gb@), *c, w),
        1 <= workers <= MAX_WORKERS,
    ensures r matches Ok(t) ==> merged_ok(*c, w, t.0@, t.1@),
{
    // one task per worker (at most 16: measured faster than 32, less to allocate and join); serially, 64 tasks keep
    // each task's slots (`u`) cache-resident
    let nm: usize = if workers == 1 { 64 } else if workers > 16 { 16 } else { workers };
    let tb = split_even(w.cap, nm);
    // local candidates per merge task: about 64 (serially) to 256 listed slots in all
    let lk: usize = if nm > 32 { 2 } else { LK };
    let nt = outs.len();
    let shared = Arc::new(outs);
    let mut tasks: Vec<MTask> = Vec::new();
    let mut k: usize = 0;
    while k < nm
        invariant
            kern_ok(*c, w),
            1 <= nm <= 64,
            shared@ == outs@,
            nt == outs@.len(),
            1 <= nt <= 64,
            outs_ok(outs@, bnds_of(*c, gb@), *c, w),
            splits(tb@, nm as int, w.cap as int),
            lk <= LK,
            k <= nm,
            tasks@.len() == k,
            forall|i: int| 0 <= i < k ==> (#[trigger] tasks@[i]).pre() && tasks@[i].w == w && tasks@[i].c@ == *c
                && tasks@[i].t_lo == tb@[i] && tasks@[i].t_hi == tb@[i + 1],
        decreases nm - k,
    {
        proof {
            assert(tb@[k as int] <= tb@[k + 1]);
            lemma_splits_le(tb@, nm as int, w.cap as int, k + 1);
        }
        let a = tb[k];
        let b = tb[k + 1];
        let u: Vec<u16> = vec![0u16; b - a];
        let hist: Vec<u32> = vec![0u32; HB + 1];
        let top: Vec<u32> = vec![0u32; lk];
        tasks.push(MTask { outs: shared.clone(), nt, w, t_lo: a, t_hi: b, u, hist, top, bnds: Ghost(bnds_of(*c, gb@)), c: Ghost(*c) });
        k = k + 1;
    }
    let ghost tv = tasks@;
    let mouts = match run_all(tasks, workers, dispatch) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    proof {
        assert forall|k2: int| 0 <= k2 < nm implies (#[trigger] mouts@[k2]).u@.len() == tb@[k2 + 1] - tb@[k2] && mouts@[k2].hist@.len() == HB + 1
            && local_ok(mouts@[k2], tb@[k2] as int, tb@[k2 + 1] as int) by {
            assert(tv[k2].post(mouts@[k2]));
        }
        assert forall|k2: int, t2: int| 0 <= k2 < nm && tb@[k2] <= t2 < tb@[k2 + 1]
            implies u_ok(#[trigger] mouts@[k2].u@[t2 - tb@[k2]], w, xs_of(*c), t2) by {
            assert(tv[k2].post(mouts@[k2]));
        }
    }
    Ok((mouts, tb))
}

/// The merge outputs: per merge task `k` the slots `[tb[k], tb[k + 1])`, their merged cells and local candidates.
pub open spec fn merged_ok(c: Li, w: Win, mouts: Seq<MOut>, tb: Seq<usize>) -> bool {
    let nm = mouts.len() as int;
    &&& 1 <= nm <= 64
    &&& splits(tb, nm, w.cap as int)
    &&& forall|k: int| 0 <= k < nm ==> (#[trigger] mouts[k]).u@.len() == tb[k + 1] - tb[k]
            && mouts[k].hist@.len() == HB + 1 && local_ok(mouts[k], tb[k] as int, tb[k + 1] as int)
    &&& forall|k: int, t2: int| 0 <= k < nm && tb[k] <= t2 < tb[k + 1]
            ==> u_ok(#[trigger] mouts[k].u@[t2 - tb[k]], w, xs_of(c), t2)
}

/// The global threshold from the merged histograms: the largest `tau` whose slots of bound sum at least `tau` would
/// exceed `KMAX`, plus one (a heuristic; the fallback when some merge task's local candidates overflowed).
fn global_threshold(mouts: &Vec<MOut>) -> (tau: usize)
    requires
        mouts@.len() <= 64,
        forall|k: int| 0 <= k < mouts@.len() ==> (#[trigger] mouts@[k]).hist@.len() == HB + 1,
    ensures 1 <= tau <= HB + 1,
{
    let hsum = hist_sum(mouts);
    let mut tau: usize = HB + 1;
    let mut cnt: u64 = 0;
    let mut go = true;
    while go && tau > 1
        invariant
            1 <= tau <= HB + 1,
            cnt <= KMAX,
            hsum@.len() == HB + 1,
            forall|b: int| 0 <= b <= HB ==> #[trigger] hsum@[b] <= 0x40_0000_0000,
        decreases tau, (go as int),
    {
        let h = hsum[tau - 1];
        if cnt + h > KMAX {
            go = false;
        } else {
            cnt = cnt + h;
            tau = tau - 1;
        }
    }
    tau
}

/// The candidates from the merge tasks' local lists (`None` when some list overflowed): `tau` is the largest local
/// threshold, so every slot of bound sum at least `tau` is listed; the listed slots with a cell at least `tau` are
/// the candidates (in slot order) and are flagged.
fn local_candidates(c: &Li, w: Win, mouts: &Vec<MOut>, tb: &Vec<usize>) -> (r: Option<(Vec<u8>, Vec<u32>, usize)>)
    requires
        kern_ok(*c, w),
        w.cap <= 0x1000_0000,
        merged_ok(*c, w, mouts@, tb@),
    ensures r matches Some(t) ==> 1 <= t.2 <= HB + 1 && flags_ok(t.0@, t.1@, w, xs_of(*c), t.2 as int),
{
    let ghost xs = xs_of(*c);
    let nm = mouts.len();
    let mut tau: usize = 1;
    let mut k: usize = 0;
    while k < nm
        invariant
            nm == mouts@.len(),
            merged_ok(*c, w, mouts@, tb@),
            k <= nm,
            1 <= tau <= HB + 1,
            forall|k2: int| 0 <= k2 < k ==> (#[trigger] mouts@[k2]).ok && mouts@[k2].tq <= tau,
        decreases nm - k,
    {
        if !mouts[k].ok {
            return None;
        }
        proof {
            assert(local_ok(mouts@[k as int], tb@[k as int] as int, tb@[k + 1] as int));
        }
        if mouts[k].tq > tau {
            tau = mouts[k].tq;
        }
        k = k + 1;
    }
    let mut flags: Vec<u8> = vec![0u8; w.cap];
    let mut cand: Vec<u32> = Vec::new();
    let mut k: usize = 0;
    while k < nm
        invariant
            nm == mouts@.len(),
            merged_ok(*c, w, mouts@, tb@),
            xs == xs_of(*c),
            w.cap <= 0x1000_0000,
            1 <= tau <= HB + 1,
            forall|k2: int| 0 <= k2 < nm ==> (#[trigger] mouts@[k2]).ok && mouts@[k2].tq <= tau,
            k <= nm,
            flags@.len() == w.cap,
            forall|t: int| 0 <= t < tb@[k as int] && #[trigger] flags@[t] == 0 ==> small(w, xs, t, tau as int),
            forall|t: int| 0 <= t < w.cap && #[trigger] flags@[t] != 0 ==> exists|a: int| 0 <= a < cand@.len() && cand@[a] == t,
            forall|a: int| 0 <= a < cand@.len() ==> (#[trigger] cand@[a] as int) < w.cap,
        decreases nm - k,
    {
        let o: &MOut = &mouts[k];
        let a0 = tb[k];
        let ghost t1 = tb@[k + 1] as int;
        proof {
            assert(tb@[k as int] <= tb@[k + 1]);
            lemma_splits_le(tb@, nm as int, w.cap as int, k + 1);
            assert(local_ok(*o, a0 as int, t1));
            assert forall|t: int| a0 <= t < t1 && !listed(o.top@, o.ntop as int, t) implies small(w, xs, t, tau as int) by {
                assert(u_ok(mouts@[k as int].u@[t - tb@[k as int]], w, xs, t));
                assert(o.u@[t - a0] < o.tq);
            }
        }
        let mut i: usize = 0;
        while i < o.ntop
            invariant
                nm == mouts@.len(),
                merged_ok(*c, w, mouts@, tb@),
                xs == xs_of(*c),
                w.cap <= 0x1000_0000,
                1 <= tau <= HB + 1,
                k < nm,
                *o == mouts@[k as int],
                a0 == tb@[k as int],
                t1 == tb@[k + 1],
                a0 <= t1 <= w.cap,
                local_ok(*o, a0 as int, t1),
                i <= o.ntop,
                flags@.len() == w.cap,
                forall|t: int| 0 <= t < a0 && #[trigger] flags@[t] == 0 ==> small(w, xs, t, tau as int),
                forall|t: int| a0 <= t < t1 && #[trigger] flags@[t] == 0
                    ==> small(w, xs, t, tau as int) || exists|i2: int| i <= i2 < o.ntop && o.top@[i2] == t,
                forall|t: int| 0 <= t < w.cap && #[trigger] flags@[t] != 0 ==> exists|a: int| 0 <= a < cand@.len() && cand@[a] == t,
                forall|a: int| 0 <= a < cand@.len() ==> (#[trigger] cand@[a] as int) < w.cap,
            decreases o.ntop - i,
        {
            let t = o.top[i] as usize;
            proof {
                assert(a0 <= o.top@[i as int] < t1);
                assert(u_ok(mouts@[k as int].u@[t - tb@[k as int]], w, xs, t as int));
            }
            let v = o.u[t - a0];
            let ghost f0 = flags@;
            let ghost c0 = cand@;
            if v as usize >= tau {
                cand.push(t as u32);
                put(&mut flags, t, 1);
                proof {
                    assert(cand@[c0.len() as int] == t);
                    assert forall|t3: int| 0 <= t3 < w.cap && #[trigger] flags@[t3] != 0 implies exists|a: int| 0 <= a < cand@.len() && cand@[a] == t3 by {
                        if t3 != t {
                            let a = choose|a: int| 0 <= a < c0.len() && c0[a] == t3;
                            assert(cand@[a] == t3);
                        }
                    }
                }
            } else {
                proof {
                    assert(v != SAT);
                    assert(small(w, xs, t as int, tau as int));
                }
            }
            proof {
                assert forall|t3: int| a0 <= t3 < t1 && #[trigger] flags@[t3] == 0
                    implies small(w, xs, t3, tau as int) || exists|i2: int| i + 1 <= i2 < o.ntop && o.top@[i2] == t3 by {
                    assert(f0[t3] == 0);
                    if !small(w, xs, t3, tau as int) {
                        let i2 = choose|i2: int| i <= i2 < o.ntop && o.top@[i2] == t3;
                        if i2 == i {
                            assert(t3 == t);
                        } else {
                            assert(i + 1 <= i2);
                        }
                    }
                }
            }
            i = i + 1;
        }
        k = k + 1;
    }
    proof {
        lemma_splits_le(tb@, nm as int, w.cap as int, nm as int);
    }
    Some((flags, cand, tau))
}

/// Adds one histogram into the running bucket sums (a function of its own so the two buffers are distinct
/// parameters and the loop vectorizes).
fn add_hist(h: &mut Vec<u64>, hk: &Vec<u32>, Ghost(k): Ghost<int>)
    requires
        0 <= k < 64,
        old(h)@.len() == HB + 1,
        hk@.len() == HB + 1,
        forall|b: int| 0 <= b <= HB ==> #[trigger] old(h)@[b] <= k * 0x1_0000_0000,
    ensures
        final(h)@.len() == HB + 1,
        forall|b: int| 0 <= b <= HB ==> #[trigger] final(h)@[b] <= (k + 1) * 0x1_0000_0000,
{
    // always true; checked once so no element access needs its own check
    if h.len() <= HB || hk.len() <= HB {
        return;
    }
    let mut b: usize = 0;
    while b <= HB
        invariant
            0 <= k < 64,
            hk@.len() == HB + 1,
            b <= HB + 1,
            h@.len() == HB + 1,
            forall|b2: int| 0 <= b2 < b ==> #[trigger] h@[b2] <= (k + 1) * 0x1_0000_0000,
            forall|b2: int| b <= b2 <= HB ==> #[trigger] h@[b2] <= k * 0x1_0000_0000,
        decreases HB + 1 - b,
    {
        proof {
            assert(h@[b as int] <= k * 0x1_0000_0000);
            assert(k * 0x1_0000_0000 <= 63 * 0x1_0000_0000) by (nonlinear_arith) requires k <= 63;
        }
        h[b] = h[b] + hk[b] as u64;
        b = b + 1;
    }
}

/// The merge tasks' histograms added bucket by bucket.
fn hist_sum(mouts: &Vec<MOut>) -> (h: Vec<u64>)
    requires
        mouts@.len() <= 64,
        forall|k: int| 0 <= k < mouts@.len() ==> (#[trigger] mouts@[k]).hist@.len() == HB + 1,
    ensures
        h@.len() == HB + 1,
        forall|b: int| 0 <= b <= HB ==> #[trigger] h@[b] <= 0x40_0000_0000,
{
    let mut h: Vec<u64> = vec![0u64; HB + 1];
    proof {
        assert forall|b: int| 0 <= b <= HB implies #[trigger] h@[b] <= 0 by {}
    }
    let mut k: usize = 0;
    while k < mouts.len()
        invariant
            mouts@.len() <= 64,
            forall|k2: int| 0 <= k2 < mouts@.len() ==> (#[trigger] mouts@[k2]).hist@.len() == HB + 1,
            k <= mouts@.len(),
            h@.len() == HB + 1,
            forall|b: int| 0 <= b <= HB ==> #[trigger] h@[b] <= k * 0x1_0000_0000,
        decreases mouts@.len() - k,
    {
        add_hist(&mut h, &mouts[k].hist, Ghost(k as int));
        k = k + 1;
    }
    proof {
        assert forall|b: int| 0 <= b <= HB implies #[trigger] h@[b] <= 0x40_0000_0000 by {
            assert(mouts@.len() * 0x1_0000_0000 <= 64 * 0x1_0000_0000) by (nonlinear_arith) requires mouts@.len() <= 64;
        }
    }
    h
}

/// The candidates (in slot order) and their flags.
fn candidates(c: &Li, w: Win, mouts: &Vec<MOut>, tb: &Vec<usize>, tau: usize) -> (r: (Vec<u8>, Vec<u32>))
    requires
        kern_ok(*c, w),
        w.cap <= 0x1000_0000,
        1 <= mouts@.len() <= 64,
        splits(tb@, mouts@.len() as int, w.cap as int),
        1 <= tau <= SAT,
        forall|k: int| 0 <= k < mouts@.len() ==> (#[trigger] mouts@[k]).u@.len() == tb@[k + 1] - tb@[k],
        forall|k: int, t2: int| 0 <= k < mouts@.len() && tb@[k] <= t2 < tb@[k + 1]
            ==> u_ok(#[trigger] mouts@[k].u@[t2 - tb@[k]], w, xs_of(*c), t2),
    ensures flags_ok(r.0@, r.1@, w, xs_of(*c), tau as int),
{
    let ghost xs = xs_of(*c);
    let nm = mouts.len();
    let mut flags: Vec<u8> = vec![0u8; w.cap];
    let mut cand: Vec<u32> = Vec::new();
    let mut k: usize = 0;
    while k < nm
        invariant
            nm == mouts@.len(), 1 <= nm <= 64,
            w.cap <= 0x1000_0000,
            splits(tb@, nm as int, w.cap as int),
            1 <= tau <= SAT,
            forall|k2: int| 0 <= k2 < nm ==> (#[trigger] mouts@[k2]).u@.len() == tb@[k2 + 1] - tb@[k2],
            forall|k2: int, t2: int| 0 <= k2 < nm && tb@[k2] <= t2 < tb@[k2 + 1]
                ==> u_ok(#[trigger] mouts@[k2].u@[t2 - tb@[k2]], w, xs, t2),
            k <= nm,
            flags@.len() == w.cap,
            forall|t: int| 0 <= t < tb@[k as int] && #[trigger] flags@[t] == 0 ==> small(w, xs, t, tau as int),
            forall|t: int| 0 <= t < w.cap && #[trigger] flags@[t] != 0 ==> exists|a: int| 0 <= a < cand@.len() && cand@[a] == t,
            forall|a: int| 0 <= a < cand@.len() ==> (#[trigger] cand@[a] as int) < w.cap,
        decreases nm - k,
    {
        let a0 = tb[k];
        let u: &Vec<u16> = &mouts[k].u;
        proof {
            assert(tb@[k as int] <= tb@[k + 1]);
            lemma_splits_le(tb@, nm as int, w.cap as int, k + 1);
        }
        let mut x: usize = 0;
        while x < u.len()
            invariant
                nm == mouts@.len(), 1 <= nm <= 64,
                k < nm,
                w.cap <= 0x1000_0000,
                a0 == tb@[k as int],
                tb@[k as int] <= tb@[k + 1] <= w.cap,
                u@ == mouts@[k as int].u@,
                u@.len() == tb@[k + 1] - tb@[k as int],
                1 <= tau <= SAT,
                forall|t2: int| tb@[k as int] <= t2 < tb@[k + 1] ==> u_ok(#[trigger] u@[t2 - a0], w, xs, t2),
                x <= u@.len(),
                flags@.len() == w.cap,
                forall|t: int| 0 <= t < a0 + x && #[trigger] flags@[t] == 0 ==> small(w, xs, t, tau as int),
                forall|t: int| 0 <= t < w.cap && #[trigger] flags@[t] != 0 ==> exists|a: int| 0 <= a < cand@.len() && cand@[a] == t,
                forall|a: int| 0 <= a < cand@.len() ==> (#[trigger] cand@[a] as int) < w.cap,
            decreases u@.len() - x,
        {
            let v = u[x];
            let t = a0 + x;
            proof {
                assert(u_ok(u@[t - a0], w, xs, t as int));
            }
            if v as usize >= tau {
                let ghost c0 = cand@;
                cand.push(t as u32);
                put(&mut flags, t, 1);
                proof {
                    assert(cand@[c0.len() as int] == t);
                    assert forall|t3: int| 0 <= t3 < w.cap && #[trigger] flags@[t3] != 0 implies exists|a: int| 0 <= a < cand@.len() && cand@[a] == t3 by {
                        if t3 != t {
                            let a = choose|a: int| 0 <= a < c0.len() && c0[a] == t3;
                            assert(cand@[a] == t3);
                        }
                    }
                }
            } else {
                proof {
                    assert(v != SAT);
                }
            }
            x = x + 1;
        }
        k = k + 1;
    }
    (flags, cand)
}

/// The exact sums of the candidates.
fn exact(c: &Li, w: Win, bs: usize, cand: Vec<u32>, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<(Arc<Vec<u32>>, Vec<i128>), WorkerFailure>)
    requires
        ix_ok(*c, w, bs),
        forall|a: int| 0 <= a < cand@.len() ==> (#[trigger] cand@[a] as int) < w.cap,
        1 <= workers <= MAX_WORKERS,
    ensures r matches Ok(t) ==> t.0@ == cand@ && tot_ok(t.1@, t.0@, w, xs_of(*c)),
{
    let nc = cand.len();
    let nx: usize = if workers > 1 && nc >= 32 { if workers < 16 { workers } else { 16 } } else { 1 };
    let cb = split_even(nc, nx);
    let ghost cv = cand@;
    let shared = Arc::new(cand);
    let mut tasks: Vec<XTask> = Vec::new();
    let mut k: usize = 0;
    while k < nx
        invariant
            ix_ok(*c, w, bs),
            shared@ == cv,
            nc == cv.len(),
            forall|a: int| 0 <= a < cv.len() ==> (#[trigger] cv[a] as int) < w.cap,
            1 <= nx <= 32,
            splits(cb@, nx as int, nc as int),
            k <= nx,
            tasks@.len() == k,
            forall|i: int| 0 <= i < k ==> (#[trigger] tasks@[i]).pre() && tasks@[i].c == *c && tasks@[i].w == w
                && tasks@[i].cand@ == cv && tasks@[i].c_lo == cb@[i] && tasks@[i].c_hi == cb@[i + 1],
        decreases nx - k,
    {
        proof {
            assert(cb@[k as int] <= cb@[k + 1]);
            lemma_splits_le(cb@, nx as int, nc as int, k + 1);
        }
        let a = cb[k];
        let b = cb[k + 1];
        let ex: Vec<i128> = vec![0i128; b - a];
        tasks.push(XTask { c: *c, w, bs, cand: shared.clone(), c_lo: a, c_hi: b, ex });
        k = k + 1;
    }
    let ghost tv = tasks@;
    let xouts = match run_all(tasks, workers, dispatch) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    let ghost g = qg(w.lo as int, w.hi as int);
    let ghost xs = xs_of(*c);
    let mut tot: Vec<i128> = Vec::new();
    let mut k: usize = 0;
    while k < nx
        invariant
            g == qg(w.lo as int, w.hi as int),
            xs == xs_of(*c),
            1 <= nx <= 32,
            xouts@.len() == nx,
            tv.len() == nx,
            splits(cb@, nx as int, nc as int),
            nc == cv.len(),
            forall|i: int| 0 <= i < nx ==> (#[trigger] tv[i]).post(xouts@[i]) && tv[i].c == *c && tv[i].w == w
                && tv[i].cand@ == cv && tv[i].c_lo == cb@[i] && tv[i].c_hi == cb@[i + 1],
            k <= nx,
            tot@.len() == cb@[k as int],
            tot@.len() <= nc,
            forall|a: int| 0 <= a < tot@.len() ==> #[trigger] tot@[a] == gsum(g, xs, kr(w.kmin + cv[a]), 0),
        decreases nx - k,
    {
        let ex: &Vec<i128> = &xouts[k].ex;
        let a0 = cb[k];
        proof {
            assert(tv[k as int].post(xouts@[k as int]));
            assert(cb@[k as int] <= cb@[k + 1]);
            lemma_splits_le(cb@, nx as int, nc as int, k + 1);
            assert forall|i: int| a0 <= i < cb@[k + 1] implies #[trigger] ex@[i - a0] == gsum(g, xs, kr(w.kmin + cv[i]), 0) by {
                let tk = tv[k as int];
                assert(tk.post(xouts@[k as int]));
                assert(tk.c_lo <= i < tk.c_hi);
                assert(xouts@[k as int].ex@[i - tk.c_lo] == gsum(qg(tk.w.lo as int, tk.w.hi as int),
                    xs_of(tk.c), kr(tk.w.kmin + tk.cand@[i]), 0));
                assert(ex@ == xouts@[k as int].ex@);
                assert(tk.w == w && tk.c == *c && tk.cand@ == cv);
                assert(tk.c_lo == a0);
                assert(ex@[i - a0] == xouts@[k as int].ex@[i - tk.c_lo]);
                assert(g == qg(tk.w.lo as int, tk.w.hi as int));
                assert(xs == xs_of(tk.c));
                assert(kr(w.kmin + cv[i]) == kr(tk.w.kmin + tk.cand@[i]));
            }
        }
        let mut x: usize = 0;
        while x < ex.len()
            invariant
                g == qg(w.lo as int, w.hi as int),
                xs == xs_of(*c),
                k < nx,
                splits(cb@, nx as int, nc as int),
                ex@.len() == cb@[k + 1] - cb@[k as int],
                a0 == cb@[k as int],
                cb@[k + 1] <= nc,
                nc == cv.len(),
                forall|i: int| a0 <= i < cb@[k + 1] ==> #[trigger] ex@[i - a0] == gsum(g, xs, kr(w.kmin + cv[i]), 0),
                x <= ex@.len(),
                tot@.len() == a0 + x,
                forall|a: int| 0 <= a < tot@.len() ==> #[trigger] tot@[a] == gsum(g, xs, kr(w.kmin + cv[a]), 0),
            decreases ex@.len() - x,
        {
            proof {
                assert(ex@[(a0 + x) - a0] == gsum(g, xs, kr(w.kmin + cv[a0 + x]), 0));
            }
            tot.push(ex[x]);
            x = x + 1;
        }
        k = k + 1;
    }
    Ok((shared, tot))
}

// ------------------------------------------------------------------------------------------------ the plan

/// The fast plan; `None` when a guard or the check fails.
pub fn fast(c: &Li, s: &Su, lo: i64, hi: i64, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<Option<(i128, Hits)>, WorkerFailure>)
    requires
        li_full(*c), su_shape(*s), 1 <= workers <= MAX_WORKERS,
        sk::keyidx_ok(s.key@, s.key_base@, Seq::<u32>::empty(), Seq::<u64>::empty(), s.bs as int, s.kind, s.ns as int),
    ensures r matches Ok(Some(t)) ==> plan_ok(*c, *s, lo, hi, t.0, t.1),
{
    // Pass 1 is bound by memory traffic: 28 tasks (when that many workers are allowed) were measured faster than 24,
    // 32 or 64 (fewer accumulators to zero and merge, fewer threads sharing cores). Below 16 workers the 16 chunks
    // run serially (the bound sums need about 16 chunks to stay tight), never on more threads than allowed.
    let nch: usize = if workers >= 28 { 28 } else if workers >= 16 { workers } else { 16 };
    let pw: usize = if workers >= nch { workers } else { 1 };
    let (w, gb, bs, p2) = match prepare(c, lo, hi, nch) {
        Some(t) => t,
        None => return Ok(None),
    };
    let outs = match pass1(c, w, &gb, nch, pw, dispatch) {
        Ok(Some(o)) => o,
        Ok(None) => return Ok(None),
        Err(e) => return Err(e),
    };
    let ghost xs = xs_of(*c);
    let ghost g = qg(lo as int, hi as int);
    proof {
        lemma_fast_prefix(outs@, bnds_of(*c, gb@), *c, w, nch as int);
        lemma_rs_end(*c);
        assert(ix_ok(*c, w, bs));
    }
    let (mouts, tb) = match merge(c, w, outs, Ghost(gb@), workers, dispatch) {
        Ok(t) => t,
        Err(e) => return Err(e),
    };
    let (flags, cand0, tau) = match local_candidates(c, w, &mouts, &tb) {
        Some(t) => t,
        None => {
            let tau = global_threshold(&mouts);
            let (f, cd) = candidates(c, w, &mouts, &tb, tau);
            (f, cd, tau)
        },
    };
    let (cand, tot) = match exact(c, w, bs, cand0, workers, dispatch) {
        Ok(t) => t,
        Err(e) => return Err(e),
    };
    let m = max_of(&tot);
    // the check: no unflagged slot can reach M
    let tm1 = (tau - 1) as u128;
    proof {
        assert(tm1 * p2 <= 0x2000 * 0x100_0000_0000) by (nonlinear_arith)
            requires tm1 <= 0x2000, p2 <= 0x100_0000_0000;
    }
    if ((tm1 * p2) as i128) <= m {
        return Ok(conclude(c, s, w, &flags, &cand, &tot, Ghost(tau as int), m));
    }
    // second round: every slot whose bound sum may reach M is a candidate
    let q = (m as u128) / p2;
    let tau2: usize = if q < 0xFFFE { (q + 1) as usize } else { 0xFFFF };
    proof {
        assert((tau2 - 1) * p2 <= q * p2) by (nonlinear_arith) requires tau2 - 1 <= q, p2 >= 0;
        assert(q * p2 <= m) by (nonlinear_arith) requires q == (m as u128) / p2, p2 >= 1, m >= 0;
    }
    let (flags2, cand2) = candidates(c, w, &mouts, &tb, tau2);
    let (cand3, tot2) = match exact(c, w, bs, cand2, workers, dispatch) {
        Ok(t) => t,
        Err(e) => return Err(e),
    };
    let m2 = max_of(&tot2);
    let tm2 = (tau2 - 1) as u128;
    proof {
        assert(tm2 * p2 <= 0xFFFF * 0x100_0000_0000) by (nonlinear_arith)
            requires tm2 <= 0xFFFF, p2 <= 0x100_0000_0000;
    }
    if ((tm2 * p2) as i128) <= m2 {
        return Ok(conclude(c, s, w, &flags2, &cand3, &tot2, Ghost(tau2 as int), m2));
    }
    Ok(None)
}

/// The largest exact sum (0 when none is positive).
fn max_of(tot: &Vec<i128>) -> (m: i128)
    ensures
        m >= 0,
        forall|a: int| 0 <= a < tot@.len() ==> #[trigger] tot@[a] <= m,
        m > 0 ==> exists|a: int| 0 <= a < tot@.len() && tot@[a] == m,
{
    let nc = tot.len();
    let mut m: i128 = 0;
    let mut a: usize = 0;
    while a < nc
        invariant
            nc == tot@.len(),
            a <= nc,
            m >= 0,
            forall|a2: int| 0 <= a2 < a ==> #[trigger] tot@[a2] <= m,
            m > 0 ==> exists|a2: int| 0 <= a2 < a && tot@[a2] == m,
        decreases nc - a,
    {
        if tot[a] > m {
            m = tot[a];
        }
        a = a + 1;
    }
    m
}

/// `M` and the hits once the check passed.
fn conclude(c: &Li, s: &Su, w: Win, flags: &Vec<u8>, cand: &Arc<Vec<u32>>, tot: &Vec<i128>, Ghost(tau): Ghost<int>, m: i128)
    -> (r: Option<(i128, Hits)>)
    requires
        su_shape(*s),
        sk::keyidx_ok(s.key@, s.key_base@, Seq::<u32>::empty(), Seq::<u64>::empty(), s.bs as int, s.kind, s.ns as int),
        kern_ok(*c, w),
        rows_fast(w, xs_of(*c), 0, c.n as int),
        flags_ok(flags@, cand@, w, xs_of(*c), tau),
        tot_ok(tot@, cand@, w, xs_of(*c)),
        w.cap <= 0x1000_0000,
        m >= 0,
        forall|a: int| 0 <= a < tot@.len() ==> #[trigger] tot@[a] <= m,
        m > 0 ==> exists|a: int| 0 <= a < tot@.len() && tot@[a] == m,
        tau >= 1,
        (tau - 1) * pow2(w.qs as nat) <= m,
    ensures r matches Some(t) ==> plan_ok(*c, *s, w.lo, w.hi, t.0, t.1),
{
    proof {
        assert(facts(*c, w, flags@, cand@, tot@, tau, m as int));
        lemma_max(*c, w, flags@, cand@, tot@, tau, m as int);
    }
    if s.kind == 1 && s.bs <= usize::MAX as u64 {
        if let Some(l) = supplier_hits_list(c, s, w, cand, tot, Ghost(flags@), Ghost(tau), m) {
            return Some((m, Hits::List(l)));
        }
        let hits = supplier_hits_idx(c, s, w, cand, tot, Ghost(flags@), Ghost(tau), m);
        return Some((m, Hits::Dense(hits)));
    }
    match supplier_hits(c, s, w, flags, cand, tot, Ghost(tau), m) {
        Some(hits) => Some((m, Hits::Dense(hits))),
        None => None,
    }
}

/// Whether key `key` is a group of sum `M` (`None`: a flagged slot not found among the candidates).
fn key_hit(c: &Li, w: Win, flags: &Vec<u8>, cand: &Arc<Vec<u32>>, tot: &Vec<i128>, Ghost(tau): Ghost<int>, m: i128, key: i128)
    -> (r: Option<bool>)
    requires
        facts(*c, w, flags@, cand@, tot@, tau, m as int),
        w.cap <= 0x1000_0000,
        -0x1_0000_0000_0000_0000 <= key <= 0x1_0000_0000_0000_0000,
    ensures
        r matches Some(h) ==> h == (gcount(qg(w.lo as int, w.hi as int), xs_of(*c), kr(key as int)) > 0
            && gsum(qg(w.lo as int, w.hi as int), xs_of(*c), kr(key as int), 0) == m),
{
    let ghost g = qg(w.lo as int, w.hi as int);
    let ghost xs = xs_of(*c);
    let ghost hm = gcount(g, xs, kr(key as int)) > 0 && gsum(g, xs, kr(key as int), 0) == m;
    proof {
        lemma_key_hit(*c, w, flags@, cand@, tot@, tau, m as int, key as int);
    }
    let t = key - w.kmin as i128;
    if 0 <= t && t < w.cap as i128 {
        let tu = t as usize;
        if flags[tu] != 0 {
            match find_cand(cand, tu as u32) {
                Some(a) => {
                    let v = tot[a];
                    proof {
                        assert(cand@[a as int] == t);
                        assert(hm == (m > 0 && tot@[a as int] == m));
                    }
                    Some(m > 0 && v == m)
                },
                None => None,
            }
        } else {
            assert(!hm);
            Some(false)
        }
    } else {
        assert(!hm);
        Some(false)
    }
}

/// `j / bs == b` for `b * bs <= j < (b + 1) * bs`.
proof fn lemma_div_between(j: int, b: int, bs: int)
    requires bs >= 1, b >= 0, b * bs <= j < (b + 1) * bs,
    ensures j / bs == b,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(j, bs);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(j, bs);
    assert(j / bs == b) by (nonlinear_arith)
        requires b * bs <= j, j < (b + 1) * bs, bs >= 1, j == bs * (j / bs) + j % bs, 0 <= j % bs < bs;
}

/// Per supplier row: whether its key is a group of sum `M` (keys decoded block by block).
fn supplier_hits(c: &Li, s: &Su, w: Win, flags: &Vec<u8>, cand: &Arc<Vec<u32>>, tot: &Vec<i128>, Ghost(tau): Ghost<int>, m: i128)
    -> (r: Option<Vec<bool>>)
    requires
        su_shape(*s),
        facts(*c, w, flags@, cand@, tot@, tau, m as int),
        w.cap <= 0x1000_0000,
    ensures
        r matches Some(hits) ==> hits@.len() == s.ns
            && forall|j: int| 0 <= j < s.ns ==> #[trigger] hits@[j] == hit_m(qg(w.lo as int, w.hi as int), xs_of(*c), m as int, mrow(*s, j)),
{
    let ghost g = qg(w.lo as int, w.hi as int);
    let ghost xs = xs_of(*c);
    let mut hits: Vec<bool> = Vec::with_capacity(s.ns);
    let bs = s.bs as u128;
    let mut b: usize = 0;
    let mut end: u128 = bs;
    let mut j: usize = 0;
    while j < s.ns
        invariant
            su_shape(*s),
            facts(*c, w, flags@, cand@, tot@, tau, m as int),
            w.cap <= 0x1000_0000,
            g == qg(w.lo as int, w.hi as int),
            xs == xs_of(*c),
            bs == s.bs,
            j <= s.ns,
            b as int * bs <= j,
            j < s.ns ==> j < end,
            end == (b + 1) * bs,
            b <= j,
            hits@.len() == j,
            forall|j2: int| 0 <= j2 < j ==> #[trigger] hits@[j2] == hit_m(g, xs, m as int, mrow(*s, j2)),
        decreases s.ns - j,
    {
        proof {
            lemma_div_between(j as int, b as int, bs as int);
            crate::stores::suppliers::interface::common::read::lemma_div_lt(j as int, s.bs as int, s.key_base@.len() as int);
        }
        let key = s.key_base[b] as i128 + s.key[j] as i128;
        proof {
            assert(key == skey_v(*s, j as int));
            assert(seq![mrow(*s, j as int)[0]] =~= kr(key as int));
        }
        match key_hit(c, w, flags, cand, tot, Ghost(tau), m, key) {
            Some(h) => hits.push(h),
            None => return None,
        }
        j = j + 1;
        if j as u128 == end && j < s.ns {
            proof {
                assert((b + 1) as int * bs <= j);
            }
            b = b + 1;
            end = end + bs;
            proof {
                assert(end == (b + 1) * bs) by (nonlinear_arith) requires end == b * bs + bs;
            }
        }
    }
    Some(hits)
}

/// Candidate `a` is a group of sum `M > 0` and supplier row `j` has its key.
pub open spec fn sel(s: Su, w: Win, cand: Seq<u32>, tot: Seq<i128>, m: int, a: int, j: int) -> bool {
    m > 0 && tot[a] == m && skey_v(s, j) == w.kmin + cand[a]
}

/// Some candidate below `a` selects supplier row `j`.
pub open spec fn sel_upto(s: Su, w: Win, cand: Seq<u32>, tot: Seq<i128>, m: int, a: int, j: int) -> bool {
    exists|a2: int| 0 <= a2 < a && #[trigger] sel(s, w, cand, tot, m, a2, j)
}

/// A key is a group of sum `M` exactly when some candidate of exact sum `M > 0` has it.
proof fn lemma_sel_hit(c: Li, s: Su, w: Win, flags: Seq<u8>, cand: Seq<u32>, tot: Seq<i128>, tau: int, m: int, j: int)
    requires facts(c, w, flags, cand, tot, tau, m), 0 <= j < s.ns,
        -0x1_0000_0000_0000_0000 <= skey_v(s, j) <= 0x1_0000_0000_0000_0000,
    ensures hit_m(qg(w.lo as int, w.hi as int), xs_of(c), m, mrow(s, j)) == sel_upto(s, w, cand, tot, m, cand.len() as int, j),
{
    let g = qg(w.lo as int, w.hi as int);
    let xs = xs_of(c);
    let key = skey_v(s, j);
    assert(seq![mrow(s, j)[0]] =~= kr(key));
    lemma_key_hit(c, w, flags, cand, tot, tau, m, key);
    let h = gcount(g, xs, kr(key)) > 0 && gsum(g, xs, kr(key), 0) == m;
    if sel_upto(s, w, cand, tot, m, cand.len() as int, j) {
        let a = choose|a2: int| 0 <= a2 < cand.len() && #[trigger] sel(s, w, cand, tot, m, a2, j);
        assert(tot[a] == m);
    }
    if h {
        let t = key - w.kmin;
        if 0 <= t < w.cap && flags[t] != 0 {
            let a = choose|a: int| 0 <= a < cand.len() && cand[a] == t;
            assert(tot[a] == m);
            assert(sel(s, w, cand, tot, m, a, j));
        }
    }
}

/// Per supplier row: whether its key is a group of sum `M`, through the supplier key order (kind 1): the rows of
/// each candidate key of exact sum `M`.
fn supplier_hits_idx(c: &Li, s: &Su, w: Win, cand: &Arc<Vec<u32>>, tot: &Vec<i128>, Ghost(flags): Ghost<Seq<u8>>,
    Ghost(tau): Ghost<int>, m: i128) -> (hits: Vec<bool>)
    requires
        su_shape(*s),
        facts(*c, w, flags, cand@, tot@, tau, m as int),
        w.cap <= 0x1000_0000,
        s.kind == 1,
        s.bs <= usize::MAX,
        sk::keyidx_ok(s.key@, s.key_base@, Seq::<u32>::empty(), Seq::<u64>::empty(), s.bs as int, s.kind, s.ns as int),
    ensures
        hits@.len() == s.ns,
        forall|j: int| 0 <= j < s.ns ==> #[trigger] hits@[j] == hit_m(qg(w.lo as int, w.hi as int), xs_of(*c), m as int, mrow(*s, j)),
{
    let ghost cv = cand@;
    let ghost tv = tot@;
    let ns = s.ns;
    let bs = s.bs as usize;
    let e32: Vec<u32> = Vec::new();
    let e64: Vec<u64> = Vec::new();
    proof {
        assert(e32@ =~= Seq::<u32>::empty());
        assert(e64@ =~= Seq::<u64>::empty());
    }
    let mut hits: Vec<bool> = vec![false; ns];
    let nc = tot.len();
    let mut a: usize = 0;
    while a < nc
        invariant
            su_shape(*s),
            facts(*c, w, flags, cv, tv, tau, m as int),
            cand@ == cv, tot@ == tv,
            s.kind == 1,
            bs as int == s.bs as int,
            sk::keyidx_ok(s.key@, s.key_base@, e32@, e64@, bs as int, 1, ns as int),
            ns == s.ns,
            nc == tv.len(),
            a <= nc,
            hits@.len() == ns,
            forall|j: int| 0 <= j < ns ==> #[trigger] hits@[j] == sel_upto(*s, w, cv, tv, m as int, a as int, j),
        decreases nc - a,
    {
        let ta = tot[a];
        if m > 0 && ta == m {
            let key = w.kmin as i128 + cand[a] as i128;
            let (lo, hi) = sk::key_range(s.key, s.key_base, e32.as_slice(), e64.as_slice(), bs, 1, ns, key);
            proof {
                assert forall|j: int| 0 <= j < ns implies ((lo <= j < hi) == sel(*s, w, cv, tv, m as int, a as int, j)) by {
                    assert(sk::irow(1, e32@, e64@, bs as int, j) == j);
                    assert(sk::fkey(s.key@, s.key_base@, bs as int, j) == skey_v(*s, j));
                }
            }
            let mut p = lo;
            while p < hi
                invariant
                    lo <= p <= hi <= ns,
                    hits@.len() == ns,
                    forall|j: int| 0 <= j < ns ==> ((lo <= j < hi) == sel(*s, w, cv, tv, m as int, a as int, j)),
                    forall|j: int| 0 <= j < ns ==> #[trigger] hits@[j]
                        == (sel_upto(*s, w, cv, tv, m as int, a as int, j) || (lo <= j < p)),
                decreases hi - p,
            {
                put(&mut hits, p, true);
                p = p + 1;
            }
        }
        proof {
            assert forall|j: int| 0 <= j < ns implies #[trigger] hits@[j] == sel_upto(*s, w, cv, tv, m as int, a + 1, j) by {
                if sel(*s, w, cv, tv, m as int, a as int, j) {
                    assert(sel_upto(*s, w, cv, tv, m as int, a + 1, j));
                }
                if sel_upto(*s, w, cv, tv, m as int, a + 1, j) {
                    let a2 = choose|a2: int| 0 <= a2 < a + 1 && #[trigger] sel(*s, w, cv, tv, m as int, a2, j);
                    if a2 < a {
                        assert(sel_upto(*s, w, cv, tv, m as int, a as int, j));
                    }
                }
            }
        }
        a = a + 1;
    }
    proof {
        assert forall|j: int| 0 <= j < ns implies #[trigger] hits@[j] == hit_m(qg(w.lo as int, w.hi as int), xs_of(*c), m as int, mrow(*s, j)) by {
            crate::stores::suppliers::interface::common::read::lemma_div_lt(j, s.bs as int, s.key_base@.len() as int);
            lemma_sel_hit(*c, *s, w, flags, cv, tv, tau, m as int, j);
        }
    }
    hits
}

/// The supplier rows whose key is a group of sum `M`, in increasing order, through the supplier key order (kind 1):
/// the rows of each candidate key of exact sum `M`. `None` when the candidates' row ranges do not come in
/// increasing order (the caller then takes the flag vector).
fn supplier_hits_list(c: &Li, s: &Su, w: Win, cand: &Arc<Vec<u32>>, tot: &Vec<i128>, Ghost(flags): Ghost<Seq<u8>>,
    Ghost(tau): Ghost<int>, m: i128) -> (r: Option<Vec<usize>>)
    requires
        su_shape(*s),
        facts(*c, w, flags, cand@, tot@, tau, m as int),
        w.cap <= 0x1000_0000,
        s.kind == 1,
        s.bs <= usize::MAX,
        sk::keyidx_ok(s.key@, s.key_base@, Seq::<u32>::empty(), Seq::<u64>::empty(), s.bs as int, s.kind, s.ns as int),
    ensures
        r matches Some(l) ==> lists_hits(l@, *s, qg(w.lo as int, w.hi as int), xs_of(*c), m as int),
{
    let ghost cv = cand@;
    let ghost tv = tot@;
    let ns = s.ns;
    let bs = s.bs as usize;
    let e32: Vec<u32> = Vec::new();
    let e64: Vec<u64> = Vec::new();
    proof {
        assert(e32@ =~= Seq::<u32>::empty());
        assert(e64@ =~= Seq::<u64>::empty());
    }
    let mut l: Vec<usize> = Vec::new();
    // every listed row is below `next`
    let mut next: usize = 0;
    let nc = tot.len();
    let mut a: usize = 0;
    while a < nc
        invariant
            su_shape(*s),
            facts(*c, w, flags, cv, tv, tau, m as int),
            cand@ == cv, tot@ == tv,
            s.kind == 1,
            bs as int == s.bs as int,
            sk::keyidx_ok(s.key@, s.key_base@, e32@, e64@, bs as int, 1, ns as int),
            ns == s.ns,
            nc == tv.len(),
            a <= nc,
            next <= ns,
            forall|i: int| 0 <= i < l@.len() ==> #[trigger] l@[i] < next,
            forall|i1: int, i2: int| #![trigger l@[i1], l@[i2]] 0 <= i1 < i2 < l@.len() ==> l@[i1] < l@[i2],
            forall|j: int| 0 <= j < ns ==> (#[trigger] listed_row(l@, j) == sel_upto(*s, w, cv, tv, m as int, a as int, j)),
        decreases nc - a,
    {
        let ta = tot[a];
        if m > 0 && ta == m {
            let key = w.kmin as i128 + cand[a] as i128;
            let (lo, hi) = sk::key_range(s.key, s.key_base, e32.as_slice(), e64.as_slice(), bs, 1, ns, key);
            proof {
                assert forall|j: int| 0 <= j < ns implies ((lo <= j < hi) == sel(*s, w, cv, tv, m as int, a as int, j)) by {
                    assert(sk::irow(1, e32@, e64@, bs as int, j) == j);
                    assert(sk::fkey(s.key@, s.key_base@, bs as int, j) == skey_v(*s, j));
                }
            }
            if lo < next {
                return None;
            }
            let mut p = lo;
            while p < hi
                invariant
                    lo <= p <= hi <= ns,
                    next <= lo,
                    forall|j: int| 0 <= j < ns ==> ((lo <= j < hi) == sel(*s, w, cv, tv, m as int, a as int, j)),
                    forall|i: int| 0 <= i < l@.len() ==> #[trigger] l@[i] < p || (p == lo && l@[i] < next),
                    forall|i1: int, i2: int| #![trigger l@[i1], l@[i2]] 0 <= i1 < i2 < l@.len() ==> l@[i1] < l@[i2],
                    forall|j: int| 0 <= j < ns ==> (#[trigger] listed_row(l@, j)
                        == (sel_upto(*s, w, cv, tv, m as int, a as int, j) || (lo <= j < p))),
                decreases hi - p,
            {
                let ghost l0 = l@;
                l.push(p);
                proof {
                    assert(l@ == l0.push(p));
                    assert forall|j: int| 0 <= j < ns implies (#[trigger] listed_row(l@, j)
                        == (sel_upto(*s, w, cv, tv, m as int, a as int, j) || (lo <= j < p + 1))) by {
                        if listed_row(l@, j) {
                            let i = choose|i: int| 0 <= i < l@.len() && l@[i] as int == j;
                            if i < l0.len() {
                                assert(l0[i] == l@[i]);
                                assert(listed_row(l0, j));
                            }
                        }
                        if listed_row(l0, j) {
                            let i = choose|i: int| 0 <= i < l0.len() && l0[i] as int == j;
                            assert(l@[i] == l0[i]);
                            assert(listed_row(l@, j));
                        }
                        if j == p {
                            assert(l@[l0.len() as int] == p);
                            assert(listed_row(l@, j));
                        }
                    }
                    assert forall|i: int| 0 <= i < l@.len() implies #[trigger] l@[i] < p + 1 by {
                        if i < l0.len() {
                            assert(l0[i] == l@[i]);
                        }
                    }
                    assert forall|i1: int, i2: int| #![trigger l@[i1], l@[i2]] 0 <= i1 < i2 < l@.len() implies l@[i1] < l@[i2] by {
                        assert(l@[i1] == l0[i1]);
                        if i2 < l0.len() {
                            assert(l@[i2] == l0[i2]);
                        }
                    }
                }
                p = p + 1;
            }
            proof {
                assert forall|i: int| 0 <= i < l@.len() implies #[trigger] l@[i] < hi by {
                    assert(l@[i] < p || (p == lo && l@[i] < next));
                }
            }
            next = hi;
        }
        proof {
            assert forall|j: int| 0 <= j < ns implies (#[trigger] listed_row(l@, j) == sel_upto(*s, w, cv, tv, m as int, a + 1, j)) by {
                if sel(*s, w, cv, tv, m as int, a as int, j) {
                    assert(sel_upto(*s, w, cv, tv, m as int, a + 1, j));
                }
                if sel_upto(*s, w, cv, tv, m as int, a as int, j) {
                    let a2 = choose|a2: int| 0 <= a2 < a && #[trigger] sel(*s, w, cv, tv, m as int, a2, j);
                    assert(sel_upto(*s, w, cv, tv, m as int, a + 1, j));
                }
                if sel_upto(*s, w, cv, tv, m as int, a + 1, j) {
                    let a2 = choose|a2: int| 0 <= a2 < a + 1 && #[trigger] sel(*s, w, cv, tv, m as int, a2, j);
                    if a2 < a {
                        assert(sel_upto(*s, w, cv, tv, m as int, a as int, j));
                    }
                }
            }
        }
        a = a + 1;
    }
    proof {
        let g = qg(w.lo as int, w.hi as int);
        assert forall|j: int| 0 <= j < ns implies (hit_m(g, xs_of(*c), m as int, mrow(*s, j)) <==> #[trigger] listed_row(l@, j)) by {
            crate::stores::suppliers::interface::common::read::lemma_div_lt(j, s.bs as int, s.key_base@.len() as int);
            lemma_sel_hit(*c, *s, w, flags, cv, tv, tau, m as int, j);
        }
    }
    Some(l)
}

} // verus!
