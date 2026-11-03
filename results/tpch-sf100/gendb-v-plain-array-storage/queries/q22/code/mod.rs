//! TPC-H Q22 (global sales opportunity) over the flat `orders` and `customer` storages: per country code (the first
//! two characters of `c_phone`) among the seven parameters, the number and balance sum of the customers with a
//! balance above the average positive balance of those codes and without orders, ordered by code.
//!
//! Plan of a call (`query`):
//! 1. read `o_custkey`, `c_custkey`, `c_phone` and `c_acctbal` as whole parts (`cols`), and build the group-id
//!    table of all two-byte ASCII codes (`codes::build_lut`);
//! 2. phase 1 (`phase1`, one task per worker, at most `MAX_TASKS`): task `t` marks the customer keys of its orders
//!    range in its own bit set and computes the group ids of its customer range (`SLOW` where the fast test cannot
//!    decide) and the AVG population's partial count and balance sum. The bit sets cover keys `0..range` with
//!    `range >= MIN_RANGE` (fresh mappings, first touched by the worker); the serial path (one task) marks chunk by
//!    chunk grouped by key slice (`common::slice_marks`), the parallel path key by key (measured faster there);
//! 3. on the calling thread (`gather`): the group ids of `SLOW` rows by the general `SUBSTRING` (`fixup`), and the
//!    AVG totals; without an AVG population the answer is empty; else the integer threshold equivalent to
//!    `c_acctbal > AVG` (`threshold`, `common::avg_threshold`);
//! 4. phase 2 (`phase2`, one task per customer range of phase 1): the qualifying rows' counts and sums per group id;
//! 5. the per-slot totals (`totals`), one row per non-empty slot (`build_rows`), sorted by the code (`finish`).
//!
//! The proof: `tables`/`normal`/`ast`/`rowsem`/`subq`/`body` give the statement's meaning as the per-slot totals of
//! `normal`; the phases compute those totals over their ranges (`out1_ok`, `gparts_ok`), the range sums add up over
//! the even splits (`common::split`, `common::rsum`), and `answer` turns the sorted rows into the fixed claim.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::numeric::pow10;
use crate::gendb_entry::{Answer, answer_meets, stores_ready};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS, WorkerTask, fork_join};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::query::param_domain;
use crate::exec::value::EVal;
use crate::exec::ast::EOrderKey;
use crate::exec::relational::order::{sort_rows_exec, view_keys};
use crate::exec::fns::div::div_scale_exec;
use crate::link::query::view_rows;
use crate::bridge::fns::div::lemma_div_scale_range;
use crate::agent::common::rsum::*;
use crate::agent::common::split::*;
use crate::agent::common::zeroed::*;
use crate::agent::common::avg_threshold::*;
use crate::agent::tables::*;
use crate::agent::normal::*;
use crate::agent::ast::order_keys;
use crate::agent::cols::*;
use crate::agent::codes::*;
use crate::agent::phase1::*;
use crate::agent::phase2::*;
use crate::agent::answer::*;

pub mod common;
pub mod tables;
pub mod ast;
pub mod normal;
pub mod rowsem;
pub mod subq;
pub mod body;
pub mod answer;
pub mod cols;
pub mod codes;
pub mod phase1;
pub mod phase2;

verus! {

/// Most tasks of a phase: more tasks than this make each task's private bit set miss the caches (measured).
pub const MAX_TASKS: usize = 24;
/// Key slices of the chunked marking of the serial path (`common::slice_marks`).
pub const NSLICE: usize = 16;
/// Orders rows per chunk of the chunked marking.
pub const CHUNK: usize = 1048576;
/// Slots per key slice of the chunked marking: more than a chunk's share, and `NSLICE * SLICE_CAP` 4-byte slots
/// (32 MiB) is mapped fresh by the allocator, so its pages are placed by the worker that fills them.
pub const SLICE_CAP: usize = 524544;
/// Least key range of the bit sets: a bit set of at least `2^28` bits (32 MiB) is mapped fresh by the allocator,
/// so no calling-thread zeroing, and its pages are first touched (placed) by the worker that marks it.
pub const MIN_RANGE: u64 = 268435456;

/// The facts the phase-1 task `k` of `nt` carries.
pub open spec fn task1_ok(task: Task1, c: Cols, sv: StoresView, ps: Seq<Literal>, nt: int, k: int, range: u64) -> bool {
    &&& task.pre()
    &&& task.c == c && task.sv@ == sv && task.ps@ == ps && task.range == range
    &&& task.olo == split(c.no as int, nt, k) && task.ohi == split(c.no as int, nt, k + 1)
    &&& task.clo == split(c.nc as int, nt, k) && task.chi == split(c.nc as int, nt, k + 1)
}

/// What phase 1 gives for task `t` of `nt`.
pub open spec fn p1_ok(o: Out1, c: Cols, sv: StoresView, ps: Seq<Literal>, nt: int, t: int, range: u64) -> bool {
    out1_ok(o, sv, ps, split(c.no as int, nt, t), split(c.no as int, nt, t + 1), range as int,
        split(c.nc as int, nt, t), split(c.nc as int, nt, t + 1))
}

/// Phase 1: one task per orders range and customer range.
#[verifier::spinoff_prover]
fn phase1(c: &Cols, lut: &Arc<Vec<u8>>, nt: usize, range: u64, nw: usize, dispatch: &mut Dispatch,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Result<Vec<Out1>, QueryError>)
    requires
        cols_ok(*c, sv), lut_ok((**lut)@, ps), 1 <= nt <= MAX_WORKERS, range < u64::MAX, nw as int == nwords(range as int),
        c.nc < range,
    ensures
        r matches Ok(outs) ==> outs@.len() == nt && forall|t: int| 0 <= t < nt ==> #[trigger] p1_ok(outs@[t], *c, sv, ps, nt as int, t, range),
        r matches Err(e) ==> e is WorkerFailed,
{
    let mut tasks: Vec<Task1> = Vec::new();
    // the serial path marks chunk by chunk, grouped by key slices of 2^shift keys (customer keys are 1..nc)
    let mut shift: u64 = 6;
    while shift < 40 && ((c.nc as u64) >> shift) >= NSLICE as u64
        invariant 6 <= shift <= 40,
        decreases 40 - shift,
    {
        shift = shift + 1;
    }
    let np: usize = if nt == 1 { NSLICE } else { 0 };
    let chunk: usize = if c.no < CHUNK { c.no + 1 } else { CHUNK };
    let cap: usize = if nt == 1 { SLICE_CAP } else { 0 };
    let mut t: usize = 0;
    while t < nt
        invariant
            t <= nt, 1 <= nt <= MAX_WORKERS, cols_ok(*c, sv), lut_ok((**lut)@, ps), range < u64::MAX,
            nw as int == nwords(range as int), tasks@.len() == t,
            shift < 64, 1 <= chunk, np <= NSLICE, cap <= CHUNK,
            forall|k: int| 0 <= k < t ==> #[trigger] task1_ok(tasks@[k], *c, sv, ps, nt as int, k, range),
        decreases nt - t,
    {
        proof {
            lemma_split(c.no as int, nt as int, t as int, t + 1);
            lemma_split(c.no as int, nt as int, t + 1, nt as int);
            lemma_split(c.nc as int, nt as int, t as int, t + 1);
            lemma_split(c.nc as int, nt as int, t + 1, nt as int);
        }
        let olo = split_exec(c.no, nt, t);
        let ohi = split_exec(c.no, nt, t + 1);
        let clo = split_exec(c.nc, nt, t);
        let chi = split_exec(c.nc, nt, t + 1);
        proof {
            assert(np * cap <= NSLICE * CHUNK) by (nonlinear_arith) requires np <= NSLICE, cap <= CHUNK;
        }
        let task = Task1 { c: *c, lut: lut.clone(), sv: Ghost(sv), ps: Ghost(ps), olo, ohi, range, bits: zeros_u64(nw),
            clo, chi, codes: zeros_u8(chi - clo), buf: zeros_u32(np * cap), fill: zeros_usize(np), shift, np, cap, chunk };
        assert(task1_ok(task, *c, sv, ps, nt as int, t as int, range));
        tasks.push(task);
        t = t + 1;
    }
    let ghost tv = tasks@;
    proof {
        assert forall|k: int| 0 <= k < nt implies #[trigger] tasks@[k].pre() by {
            assert(task1_ok(tasks@[k], *c, sv, ps, nt as int, k, range));
        }
    }
    // even one task runs on a spawned thread: the calling thread stays light, so the kernel's NUMA balancing gives
    // it no preferred node that later calls' worker threads would inherit (measured: they crowd onto one node)
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => { return Err(QueryError::WorkerFailed(e)); },
    };
    proof {
        assert forall|k: int| 0 <= k < nt implies #[trigger] p1_ok(outs@[k], *c, sv, ps, nt as int, k, range) by {
            assert(task1_ok(tv[k], *c, sv, ps, nt as int, k, range));
            assert(tv[k].post(outs@[k]));
        }
    }
    Ok(outs)
}

/// The group ids of the `SLOW` rows of a customer range, and the range's exact AVG partials.
#[verifier::spinoff_prover]
fn fixup(c: &Cols, params: &Params, codes: Vec<u8>, clo: usize, chi: usize, Ghost(sv): Ghost<StoresView>)
    -> (r: (Vec<u8>, i128, u64))
    requires cols_ok(*c, sv), clo <= chi <= c.nc, codes_ok(codes@, sv, params@, clo as int, chi as int, false),
    ensures
        codes_ok(r.0@, sv, params@, clo as int, chi as int, true),
        avg_part_ok(r.1 as int, r.2 as int, sv, params@, clo as int, chi as int, true),
{
    let ghost ps = params@;
    let mut codes = codes;
    let mut sum: i128 = 0;
    let mut cnt: u64 = 0;
    let mut i = clo;
    while i < chi
        invariant
            clo <= i <= chi, chi <= c.nc, cols_ok(*c, sv), ps == params@,
            codes@.len() == chi - clo,
            forall|r: int| clo <= r < i ==> #[trigger] codes@[r - clo] == gid(sv, ps, r),
            forall|r: int| i <= r < chi ==> (#[trigger] codes@[r - clo] == SLOW) || codes@[r - clo] == gid(sv, ps, r),
            avg_part_ok(sum as int, cnt as int, sv, ps, clo as int, i as int, true),
        decreases chi - i,
    {
        let ghost before = codes@;
        if codes[i - clo] == SLOW {
            let g = slow_code(c, params, i, Ghost(sv));
            codes[i - clo] = g;
        }
        let g = codes[i - clo];
        proof {
            assert(g == gid(sv, ps, i as int));
            lemma_grp(ps, code_of(sv, i as int));
            assert(num15(bal(sv)[i as int]));
            assert forall|r: int| clo <= r < i + 1 implies #[trigger] codes@[r - clo] == gid(sv, ps, r) by {
                if r < i { assert(codes@[r - clo] == before[r - clo]); }
            }
            assert forall|r: int| i + 1 <= r < chi implies (#[trigger] codes@[r - clo] == SLOW) || codes@[r - clo] == gid(sv, ps, r) by {
                assert(codes@[r - clo] == before[r - clo]);
            }
        }
        if g < NONE {
            let v = c.bal[i];
            if v > 0 {
                proof {
                    assert(sum as int + v as int <= 999_999_999_999_999 * (cnt as int + 1)) by (nonlinear_arith)
                        requires sum as int <= 999_999_999_999_999 * (cnt as int), v < 1_000_000_000_000_000;
                    assert(999_999_999_999_999 * (cnt as int + 1) < 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff)
                        by (nonlinear_arith) requires cnt as int + 1 <= 0x2000_0000_0000_0000;
                }
                sum = sum + v;
                cnt = cnt + 1;
            }
        }
        proof {
            lemma_range_sum_step(clo as int, i as int, avg_sum_term(sv, ps));
            lemma_range_sum_step(clo as int, i as int, avg_cnt_term(sv, ps));
        }
        i = i + 1;
    }
    (codes, sum, cnt)
}

/// The phase-1 outputs, separated: the bit sets, the exact group ids per customer range, and the AVG totals.
#[verifier::spinoff_prover]
fn gather(c: &Cols, params: &Params, outs: Vec<Out1>, nt: usize, range: u64, Ghost(sv): Ghost<StoresView>)
    -> (r: (Vec<Vec<u64>>, Vec<Vec<u8>>, i128, u64))
    requires
        cols_ok(*c, sv), 1 <= nt <= MAX_WORKERS, range < u64::MAX, outs@.len() == nt,
        forall|t: int| 0 <= t < nt ==> #[trigger] p1_ok(outs@[t], *c, sv, params@, nt as int, t, range),
    ensures
        sets_ok(r.0@, sv, nt as int, range as int),
        forall|s: int| 0 <= s < nt ==> (#[trigger] r.0@[s])@.len() == nwords(range as int),
        r.1@.len() == nt,
        forall|t: int| 0 <= t < nt ==> #[trigger] codes_ok(r.1@[t]@, sv, params@, split(c.nc as int, nt as int, t),
            split(c.nc as int, nt as int, t + 1), true),
        r.2 as int == avg_s(sv, params@),
        r.3 as int == avg_n(sv, params@),
{
    let ghost ps = params@;
    let ghost orig = outs@;
    let mut outs = outs;
    let mut sets: Vec<Vec<u64>> = Vec::new();
    let mut codes_v: Vec<Vec<u8>> = Vec::new();
    let mut sum: i128 = 0;
    let mut cnt: u64 = 0;
    let mut t: usize = 0;
    proof { lemma_split(c.nc as int, nt as int, 0, nt as int); }
    while t < nt
        invariant
            t <= nt, 1 <= nt <= MAX_WORKERS, cols_ok(*c, sv), range < u64::MAX, ps == params@,
            orig.len() == nt,
            forall|k: int| 0 <= k < nt ==> #[trigger] p1_ok(orig[k], *c, sv, ps, nt as int, k, range),
            outs@ == orig.subrange(t as int, nt as int),
            sets@.len() == t, codes_v@.len() == t,
            forall|k: int| 0 <= k < t ==> (#[trigger] sets@[k])@ == orig[k].bits@,
            forall|k: int| 0 <= k < t ==> #[trigger] codes_ok(codes_v@[k]@, sv, ps, split(c.nc as int, nt as int, k),
                split(c.nc as int, nt as int, k + 1), true),
            avg_part_ok(sum as int, cnt as int, sv, ps, 0, split(c.nc as int, nt as int, t as int), true),
        decreases nt - t,
    {
        let o = outs.remove(0);
        proof {
            assert(o == orig[t as int]);
            assert(p1_ok(o, *c, sv, ps, nt as int, t as int, range));
            lemma_split(c.nc as int, nt as int, t as int, t + 1);
            lemma_split(c.nc as int, nt as int, t + 1, nt as int);
            assert(outs@ =~= orig.subrange(t + 1, nt as int));
        }
        let clo = split_exec(c.nc, nt, t);
        let chi = split_exec(c.nc, nt, t + 1);
        let Out1 { bits, codes, sum: s1, cnt: n1, slow } = o;
        let (codes, s1, n1) = if slow == 0 { (codes, s1, n1) } else { fixup(c, params, codes, clo, chi, Ghost(sv)) };
        proof {
            let (lo, mid, hi) = (0int, clo as int, chi as int);
            lemma_range_sum_split(lo, mid, hi, avg_sum_term(sv, ps));
            lemma_range_sum_split(lo, mid, hi, avg_cnt_term(sv, ps));
            let (s0, c0, sa, ca) = (sum as int, cnt as int, s1 as int, n1 as int);
            assert(s0 + sa <= 999_999_999_999_999 * (c0 + ca)) by (nonlinear_arith)
                requires s0 <= 999_999_999_999_999 * c0, sa <= 999_999_999_999_999 * ca;
            assert(c0 + ca <= hi);
            assert(hi <= 0x1fff_ffff_ffff_ffff);
            assert(999_999_999_999_999 * (c0 + ca) < 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff) by (nonlinear_arith)
                requires c0 + ca <= 0x1fff_ffff_ffff_ffff;
        }
        sum = sum + s1;
        cnt = cnt + n1;
        sets.push(bits);
        codes_v.push(codes);
        t = t + 1;
    }
    proof {
        assert forall|s: int| 0 <= s < nt implies #[trigger] keys_ok(sets@[s]@, sv, split(n_o(sv) as int, nt as int, s),
            split(n_o(sv) as int, nt as int, s + 1), range as int) by {
            assert(p1_ok(orig[s], *c, sv, ps, nt as int, s, range));
        }
        assert forall|s: int| 0 <= s < nt implies (#[trigger] sets@[s])@.len() == nwords(range as int) by {
            assert(p1_ok(orig[s], *c, sv, ps, nt as int, s, range));
        }
    }
    (sets, codes_v, sum, cnt)
}

/// `10^k` for `k <= 19`.
#[verifier::spinoff_prover]
fn pow10_u128(k: u32) -> (r: u128)
    requires k <= 19,
    ensures r as int == pow10(k as nat),
{
    let mut r: u128 = 1;
    let mut i: u32 = 0;
    while i < k
        invariant i <= k, k <= 19, r as int == pow10(i as nat), r <= 10_000_000_000_000_000_000,
        decreases k - i,
    {
        proof {
            crate::spec::numeric::lemma_pow10_monotone((i + 1) as nat, 19);
            assert(pow10(19) == 10_000_000_000_000_000_000) by (compute);
            assert(pow10((i + 1) as nat) == 10 * pow10(i as nat));
        }
        r = r * 10;
        i = i + 1;
    }
    r
}

/// The integer threshold `avg_thr(s, 2, n)`: a balance exceeds the AVG exactly when it exceeds this.
#[verifier::spinoff_prover]
fn threshold(s: i128, n: u64) -> (thr: i128)
    requires 1 <= n, 0 <= s <= 999_999_999_999_999 * (n as int), n <= 0x1fff_ffff_ffff_ffff,
    ensures thr as int == avg_thr(s as int, 2, n as int),
{
    let r = div_scale_exec(s, 2, n as i128, 0);
    proof { lemma_div_scale_range(s as int, 2, n as int, 0); }
    let k: u32 = r - 2;
    let ghost p = pow10(k as nat);
    proof {
        assert(k as nat == avg_shift(s as int, 2, n as int));
        crate::spec::numeric::lemma_pow10_positive(k as nat);
    }
    let half: u128 = if k >= 20 {
        proof { lemma_thr_large_shift(n as int, k as nat); }
        0
    } else {
        let p10 = pow10_u128(k);
        proof {
            crate::spec::numeric::lemma_pow10_monotone(k as nat, 19);
            assert(pow10(19) == 10_000_000_000_000_000_000) by (compute);
            assert(2 * p10 <= 20_000_000_000_000_000_000u128);
        }
        (n as u128) / (2 * p10)
    };
    proof {
        assert(half as int == (n as int) / (2 * p));
        assert(half <= n as u128) by (nonlinear_arith) requires half as int == (n as int) / (2 * p), p >= 1, n >= 1;
        assert(999_999_999_999_999 * (n as int) < 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff) by (nonlinear_arith)
            requires n as int <= 0x1fff_ffff_ffff_ffff;
    }
    let q: u128 = ((s as u128) + half) / (n as u128);
    proof {
        let (qq, xx, nn) = (q as int, (s as u128 + half) as int, n as int);
        assert(qq <= xx) by (nonlinear_arith) requires qq == xx / nn, nn >= 1, xx >= 0;
    }
    q as i128
}

/// The facts the phase-2 task `k` of `nt` carries.
pub open spec fn task2_ok(task: Task2, c: Cols, sv: StoresView, ps: Seq<Literal>, nt: int, k: int) -> bool {
    &&& task.pre()
    &&& task.sv@ == sv && task.ps@ == ps
    &&& task.clo == split(c.nc as int, nt, k) && task.chi == split(c.nc as int, nt, k + 1)
}

/// What phase 2 gives for task `t` of `nt`.
pub open spec fn p2_ok(o: Out2, c: Cols, sv: StoresView, ps: Seq<Literal>, nt: int, t: int) -> bool {
    gparts_ok(o.cnts@, o.sums@, sv, ps, split(c.nc as int, nt, t), split(c.nc as int, nt, t + 1))
}

/// Phase 2: the qualifying rows' counts and sums per group id, one task per customer range.
#[verifier::spinoff_prover]
fn phase2(c: &Cols, sets: &Arc<Vec<Vec<u64>>>, codes_all: &Arc<Vec<Vec<u8>>>, nt: usize, range: u64, nw: usize,
    threshold: i128, dispatch: &mut Dispatch, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: Result<Vec<Out2>, QueryError>)
    requires
        cols_ok(*c, sv), 1 <= nt <= MAX_WORKERS, range < u64::MAX, nw as int == nwords(range as int),
        sets_ok((**sets)@, sv, nt as int, range as int),
        forall|s: int| 0 <= s < nt ==> (#[trigger] (**sets)@[s])@.len() == nwords(range as int),
        (**codes_all)@.len() == nt,
        forall|t: int| 0 <= t < nt ==> #[trigger] codes_ok((**codes_all)@[t]@, sv, ps, split(c.nc as int, nt as int, t),
            split(c.nc as int, nt as int, t + 1), true),
        avg_n(sv, ps) > 0, threshold as int == thr(sv, ps),
    ensures
        r matches Ok(outs) ==> outs@.len() == nt && forall|t: int| 0 <= t < nt ==> #[trigger] p2_ok(outs@[t], *c, sv, ps, nt as int, t),
        r matches Err(e) ==> e is WorkerFailed,
{
    let mut tasks: Vec<Task2> = Vec::new();
    let mut t: usize = 0;
    while t < nt
        invariant
            t <= nt, 1 <= nt <= MAX_WORKERS, cols_ok(*c, sv), range < u64::MAX, nw as int == nwords(range as int),
            sets_ok((**sets)@, sv, nt as int, range as int),
            forall|s: int| 0 <= s < nt ==> (#[trigger] (**sets)@[s])@.len() == nwords(range as int),
            (**codes_all)@.len() == nt,
            forall|k: int| 0 <= k < nt ==> #[trigger] codes_ok((**codes_all)@[k]@, sv, ps, split(c.nc as int, nt as int, k),
                split(c.nc as int, nt as int, k + 1), true),
            avg_n(sv, ps) > 0, threshold as int == thr(sv, ps),
            tasks@.len() == t,
            forall|k: int| 0 <= k < t ==> #[trigger] task2_ok(tasks@[k], *c, sv, ps, nt as int, k),
        decreases nt - t,
    {
        proof {
            lemma_split(c.nc as int, nt as int, t as int, t + 1);
            lemma_split(c.nc as int, nt as int, t + 1, nt as int);
        }
        let clo = split_exec(c.nc, nt, t);
        let chi = split_exec(c.nc, nt, t + 1);
        proof { assert(chi <= c.nc && c.nc <= 0x1fff_ffff_ffff_ffff); }
        // the key window of the rows (customer keys `row + 1` in the usual layout)
        let a = clo / 64;
        let b = chi / 64 + 2;
        let w1 = if b < nw { b } else { nw };
        let w0 = if a < w1 { a } else { w1 };
        let task = Task2 { c: *c, sv: Ghost(sv), ps: Ghost(ps), sets: sets.clone(), nsets: nt, range, nw,
            codes_all: codes_all.clone(), t, clo, chi, thr: threshold, w0, w1, merged: zeros_u64(w1 - w0), cnts: zeros_u64(7),
            sums: zeros_i128(7) };
        assert(task2_ok(task, *c, sv, ps, nt as int, t as int));
        tasks.push(task);
        t = t + 1;
    }
    let ghost tv = tasks@;
    proof {
        assert forall|k: int| 0 <= k < nt implies #[trigger] tasks@[k].pre() by {
            assert(task2_ok(tasks@[k], *c, sv, ps, nt as int, k));
        }
    }
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => { return Err(QueryError::WorkerFailed(e)); },
    };
    proof {
        assert forall|k: int| 0 <= k < nt implies #[trigger] p2_ok(outs@[k], *c, sv, ps, nt as int, k) by {
            assert(task2_ok(tv[k], *c, sv, ps, nt as int, k));
            assert(tv[k].post(outs@[k]));
        }
    }
    Ok(outs)
}

/// The per-slot totals over all customer rows.
#[verifier::spinoff_prover]
fn totals(c: &Cols, outs: &Vec<Out2>, nt: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: (Vec<u64>, Vec<i128>))
    requires
        cols_ok(*c, sv), 1 <= nt <= MAX_WORKERS, outs@.len() == nt,
        forall|t: int| 0 <= t < nt ==> #[trigger] p2_ok(outs@[t], *c, sv, ps, nt as int, t),
    ensures gparts_ok(r.0@, r.1@, sv, ps, 0, c.nc as int),
{
    let mut cnts = zeros_u64(7);
    let mut sums = zeros_i128(7);
    let mut t: usize = 0;
    proof { lemma_split(c.nc as int, nt as int, 0, nt as int); }
    while t < nt
        invariant
            t <= nt, 1 <= nt <= MAX_WORKERS, cols_ok(*c, sv), outs@.len() == nt,
            forall|k: int| 0 <= k < nt ==> #[trigger] p2_ok(outs@[k], *c, sv, ps, nt as int, k),
            gparts_ok(cnts@, sums@, sv, ps, 0, split(c.nc as int, nt as int, t as int)),
        decreases nt - t,
    {
        proof {
            lemma_split(c.nc as int, nt as int, t as int, t + 1);
            lemma_split(c.nc as int, nt as int, t + 1, nt as int);
            assert(p2_ok(outs@[t as int], *c, sv, ps, nt as int, t as int));
        }
        let ghost mid = split(c.nc as int, nt as int, t as int);
        let ghost hi = split(c.nc as int, nt as int, t + 1);
        let o = &outs[t];
        let ghost (c0, s0) = (cnts@, sums@);
        let mut g: usize = 0;
        while g < 7
            invariant
                g <= 7, cnts@.len() == 7, sums@.len() == 7, 0 <= mid <= hi <= c.nc, c.nc as int == n_c(sv), sizes_ok(sv),
                gparts_ok(c0, s0, sv, ps, 0, mid),
                gparts_ok(o.cnts@, o.sums@, sv, ps, mid, hi),
                forall|g2: int| 0 <= g2 < g ==> #[trigger] cnts@[g2] as int == c0[g2] + o.cnts@[g2]
                    && sums@[g2] as int == s0[g2] + o.sums@[g2],
                forall|g2: int| g <= g2 < 7 ==> #[trigger] cnts@[g2] == c0[g2] && sums@[g2] == s0[g2],
            decreases 7 - g,
        {
            proof {
                let (ca, cb, sa, sb) = (c0[g as int] as int, o.cnts@[g as int] as int, s0[g as int] as int, o.sums@[g as int] as int);
                assert(ca <= mid && cb <= hi - mid);
                assert(sa + sb <= 999_999_999_999_999 * (ca + cb)) by (nonlinear_arith)
                    requires sa <= 999_999_999_999_999 * ca, sb <= 999_999_999_999_999 * cb;
                assert(sa + sb >= -999_999_999_999_999 * (ca + cb)) by (nonlinear_arith)
                    requires sa >= -999_999_999_999_999 * ca, sb >= -999_999_999_999_999 * cb;
                assert(999_999_999_999_999 * (ca + cb) < 0x7fff_ffff_ffff_ffff_ffff_ffff_ffff_ffff) by (nonlinear_arith)
                    requires ca + cb <= 0x1fff_ffff_ffff_ffff;
            }
            cnts[g] = cnts[g] + o.cnts[g];
            sums[g] = sums[g] + o.sums[g];
            g = g + 1;
        }
        proof {
            assert forall|g2: int| 0 <= g2 < 7 implies #[trigger] cnts@[g2] as int == range_sum(0, hi, gcnt_term(sv, ps, g2))
                && sums@[g2] as int == range_sum(0, hi, gsum_term(sv, ps, g2))
                && cnts@[g2] <= hi - 0
                && -999_999_999_999_999 * (cnts@[g2] as int) <= sums@[g2] as int <= 999_999_999_999_999 * (cnts@[g2] as int) by {
                lemma_range_sum_split(0, mid, hi, gcnt_term(sv, ps, g2));
                lemma_range_sum_split(0, mid, hi, gsum_term(sv, ps, g2));
                let (ca, cb, sa, sb) = (c0[g2] as int, o.cnts@[g2] as int, s0[g2] as int, o.sums@[g2] as int);
                assert(ca == range_sum(0, mid, gcnt_term(sv, ps, g2)) && sa == range_sum(0, mid, gsum_term(sv, ps, g2))
                    && ca <= mid && -999_999_999_999_999 * ca <= sa <= 999_999_999_999_999 * ca);
                assert(cb == range_sum(mid, hi, gcnt_term(sv, ps, g2)) && sb == range_sum(mid, hi, gsum_term(sv, ps, g2))
                    && cb <= hi - mid && -999_999_999_999_999 * cb <= sb <= 999_999_999_999_999 * cb);
                assert(cnts@[g2] as int == c0[g2] + o.cnts@[g2]);
                assert(sums@[g2] as int == s0[g2] + o.sums@[g2]);
                assert(sa + sb <= 999_999_999_999_999 * (ca + cb)) by (nonlinear_arith)
                    requires sa <= 999_999_999_999_999 * ca, sb <= 999_999_999_999_999 * cb;
                assert(sa + sb >= -999_999_999_999_999 * (ca + cb)) by (nonlinear_arith)
                    requires sa >= -999_999_999_999_999 * ca, sb >= -999_999_999_999_999 * cb;
            }
        }
        t = t + 1;
    }
    (cnts, sums)
}

/// Copies a byte string.
#[verifier::spinoff_prover]
fn copy_bytes(p: &[u8]) -> (v: Vec<u8>)
    ensures v@ == p@,
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < p.len()
        invariant i <= p@.len(), v@ == p@.subrange(0, i as int),
        decreases p@.len() - i,
    {
        v.push(p[i]);
        i = i + 1;
        proof { assert(v@ =~= p@.subrange(0, i as int)); }
    }
    proof { assert(v@ =~= p@); }
    v
}

/// One answer row per non-empty slot, in slot order.
#[verifier::spinoff_prover]
fn build_rows(c: &Cols, params: &Params, cnts: &Vec<u64>, sums: &Vec<i128>, Ghost(sv): Ghost<StoresView>)
    -> (rows: Vec<Vec<EVal>>)
    requires cols_ok(*c, sv), gparts_ok(cnts@, sums@, sv, params@, 0, c.nc as int),
    ensures view_rows(rows@) == slot_rows(sv, params@, 7),
{
    let ghost ps = params@;
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut g: usize = 0;
    while g < 7
        invariant
            g <= 7, cols_ok(*c, sv), ps == params@, gparts_ok(cnts@, sums@, sv, ps, 0, c.nc as int),
            view_rows(rows@) == slot_rows(sv, ps, g as int),
        decreases 7 - g,
    {
        proof {
            assert(cnts@[g as int] as int == gcnt(sv, ps, g as int));
            assert(sums@[g as int] as int == gsm(sv, ps, g as int));
        }
        if cnts[g] > 0 {
            let p = param_at(params, g);
            let mut row: Vec<EVal> = Vec::new();
            row.push(EVal::Text(copy_bytes(p)));
            row.push(EVal::Int(cnts[g] as i64));
            row.push(EVal::Num { coeff: sums[g], scale: 2 });
            proof {
                assert(crate::exec::value::view_row(row@) =~= slot_row(sv, ps, g as int));
                assert(view_rows(rows@.push(row)) =~= view_rows(rows@).push(crate::exec::value::view_row(row@)));
            }
            rows.push(row);
        }
        g = g + 1;
    }
    rows
}

/// The answer from the per-slot rows: sorted by the code.
#[verifier::spinoff_prover]
fn finish(c: &Cols, params: &Params, rows: Vec<Vec<EVal>>, Ghost(sv): Ghost<StoresView>) -> (r: Result<Answer, QueryError>)
    requires cols_ok(*c, sv), view_rows(rows@) == slot_rows(sv, params@, 7),
    ensures answer_meets(sv, params@, r),
{
    let ghost ps = params@;
    let mut keys: Vec<EOrderKey> = Vec::new();
    keys.push(EOrderKey { col: 0, desc: false, nulls_first: false });
    proof {
        assert(view_keys(keys@) =~= order_keys());
    }
    let ghost rv = rows@;
    let sorted = sort_rows_exec(&keys, rows);
    proof {
        assert(crate::exec::relational::schema::view_rows(rv) =~= view_rows(rv));
        assert(crate::exec::relational::schema::view_rows(sorted@) =~= view_rows(sorted@));
        let out = view_rows(sorted@);
        lemma_answer(sv, ps, out);
        assert(ps_ok(ps));
        lemma_outcome(sv, ps, out);
    }
    Ok(Answer::Rows(sorted))
}

/// Without an AVG population the answer has no row.
#[verifier::spinoff_prover]
proof fn lemma_slot_rows_empty(sv: StoresView, ps: Seq<Literal>, g: int)
    requires avg_n(sv, ps) == 0, 0 <= g <= 7,
    ensures slot_rows(sv, ps, g) == Seq::<Row>::empty(),
    decreases g,
{
    if g > 0 {
        lemma_slot_rows_empty(sv, ps, g - 1);
        lemma_no_population(sv, ps, g - 1);
    }
}

#[verifier::spinoff_prover]
pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost ps = params@;
    let c = read_cols(stores, Ghost(sv));
    let lut = Arc::new(build_lut(params));
    let nt = if workers < MAX_TASKS { workers } else { MAX_TASKS };
    let range: u64 = if (c.nc as u64) + 1 < MIN_RANGE { MIN_RANGE } else { (c.nc as u64) + 1 };
    let nw: usize = (range / 64 + 1) as usize;
    let outs = match phase1(&c, &lut, nt, range, nw, dispatch, Ghost(sv), Ghost(ps)) {
        Ok(o) => o,
        Err(e) => { return Err(e); },
    };
    let (sets, codes_v, s, n) = gather(&c, params, outs, nt, range, Ghost(sv));
    if n == 0 {
        let rows: Vec<Vec<EVal>> = Vec::new();
        proof {
            lemma_slot_rows_empty(sv, ps, 7);
            assert(view_rows(rows@) =~= Seq::<Row>::empty());
        }
        return finish(&c, params, rows, Ghost(sv));
    }
    proof {
        crate::agent::subq::lemma_avg_totals(sv, ps);
    }
    let thr = threshold(s, n);
    let sets = Arc::new(sets);
    let codes_all = Arc::new(codes_v);
    let outs2 = match phase2(&c, &sets, &codes_all, nt, range, nw, thr, dispatch, Ghost(sv), Ghost(ps)) {
        Ok(o) => o,
        Err(e) => { return Err(e); },
    };
    let (cnts, sums) = totals(&c, &outs2, nt, Ghost(sv), Ghost(ps));
    let rows = build_rows(&c, params, &cnts, &sums, Ghost(sv));
    finish(&c, params, rows, Ghost(sv))
}

} // verus!
