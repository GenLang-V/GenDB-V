//! Per-filing scan (one worker task per range `[lo, hi)` of positions of `sub_fy.fy_order`).
//!
//! The `sub` rows are visited in fiscal-year order (`j = fy_order[p]`: by fy, cik, name code, row). A row with
//! `fy = $2` is matched against the runs of the uom range `[r0, r1)` of `num` (their adsh values strictly increase) by
//! its adsh code (looked up near the row's rank in adsh order) and that code's run (a map from codes to the runs of
//! the range, built once per call). A matched row's run is summed: its value coefficients (`sum`) and absolute
//! coefficients (`mass`); the mass is accumulated while it stays at most `i128::MAX`, and a larger one stops the task
//! with `over` (the SUM's capacity condition fails for that filing's group). The output buffer is preallocated on the
//! calling thread.
//!
//! Contract (`ScanTask::post`): without `over` the buffer lists, in position order, `entry(j)` of every qualifying
//! row (`fy = $2` and a run of `($1, adsh_j)`), each with its run's exact sum and mass.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::text::lex_cmp;
use crate::spec::numeric::abs;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::parallel::WorkerTask;
use crate::gendb_entry::work::TaskBuffer;
use crate::stores::num::interface as num_if;
use crate::stores::num::interface::{num_layout_ok, run_adsh_of, u64s, uom_count, adsh_count, run_count};
use crate::stores::num::interface::common::text::{text_entry_of, compare_bytes, find_text, u8_part, lemma_dict_codes};
use crate::stores::num::interface::common::cols::i32_part;
use crate::stores::num::interface::common::runs::pair_lt;
use crate::stores::sub_fy::interface as sub_if;
use crate::stores::sub_fy::interface::{sub_layout_ok, adsh_bytes, fy_order};
use crate::stores::sub_fy::interface::common::perm::lemma_permutation_facts;
use crate::bridge::order::{lemma_lex_cmp_antisym, lemma_lex_cmp_trans};
use crate::bridge::equality::lemma_lex_cmp_zero;
use crate::agent::common::sort::Filing;
use crate::agent::common::sums::*;
use crate::agent::numlink::{run_lo, run_hi, run_sum, run_mass, val_term, abs_term_at, value_at};

verus! {

// ------------------------------------------------------------------------------------------------ specification

/// What a scan reads: the parts of both storages, the uom code `u` of `$1` and its run range `[r0, r1)`, `$2`.
pub struct ScanCtx {
    pub np: Seq<PartView>,
    pub sp: Seq<PartView>,
    pub u: int,
    pub r0: int,
    pub r1: int,
    pub p1: int,
}

pub open spec fn ctx_ok(c: ScanCtx) -> bool {
    &&& num_layout_ok(c.np)
    &&& sub_layout_ok(c.sp)
    &&& 0 <= c.u < uom_count(c.np)
    &&& c.r0 == u64s(c.np, num_if::P_UOM_RUNS)[c.u] as int
    &&& c.r1 == u64s(c.np, num_if::P_UOM_RUNS)[c.u + 1] as int
}

/// Number of `sub` rows.
pub open spec fn n_sub(c: ScanCtx) -> int {
    sub_if::row_count(c.sp)
}

/// The sub row at position `p` of the fiscal-year order.
pub open spec fn row_at(c: ScanCtx, p: int) -> int {
    fy_order(c.sp)[p] as int
}

/// `fy = $2` (not NULL).
pub open spec fn fy_ok(c: ScanCtx, j: int) -> bool {
    u8_part(c.sp[sub_if::P_FY_VALID as int])[j] != 0 && i32_part(c.sp[sub_if::P_FY as int])[j] as int == c.p1
}

/// The `fy` sort word of `$2` (`interface::fy_word` of a row with `fy = $2`).
pub open spec fn fy_target(p1: int) -> int {
    p1 + 0x8000_0001
}

/// The `fy` sort word of the row at position `p` of the fiscal-year order.
pub open spec fn word_at(c: ScanCtx, p: int) -> int {
    sub_if::fy_word(c.sp, row_at(c, p)) as int
}

/// A row whose `fy` sort word is `$2`'s has `fy = $2`.
pub proof fn lemma_word_fy(c: ScanCtx, j: int)
    requires
        ctx_ok(c), 0 <= j < n_sub(c), -0x8000_0000 <= c.p1 < 0x8000_0000,
        sub_if::fy_word(c.sp, j) as int == fy_target(c.p1),
    ensures fy_ok(c, j),
{
    let v = i32_part(c.sp[sub_if::P_FY as int])[j];
    assert(i32::MIN <= v <= i32::MAX);
}

/// Run `r` of the uom range holds the filing of sub row `j`.
pub open spec fn run_match(c: ScanCtx, j: int, r: int) -> bool {
    c.r0 <= r < c.r1 && run_adsh_of(c.np, r) == adsh_bytes(c.sp, j)
}

pub open spec fn matched(c: ScanCtx, j: int) -> bool {
    exists|r: int| #[trigger] run_match(c, j, r)
}

pub open spec fn the_run(c: ScanCtx, j: int) -> int {
    choose|r: int| #[trigger] run_match(c, j, r)
}

/// Sub row `j` qualifies: `fy = $2` and a run of `($1, adsh_j)`.
pub open spec fn qualifies(c: ScanCtx, j: int) -> bool {
    fy_ok(c, j) && matched(c, j)
}

/// The group key words of sub row `j`: cik biased by `2^31` (order preserving, nonnegative), name code.
pub open spec fn cik_word(c: ScanCtx, j: int) -> u64 {
    (i32_part(c.sp[sub_if::P_CIK as int])[j] as int + 0x8000_0000) as u64
}

pub open spec fn name_word(c: ScanCtx, j: int) -> u64 {
    u64s(c.sp, sub_if::P_NAME_CODES)[j]
}

/// The output entry of a qualifying sub row `j`.
pub open spec fn entry(c: ScanCtx, j: int) -> Filing {
    Filing {
        cik: cik_word(c, j),
        name: name_word(c, j),
        sum: run_sum(c.np, the_run(c, j)) as i128,
        mass: run_mass(c.np, the_run(c, j)) as u128,
    }
}

/// The entries of the qualifying rows at positions `[lo, hi)`, in position order.
pub open spec fn filt(c: ScanCtx, lo: int, hi: int) -> Seq<Filing>
    decreases hi - lo,
{
    if hi <= lo {
        Seq::empty()
    } else {
        let j = row_at(c, hi - 1);
        filt(c, lo, hi - 1) + if qualifies(c, j) { seq![entry(c, j)] } else { Seq::<Filing>::empty() }
    }
}

/// A qualifying row whose run's absolute mass exceeds `i128::MAX`.
pub open spec fn big(c: ScanCtx, j: int) -> bool {
    qualifies(c, j) && run_mass(c.np, the_run(c, j)) > i128::MAX as int
}

/// No row at positions `[lo, hi)` is big.
pub open spec fn none_big(c: ScanCtx, lo: int, hi: int) -> bool {
    forall|p: int| lo <= p < hi ==> !#[trigger] big(c, row_at(c, p))
}

// ------------------------------------------------------------------------------------------------ layout facts

/// The uom range is a range of runs, all of uom code `u`.
pub proof fn lemma_range(c: ScanCtx)
    requires ctx_ok(c),
    ensures
        0 <= c.r0 <= c.r1 <= run_count(c.np),
        forall|r: int| c.r0 <= r < c.r1 ==> #[trigger] u64s(c.np, num_if::P_RUN_UOM)[r] == c.u,
{
    num_if::lemma_uom_runs(c.np, c.u);
}

/// Inside the uom range the runs' adsh values strictly increase.
pub proof fn lemma_runs_increase(c: ScanCtx, a: int, b: int)
    requires ctx_ok(c), c.r0 <= a < b < c.r1,
    ensures lex_cmp(run_adsh_of(c.np, a), run_adsh_of(c.np, b)) < 0,
{
    lemma_range(c);
    let ru = u64s(c.np, num_if::P_RUN_UOM);
    let ra = u64s(c.np, num_if::P_RUN_ADSH);
    assert(pair_lt(ru[a], ra[a], ru[b], ra[b]));
    assert(ru[a] == ru[b]);
    assert(ra[a] < adsh_count(c.np) && ra[b] < adsh_count(c.np));
    lemma_dict_codes(u64s(c.np, num_if::P_ADSH_OFF), u8_part(c.np[num_if::P_ADSH_BYTES as int]), adsh_count(c.np),
        ra[a] as int, ra[b] as int);
}

/// At most one run of the uom range holds a given filing.
pub proof fn lemma_run_match_unique(c: ScanCtx, j: int, a: int, b: int)
    requires ctx_ok(c), run_match(c, j, a), run_match(c, j, b),
    ensures a == b,
{
    if a < b {
        lemma_runs_increase(c, a, b);
        lemma_lex_cmp_zero(run_adsh_of(c.np, a), run_adsh_of(c.np, b));
    } else if b < a {
        lemma_runs_increase(c, b, a);
        lemma_lex_cmp_zero(run_adsh_of(c.np, b), run_adsh_of(c.np, a));
    }
}

/// One more position of `filt`.
pub proof fn lemma_filt_step(c: ScanCtx, lo: int, hi: int)
    requires lo <= hi,
    ensures
        filt(c, lo, hi + 1) == filt(c, lo, hi) + if qualifies(c, row_at(c, hi)) {
            seq![entry(c, row_at(c, hi))]
        } else {
            Seq::<Filing>::empty()
        },
{
}

pub proof fn lemma_filt_len(c: ScanCtx, lo: int, hi: int)
    requires lo <= hi,
    ensures filt(c, lo, hi).len() <= hi - lo,
    decreases hi - lo,
{
    if hi > lo {
        lemma_filt_len(c, lo, hi - 1);
    }
}

/// The run boundaries of the uom range lie inside the values of the range.
pub proof fn lemma_run_bounds(c: ScanCtx, r: int)
    requires ctx_ok(c), c.r0 <= r < c.r1,
    ensures run_lo(c.np, c.r0) <= run_lo(c.np, r) < run_hi(c.np, r) <= run_lo(c.np, c.r1),
{
    lemma_range(c);
    let start = u64s(c.np, num_if::P_RUN_START);
    assert(start[r] < start[r + 1]);
    if c.r0 < r {
        assert(start[c.r0] < start[r]);
    }
    if r + 1 < c.r1 {
        assert(start[r + 1] < start[c.r1]);
    }
}

// ------------------------------------------------------------------------------------------------ exec helpers

/// Absolute value of an `i128` as `u128` (exact, also for `i128::MIN`).
pub fn abs_u128(v: i128) -> (r: u128)
    ensures r as int == abs(v as int),
    no_unwind
{
    if v >= 0 { v as u128 } else { ((-(v + 1)) as u128) + 1 }
}

/// Sum and absolute mass of `values[a..b)`, the stored positions `[v_lo + a, v_lo + b)`; `None` when the mass
/// exceeds `i128::MAX`.
pub fn sum_range(values: &[i128], a: usize, b: usize, Ghost(np): Ghost<Seq<PartView>>, Ghost(v_lo): Ghost<int>)
    -> (r: Option<(i128, u128)>)
    requires
        a <= b <= values@.len(),
        forall|k: int| 0 <= k < values@.len() ==> #[trigger] values@[k] as int == value_at(np, v_lo + k),
    ensures
        match r {
            Some((s, m)) => s as int == rsum(v_lo + a, v_lo + b, val_term(np))
                && m as int == rsum(v_lo + a, v_lo + b, abs_term_at(np)) && m <= i128::MAX as u128,
            None => rsum(v_lo + a, v_lo + b, abs_term_at(np)) > i128::MAX as int,
        },
    no_unwind
{
    let ghost (lo, hi) = (v_lo + a, v_lo + b);
    proof {
        assert forall|k: int| lo <= k < hi implies #[trigger] abs_term_at(np)(k) >= 0 by {}
    }
    let mut i = a;
    let mut sum: i128 = 0;
    let mut mass: u128 = 0;
    while i < b
        invariant
            a <= i <= b <= values@.len(),
            forall|k: int| 0 <= k < values@.len() ==> #[trigger] values@[k] as int == value_at(np, v_lo + k),
            lo == v_lo + a, hi == v_lo + b,
            sum as int == rsum(lo, v_lo + i, val_term(np)),
            mass as int == rsum(lo, v_lo + i, abs_term_at(np)),
            mass <= i128::MAX as u128,
            forall|k: int| lo <= k < hi ==> #[trigger] abs_term_at(np)(k) >= 0,
        decreases b - i,
    {
        let v = values[i];
        proof {
            lemma_rsum_step(lo, v_lo + i, val_term(np));
            lemma_rsum_step(lo, v_lo + i, abs_term_at(np));
            lemma_rsum_abs(lo, v_lo + i + 1, val_term(np), abs_term_at(np));
        }
        let m = mass + abs_u128(v);
        if m > i128::MAX as u128 {
            proof {
                lemma_rsum_sub_range(lo, lo, v_lo + i + 1, hi, abs_term_at(np));
            }
            return None;
        }
        mass = m;
        sum = sum + v;
        i = i + 1;
    }
    Some((sum, mass))
}

// ------------------------------------------------------------------------------------------------ the task

/// Inputs of one range `[lo, hi)` of fiscal-year-order positions. Run positions are relative to `r0`; `values[k]` is the
/// value of stored position `v_lo + k`.
pub struct ScanTask {
    pub lo: usize,
    pub hi: usize,
    pub fy_order: &'static [u64],
    pub adsh_rank: &'static [u64],
    pub sub_adsh_off: &'static [u64],
    pub sub_adsh_bytes: &'static [u8],
    pub sub_rows: usize,
    pub fy: &'static [i32],
    pub fy_valid: &'static [u8],
    pub cik: &'static [i32],
    pub name_codes: &'static [u64],
    pub p1: i64,
    pub run_adsh: &'static [u64],
    pub run_start: &'static [u64],
    pub run_map: Arc<Vec<u64>>,
    pub nr: usize,
    pub dict_off: &'static [u64],
    pub dict_bytes: &'static [u8],
    pub dict_count: usize,
    pub values: &'static [i128],
    pub v_lo: u64,
    pub out: TaskBuffer<Filing>,
    pub ctx: Ghost<ScanCtx>,
}

/// The slices a scan reads, as parts of its context (shared by the task's `pre` and its loop).
pub open spec fn slices_ok(c: ScanCtx, sub_rows: usize, fy_order_s: Seq<u64>, adsh_rank_s: Seq<u64>, sub_adsh_off: Seq<u64>,
    sub_adsh_bytes: Seq<u8>, fy: Seq<i32>, fy_valid: Seq<u8>, cik: Seq<i32>, name_codes: Seq<u64>, p1: i64,
    run_adsh: Seq<u64>, run_start: Seq<u64>, nr: usize, dict_off: Seq<u64>, dict_bytes: Seq<u8>, dict_count: usize,
    values: Seq<i128>, v_lo: u64) -> bool {
    &&& ctx_ok(c)
    &&& sub_rows == n_sub(c)
    &&& fy_order_s == fy_order(c.sp)
    &&& adsh_rank_s == sub_if::adsh_rank(c.sp)
    &&& sub_adsh_off == u64s(c.sp, sub_if::P_ADSH_OFF)
    &&& sub_adsh_bytes == u8_part(c.sp[sub_if::P_ADSH_BYTES as int])
    &&& fy == i32_part(c.sp[sub_if::P_FY as int])
    &&& fy_valid == u8_part(c.sp[sub_if::P_FY_VALID as int])
    &&& cik == i32_part(c.sp[sub_if::P_CIK as int])
    &&& name_codes == u64s(c.sp, sub_if::P_NAME_CODES)
    &&& p1 as int == c.p1
    &&& nr == c.r1 - c.r0
    &&& run_adsh == u64s(c.np, num_if::P_RUN_ADSH).subrange(c.r0, c.r1)
    &&& run_start == u64s(c.np, num_if::P_RUN_START).subrange(c.r0, c.r1 + 1)
    &&& dict_off == u64s(c.np, num_if::P_ADSH_OFF)
    &&& dict_bytes == u8_part(c.np[num_if::P_ADSH_BYTES as int])
    &&& dict_count == adsh_count(c.np)
    &&& v_lo as int == run_lo(c.np, c.r0)
    &&& values.len() == run_lo(c.np, c.r1) - run_lo(c.np, c.r0)
    &&& values.len() <= usize::MAX
    &&& forall|k: int| 0 <= k < values.len() ==> #[trigger] values[k] as int == value_at(c.np, v_lo + k)
}

impl WorkerTask for ScanTask {
    type Output = (TaskBuffer<Filing>, bool);

    open spec fn pre(&self) -> bool {
        &&& slices_ok(self.ctx@, self.sub_rows, self.fy_order@, self.adsh_rank@, self.sub_adsh_off@, self.sub_adsh_bytes@, self.fy@,
            self.fy_valid@, self.cik@, self.name_codes@, self.p1, self.run_adsh@, self.run_start@, self.nr,
            self.dict_off@, self.dict_bytes@, self.dict_count, self.values@, self.v_lo)
        &&& self.lo <= self.hi <= self.sub_rows
        &&& -0x8000_0000 <= self.ctx@.p1 < 0x8000_0000
        &&& forall|q: int| self.lo <= q < self.hi ==> #[trigger] word_at(self.ctx@, q) == fy_target(self.ctx@.p1)
        &&& run_map_ok(self.ctx@, self.run_map@)
        &&& self.out.wf()
        &&& self.out.view().len() == 0
        &&& self.out.capacity() == self.hi - self.lo
    }

    open spec fn post(&self, out: Self::Output) -> bool {
        let c = self.ctx@;
        &&& out.0.wf()
        &&& !out.1 ==> out.0.view() == filt(c, self.lo as int, self.hi as int)
            && none_big(c, self.lo as int, self.hi as int)
        &&& out.1 ==> exists|p: int| self.lo <= p < self.hi && #[trigger] big(c, row_at(c, p))
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.lo as u64, self.hi as u64)
    }

    fn run(self) -> (out: Self::Output) {
        let ghost c = self.ctx@;
        let ghost (slo, shi) = (self.lo, self.hi);
        let ScanTask {
            lo, hi, fy_order: ord, adsh_rank, sub_adsh_off, sub_adsh_bytes, sub_rows, fy, fy_valid, cik, name_codes, p1, run_adsh,
            run_start, run_map, nr, dict_off, dict_bytes, dict_count, values, v_lo, out, ctx,
        } = self;
        let map: &Vec<u64> = &*run_map;
        proof {
            lemma_range(c);
            lemma_permutation_facts(fy_order(c.sp), n_sub(c) as nat);
        }
        let mut out = out;
        let mut p = lo;
        while p < hi
            invariant
                slices_ok(c, sub_rows, ord@, adsh_rank@, sub_adsh_off@, sub_adsh_bytes@, fy@, fy_valid@, cik@,
                    name_codes@, p1, run_adsh@, run_start@, nr, dict_off@, dict_bytes@, dict_count, values@, v_lo),
                0 <= c.r0 <= c.r1 <= run_count(c.np),
                slo == lo, shi == hi, self.lo == lo, self.hi == hi, self.ctx@ == c,
                lo <= p <= hi <= sub_rows,
                -0x8000_0000 <= c.p1 < 0x8000_0000,
                forall|q: int| lo <= q < hi ==> #[trigger] word_at(c, q) == fy_target(c.p1),
                run_map_ok(c, map@),
                forall|i: int| 0 <= i < n_sub(c) ==> #[trigger] fy_order(c.sp)[i] < n_sub(c),
                fy_order(c.sp).len() == n_sub(c),
                out.wf(),
                out.capacity() == hi - lo,
                out.view() == filt(c, lo as int, p as int),
                none_big(c, lo as int, p as int),
            decreases hi - p,
        {
            let j = ord[p] as usize;
            proof {
                lemma_filt_len(c, lo as int, p as int);
                lemma_filt_step(c, lo as int, p as int);
            }
            // Every position of the task's range has `fy = $2` (the range lies in the fiscal-year range of `$2`).
            proof {
                assert(word_at(c, p as int) == fy_target(c.p1));
                lemma_word_fy(c, j as int);
            }
            {
                assert(sub_if::adsh_rank(c.sp).len() == n_sub(c));
                let hint = adsh_rank[j];
                let found = match_run(sub_adsh_off, sub_adsh_bytes, sub_rows, j, hint, run_adsh, map, nr, dict_off,
                    dict_bytes, dict_count, Ghost(c));
                if found < nr {
                    let r = found;
                    proof {
                        assert(run_match(c, j as int, c.r0 + r));
                        lemma_run_match_unique(c, j as int, c.r0 + r, the_run(c, j as int));
                        lemma_run_bounds(c, c.r0 + r);
                        assert(run_start@[r as int] == u64s(c.np, num_if::P_RUN_START)[c.r0 + r]);
                        assert(run_start@[r + 1] == u64s(c.np, num_if::P_RUN_START)[c.r0 + r + 1]);
                        assert(run_start@[r as int] as int == run_lo(c.np, c.r0 + r));
                        assert(run_start@[r + 1] as int == run_hi(c.np, c.r0 + r));
                    }
                    let a = (run_start[r] - v_lo) as usize;
                    let b = (run_start[r + 1] - v_lo) as usize;
                    match sum_range(values, a, b, Ghost(c.np), Ghost(v_lo as int)) {
                        Some((s, m)) => {
                            proof {
                                lemma_rsum_abs(run_lo(c.np, c.r0 + r), run_hi(c.np, c.r0 + r), val_term(c.np),
                                    abs_term_at(c.np));
                            }
                            let f = Filing {
                                cik: (cik[j] as i64 + 0x8000_0000) as u64, name: name_codes[j],
                                sum: s, mass: m,
                            };
                            assert(f == entry(c, j as int));
                            out.push(f);
                        },
                        None => {
                            proof {
                                assert(v_lo + a == run_lo(c.np, c.r0 + r));
                                assert(v_lo + b == run_hi(c.np, c.r0 + r));
                                assert(run_mass(c.np, c.r0 + r) > i128::MAX as int);
                                assert(fy_ok(c, j as int));
                                assert(qualifies(c, j as int));
                                assert(big(c, row_at(c, p as int)));
                                assert(exists|q: int| slo <= q < shi && #[trigger] big(c, row_at(c, q)));
                            }
                            return (out, true);
                        },
                    }
                }
            }
            proof {
                assert forall|q: int| lo <= q < p + 1 implies !#[trigger] big(c, row_at(c, q)) by {
                    if q < p {
                        assert(!big(c, row_at(c, q)));
                    }
                }
            }
            p = p + 1;
        }
        (out, false)
    }
}

/// Inside the uom range the runs' adsh codes strictly increase.
pub proof fn lemma_codes_increase(c: ScanCtx, a: int, b: int)
    requires ctx_ok(c), c.r0 <= a < b < c.r1,
    ensures u64s(c.np, num_if::P_RUN_ADSH)[a] < u64s(c.np, num_if::P_RUN_ADSH)[b],
{
    lemma_range(c);
    let ru = u64s(c.np, num_if::P_RUN_UOM);
    let ra = u64s(c.np, num_if::P_RUN_ADSH);
    assert(pair_lt(ru[a], ra[a], ru[b], ra[b]));
    assert(ru[a] == ru[b]);
}

/// The num adsh code of sub row `j`: `Some(k)` when dictionary value `k` is the row's adsh, `None` when no value
/// is. The codes `hint` and `hint - 1` are tried first (num's adsh dictionary and sub's adsh order list nearly the
/// same filings, so a row's rank in adsh order is usually its code or one more), then a binary search.
pub fn find_code(sub_adsh_off: &[u64], sub_adsh_bytes: &[u8], sub_rows: usize, j: usize, hint: u64,
    dict_off: &[u64], dict_bytes: &[u8], dict_count: usize, Ghost(c): Ghost<ScanCtx>) -> (r: Option<usize>)
    requires
        ctx_ok(c),
        j < sub_rows, sub_rows == n_sub(c),
        sub_adsh_off@ == u64s(c.sp, sub_if::P_ADSH_OFF),
        sub_adsh_bytes@ == u8_part(c.sp[sub_if::P_ADSH_BYTES as int]),
        dict_off@ == u64s(c.np, num_if::P_ADSH_OFF),
        dict_bytes@ == u8_part(c.np[num_if::P_ADSH_BYTES as int]),
        dict_count == adsh_count(c.np),
    ensures
        r matches Some(k) ==> k < dict_count && num_if::dict_entry(c.np, num_if::P_ADSH_OFF, k as int) == adsh_bytes(c.sp, j as int),
        r is None ==> forall|k: int| 0 <= k < dict_count
            ==> #[trigger] num_if::dict_entry(c.np, num_if::P_ADSH_OFF, k) != adsh_bytes(c.sp, j as int),
    no_unwind
{
    let (key, key_len) = text_entry_of(sub_adsh_off, sub_adsh_bytes, sub_rows, j);
    if hint < dict_count as u64 {
        let k = hint as usize;
        let (e, en) = text_entry_of(dict_off, dict_bytes, dict_count, k);
        if compare_bytes(e, en, key, key_len) == 0 {
            proof { lemma_lex_cmp_zero(e@, key@); }
            return Some(k);
        }
    }
    if 0 < hint && hint <= dict_count as u64 {
        let k = (hint - 1) as usize;
        let (e, en) = text_entry_of(dict_off, dict_bytes, dict_count, k);
        if compare_bytes(e, en, key, key_len) == 0 {
            proof { lemma_lex_cmp_zero(e@, key@); }
            return Some(k);
        }
    }
    find_text(dict_off, dict_bytes, dict_count, key, key_len)
}

/// `map` locates the runs of the uom range by adsh code: the run (relative to `r0`) of each run's code. Codes of no
/// run hold anything; a lookup checks the run's code.
pub open spec fn run_map_ok(c: ScanCtx, map: Seq<u64>) -> bool {
    &&& map.len() == adsh_count(c.np)
    &&& forall|t: int| c.r0 <= t < c.r1 ==> map[#[trigger] u64s(c.np, num_if::P_RUN_ADSH)[t] as int] == t - c.r0
}

/// The run of the uom range (relative to `r0`) holding the filing of sub row `j`, or `nr` when there is none: the
/// row's adsh code (`find_code`, hinted by its rank `hint` in adsh order), then that code's run (`run_map`).
pub fn match_run(sub_adsh_off: &[u64], sub_adsh_bytes: &[u8], sub_rows: usize, j: usize, hint: u64, run_adsh: &[u64],
    run_map: &Vec<u64>, nr: usize, dict_off: &[u64], dict_bytes: &[u8], dict_count: usize, Ghost(c): Ghost<ScanCtx>)
    -> (r: usize)
    requires
        run_map_ok(c, run_map@),
        ctx_ok(c),
        j < sub_rows, sub_rows == n_sub(c),
        sub_adsh_off@ == u64s(c.sp, sub_if::P_ADSH_OFF),
        sub_adsh_bytes@ == u8_part(c.sp[sub_if::P_ADSH_BYTES as int]),
        nr == c.r1 - c.r0,
        run_adsh@ == u64s(c.np, num_if::P_RUN_ADSH).subrange(c.r0, c.r1),
        dict_off@ == u64s(c.np, num_if::P_ADSH_OFF),
        dict_bytes@ == u8_part(c.np[num_if::P_ADSH_BYTES as int]),
        dict_count == adsh_count(c.np),
    ensures
        r <= nr,
        r < nr ==> run_match(c, j as int, c.r0 + r),
        r == nr ==> forall|rr: int| !#[trigger] run_match(c, j as int, rr),
    no_unwind
{
    proof { lemma_range(c); }
    let ghost key_j = adsh_bytes(c.sp, j as int);
    let ghost ra = u64s(c.np, num_if::P_RUN_ADSH);
    match find_code(sub_adsh_off, sub_adsh_bytes, sub_rows, j, hint, dict_off, dict_bytes, dict_count, Ghost(c)) {
        Some(k) => {
            let r0 = run_map[k] as usize;
            let r = if r0 < nr && run_adsh[r0] == k as u64 { r0 } else { nr };
            proof {
                if r < nr {
                    assert(ra[c.r0 + r] == k as u64);
                } else {
                    // No run of the range has code `k`: the map would locate it.
                    assert forall|t: int| c.r0 <= t < c.r1 implies #[trigger] ra[t] != k as u64 by {
                        if ra[t] == k as u64 {
                            assert(run_map@[ra[t] as int] == t - c.r0);
                        }
                    }
                }
                if r == nr {
                    // A matching run's code has the row's adsh as its value, so it is `k` (sorted dictionary).
                    assert forall|rr: int| !#[trigger] run_match(c, j as int, rr) by {
                        if run_match(c, j as int, rr) {
                            assert(u64s(c.np, num_if::P_RUN_UOM)[rr] < uom_count(c.np));
                            assert(ra[rr] < adsh_count(c.np));
                            lemma_dict_codes(u64s(c.np, num_if::P_ADSH_OFF), u8_part(c.np[num_if::P_ADSH_BYTES as int]),
                                adsh_count(c.np), ra[rr] as int, k as int);
                            assert(ra[rr] != k as u64);
                        }
                    }
                }
            }
            r
        },
        None => {
            proof {
                assert forall|rr: int| !#[trigger] run_match(c, j as int, rr) by {
                    if run_match(c, j as int, rr) {
                        assert(u64s(c.np, num_if::P_RUN_UOM)[rr] < uom_count(c.np));
                        assert(ra[rr] < adsh_count(c.np));
                        assert(num_if::dict_entry(c.np, num_if::P_ADSH_OFF, ra[rr] as int) != key_j);
                    }
                }
            }
            nr
        },
    }
}

} // verus!
