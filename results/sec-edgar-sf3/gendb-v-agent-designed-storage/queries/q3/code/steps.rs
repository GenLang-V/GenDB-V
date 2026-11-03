//! The executable steps of `query`, each with the contract its proof uses: reading the storages' parts
//! (`lookup_uom`, `read_num`, `read_sub`), the parallel scan (`scan_all`), the per-cik totals (`cik_totals`), the
//! HAVING filter (`having`) and the output rows (`output_rows`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::parallel::{fork_join, Dispatch, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::work::TaskBuffer;
use crate::exec::value::{EVal, view_row};
use crate::exec::numeric::num_cmp_exec;
use crate::link::query::view_rows;
use crate::stores::num::interface as num_if;
use crate::stores::num::interface::{u64s, adsh_count, uom_count};
use crate::stores::sub_fy::interface as sub_if;
use crate::stores::num::interface::common::text::{find_text, text_entry_of, u64_part, u8_part};
use crate::stores::num::interface::common::cols::{i32_part, i128_part};
use crate::agent::common::sort::{Filing, SumRef};
use crate::agent::common::sums::*;
use crate::agent::scan::*;
use crate::agent::numlink::{run_lo, value_at};
use crate::agent::groups::Groups;
use crate::agent::link::{name_count, key_valid};
use crate::agent::assemble::hkey;
use crate::agent::output::{kept_upto, rr, rr_of};

verus! {

// ------------------------------------------------------------------------------------------------ reading parts

/// A whole `U64` part.
pub fn read_u64_all(st: &mut StoredParts, p: usize) -> (r: &'static [u64])
    requires p < old(st)@.len(), old(st)@[p as int] is U64,
    ensures final(st)@ == old(st)@, r@ == u64_part(old(st)@[p as int]),
{
    let n = st.part_len(p);
    let r = st.extent_u64(p, 0, n);
    assert(r@ =~= u64_part(old(st)@[p as int]));
    r
}

/// A whole `U8` part.
pub fn read_u8_all(st: &mut StoredParts, p: usize) -> (r: &'static [u8])
    requires p < old(st)@.len(), old(st)@[p as int] is U8,
    ensures final(st)@ == old(st)@, r@ == u8_part(old(st)@[p as int]),
{
    let n = st.part_len(p);
    let r = st.extent_u8(p, 0, n);
    assert(r@ =~= u8_part(old(st)@[p as int]));
    r
}

/// The uom code of `p0`, if `p0` is a unit of `num`.
pub fn lookup_uom(st: &mut StoredParts, p0: &[u8]) -> (r: Option<usize>)
    requires num_if::num_layout_ok(old(st)@),
    ensures
        final(st)@ == old(st)@,
        r matches Some(u) ==> u < num_if::uom_count(old(st)@) && num_if::dict_entry(old(st)@, num_if::P_UOM_OFF, u as int) == p0@,
        r is None ==> forall|k: int| 0 <= k < num_if::uom_count(old(st)@)
            ==> num_if::dict_entry(old(st)@, num_if::P_UOM_OFF, k) != p0@,
{
    let off = read_u64_all(st, num_if::P_UOM_OFF);
    let bytes = read_u8_all(st, num_if::P_UOM_BYTES);
    let count = off.len() - 1;
    let n = p0.len();
    find_text(off, bytes, count, p0, n)
}

/// The parts of `num` a scan reads (runs of the uom range, adsh dictionary, values of the range).
pub struct NumIn {
    pub run_adsh: &'static [u64],
    pub run_start: &'static [u64],
    pub nr: usize,
    pub dict_off: &'static [u64],
    pub dict_bytes: &'static [u8],
    pub dict_count: usize,
    pub values: &'static [i128],
    pub v_lo: u64,
}

/// The parts of `sub` a scan and the output read.
pub struct SubIn {
    pub ns: usize,
    pub fy_order: &'static [u64],
    pub adsh_rank: &'static [u64],
    pub adsh_off: &'static [u64],
    pub adsh_bytes: &'static [u8],
    pub fy: &'static [i32],
    pub fy_valid: &'static [u8],
    pub cik: &'static [i32],
    pub name_codes: &'static [u64],
    pub name_off: &'static [u64],
    pub name_bytes: &'static [u8],
    pub n_names: usize,
}

/// The scan's inputs are the parts of its context.
pub open spec fn inputs_ok(c: ScanCtx, ni: NumIn, si: SubIn, p1: i64) -> bool {
    &&& slices_ok(c, si.ns, si.fy_order@, si.adsh_rank@, si.adsh_off@, si.adsh_bytes@, si.fy@, si.fy_valid@, si.cik@,
        si.name_codes@, p1, ni.run_adsh@, ni.run_start@, ni.nr, ni.dict_off@, ni.dict_bytes@, ni.dict_count,
        ni.values@, ni.v_lo)
    &&& si.name_off@ == crate::stores::sub_fy::interface::common::text::u64_part(c.sp[sub_if::P_NAME_DICT_OFF as int])
    &&& si.name_bytes@ == crate::stores::sub_fy::interface::common::text::u8_part(c.sp[sub_if::P_NAME_DICT_BYTES as int])
    &&& si.n_names == name_count(c.sp)
}

/// The run range of uom code `u` and the `num` parts over it.
pub fn read_num(st: &mut StoredParts, u: usize) -> (r: (NumIn, usize, usize))
    requires num_if::num_layout_ok(old(st)@), u < num_if::uom_count(old(st)@),
    ensures
        final(st)@ == old(st)@,
        r.1 as int == num_if::u64s(old(st)@, num_if::P_UOM_RUNS)[u as int],
        r.2 as int == num_if::u64s(old(st)@, num_if::P_UOM_RUNS)[u + 1],
        ({
            let np = old(st)@;
            let (ni, r0, r1) = r;
            &&& ni.nr == r1 - r0
            &&& ni.run_adsh@ == num_if::u64s(np, num_if::P_RUN_ADSH).subrange(r0 as int, r1 as int)
            &&& ni.run_start@ == num_if::u64s(np, num_if::P_RUN_START).subrange(r0 as int, r1 + 1)
            &&& ni.dict_off@ == num_if::u64s(np, num_if::P_ADSH_OFF)
            &&& ni.dict_bytes@ == u8_part(np[num_if::P_ADSH_BYTES as int])
            &&& ni.dict_count == num_if::adsh_count(np)
            &&& ni.v_lo as int == run_lo(np, r0 as int)
            &&& ni.values@.len() == run_lo(np, r1 as int) - run_lo(np, r0 as int)
            &&& ni.values@.len() <= usize::MAX
            &&& forall|k: int| 0 <= k < ni.values@.len() ==> #[trigger] ni.values@[k] as int == value_at(np, ni.v_lo + k)
        }),
{
    let ghost np = st@;
    proof { num_if::lemma_uom_runs(np, u as int); }
    let n_runs = st.part_len(num_if::P_RUN_UOM);
    let n_uom_runs = st.part_len(num_if::P_UOM_RUNS);
    let n_run_start = st.part_len(num_if::P_RUN_START);
    let uom_runs = st.extent_u64(num_if::P_UOM_RUNS, u, u + 2);
    let r0 = uom_runs[0] as usize;
    let r1 = uom_runs[1] as usize;
    let nr = r1 - r0;
    let run_adsh = st.extent_u64(num_if::P_RUN_ADSH, r0, r1);
    let run_start = st.extent_u64(num_if::P_RUN_START, r0, r1 + 1);
    let dict_off = read_u64_all(st, num_if::P_ADSH_OFF);
    let dict_bytes = read_u8_all(st, num_if::P_ADSH_BYTES);
    let dict_count = dict_off.len() - 1;
    let n_values = st.part_len(num_if::P_VALUE);
    proof {
        let start = num_if::u64s(np, num_if::P_RUN_START);
        let nruns = num_if::run_count(np);
        assert(start[0] == 0 && start[nruns] == num_if::row_count(np));
        if r0 < r1 {
            assert(start[r0 as int] < start[r1 as int]);
        }
        if (r1 as int) < nruns {
            assert(start[r1 as int] < start[nruns]);
        }
        assert(run_start@[0] == start[r0 as int]);
        assert(run_start@[nr as int] == start[r1 as int]);
    }
    let v_lo = run_start[0];
    let v_hi = run_start[nr];
    let values = st.extent_i128(num_if::P_VALUE, v_lo as usize, v_hi as usize);
    (NumIn { run_adsh, run_start, nr, dict_off, dict_bytes, dict_count, values, v_lo }, r0, r1)
}

/// The `sub` parts.
pub fn read_sub(st: &mut StoredParts) -> (si: SubIn)
    requires sub_if::sub_layout_ok(old(st)@),
    ensures
        final(st)@ == old(st)@,
        ({
            let sp = old(st)@;
            &&& si.ns as int == sub_if::row_count(sp)
            &&& si.fy_order@ == sub_if::fy_order(sp)
            &&& si.adsh_rank@ == sub_if::adsh_rank(sp)
            &&& si.adsh_off@ == num_if::u64s(sp, sub_if::P_ADSH_OFF)
            &&& si.adsh_bytes@ == u8_part(sp[sub_if::P_ADSH_BYTES as int])
            &&& si.fy@ == i32_part(sp[sub_if::P_FY as int])
            &&& si.fy_valid@ == u8_part(sp[sub_if::P_FY_VALID as int])
            &&& si.cik@ == i32_part(sp[sub_if::P_CIK as int])
            &&& si.name_codes@ == num_if::u64s(sp, sub_if::P_NAME_CODES)
            &&& si.name_off@ == crate::stores::sub_fy::interface::common::text::u64_part(sp[sub_if::P_NAME_DICT_OFF as int])
            &&& si.name_bytes@ == crate::stores::sub_fy::interface::common::text::u8_part(sp[sub_if::P_NAME_DICT_BYTES as int])
            &&& si.n_names == name_count(sp)
        }),
{
    let ns = st.part_len(sub_if::P_CIK);
    proof {
        crate::stores::sub_fy::interface::common::perm::lemma_permutation_facts(sub_if::fy_order(old(st)@), ns as nat);
    }
    let fy_order = st.extent_u64(sub_if::P_FY_ORDER, 0, ns);
    let adsh_rank = st.extent_u64(sub_if::P_ADSH_RANK, 0, ns);
    let adsh_off = read_u64_all(st, sub_if::P_ADSH_OFF);
    let adsh_bytes = read_u8_all(st, sub_if::P_ADSH_BYTES);
    let fy = st.extent_i32(sub_if::P_FY, 0, ns);
    let fy_valid = st.extent_u8(sub_if::P_FY_VALID, 0, ns);
    let cik = st.extent_i32(sub_if::P_CIK, 0, ns);
    let name_codes = st.extent_u64(sub_if::P_NAME_CODES, 0, ns);
    let name_off = read_u64_all(st, sub_if::P_NAME_DICT_OFF);
    let name_bytes = read_u8_all(st, sub_if::P_NAME_DICT_BYTES);
    let n_names = name_off.len() - 1;
    proof {
        let sp = old(st)@;
        assert(fy_order@ =~= sub_if::fy_order(sp));
        assert(adsh_rank@ =~= sub_if::adsh_rank(sp));
        assert(fy@ =~= i32_part(sp[sub_if::P_FY as int]));
        assert(fy_valid@ =~= u8_part(sp[sub_if::P_FY_VALID as int]));
        assert(cik@ =~= i32_part(sp[sub_if::P_CIK as int]));
        assert(name_codes@ =~= num_if::u64s(sp, sub_if::P_NAME_CODES));
    }
    SubIn { ns, fy_order, adsh_rank, adsh_off, adsh_bytes, fy, fy_valid, cik, name_codes, name_off, name_bytes, n_names }
}

/// The scan's inputs for uom code `u`, as the parts of the context `c` (its run range read from the directory).
pub fn read_inputs(stores: &mut crate::gendb_entry::stores::Stores, u: usize, p1: i64, Ghost(c): Ghost<ScanCtx>)
    -> (r: (NumIn, SubIn))
    requires
        num_if::num_layout_ok(old(stores)@.num), sub_if::sub_layout_ok(old(stores)@.sub_fy),
        u < num_if::uom_count(old(stores)@.num),
        c.np == old(stores)@.num, c.sp == old(stores)@.sub_fy, c.u == u, c.p1 == p1 as int,
        c.r0 == num_if::u64s(c.np, num_if::P_UOM_RUNS)[u as int] as int,
        c.r1 == num_if::u64s(c.np, num_if::P_UOM_RUNS)[u + 1] as int,
    ensures
        final(stores)@ == old(stores)@, inputs_ok(c, r.0, r.1, p1), ctx_ok(c),
        r.1.name_off@ == crate::stores::sub_fy::interface::common::text::u64_part(c.sp[sub_if::P_NAME_DICT_OFF as int]),
        r.1.name_bytes@ == crate::stores::sub_fy::interface::common::text::u8_part(c.sp[sub_if::P_NAME_DICT_BYTES as int]),
        r.1.n_names == name_count(c.sp),
{
    let (ni, r0, r1) = read_num(&mut stores.num, u);
    let si = read_sub(&mut stores.sub_fy);
    proof {
        assert(ctx_ok(c));
    }
    (ni, si)
}

// ------------------------------------------------------------------------------------------------ the fiscal-year range

/// The `fy` sort words of the fiscal-year order do not decrease.
proof fn lemma_words_sorted(c: ScanCtx, p: int, q: int)
    requires ctx_ok(c), 0 <= p <= q < n_sub(c),
    ensures word_at(c, p) <= word_at(c, q),
{
    if p < q {
        assert(sub_if::key_le(sub_if::row_key(c.sp, sub_if::fy_order(c.sp)[p] as int),
            sub_if::row_key(c.sp, sub_if::fy_order(c.sp)[q] as int)));
    }
}

/// The first position of the fiscal-year order whose `fy` sort word is at least `w`.
pub fn lower_fy(si: &SubIn, w: u64, Ghost(c): Ghost<ScanCtx>) -> (r: usize)
    requires
        ctx_ok(c), si.ns == n_sub(c),
        si.fy_order@ == sub_if::fy_order(c.sp),
        si.fy@ == i32_part(c.sp[sub_if::P_FY as int]),
        si.fy_valid@ == u8_part(c.sp[sub_if::P_FY_VALID as int]),
    ensures
        r <= si.ns,
        forall|q: int| 0 <= q < r ==> #[trigger] word_at(c, q) < w,
        forall|q: int| r <= q < si.ns ==> #[trigger] word_at(c, q) >= w,
{
    proof {
        crate::stores::sub_fy::interface::common::perm::lemma_permutation_facts(sub_if::fy_order(c.sp), n_sub(c) as nat);
    }
    let mut lo: usize = 0;
    let mut hi: usize = si.ns;
    while lo < hi
        invariant
            ctx_ok(c), si.ns == n_sub(c), lo <= hi <= si.ns,
            si.fy_order@ == sub_if::fy_order(c.sp),
            si.fy@ == i32_part(c.sp[sub_if::P_FY as int]),
            si.fy_valid@ == u8_part(c.sp[sub_if::P_FY_VALID as int]),
            sub_if::fy_order(c.sp).len() == n_sub(c),
            forall|i: int| 0 <= i < n_sub(c) ==> #[trigger] sub_if::fy_order(c.sp)[i] < n_sub(c),
            forall|q: int| 0 <= q < lo ==> #[trigger] word_at(c, q) < w,
            forall|q: int| hi <= q < si.ns ==> #[trigger] word_at(c, q) >= w,
        decreases hi - lo,
    {
        let mid = lo + (hi - lo) / 2;
        let j = si.fy_order[mid] as usize;
        let word: u64 = if si.fy_valid[j] == 0 { 0 } else { (si.fy[j] as i64 + 0x8000_0001) as u64 };
        assert(word as int == word_at(c, mid as int));
        if word < w {
            proof {
                assert forall|q: int| 0 <= q < mid + 1 implies #[trigger] word_at(c, q) < w by {
                    lemma_words_sorted(c, q, mid as int);
                }
            }
            lo = mid + 1;
        } else {
            proof {
                assert forall|q: int| mid <= q < si.ns implies #[trigger] word_at(c, q) >= w by {
                    lemma_words_sorted(c, mid as int, q);
                }
            }
            hi = mid;
        }
    }
    lo
}

/// Positions whose row has another `fy` sort word than `$2`'s do not qualify.
proof fn lemma_off_range(c: ScanCtx, q: int)
    requires ctx_ok(c), 0 <= q < n_sub(c), word_at(c, q) != fy_target(c.p1),
    ensures !qualifies(c, row_at(c, q)),
{
    crate::stores::sub_fy::interface::common::perm::lemma_permutation_facts(sub_if::fy_order(c.sp), n_sub(c) as nat);
    assert(0 <= row_at(c, q) < n_sub(c));
}

/// A range of positions without a qualifying row has no filings and no big filing.
proof fn lemma_filt_none(c: ScanCtx, lo: int, hi: int)
    requires lo <= hi, forall|q: int| lo <= q < hi ==> !qualifies(c, #[trigger] row_at(c, q)),
    ensures filt(c, lo, hi) == Seq::<Filing>::empty(), none_big(c, lo, hi),
    decreases hi - lo,
{
    if lo < hi {
        lemma_filt_none(c, lo, hi - 1);
        lemma_filt_step(c, lo, hi - 1);
        assert(!qualifies(c, row_at(c, hi - 1)));
        assert(filt(c, lo, hi) =~= Seq::<Filing>::empty());
    }
}

/// The filings of the fiscal-year range `[a, b)` are all the filings.
proof fn lemma_range_all(c: ScanCtx, a: int, b: int)
    requires
        ctx_ok(c), 0 <= a <= b <= n_sub(c),
        forall|q: int| 0 <= q < a ==> #[trigger] word_at(c, q) < fy_target(c.p1),
        forall|q: int| b <= q < n_sub(c) ==> #[trigger] word_at(c, q) >= fy_target(c.p1) + 1,
    ensures
        filt(c, a, b) == filt(c, 0, n_sub(c)),
        none_big(c, a, b) ==> none_big(c, 0, n_sub(c)),
{
    let n = n_sub(c);
    assert forall|q: int| 0 <= q < a implies !qualifies(c, #[trigger] row_at(c, q)) by {
        assert(word_at(c, q) < fy_target(c.p1));
        lemma_off_range(c, q);
    }
    assert forall|q: int| b <= q < n implies !qualifies(c, #[trigger] row_at(c, q)) by {
        assert(word_at(c, q) >= fy_target(c.p1) + 1);
        lemma_off_range(c, q);
    }
    lemma_filt_none(c, 0, a);
    lemma_filt_none(c, b, n);
    crate::agent::link::lemma_filt_append(c, 0, a, b);
    crate::agent::link::lemma_filt_append(c, 0, b, n);
    assert(filt(c, 0, b) =~= filt(c, a, b));
    assert(filt(c, 0, n) =~= filt(c, 0, b));
    if none_big(c, a, b) {
        assert forall|q: int| 0 <= q < n implies !#[trigger] big(c, row_at(c, q)) by {
            if q < a {
                assert(!qualifies(c, row_at(c, q)));
            } else if q >= b {
                assert(!qualifies(c, row_at(c, q)));
            } else {
                assert(!big(c, row_at(c, q)));
            }
        }
    }
}

// ------------------------------------------------------------------------------------------------ the run map

/// The run map of the uom range (`run_map_ok`): one entry per adsh code, `nr` where no run has the code, else the
/// run's position in the range. One pass over the range's runs (their codes strictly increase, so no entry is
/// written twice).
pub fn build_run_map(ni: &NumIn, Ghost(c): Ghost<ScanCtx>) -> (map: Vec<u64>)
    requires
        ctx_ok(c), ni.nr == c.r1 - c.r0, ni.dict_count == adsh_count(c.np),
        ni.run_adsh@ == u64s(c.np, num_if::P_RUN_ADSH).subrange(c.r0, c.r1),
    ensures run_map_ok(c, map@),
{
    proof { lemma_range(c); }
    let ghost ra = u64s(c.np, num_if::P_RUN_ADSH);
    let nr = ni.nr;
    let mut map: Vec<u64> = crate::gendb_entry::work::filled(ni.dict_count, nr as u64);
    let mut r: usize = 0;
    while r < nr
        invariant
            ctx_ok(c), r <= nr, nr == c.r1 - c.r0, 0 <= c.r0 <= c.r1 <= num_if::run_count(c.np),
            ra == u64s(c.np, num_if::P_RUN_ADSH), ni.run_adsh@ == ra.subrange(c.r0, c.r1),
            map@.len() == adsh_count(c.np), ni.dict_count == adsh_count(c.np),
            forall|t: int| c.r0 <= t < c.r0 + r ==> map@[#[trigger] ra[t] as int] == t - c.r0,
        decreases nr - r,
    {
        proof {
            assert(u64s(c.np, num_if::P_RUN_UOM)[c.r0 + r] < uom_count(c.np));
            assert(ra[c.r0 + r] < adsh_count(c.np));
        }
        let k = ni.run_adsh[r] as usize;
        map[k] = r as u64;
        proof {
            assert forall|t: int| c.r0 <= t < c.r0 + r + 1 implies map@[#[trigger] ra[t] as int] == t - c.r0 by {
                if t < c.r0 + r {
                    lemma_codes_increase(c, t, c.r0 + r);
                }
            }
        }
        r = r + 1;
    }
    map
}

// ------------------------------------------------------------------------------------------------ the scan

/// Positions of the fiscal-year range per scan task (at least).
pub const SCAN_ROWS: usize = 256;

/// Scan tasks per call (at most) when the unit's run range is light: each thread costs about 40 us of spawning on the
/// calling thread, so a few large tasks beat many small ones.
pub const SCAN_TASKS_LIGHT: usize = 16;

/// Scan tasks per call (at most) when the unit's run range holds at least `HEAVY_VALUES` values: summing them is
/// bound by memory bandwidth, which more threads raise.
pub const SCAN_TASKS_HEAVY: usize = 32;

/// Values (stored `num` rows) of a unit's run range from which it counts as heavy.
pub const HEAVY_VALUES: usize = 16_000_000;

/// The result of the scan task of positions `[lo, hi)`.
#[verifier::opaque]
pub open spec fn task_result(c: ScanCtx, lo: int, hi: int, out: (TaskBuffer<Filing>, bool)) -> bool {
    &&& out.0.wf()
    &&& !out.1 ==> out.0.view() == filt(c, lo, hi) && none_big(c, lo, hi)
    &&& out.1 ==> exists|p: int| lo <= p < hi && #[trigger] big(c, row_at(c, p))
}

/// A task's postcondition is its result.
proof fn lemma_task_result(t: ScanTask, out: (TaskBuffer<Filing>, bool))
    requires t.post(out),
    ensures task_result(t.ctx@, t.lo as int, t.hi as int, out),
{
    reveal(task_result);
}

/// Appending the filings of `[done, hi)` to those of `[a, done)`.
proof fn lemma_collect_step(c: ScanCtx, a: int, done: int, hi: int, before: Seq<Filing>, out: (TaskBuffer<Filing>, bool),
    v: Seq<Filing>)
    requires
        a <= done <= hi, before == filt(c, a, done), none_big(c, a, done),
        task_result(c, done, hi, out), !out.1, v == out.0.view(),
    ensures before + v == filt(c, a, hi), none_big(c, a, hi),
{
    reveal(task_result);
    crate::agent::link::lemma_filt_append(c, a, done, hi);
    assert forall|q: int| a <= q < hi implies !#[trigger] big(c, row_at(c, q)) by {
        if q < done {
            assert(!big(c, row_at(c, q)));
        }
    }
}

/// A task without a big filing: its buffer lists the filings of its range.
proof fn lemma_task_ok(c: ScanCtx, lo: int, hi: int, out: (TaskBuffer<Filing>, bool))
    requires task_result(c, lo, hi, out), !out.1,
    ensures out.0.wf(), out.0.view() == filt(c, lo, hi),
{
    reveal(task_result);
}

/// A task that reports a big filing.
proof fn lemma_collect_big(c: ScanCtx, lo: int, hi: int, out: (TaskBuffer<Filing>, bool))
    requires task_result(c, lo, hi, out), out.1, 0 <= lo, hi <= n_sub(c),
    ensures exists|p: int| 0 <= p < n_sub(c) && #[trigger] big(c, row_at(c, p)),
{
    reveal(task_result);
    let p = choose|p: int| lo <= p < hi && #[trigger] big(c, row_at(c, p));
}

/// The boundary between scan tasks `i - 1` and `i` of the range `[a, a + m)` (`a + m` after the last): the
/// fraction `f(x) = x (3 + x) / 4` of `m` at `x = i / ntasks`. Task `i` gets about `(3 + 2x) / 4` of the mean share of
/// positions, so the first tasks get fewer: the fiscal-year order runs by cik, and filings of low ciks (older,
/// larger filers) carry more values per filing (measured: equal shares left the first tasks last to finish).
pub open spec fn bnd(a: int, i: int, ntasks: int, m: int) -> int {
    if i >= ntasks { a + m } else { a + (m * i * (3 * ntasks + i)) / (4 * ntasks * ntasks) }
}

/// The boundaries start at `a`, never decrease and stay within `[a, a + m]`.
proof fn lemma_bnd(a: int, i: int, ntasks: int, m: int)
    requires 0 <= i < ntasks, m >= 0,
    ensures
        bnd(a, 0, ntasks, m) == a,
        a <= bnd(a, i, ntasks, m) <= bnd(a, i + 1, ntasks, m) <= a + m,
{
    let d = 4 * ntasks * ntasks;
    let n0 = m * i * (3 * ntasks + i);
    let n1 = m * (i + 1) * (3 * ntasks + i + 1);
    let top = m * d;
    assert(d > 0) by (nonlinear_arith) requires ntasks >= 1, d == 4 * ntasks * ntasks;
    assert(0 <= n0 <= n1 <= top) by (nonlinear_arith)
        requires 0 <= i < ntasks, m >= 0, n0 == m * i * (3 * ntasks + i), n1 == m * (i + 1) * (3 * ntasks + i + 1),
            top == m * d, d == 4 * ntasks * ntasks;
    assert(m * 0 * (3 * ntasks + 0) == 0) by (nonlinear_arith);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(n0, n1, d);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(n1, top, d);
    vstd::arithmetic::div_mod::lemma_div_multiples_vanish(m, d);
    vstd::arithmetic::div_mod::lemma_div_pos_is_pos(n0, d);
    assert(top / d == m);
}

/// `bnd(a, i, ntasks, m)` for a task `i < ntasks` (computed in 128 bits: no overflow for any `m`).
fn task_bound(a: usize, m: usize, i: usize, ntasks: usize) -> (r: usize)
    requires 1 <= ntasks <= MAX_WORKERS, i < ntasks, a + m <= usize::MAX,
    ensures r as int == bnd(a as int, i as int, ntasks as int, m as int),
{
    proof { lemma_bnd(a as int, i as int, ntasks as int, m as int); }
    let w = (3 * ntasks + i) as u128;
    assert((m as u128) * (i as u128) <= 0x1_0000_0000_0000_0000u128 * 64) by (nonlinear_arith)
        requires m <= usize::MAX, i < 64;
    let mi = (m as u128) * (i as u128);
    assert(mi * w <= 0x1_0000_0000_0000_0000u128 * 64 * 256) by (nonlinear_arith)
        requires mi <= 0x1_0000_0000_0000_0000u128 * 64, w < 256;
    let num = mi * w;
    let nt = ntasks as u128;
    assert(4 * nt * nt <= 4 * 64 * 64 && 4 * nt * nt >= 4) by (nonlinear_arith) requires 1 <= nt <= 64;
    let d = 4 * nt * nt;
    let q = num / d;
    assert(num as int == (m as int) * (i as int) * (3 * (ntasks as int) + (i as int)));
    assert(d as int == 4 * (ntasks as int) * (ntasks as int));
    a + q as usize
}

/// The parallel scan of the fiscal-year range of `$2`: all qualifying filings in fiscal-year order (sorted by
/// cik, name code, row), or a big filing.
pub fn scan_all(ni: &NumIn, si: &SubIn, p1: i64, workers: usize, dispatch: &mut Dispatch, Ghost(c): Ghost<ScanCtx>)
    -> (r: Result<Result<Vec<Filing>, ()>, QueryError>)
    requires inputs_ok(c, *ni, *si, p1), 1 <= workers <= MAX_WORKERS, -0x8000_0000 <= p1 < 0x8000_0000,
    ensures
        r matches Ok(Ok(f)) ==> f@ == filt(c, 0, n_sub(c)) && none_big(c, 0, n_sub(c)),
        r matches Ok(Err(_)) ==> exists|p: int| 0 <= p < n_sub(c) && #[trigger] big(c, row_at(c, p)),
        r matches Err(e) ==> e is WorkerFailed,
{
    hide(crate::stores::num::interface::num_layout_ok);
    hide(crate::stores::sub_fy::interface::sub_layout_ok);
    let ns = si.ns;
    proof {
        reveal(crate::stores::sub_fy::interface::sub_layout_ok);
        assert(ctx_ok(c));
    }
    // ---- the positions with `fy = $2`
    let w = (p1 + 0x8000_0001) as u64;
    let a = lower_fy(si, w, Ghost(c));
    let b = lower_fy(si, w + 1, Ghost(c));
    proof {
        if b < a {
            assert(word_at(c, b as int) >= w + 1);
            assert(word_at(c, b as int) < w);
        }
        lemma_range_all(c, a as int, b as int);
    }
    proof {
        assert forall|q: int| a <= q < b implies #[trigger] word_at(c, q) == fy_target(c.p1) by {
            assert(word_at(c, q) >= w && word_at(c, q) < w + 1);
        }
    }
    let m = b - a;
    let mut ntasks = m / SCAN_ROWS;
    if ntasks > workers { ntasks = workers; }
    let max_tasks = if ni.values.len() >= HEAVY_VALUES { SCAN_TASKS_HEAVY } else { SCAN_TASKS_LIGHT };
    if ntasks > max_tasks { ntasks = max_tasks; }
    if ntasks == 0 { ntasks = 1; }
    // ---- one task: the serial three-pass scan on the calling thread (no thread spawned)
    if ntasks == 1 {
        let map = build_run_map(ni, Ghost(c));
        proof {
            assert(crate::agent::serial::range_ok(c, a as int, m as int));
        }
        return match crate::agent::serial::scan_serial(ni, si, p1, a, m, &map, Ghost(c)) {
            Ok(f) => Ok(Ok(f)),
            Err(_) => {
                proof {
                    let p = choose|p: int| a <= p < a + m && #[trigger] big(c, row_at(c, p));
                    assert(0 <= p < n_sub(c) && big(c, row_at(c, p)));
                }
                Ok(Err(()))
            },
        };
    }
    let run_map = Arc::new(build_run_map(ni, Ghost(c)));
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut lo: usize = a;
    proof { lemma_bnd(a as int, 0, ntasks as int, m as int); }
    let mut ci: usize = 0;
    while ci < ntasks
        invariant
            1 <= ntasks <= workers <= MAX_WORKERS, ci <= ntasks, ns == si.ns,
            a + m == b, b <= ns,
            tasks.len() == ci,
            lo as int == bnd(a as int, ci as int, ntasks as int, m as int),
            inputs_ok(c, *ni, *si, p1),
            forall|q: int| a <= q < b ==> #[trigger] word_at(c, q) == fy_target(c.p1),
            c.p1 == p1 as int, -0x8000_0000 <= p1 < 0x8000_0000,
            run_map_ok(c, run_map@),
            forall|k: int| 0 <= k < ci ==> (#[trigger] tasks@[k]).pre() && tasks@[k].ctx@ == c,
            forall|k: int| 0 <= k < ci ==> (#[trigger] tasks@[k]).lo == bnd(a as int, k, ntasks as int, m as int)
                && tasks@[k].hi == bnd(a as int, k + 1, ntasks as int, m as int),
        decreases ntasks - ci,
    {
        proof { lemma_bnd(a as int, ci as int, ntasks as int, m as int); }
        let hi = if ci + 1 == ntasks { b } else { task_bound(a, m, ci + 1, ntasks) };
        proof {
            assert(a <= lo && lo <= hi && hi <= b);
            assert forall|q: int| lo <= q < hi implies #[trigger] word_at(c, q) == fy_target(c.p1) by {}
        }
        let t = ScanTask {
            lo, hi, fy_order: si.fy_order, adsh_rank: si.adsh_rank, sub_adsh_off: si.adsh_off, sub_adsh_bytes: si.adsh_bytes, sub_rows: ns,
            fy: si.fy, fy_valid: si.fy_valid, cik: si.cik, name_codes: si.name_codes, p1, run_adsh: ni.run_adsh,
            run_start: ni.run_start, run_map: run_map.clone(), nr: ni.nr, dict_off: ni.dict_off, dict_bytes: ni.dict_bytes,
            dict_count: ni.dict_count, values: ni.values, v_lo: ni.v_lo,
            out: TaskBuffer::new(hi - lo, Filing { cik: 0, name: 0, sum: 0, mass: 0 }),
            ctx: Ghost(c),
        };
        tasks.push(t);
        lo = hi;
        ci = ci + 1;
    }
    let ghost ts = tasks@;
    let ghost (ga, gn, gm) = (a as int, ntasks as int, m as int);
    proof {
        assert forall|i: int| 0 <= i < ntasks implies (#[trigger] ts[i]).lo == bnd(ga, i, gn, gm)
            && ts[i].hi == bnd(ga, i + 1, gn, gm) && ts[i].lo <= ts[i].hi && ts[i].hi <= ns by {
            lemma_bnd(ga, i, gn, gm);
        }
        lemma_bnd(ga, 0, gn, gm);
    }
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(f) => return Err(QueryError::WorkerFailed(f)),
    };
    let ghost touts = outs@;
    proof {
        assert forall|i: int| 0 <= i < ntasks implies #[trigger] task_result(c, ts[i].lo as int, ts[i].hi as int, touts[i]) by {
            lemma_task_result(ts[i], touts[i]);
        }
        assert(ns == n_sub(c));
        assert(filt(c, ga, ga) =~= Seq::<Filing>::empty());
    }
    let mut outs = outs;
    let mut filings: Vec<Filing> = Vec::with_capacity(m);
    let mut k: usize = 0;
    while k < ntasks
        invariant
            k <= ntasks, outs@ == touts.subrange(k as int, ntasks as int), touts.len() == ntasks, ts.len() == ntasks,
            ns == n_sub(c), 1 <= ntasks, ga == a, gn == ntasks, gm == m, a + m == b, b <= ns,
            forall|i: int| 0 <= i < ntasks ==> #[trigger] task_result(c, ts[i].lo as int, ts[i].hi as int, touts[i]),
            forall|i: int| 0 <= i < ntasks ==> (#[trigger] ts[i]).lo == bnd(ga, i, gn, gm)
                && ts[i].hi == bnd(ga, i + 1, gn, gm) && ts[i].lo <= ts[i].hi && ts[i].hi <= ns,
            bnd(ga, 0, gn, gm) == ga,
            filings@ == filt(c, ga, bnd(ga, k as int, gn, gm)),
            none_big(c, ga, bnd(ga, k as int, gn, gm)),
            ga <= bnd(ga, k as int, gn, gm),
        decreases ntasks - k,
    {
        let ghost done = bnd(ga, k as int, gn, gm);
        let ghost upto = bnd(ga, k + 1, gn, gm);
        assert(ts[k as int].lo == done && ts[k as int].hi == upto);
        assert(outs@[0] == touts[k as int]);
        let (buf, over) = outs.remove(0);
        if over {
            proof { lemma_collect_big(c, done, upto, (buf, over)); }
            return Ok(Err(()));
        }
        proof { lemma_task_ok(c, done, upto, (buf, over)); }
        let ghost bv = buf.view();
        let mut v = buf.into_vec();
        let ghost before = filings@;
        filings.append(&mut v);
        proof {
            lemma_collect_step(c, ga, done, upto, before, (buf, over), bv);
        }
        k = k + 1;
        proof {
            assert(outs@ =~= touts.subrange(k as int, ntasks as int));
        }
    }
    proof {
        assert(bnd(ga, ntasks as int, gn, gm) == b);
    }
    Ok(Ok(filings))
}

// ------------------------------------------------------------------------------------------------ totals, HAVING, rows

/// The total of the per-cik sums, or a prefix of them whose absolute mass exceeds `i128::MAX`.
pub fn cik_totals(cg: &Groups) -> (r: Result<i128, usize>)
    ensures
        r matches Ok(t) ==> t as int == rsum(0, cg.sum@.len() as int, |i: int| cg.sum@[i] as int)
            && -(i128::MAX as int) <= t as int <= i128::MAX as int,
        r matches Err(h0) ==> 0 < h0 <= cg.sum@.len()
            && rsum(0, h0 as int, |i: int| abs(cg.sum@[i] as int)) > i128::MAX as int,
{
    let nc = cg.sum.len();
    let mut total: i128 = 0;
    let mut avg_mass: u128 = 0;
    let mut h: usize = 0;
    while h < nc
        invariant
            h <= nc, nc == cg.sum@.len(),
            total as int == rsum(0, h as int, |i: int| cg.sum@[i] as int),
            avg_mass as int == rsum(0, h as int, |i: int| abs(cg.sum@[i] as int)),
            avg_mass <= i128::MAX as u128,
            total as int <= avg_mass as int, -(total as int) <= avg_mass as int,
        decreases nc - h,
    {
        let s = cg.sum[h];
        let am = avg_mass + abs_u128(s);
        proof {
            lemma_rsum_step(0, h as int, |i: int| cg.sum@[i] as int);
            lemma_rsum_step(0, h as int, |i: int| abs(cg.sum@[i] as int));
        }
        if am > i128::MAX as u128 {
            return Err(h + 1);
        }
        avg_mass = am;
        total = total + s;
        h = h + 1;
    }
    Ok(total)
}

/// The groups kept by HAVING `sum > avg` (`Num { avg_c, avg_s }`), as `(sum, index)` in group order.
pub fn having(g: &Groups, avg_c: i128, avg_s: u32) -> (kept: Vec<SumRef>)
    ensures kept@ == kept_upto(*g, avg_c as int, avg_s as nat, g.sum@.len() as int),
{
    let ng = g.sum.len();
    let mut kept: Vec<SumRef> = Vec::new();
    let mut h: usize = 0;
    while h < ng
        invariant
            h <= ng, ng == g.sum@.len(),
            kept@ == kept_upto(*g, avg_c as int, avg_s as nat, h as int),
        decreases ng - h,
    {
        if num_cmp_exec(g.sum[h], 4, avg_c, avg_s) > 0 {
            kept.push(SumRef { sum: g.sum[h], idx: h as u64 });
            proof {
                assert(kept_upto(*g, avg_c as int, avg_s as nat, h + 1)
                    =~= kept_upto(*g, avg_c as int, avg_s as nat, h as int).push(SumRef { sum: g.sum@[h as int], idx: h as u64 }));
            }
        } else {
            proof {
                assert(kept_upto(*g, avg_c as int, avg_s as nat, h + 1) =~= kept_upto(*g, avg_c as int, avg_s as nat, h as int));
            }
        }
        h = h + 1;
    }
    kept
}

/// Output rows.
pub const LIMIT: usize = 100;

/// The first 100 sorted groups as answer rows: name text, cik, sum at scale 4.
pub fn output_rows(kept: &Vec<SumRef>, g: &Groups, si: &SubIn, Ghost(sp): Ghost<Seq<PartView>>) -> (rows: Vec<Vec<EVal>>)
    requires
        sub_if::sub_layout_ok(sp),
        si.name_off@ == crate::stores::sub_fy::interface::common::text::u64_part(sp[sub_if::P_NAME_DICT_OFF as int]),
        si.name_bytes@ == crate::stores::sub_fy::interface::common::text::u8_part(sp[sub_if::P_NAME_DICT_BYTES as int]),
        si.n_names == name_count(sp),
        forall|i: int| 0 <= i < kept@.len() ==> (#[trigger] kept@[i]).idx < g.sum@.len(),
        forall|h: int| 0 <= h < g.sum@.len() ==> #[trigger] key_valid(sp, hkey(*g, h, true), true),
        g.cik@.len() == g.sum@.len(), g.name@.len() == g.sum@.len(),
    ensures
        view_rows(rows@) == crate::spec::order::slice_rows(kept@.map_values(rr_of(sp, *g)), 0, Some(100nat)),
{
    let ng = g.sum.len();
    let n_out = if kept.len() < LIMIT { kept.len() } else { LIMIT };
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut q: usize = 0;
    while q < n_out
        invariant
            ng == g.sum@.len(),
            q <= n_out <= kept@.len(), n_out <= LIMIT,
            n_out == if kept@.len() < LIMIT { kept@.len() } else { LIMIT as nat },
            forall|i: int| 0 <= i < kept@.len() ==> (#[trigger] kept@[i]).idx < g.sum@.len(),
            forall|h: int| 0 <= h < g.sum@.len() ==> #[trigger] key_valid(sp, hkey(*g, h, true), true),
            g.cik@.len() == g.sum@.len(), g.name@.len() == g.sum@.len(),
            sub_if::sub_layout_ok(sp),
            si.name_off@ == crate::stores::sub_fy::interface::common::text::u64_part(sp[sub_if::P_NAME_DICT_OFF as int]),
            si.name_bytes@ == crate::stores::sub_fy::interface::common::text::u8_part(sp[sub_if::P_NAME_DICT_BYTES as int]),
            si.n_names == name_count(sp),
            view_rows(rows@) == kept@.subrange(0, q as int).map_values(rr_of(sp, *g)),
        decreases n_out - q,
    {
        let gi = kept[q].idx as usize;
        assert(gi as int == kept@[q as int].idx as int);
        assert(key_valid(sp, hkey(*g, gi as int, true), true));
        let (nb, _) = text_entry_of(si.name_off, si.name_bytes, si.n_names, g.name[gi] as usize);
        let mut row: Vec<EVal> = Vec::new();
        row.push(EVal::Text(vstd::slice::slice_to_vec(nb)));
        row.push(EVal::Int(g.cik[gi] as i64 - 0x8000_0000));
        row.push(EVal::Num { coeff: g.sum[gi], scale: 4 });
        let ghost before = rows@;
        rows.push(row);
        proof {
            assert(view_row(row@) =~= rr(sp, *g, gi as int));
            assert(view_rows(rows@) =~= view_rows(before).push(view_row(row@)));
            assert(kept@.subrange(0, q + 1).map_values(rr_of(sp, *g))
                =~= kept@.subrange(0, q as int).map_values(rr_of(sp, *g)).push(rr(sp, *g, gi as int)));
        }
        q = q + 1;
    }
    proof {
        assert(view_rows(rows@) =~= crate::spec::order::slice_rows(kept@.map_values(rr_of(sp, *g)), 0, Some(100nat)));
    }
    rows
}

} // verus!
