// AUTHOR MODULE ROOT (crate::agent). You own every file under src/agent/.
//! TPC-H Q12 (shipping modes and order priority) over storage `li_okmode` (storage `facts`' parts, kept unchanged
//! through `li_okruns`, the l_orderkey run starts, and bitmaps of run starts and of l_shipmode entries); `facts` and
//! `li_okruns` are listed for their interfaces.
//!
//! Plan: orders are stored by o_orderdate and lineitem rows are stored grouped by their order in the same order
//! (checked co-clustering flag), with receipt-date zone maps per lineitem group. The query
//! 1. computes the receipt-date window `[lo, hi]` in days (`hi`: the last day before `$3 + 1 year`, as SQL compares
//!    the date with that timestamp), the l_shipmode dictionary entries of `$1` and `$2` and the o_orderpriority
//!    entries `'1-URGENT'` and `'2-HIGH'` (`make_win`);
//! 2. checks whether the bitmap path applies (`open_fast`: as many l_orderkey runs as orders and the last keys
//!    equal, so run `k` is orders row `k`; bitmaps present for both selected modes; flat priority bases);
//! 3. narrows the lineitem groups to `[ga, gb)` by the receipt-date zone maps (`candidate_groups`);
//! 4. splits them evenly into scan tasks (`kernel::ScanTask`): each evaluates the lineitem conditions per row (date
//!    codes, and the ship-mode bitmaps on the bitmap path) and finds the order of every qualifying line by its run
//!    rank (bitmap path) or a forward cursor over the stored orders rows, counting high and low priority lines per
//!    ship-mode entry;
//! 5. sums the task counts and answers one row per ship-mode entry with a qualifying line, in dictionary order
//!    (bytewise, the ORDER BY order).
//! Proof: `model` (scan model), `kernel` and `runs` (scan), `bind` (model = stored rows), `sql` (SQL meaning in
//! normal form over the product of the stored relations), `joinsum` (the normal form's group sums = the model's
//! per-line counts), `answer` (rows and errors are allowed outcomes; the storage facts in model terms).
use vstd::prelude::*;
use crate::gendb_entry::{Answer, answer_meets, bound_db, stores_ready};
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::{QueryError, WorkerFailure};
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::work::filled;
use crate::gendb_params::Params;
use crate::query::{param_domain, param_typed};
use crate::spec::value::*;
use crate::spec::datetime::*;
use crate::spec::limits::int8_max;
use crate::exec::value::{EVal, view_row};
use crate::exec::datetime::{date_from_civil_exec, date_to_ts_exec, ts_add_interval_exec, floor_divmod};
use crate::stores::facts::interface::*;
use crate::stores::li_okruns::interface::RUN_STARTS;
use crate::stores::li_okmode::interface::{OKM_LAYOUT, RUN_BITS, MODE_BITS};
use crate::stores::facts::interface::common::colfmt::*;
use crate::stores::facts::interface::common::read::{dict_find, text_slice};

pub mod common;
pub mod model;
pub mod kernel;
pub mod runs;
pub mod sql;
pub mod bind;
pub mod joinsum;
pub mod answer;

use model::*;
use kernel::*;
use runs::*;
use common::bits::{tz_table, tz_table_ok};
use sql::*;
use bind::*;
use joinsum::*;
use answer::*;

verus! {

// ------------------------------------------------------------------------------------------------ parameters

/// The receipt-date window: `$3` in days, and the last day before `$3 + 1 year` (or the error computing that
/// timestamp).
fn date_window(params: &Params) -> (r: (i64, Result<i64, SqlError>))
    requires param_typed(params@),
    ensures
        r.0 as int == lo_of(params@),
        match r.1 {
            Ok(h) => hi_ok(lo_of(params@), h as int),
            Err(e) => hi_value(lo_of(params@)) == Err::<int, SqlError>(e),
        },
{
    let ghost ps = params@;
    proof {
        lemma_lit(ps);
        assert(days_in_month(params.p2.y as int, params.p2.m as int) <= 31);
    }
    let lo = date_from_civil_exec(params.p2.y as i64, params.p2.m as i64, params.p2.d as i64);
    let t0 = match date_to_ts_exec(lo as i32) {
        Ok(t) => t,
        Err(e) => return (lo, Err(e)),
    };
    let t1 = match ts_add_interval_exec(t0, 12, 0, 0) {
        Ok(t) => t,
        Err(e) => return (lo, Err(e)),
    };
    let (q, _) = floor_divmod(t1 - 1, 86_400_000_000i64);
    (lo, Ok(q))
}

/// `s` is the dictionary entry holding `needle`, or `u64::MAX` when no entry does.
pub open spec fn opt_ok(offs: Seq<u64>, bytes: Seq<u8>, needle: Seq<u8>, s: u64) -> bool {
    &&& s != u64::MAX ==> s < offs.len() - 1 && text_of(offs, bytes, s as int) == needle
    &&& s == u64::MAX ==> forall|x: int| 0 <= x < offs.len() - 1 ==> text_of(offs, bytes, x) != needle
}

/// The dictionary entry holding `needle`, or `u64::MAX`.
fn opt_entry(offs: &[u64], bytes: &[u8], needle: &[u8]) -> (r: u64)
    requires dict_ok(offs@, bytes@),
    ensures opt_ok(offs@, bytes@, needle@, r),
{
    let k = offs.len() - 1;
    match dict_find(offs, bytes, k, needle, needle.len()) {
        Some(x) => x as u64,
        None => u64::MAX,
    }
}

/// Entry `e` is the entry `s` found for `needle` exactly when it holds `needle` (entries are distinct).
proof fn lemma_entry_is(offs: Seq<u64>, bytes: Seq<u8>, needle: Seq<u8>, s: u64, e: int)
    requires
        dict_ok(offs, bytes),
        opt_ok(offs, bytes, needle, s),
        offs.len() - 1 < u64::MAX,
        0 <= e < offs.len() - 1,
    ensures (e == s) == (text_of(offs, bytes, e) == needle),
{
    if text_of(offs, bytes, e) == needle && e != s {
        assert(s != u64::MAX);
        lemma_dict_distinct(offs, bytes, offs.len() - 1, e, s as int);
    }
}

/// `'1-URGENT'`.
fn urgent_bytes() -> (v: Vec<u8>)
    ensures v@ == urgent(),
{
    let mut v: Vec<u8> = Vec::new();
    v.push(49u8); v.push(45u8); v.push(85u8); v.push(82u8); v.push(71u8); v.push(69u8); v.push(78u8); v.push(84u8);
    assert(v@ =~= urgent());
    v
}

/// `'2-HIGH'`.
fn high_bytes() -> (v: Vec<u8>)
    ensures v@ == high2(),
{
    let mut v: Vec<u8> = Vec::new();
    v.push(50u8); v.push(45u8); v.push(72u8); v.push(73u8); v.push(71u8); v.push(72u8);
    assert(v@ =~= high2());
    v
}

/// The scan window of the bound parameters: receipt days `[lo, hi]`, the ship-mode entries of `$1` and `$2` (the
/// second dropped when it is the first) and the high priority entries.
fn make_win(po: &[u64], py: &[u8], mo: &[u64], my: &[u8], params: &Params, lo: i64, hi: i64) -> (w: Win)
    requires
        dict_ok(po@, py@),
        dict_ok(mo@, my@),
        po@.len() - 1 < u64::MAX,
        mo@.len() - 1 < u64::MAX,
        lo as int == lo_of(params@),
    ensures
        win_ok(w),
        win_matches(w, prm_of(params@, hi as int), po@, py@, mo@, my@),
{
    let ghost prm = prm_of(params@, hi as int);
    let s0 = opt_entry(mo, my, params.p0);
    let s1a = opt_entry(mo, my, params.p1);
    let s1 = if s1a == s0 { u64::MAX } else { s1a };
    let ub = urgent_bytes();
    let hb = high_bytes();
    let u0 = opt_entry(po, py, ub.as_slice());
    let u1 = opt_entry(po, py, hb.as_slice());
    let w = Win { lo, hi, s0, s1, u0, u1 };
    proof {
        assert(prm.p0 == params.p0@ && prm.p1 == params.p1@);
        assert forall|e: int| 0 <= e < mo@.len() - 1 implies
            ((e == w.s0 || e == w.s1) <==> (#[trigger] text_of(mo@, my@, e) == prm.p0 || text_of(mo@, my@, e) == prm.p1)) by {
            lemma_entry_is(mo@, my@, params.p0@, s0, e);
            lemma_entry_is(mo@, my@, params.p1@, s1a, e);
        }
        assert forall|e: int| 0 <= e < po@.len() - 1 implies
            (phigh(w, e) <==> (#[trigger] text_of(po@, py@, e) == urgent() || text_of(po@, py@, e) == high2())) by {
            lemma_entry_is(po@, py@, urgent(), u0, e);
            lemma_entry_is(po@, py@, high2(), u1, e);
        }
    }
    w
}

// ------------------------------------------------------------------------------------------------ the model

/// A group size for the model that decodes like the stored one on `n` rows (`bind::bs_ok`).
fn model_bs(stored: u64, n: usize) -> (b: usize)
    requires stored >= 1,
    ensures bs_ok(b as int, stored as int, n as int),
{
    if stored <= n as u64 {
        stored as usize
    } else if n > 0 {
        n
    } else {
        1
    }
}

/// The scan model's columns as whole parts of storage `facts` (the first parts of storage `li_okruns`), with the o_orderpriority and l_shipmode
/// dictionaries (offsets, bytes) and the co-clustering flag.
fn open_model(st: &mut StoredParts, Ghost(db): Ghost<Database>)
    -> (r: (Cols, &'static [u64], &'static [u8], &'static [u64], &'static [u8], u64))
    requires
        old(st)@.len() >= FACTS_PARTS,
        bound(db, old(st)@.subrange(0, FACTS_PARTS as int)),
    ensures
        final(st)@ == old(st)@,
        cols_from_parts(r.0, old(st)@.subrange(0, FACTS_PARTS as int)),
        dicts_from_parts(old(st)@.subrange(0, FACTS_PARTS as int), r.1@, r.2@, r.3@, r.4@),
        r.5 == u64s(old(st)@.subrange(0, FACTS_PARTS as int)[p_flag()])[0],
{
    let ghost parts = st@.subrange(0, FACTS_PARTS as int);
    proof {
        lemma_parts_shape(db, parts);
    }
    let olay = st.extent_u64(ORDERS_FIRST + OR_LAYOUT, 0, 2);
    let llay = st.extent_u64(LINEITEM_FIRST + LI_LAYOUT, 0, 2);
    let n_o = st.part_len(ORDERS_FIRST + OR_ORDERKEY_CODES);
    let n_l = st.part_len(LINEITEM_FIRST + LI_ORDERKEY_CODES);
    let ng_o = st.part_len(ORDERS_FIRST + OR_ORDERKEY_BASE);
    let ng_l = st.part_len(LINEITEM_FIRST + LI_ORDERKEY_BASE);
    proof {
        assert(olay@ =~= u64s(parts[p_ol()]));
        assert(llay@ =~= u64s(parts[p_ll()]));
    }
    let bs_o = model_bs(olay[1], n_o);
    let bs_l = model_bs(llay[1], n_l);
    let ok_codes = st.extent_u32(ORDERS_FIRST + OR_ORDERKEY_CODES, 0, n_o);
    let ok_bases = st.extent_i64(ORDERS_FIRST + OR_ORDERKEY_BASE, 0, ng_o);
    let op_codes = st.extent_u8(ORDERS_FIRST + OR_ORDERPRIORITY_CODES, 0, n_o);
    let op_bases = st.extent_u64(ORDERS_FIRST + OR_ORDERPRIORITY_BASE, 0, ng_o);
    let oic_len = st.part_len(ORDERS_FIRST + OR_KEYIDX_CODES);
    let oi_codes = st.extent_u32(ORDERS_FIRST + OR_KEYIDX_CODES, 0, oic_len);
    let oib_len = st.part_len(ORDERS_FIRST + OR_KEYIDX_BASE);
    let oi_bases = st.extent_u64(ORDERS_FIRST + OR_KEYIDX_BASE, 0, oib_len);
    let oi_kind = st.extent_u64(ORDERS_FIRST + OR_KEYIDX_KIND, 0, 1)[0];
    let lk_codes = st.extent_u32(LINEITEM_FIRST + LI_ORDERKEY_CODES, 0, n_l);
    let lk_bases = st.extent_i64(LINEITEM_FIRST + LI_ORDERKEY_BASE, 0, ng_l);
    let ls_codes = st.extent_u16(LINEITEM_FIRST + LI_SHIPDATE_CODES, 0, n_l);
    let ls_bases = st.extent_i64(LINEITEM_FIRST + LI_SHIPDATE_BASE, 0, ng_l);
    let ls_zmax = st.extent_i64(LINEITEM_FIRST + LI_SHIPDATE_ZMAX, 0, ng_l);
    let lc_codes = st.extent_u16(LINEITEM_FIRST + LI_COMMITDATE_CODES, 0, n_l);
    let lc_bases = st.extent_i64(LINEITEM_FIRST + LI_COMMITDATE_BASE, 0, ng_l);
    let lc_zmax = st.extent_i64(LINEITEM_FIRST + LI_COMMITDATE_ZMAX, 0, ng_l);
    let lr_codes = st.extent_u16(LINEITEM_FIRST + LI_RECEIPTDATE_CODES, 0, n_l);
    let lr_bases = st.extent_i64(LINEITEM_FIRST + LI_RECEIPTDATE_BASE, 0, ng_l);
    let lr_zmax = st.extent_i64(LINEITEM_FIRST + LI_RECEIPTDATE_ZMAX, 0, ng_l);
    let lm_codes = st.extent_u8(LINEITEM_FIRST + LI_SHIPMODE_CODES, 0, n_l);
    let lm_bases = st.extent_u64(LINEITEM_FIRST + LI_SHIPMODE_BASE, 0, ng_l);
    let polen = st.part_len(ORDERS_FIRST + OR_ORDERPRIORITY_DICT_OFFS);
    let po = st.extent_u64(ORDERS_FIRST + OR_ORDERPRIORITY_DICT_OFFS, 0, polen);
    let pylen = st.part_len(ORDERS_FIRST + OR_ORDERPRIORITY_DICT_BYTES);
    let py = st.extent_u8(ORDERS_FIRST + OR_ORDERPRIORITY_DICT_BYTES, 0, pylen);
    let molen = st.part_len(LINEITEM_FIRST + LI_SHIPMODE_DICT_OFFS);
    let mo = st.extent_u64(LINEITEM_FIRST + LI_SHIPMODE_DICT_OFFS, 0, molen);
    let mylen = st.part_len(LINEITEM_FIRST + LI_SHIPMODE_DICT_BYTES);
    let my = st.extent_u8(LINEITEM_FIRST + LI_SHIPMODE_DICT_BYTES, 0, mylen);
    let flag = st.extent_u64(FACTS_CLUSTER, 0, 1)[0];
    let c = Cols {
        ok_codes, ok_bases, op_codes, op_bases, oi_codes, oi_bases, oi_kind, n_o, bs_o,
        lk_codes, lk_bases, ls_codes, ls_bases, ls_zmax, lc_codes, lc_bases, lc_zmax, lr_codes, lr_bases, lr_zmax, lm_codes, lm_bases,
        n_l, bs_l,
    };
    proof {
        assert(ok_codes@ =~= u32s(parts[p_okc()]));
        assert(ok_bases@ =~= i64s(parts[p_okb()]));
        assert(op_codes@ =~= u8s(parts[p_opc()]));
        assert(op_bases@ =~= u64s(parts[p_opb()]));
        assert(oi_codes@ =~= u32s(parts[p_oic()]));
        assert(oi_bases@ =~= u64s(parts[p_oib()]));
        assert(lk_codes@ =~= u32s(parts[p_lkc()]));
        assert(lk_bases@ =~= i64s(parts[p_lkb()]));
        assert(ls_codes@ =~= u16s(parts[p_lsc()]));
        assert(ls_bases@ =~= i64s(parts[p_lsb()]));
        assert(lc_codes@ =~= u16s(parts[p_lcc()]));
        assert(lc_bases@ =~= i64s(parts[p_lcb()]));
        assert(lr_codes@ =~= u16s(parts[p_lrc()]));
        assert(lr_bases@ =~= i64s(parts[p_lrb()]));
        assert(lr_zmax@ =~= i64s(parts[p_lrz()]));
        assert(lc_zmax@ =~= i64s(parts[p_lcz()]));
        assert(ls_zmax@ =~= i64s(parts[p_lsz()]));
        assert(lm_codes@ =~= u8s(parts[p_lmc()]));
        assert(lm_bases@ =~= u64s(parts[p_lmb()]));
        assert(po@ =~= u64s(parts[p_odo()]));
        assert(py@ =~= u8s(parts[p_ody()]));
        assert(mo@ =~= u64s(parts[p_lmo()]));
        assert(my@ =~= u8s(parts[p_lmy()]));
    }
    (c, po, py, mo, my, flag)
}

// ------------------------------------------------------------------------------------------------ candidate groups

/// No row of lineitem group `g` can qualify by its zones: the receipt-date zone misses the window, or every commit
/// date is at or past the window end (a qualifying line has `l_commitdate < l_receiptdate <= hi`).
pub open spec fn zone_miss(c: Cols, w: Win, g: int) -> bool {
    c.lr_bases@[g] > w.hi || c.lr_zmax@[g] < w.lo || c.lc_bases@[g] >= w.hi
}

/// A row of a group whose zone misses the window never qualifies.
proof fn lemma_row_skip(c: Cols, w: Win, kp: int, km: int, j: int)
    requires
        cols_ok(c, kp, km),
        0 <= j < c.n_l,
        zone_miss(c, w, j / c.bs_l as int),
    ensures !lqual(c, w, j),
{
    assert(lrcp(c, j) <= c.lr_zmax@[j / c.bs_l as int]);
    assert(c.lr_codes@[j] >= 0);
    assert(c.lc_codes@[j] >= 0);
}

/// Rows below `g * bs` lie in groups below `g`; rows from `g * bs` in groups from `g` on.
proof fn lemma_group_side(p: int, bs: int, g: int)
    requires p >= 0, bs >= 1, g >= 0,
    ensures
        p < g * bs ==> p / bs < g,
        p >= g * bs ==> p / bs >= g,
{
    vstd::arithmetic::div_mod::lemma_fundamental_div_mod(p, bs);
    vstd::arithmetic::div_mod::lemma_mod_pos_bound(p, bs);
    let q = p / bs;
    assert(bs * q == q * bs) by (nonlinear_arith);
    if p < g * bs && q >= g {
        assert(q * bs >= g * bs) by (nonlinear_arith) requires q >= g, bs >= 1;
    }
    if p >= g * bs && q < g {
        assert(q * bs + bs <= g * bs) by (nonlinear_arith) requires q + 1 <= g, bs >= 1;
    }
}

/// The candidate lineitem groups `[ga, gb)` by the receipt-date zone maps: no row outside qualifies.
fn candidate_groups(c: &Cols, w: &Win, Ghost(kp): Ghost<int>, Ghost(km): Ghost<int>) -> (r: (usize, usize))
    requires cols_ok(*c, kp, km),
    ensures
        r.0 <= r.1 <= c.lk_bases@.len(),
        forall|j: int| 0 <= j < c.n_l && (j < row_of(*c, r.0 as int) || j >= row_of(*c, r.1 as int))
            ==> !#[trigger] lqual(*c, *w, j),
{
    let ng = c.lk_bases.len();
    let mut ga: usize = 0;
    while ga < ng && (c.lr_bases[ga] > w.hi || c.lr_zmax[ga] < w.lo || c.lc_bases[ga] >= w.hi)
        invariant
            ga <= ng,
            ng == c.lk_bases@.len(),
            cols_ok(*c, kp, km),
            forall|g: int| 0 <= g < ga ==> #[trigger] zone_miss(*c, *w, g),
        decreases ng - ga,
    {
        ga = ga + 1;
    }
    let mut gb: usize = ng;
    while gb > ga && (c.lr_bases[gb - 1] > w.hi || c.lr_zmax[gb - 1] < w.lo || c.lc_bases[gb - 1] >= w.hi)
        invariant
            ga <= gb <= ng,
            ng == c.lk_bases@.len(),
            cols_ok(*c, kp, km),
            forall|g: int| gb <= g < ng ==> #[trigger] zone_miss(*c, *w, g),
        decreases gb,
    {
        gb = gb - 1;
    }
    proof {
        let bs = c.bs_l as int;
        assert forall|j: int| 0 <= j < c.n_l && (j < row_of(*c, ga as int) || j >= row_of(*c, gb as int))
            implies !#[trigger] lqual(*c, *w, j) by {
            lemma_div_below(j, bs, ng as int);
            if j < row_of(*c, ga as int) {
                lemma_group_side(j, bs, ga as int);
            } else {
                lemma_group_side(j, bs, gb as int);
            }
            assert(zone_miss(*c, *w, j / bs));
            lemma_row_skip(*c, *w, kp, km, j);
        }
    }
    (ga, gb)
}

// ------------------------------------------------------------------------------------------------ scan tasks

/// Task boundary `i` of `nt` tasks over the `span` groups from `ga`: an even split.
pub open spec fn bnd(ga: int, span: int, nt: int, i: int) -> int {
    ga + (span * i) / nt
}

proof fn lemma_bnd(ga: int, span: int, nt: int, i: int, j: int)
    requires
        span >= 0,
        nt >= 1,
        0 <= i <= j <= nt,
    ensures
        ga <= bnd(ga, span, nt, i) <= bnd(ga, span, nt, j) <= ga + span,
        bnd(ga, span, nt, 0) == ga,
        bnd(ga, span, nt, nt) == ga + span,
{
    assert(span * i <= span * j) by (nonlinear_arith) requires span >= 0, i <= j;
    assert(span * j <= span * nt) by (nonlinear_arith) requires span >= 0, j <= nt;
    assert(span * i >= 0) by (nonlinear_arith) requires span >= 0, i >= 0;
    assert(span * 0 == 0);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(span * i, span * j, nt);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(span * j, span * nt, nt);
    vstd::arithmetic::div_mod::lemma_div_is_ordered(0, span * i, nt);
    vstd::arithmetic::div_mod::lemma_div_by_multiple(span, nt);
}

/// `ga + span * i / nt`, computed without overflow.
fn bnd_exec(ga: usize, span: usize, nt: usize, i: usize) -> (r: usize)
    requires
        nt >= 1,
        i <= nt,
        ga + span <= usize::MAX,
    ensures r as int == bnd(ga as int, span as int, nt as int, i as int),
{
    proof {
        lemma_bnd(ga as int, span as int, nt as int, i as int, nt as int);
        assert(span as int * i as int <= span as int * nt as int) by (nonlinear_arith) requires i <= nt;
        assert(span as int * nt as int <= 0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffffint) by (nonlinear_arith)
            requires span <= usize::MAX, nt <= usize::MAX, usize::MAX <= 0xffff_ffff_ffff_ffffint;
    }
    let p = span as u128 * i as u128;
    let q = p / nt as u128;
    ga + q as usize
}

/// `row_of` is nondecreasing in the group.
proof fn lemma_row_of_mono(c: Cols, g: int, h: int)
    requires 0 <= g <= h, c.bs_l >= 1,
    ensures row_of(c, g) <= row_of(c, h),
{
    assert(g * c.bs_l <= h * c.bs_l) by (nonlinear_arith) requires g <= h, c.bs_l >= 1;
}

/// The scan tasks over groups `[ga, ga + span)`: `nt` tasks, an even split.
fn make_tasks(c: &Cols, w: &Win, kp: usize, km: usize, clustered: bool, st: &'static [u32], bits: Bits, sel: Sel,
    fast: bool, ga: usize, span: usize, nt: usize) -> (tasks: Vec<ScanTask>)
    requires
        fast ==> fast_ok(*c, *w, st@, bits, sel),
        cols_ok(*c, kp as int, km as int),
        keys_distinct(*c),
        clustered ==> lines_clustered(*c),
        win_ok(*w),
        ga + span <= c.lk_bases@.len(),
        ga + span <= usize::MAX,
        1 <= nt <= MAX_WORKERS,
    ensures
        tasks@.len() == nt,
        forall|i: int| 0 <= i < nt ==> {
            &&& (#[trigger] tasks@[i]).pre()
            &&& tasks@[i].cols == *c
            &&& tasks@[i].win == *w
            &&& tasks@[i].km == km
            &&& tasks@[i].g0 == bnd(ga as int, span as int, nt as int, i)
            &&& tasks@[i].g1 == bnd(ga as int, span as int, nt as int, i + 1)
        },
{
    let mut tasks: Vec<ScanTask> = Vec::new();
    let tab = tz_table();
    let mut t: usize = 0;
    while t < nt
        invariant
            cols_ok(*c, kp as int, km as int),
            keys_distinct(*c),
            clustered ==> lines_clustered(*c),
            win_ok(*w),
            ga + span <= c.lk_bases@.len(),
            ga + span <= usize::MAX,
            1 <= nt <= MAX_WORKERS,
            tz_table_ok(tab),
            fast ==> fast_ok(*c, *w, st@, bits, sel),
            t <= nt,
            tasks@.len() == t,
            forall|i: int| 0 <= i < t ==> {
                &&& (#[trigger] tasks@[i]).pre()
                &&& tasks@[i].cols == *c
                &&& tasks@[i].win == *w
                &&& tasks@[i].km == km
                &&& tasks@[i].g0 == bnd(ga as int, span as int, nt as int, i)
                &&& tasks@[i].g1 == bnd(ga as int, span as int, nt as int, i + 1)
            },
        decreases nt - t,
    {
        proof {
            lemma_bnd(ga as int, span as int, nt as int, t as int, t + 1);
        }
        let g0 = bnd_exec(ga, span, nt, t);
        let g1 = bnd_exec(ga, span, nt, t + 1);
        let task = ScanTask { cols: *c, win: *w, kp, km, g0, g1, clustered,
            hi_cnt: filled(km, 0usize), lo_cnt: filled(km, 0usize), flags: [0u8; FB],
            masks: [0u64; 64], keys: [0u32; FB], modes: [0u8; FB], tab, st, bits, sel, fast };
        proof {
            assert(task.hi_cnt@ =~= zeros(km as nat));
            assert(task.lo_cnt@ =~= zeros(km as nat));
        }
        tasks.push(task);
        t = t + 1;
    }
    tasks
}

/// Per-entry sums of the task outputs: the counts over the rows of groups `[ga, ga + span)`.
fn merge_counts(c: &Cols, w: &Win, km: usize, ga: usize, span: usize, tv: Ghost<Seq<ScanTask>>,
    outs: &Vec<(Vec<usize>, Vec<usize>)>) -> (r: (Vec<usize>, Vec<usize>))
    requires
        c.bs_l >= 1,
        tv@.len() >= 1,
        outs@.len() == tv@.len(),
        forall|i: int| 0 <= i < tv@.len() ==> {
            &&& (#[trigger] tv@[i]).post(outs@[i])
            &&& tv@[i].cols == *c
            &&& tv@[i].win == *w
            &&& tv@[i].km == km
            &&& tv@[i].g0 == bnd(ga as int, span as int, tv@.len() as int, i)
            &&& tv@[i].g1 == bnd(ga as int, span as int, tv@.len() as int, i + 1)
        },
    ensures
        counts_at(*c, *w, km as int, r.0@, r.1@, row_of(*c, ga as int), row_of(*c, ga + span)),
{
    let ghost nt = tv@.len() as int;
    let ghost j0 = row_of(*c, ga as int);
    let n_out = outs.len();
    let mut hs: Vec<usize> = filled(km, 0usize);
    let mut ls: Vec<usize> = filled(km, 0usize);
    let mut t: usize = 0;
    proof {
        lemma_bnd(ga as int, span as int, nt, 0, 0);
        lemma_row_of_mono(*c, 0, ga as int);
        assert(0 * c.bs_l == 0);
    }
    while t < n_out
        invariant
            n_out == nt == outs@.len(),
            c.bs_l >= 1,
            1 <= nt,
            t <= nt,
            j0 == row_of(*c, ga as int),
            0 <= j0,
            forall|i: int| 0 <= i < nt ==> {
                &&& (#[trigger] tv@[i]).post(outs@[i])
                &&& tv@[i].cols == *c
                &&& tv@[i].win == *w
                &&& tv@[i].km == km
                &&& tv@[i].g0 == bnd(ga as int, span as int, nt, i)
                &&& tv@[i].g1 == bnd(ga as int, span as int, nt, i + 1)
            },
            counts_at(*c, *w, km as int, hs@, ls@, j0, row_of(*c, bnd(ga as int, span as int, nt, t as int))),
        decreases nt - t,
    {
        let ghost t0 = row_of(*c, bnd(ga as int, span as int, nt, t as int));
        let ghost t1 = row_of(*c, bnd(ga as int, span as int, nt, t + 1));
        proof {
            lemma_bnd(ga as int, span as int, nt, t as int, t + 1);
            lemma_bnd(ga as int, span as int, nt, 0, t as int);
            lemma_row_of_mono(*c, ga as int, bnd(ga as int, span as int, nt, t as int));
            lemma_row_of_mono(*c, bnd(ga as int, span as int, nt, t as int), bnd(ga as int, span as int, nt, t + 1));
        }
        let oh = &outs[t].0;
        let ol = &outs[t].1;
        proof {
            let task = tv@[t as int];
            assert(task.post(outs@[t as int]));
            assert(counts_at(*c, *w, km as int, oh@, ol@, t0, t1));
        }
        let mut d: usize = 0;
        while d < km
            invariant
                0 <= j0 <= t0 <= t1,
                t1 <= c.n_l,
                hs@.len() == km,
                ls@.len() == km,
                d <= km,
                counts_at(*c, *w, km as int, oh@, ol@, t0, t1),
                forall|e: int| 0 <= e < d ==> #[trigger] hs@[e] as int == cnt(*c, *w, 0, e, j0, t1),
                forall|e: int| d <= e < km ==> #[trigger] hs@[e] as int == cnt(*c, *w, 0, e, j0, t0),
                forall|e: int| 0 <= e < d ==> #[trigger] ls@[e] as int == cnt(*c, *w, 1, e, j0, t1),
                forall|e: int| d <= e < km ==> #[trigger] ls@[e] as int == cnt(*c, *w, 1, e, j0, t0),
            decreases km - d,
        {
            proof {
                lemma_cnt_split(*c, *w, 0, d as int, j0, t0, t1);
                lemma_cnt_bound(*c, *w, 0, d as int, j0, t1);
                lemma_cnt_bound(*c, *w, 0, d as int, j0, t0);
                lemma_cnt_split(*c, *w, 1, d as int, j0, t0, t1);
                lemma_cnt_bound(*c, *w, 1, d as int, j0, t1);
                lemma_cnt_bound(*c, *w, 1, d as int, j0, t0);
                assert(oh@[d as int] as int == cnt(*c, *w, 0, d as int, t0, t1));
                assert(ol@[d as int] as int == cnt(*c, *w, 1, d as int, t0, t1));
            }
            let h = hs[d] + oh[d];
            hs.set(d, h);
            let l = ls[d] + ol[d];
            ls.set(d, l);
            d = d + 1;
        }
        t = t + 1;
    }
    proof {
        assert(bnd(ga as int, span as int, nt, nt) == ga + span) by {
            lemma_bnd(ga as int, span as int, nt, 0, nt);
        }
    }
    (hs, ls)
}

/// The bitmap path's inputs and whether it applies (`fast_ok`): the runs match the orders, the bitmaps are present
/// with an l_shipmode bitmap for each selected entry, every o_orderpriority group base is 0, and lineitem groups
/// are whole bitmap words.
fn fast_setup(c: &Cols, w: &Win, olay: &'static [u64], run: &'static [u64], mode: &'static [u64],
    Ghost(st): Ghost<Seq<u32>>, runs: bool, Ghost(kp): Ghost<int>, Ghost(km): Ghost<int>, Ghost(db): Ghost<Database>,
    Ghost(sv): Ghost<crate::gendb_entry::stores::StoresView>) -> (r: (Bits, Sel, bool))
    requires
        cols_ok(*c, kp, km),
        bound_db(sv, db),
        cols_from_parts(*c, fparts(sv)),
        olay@ == u64s(sv.li_okmode[OKM_LAYOUT as int]),
        run@ == u64s(sv.li_okmode[RUN_BITS as int]),
        mode@ == u64s(sv.li_okmode[MODE_BITS as int]),
        st == u32s(sv.li_okmode[RUN_STARTS as int]),
        starts_ok(*c, st),
        runs ==> runs_match(*c, st) && rank_ok(*c),
    ensures r.2 ==> fast_ok(*c, *w, st, r.0, r.1),
{
    let nw = run.len();
    let nm64 = olay[1];
    let nm: usize = if nm64 <= 64 { nm64 as usize } else { 0 };
    let bits = Bits { run, mode, nw, nm };
    let none = Sel { o0: 0, k0: 0, o1: 0, k1: 0 };
    if !runs || nw == 0 || nm == 0 || c.bs_l % 64 != 0 || mode.len() != nm * nw {
        return (bits, none, false);
    }
    let s0ok = w.s0 < nm as u64;
    let s1ok = w.s1 < nm as u64;
    if !(s0ok || w.s0 == u64::MAX) || !(s1ok || w.s1 == u64::MAX) {
        return (bits, none, false);
    }
    proof {
        if s0ok {
            assert((w.s0 as int) * nw + nw <= nm * nw) by (nonlinear_arith) requires w.s0 < nm;
        }
        if s1ok {
            assert((w.s1 as int) * nw + nw <= nm * nw) by (nonlinear_arith) requires w.s1 < nm;
        }
        assert(nw <= nm * nw) by (nonlinear_arith) requires nm >= 1;
    }
    let o0 = if s0ok { w.s0 as usize * nw } else { 0 };
    let o1 = if s1ok { w.s1 as usize * nw } else { 0 };
    let sel = Sel { o0, k0: if s0ok { u64::MAX } else { 0 }, o1, k1: if s1ok { u64::MAX } else { 0 } };
    // Every o_orderpriority group base is 0.
    let ng = c.op_bases.len();
    let mut g: usize = 0;
    while g < ng
        invariant
            ng == c.op_bases@.len(),
            g <= ng,
            forall|h: int| 0 <= h < g ==> #[trigger] c.op_bases@[h] == 0,
        decreases ng - g,
    {
        if c.op_bases[g] != 0 {
            return (bits, none, false);
        }
        g = g + 1;
    }
    proof {
        lemma_bits_model(db, sv, *c, bits);
    }
    (bits, sel, true)
}

/// The run starts and bitmaps of storage `li_okmode` (parts 75 to 78) and whether the bitmap path applies.
fn open_fast(st: &mut StoredParts, c: &Cols, w: &Win, clustered: bool, Ghost(kp): Ghost<int>, Ghost(km): Ghost<int>,
    Ghost(db): Ghost<Database>, Ghost(sv): Ghost<crate::gendb_entry::stores::StoresView>)
    -> (r: (&'static [u32], Bits, Sel, bool))
    requires
        old(st)@ == sv.li_okmode,
        bound_db(sv, db),
        cols_from_parts(*c, fparts(sv)),
        cols_ok(*c, kp, km),
        keys_distinct(*c),
        clustered ==> lines_clustered(*c),
    ensures
        final(st)@ == old(st)@,
        r.3 ==> fast_ok(*c, *w, r.0@, r.1, r.2),
{
    proof {
        lemma_starts_model(db, sv, *c);
        lemma_bound(sv, db);
    }
    let nst = st.part_len(RUN_STARTS);
    let starts = st.extent_u32(RUN_STARTS, 0, nst);
    let olay = st.extent_u64(OKM_LAYOUT, 0, 2);
    let nrun = st.part_len(RUN_BITS);
    let run = st.extent_u64(RUN_BITS, 0, nrun);
    let nmode = st.part_len(MODE_BITS);
    let mode = st.extent_u64(MODE_BITS, 0, nmode);
    proof {
        assert(starts@ =~= u32s(sv.li_okmode[RUN_STARTS as int]));
        assert(olay@ =~= u64s(sv.li_okmode[OKM_LAYOUT as int]));
        assert(run@ =~= u64s(sv.li_okmode[RUN_BITS as int]));
        assert(mode@ =~= u64s(sv.li_okmode[MODE_BITS as int]));
    }
    let runs = check_runs(c, starts, clustered, Ghost(kp), Ghost(km));
    let (bits, sel, fast) = fast_setup(c, w, olay, run, mode, Ghost(starts@), runs, Ghost(kp), Ghost(km), Ghost(db),
        Ghost(sv));
    (starts, bits, sel, fast)
}

/// High and low counts per ship-mode entry over every stored lineitem row.
fn count_all(c: &Cols, w: &Win, kp: usize, km: usize, clustered: bool, st: &'static [u32], bits: Bits, sel: Sel,
    fast: bool, workers: usize, dispatch: &mut Dispatch) -> (r: Result<(Vec<usize>, Vec<usize>), WorkerFailure>)
    requires
        fast ==> fast_ok(*c, *w, st@, bits, sel),
        cols_ok(*c, kp as int, km as int),
        keys_distinct(*c),
        clustered ==> lines_clustered(*c),
        win_ok(*w),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(v) ==> counts_at(*c, *w, km as int, v.0@, v.1@, 0, c.n_l as int),
{
    let (ga, gb) = candidate_groups(c, w, Ghost(kp as int), Ghost(km as int));
    let span = gb - ga;
    let nt = if span == 0 { 1 } else if span < workers { span } else { workers };
    let tasks = make_tasks(c, w, kp, km, clustered, st, bits, sel, fast, ga, span, nt);
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(f) => return Err(f),
    };
    let (hs, ls) = merge_counts(c, w, km, ga, span, Ghost(tv), &outs);
    proof {
        let (a, b, n) = (row_of(*c, ga as int), row_of(*c, gb as int), c.n_l as int);
        lemma_row_of_mono(*c, ga as int, gb as int);
        assert(0 * c.bs_l == 0);
        assert(row_of(*c, ga as int) <= n);
        assert forall|e: int| 0 <= e < km implies #[trigger] hs@[e] as int == cnt(*c, *w, 0, e, 0, n) by {
            lemma_cnt_split(*c, *w, 0, e, 0, a, n);
            lemma_cnt_split(*c, *w, 0, e, a, b, n);
            lemma_cnt_none(*c, *w, 0, e, 0, a);
            lemma_cnt_none(*c, *w, 0, e, b, n);
        }
        assert forall|e: int| 0 <= e < km implies #[trigger] ls@[e] as int == cnt(*c, *w, 1, e, 0, n) by {
            lemma_cnt_split(*c, *w, 1, e, 0, a, n);
            lemma_cnt_split(*c, *w, 1, e, a, b, n);
            lemma_cnt_none(*c, *w, 1, e, 0, a);
            lemma_cnt_none(*c, *w, 1, e, b, n);
        }
    }
    Ok((hs, ls))
}

// ------------------------------------------------------------------------------------------------ the answer

/// The first ship-mode entry whose high or low sum exceeds int8, if any.
fn find_overflow(hs: &Vec<usize>, ls: &Vec<usize>) -> (r: Option<usize>)
    requires hs@.len() == ls@.len(),
    ensures
        r matches Some(d) ==> d < hs@.len() && (hs@[d as int] > int8_max() || ls@[d as int] > int8_max()),
        r is None ==> sums_fit(hs@, ls@),
{
    let k = hs.len();
    let mut d: usize = 0;
    while d < k
        invariant
            k == hs@.len(),
            k == ls@.len(),
            d <= k,
            forall|e: int| 0 <= e < d ==> #[trigger] hs@[e] <= int8_max(),
            forall|e: int| 0 <= e < d ==> #[trigger] ls@[e] <= int8_max(),
        decreases k - d,
    {
        if hs[d] as u128 > i64::MAX as u128 || ls[d] as u128 > i64::MAX as u128 {
            return Some(d);
        }
        d = d + 1;
    }
    None
}

/// The bytes of dictionary entry `d`, copied.
fn copy_text(offs: &[u64], bytes: &[u8], d: usize) -> (v: Vec<u8>)
    requires
        d + 1 < offs@.len(),
        text_range_ok(offs@, bytes@, d as int),
    ensures v@ == text_of(offs@, bytes@, d as int),
{
    let s = text_slice(offs, bytes, d);
    let n = s.len();
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == s@.len(),
            i <= n,
            v@ == s@.subrange(0, i as int),
        decreases n - i,
    {
        v.push(s[i]);
        i = i + 1;
        proof {
            assert(v@ =~= s@.subrange(0, i as int));
        }
    }
    proof {
        assert(s@.subrange(0, n as int) =~= s@);
    }
    v
}

/// One row `[entry text, high, low]` per ship-mode entry with a qualifying line, in dictionary order.
fn build_rows(mo: &[u64], my: &[u8], hs: &Vec<usize>, ls: &Vec<usize>) -> (r: (Vec<Vec<EVal>>, Ghost<Seq<int>>))
    requires
        mo@.len() >= 1,
        hs@.len() == mo@.len() - 1,
        ls@.len() == hs@.len(),
        text_parts_wf(mo@, my@, mo@.len() - 1),
        sums_fit(hs@, ls@),
    ensures
        entries_ok(hs@, ls@, r.1@),
        r.0@.len() == r.1@.len(),
        forall|i: int| 0 <= i < r.0@.len() ==> #[trigger] view_row(r.0@[i]@) == entry_row(mo@, my@, hs@, ls@, r.1@[i]),
{
    let k = hs.len();
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let ghost mut ds: Seq<int> = Seq::empty();
    let mut d: usize = 0;
    while d < k
        invariant
            k == hs@.len(),
            k == ls@.len(),
            k == mo@.len() - 1,
            text_parts_wf(mo@, my@, k as int),
            d <= k,
            sums_fit(hs@, ls@),
            rows@.len() == ds.len(),
            forall|i: int| 0 <= i < ds.len() ==> #[trigger] view_row(rows@[i]@) == entry_row(mo@, my@, hs@, ls@, ds[i]),
            forall|i: int| 0 <= i < ds.len() ==> 0 <= #[trigger] ds[i] < d && hs@[ds[i]] + ls@[ds[i]] > 0,
            forall|i: int, j: int| 0 <= i < j < ds.len() ==> #[trigger] ds[i] < #[trigger] ds[j],
            forall|e: int| 0 <= e < d && #[trigger] hs@[e] + ls@[e] > 0 ==> ds.contains(e),
        decreases k - d,
    {
        let ghost ds0 = ds;
        if hs[d] > 0 || ls[d] > 0 {
            proof {
                assert(text_range_ok(mo@, my@, d as int));
                assert(hs@[d as int] <= int8_max() && ls@[d as int] <= int8_max());
            }
            let txt = copy_text(mo, my, d);
            let hv = hs[d] as i64;
            let lv = ls[d] as i64;
            let mut row: Vec<EVal> = Vec::new();
            row.push(EVal::Text(txt));
            row.push(EVal::Int(hv));
            row.push(EVal::Int(lv));
            proof {
                assert(view_row(row@) =~= entry_row(mo@, my@, hs@, ls@, d as int));
            }
            rows.push(row);
            proof {
                ds = ds.push(d as int);
                assert(ds[ds.len() - 1] == d as int);
            }
        }
        proof {
            assert forall|e: int| 0 <= e < d + 1 && #[trigger] hs@[e] + ls@[e] > 0 implies ds.contains(e) by {
                if e < d {
                    let i = choose|i: int| 0 <= i < ds0.len() && ds0[i] == e;
                    assert(ds[i] == e);
                } else {
                    assert(ds[ds.len() - 1] == e);
                }
            }
        }
        d = d + 1;
    }
    (rows, Ghost(ds))
}

/// TPC-H Q12 over storage `facts`.
pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost parts = fparts(stores@);
    let ghost ps = params@;
    let ghost db0 = choose|db: Database| #[trigger] bound_db(sv, db);
    proof {
        lemma_bound(sv, db0);
        lemma_parts_shape(db0, parts);
    }
    let (lo_day, hi_res) = date_window(params);
    let (c, po, py, mo, my, flag) = open_model(&mut stores.li_okmode, Ghost(db0));
    let kp = po.len() - 1;
    let km = mo.len() - 1;

    // An error of `$3 + 1 year` is the statement's error unless the product is empty.
    let hi_day = match hi_res {
        Ok(h) => h,
        Err(e) => {
            if c.n_o > 0 && c.n_l > 0 {
                proof {
                    lemma_meets_date_err(sv, ps, e);
                }
                return Ok(Answer::SqlError(e));
            }
            lo_day
        },
    };
    proof {
        lemma_model_facts(db0, parts, c, po@, py@, mo@, my@);
    }
    let w = make_win(po, py, mo, my, params, lo_day, hi_day);
    let (st, bits, sel, fast) = open_fast(&mut stores.li_okmode, &c, &w, flag == 1, Ghost(kp as int), Ghost(km as int),
        Ghost(db0), Ghost(sv));
    let (hs, ls) = match count_all(&c, &w, kp, km, flag == 1, st, bits, sel, fast, workers, dispatch) {
        Ok(v) => v,
        Err(f) => return Err(QueryError::WorkerFailed(f)),
    };
    proof {
        lemma_meets_totals(sv, c, w, po@, py@, mo@, my@, ps, hi_day as int, hs@, ls@);
    }

    // A SUM beyond int8 is error 22003.
    if let Some(d) = find_overflow(&hs, &ls) {
        proof {
            lemma_meets_overflow(sv, mo@, my@, ps, hi_day as int, hs@, ls@, d as int);
        }
        return Ok(Answer::SqlError(SqlError::NumericValueOutOfRange));
    }

    let (rows, ds) = build_rows(mo, my, &hs, &ls);
    proof {
        lemma_meets_rows(sv, c, po@, py@, mo@, my@, ps, hi_day as int, hs@, ls@, ds@, rows);
    }
    Ok(Answer::Rows(rows))
}

} // verus!
