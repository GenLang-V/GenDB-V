// AUTHOR MODULE ROOT (crate::agent). You own every file under src/agent/.
//! TPC-H Q4 (order priority checking) over storage `facts`.
//!
//! Plan: orders are stored by o_orderdate with per-group zone maps, and lineitem rows are stored grouped by their
//! order in the same order (checked co-clustering flag). The query
//! 1. computes the date window `[lo, hi]` in days (`hi`: the last day before `$1 + 3 months`, as SQL compares the
//!    date with that timestamp);
//! 2. narrows the stored orders rows to `[a, b)` with the zone maps (rows outside cannot have a date in the window);
//! 3. splits `[a, b)` into scan tasks (`kernel::ScanTask`): each walks its orders and, in step, their lineitem runs,
//!    deciding EXISTS (a line with l_commitdate < l_receiptdate) and counting qualifying orders per o_orderpriority
//!    dictionary entry (a serial full-scan fallback runs when the co-clustering flag is not set);
//! 4. sums the task counts and answers one row per dictionary entry with a nonzero count, in dictionary order
//!    (bytewise, the ORDER BY order).
//! Proof: `model` (scan model), `kernel` (scan), `bind` (model = stored rows), `sql` (SQL meaning in normal form),
//! `answer` (rows and errors are allowed outcomes).
use vstd::prelude::*;
use crate::gendb_entry::{Answer, answer_meets, bound_db, stores_ready, outcome_ok};
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::{QueryError, WorkerFailure};
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::work::filled;
use crate::gendb_params::Params;
use crate::query::{param_domain, param_typed, query_spec_at};
use crate::spec::value::*;
use crate::spec::datetime::*;
use crate::spec::limits::int8_max;
use crate::exec::value::{EVal, view_row};
use crate::exec::datetime::{date_from_civil_exec, date_to_ts_exec, ts_add_interval_exec, floor_divmod};
use crate::link::query::view_rows;
use crate::stores::facts::interface::*;
use crate::stores::facts::interface::common::colfmt::*;

pub mod model;
pub mod kernel;
pub mod fast;
pub mod sql;
pub mod bind;
pub mod answer;

use model::*;
use kernel::*;
use sql::*;
use bind::*;
use answer::*;
use fast::{fast_ok, run_fast, FLAGS_LEN, OB};
use crate::stores::li_ordruns::interface::{facts_parts, run_lens, RUN_LENS};

verus! {

/// The date window: `$1` in days, and the last day before `$1 + 3 months` (or the error computing that timestamp).
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
        assert(days_in_month(params.p0.y as int, params.p0.m as int) <= 31);
    }
    let lo = date_from_civil_exec(params.p0.y as i64, params.p0.m as i64, params.p0.d as i64);
    let t0 = match date_to_ts_exec(lo as i32) {
        Ok(t) => t,
        Err(e) => return (lo, Err(e)),
    };
    let t1 = match ts_add_interval_exec(t0, 3, 0, 0) {
        Ok(t) => t,
        Err(e) => return (lo, Err(e)),
    };
    let (q, _) = floor_divmod(t1 - 1, 86_400_000_000i64);
    (lo, Ok(q))
}

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

/// The bytes of dictionary entry `d`, copied.
fn copy_text(offs: &[u64], bytes: &[u8], d: usize) -> (v: Vec<u8>)
    requires
        d + 1 < offs@.len(),
        text_range_ok(offs@, bytes@, d as int),
    ensures v@ == text_of(offs@, bytes@, d as int),
{
    let s = crate::stores::facts::interface::common::read::text_slice(offs, bytes, d);
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

/// Task boundary `i` of `nt` tasks over `[a, b)` in chunks of `chunk` rows (the last task takes the rest).
pub open spec fn tb(a: int, b: int, chunk: int, nt: int, i: int) -> int {
    if i >= nt { b } else { a + chunk * i }
}

proof fn lemma_tb(a: int, b: int, chunk: int, nt: int, i: int, j: int)
    requires
        0 <= a <= b,
        nt >= 1,
        chunk >= 0,
        chunk * nt <= b - a,
        0 <= i <= j <= nt,
    ensures
        a <= tb(a, b, chunk, nt, i) <= tb(a, b, chunk, nt, j) <= b,
{
    if j < nt {
        assert(chunk * i <= chunk * j) by (nonlinear_arith) requires i <= j, chunk >= 0;
        assert(chunk * j <= chunk * nt) by (nonlinear_arith) requires j <= nt, chunk >= 0;
        assert(chunk * i >= 0) by (nonlinear_arith) requires i >= 0, chunk >= 0;
    } else if i < nt {
        assert(chunk * i <= chunk * nt) by (nonlinear_arith) requires i <= nt, chunk >= 0;
        assert(chunk * i >= 0) by (nonlinear_arith) requires i >= 0, chunk >= 0;
    }
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

/// The scan model's columns as whole parts of storage `facts`, with the o_orderpriority dictionary (offsets,
/// bytes), the o_orderdate zone maxima and the co-clustering flag.
fn open_model(st: &mut StoredParts, Ghost(db): Ghost<Database>) -> (r: (Cols, &'static [u64], &'static [u8], &'static [i64], u64))
    requires bound2(db, old(st)@),
    ensures
        final(st)@ == old(st)@,
        cols_from_parts(r.0, facts_parts(old(st)@)),
        r.0.rl@ == run_lens(old(st)@),
        facts_parts(old(st)@)[p_odo()] == PartView::U64(r.1@),
        facts_parts(old(st)@)[p_ody()] == PartView::U8(r.2@),
        r.3@ == i64s(facts_parts(old(st)@)[p_odz()]),
        r.4 == u64s(facts_parts(old(st)@)[p_flag()])[0],
{
    let ghost parts = facts_parts(st@);
    proof {
        lemma_bound2(db, st@);
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
    let od_codes = st.extent_u16(ORDERS_FIRST + OR_ORDERDATE_CODES, 0, n_o);
    let od_bases = st.extent_i64(ORDERS_FIRST + OR_ORDERDATE_BASE, 0, ng_o);
    let od_zmax = st.extent_i64(ORDERS_FIRST + OR_ORDERDATE_ZMAX, 0, ng_o);
    let op_codes = st.extent_u8(ORDERS_FIRST + OR_ORDERPRIORITY_CODES, 0, n_o);
    let op_bases = st.extent_u64(ORDERS_FIRST + OR_ORDERPRIORITY_BASE, 0, ng_o);
    let oic_len = st.part_len(ORDERS_FIRST + OR_KEYIDX_CODES);
    let oi_codes = st.extent_u32(ORDERS_FIRST + OR_KEYIDX_CODES, 0, oic_len);
    let oib_len = st.part_len(ORDERS_FIRST + OR_KEYIDX_BASE);
    let oi_bases = st.extent_u64(ORDERS_FIRST + OR_KEYIDX_BASE, 0, oib_len);
    let oi_kind = st.extent_u64(ORDERS_FIRST + OR_KEYIDX_KIND, 0, 1)[0];
    let lk_codes = st.extent_u32(LINEITEM_FIRST + LI_ORDERKEY_CODES, 0, n_l);
    let lk_bases = st.extent_i64(LINEITEM_FIRST + LI_ORDERKEY_BASE, 0, ng_l);
    let lc_codes = st.extent_u16(LINEITEM_FIRST + LI_COMMITDATE_CODES, 0, n_l);
    let lc_bases = st.extent_i64(LINEITEM_FIRST + LI_COMMITDATE_BASE, 0, ng_l);
    let lr_codes = st.extent_u16(LINEITEM_FIRST + LI_RECEIPTDATE_CODES, 0, n_l);
    let lr_bases = st.extent_i64(LINEITEM_FIRST + LI_RECEIPTDATE_BASE, 0, ng_l);
    let dlen = st.part_len(ORDERS_FIRST + OR_ORDERPRIORITY_DICT_OFFS);
    let doffs = st.extent_u64(ORDERS_FIRST + OR_ORDERPRIORITY_DICT_OFFS, 0, dlen);
    let dblen = st.part_len(ORDERS_FIRST + OR_ORDERPRIORITY_DICT_BYTES);
    let dbytes = st.extent_u8(ORDERS_FIRST + OR_ORDERPRIORITY_DICT_BYTES, 0, dblen);
    let flag = st.extent_u64(FACTS_CLUSTER, 0, 1)[0];
    let n_r = st.part_len(RUN_LENS);
    let rl = st.extent_u8(RUN_LENS, 0, n_r);
    let c = Cols {
        ok_codes, ok_bases, od_codes, od_bases, op_codes, op_bases, oi_codes, oi_bases, oi_kind, n_o, bs_o,
        lk_codes, lk_bases, lc_codes, lc_bases, lr_codes, lr_bases, n_l, bs_l, rl,
    };
    proof {
        assert(ok_codes@ =~= u32s(parts[p_okc()]));
        assert(ok_bases@ =~= i64s(parts[p_okb()]));
        assert(od_codes@ =~= u16s(parts[p_odc()]));
        assert(od_bases@ =~= i64s(parts[p_odb()]));
        assert(od_zmax@ =~= i64s(parts[p_odz()]));
        assert(op_codes@ =~= u8s(parts[p_opc()]));
        assert(op_bases@ =~= u64s(parts[p_opb()]));
        assert(oi_codes@ =~= u32s(parts[p_oic()]));
        assert(oi_bases@ =~= u64s(parts[p_oib()]));
        assert(lk_codes@ =~= u32s(parts[p_lkc()]));
        assert(lk_bases@ =~= i64s(parts[p_lkb()]));
        assert(lc_codes@ =~= u16s(parts[p_lcc()]));
        assert(lc_bases@ =~= i64s(parts[p_lcb()]));
        assert(lr_codes@ =~= u16s(parts[p_lrc()]));
        assert(lr_bases@ =~= i64s(parts[p_lrb()]));
        assert(doffs@ =~= u64s(parts[p_odo()]));
        assert(dbytes@ =~= u8s(parts[p_ody()]));
        assert(rl@ =~= run_lens(st@));
    }
    (c, doffs, dbytes, od_zmax, flag)
}

/// Candidate stored orders rows `[a, b)` by the o_orderdate zone maps: no row outside qualifies.
fn candidate_range(c: &Cols, k: Ghost<int>, zmax: &[i64], lo: i64, hi: i64) -> (r: (usize, usize))
    requires
        cols_ok(*c, k@),
        zmax@.len() == c.od_bases@.len(),
        forall|p: int| 0 <= p < c.n_o ==> #[trigger] odate(*c, p) <= zmax@[p / c.bs_o as int],
    ensures
        r.0 <= r.1 <= c.n_o,
        forall|p: int| 0 <= p < c.n_o && (p < r.0 || p >= r.1) ==> !#[trigger] qual_raw(*c, lo as int, hi as int, p),
{
    let ng = c.od_bases.len();
    let n_o = c.n_o;
    let bs = c.bs_o;
    let mut g_lo: usize = 0;
    while g_lo < ng && zmax[g_lo] < lo
        invariant
            g_lo <= ng,
            ng == zmax@.len(),
            forall|g: int| 0 <= g < g_lo ==> zmax@[g] < lo,
        decreases ng - g_lo,
    {
        g_lo = g_lo + 1;
    }
    let mut g_hi: usize = ng;
    while g_hi > g_lo && c.od_bases[g_hi - 1] > hi
        invariant
            g_lo <= g_hi <= ng,
            ng == c.od_bases@.len(),
            forall|g: int| g_hi <= g < ng ==> c.od_bases@[g] > hi,
        decreases g_hi,
    {
        g_hi = g_hi - 1;
    }
    let b = match g_hi.checked_mul(bs) {
        Some(x) => if x < n_o { x } else { n_o },
        None => n_o,
    };
    let a0 = match g_lo.checked_mul(bs) {
        Some(x) => if x < n_o { x } else { n_o },
        None => n_o,
    };
    let a = if a0 < b { a0 } else { b };
    proof {
        assert forall|p: int| 0 <= p < c.n_o && (p < a || p >= b) implies !#[trigger] qual_raw(*c, lo as int, hi as int, p) by {
            lemma_div_below(p, bs as int, ng as int);
            assert(odate(*c, p) <= zmax@[p / bs as int]);
            if p < a {
                assert(p < g_lo * bs);
                lemma_group_side(p, bs as int, g_lo as int);
                assert(zmax@[p / bs as int] < lo);
            } else {
                assert(p >= g_hi * bs);
                lemma_group_side(p, bs as int, g_hi as int);
                assert(c.od_bases@[p / bs as int] > hi);
            }
        }
    }
    (a, b)
}

/// The scan tasks over `[a, b)`: at most `workers` and 32, at least 65536 rows each (one task for a small range).
fn make_tasks(c: &Cols, k: usize, a: usize, b: usize, lo: i64, hi: i64, fast: bool, zmax: &'static [i64], workers: usize)
    -> (r: (Vec<ScanTask>, Ghost<int>))
    requires
        cols_ok(*c, k as int),
        keys_distinct(*c),
        lines_clustered(*c),
        fast ==> fast_ok(*c, k as int),
        zmax@.len() == c.od_bases@.len(),
        forall|q: int| 0 <= q < c.n_o ==> #[trigger] odate(*c, q) <= zmax@[q / c.bs_o as int],
        a <= b <= c.n_o,
        1 <= workers <= MAX_WORKERS,
    ensures ({
        let (tasks, chunk) = (r.0@, r.1@);
        let nt = tasks.len() as int;
        &&& 1 <= nt <= MAX_WORKERS
        &&& chunk >= 0
        &&& chunk * nt <= b - a
        &&& forall|i: int| 0 <= i < nt ==> {
            &&& (#[trigger] tasks[i]).pre()
            &&& tasks[i].cols == *c
            &&& tasks[i].q0 == tb(a as int, b as int, chunk, nt, i)
            &&& tasks[i].q1 == tb(a as int, b as int, chunk, nt, i + 1)
            &&& tasks[i].lo == lo
            &&& tasks[i].hi == hi
            &&& tasks[i].k == k
        }
    }),
{
    let span = b - a;
    // At most 32 tasks: the scan is memory bound by then, and more threads only add start and join time.
    let mut nt: usize = if workers > 32 { 32 } else { workers };
    let cap = span / 65536 + 1;
    if cap < nt {
        nt = cap;
    }
    let chunk = span / nt;
    proof {
        vstd::arithmetic::div_mod::lemma_fundamental_div_mod(span as int, nt as int);
        vstd::arithmetic::div_mod::lemma_mod_pos_bound(span as int, nt as int);
        assert(chunk * nt <= span) by (nonlinear_arith)
            requires nt * chunk + span as int % nt as int == span, span as int % nt as int >= 0;
    }
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut t: usize = 0;
    while t < nt
        invariant
            cols_ok(*c, k as int),
            keys_distinct(*c),
            lines_clustered(*c),
            fast ==> fast_ok(*c, k as int),
            zmax@.len() == c.od_bases@.len(),
            forall|q: int| 0 <= q < c.n_o ==> #[trigger] odate(*c, q) <= zmax@[q / c.bs_o as int],
            a <= b <= c.n_o,
            1 <= nt <= MAX_WORKERS,
            chunk * nt <= b - a,
            t <= nt,
            tasks@.len() == t,
            forall|i: int| 0 <= i < t ==> {
                &&& (#[trigger] tasks@[i]).pre()
                &&& tasks@[i].cols == *c
                &&& tasks@[i].q0 == tb(a as int, b as int, chunk as int, nt as int, i)
                &&& tasks@[i].q1 == tb(a as int, b as int, chunk as int, nt as int, i + 1)
                &&& tasks@[i].lo == lo
                &&& tasks@[i].hi == hi
                &&& tasks@[i].k == k
            },
        decreases nt - t,
    {
        proof {
            lemma_tb(a as int, b as int, chunk as int, nt as int, t as int, t + 1);
        }
        let q0 = a + chunk * t;
        let q1 = if t + 1 == nt { b } else { a + chunk * (t + 1) };
        let (flags, tbuf, key): (Vec<u8>, Vec<u16>, Vec<u16>) = if fast {
            (vec![0u8; FLAGS_LEN], vec![0u16; OB], vec![0u16; OB])
        } else {
            (Vec::new(), Vec::new(), Vec::new())
        };
        let task = ScanTask { cols: *c, q0, q1, lo, hi, k, counts: filled(k, 0usize), fast, zmax, flags, tbuf, key };
        proof {
            assert(task.counts@ =~= zeros(k as nat));
        }
        tasks.push(task);
        t = t + 1;
    }
    (tasks, Ghost(chunk as int))
}

/// Per-entry sums of the task outputs: the counts over `[a, b)`.
fn merge_counts(c: &Cols, k: usize, a: usize, b: usize, lo: i64, hi: i64, chunk: Ghost<int>, tv: Ghost<Seq<ScanTask>>,
    outs: &Vec<Vec<usize>>) -> (sums: Vec<usize>)
    requires
        a <= b,
        tv@.len() >= 1,
        chunk@ >= 0,
        chunk@ * tv@.len() <= b - a,
        outs@.len() == tv@.len(),
        forall|i: int| 0 <= i < tv@.len() ==> {
            &&& (#[trigger] tv@[i]).post(outs@[i])
            &&& tv@[i].cols == *c
            &&& tv@[i].q0 == tb(a as int, b as int, chunk@, tv@.len() as int, i)
            &&& tv@[i].q1 == tb(a as int, b as int, chunk@, tv@.len() as int, i + 1)
            &&& tv@[i].lo == lo
            &&& tv@[i].hi == hi
            &&& tv@[i].k == k
        },
    ensures
        sums@.len() == k,
        forall|d: int| 0 <= d < k ==> #[trigger] sums@[d] as int == count_raw(*c, lo as int, hi as int, d, a as int, b as int),
{
    let ghost nt = tv@.len() as int;
    let n_out = outs.len();
    let mut sums: Vec<usize> = filled(k, 0usize);
    let mut t: usize = 0;
    proof {
        assert forall|d: int| 0 <= d < k implies #[trigger] sums@[d] as int
            == count_raw(*c, lo as int, hi as int, d, a as int, tb(a as int, b as int, chunk@, nt, 0)) by {}
    }
    while t < n_out
        invariant
            n_out == nt == outs@.len(),
            a <= b,
            1 <= nt,
            chunk@ >= 0,
            chunk@ * nt <= b - a,
            t <= nt,
            forall|i: int| 0 <= i < nt ==> {
                &&& (#[trigger] tv@[i]).post(outs@[i])
                &&& tv@[i].cols == *c
                &&& tv@[i].q0 == tb(a as int, b as int, chunk@, nt, i)
                &&& tv@[i].q1 == tb(a as int, b as int, chunk@, nt, i + 1)
                &&& tv@[i].lo == lo
                &&& tv@[i].hi == hi
                &&& tv@[i].k == k
            },
            sums@.len() == k,
            forall|d: int| 0 <= d < k ==> #[trigger] sums@[d] as int
                == count_raw(*c, lo as int, hi as int, d, a as int, tb(a as int, b as int, chunk@, nt, t as int)),
        decreases nt - t,
    {
        let ghost t0 = tb(a as int, b as int, chunk@, nt, t as int);
        let ghost t1 = tb(a as int, b as int, chunk@, nt, t + 1);
        proof {
            lemma_tb(a as int, b as int, chunk@, nt, t as int, t + 1);
            lemma_tb(a as int, b as int, chunk@, nt, 0, t as int);
        }
        let ot = &outs[t];
        proof {
            let task = tv@[t as int];
            assert(task.post(outs@[t as int]));
            assert(outs@[t as int]@.len() == k);
            assert(ot@ == outs@[t as int]@);
            assert(task.q0 as int == t0 && task.q1 as int == t1);
            assert forall|e: int| 0 <= e < k implies #[trigger] ot@[e] as int == count_raw(*c, lo as int, hi as int, e, t0, t1) by {
                assert(outs@[t as int]@[e] as int == count_raw(task.cols, task.lo as int, task.hi as int, e, task.q0 as int, task.q1 as int));
            }
        }
        let mut d: usize = 0;
        while d < k
            invariant
                a <= t0 <= t1 <= b,
                sums@.len() == k,
                ot@.len() == k,
                d <= k,
                forall|e: int| 0 <= e < k ==> #[trigger] ot@[e] as int == count_raw(*c, lo as int, hi as int, e, t0, t1),
                forall|e: int| 0 <= e < d ==> #[trigger] sums@[e] as int == count_raw(*c, lo as int, hi as int, e, a as int, t1),
                forall|e: int| d <= e < k ==> #[trigger] sums@[e] as int == count_raw(*c, lo as int, hi as int, e, a as int, t0),
            decreases k - d,
        {
            proof {
                lemma_count_split(*c, lo as int, hi as int, d as int, a as int, t0, t1);
                lemma_count_bound(*c, lo as int, hi as int, d as int, a as int, t1);
                assert(sums@[d as int] as int == count_raw(*c, lo as int, hi as int, d as int, a as int, t0));
                assert(ot@[d as int] as int == count_raw(*c, lo as int, hi as int, d as int, t0, t1));
            }
            let s = sums[d] + ot[d];
            sums[d] = s;
            d = d + 1;
        }
        t = t + 1;
    }
    proof {
        assert(tb(a as int, b as int, chunk@, nt, nt) == b);
    }
    sums
}

/// Counts per dictionary entry over `[a, b)`: parallel scan tasks when the lineitem rows follow the orders,
/// else the serial fallback.
fn count_range(c: &Cols, k: usize, a: usize, b: usize, lo: i64, hi: i64, clustered: bool, fast: bool,
    zmax: &'static [i64], workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<usize>, WorkerFailure>)
    requires
        cols_ok(*c, k as int),
        keys_distinct(*c),
        clustered ==> lines_clustered(*c),
        fast ==> clustered && fast_ok(*c, k as int),
        zmax@.len() == c.od_bases@.len(),
        forall|q: int| 0 <= q < c.n_o ==> #[trigger] odate(*c, q) <= zmax@[q / c.bs_o as int],
        a <= b <= c.n_o,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(v) ==> v@.len() == k
            && forall|d: int| 0 <= d < k ==> #[trigger] v@[d] as int == count_raw(*c, lo as int, hi as int, d, a as int, b as int),
{
    if !clustered {
        return Ok(count_fallback(c, k, a, b, lo, hi));
    }
    if fast && workers == 1 {
        // One worker: the scan runs on the calling thread (no thread start, and the core is already running).
        let counts = filled(k, 0usize);
        proof {
            assert forall|d: int| 0 <= d < k implies #[trigger] counts@[d] == 0 by {}
        }
        return Ok(run_fast(*c, k, zmax, a, b, lo, hi, counts, vec![0u8; FLAGS_LEN], vec![0u16; OB], vec![0u16; OB]));
    }
    let (tasks, chunk) = make_tasks(c, k, a, b, lo, hi, fast, zmax, workers);
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(f) => return Err(f),
    };
    Ok(merge_counts(c, k, a, b, lo, hi, chunk, Ghost(tv), &outs))
}

/// The first dictionary entry whose count exceeds int8, if any.
fn find_overflow(totals: &Vec<usize>) -> (r: Option<usize>)
    ensures
        r matches Some(d) ==> d < totals@.len() && totals@[d as int] > int8_max(),
        r is None ==> forall|d: int| 0 <= d < totals@.len() ==> #[trigger] totals@[d] <= int8_max(),
{
    let k = totals.len();
    let mut d: usize = 0;
    while d < k
        invariant
            k == totals@.len(),
            d <= k,
            forall|e: int| 0 <= e < d ==> #[trigger] totals@[e] <= int8_max(),
        decreases k - d,
    {
        if totals[d] as u128 > i64::MAX as u128 {
            return Some(d);
        }
        d = d + 1;
    }
    None
}

/// One row `[entry text, count]` per dictionary entry with a nonzero count, in dictionary order.
fn build_rows(doffs: &[u64], dbytes: &[u8], totals: &Vec<usize>) -> (r: (Vec<Vec<EVal>>, Ghost<Seq<int>>))
    requires
        doffs@.len() >= 1,
        totals@.len() == doffs@.len() - 1,
        text_parts_wf(doffs@, dbytes@, doffs@.len() - 1),
        forall|e: int| 0 <= e < totals@.len() ==> #[trigger] totals@[e] <= int8_max(),
    ensures
        entries_ok(totals@, r.1@),
        r.0@.len() == r.1@.len(),
        forall|i: int| 0 <= i < r.0@.len() ==> #[trigger] view_row(r.0@[i]@) == entry_row(doffs@, dbytes@, totals@, r.1@[i]),
{
    let k = totals.len();
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let ghost mut ds: Seq<int> = Seq::empty();
    let mut d: usize = 0;
    while d < k
        invariant
            k == totals@.len(),
            k == doffs@.len() - 1,
            text_parts_wf(doffs@, dbytes@, k as int),
            d <= k,
            forall|e: int| 0 <= e < k ==> #[trigger] totals@[e] <= int8_max(),
            rows@.len() == ds.len(),
            forall|i: int| 0 <= i < ds.len() ==> #[trigger] view_row(rows@[i]@) == entry_row(doffs@, dbytes@, totals@, ds[i]),
            forall|i: int| 0 <= i < ds.len() ==> 0 <= #[trigger] ds[i] < d && totals@[ds[i]] > 0,
            forall|i: int, j: int| 0 <= i < j < ds.len() ==> #[trigger] ds[i] < #[trigger] ds[j],
            forall|e: int| 0 <= e < d && #[trigger] totals@[e] > 0 ==> ds.contains(e),
        decreases k - d,
    {
        let ghost ds0 = ds;
        if totals[d] > 0 {
            proof {
                assert(text_range_ok(doffs@, dbytes@, d as int));
            }
            let txt = copy_text(doffs, dbytes, d);
            let cnt = totals[d] as i64;
            let mut row: Vec<EVal> = Vec::new();
            row.push(EVal::Text(txt));
            row.push(EVal::Int(cnt));
            proof {
                assert(view_row(row@) =~= entry_row(doffs@, dbytes@, totals@, d as int));
            }
            rows.push(row);
            proof {
                ds = ds.push(d as int);
                assert(ds[ds.len() - 1] == d as int);
            }
        }
        proof {
            assert forall|e: int| 0 <= e < d + 1 && #[trigger] totals@[e] > 0 implies ds.contains(e) by {
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

/// TPC-H Q4 over storage `facts`.
pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures
        answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost parts = facts_parts(stores.li_ordruns@);
    let ghost ps = params@;
    let ghost db0 = choose|db: Database| #[trigger] bound_db(sv, db);
    proof {
        lemma_bound(sv, db0);
        lemma_parts_shape(db0, parts);
    }
    let (lo_day, hi_res) = date_window(params);
    let (c, doffs, dbytes, zmax, flag) = open_model(&mut stores.li_ordruns, Ghost(db0));
    let k = doffs.len() - 1;

    // An error of `$1 + 3 months` is the statement's error unless orders is empty.
    let hi_day = match hi_res {
        Ok(h) => h,
        Err(e) => {
            if c.n_o > 0 {
                proof {
                    lemma_meets_date_err(sv, ps, e);
                }
                return Ok(Answer::SqlError(e));
            }
            lo_day
        },
    };
    proof {
        lemma_model_facts(db0, parts, c, doffs@, dbytes@, zmax@);
    }
    let (a, b) = candidate_range(&c, Ghost(k as int), zmax, lo_day, hi_day);
    // The run-length scan needs one run per stored orders row and the last line's order present (`lemma_runs_aligned`).
    let mut fast = false;
    if flag == 1 && c.rl.len() == c.n_o && c.n_o > 0 && c.n_l > 0 {
        proof {
            lemma_runs_model(db0, sv.li_ordruns, c);
        }
        if order_pos_at(&c, Ghost(k as int), c.n_l - 1) < c.n_o {
            proof {
                lemma_runs_aligned(c);
            }
            fast = true;
        }
    }
    let totals = match count_range(&c, k, a, b, lo_day, hi_day, flag == 1, fast, zmax, workers, dispatch) {
        Ok(v) => v,
        Err(f) => return Err(QueryError::WorkerFailed(f)),
    };
    proof {
        let (lo, hi) = (lo_day as int, hi_day as int);
        assert forall|d: int| 0 <= d < k implies #[trigger] totals@[d] as int == count_raw(c, lo, hi, d, 0, c.n_o as int) by {
            lemma_count_split(c, lo, hi, d, 0, a as int, c.n_o as int);
            lemma_count_split(c, lo, hi, d, a as int, b as int, c.n_o as int);
            lemma_count_none(c, lo, hi, d, 0, a as int);
            lemma_count_none(c, lo, hi, d, b as int, c.n_o as int);
        }
        lemma_meets_totals(sv, c, doffs@, dbytes@, ps, hi, totals@);
    }

    // COUNT(*) beyond int8 is error 22003.
    if let Some(d) = find_overflow(&totals) {
        proof {
            lemma_meets_overflow(sv, doffs@, dbytes@, ps, hi_day as int, totals@, d as int);
        }
        return Ok(Answer::SqlError(SqlError::NumericValueOutOfRange));
    }

    let (rows, ds) = build_rows(doffs, dbytes, &totals);
    proof {
        lemma_meets_rows(sv, c, doffs@, dbytes@, ps, hi_day as int, totals@, ds@, rows);
    }
    Ok(Answer::Rows(rows))
}

} // verus!
