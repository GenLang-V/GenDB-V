//! TPC-H Q6 over the storage `facts`: `SUM(l_extendedprice * l_discount)` of the lineitem rows with
//! `$1 <= l_shipdate < $1 + 1 year`, `l_discount BETWEEN $2 - 0.01 AND $2 + 0.01` and `l_quantity < $3`.
//!
//! Plan: compute the exact bounds of the condition once, read the four code parts and the per-group base / zone
//! parts of lineitem as whole extents, split the row groups into contiguous ranges of about equal scan cost
//! (groups the zone map skips cost nothing) and scan each range on its own thread (`scan::scan_groups`), then add
//! the partial sums in range order. The proof: each range's result is the normal form's accumulator over its
//! stored rows (`scan`), the ranges cover the groups in order, and the normal form over the stored rows is the
//! SQL meaning for every database bound to the parts (`norm`).
use vstd::prelude::*;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db, outcome_ok};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::stored::StoredParts;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::parallel::{Dispatch, fork_join, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::exec::value::EVal;
use crate::exec::datetime::{date_from_civil_exec, date_to_ts_exec, ts_add_interval_exec, floor_divmod};
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::datetime::*;
use crate::spec::limits::USECS_PER_DAY;
use crate::link::query::*;
use crate::link::expr::i128_max;
use crate::query::{param_domain, query_spec_at};
use crate::stores::facts::interface::*;
use crate::stores::facts::interface::common::colfmt::*;
use crate::stores::li_bits::interface as LB;
use bits::*;
use common::bitwords::bit64;
use crate::spec::value::Database;

pub mod bits;
pub mod common;
pub mod norm;
pub mod scan;

use norm::*;
use scan::*;

verus! {

/// One worker's share: the row groups `g_lo .. g_hi`.
pub struct ScanTask {
    pub cols: Cols,
    pub bits: Bits,
    pub g_lo: usize,
    pub g_hi: usize,
    pub b: Bnd,
    pub parts: Ghost<Seq<PartView>>,
}

impl WorkerTask for ScanTask {
    type Output = (i128, i128, u64, bool);

    open spec fn pre(&self) -> bool {
        cols_ok(self.cols, self.parts@) && bits_rows_ok(self.bits, self.b, self.parts@) && self.g_lo <= self.g_hi <= self.cols.ng
    }

    open spec fn post(&self, out: (i128, i128, u64, bool)) -> bool {
        &&& partial_ok(out, qs(self.b), xs_parts(self.parts@).subrange(
                self.cols.gs@[self.g_lo as int] as int, self.cols.gs@[self.g_hi as int] as int))
        &&& out.3 ==> out.2 <= self.cols.gs@[self.g_hi as int] - self.cols.gs@[self.g_lo as int]
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.g_lo as u64, self.g_hi as u64)
    }

    fn run(self) -> (out: (i128, i128, u64, bool)) {
        scan_groups(self.cols, self.bits, self.g_lo, self.g_hi, self.b, false, Ghost(self.parts@))
    }
}

/// Scan cost of a group: 0 when the zone map skips it, 7 bytes per row inside the date range, 9 across it.
fn group_cost(sb: i64, sz: i64, b: Bnd) -> (w: u64)
    ensures w <= 9,
{
    if sb < b.hi && sz >= b.lo {
        if sb >= b.lo && sz < b.hi { 7 } else { 9 }
    } else {
        0
    }
}

/// The one result row `[v]`.
fn one_row(v: EVal) -> (rows: Vec<Vec<EVal>>)
    ensures view_rows(rows@) == seq![seq![v@]],
{
    let mut row: Vec<EVal> = Vec::new();
    row.push(v);
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    rows.push(row);
    proof {
        assert(crate::exec::value::view_row(rows@[0]@) =~= seq![v@]);
        assert(view_rows(rows@) =~= seq![seq![v@]]);
    }
    rows
}

/// The day range of the parameter domain fits `i32`.
proof fn lemma_date_domain()
    ensures -800000 <= date_from_civil(1, 1, 1), date_from_civil(9999, 12, 31) <= 3000000,
{
    assert(-800000 <= date_from_civil(1, 1, 1)) by (compute);
    assert(date_from_civil(9999, 12, 31) <= 3000000) by (compute);
}

/// The SUM of the qualifying rows, or NULL without one, as the statement's answer.
fn finish_ok(sum: i128, cnt: u64, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>, Ghost(b): Ghost<Bnd>)
    -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(sv),
        bounds_ok(ps, b.lo as int, b.hi as int, b.dlo as int, b.dhi as int, b.qhi as int) || n_rows(lbf(sv)) == 0,
        gsum(qs(b), xs_parts(lbf(sv)), ek(), 0) == sum,
        gabs(qs(b), xs_parts(lbf(sv)), ek(), 0) <= i128_max(),
        gcount(qs(b), xs_parts(lbf(sv)), ek()) == cnt,
    ensures answer_meets(sv, ps, r),
{
    let v = if cnt == 0 { EVal::Null } else { EVal::Num { coeff: sum, scale: 4 } };
    let rows = one_row(v);
    proof {
        assert(v@ == result_val(sum as int, cnt as int));
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
            lemma_outcome_ok(sv, db, ps, b.lo as int, b.hi as int, b.dlo as int, b.dhi as int, b.qhi as int, sum as int, cnt as int);
        }
    }
    Ok(Answer::Rows(rows))
}

/// `$1` or `$1 + 1 year` is past the timestamp range (error `e` of `$1 + INTERVAL '1' YEAR`): the statement's
/// meaning is that error on a non-empty table, the NULL sum on an empty one.
fn finish_err(e: SqlError, n: usize, Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(sv),
        param_domain(ps),
        n == n_rows(lbf(sv)),
        eval_expr_hi_err(ps, e),
    ensures answer_meets(sv, ps, r),
{
    if n == 0 {
        proof {
            let b = Bnd { lo: 0, hi: 0, dlo: 0, dhi: 0, qhi: 0 };
            assert(xs_parts(lbf(sv)) =~= Seq::<Row>::empty());
        }
        return finish_ok(0, 0, Ghost(sv), Ghost(ps), Ghost(Bnd { lo: 0, hi: 0, dlo: 0, dhi: 0, qhi: 0 }));
    }
    proof {
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::SqlError(e))) by {
            lemma_outcome_err(sv, db, ps, e);
        }
    }
    Ok(Answer::SqlError(e))
}

/// The extents the scan reads: the per-group parts and the code parts of lineitem, whole.
fn read_cols(f: &mut StoredParts, n: usize, Ghost(parts): Ghost<Seq<PartView>>) -> (c: Cols)
    requires
        LB::facts_parts(old(f)@) == parts,
        old(f)@.len() == LB::LI_BITS_PARTS,
        shape_ok(parts),
        n == n_rows(parts),
    ensures
        final(f)@ == old(f)@,
        cols_ok(c, parts),
{
    proof {
        assert forall|k: int| 0 <= k < FACTS_PARTS implies #[trigger] f@[k] == parts[k] by {}
    }
    let ng1 = f.part_len(LI_GROUPS);
    proof {
        lemma_groups_bounds(gsv(parts), n_rows(parts), 0);
    }
    let ng = ng1 - 1;
    let gs = f.extent_u64(LI_GROUPS, 0, ng1);
    let ship_base = f.extent_i64(LI_SHIPDATE_BASE, 0, ng);
    let ship_zmax = f.extent_i64(LI_SHIPDATE_ZMAX, 0, ng);
    let disc_base = f.extent_i64(LI_DISCOUNT_BASE, 0, ng);
    let qty_base = f.extent_i64(LI_QUANTITY_BASE, 0, ng);
    let price_base = f.extent_i64(LI_EXTENDEDPRICE_BASE, 0, ng);
    let ship = f.extent_u16(LI_SHIPDATE_CODES, 0, n);
    let disc = f.extent_u8(LI_DISCOUNT_CODES, 0, n);
    let qty = f.extent_u16(LI_QUANTITY_CODES, 0, n);
    let price = f.extent_u32(LI_EXTENDEDPRICE_CODES, 0, n);
    let c = Cols { gs, ship, disc, qty, price, ship_base, ship_zmax, disc_base, qty_base, price_base, ng, n };
    proof {
        assert(gs@ =~= gsv(parts));
        assert(ship@ =~= parts[LI_SHIPDATE_CODES as int]->U16_0);
        assert(disc@ =~= parts[LI_DISCOUNT_CODES as int]->U8_0);
        assert(qty@ =~= parts[LI_QUANTITY_CODES as int]->U16_0);
        assert(price@ =~= parts[LI_EXTENDEDPRICE_CODES as int]->U32_0);
        assert(ship_base@ =~= i64s(parts[LI_SHIPDATE_BASE as int]));
        assert(ship_zmax@ =~= i64s(parts[LI_SHIPDATE_ZMAX as int]));
        assert(disc_base@ =~= i64s(parts[LI_DISCOUNT_BASE as int]));
        assert(qty_base@ =~= i64s(parts[LI_QUANTITY_BASE as int]));
        assert(price_base@ =~= i64s(parts[LI_EXTENDEDPRICE_BASE as int]));
    }
    c
}

/// Total scan cost of the groups (saturating).
fn total_cost(c: Cols, b: Bnd, Ghost(parts): Ghost<Seq<PartView>>) -> (w: u64)
    requires cols_ok(c, parts),
{
    let mut w: u64 = 0;
    let mut gi: usize = 0;
    while gi < c.ng
        invariant cols_ok(c, parts), gi <= c.ng,
        decreases c.ng - gi,
    {
        let x = group_cost(c.ship_base[gi], c.ship_zmax[gi], b);
        w = if w <= u64::MAX - x { w + x } else { w };
        gi = gi + 1;
    }
    w
}

/// The tasks `k` of a partition `bnds` of the groups (task `k` covers groups `bnds[k] .. bnds[k + 1]`).
pub open spec fn tasks_ok(tasks: Seq<ScanTask>, bnds: Seq<int>, c: Cols, bt: Bits, b: Bnd, parts: Seq<PartView>) -> bool {
    &&& bnds.len() == tasks.len() + 1
    &&& bnds[0] == 0
    &&& forall|k: int| 0 <= k < tasks.len() ==> {
        &&& (#[trigger] tasks[k]).g_lo == bnds[k]
        &&& tasks[k].g_hi == bnds[k + 1]
        &&& tasks[k].cols == c
        &&& tasks[k].bits == bt
        &&& tasks[k].b == b
        &&& tasks[k].parts@ == parts
        &&& tasks[k].pre()
    }
}

/// Cumulative cost goal after task `t` of `ntasks`. `fork_join` spawns the last task first and task 0 last, so
/// task `t` starts about `(ntasks - 1 - t)` spawn delays late; its share of the cost falls linearly with that
/// delay: weight `1 - beta * (ntasks - 1 - t) / (ntasks - 1)` with `beta = ntasks / 200`, i.e. the goal is
/// `total * N(t) / D` with `N(t) = 2000 (n - 1)(t + 1) - B (2 (t + 1)(n - 1) - t (t + 1))`, `D = n (n - 1)(2000 - B)`,
/// `B = 5 n` (`N(n - 1) = D`).
fn cost_goal(total: u64, t: usize, ntasks: usize) -> (goal: u128)
    requires 2 <= ntasks <= MAX_WORKERS, t < ntasks,
{
    let n = ntasks as u128;
    let k = t as u128 + 1;
    let bb: u128 = 5 * n;
    proof {
        assert(k * (n - 1) <= 64 * 64) by (nonlinear_arith) requires 1 <= k <= n, 2 <= n <= 64;
        assert((k - 1) * k <= k * (n - 1)) by (nonlinear_arith) requires 1 <= k <= n;
        assert(0 <= (k - 1) * k) by (nonlinear_arith) requires 1 <= k;
    }
    let a = k * (n - 1);
    let c = (k - 1) * k;
    let inner = 2 * a - c;
    proof {
        assert(bb * inner <= 320 * 8192) by (nonlinear_arith) requires bb <= 320, inner <= 8192;
        assert(bb * inner <= 2000 * a) by (nonlinear_arith) requires bb <= 320, inner <= 2 * a, a >= 0;
        assert(n * (n - 1) <= 64 * 64) by (nonlinear_arith) requires 2 <= n <= 64;
        assert(n * (n - 1) >= 1) by (nonlinear_arith) requires 2 <= n;
    }
    let num = 2000 * a - bb * inner;
    let nn1 = n * (n - 1);
    proof {
        assert(nn1 * (2000 - bb) >= 1) by (nonlinear_arith) requires nn1 >= 1, bb <= 320;
        assert(nn1 * (2000 - bb) <= 4096 * 2000) by (nonlinear_arith) requires nn1 <= 4096, bb <= 320;
        assert(total as u128 * num <= 0xffff_ffff_ffff_ffff * (2000 * 4096)) by (nonlinear_arith)
            requires total <= 0xffff_ffff_ffff_ffff, num <= 2000 * 4096;
    }
    let den = nn1 * (2000 - bb);
    (total as u128) * num / den
}

/// `ntasks` contiguous group ranges of about equal scan cost, covering every group.
fn make_tasks(c: Cols, bt: Bits, b: Bnd, ntasks: usize, Ghost(parts): Ghost<Seq<PartView>>) -> (r: (Vec<ScanTask>, Ghost<Seq<int>>))
    requires
        cols_ok(c, parts),
        bits_rows_ok(bt, b, parts),
        2 <= ntasks <= MAX_WORKERS,
    ensures
        r.0@.len() == ntasks,
        tasks_ok(r.0@, r.1@, c, bt, b, parts),
        r.1@[ntasks as int] == c.ng,
{
    let total = total_cost(c, b, Ghost(parts));
    let mut tasks: Vec<ScanTask> = Vec::new();
    let ghost mut bnds: Seq<int> = seq![0int];
    let mut a: usize = 0;
    let mut done: u64 = 0;
    let mut t: usize = 0;
    while t < ntasks
        invariant
            cols_ok(c, parts),
            bits_rows_ok(bt, b, parts),
            2 <= ntasks <= MAX_WORKERS,
            t <= ntasks,
            a <= c.ng,
            t < ntasks || a == c.ng,
            tasks@.len() == t,
            bnds[t as int] == a,
            tasks_ok(tasks@, bnds, c, bt, b, parts),
        decreases ntasks - t,
    {
        proof {
            assert(total as int * (t + 1) <= 0xffff_ffff_ffff_ffff * 64) by (nonlinear_arith)
                requires total <= 0xffff_ffff_ffff_ffff, t + 1 <= 64;
        }
        let goal = cost_goal(total, t, ntasks);
        let mut e: usize = a;
        while e < c.ng && (done as u128) < goal
            invariant cols_ok(c, parts), a <= e <= c.ng,
            decreases c.ng - e,
        {
            let x = group_cost(c.ship_base[e], c.ship_zmax[e], b);
            done = if done <= u64::MAX - x { done + x } else { done };
            e = e + 1;
        }
        let e = if t + 1 == ntasks { c.ng } else { e };
        let task = ScanTask { cols: c, bits: bt, g_lo: a, g_hi: e, b, parts: Ghost(parts) };
        let ghost old_tasks = tasks@;
        tasks.push(task);
        proof {
            bnds = bnds.push(e as int);
            assert forall|k: int| 0 <= k < tasks@.len() implies {
                &&& (#[trigger] tasks@[k]).g_lo == bnds[k]
                &&& tasks@[k].g_hi == bnds[k + 1]
                &&& tasks@[k].cols == c
                &&& tasks@[k].bits == bt
                &&& tasks@[k].b == b
                &&& tasks@[k].parts@ == parts
                &&& tasks@[k].pre()
            } by {
                if k < t {
                    assert(tasks@[k] == old_tasks[k]);
                }
            }
        }
        a = e;
        t = t + 1;
    }
    (tasks, Ghost(bnds))
}

/// Adds the task outputs in range order: the partial result of all groups.
fn merge(outs: &Vec<(i128, i128, u64, bool)>, Ghost(tv): Ghost<Seq<ScanTask>>, Ghost(bnds): Ghost<Seq<int>>, c: Cols, bt: Bits, b: Bnd,
    Ghost(parts): Ghost<Seq<PartView>>) -> (r: (i128, i128, u64, bool))
    requires
        cols_ok(c, parts),
        tasks_ok(tv, bnds, c, bt, b, parts),
        bnds[tv.len() as int] == c.ng,
        outs@.len() == tv.len(),
        forall|k: int| 0 <= k < tv.len() ==> (#[trigger] tv[k]).post(outs@[k]),
    ensures
        partial_ok(r, qs(b), xs_parts(parts)),
{
    let ghost g = qs(b);
    let ghost xs = xs_parts(parts);
    let ghost gs = gsv(parts);
    let ghost nr = n_rows(parts);
    let mut sum: i128 = 0;
    let mut mass: i128 = 0;
    let mut cnt: u64 = 0;
    let mut i: usize = 0;
    proof {
        lemma_empty(g, xs, 0, ek(), 0);
        lemma_groups_bounds(gs, nr, 0);
        lemma_groups_bounds(gs, nr, c.ng as int);
        assert(xs.subrange(0, nr) =~= xs);
    }
    while i < outs.len()
        invariant
            cols_ok(c, parts),
            tasks_ok(tv, bnds, c, bt, b, parts),
            bnds[tv.len() as int] == c.ng,
            outs@.len() == tv.len(),
            forall|k: int| 0 <= k < tv.len() ==> (#[trigger] tv[k]).post(outs@[k]),
            i <= tv.len(),
            g == qs(b),
            xs == xs_parts(parts),
            gs == gsv(parts),
            nr == n_rows(parts),
            xs.subrange(0, nr) == xs,
            0 <= bnds[i as int] <= c.ng,
            sum == gsum(g, xs.subrange(0, gs[bnds[i as int]] as int), ek(), 0),
            mass == gabs(g, xs.subrange(0, gs[bnds[i as int]] as int), ek(), 0),
            cnt == gcount(g, xs.subrange(0, gs[bnds[i as int]] as int), ek()),
            cnt <= gs[bnds[i as int]],
        decreases outs.len() - i,
    {
        let (s, m, k, o) = outs[i];
        let ghost lo_g = bnds[i as int];
        let ghost hi_g = bnds[i + 1];
        let ghost r_lo = gs[lo_g] as int;
        let ghost r_hi = gs[hi_g] as int;
        proof {
            assert(tv[i as int].post(outs@[i as int]));
            assert(tv[i as int].pre());
            lemma_groups_bounds(gs, nr, lo_g);
            lemma_groups_bounds(gs, nr, hi_g);
            if lo_g < hi_g {
                lemma_groups_mono(gs, nr, lo_g, hi_g);
            }
            lemma_groups_bounds(gs, nr, c.ng as int);
            lemma_split(g, xs, 0, r_lo, r_hi, ek(), 0);
            lemma_abs_bound(g, xs.subrange(0, r_lo), ek(), 0);
        }
        if !o {
            proof {
                lemma_abs_mono(g, xs, 0, r_lo, r_hi, nr);
            }
            return (sum, mass, cnt, false);
        }
        proof {
            lemma_abs_bound(g, xs.subrange(r_lo, r_hi), ek(), 0);
        }
        if mass > i128::MAX - m {
            proof {
                lemma_abs_mono(g, xs, 0, 0, r_hi, nr);
            }
            return (sum, mass, cnt, false);
        }
        proof {
            lemma_abs_bound(g, xs.subrange(0, r_hi), ek(), 0);
            assert(r_hi <= c.n);
        }
        sum = sum + s;
        mass = mass + m;
        cnt = cnt + k;
        i = i + 1;
    }
    (sum, mass, cnt, true)
}

/// The partial result of all stored rows: serially, or over `ntasks` threads.
fn scan_all(c: Cols, bt: Bits, b: Bnd, workers: usize, dispatch: &mut Dispatch, Ghost(parts): Ghost<Seq<PartView>>)
    -> (r: Result<(i128, i128, u64, bool), QueryError>)
    requires
        cols_ok(c, parts),
        bits_rows_ok(bt, b, parts),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(p) ==> partial_ok(p, qs(b), xs_parts(parts)),
        r matches Err(e) ==> e is WorkerFailed,
{
    proof {
        lemma_groups_bounds(gsv(parts), n_rows(parts), 0);
        lemma_groups_bounds(gsv(parts), n_rows(parts), c.ng as int);
        assert(xs_parts(parts).subrange(0, n_rows(parts)) =~= xs_parts(parts));
    }
    // The scan is memory-bandwidth bound: about 20-24 threads already saturate it (measured: 32 or 64 threads are
    // ~10% slower than 20-24 through contention and thread start cost), so cap the task count.
    let cap = if workers >= 64 { 24 } else if workers >= 32 { 20 } else { workers };
    let ntasks = if cap < c.ng { cap } else { c.ng };
    if ntasks <= 1 {
        return Ok(scan_groups(c, bt, 0, c.ng, b, true, Ghost(parts)));
    }
    let (tasks, Ghost(bnds)) = make_tasks(c, bt, b, ntasks, Ghost(parts));
    let ghost tv = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(w) => return Err(QueryError::WorkerFailed(w)),
    };
    Ok(merge(&outs, Ghost(tv), Ghost(bnds), c, bt, b, Ghost(parts)))
}

/// The index of key `x` among `keys`, if any.
fn find_key(keys: &[i64], x: i64) -> (r: Option<usize>)
    ensures r matches Some(k) ==> k < keys@.len() && keys@[k as int] == x,
{
    let mut k: usize = 0;
    while k < keys.len()
        invariant k <= keys@.len(),
        decreases keys@.len() - k,
    {
        if keys[k] == x {
            return Some(k);
        }
        k = k + 1;
    }
    None
}

/// The selected bitmaps state the rows' discount / quantity / shipdate conditions (from `li_bits::bits_ok`).
proof fn lemma_bits_rows(lb: Seq<PartView>, bt: Bits, b: Bnd, ka: int, kb: int, kc: int, tq: int)
    requires
        LB::bits_ok(lb),
        lb.len() == LB::LI_BITS_PARTS,
        bt.on,
        bnd_bits_ok(bt, b),
        bt.dbits@ == u64s(lb[LB::DISC_BITS as int]),
        bt.qbits@ == u64s(lb[LB::QTY_BITS as int]),
        bt.sbits@ == u64s(lb[LB::SHIP_BITS as int]),
        bt.skeys@ == i64s(lb[LB::SHIP_KEYS as int]),
        bt.nw == LB::n_words(lb),
        bt.ns == LB::n_ship(lb),
        0 <= ka < LB::n_disc(lb) && i64s(lb[LB::DISC_KEYS as int])[ka] == b.dlo && bt.oa == ka * bt.nw,
        0 <= kb < LB::n_disc(lb) && i64s(lb[LB::DISC_KEYS as int])[kb] == b.dlo + 1 && bt.ob == kb * bt.nw,
        0 <= kc < LB::n_disc(lb) && i64s(lb[LB::DISC_KEYS as int])[kc] == b.dlo + 2 && bt.oc == kc * bt.nw,
        0 <= tq < LB::n_qty(lb) && i64s(lb[LB::QTY_KEYS as int])[tq] == b.qhi && bt.oq == tq * bt.nw,
        bt.dbits@.len() <= usize::MAX && bt.qbits@.len() <= usize::MAX,
        bt.sbits@.len() <= usize::MAX && bt.skeys@.len() <= usize::MAX,
    ensures
        bits_rows_ok(bt, b, LB::facts_parts(lb)),
{
    assert(LB::bits_shape(lb));
    let parts = LB::facts_parts(lb);
    let n = n_rows(parts);
    let nw = bt.nw as int;
    assert(LB::n_rows(parts) == n);
    assert(LB::gsv(parts) == gsv(parts));
    assert(bt.oa + nw <= bt.dbits@.len()) by {
        assert(ka * nw + nw <= LB::n_disc(lb) * nw) by (nonlinear_arith) requires ka + 1 <= LB::n_disc(lb), 0 <= nw;
    }
    assert(bt.ob + nw <= bt.dbits@.len()) by {
        assert(kb * nw + nw <= LB::n_disc(lb) * nw) by (nonlinear_arith) requires kb + 1 <= LB::n_disc(lb), 0 <= nw;
    }
    assert(bt.oc + nw <= bt.dbits@.len()) by {
        assert(kc * nw + nw <= LB::n_disc(lb) * nw) by (nonlinear_arith) requires kc + 1 <= LB::n_disc(lb), 0 <= nw;
    }
    assert(bt.oq + nw <= bt.qbits@.len()) by {
        assert(tq * nw + nw <= LB::n_qty(lb) * nw) by (nonlinear_arith) requires tq + 1 <= LB::n_qty(lb), 0 <= nw;
    }
    assert forall|j: int| 0 <= j < n implies {
        &&& #[trigger] wbit(bt.dbits@, bt.oa as int, j) == (disc_at(parts, j) == b.dlo)
        &&& wbit(bt.dbits@, bt.ob as int, j) == (disc_at(parts, j) == b.dlo + 1)
        &&& wbit(bt.dbits@, bt.oc as int, j) == (disc_at(parts, j) == b.dlo + 2)
        &&& wbit(bt.qbits@, bt.oq as int, j) == (qty_at(parts, j) < b.qhi)
    } by {
        assert(LB::disc_bit_ok(lb, ka, j));
        assert(LB::disc_bit_ok(lb, kb, j));
        assert(LB::disc_bit_ok(lb, kc, j));
        assert(LB::qty_bit_ok(lb, tq, j));
        assert(LB::disc_at(parts, j) == disc_at(parts, j));
        assert(LB::qty_at(parts, j) == qty_at(parts, j));
    }
    assert forall|t: int, j: int| 0 <= t < bt.ns && 0 <= j < n implies #[trigger] wbit(bt.sbits@, t * nw, j)
        == (ship_at(parts, j) < bt.skeys@[group_of(gsv(parts), j) * bt.ns + t]) by {
        assert(LB::ship_bit_ok(lb, t, j));
        assert(LB::ship_at(parts, j) == ship_at(parts, j));
        let words = u64s(lb[LB::SHIP_BITS as int]);
        assert(LB::row_bit(words, nw, t, j) == LB::bit(words[t * nw + j / 64], j % 64));
        assert(LB::bit(words[t * nw + j / 64], j % 64) == bit64(words[t * nw + j / 64], j % 64));
        assert(wbit(bt.sbits@, t * nw, j) == bit64(words[t * nw + j / 64], j % 64));
    }
}

/// The bitmaps of li_bits for the binding `b`: on when li_bits holds the discount keys `dlo, dlo + 1, dlo + 2`
/// (`dhi = dlo + 2`, `0 <= dlo <= 509`) and the quantity key `qhi`.
fn read_bits(f: &mut StoredParts, b: Bnd) -> (bt: Bits)
    requires LB::bits_ok(old(f)@), old(f)@.len() == LB::LI_BITS_PARTS,
    ensures final(f)@ == old(f)@, bits_rows_ok(bt, b, LB::facts_parts(old(f)@)),
{
    let ghost lb = f@;
    let lay = f.extent_u64(LB::BITS_LAYOUT, 0, 4);
    let nd_len = f.part_len(LB::DISC_KEYS);
    let nq_len = f.part_len(LB::QTY_KEYS);
    let dkeys = f.extent_i64(LB::DISC_KEYS, 0, nd_len);
    let qkeys = f.extent_i64(LB::QTY_KEYS, 0, nq_len);
    let dlen = f.part_len(LB::DISC_BITS);
    let qlen = f.part_len(LB::QTY_BITS);
    let slen = f.part_len(LB::SHIP_BITS);
    let sklen = f.part_len(LB::SHIP_KEYS);
    let dbits = f.extent_u64(LB::DISC_BITS, 0, dlen);
    let qbits = f.extent_u64(LB::QTY_BITS, 0, qlen);
    let sbits = f.extent_u64(LB::SHIP_BITS, 0, slen);
    let skeys = f.extent_i64(LB::SHIP_KEYS, 0, sklen);
    proof {
        assert(lay@ =~= u64s(lb[LB::BITS_LAYOUT as int]));
        assert(dkeys@ =~= i64s(lb[LB::DISC_KEYS as int]));
        assert(qkeys@ =~= i64s(lb[LB::QTY_KEYS as int]));
        assert(dbits@ =~= u64s(lb[LB::DISC_BITS as int]));
        assert(qbits@ =~= u64s(lb[LB::QTY_BITS as int]));
        assert(sbits@ =~= u64s(lb[LB::SHIP_BITS as int]));
        assert(skeys@ =~= i64s(lb[LB::SHIP_KEYS as int]));
    }
    let off = Bits { dbits, qbits, sbits, skeys, nw: 0, ns: 0, on: false, oa: 0, ob: 0, oc: 0, oq: 0, dlo: 0 };
    proof {
        assert(dbits@.len() == dlen && qbits@.len() == qlen && sbits@.len() == slen && skeys@.len() == sklen);
    }
    // the casts below are exact: nw <= |dbits| (at least one discount key) and ns <= |skeys| (at least one group)
    if !(lay[0] <= dlen as u64 && lay[3] <= sklen as u64 && 0 <= b.dlo && b.dlo <= 509 && b.dhi == b.dlo + 2) {
        return off;
    }
    let nw = lay[0] as usize;
    let ns = lay[3] as usize;
    let ka = find_key(dkeys, b.dlo);
    let kb = find_key(dkeys, b.dlo + 1);
    let kc = find_key(dkeys, b.dlo + 2);
    let tq = find_key(qkeys, b.qhi);
    match (ka, kb, kc, tq) {
        (Some(ka), Some(kb), Some(kc), Some(tq)) => {
            proof {
                let nd = LB::n_disc(lb);
                let nq = LB::n_qty(lb);
                assert(ka * nw + nw <= nd * nw) by (nonlinear_arith) requires ka + 1 <= nd, 0 <= nw;
                assert(kb * nw + nw <= nd * nw) by (nonlinear_arith) requires kb + 1 <= nd, 0 <= nw;
                assert(kc * nw + nw <= nd * nw) by (nonlinear_arith) requires kc + 1 <= nd, 0 <= nw;
                assert(tq * nw + nw <= nq * nw) by (nonlinear_arith) requires tq + 1 <= nq, 0 <= nw;
                assert(0 <= ka * nw && 0 <= kb * nw && 0 <= kc * nw && 0 <= tq * nw) by (nonlinear_arith)
                    requires 0 <= ka, 0 <= kb, 0 <= kc, 0 <= tq, 0 <= nw;
            }
            let bt = Bits {
                dbits, qbits, sbits, skeys, nw, ns, on: true,
                oa: ka * nw, ob: kb * nw, oc: kc * nw, oq: tq * nw, dlo: b.dlo as u32,
            };
            proof {
                lemma_bits_rows(lb, bt, b, ka as int, kb as int, kc as int, tq as int);
            }
            bt
        }
        _ => off,
    }
}

/// The exact bounds of the binding's condition, or the error of `$1 + INTERVAL '1' YEAR`.
fn bounds(params: &Params) -> (r: Result<Bnd, SqlError>)
    requires param_domain(params@),
    ensures
        r matches Ok(b) ==> bounds_ok(params@, b.lo as int, b.hi as int, b.dlo as int, b.dhi as int, b.qhi as int),
        r matches Err(e) ==> eval_expr_hi_err(params@, e),
{
    let ghost ps = params@;
    proof {
        lemma_param_lits(ps);
        lemma_date_domain();
    }
    let lo = date_from_civil_exec(params.p0.y as i64, params.p0.m as i64, params.p0.d as i64);
    let dlo = (params.p1 - 1) as i64;
    let dhi = (params.p1 + 1) as i64;
    let qhi = params.p2 * 100;
    proof {
        lemma_hi_eval(ps, lo as int);
    }
    let t0 = match date_to_ts_exec(lo as i32) {
        Ok(t) => t,
        Err(e) => return Err(e),
    };
    let t1 = match ts_add_interval_exec(t0, 12, 0, 0) {
        Ok(t) => t,
        Err(e) => return Err(e),
    };
    let (hi, rem) = floor_divmod(t1, USECS_PER_DAY);
    proof {
        assert(t0 == lo * usecs_per_day());
        lemma_year_later_midnight(lo as int, t1 as int);
        assert(t1 == hi * usecs_per_day());
    }
    Ok(Bnd { lo, hi, dlo, dhi, qhi })
}

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
    let ghost parts = lbf(stores@);
    proof {
        let db = choose|db: Database| #[trigger] bound_db(sv, db);
        lemma_db_link(sv, db);
    }
    proof {
        let db = choose|db: Database| #[trigger] bound_db(sv, db);
        lemma_lb_facts(sv, db);
        assert(stores@.li_bits[LI_SHIPDATE_CODES as int] == parts[LI_SHIPDATE_CODES as int]);
    }
    let n = stores.li_bits.part_len(LI_SHIPDATE_CODES);
    let b = match bounds(params) {
        Ok(b) => b,
        Err(e) => return finish_err(e, n, Ghost(sv), Ghost(ps)),
    };
    let c = read_cols(&mut stores.li_bits, n, Ghost(parts));
    let bt = read_bits(&mut stores.li_bits, b);
    let (sum, mass, cnt, ok) = match scan_all(c, bt, b, workers, dispatch, Ghost(parts)) {
        Ok(p) => p,
        Err(e) => return Err(e),
    };
    if !ok {
        proof {
            assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
                lemma_outcome_capacity(sv, db, ps, b.lo as int, b.hi as int, b.dlo as int, b.dhi as int, b.qhi as int);
            }
        }
        return Ok(Answer::Capacity);
    }
    finish_ok(sum, cnt, Ghost(sv), Ghost(ps), Ghost(b))
}

} // verus!
