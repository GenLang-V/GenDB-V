// AUTHOR MODULE ROOT (crate::agent). You own every file under src/agent/.
//! TPC-H Q14 (promotion effect) over the storages `facts` (lineitem, clustered by order date, shipdate zone maps)
//! and `custpart` (part in key order, p_type as a sorted dictionary).
//!
//! Plan: the shipdate window `[lo, hi)` of `$1` (`bounds`); the `LIKE 'PROMO%'` flag of every p_type dictionary
//! entry (`promo_table`); when the part keys are `1..n` in stored order (checked in O(1) from the stored sort flag,
//! the first and last key and the declared primary key, `dense_check`), lineitem row groups are split into ranges
//! of about equal work and scanned in parallel (`kernel::scan_range`): a group outside the window by its zone map is
//! skipped, a row inside the window finds its part at position `l_partkey - 1`. Otherwise, or when a group's bases
//! are not small, a serial nested loop computes the same totals (`general`). The answer is `100.00 * s0 / s1` on the
//! aggregate row (`out_value`, with the verified numeric operators).
//!
//! Proof: `terms` states the accumulators as sums over the stored rows of the join; `answer` proves that the
//! statement's outcome is determined by them for every database bound to the parts.
use vstd::prelude::*;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db, outcome_ok};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::parallel::{Dispatch, fork_join, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_params::Params;
use crate::exec::value::*;
use crate::exec::scalar::arith_exec;
use crate::exec::fns::div::exec_div;
use crate::exec::fns::like::like_value_exec;
use crate::exec::datetime::{date_from_civil_exec, date_to_ts_exec, ts_add_interval_exec, floor_divmod};
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::scalar::*;
use crate::spec::eval::eval_expr;
use crate::stores::facts::interface::common::colfmt::lemma_groups_bounds;
use crate::spec::datetime::*;
use crate::spec::limits::USECS_PER_DAY;
use crate::link::query::view_rows;
use crate::query::{param_domain, query_spec_at};
use crate::stores::custpart::interface::common::read::text_slice;

pub mod model;
pub mod terms;
pub mod kernel;
pub mod general;
pub mod answer;
pub mod bitmap;
pub mod outexpr;
pub mod sqlrow;
pub mod bind;
pub mod joinsum;
pub mod aggsum;

use model::*;
use terms::*;
use kernel::*;
use general::*;
use answer::*;
use bitmap::*;
use std::sync::Arc;

verus! {

// ------------------------------------------------------------------------------------------------ parameters

/// The day range of the parameter domain fits `i32`.
proof fn lemma_date_domain()
    ensures -800000 <= date_from_civil(1, 1, 1), date_from_civil(9999, 12, 31) <= 3000000,
{
    assert(-800000 <= date_from_civil(1, 1, 1)) by (compute);
    assert(date_from_civil(9999, 12, 31) <= 3000000) by (compute);
}

/// The shipdate window of the binding, or the error of `$1 + INTERVAL '1' MONTH`.
fn bounds(params: &Params) -> (r: Result<Win, SqlError>)
    requires param_domain(params@),
    ensures
        r matches Ok(w) ==> win_ok(params@, w.lo as int, w.hi as int),
        r matches Err(e) ==> hi_err(params@, e),
{
    let ghost ps = params@;
    proof {
        lemma_date_domain();
    }
    let lo = date_from_civil_exec(params.p0.y as i64, params.p0.m as i64, params.p0.d as i64);
    proof {
        lemma_hi_eval(ps, lo as int);
    }
    let t0 = match date_to_ts_exec(lo as i32) {
        Ok(t) => t,
        Err(e) => return Err(e),
    };
    let t1 = match ts_add_interval_exec(t0, 1, 0, 0) {
        Ok(t) => t,
        Err(e) => return Err(e),
    };
    let (hi, rem) = floor_divmod(t1, USECS_PER_DAY);
    proof {
        assert(t0 == lo * usecs_per_day());
        lemma_month_later_midnight(lo as int, t1 as int);
        assert(t1 == hi * usecs_per_day());
    }
    Ok(Win { lo, hi })
}

/// The literal `$1` evaluates to its day.
proof fn lemma_param_lit(ps: Seq<Literal>)
    requires param_domain(ps),
    ensures ps[0] matches Literal::Date { y, m, d } && crate::spec::eval::lit_val(ps[0]) == Ok::<Val, SqlError>(Val::Date(date_from_civil(y, m, d))),
{
}

/// The value of `$1 + INTERVAL '1' MONTH` from the day of `$1`.
proof fn lemma_hi_eval(ps: Seq<Literal>, lo: int)
    requires
        param_domain(ps),
        ps[0] matches Literal::Date { y, m, d } && lo == date_from_civil(y, m, d),
    ensures
        eval_expr(crate::link::expr::closed_db(), Seq::empty(), hi_expr(ps)) == match date_to_ts(lo) {
            Err(e) => Err::<Val, SqlError>(e),
            Ok(t0) => match ts_add_interval(t0, 1, 0, 0) {
                Ok(t1) => Ok::<Val, SqlError>(Val::Ts(t1)),
                Err(e) => Err::<Val, SqlError>(e),
            },
        },
{
    hide(crate::spec::eval::lit_val);
    lemma_param_lit(ps);
    let cdb = crate::link::expr::closed_db();
    let env = Seq::<Val>::empty();
    let lit = Expr::Lit(ps[0]);
    let c = Expr::Cast { cast: CastOp::DateToTimestamp, arg: Box::new(lit) };
    assert(eval_expr(cdb, env, lit) == Ok::<Val, SqlError>(Val::Date(lo)));
    assert(eval_expr(cdb, env, c) == cast(CastOp::DateToTimestamp, Val::Date(lo)));
}

/// `date + 1 month` of a date at midnight is a midnight.
proof fn lemma_month_later_midnight(lo: int, t: int)
    requires ts_add_interval(lo * usecs_per_day(), 1, 0, 0) == Ok::<int, SqlError>(t),
    ensures t % usecs_per_day() == 0,
{
    let u = usecs_per_day();
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(lo, u);
    let t0 = lo * u;
    assert(t0 % u == 0);
    let day = t0 / u;
    let ymd = civil_from_date(day);
    let total = ymd.0 * 12 + (ymd.1 - 1) + 1;
    let y2 = total / 12;
    let m2 = total % 12 + 1;
    let d2 = if ymd.2 <= days_in_month(y2, m2) { ymd.2 } else { days_in_month(y2, m2) };
    let k = date_from_civil(y2, m2, d2);
    assert(ts_add_months(t0, 1) == ts_result(k * u + 0));
    assert(t == k * u);
    vstd::arithmetic::div_mod::lemma_mod_multiples_basic(k, u);
}

// ------------------------------------------------------------------------------------------------ preparation

/// The bytes of a slice as a vector.
fn bytes_vec(s: &[u8]) -> (v: Vec<u8>)
    ensures v@ == s@,
{
    let mut v: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant i <= s.len(), v@ == s@.subrange(0, i as int),
        decreases s.len() - i,
    {
        v.push(s[i]);
        proof {
            assert(s@.subrange(0, i + 1) =~= s@.subrange(0, i as int).push(s@[i as int]));
        }
        i = i + 1;
    }
    proof {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }
    v
}

/// The promotion flag (`p_type LIKE 'PROMO%'`) of every p_type dictionary entry.
fn promo_table(p: &PaCols, Ghost(cp): Ghost<Seq<PartView>>) -> (r: Vec<bool>)
    requires pa_cols_ok(*p, cp),
    ensures promo_ok(r@, cp),
{
    let nd = p.d_offs.len() - 1;
    let mut pat: Vec<u8> = Vec::new();
    pat.push(80u8);
    pat.push(82u8);
    pat.push(79u8);
    pat.push(77u8);
    pat.push(79u8);
    pat.push(37u8);
    let mut esc: Vec<u8> = Vec::new();
    esc.push(92u8);
    proof {
        assert(pat@ =~= promo_pat());
        assert(esc@ =~= seq![92u8]);
    }
    let pv = EVal::Text(pat);
    let ev = EVal::Text(esc);
    let mut out: Vec<bool> = Vec::new();
    let mut e: usize = 0;
    while e < nd
        invariant
            pa_cols_ok(*p, cp),
            nd == n_td(cp),
            e <= nd,
            pv@ == Val::Text(promo_pat()),
            ev@ == Val::Text(seq![92u8]),
            out@.len() == e,
            forall|x: int| 0 <= x < e ==> #[trigger] out@[x] == promo_text(tdict(cp, x)),
        decreases nd - e,
    {
        proof {
            assert(crate::stores::custpart::interface::common::colfmt::text_range_ok(td_o(cp), td_y(cp), e as int));
        }
        let s = text_slice(p.d_offs, p.d_bytes, e);
        let sv = EVal::Text(bytes_vec(s));
        let r = like_value_exec(&sv, &pv, &ev);
        let b = match r {
            Ok(EVal::Bool(true)) => true,
            _ => false,
        };
        proof {
            assert(sv@ == Val::Text(tdict(cp, e as int)));
        }
        out.push(b);
        e = e + 1;
    }
    out
}

/// A copy of a flag vector (one per worker task).
fn copy_bools(v: &Vec<bool>) -> (r: Vec<bool>)
    ensures r@ == v@,
{
    let mut r: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < v.len()
        invariant i <= v.len(), r@ == v@.subrange(0, i as int),
        decreases v.len() - i,
    {
        r.push(v[i]);
        proof {
            assert(v@.subrange(0, i + 1) =~= v@.subrange(0, i as int).push(v@[i as int]));
        }
        i = i + 1;
    }
    proof {
        assert(v@.subrange(0, v@.len() as int) =~= v@);
    }
    r
}

/// Part keys are dense: the stored rows are sorted by key (kind 1) from 1 to `n`; with the primary key this makes
/// every key its position plus one.
fn dense_check(p: &PaCols, Ghost(cp): Ghost<Seq<PartView>>) -> (b: bool)
    requires pa_cols_ok(*p, cp),
    ensures b ==> dense(cp),
{
    if p.kind != 1 {
        return false;
    }
    if p.n == 0 {
        return true;
    }
    if p.bsize == 0 {
        return false;
    }
    let last = p.n - 1;
    proof {
        lemma_part_row_vals(*p, cp, 0);
        lemma_part_row_vals(*p, cp, last as int);
    }
    let b0 = (0u64 / p.bsize) as usize;
    let bl = (last as u64 / p.bsize) as usize;
    let k0 = p.pk_base[b0] as i128 + p.pk[0] as i128;
    let kl = p.pk_base[bl] as i128 + p.pk[last] as i128;
    if k0 != 1 || kl != p.n as i128 {
        return false;
    }
    proof {
        lemma_dense(cp);
    }
    true
}

/// Sorted distinct integer keys from 1 to `n` are `1..n`.
proof fn lemma_dense(cp: Seq<PartView>)
    requires
        pa_shape(cp),
        crate::stores::custpart::interface::common::colfmt::u64s(cp[pp(crate::stores::custpart::interface::PA_KEYIDX_KIND)])[0] == 1,
        n_pa(cp) > 0,
        pkey_at(cp, 0) == 1,
        pkey_at(cp, n_pa(cp) - 1) == n_pa(cp),
    ensures dense(cp),
{
    hide(pa_shape);
    let n = n_pa(cp);
    assert forall|j: int| 0 <= j < n implies #[trigger] pkey_at(cp, j) == j + 1 by {
        lemma_keys_from_start(cp, j);
        lemma_keys_to_end(cp, j);
    }
}

/// Sorted distinct keys increase strictly.
proof fn lemma_key_step(cp: Seq<PartView>, j: int)
    requires
        pa_shape(cp),
        crate::stores::custpart::interface::common::colfmt::u64s(cp[pp(crate::stores::custpart::interface::PA_KEYIDX_KIND)])[0] == 1,
        0 <= j < n_pa(cp) - 1,
    ensures pkey_at(cp, j) < pkey_at(cp, j + 1),
{
    assert(pkey_at(cp, j) <= pkey_at(cp, j + 1));
    assert(pkey_at(cp, j) != pkey_at(cp, j + 1));
}

/// From the first key 1, key `j` is at least `j + 1`.
proof fn lemma_keys_from_start(cp: Seq<PartView>, j: int)
    requires
        pa_shape(cp),
        crate::stores::custpart::interface::common::colfmt::u64s(cp[pp(crate::stores::custpart::interface::PA_KEYIDX_KIND)])[0] == 1,
        0 <= j < n_pa(cp),
        pkey_at(cp, 0) == 1,
    ensures pkey_at(cp, j) >= j + 1,
    decreases j,
{
    hide(pa_shape);
    if j > 0 {
        lemma_keys_from_start(cp, j - 1);
        lemma_key_step(cp, j - 1);
    }
}

/// Up to the last key `n`, key `j` is at most `j + 1`.
proof fn lemma_keys_to_end(cp: Seq<PartView>, j: int)
    requires
        pa_shape(cp),
        crate::stores::custpart::interface::common::colfmt::u64s(cp[pp(crate::stores::custpart::interface::PA_KEYIDX_KIND)])[0] == 1,
        0 <= j < n_pa(cp),
        pkey_at(cp, n_pa(cp) - 1) == n_pa(cp),
    ensures pkey_at(cp, j) <= j + 1,
    decreases n_pa(cp) - j,
{
    hide(pa_shape);
    if j < n_pa(cp) - 1 {
        lemma_keys_to_end(cp, j + 1);
        lemma_key_step(cp, j);
    }
}

// ------------------------------------------------------------------------------------------------ the parallel scan

/// One worker's share: the lineitem groups `g_lo .. g_hi`.
pub struct ScanTask {
    pub li: LiCols,
    pub pa: PaCols,
    pub bits: Arc<Vec<Vec<u64>>>,
    pub s: u64,
    pub rbuf: Vec<u64>,
    pub vbuf: Vec<i64>,
    pub g_lo: usize,
    pub g_hi: usize,
    pub w: Win,
    pub fp: Ghost<Seq<PartView>>,
    pub cp: Ghost<Seq<PartView>>,
}

impl WorkerTask for ScanTask {
    type Output = Option<Acc>;

    open spec fn pre(&self) -> bool {
        &&& li_cols_ok(self.li, self.fp@)
        &&& look_ok(self.pa, self.cp@)
        &&& bits_ok((*self.bits)@, self.s as int, self.cp@)
        &&& self.rbuf@.len() == CHUNK
        &&& self.vbuf@.len() == CHUNK
        &&& self.g_lo <= self.g_hi <= self.li.ng
    }

    open spec fn post(&self, out: Option<Acc>) -> bool {
        out matches Some(a) ==> acc_ok(a, self.fp@, self.cp@, self.w, self.li.gs@[self.g_lo as int] as int, self.li.gs@[self.g_hi as int] as int)
            && acc_small(a, self.li.gs@[self.g_hi as int] - self.li.gs@[self.g_lo as int])
    }

    fn declared_rows(&self) -> (u64, u64) {
        (self.g_lo as u64, self.g_hi as u64)
    }

    fn run(self) -> (out: Option<Acc>) {
        let mut rbuf = self.rbuf;
        let mut vbuf = self.vbuf;
        let bits: &Vec<Vec<u64>> = &*self.bits;
        scan_range(&self.li, &self.pa, bits, self.s, &mut rbuf, &mut vbuf, self.g_lo, self.g_hi, self.w, self.fp, self.cp)
    }
}

/// Estimated scan cost of lineitem group `g`: 0 when its zone map skips it, else 64 for the window test of its
/// rows plus up to 384 for the part lookups, in proportion to the share of its shipdate range `[base, zmax]` inside
/// the window.
fn group_cost(c: &LiCols, g: usize, w: Win) -> (x: u64)
    requires g < c.ng, c.ship_base@.len() == c.ng, c.ship_zmax@.len() == c.ng,
    ensures x <= 448,
{
    let b = c.ship_base[g] as i128;
    let z = c.ship_zmax[g] as i128;
    let lo = w.lo as i128;
    let hi = w.hi as i128;
    if b >= hi || z < lo || z < b {
        return 0;
    }
    let a = if b > lo { b } else { lo };
    let e = if z < hi - 1 { z } else { hi - 1 };
    let span = z - b + 1;
    let inside = if e >= a { e - a + 1 } else { 0 };
    proof {
        assert(0 <= inside <= span);
        assert(0 <= 384 * (inside as int) / (span as int) <= 384) by (nonlinear_arith) requires 0 <= inside <= span, span >= 1;
    }
    64 + (384 * inside / span) as u64
}

/// The tasks `k` of a partition `bnds` of the groups (task `k` covers groups `bnds[k] .. bnds[k + 1]`).
pub open spec fn tasks_ok(tasks: Seq<ScanTask>, bnds: Seq<int>, c: LiCols, p: PaCols, w: Win, fp: Seq<PartView>, cp: Seq<PartView>) -> bool {
    &&& bnds.len() == tasks.len() + 1
    &&& bnds[0] == 0
    &&& forall|k: int| 0 <= k < tasks.len() ==> {
        &&& (#[trigger] tasks[k]).g_lo == bnds[k]
        &&& tasks[k].g_hi == bnds[k + 1]
        &&& tasks[k].li == c
        &&& tasks[k].pa == p
        &&& tasks[k].w == w
        &&& tasks[k].fp@ == fp
        &&& tasks[k].cp@ == cp
        &&& tasks[k].pre()
    }
}

/// `ntasks` contiguous group ranges with about equal numbers of candidate groups, covering every group.
fn make_tasks(c: &LiCols, p: &PaCols, bits: &Arc<Vec<Vec<u64>>>, s: u64, w: Win, ntasks: usize,
    Ghost(fp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>) -> (r: (Vec<ScanTask>, Ghost<Seq<int>>))
    requires
        li_cols_ok(*c, fp),
        look_ok(*p, cp),
        bits_ok((**bits)@, s as int, cp),
        1 <= ntasks <= MAX_WORKERS,
    ensures
        r.0@.len() == ntasks,
        tasks_ok(r.0@, r.1@, *c, *p, w, fp, cp),
        r.1@[ntasks as int] == c.ng,
{
    let mut total: u64 = 0;
    let mut g: usize = 0;
    while g < c.ng
        invariant li_cols_ok(*c, fp), g <= c.ng,
        decreases c.ng - g,
    {
        let x = group_cost(c, g, w);
        total = if total <= u64::MAX - x { total + x } else { total };
        g = g + 1;
    }
    let mut tasks: Vec<ScanTask> = Vec::new();
    let ghost mut bnds: Seq<int> = seq![0int];
    let mut a: usize = 0;
    let mut done: u64 = 0;
    let mut t: usize = 0;
    while t < ntasks
        invariant
            li_cols_ok(*c, fp),
            look_ok(*p, cp),
            bits_ok((**bits)@, s as int, cp),
            1 <= ntasks <= MAX_WORKERS,
            t <= ntasks,
            a <= c.ng,
            t < ntasks || a == c.ng,
            tasks@.len() == t,
            bnds[t as int] == a,
            tasks_ok(tasks@, bnds, *c, *p, w, fp, cp),
        decreases ntasks - t,
    {
        proof {
            assert((t + 1) * total <= 64 * 0xffff_ffff_ffff_ffff) by (nonlinear_arith)
                requires t + 1 <= 64, total <= 0xffff_ffff_ffff_ffff;
        }
        let goal: u128 = (t as u128 + 1) * total as u128 / ntasks as u128;
        let mut e: usize = a;
        while e < c.ng && (done as u128) < goal
            invariant li_cols_ok(*c, fp), a <= e <= c.ng,
            decreases c.ng - e,
        {
            let x = group_cost(c, e, w);
            done = if done <= u64::MAX - x { done + x } else { done };
            e = e + 1;
        }
        let e = if t + 1 == ntasks { c.ng } else { e };
        let task = ScanTask { li: *c, pa: *p, bits: bits.clone(), s, rbuf: vec![0u64; CHUNK], vbuf: vec![0i64; CHUNK], g_lo: a, g_hi: e, w, fp: Ghost(fp), cp: Ghost(cp) };
        let ghost old_tasks = tasks@;
        tasks.push(task);
        proof {
            bnds = bnds.push(e as int);
            assert forall|k: int| 0 <= k < tasks@.len() implies {
                &&& (#[trigger] tasks@[k]).g_lo == bnds[k]
                &&& tasks@[k].g_hi == bnds[k + 1]
                &&& tasks@[k].li == *c
                &&& tasks@[k].pa == *p
                &&& tasks@[k].w == w
                &&& tasks@[k].fp@ == fp
                &&& tasks@[k].cp@ == cp
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

/// Adds the task outputs in range order: the accumulators of every stored lineitem row, or `None` when a task met a
/// group outside the fast condition.
fn merge(outs: &Vec<Option<Acc>>, Ghost(tv): Ghost<Seq<ScanTask>>, Ghost(bnds): Ghost<Seq<int>>, c: &LiCols, p: &PaCols,
    w: Win, Ghost(fp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>) -> (r: Option<Acc>)
    requires
        li_cols_ok(*c, fp),
        tasks_ok(tv, bnds, *c, *p, w, fp, cp),
        bnds[tv.len() as int] == c.ng,
        outs@.len() == tv.len(),
        forall|k: int| 0 <= k < tv.len() ==> (#[trigger] tv[k]).post(outs@[k]),
    ensures
        r matches Some(a) ==> acc_ok(a, fp, cp, w, 0, n_li(fp)) && acc_small(a, n_li(fp)),
{
    let ghost (lo, hi) = (w.lo as int, w.hi as int);
    let ghost gs = li_gs(fp);
    let ghost n = n_li(fp);
    proof {
        lemma_groups_bounds(gs, n, 0);
        lemma_tot_empty(fp, cp, 0, lo, hi, 0);
        lemma_tot_empty(fp, cp, 1, lo, hi, 0);
        lemma_tot_empty(fp, cp, 2, lo, hi, 0);
        lemma_tot_empty(fp, cp, 3, lo, hi, 0);
        lemma_tot_empty(fp, cp, 4, lo, hi, 0);
    }
    let mut acc = Acc { cnt: 0, pcnt: 0, psum: 0, sum: 0, mass: 0 };
    let mut i: usize = 0;
    while i < outs.len()
        invariant
            li_cols_ok(*c, fp),
            tasks_ok(tv, bnds, *c, *p, w, fp, cp),
            bnds[tv.len() as int] == c.ng,
            outs@.len() == tv.len(),
            forall|k: int| 0 <= k < tv.len() ==> (#[trigger] tv[k]).post(outs@[k]),
            i <= tv.len(),
            lo == w.lo, hi == w.hi, gs == li_gs(fp), n == n_li(fp),
            0 <= bnds[i as int] <= c.ng,
            acc_ok(acc, fp, cp, w, 0, gs[bnds[i as int]] as int),
            acc_small(acc, gs[bnds[i as int]] as int),
        decreases outs.len() - i,
    {
        let ghost lo_g = bnds[i as int];
        let ghost hi_g = bnds[i + 1];
        proof {
            assert(tv[i as int].pre());
            assert(tv[i as int].post(outs@[i as int]));
            crate::stores::facts::interface::common::colfmt::lemma_groups_bounds(gs, n, lo_g);
            crate::stores::facts::interface::common::colfmt::lemma_groups_bounds(gs, n, hi_g);
        }
        let o = outs[i];
        let ga = match o {
            Some(x) => x,
            None => return None,
        };
        let ghost (r1, r2) = (gs[lo_g] as int, gs[hi_g] as int);
        proof {
            lemma_tot_split(fp, cp, 0, lo, hi, 0, r1, r2);
            lemma_tot_split(fp, cp, 1, lo, hi, 0, r1, r2);
            lemma_tot_split(fp, cp, 2, lo, hi, 0, r1, r2);
            lemma_tot_split(fp, cp, 3, lo, hi, 0, r1, r2);
            lemma_tot_split(fp, cp, 4, lo, hi, 0, r1, r2);
            assert(r1 * v_max() + (r2 - r1) * v_max() == r2 * v_max()) by (nonlinear_arith);
            assert(r2 * v_max() <= range_mass_max()) by (nonlinear_arith)
                requires 0 <= r2 <= 0x1_0000_0000_0000_0000;
        }
        acc = Acc {
            cnt: acc.cnt + ga.cnt,
            pcnt: acc.pcnt + ga.pcnt,
            psum: acc.psum + ga.psum,
            sum: acc.sum + ga.sum,
            mass: acc.mass + ga.mass,
        };
        i = i + 1;
    }
    proof {
        assert(gs[c.ng as int] == n);
    }
    Some(acc)
}

/// The totals of the scan: the parallel fast path when the part keys are dense, else (or when a group is outside
/// the fast condition) the general path.
fn scan_all(c: &LiCols, p: &PaCols, promo: &Vec<bool>, w: Win, workers: usize, dispatch: &mut Dispatch,
    Ghost(fp): Ghost<Seq<PartView>>, Ghost(cp): Ghost<Seq<PartView>>) -> (r: Result<Option<Tot>, QueryError>)
    requires
        li_cols_ok(*c, fp),
        pa_cols_ok(*p, cp),
        promo_ok(promo@, cp),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(Some(t)) ==> tot_ok(t, fp, cp, w),
        r matches Ok(None) ==> tot(fp, cp, 4, w.lo as int, w.hi as int, 0, n_li(fp)) > i128::MAX,
        r matches Err(e) ==> e is WorkerFailed,
{
    if p.bsize == 65536 && dense_check(p, Ghost(cp)) {
        let (bits, s) = match build_bitmap(p, promo, workers, dispatch, Ghost(cp)) {
            Ok(b) => b,
            Err(e) => return Err(e),
        };
        let ntasks = if workers < c.ng { workers } else if c.ng >= 1 { c.ng } else { 1 };
        let fast = if ntasks <= 1 {
            proof {
                lemma_groups_bounds(li_gs(fp), n_li(fp), 0);
            }
            let mut rbuf = vec![0u64; CHUNK];
            let mut vbuf = vec![0i64; CHUNK];
            scan_range(c, p, &bits, s, &mut rbuf, &mut vbuf, 0, c.ng, w, Ghost(fp), Ghost(cp))
        } else {
            let shared = Arc::new(bits);
            let (tasks, Ghost(bnds)) = make_tasks(c, p, &shared, s, w, ntasks, Ghost(fp), Ghost(cp));
            let ghost tv = tasks@;
            let outs = match fork_join(dispatch, tasks) {
                Ok(o) => o,
                Err(e) => return Err(QueryError::WorkerFailed(e)),
            };
            merge(&outs, Ghost(tv), Ghost(bnds), c, p, w, Ghost(fp), Ghost(cp))
        };
        if let Some(a) = fast {
            proof {
                lemma_groups_bounds(li_gs(fp), n_li(fp), 0);
                assert(c.gs@[c.ng as int] == n_li(fp));
                assert(n_li(fp) * v_max() <= range_mass_max()) by (nonlinear_arith)
                    requires 0 <= n_li(fp) <= 0x1_0000_0000_0000_0000;
            }
            return Ok(Some(Tot { psum: a.psum, sum: a.sum, any: a.cnt > 0, pany: a.pcnt > 0 }));
        }
    }
    Ok(scan_general(c, p, promo, w, Ghost(fp), Ghost(cp)))
}

// ------------------------------------------------------------------------------------------------ the answer

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

/// `100.00 * s0 / s1` on the aggregate row of the totals.
fn out_value(t: Tot) -> (r: Outcome<EVal>)
    ensures
        match r {
            Ok(res) => fits_out(agg_row_of(t)) && view_result(res) == eval_out(agg_row_of(t)),
            Err(_) => !fits_out(agg_row_of(t)),
        },
{
    let (a0, a1) = if !t.any {
        (EVal::Null, EVal::Null)
    } else {
        (EVal::Num { coeff: t.psum, scale: if t.pany { 4 } else { 0 } }, EVal::Num { coeff: t.sum, scale: 4 })
    };
    let ghost row = agg_row_of(t);
    proof {
        assert(row.len() == 2 && row[0] == a0@ && row[1] == a1@);
        outexpr::lemma_out_eval(row);
    }
    let hundred = EVal::Num { coeff: 10000, scale: 2 };
    proof {
        assert(hundred@ == outexpr::hundred());
    }
    let m = match arith_exec(ArithOp::Mul, NumKind::Numeric, &hundred, &a0) {
        Err(c) => return Err(c),
        Ok(Err(e)) => return Ok(Err(e)),
        Ok(Ok(v)) => v,
    };
    let mut args: Vec<EVal> = Vec::new();
    args.push(m);
    args.push(a1);
    proof {
        assert(crate::exec::value::view_row(args@) =~= seq![m@, a1@]);
        assert(m@ is Num || m@ is Null);
        assert(crate::exec::domain::row_ts_ok(crate::exec::value::view_row(args@)));
    }
    exec_div(ScalarFn::DivNumeric, &args)
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
    let ghost fp = stores@.facts;
    let ghost cp = stores@.custpart;
    proof {
        let db = choose|db: Database| #[trigger] bound_db(sv, db);
        lemma_db_link(sv, db);
    }
    let c = read_li(&mut stores.facts, Ghost(fp));
    let p = read_pa(&mut stores.custpart, Ghost(cp));
    if c.n == 0 || p.n == 0 {
        let rows = one_row(EVal::Null);
        proof {
            assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
                lemma_outcome_empty(sv, db, ps);
            }
        }
        return Ok(Answer::Rows(rows));
    }
    let w = match bounds(params) {
        Ok(w) => w,
        Err(e) => {
            proof {
                assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::SqlError(e))) by {
                    lemma_outcome_hi_err(sv, db, ps, e);
                }
            }
            return Ok(Answer::SqlError(e));
        },
    };
    let promo = promo_table(&p, Ghost(cp));
    let t = match scan_all(&c, &p, &promo, w, workers, dispatch, Ghost(fp), Ghost(cp)) {
        Err(e) => return Err(e),
        Ok(None) => {
            proof {
                assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
                    lemma_outcome_mass(sv, db, ps, w);
                }
            }
            return Ok(Answer::Capacity);
        },
        Ok(Some(t)) => t,
    };
    let out = out_value(t);
    proof {
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies true by {
            lemma_outcome_out(sv, db, ps, w, t);
        }
    }
    match out {
        Err(_) => {
            proof {
                assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Capacity)) by {
                    lemma_outcome_out(sv, db, ps, w, t);
                }
            }
            Ok(Answer::Capacity)
        },
        Ok(Err(e)) => {
            proof {
                assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::SqlError(e))) by {
                    lemma_outcome_out(sv, db, ps, w, t);
                }
            }
            Ok(Answer::SqlError(e))
        },
        Ok(Ok(v)) => {
            let rows = one_row(v);
            proof {
                assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::Rows(rows))) by {
                    lemma_outcome_out(sv, db, ps, w, t);
                }
            }
            Ok(Answer::Rows(rows))
        },
    }
}

} // verus!
