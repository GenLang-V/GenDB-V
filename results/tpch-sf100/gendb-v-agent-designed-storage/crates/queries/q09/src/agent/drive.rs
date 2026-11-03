//! Running the kernels on the calling thread: the part filter bits (`bits`), the small tables (`prep`), the compact
//! partsupp tables (`ptable`), the directory shuffle of the matching rows by destination chunk (`shuffle`), one scan
//! task per range of whole chunks of lineitem rows (`scan`; a task that stopped early for want of a year slot is
//! resumed on the calling thread), the merge of the tasks' cells into the group entries in row order (`groups`), and the sorted result rows
//! (`output`). A LIKE error is the statement's error (`errs`), an absolute amount mass beyond `i128` is Capacity
//! (`capacity`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::query::{query_spec_at, param_domain};
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::work::filled;
use crate::gendb_entry::{Answer, outcome_ok};
use crate::gendb_params::Params;
use crate::exec::value::ERow;
use crate::exec::relational::order::sort_rows_exec;
use crate::link::query::view_rows;
use crate::link::expr::i128_max;
use super::model::*;
use super::qspec::*;
use super::cols::*;
use super::cells::*;
use super::lookups::*;
use super::common::grp::*;
use super::scan::*;
use super::groups::*;
use super::answer::{bound_ok, no_like_err, kabs};
use super::errs::{lemma_q9_err, ies};
use super::capacity::lemma_q9_capacity;
use super::output::*;
use super::year::{year_of, year_exec};
use super::shuffle::{his_ok, lo_of, shuffle_rows, ShufOut, PA, res_ok, CH};

verus! {

/// What every scan task shares: the columns, the filter bits and the lookup tables, and the year capacity.
pub struct Env {
    pub c: Cols,
    pub d: Divs,
    pub bits: Arc<Vec<u64>>,
    pub wpre: Arc<Vec<u32>>,
    pub ents: Arc<Vec<super::build::BuildOut>>,
    pub k0s: Arc<Vec<u64>>,
    pub edv: Div,
    pub ntab: Arc<Vec<u64>>,
    pub gyear: Arc<Vec<i64>>,
    pub ofast: bool,
    pub fast_ps: bool,
    pub n_small: bool,
    pub p_dense: bool,
    pub s_dense: bool,
    pub ycap: usize,
    pub use_bm: bool,
    pub res: Arc<Vec<ShufOut>>,
}

/// The payload context of the environment's tables.
pub open spec fn pa_env(e: Env) -> PA {
    PA { bits: (*e.bits)@, wpre: (*e.wpre)@, k0s: (*e.k0s)@, per: e.edv.bs as int }
}

pub open spec fn env_ok(e: Env, m: M, p: QP) -> bool {
    &&& look_ok(e.c, e.d, m)
    &&& m.p_n > 0
    &&& bits_ok((*e.bits)@, m, p)
    &&& e.fast_ps ==> ents_ok((*e.bits)@, (*e.wpre)@, (*e.ents)@, (*e.k0s)@, e.edv.bs as int, m) && div_ok(e.edv, e.edv.bs as int)
    &&& ntab_ok((*e.ntab)@, e.n_small, m)
    &&& e.ofast ==> m.cluster == 1 && ofacts_ok(m) && gyear_ok((*e.gyear)@, m)
    &&& e.p_dense ==> p_dense_ok(m)
    &&& e.s_dense ==> s_dense_ok(m)
    &&& e.ycap >= 1 && e.ycap * m.n_n <= usize::MAX
    &&& e.use_bm ==> res_ok((*e.res)@, m, p, pa_env(e)) && m.l_n + CH <= usize::MAX
}

/// The shared parts of scan task `t`.
pub open spec fn task_env(t: ScanTask, e: Env, m: M, p: QP) -> bool {
    &&& t.cols == e.c && t.divs == e.d && t.bits == e.bits && t.wpre == e.wpre && t.ents == e.ents && t.ntab == e.ntab
    &&& t.k0s == e.k0s && t.edv == e.edv && t.res == e.res
    &&& t.gyear == e.gyear && t.ofast == e.ofast
    &&& t.fast_ps == e.fast_ps && t.n_small == e.n_small && t.p_dense == e.p_dense && t.s_dense == e.s_dense
    &&& t.nn == m.n_n && t.ycap == e.ycap && t.m@ == m && t.p@ == p
}

/// The order year of every orders group whose date zone `[base, zone maximum]` (at most 1000 days) lies in one year
/// (`NO_YEAR` otherwise), checked day by day.
pub fn order_years(c: &Cols, d: &Divs, Ghost(m): Ghost<M>) -> (gy: Vec<i64>)
    requires look_ok(*c, *d, m), ofacts_ok(m),
    ensures gyear_ok(gy@, m),
{
    let nb = c.o_date_b.len();
    let mut gy: Vec<i64> = Vec::new();
    let mut g: usize = 0;
    while g < nb
        invariant
            look_ok(*c, *d, m), ofacts_ok(m), nb == m.o_nb,
            g <= nb, gy@.len() == g,
            forall|h: int| 0 <= h < g && #[trigger] gy@[h] != NO_YEAR ==> forall|x: int|
                m.o_date_b[h] <= x <= m.o_date_z[h] ==> year_of(x) == gy@[h],
        decreases nb - g,
    {
        let lo = c.o_date_b[g];
        let hi = c.o_date_z[g];
        let mut y: i64 = NO_YEAR;
        if lo <= hi && (hi as i128) - (lo as i128) <= 1000 && crate::exec::datetime::date_valid_exec(lo)
            && crate::exec::datetime::date_valid_exec(hi) {
            let y0 = year_exec(lo);
            let mut dd = lo;
            let mut ok = true;
            while dd < hi && ok
                invariant
                    lo <= dd <= hi,
                    crate::spec::datetime::date_valid(lo as int), crate::spec::datetime::date_valid(hi as int),
                    y0 as int == year_of(lo as int),
                    ok ==> forall|x: int| lo <= x <= dd ==> year_of(x) == y0,
                decreases hi - dd + if ok { 1int } else { 0int },
            {
                dd = dd + 1;
                if year_exec(dd) != y0 {
                    ok = false;
                }
            }
            if ok && dd == hi && y0 != NO_YEAR {
                y = y0;
            }
        }
        let ghost g0 = gy@;
        gy.push(y);
        proof {
            assert forall|h: int| 0 <= h < g + 1 && #[trigger] gy@[h] != NO_YEAR implies forall|x: int|
                m.o_date_b[h] <= x <= m.o_date_z[h] ==> year_of(x) == gy@[h] by {
                if h < g { assert(gy@[h] == g0[h]); }
            }
        }
        g = g + 1;
    }
    proof {
        assert forall|q: int| 0 <= q < m.o_n && #[trigger] gy@[q / m.o_bs] != NO_YEAR implies year_of(odate(m, q)) == gy@[q / m.o_bs] by {
            lemma_block(q, m.o_bs, m.o_n, m.o_nb);
            let h = q / m.o_bs;
            assert(m.o_date_b[h] <= odate(m, q));
            assert(odate(m, q) <= m.o_date_z[h]);
        }
    }
    gy
}

/// A scan task over the lineitem rows `[lo, hi)` (with `bmode`: through the destination chunks of the shuffle).
fn make_task(e: &Env, lo: usize, hi: usize, bmode: bool, plcap: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (t: ScanTask)
    requires
        env_ok(*e, m, p), lo <= hi <= m.l_n,
        bmode ==> e.use_bm && lo as int % CH as int == 0 && (hi == m.l_n || hi as int % CH as int == 0),
    ensures scan_pre(t), task_env(t, *e, m, p), t.j_lo == lo && t.j_hi == hi,
{
    let (bm, wp, pl) = if bmode {
        (vec![0u64; CHW + 1], vec![0u32; CHW + 2], vec![0u32; plcap])
    } else {
        (Vec::new(), Vec::new(), Vec::new())
    };
    let nn = e.c.n_n;
    let ycap = e.ycap;
    let zero = Cell { cnt: 0, sum: 0, ab: 0 };
    let t = ScanTask {
        cols: e.c, divs: e.d, bits: e.bits.clone(), wpre: e.wpre.clone(), ents: e.ents.clone(), k0s: e.k0s.clone(), edv: e.edv, ntab: e.ntab.clone(),
        gyear: e.gyear.clone(), ofast: e.ofast,
        fast_ps: e.fast_ps, n_small: e.n_small, p_dense: e.p_dense, s_dense: e.s_dense, j_lo: lo, j_hi: hi, nn, ycap,
        cells: filled(ycap * nn, zero), years: filled(ycap, 0i64),
        qj: filled(BLOCK + 1, 0usize), qc: filled(BLOCK + 1, 0i64), qn: filled(BLOCK + 1, 0u64),
        qs: filled(BLOCK + 1, 0i64), qr: filled(BLOCK + 1, 0u64), qa: filled(BLOCK + 1, 0i128),
        use_bm: bmode, res: e.res.clone(), bm, wp, pl,
        m: Ghost(m), p: Ghost(p),
    };
    proof {
        assert(t.cells@ =~= Seq::new((ycap * nn) as nat, |i: int| zero_cell()));
        assert(pa_task(t) == pa_env(*e));
    }
    t
}

/// Consecutive scan tasks over the lineitem rows `[0, l_n)`.
pub open spec fn stasks_ok(ts: Seq<ScanTask>, his: Seq<usize>, m: M) -> bool {
    &&& his.len() == ts.len()
    &&& forall|t: int| 0 <= t < ts.len() ==> #[trigger] his[t] == ts[t].j_hi && ts[t].j_lo <= ts[t].j_hi <= m.l_n
    &&& forall|t: int| 0 <= t < ts.len() - 1 ==> #[trigger] his[t] == ts[t + 1].j_lo
    &&& ts.len() > 0 ==> ts[0].j_lo == 0 && his[ts.len() - 1] == m.l_n
    &&& ts.len() == 0 ==> m.l_n == 0
}

/// Payload slots per scan task: twice the average matching rows per destination chunk and 8192 more, at most `CH`
/// (a chunk with more matching rows reads its rows' parts from lineitem instead).
fn pay_cap(res: &Vec<ShufOut>, n: usize) -> (cap: usize)
{
    let mut total: u64 = 0;
    let mut s: usize = 0;
    while s < res.len()
        invariant total <= 0x100_0000_0000u64,
        decreases res.len() - s,
    {
        let o = &res[s];
        let e: u64 = if o.st.len() > 0 { o.st[o.st.len() - 1] as u64 } else { 0 };
        total = if e > 0x100_0000_0000u64 - total { 0x100_0000_0000u64 } else { total + e };
        s = s + 1;
    }
    let avg = total / ((n / CH) as u64 + 1);
    if avg < 0x10_0000 && avg * 2 + 8192 < CH as u64 { (avg * 2 + 8192) as usize } else { CH }
}

/// Every task end is a chunk boundary or the last row.
pub open spec fn his_chunks(his: Seq<usize>, n: int) -> bool {
    forall|t: int| 0 <= t < his.len() ==> (#[trigger] his[t] as int % CH as int == 0 || his[t] == n)
}

/// At most `workers` consecutive scan task ends over the lineitem rows `[0, n)`, in whole destination chunks of `CH`
/// rows.
fn scan_bounds(n: usize, workers: usize) -> (his: Vec<usize>)
    requires 1 <= workers <= MAX_WORKERS,
    ensures his_ok(his@, n as int), his.len() <= workers, his_chunks(his@, n as int),
{
    let q = n / workers / CH;
    let per = if q < 0x1000 { (q + 1) * CH } else { 0x1000 * CH };
    proof {
        assert(per as int % CH as int == 0) by (nonlinear_arith) requires per == (q + 1) * 262144 || per == 0x1000 * 262144;
    }
    let mut his: Vec<usize> = Vec::new();
    let mut lo: usize = 0;
    let mut done = false;
    while !done
        invariant
            1 <= workers <= MAX_WORKERS, per >= 1, per as int % CH as int == 0,
            lo <= n, his.len() <= workers,
            !done ==> his.len() < workers,
            done ==> his.len() >= 1 && lo == n,
            his.len() >= 1 ==> his@[his.len() - 1] == lo,
            his.len() == 0 ==> lo == 0,
            lo as int % CH as int == 0 || lo == n,
            forall|t: int| 0 <= t < his.len() ==> #[trigger] his@[t] <= lo && lo_of(his@, t) <= his@[t],
            forall|t: int| 0 <= t < his.len() ==> (#[trigger] his@[t] as int % CH as int == 0 || his@[t] == n),
        decreases (if done { 0int } else { 1int }) + n - lo + workers - his.len(),
    {
        let last = his.len() + 1 == workers || n - lo <= per;
        let hi = if last { n } else { lo + per };
        proof {
            if !last {
                assert(lo as int % CH as int == 0);
                assert(hi as int % CH as int == 0) by (nonlinear_arith)
                    requires hi == lo + per, lo as int % 262144 == 0, per as int % 262144 == 0;
            }
        }
        let ghost h0 = his@;
        his.push(hi);
        proof {
            assert forall|t: int| 0 <= t < his.len() implies #[trigger] his@[t] <= hi && lo_of(his@, t) <= his@[t] by {
                if t < h0.len() {
                    assert(his@[t] == h0[t]);
                    if t > 0 { assert(his@[t - 1] == h0[t - 1]); }
                } else if t > 0 {
                    assert(his@[t - 1] == lo);
                }
            }
            assert forall|t: int| 0 <= t < his.len() implies (#[trigger] his@[t] as int % CH as int == 0 || his@[t] == n) by {
                if t < h0.len() { assert(his@[t] == h0[t]); }
            }
        }
        lo = hi;
        if last {
            done = true;
        }
    }
    his
}

/// The scan tasks of the task ends `his` (with `bmode`: through the destination chunks).
fn scan_tasks(e: &Env, his: &Vec<usize>, bmode: bool, plcap: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (tasks: Vec<ScanTask>)
    requires
        env_ok(*e, m, p),
        his_ok(his@, m.l_n), his_chunks(his@, m.l_n),
        bmode ==> e.use_bm,
    ensures
        tasks.len() == his.len(),
        stasks_ok(tasks@, his@, m),
        forall|t: int| 0 <= t < tasks.len() ==> scan_pre(#[trigger] tasks@[t]) && task_env(tasks@[t], *e, m, p),
{
    let nt = his.len();
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut t: usize = 0;
    while t < nt
        invariant
            env_ok(*e, m, p), his_ok(his@, m.l_n), his_chunks(his@, m.l_n), nt == his.len(),
            bmode ==> e.use_bm,
            t <= nt, tasks.len() == t,
            forall|u: int| 0 <= u < t ==> scan_pre(#[trigger] tasks@[u]) && task_env(tasks@[u], *e, m, p)
                && tasks@[u].j_lo == lo_of(his@, u) && tasks@[u].j_hi == his@[u],
        decreases nt - t,
    {
        let lo = if t == 0 { 0 } else { his[t - 1] };
        let hi = his[t];
        proof {
            assert(lo_of(his@, t as int) <= his@[t as int] <= m.l_n);
            if t > 0 {
                assert(his@[t - 1] as int % CH as int == 0 || his@[t - 1] == m.l_n);
                if his@[t - 1] == m.l_n {
                    assert(his@[t as int] == m.l_n);
                }
            }
            assert(hi as int % CH as int == 0 || hi == m.l_n);
        }
        let bm_t = bmode && lo % CH == 0;
        let tk = make_task(e, lo, hi, bm_t, plcap, Ghost(m), Ghost(p));
        let ghost t0 = tasks@;
        tasks.push(tk);
        proof {
            assert forall|u: int| 0 <= u < t + 1 implies scan_pre(#[trigger] tasks@[u]) && task_env(tasks@[u], *e, m, p)
                && tasks@[u].j_lo == lo_of(his@, u) && tasks@[u].j_hi == his@[u] by {
                if u < t { assert(tasks@[u] == t0[u]); }
            }
        }
        t = t + 1;
    }
    proof {
        assert forall|u: int| 0 <= u < tasks.len() - 1 implies #[trigger] his@[u] == tasks@[u + 1].j_lo by {
            assert(tasks@[u + 1].j_lo == lo_of(his@, u + 1));
        }
        assert forall|u: int| 0 <= u < tasks.len() implies #[trigger] his@[u] == tasks@[u].j_hi && tasks@[u].j_lo <= tasks@[u].j_hi <= m.l_n by {
            assert(lo_of(his@, u) <= his@[u] <= m.l_n);
        }
    }
    tasks
}

/// A task's output over the rows `[lo, hi)` (`scan_post` without the task).
pub open spec fn out_ok(m: M, p: QP, out: ScanOut, nn: int, ycap: int, lo: int, hi: int) -> bool {
    &&& lo <= out.stop <= hi
    &&& out.years@.len() == ycap
    &&& out.cells@.len() == ycap * nn
    &&& out.ny <= ycap
    &&& !out.aovf ==> cells_inv(m, p, out.cells@, out.years@, out.ny as int, ycap, nn, lo, out.stop as int)
    &&& !out.aovf && out.stop < hi ==> out.stop > lo
    &&& out.aovf ==> {
        &&& out.stop < hi
        &&& out.ovf_k < out.ny && out.ovf_n < nn
        &&& dsum(abs_f(m, p, out.ovf_n as int, out.years@[out.ovf_k as int] as int), lo, out.stop + 1) > i128_max()
    }
}

proof fn lemma_out_ok(t: ScanTask, out: ScanOut)
    requires scan_post(t, out),
    ensures out_ok(t.m@, t.p@, out, t.nn as int, t.ycap as int, t.j_lo as int, t.j_hi as int),
{
}

/// The overflow of a task's cell: a group whose absolute mass is beyond `i128::MAX`.
fn overflow_group(out: &ScanOut, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>, Ghost(nn): Ghost<int>, Ghost(ycap): Ghost<int>,
    Ghost(lo): Ghost<int>, Ghost(hi): Ghost<int>) -> (r: (usize, i64))
    requires model_ok(m), out_ok(m, p, *out, nn, ycap, lo, hi), out.aovf, nn == m.n_n, 0 <= lo, hi <= m.l_n,
    ensures r.0 < m.n_n && kabs(m, p, gkey(nname(m, r.0 as int), r.1 as int)) > i128_max(),
{
    let n = out.ovf_n;
    let y = out.years[out.ovf_k];
    proof { lemma_cell_ovf(m, p, n as int, y as int, lo, out.stop + 1); }
    (n, y)
}

/// Merge a task's output over `[pos, hi)`, resuming the task on the calling thread while it stopped early: `None`
/// when every group is merged through `[0, hi)`, else a group (nation row, year) whose absolute mass is beyond
/// `i128::MAX`.
fn finish_range(es: &mut Vec<Ent>, first: &ScanOut, nrep: &Vec<u64>, e: &Env, pos: usize, hi: usize, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>)
    -> (r: Option<(usize, i64)>)
    requires
        env_ok(*e, m, p),
        nrep_ok(m, nrep@), ents_wf(m, nrep@, old(es)@),
        keys_on(m, p, old(es)@, pos as int),
        pos <= hi <= m.l_n,
        out_ok(m, p, *first, m.n_n, e.ycap as int, pos as int, hi as int),
    ensures
        ents_wf(m, nrep@, final(es)@),
        r is None ==> keys_on(m, p, final(es)@, hi as int),
        r matches Some((n, y)) ==> n < m.n_n && kabs(m, p, gkey(nname(m, n as int), y as int)) > i128_max(),
{
    let nn = e.c.n_n;
    if first.aovf {
        return Some(overflow_group(first, Ghost(m), Ghost(p), Ghost(m.n_n), Ghost(e.ycap as int), Ghost(pos as int), Ghost(hi as int)));
    }
    match merge_out(es, first, nrep, nn, Ghost(m), Ghost(p), Ghost(pos as int), Ghost(e.ycap as int)) {
        Some(w) => { return Some(w); },
        None => {},
    }
    let mut at = first.stop;
    while at < hi
        invariant
            env_ok(*e, m, p), nn == m.n_n,
            nrep_ok(m, nrep@), ents_wf(m, nrep@, es@),
            keys_on(m, p, es@, at as int),
            at <= hi <= m.l_n,
        decreases hi - at,
    {
        let t = make_task(e, at, hi, false, 0, Ghost(m), Ghost(p));
        let ghost tv = t;
        let out = t.run();
        proof { lemma_out_ok(tv, out); }
        if out.aovf {
            return Some(overflow_group(&out, Ghost(m), Ghost(p), Ghost(m.n_n), Ghost(e.ycap as int), Ghost(at as int), Ghost(hi as int)));
        }
        match merge_out(es, &out, nrep, nn, Ghost(m), Ghost(p), Ghost(at as int), Ghost(e.ycap as int)) {
            Some(w) => { return Some(w); },
            None => {},
        }
        at = out.stop;
    }
    None
}

/// Before any row: every group is zero.
proof fn lemma_keys_start(m: M, p: QP)
    ensures keys_on(m, p, Seq::<Ent>::empty(), 0),
{
    assert forall|name: Seq<u8>, y: int| #[trigger] key_is(m, p, Seq::<Ent>::empty(), name, y, 0, m.n_n, 0) by {
        assert(!has_key(m, Seq::<Ent>::empty(), name, y));
        lemma_dsum_empty(gc_f(m, p, name, y, m.n_n), 0);
        lemma_dsum_empty(gs_f(m, p, name, y, m.n_n), 0);
        lemma_dsum_empty(ga_f(m, p, name, y, m.n_n), 0);
    }
}

/// Without part rows no lineitem row joins: every group is zero through every row.
proof fn lemma_keys_no_parts(m: M, p: QP)
    requires m.p_n == 0, m.l_n >= 0,
    ensures keys_on(m, p, Seq::<Ent>::empty(), m.l_n),
{
    assert forall|name: Seq<u8>, y: int| #[trigger] key_is(m, p, Seq::<Ent>::empty(), name, y, m.l_n, m.n_n, m.l_n) by {
        assert(!has_key(m, Seq::<Ent>::empty(), name, y));
        assert forall|j: int| 0 <= j < m.l_n implies #[trigger] gc_f(m, p, name, y, m.n_n)(j) == 0 by {}
        assert forall|j: int| 0 <= j < m.l_n implies #[trigger] gs_f(m, p, name, y, m.n_n)(j) == 0 by {}
        assert forall|j: int| 0 <= j < m.l_n implies #[trigger] ga_f(m, p, name, y, m.n_n)(j) == 0 by {}
        lemma_dsum_zero(gc_f(m, p, name, y, m.n_n), 0, m.l_n);
        lemma_dsum_zero(gs_f(m, p, name, y, m.n_n), 0, m.l_n);
        lemma_dsum_zero(ga_f(m, p, name, y, m.n_n), 0, m.l_n);
        lemma_dsum_empty(gc_f(m, p, name, y, m.n_n), m.l_n);
        lemma_dsum_empty(gs_f(m, p, name, y, m.n_n), m.l_n);
        lemma_dsum_empty(ga_f(m, p, name, y, m.n_n), m.l_n);
    }
}

/// The groups merged, the sorted rows of the entries.
fn answer_rows(c: &Cols, es: &Vec<Ent>, Ghost(m): Ghost<M>, Ghost(nrep): Ghost<Seq<u64>>, Ghost(ps): Ghost<Seq<Literal>>)
    -> (r: Result<Answer, QueryError>)
    requires
        cols_ok(*c, m), model_ok(m), nrep_ok(m, nrep), ents_wf(m, nrep, es@),
        keys_on(m, qp_of(ps), es@, m.l_n),
        param_domain(ps),
    ensures forall|db: Database| #[trigger] bound_ok(db, m, ps) && no_like_err(m, qp_of(ps)) ==> outcome_ok(db, query_spec_at(ps), r),
{
    let rows = build_rows(c, es, Ghost(m), Ghost(nrep));
    let keys = order_keys();
    let sorted = sort_rows_exec(&keys, rows);
    proof {
        assert forall|db: Database| #[trigger] bound_ok(db, m, ps) && no_like_err(m, qp_of(ps)) implies
            crate::spec::order::ordered_ok(db, query_spec_at(ps), Ok::<Relation, SqlError>(view_rows(sorted@))) by {
            lemma_final(db, m, ps, nrep, es@, view_rows(rows@), view_rows(sorted@));
        }
    }
    Ok(Answer::Rows(sorted))
}

/// The shared parts of the scan tasks: the filter bits, the compact partsupp tables, the directory shuffle of the
/// matching rows by destination chunk (the fast layout), the order years of the orders groups.
fn make_env(c: Cols, d: Divs, bits: Vec<u64>, ntab: Vec<u64>, n_small: bool, p_dense: bool, s_dense: bool, ycap: usize,
    workers: usize, dispatch: &mut Dispatch, Ghost(m): Ghost<M>, Ghost(p): Ghost<QP>) -> (r: Result<Env, QueryError>)
    requires
        look_ok(c, d, m), model_ok(m), ofacts_ok(m), pdir_ok(m), m.p_n > 0,
        bits_ok(bits@, m, p),
        ntab_ok(ntab@, n_small, m),
        p_dense ==> p_dense_ok(m),
        s_dense ==> s_dense_ok(m),
        ycap >= 1 && ycap * m.n_n <= usize::MAX,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(env) ==> env_ok(env, m, p) && env.c == c,
        r matches Err(e) ==> e is WorkerFailed,
{
    let bits = Arc::new(bits);
    let ntab = Arc::new(ntab);
    // the compact partsupp table of the matching parts
    let (wpre, ents, k0s, per, fast_ps) = match super::ptable::part_table(c, d, &bits, &ntab, n_small, s_dense, p_dense, workers, dispatch, Ghost(m)) {
        Err(e) => {
            return Err(e);
        },
        Ok(Some((w, e, k, per))) => (w, e, k, per, true),
        Ok(None) => (Vec::new(), Vec::new(), Vec::new(), 1usize, false),
    };
    let edv = div_of(per as u64);
    let wpre = Arc::new(wpre);
    let k0s = Arc::new(k0s);
    // the matching rows by destination chunk, with their payloads (the fast layout)
    let shuf = if fast_ps && c.l_n <= 0xf000_0000 {
        match shuffle_rows(c, d, &bits, &wpre, &k0s, edv, p_dense, workers, dispatch, Ghost(m), Ghost(p)) {
            Err(e) => {
                return Err(e);
            },
            Ok(x) => x,
        }
    } else {
        None
    };
    let (use_bm, res) = match shuf {
        Some(rs) => (true, rs),
        None => (false, Arc::new(Vec::new())),
    };
    let gyear = order_years(&c, &d, Ghost(m));
    let ofast = c.cluster == 1;
    let env = Env { c, d, bits, wpre, ents: Arc::new(ents), k0s, edv, ntab, gyear: Arc::new(gyear), ofast,
        fast_ps, n_small, p_dense, s_dense, ycap, use_bm, res };
    proof {
        assert(look_ok(env.c, env.d, m));
        assert(bits_ok((*env.bits)@, m, p));
        assert(env.fast_ps ==> ents_ok((*env.bits)@, (*env.wpre)@, (*env.ents)@, (*env.k0s)@, env.edv.bs as int, m));
        assert(ntab_ok((*env.ntab)@, env.n_small, m));
        assert(env.ycap >= 1 && env.ycap * m.n_n <= usize::MAX);
        assert(env.use_bm ==> res_ok((*env.res)@, m, p, pa_env(env)));
        assert(env_ok(env, m, p));
    }
    Ok(env)
}

/// The whole query after reading the columns.
pub fn run(c: Cols, params: &Params, workers: usize, dispatch: &mut Dispatch, Ghost(m): Ghost<M>) -> (r: Result<Answer, QueryError>)
    requires cols_ok(c, m), model_ok(m), ofacts_ok(m), pdir_ok(m), psig_ok(c.p_sig@, m), param_domain(params@), 1 <= workers <= MAX_WORKERS,
    ensures forall|db: Database| #[trigger] bound_ok(db, m, params@) ==> outcome_ok(db, query_spec_at(params@), r),
{
    let ghost ps = params@;
    let ghost p = qp_of(ps);
    let pat: &'static [u8] = params.p0;
    proof {
        assert(p.pat == pat@);
        assert(frame_ok(m.l_n, m.l_bs, m.l_nb) && frame_ok(m.o_n, m.o_bs, m.o_nb) && frame_ok(m.p_n, m.p_bs, m.p_nb));
        assert(frame_ok(m.t_n, m.t_bs, m.t_nb) && frame_ok(m.s_n, m.s_bs, m.s_nb) && frame_ok(m.n_n, m.n_bs, m.n_nb));
    }
    let d = Divs { l: div_of(c.l_bs), o: div_of(c.o_bs), p: div_of(c.p_bs), t: div_of(c.t_bs), s: div_of(c.s_bs), n: div_of(c.n_bs) };
    proof { assert(look_ok(c, d, m)); }
    // the part filter bits
    let mut p_dense = false;
    let mut fast: Option<Vec<u64>> = None;
    if super::bits::is_word_shape(pat) {
        match super::bits::word_bits(c, d, pat, workers, dispatch, Ghost(m), Ghost(p)) {
            Err(e) => {
                return Err(e);
            },
            Ok(Some((b, dn))) => {
                fast = Some(b);
                p_dense = dn;
            },
            Ok(None) => {},
        }
    }
    let mut err: Option<usize> = None;
    let bits = match fast {
        Some(b) => b,
        None => {
            let (b, e) = super::bits::like_bits(&c, pat, Ghost(m), Ghost(p));
            err = e;
            b
        },
    };
    proof {
        assert(bits_ok(bits@, m, p));
        assert(err is None ==> like_total(m, p));
    }
    match err {
        Some(x) => {
            if c.s_n > 0 && c.l_n > 0 && c.t_n > 0 && c.o_n > 0 && c.n_n > 0 {
                let r = Ok(Answer::SqlError(crate::spec::value::SqlError::InvalidEscapeSequence));
                proof {
                    assert forall|db: Database| #[trigger] bound_ok(db, m, ps) implies outcome_ok(db, query_spec_at(ps), r) by {
                        lemma_q9_err(db, m, ps, x as int);
                    }
                }
                return r;
            }
        },
        None => {},
    }
    proof { assert(no_like_err(m, p)); }
    // the small tables
    let nrep = super::prep::first_names(&c, Ghost(m));
    if c.p_n == 0 {
        let es: Vec<Ent> = Vec::new();
        proof { lemma_keys_no_parts(m, p); assert(es@ =~= Seq::<Ent>::empty()); }
        return answer_rows(&c, &es, Ghost(m), Ghost(nrep@), Ghost(ps));
    }
    let (ntab, n_small) = super::prep::nation_table(&c, &d, Ghost(m));
    let s_dense = super::prep::supp_dense(&c, &d, Ghost(m));
    let nn = c.n_n;
    let ycap = if nn <= usize::MAX / YEARS { YEARS } else { 1 };
    proof {
        if nn <= usize::MAX / YEARS {
            assert(YEARS * nn <= usize::MAX) by (nonlinear_arith) requires nn <= usize::MAX / 8, YEARS == 8;
            assert(ycap * m.n_n <= usize::MAX);
        } else {
            assert(ycap == 1);
            assert(ycap * m.n_n == m.n_n);
        }
    }
    let env = match make_env(c, d, bits, ntab, n_small, p_dense, s_dense, ycap, workers, dispatch, Ghost(m), Ghost(p)) {
        Err(e) => {
            return Err(e);
        },
        Ok(e) => e,
    };
    // the scan tasks: their row ranges (whole chunks), their tasks
    let his = scan_bounds(env.c.l_n, workers);
    let plcap = pay_cap(&env.res, env.c.l_n);
    let tasks = scan_tasks(&env, &his, env.use_bm, plcap, Ghost(m), Ghost(p));
    let ghost ts = tasks@;
    proof {
        assert forall|t: int| 0 <= t < tasks.len() implies #[trigger] tasks@[t].pre() by {}
    }
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => {
            return Err(QueryError::WorkerFailed(e));
        },
    };
    // the merge, in row order
    let mut es: Vec<Ent> = Vec::new();
    proof { lemma_keys_start(m, p); assert(es@ =~= Seq::<Ent>::empty()); }
    let mut t: usize = 0;
    while t < outs.len()
        invariant
            env_ok(env, m, p), env.c == c,
            no_like_err(m, p), param_domain(ps), ps == params@, p == qp_of(ps),
            nrep_ok(m, nrep@), ents_wf(m, nrep@, es@),
            outs.len() == ts.len(),
            stasks_ok(ts, his@, m),
            forall|x: int| 0 <= x < ts.len() ==> (#[trigger] ts[x]).post(outs@[x])
                && task_env(ts[x], env, m, p),
            t <= ts.len(),
            keys_on(m, p, es@, if t == 0 { 0 } else { his@[t - 1] as int }),
        decreases ts.len() - t,
    {
        let lo = if t == 0 { 0 } else { his[t - 1] };
        let hi = his[t];
        proof {
            let tk = ts[t as int];
            assert(tk.post(outs@[t as int]));
            assert(task_env(tk, env, m, p));
            if t > 0 { assert(his@[t - 1] == ts[t as int].j_lo); }
            assert(hi == tk.j_hi);
            lemma_out_ok(tk, outs@[t as int]);
            assert(tk.j_lo == lo);
        }
        match finish_range(&mut es, &outs[t], &nrep, &env, lo, hi, Ghost(m), Ghost(p)) {
            Some((n, y)) => {
                let r = Ok(Answer::Capacity);
                proof {
                    assert forall|db: Database| #[trigger] bound_ok(db, m, ps) implies outcome_ok(db, query_spec_at(ps), r) by {
                        lemma_q9_capacity(db, m, ps, gkey(nname(m, n as int), y as int));
                    }
                }
                return r;
            },
            None => {},
        }
        t = t + 1;
    }
    proof {
        if ts.len() > 0 { assert(his@[ts.len() - 1] == m.l_n); }
    }
    let r = answer_rows(&c, &es, Ghost(m), Ghost(nrep@), Ghost(ps));
    r
}

} // verus!
