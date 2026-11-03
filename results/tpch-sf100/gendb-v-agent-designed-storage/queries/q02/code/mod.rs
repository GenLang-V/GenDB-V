//! TPC-H Q2 (minimum cost supplier) over the storages `custpart` (part), `suppliers` (partsupp, supplier, nation,
//! region), `part_sztyidx` (a (p_size, p_type) index of part), `suppliers_psrun` (partsupp's ps_partkey run layout)
//! and `suppliers_rank` (supplier rows by descending s_acctbal, and a ps_suppkey directory of partsupp).
//!
//! Plan: open the column handles (`tables`); evaluate `p_type LIKE $2` once per p_type dictionary entry
//! (`prep::like_table`; a failing pattern on some part row is the statement's error); build the nation/region
//! lookups. Then the candidates (selected part, minimal-cost partsupp row in the region, supplier, nation) and a
//! threshold reached by at least 100 candidates' s_acctbal (or by all): first by walking the suppliers from the
//! largest balance down (`walk`, about 2K suppliers and 34K partsupp rows on the benchmark data); past its visit
//! budget, or without the indexes, from the (p_size, p_type) index (`sty`) or a scan of every part group (`scan`),
//! in parallel tasks. Build and sort only the output rows reaching the threshold, and return the first 100.
//!
//! Proof: `q2spec` states the candidates' normal form, `sqlq`/`sqlrel` prove that the statement's body is the bag
//! of the candidates' output rows (`sqlrel::lemma_body_multiset`), and `output::lemma_final` that the sorted cut
//! is an allowed output. `bind` turns every database bound to the parts into the same five tables with their keys.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::ast::Literal;
use crate::spec::order::{ordered_ok, denote_body, slice_rows, sort_rows};
use crate::query::{query_spec_at, param_domain};
use crate::gendb_entry::stores::Stores;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::{Answer, answer_meets, stores_ready, bound_db, outcome_ok};
use crate::gendb_entry::stores::StoresView;
use crate::gendb_params::Params;
use crate::exec::value::*;
use crate::exec::ast::{EOrderKey, view_order_keys};
use crate::exec::relational::order::{sort_rows_exec, slice_rows_exec, view_keys};
use crate::link::query::view_rows;

pub mod tables;
pub mod q2spec;
pub mod scan;
pub mod sqlq;
pub mod common;
pub mod sqlrel;
pub mod bind;
pub mod output;
pub mod prep;
pub mod sty;
pub mod walk;

use tables::*;
use q2spec::*;
use scan::*;
use sqlq::*;
use sqlrel::*;
use bind::*;
use output::*;
use prep::*;
use common::relops::*;
use sty::*;
use crate::stores::part_sztyidx::interface as sxi;
use crate::stores::suppliers_psrun::interface as ppi;
use crate::stores::suppliers_rank::interface as rki;
use walk::{RankIdx, rank_ok, walk};

verus! {

// ------------------------------------------------------------------------------------------------ scan driver

/// First row of group `g` (`scan::row_start`).
fn row_start_exec(c: &Cols, g: usize, Ghost(t): Ghost<Tabs>) -> (r: usize)
    requires cols_ok(*c, t), g <= c.p.ng,
    ensures r as int == row_start(*c, g as int),
{
    if g < c.p.ng {
        proof {
            assert((g as int) * (c.p.bs as int) <= ((c.p.ng - 1) as int) * (c.p.bs as int)) by (nonlinear_arith)
                requires g < c.p.ng, c.p.bs >= 1;
        }
        g * c.p.bs
    } else {
        c.p.n
    }
}

/// Group starts are nondecreasing and end at the row count.
proof fn lemma_row_start(c: Cols, t: Tabs, g1: int, g2: int)
    requires cols_ok(c, t), 0 <= g1 <= g2 <= c.p.ng,
    ensures row_start(c, g1) <= row_start(c, g2), row_start(c, c.p.ng as int) == c.p.n, row_start(c, 0) == 0,
{
    let bs = c.p.bs as int;
    let ng = c.p.ng as int;
    if g2 < ng {
        assert(g1 * bs <= g2 * bs) by (nonlinear_arith) requires g1 <= g2, bs >= 1;
    } else if g1 < ng {
        assert(g1 * bs <= (ng - 1) * bs) by (nonlinear_arith) requires g1 <= ng - 1, bs >= 1;
    }
    if ng == 0 {
        assert(ng * bs == 0) by (nonlinear_arith) requires ng == 0;
    }
}

/// Appends `src[0 .. len]` to `dst`.
fn append_prefix(dst: &mut Vec<Cand>, src: &Vec<Cand>, len: usize)
    requires len <= src@.len(),
    ensures final(dst)@ == old(dst)@ + src@.subrange(0, len as int),
{
    let mut x: usize = 0;
    while x < len
        invariant len <= src@.len(), x <= len, dst@ == old(dst)@ + src@.subrange(0, x as int),
        decreases len - x,
    {
        dst.push(src[x]);
        proof { assert(src@.subrange(0, x + 1) =~= src@.subrange(0, x as int).push(src@[x as int])); }
        x = x + 1;
    }
}

/// Group bounds of `nt` tasks over `ng` groups: nondecreasing from 0 to `ng`. `fork_join` starts the tasks from
/// the last one, so task `k` gets a weight growing with `k` (`2 nt + k`): tasks that start later get fewer groups.
/// Only the bounds' order is relied on.
fn task_bounds(ng: usize, nt: usize) -> (b: Vec<usize>)
    requires 1 <= nt <= MAX_WORKERS,
    ensures
        b@.len() == nt + 1,
        b@[0] == 0,
        b@[nt as int] == ng,
        forall|k: int| 0 <= k < nt ==> #[trigger] b@[k] <= b@[k + 1],
        forall|k: int| 0 <= k <= nt ==> #[trigger] b@[k] <= ng,
{
    let mut tot: u128 = 0;
    let mut j: usize = 0;
    while j < nt
        invariant j <= nt, nt <= MAX_WORKERS, tot <= 192 * j,
        decreases nt - j,
    {
        tot = tot + (2 * nt + j) as u128;
        j = j + 1;
    }
    let mut b: Vec<usize> = Vec::new();
    b.push(0);
    let mut cum: u128 = 0;
    let mut prev: usize = 0;
    let mut k: usize = 0;
    while k < nt
        invariant
            1 <= nt <= MAX_WORKERS, k <= nt, cum <= 192 * k,
            b@.len() == k + 1, b@[0] == 0, b@[k as int] == prev, prev <= ng,
            k == nt ==> prev == ng,
            forall|x: int| 0 <= x < k ==> #[trigger] b@[x] <= b@[x + 1],
            forall|x: int| 0 <= x <= k ==> #[trigger] b@[x] <= ng,
        decreases nt - k,
    {
        cum = cum + (2 * nt + k) as u128;
        let mut h: usize = if k + 1 == nt {
            ng
        } else if tot == 0 {
            prev
        } else {
            proof {
                assert((ng as int) * (cum as int) <= (ng as int) * 12288) by (nonlinear_arith)
                    requires cum <= 12288, ng >= 0;
            }
            let x = (ng as u128) * cum / tot;
            if x > ng as u128 { ng } else { x as usize }
        };
        if h < prev {
            h = prev;
        }
        let ghost before = b@;
        b.push(h);
        proof {
            assert forall|x: int| 0 <= x < k + 1 implies #[trigger] b@[x] <= b@[x + 1] by {
                if x < k { assert(b@[x] == before[x] && b@[x + 1] == before[x + 1]); }
            }
            assert forall|x: int| 0 <= x <= k + 1 implies #[trigger] b@[x] <= ng by {
                if x <= k { assert(b@[x] == before[x]); }
            }
        }
        prev = h;
        k = k + 1;
    }
    b
}

/// All candidates of the part rows on the calling thread.
fn scan_serial(c: &Cols, lk: &Lookups, a: ScanArgs, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>) -> (cs: Vec<Cand>)
    requires scan_env(*c, *lk, a, t, m),
    ensures chunk_ok(t, m, cs@, 0, t.p.len() as int),
{
    let ng = c.p.ng;
    let dummy = Cand { part: 0, ps: 0, supp: 0, nation: 0, acct: 0 };
    let mut cands: Vec<Cand> = Vec::new();
    proof { lemma_row_start(*c, t, 0, ng as int); }
    let share = c.p.n / 320;
    let cap = if share < 1000000000 { share + 512 } else { share };
    let mut st = ScanState { buf: CandBuf { v: vec![dummy; cap], len: 0 }, pend: vec![0usize; 128], sink: 0 };
    let next = scan_groups(c, lk, a, 0, ng, &mut st, Ghost(t), Ghost(m));
    append_prefix(&mut cands, &st.buf.v, st.buf.len);
    proof { assert(cands@ =~= buf_view(st.buf)); }
    let ghost before = cands@;
    scan_rows_serial(c, lk, a, next, c.p.n, &mut cands, Ghost(t), Ghost(m));
    proof {
        let seg = choose|seg: Seq<Cand>| cands@ == before + seg && chunk_ok(t, m, seg, next as int, c.p.n as int);
        lemma_chunk_append(t, m, before, seg, 0, next as int, c.p.n as int);
    }
    cands
}

/// The bounds `bnd` of `nt` tasks: nondecreasing from 0 to the group count.
pub open spec fn bounds_ok(bnd: Seq<usize>, nt: int, ng: int) -> bool {
    &&& bnd.len() == nt + 1
    &&& bnd[0] == 0
    &&& bnd[nt] == ng
    &&& forall|x: int| 0 <= x < nt ==> #[trigger] bnd[x] <= bnd[x + 1]
    &&& forall|x: int| 0 <= x <= nt ==> #[trigger] bnd[x] <= ng
}

/// One task per bound pair.
fn build_tasks(c: &Cols, lk: &Lookups, a: ScanArgs, bnd: &Vec<usize>, nt: usize, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>)
    -> (tasks: Vec<ScanTask>)
    requires scan_env(*c, *lk, a, t, m), 1 <= nt <= MAX_WORKERS, bounds_ok(bnd@, nt as int, c.p.ng as int),
    ensures
        tasks@.len() == nt,
        forall|i: int| 0 <= i < nt ==> (#[trigger] tasks@[i]).pre(),
        forall|i: int| 0 <= i < nt ==> (#[trigger] tasks@[i]).c == *c && tasks@[i].t@ == t && tasks@[i].m@ == m,
        forall|i: int| 0 <= i < nt ==> (#[trigger] tasks@[i]).g_lo == bnd@[i] && tasks@[i].g_hi == bnd@[i + 1],
{
    let dummy = Cand { part: 0, ps: 0, supp: 0, nation: 0, acct: 0 };
    let share = c.p.n / (nt * 320);
    let cap = if share < 1000000000 { share + 512 } else { share };
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut k: usize = 0;
    while k < nt
        invariant
            scan_env(*c, *lk, a, t, m), 1 <= nt <= MAX_WORKERS, bounds_ok(bnd@, nt as int, c.p.ng as int),
            k <= nt, tasks@.len() == k,
            forall|i: int| 0 <= i < k ==> (#[trigger] tasks@[i]).pre(),
            forall|i: int| 0 <= i < k ==> (#[trigger] tasks@[i]).c == *c && tasks@[i].t@ == t && tasks@[i].m@ == m,
            forall|i: int| 0 <= i < k ==> (#[trigger] tasks@[i]).g_lo == bnd@[i] && tasks@[i].g_hi == bnd@[i + 1],
        decreases nt - k,
    {
        let g_lo = bnd[k];
        let g_hi = bnd[k + 1];
        assert(bnd@[k as int] <= bnd@[k + 1] && bnd@[k + 1] <= c.p.ng);
        let lk2 = copy_lookups(lk);
        let st = ScanState { buf: CandBuf { v: vec![dummy; cap], len: 0 }, pend: vec![0usize; 128], sink: 0 };
        let task = ScanTask { c: *c, lk: lk2, a, g_lo, g_hi, st, t: Ghost(t), m: Ghost(m) };
        assert(task.pre());
        tasks.push(task);
        k = k + 1;
    }
    tasks
}

/// Merges the task outputs in task order: each task's buffer, then the serial rest of its rows.
fn merge_outs(c: &Cols, lk: &Lookups, a: ScanArgs, bnd: &Vec<usize>, outs: &Vec<(ScanState, usize)>,
    Ghost(tk): Ghost<Seq<ScanTask>>, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>) -> (cs: Vec<Cand>)
    requires
        scan_env(*c, *lk, a, t, m),
        tk.len() == outs@.len(), 1 <= tk.len() <= MAX_WORKERS,
        bounds_ok(bnd@, tk.len() as int, c.p.ng as int),
        forall|j: int| 0 <= j < tk.len() ==> (#[trigger] tk[j]).post(outs@[j]),
        forall|j: int| 0 <= j < tk.len() ==> (#[trigger] tk[j]).c == *c && tk[j].t@ == t && tk[j].m@ == m,
        forall|j: int| 0 <= j < tk.len() ==> (#[trigger] tk[j]).g_lo == bnd@[j] && tk[j].g_hi == bnd@[j + 1],
    ensures chunk_ok(t, m, cs@, 0, t.p.len() as int),
{
    let ng = c.p.ng;
    let nt = outs.len();
    let mut cands: Vec<Cand> = Vec::new();
    proof {
        lemma_row_start(*c, t, 0, ng as int);
        lemma_chunk_empty(t, m, 0);
        assert(cands@ =~= Seq::<Cand>::empty());
    }
    let mut i: usize = 0;
    while i < nt
        invariant
            scan_env(*c, *lk, a, t, m), ng == c.p.ng, nt == tk.len(), nt == outs@.len(),
            bounds_ok(bnd@, nt as int, ng as int),
            i <= nt,
            forall|j: int| 0 <= j < nt ==> (#[trigger] tk[j]).post(outs@[j]),
            forall|j: int| 0 <= j < nt ==> (#[trigger] tk[j]).c == *c && tk[j].t@ == t && tk[j].m@ == m,
            forall|j: int| 0 <= j < nt ==> (#[trigger] tk[j]).g_lo == bnd@[j] && tk[j].g_hi == bnd@[j + 1],
            chunk_ok(t, m, cands@, 0, row_start(*c, bnd@[i as int] as int)),
        decreases nt - i,
    {
        proof { assert(tk[i as int].post(outs@[i as int])); }
        let g_lo = bnd[i];
        let g_hi = bnd[i + 1];
        let st = &outs[i].0;
        let next = outs[i].1;
        let ghost before = cands@;
        append_prefix(&mut cands, &st.buf.v, st.buf.len);
        let ghost mid = cands@;
        assert(g_hi <= ng);
        let end = row_start_exec(c, g_hi, Ghost(t));
        proof {
            assert(g_hi == tk[i as int].g_hi);
            assert(g_lo == tk[i as int].g_lo);
            assert(next == outs@[i as int].1);
            assert(st.buf == outs@[i as int].0.buf);
            lemma_row_start(*c, t, g_hi as int, ng as int);
            assert(mid =~= before + buf_view(st.buf));
            lemma_chunk_append(t, m, before, buf_view(st.buf), 0, row_start(*c, g_lo as int), next as int);
        }
        scan_rows_serial(c, lk, a, next, end, &mut cands, Ghost(t), Ghost(m));
        proof {
            let seg = choose|seg: Seq<Cand>| cands@ == mid + seg && chunk_ok(t, m, seg, next as int, end as int);
            lemma_chunk_append(t, m, mid, seg, 0, next as int, end as int);
        }
        i = i + 1;
    }
    cands
}

/// All candidates of the part rows, scanned by up to `workers` tasks.
fn scan_all(c: &Cols, lk: &Lookups, a: ScanArgs, workers: usize, dispatch: &mut Dispatch, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>)
    -> (r: Result<Vec<Cand>, QueryError>)
    requires scan_env(*c, *lk, a, t, m), 1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(cs) ==> chunk_ok(t, m, cs@, 0, t.p.len() as int),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ng = c.p.ng;
    // At most 32 tasks: threads are spawned one after another (about 35 us each on the measured host), and with
    // 64 tasks the later spawns cost more than their share of the scan saves (measured 6.1-7.0 ms vs 5.4 ms).
    let w: usize = if workers < 32 { workers } else { 32 };
    let nt: usize = if w < ng { w } else { ng };
    if nt <= 1 {
        return Ok(scan_serial(c, lk, a, Ghost(t), Ghost(m)));
    }
    let bnd = task_bounds(ng, nt);
    let tasks = build_tasks(c, lk, a, &bnd, nt, Ghost(t), Ghost(m));
    let ghost tk = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(f) => {
            return Err(QueryError::WorkerFailed(f));
        },
    };
    Ok(merge_outs(c, lk, a, &bnd, &outs, Ghost(tk), Ghost(t), Ghost(m)))
}


// ------------------------------------------------------------------------------------------------ index driver

/// The composite (p_size, p_type) index of storage `part_sztyidx` when it is a dense directory (`None`: the
/// fallback mode).
fn open_styidx(stores: &mut Stores, Ghost(xr): Ghost<Seq<Seq<Row>>>, Ghost(p): Ghost<Seq<Row>>) -> (r: Option<StyIdx>)
    requires
        sxi::represents(old(stores)@.part_sztyidx, xr),
        xr[0].len() == p.len(),
        forall|i: int| 0 <= i < p.len() ==> #[trigger] xr[0][i][0] == p[i][4] && xr[0][i][1] == p[i][5],
    ensures
        final(stores)@ == old(stores)@,
        r matches Some(x) ==> styx_ok(x, p),
{
    let ghost parts = stores.part_sztyidx@;
    let meta = stores.part_sztyidx.extent_i64(sxi::META, 0, 2);
    proof { assert(meta@ =~= sxi::idx_i64s(parts[sxi::META as int])); }
    if meta[0] == sxi::MODE_DIRECTORY {
        let lo = stores.part_sztyidx.part_len(sxi::OFFS);
        let offs = stores.part_sztyidx.extent_u32(sxi::OFFS, 0, lo);
        let lp = stores.part_sztyidx.part_len(sxi::PERM);
        let perm = stores.part_sztyidx.extent_u32(sxi::PERM, 0, lp);
        let lt = stores.part_sztyidx.part_len(sxi::TOFFS);
        proof {
            assert(offs@ =~= sxi::idx_u32s(parts[sxi::OFFS as int]));
            assert(perm@ =~= sxi::idx_u32s(parts[sxi::PERM as int]));
        }
        let x = StyIdx {
            kmin: meta[1], nt: lt - 1, nk: lo - 1, np: lp, offs, perm,
            toffs: Ghost(sxi::idx_u64s(parts[sxi::TOFFS as int])), tbytes: Ghost(sxi::idx_u8s(parts[sxi::TBYTES as int])),
            rel: Ghost(xr[0]),
        };
        proof {
            reveal(styx_ok);
            let toffs = sxi::idx_u64s(parts[sxi::TOFFS as int]);
            assert(x.offs@.len() == x.nk + 1);
            assert(x.perm@.len() == x.np);
            assert(x.nt as int == x.toffs@.len() - 1);
            assert(x.kmin == sxi::idx_i64s(parts[sxi::META as int])[1]);
            assert(sxi::directory_ok(x.kmin as int, x.nt as int, x.toffs@, x.tbytes@, x.offs@, x.perm@, x.rel@));
            assert(x.rel@.len() == p.len());
            assert(styx_ok(x, p));
        }
        Some(x)
    } else {
        None
    }
}

/// The handles of storage suppliers_rank's two indexes, when both are present (`ns` supplier rows).
fn open_rank(stores: &mut Stores, ns: usize, Ghost(t): Ghost<Tabs>, Ghost(rels): Ghost<Seq<Seq<Row>>>) -> (r: Option<RankIdx>)
    requires
        rki::represents(old(stores)@.suppliers_rank, rels),
        rels[0] == t.ps, rels[1] == t.s, ns == t.s.len(),
    ensures
        final(stores)@ == old(stores)@,
        r matches Some(x) ==> rank_ok(x, t),
{
    let ghost parts = stores.suppliers_rank@;
    let lb = stores.suppliers_rank.part_len(rki::SBAL);
    if lb == 0 || lb != ns {
        return None;
    }
    let meta = stores.suppliers_rank.extent_i64(rki::PSMETA, 0, 2);
    proof { assert(meta@ =~= rki::i64s_of(parts[rki::PSMETA as int])); }
    if meta[0] != rki::MODE_DIRECTORY {
        return None;
    }
    let sbal = stores.suppliers_rank.extent_u32(rki::SBAL, 0, lb);
    let lo = stores.suppliers_rank.part_len(rki::PSOFFS);
    let offs = stores.suppliers_rank.extent_u32(rki::PSOFFS, 0, lo);
    let lp = stores.suppliers_rank.part_len(rki::PSPERM);
    let perm = stores.suppliers_rank.extent_u32(rki::PSPERM, 0, lp);
    let x = RankIdx { sbal, kmin: meta[1], offs, perm };
    proof {
        assert(sbal@ =~= rki::u32s_of(parts[rki::SBAL as int]));
        assert(offs@ =~= rki::u32s_of(parts[rki::PSOFFS as int]));
        assert(perm@ =~= rki::u32s_of(parts[rki::PSPERM as int]));
        assert(walk::rmeta(x) =~= meta@);
    }
    Some(x)
}

/// Position bounds of `nt` tasks over `[lo, hi)`: nondecreasing from `lo` to `hi`, equal shares.
fn pos_bounds(lo: usize, hi: usize, nt: usize) -> (b: Vec<usize>)
    requires 1 <= nt <= MAX_WORKERS, lo <= hi,
    ensures
        b@.len() == nt + 1,
        b@[0] == lo,
        b@[nt as int] == hi,
        forall|k: int| 0 <= k < nt ==> #[trigger] b@[k] <= b@[k + 1],
        forall|k: int| 0 <= k <= nt ==> lo <= #[trigger] b@[k] <= hi,
{
    let w = hi - lo;
    let mut b: Vec<usize> = Vec::new();
    b.push(lo);
    let mut prev = lo;
    let mut k: usize = 1;
    while k <= nt
        invariant
            1 <= nt <= MAX_WORKERS, lo <= hi, w == hi - lo,
            1 <= k <= nt + 1,
            b@.len() == k, b@[0] == lo, b@[k - 1] == prev, lo <= prev <= hi,
            k == nt + 1 ==> prev == hi,
            forall|x: int| 0 <= x < k - 1 ==> #[trigger] b@[x] <= b@[x + 1],
            forall|x: int| 0 <= x < k ==> lo <= #[trigger] b@[x] <= hi,
        decreases nt + 1 - k,
    {
        let mut h: usize = if k == nt {
            hi
        } else {
            proof {
                assert((w as int) * (k as int) <= (usize::MAX as int) * 64) by (nonlinear_arith)
                    requires 0 <= w <= usize::MAX, 0 <= k <= 64;
            }
            let q = (w as u128) * (k as u128) / (nt as u128);
            if q > w as u128 { hi } else { lo + q as usize }
        };
        if h < prev {
            h = prev;
        }
        let ghost before = b@;
        b.push(h);
        proof {
            assert forall|x: int| 0 <= x < k implies #[trigger] b@[x] <= b@[x + 1] by {
                if x < k - 1 { assert(b@[x] == before[x] && b@[x + 1] == before[x + 1]); }
            }
            assert forall|x: int| 0 <= x < k + 1 implies lo <= #[trigger] b@[x] <= hi by {
                if x < k { assert(b@[x] == before[x]); }
            }
        }
        prev = h;
        k = k + 1;
    }
    b
}

/// Number of selected positions of the entries `e0 .. e1` (for sizing only).
fn selected_count(x: &StyIdx, e0: usize, e1: usize, sel: &Vec<bool>) -> (n: usize)
    requires e0 <= e1 <= x.nk, x.offs@.len() == x.nk + 1, sel@.len() == e1 - e0,
{
    let mut n: usize = 0;
    let mut e = e0;
    while e < e1
        invariant e0 <= e <= e1 <= x.nk, x.offs@.len() == x.nk + 1, sel@.len() == e1 - e0,
        decreases e1 - e,
    {
        let a = x.offs[e] as usize;
        let b = x.offs[e + 1] as usize;
        if sel[e - e0] && a < b && n <= usize::MAX - (b - a) {
            n = n + (b - a);
        }
        e = e + 1;
    }
    n
}

/// Position bounds of `nt` tasks over `[lo, hi)` with about equal numbers of selected positions (`total` in all):
/// nondecreasing from `lo` to `hi`. Only the bounds' order is relied on.
fn sel_bounds(x: &StyIdx, e0: usize, e1: usize, sel: &Vec<bool>, lo: usize, hi: usize, nt: usize, total: usize) -> (b: Vec<usize>)
    requires
        1 <= nt <= MAX_WORKERS, lo <= hi,
        e0 <= e1 <= x.nk, x.offs@.len() == x.nk + 1, sel@.len() == e1 - e0,
    ensures
        b@.len() == nt + 1,
        b@[0] == lo,
        b@[nt as int] == hi,
        forall|k: int| 0 <= k < nt ==> #[trigger] b@[k] <= b@[k + 1],
        forall|k: int| 0 <= k <= nt ==> lo <= #[trigger] b@[k] <= hi,
{
    let mut b: Vec<usize> = Vec::new();
    b.push(lo);
    let mut prev = lo;
    // Walk the entries once: `acc` selected positions lie before entry `e`.
    let mut e = e0;
    let mut acc: usize = 0;
    let mut k: usize = 1;
    while k <= nt
        invariant
            1 <= nt <= MAX_WORKERS, lo <= hi,
            e0 <= e <= e1 <= x.nk, x.offs@.len() == x.nk + 1, sel@.len() == e1 - e0,
            1 <= k <= nt + 1,
            b@.len() == k, b@[0] == lo, b@[k - 1] == prev, lo <= prev <= hi,
            k == nt + 1 ==> prev == hi,
            forall|y: int| 0 <= y < k - 1 ==> #[trigger] b@[y] <= b@[y + 1],
            forall|y: int| 0 <= y < k ==> lo <= #[trigger] b@[y] <= hi,
        decreases nt + 1 - k,
    {
        let mut h: usize = hi;
        if k < nt {
            let target: usize = if total <= usize::MAX / 64 {
                proof {
                    assert((total as int) * (k as int) <= (usize::MAX / 64) * 64) by (nonlinear_arith)
                        requires total <= usize::MAX / 64, k <= 64;
                }
                total * k / nt
            } else {
                total / nt
            };
            // Skip whole entries whose selected positions end at or before the target.
            while e < e1
                invariant e0 <= e <= e1 <= x.nk, x.offs@.len() == x.nk + 1, sel@.len() == e1 - e0,
                decreases e1 - e,
            {
                let a = x.offs[e] as usize;
                let bb = x.offs[e + 1] as usize;
                let len: usize = if sel[e - e0] && a < bb { bb - a } else { 0 };
                if acc <= usize::MAX - len && acc + len <= target {
                    acc = acc + len;
                    e = e + 1;
                } else {
                    break;
                }
            }
            if e < e1 {
                let a = x.offs[e] as usize;
                let d = if target >= acc { target - acc } else { 0 };
                h = if a <= usize::MAX - d { a + d } else { hi };
            }
        }
        if h < prev {
            h = prev;
        }
        if h > hi {
            h = hi;
        }
        if k == nt {
            h = hi;
        }
        let ghost before = b@;
        b.push(h);
        proof {
            assert forall|y: int| 0 <= y < k implies #[trigger] b@[y] <= b@[y + 1] by {
                if y < k - 1 { assert(b@[y] == before[y] && b@[y + 1] == before[y + 1]); }
            }
            assert forall|y: int| 0 <= y < k + 1 implies lo <= #[trigger] b@[y] <= hi by {
                if y < k { assert(b@[y] == before[y]); }
            }
        }
        prev = h;
        k = k + 1;
    }
    b
}

/// A copy of the selection flags (one per worker task).
fn copy_sel(v: &Vec<bool>) -> (r: Vec<bool>)
    ensures r@ == v@,
{
    copy_bools(v)
}

/// One task per position bound pair.
fn build_sty_tasks(c: &Cols, lk: &Lookups, a: ScanArgs, x: &StyIdx, e0: usize, e1: usize, sel: &Vec<bool>,
    bnd: &Vec<usize>, nt: usize, cap: usize, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>) -> (tasks: Vec<StyTask>)
    requires
        sty_env(*c, *lk, a, *x, t, m, e0 as int, e1 as int, sel@),
        1 <= nt <= MAX_WORKERS,
        bnd@.len() == nt + 1, bnd@[0] == x.offs@[e0 as int], bnd@[nt as int] == x.offs@[e1 as int],
        forall|k: int| 0 <= k < nt ==> #[trigger] bnd@[k] <= bnd@[k + 1],
        forall|k: int| 0 <= k <= nt ==> x.offs@[e0 as int] <= #[trigger] bnd@[k] <= x.offs@[e1 as int],
    ensures
        tasks@.len() == nt,
        forall|i: int| 0 <= i < nt ==> (#[trigger] tasks@[i]).pre(),
        forall|i: int| 0 <= i < nt ==> (#[trigger] tasks@[i]).c == *c && tasks@[i].t@ == t && tasks@[i].m@ == m
            && tasks@[i].x == *x,
        forall|i: int| 0 <= i < nt ==> (#[trigger] tasks@[i]).j0 == bnd@[i] && tasks@[i].j1 == bnd@[i + 1],
{
    let dummy = Cand { part: 0, ps: 0, supp: 0, nation: 0, acct: 0 };
    let mut tasks: Vec<StyTask> = Vec::new();
    let mut k: usize = 0;
    while k < nt
        invariant
            sty_env(*c, *lk, a, *x, t, m, e0 as int, e1 as int, sel@),
            1 <= nt <= MAX_WORKERS,
            bnd@.len() == nt + 1, bnd@[0] == x.offs@[e0 as int], bnd@[nt as int] == x.offs@[e1 as int],
            forall|kk: int| 0 <= kk < nt ==> #[trigger] bnd@[kk] <= bnd@[kk + 1],
            forall|kk: int| 0 <= kk <= nt ==> x.offs@[e0 as int] <= #[trigger] bnd@[kk] <= x.offs@[e1 as int],
            k <= nt, tasks@.len() == k,
            forall|i: int| 0 <= i < k ==> (#[trigger] tasks@[i]).pre(),
            forall|i: int| 0 <= i < k ==> (#[trigger] tasks@[i]).c == *c && tasks@[i].t@ == t && tasks@[i].m@ == m
                && tasks@[i].x == *x,
            forall|i: int| 0 <= i < k ==> (#[trigger] tasks@[i]).j0 == bnd@[i] && tasks@[i].j1 == bnd@[i + 1],
        decreases nt - k,
    {
        let j0 = bnd[k];
        let j1 = bnd[k + 1];
        assert(bnd@[k as int] <= bnd@[k + 1]);
        let lk2 = copy_lookups(lk);
        let sel2 = copy_sel(sel);
        let st = ScanState { buf: CandBuf { v: vec![dummy; cap], len: 0 }, pend: vec![0usize; 128], sink: 0 };
        let task = StyTask { c: *c, lk: lk2, a, x: *x, e0, e1, sel: sel2, j0, j1, st, t: Ghost(t), m: Ghost(m) };
        assert(task.pre());
        tasks.push(task);
        k = k + 1;
    }
    tasks
}

/// Merges the task outputs in task order: each task's buffer, then the serial rest of its positions.
fn merge_sty_outs(c: &Cols, lk: &Lookups, a: ScanArgs, x: &StyIdx, lo: usize, hi: usize, bnd: &Vec<usize>,
    outs: &Vec<(ScanState, usize)>, Ghost(tk): Ghost<Seq<StyTask>>, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>)
    -> (cs: Vec<Cand>)
    requires
        scan_env(*c, *lk, a, t, m), styx_ok(*x, t.p), hi <= x.np,
        tk.len() == outs@.len(), 1 <= tk.len() <= MAX_WORKERS,
        bnd@.len() == tk.len() + 1, bnd@[0] == lo, bnd@[tk.len() as int] == hi,
        forall|k: int| 0 <= k < tk.len() ==> #[trigger] bnd@[k] <= bnd@[k + 1],
        forall|k: int| 0 <= k <= tk.len() ==> lo <= #[trigger] bnd@[k] <= hi,
        forall|j: int| 0 <= j < tk.len() ==> (#[trigger] tk[j]).post(outs@[j]),
        forall|j: int| 0 <= j < tk.len() ==> (#[trigger] tk[j]).c == *c && tk[j].t@ == t && tk[j].m@ == m && tk[j].x == *x,
        forall|j: int| 0 <= j < tk.len() ==> (#[trigger] tk[j]).j0 == bnd@[j] && tk[j].j1 == bnd@[j + 1],
    ensures pchunk_ok(t, m, *x, cs@, lo as int, hi as int),
{
    let nt = outs.len();
    let mut total: usize = 0;
    let mut i: usize = 0;
    while i < nt
        invariant nt == outs@.len(), i <= nt,
        decreases nt - i,
    {
        let l = outs[i].0.buf.len;
        if total <= usize::MAX - l { total = total + l; }
        i = i + 1;
    }
    let mut cands: Vec<Cand> = Vec::with_capacity(total);
    proof {
        lemma_pchunk_empty(t, m, *x, lo as int);
        assert(cands@ =~= Seq::<Cand>::empty());
    }
    let mut i: usize = 0;
    while i < nt
        invariant
            scan_env(*c, *lk, a, t, m), styx_ok(*x, t.p), hi <= x.np,
            nt == tk.len(), nt == outs@.len(),
            bnd@.len() == nt + 1, bnd@[0] == lo, bnd@[nt as int] == hi,
            forall|k: int| 0 <= k < nt ==> #[trigger] bnd@[k] <= bnd@[k + 1],
            forall|k: int| 0 <= k <= nt ==> lo <= #[trigger] bnd@[k] <= hi,
            i <= nt,
            forall|j: int| 0 <= j < nt ==> (#[trigger] tk[j]).post(outs@[j]),
            forall|j: int| 0 <= j < nt ==> (#[trigger] tk[j]).c == *c && tk[j].t@ == t && tk[j].m@ == m && tk[j].x == *x,
            forall|j: int| 0 <= j < nt ==> (#[trigger] tk[j]).j0 == bnd@[j] && tk[j].j1 == bnd@[j + 1],
            pchunk_ok(t, m, *x, cands@, lo as int, bnd@[i as int] as int),
        decreases nt - i,
    {
        proof {
            assert(tk[i as int].post(outs@[i as int]));
        }
        let j1 = bnd[i + 1];
        let st = &outs[i].0;
        let next = outs[i].1;
        let ghost before = cands@;
        append_prefix(&mut cands, &st.buf.v, st.buf.len);
        let ghost mid = cands@;
        proof {
            assert(next == outs@[i as int].1);
            assert(st.buf == outs@[i as int].0.buf);
            assert(mid =~= before + buf_view(st.buf));
            lemma_pchunk_append(t, m, *x, before, buf_view(st.buf), lo as int, bnd@[i as int] as int, next as int);
        }
        scan_pos_serial(c, lk, a, x, next, j1, &mut cands, Ghost(t), Ghost(m));
        proof {
            let seg = choose|seg: Seq<Cand>| cands@ == mid + seg && pchunk_ok(t, m, *x, seg, next as int, j1 as int);
            lemma_pchunk_append(t, m, *x, mid, seg, lo as int, next as int, j1 as int);
        }
        i = i + 1;
    }
    cands
}

// ------------------------------------------------------------------------------------------------ the pick

/// The candidates `sel` reaching the threshold `thr`, out of all candidates `all`: at least 100 of them, or all.
pub open spec fn picked_ok(t: Tabs, m: Prm, all: Seq<Cand>, sel: Seq<Cand>, thr: int) -> bool {
    &&& cands_ok(t, m, all)
    &&& sel == select(all, ge_f(thr))
    &&& select(all, ge_f(thr)).len() >= 100 || select(all, lt_f(thr)).len() == 0
}

/// The candidates whose s_acctbal reaches `thr`, in order.
fn select_ge(cands: &Vec<Cand>, thr: i64) -> (r: Vec<Cand>)
    ensures r@ == select(cands@, ge_f(thr as int)),
{
    let nc = cands.len();
    let mut r: Vec<Cand> = Vec::new();
    let mut x: usize = 0;
    while x < nc
        invariant nc == cands@.len(), x <= nc, r@ == select(cands@.subrange(0, x as int), ge_f(thr as int)),
        decreases nc - x,
    {
        proof {
            assert(cands@.subrange(0, x + 1) =~= cands@.subrange(0, x as int).push(cands@[x as int]));
            lemma_select_push(cands@.subrange(0, x as int), cands@[x as int], ge_f(thr as int));
        }
        if cands[x].acct >= thr {
            r.push(cands[x]);
        }
        x = x + 1;
    }
    proof { assert(cands@.subrange(0, nc as int) =~= cands@); }
    r
}

/// The pick from a vector of all candidates: the 100th largest s_acctbal as threshold (or the least `i64`).
fn pick_from_vec(cands: &Vec<Cand>, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>) -> (r: (Vec<Cand>, i64))
    requires cands_ok(t, m, cands@),
    ensures picked_ok(t, m, cands@, r.0@, r.1 as int),
{
    let mut thr = threshold(cands);
    let cnt = count_ge(cands, thr);
    if cnt < 100 && cnt < cands.len() {
        thr = i64::MIN;
    }
    proof {
        lemma_select_split_map(cands@, ge_f(thr as int), lt_f(thr as int), row_f(t, m));
        if thr == i64::MIN {
            lemma_none_below_min(cands@);
        }
    }
    let sel = select_ge(cands, thr);
    (sel, thr)
}

/// The task buffers' candidates `0 .. i`, in task order.
pub open spec fn bufs_cat(outs: Seq<(ScanState, usize)>, i: int) -> Seq<Cand>
    decreases i,
{
    if i <= 0 { Seq::<Cand>::empty() } else { bufs_cat(outs, i - 1) + buf_view(outs[i - 1].0.buf) }
}

/// Completed tasks' buffers concatenate to the chunk of their positions.
proof fn lemma_bufs_chunk(t: Tabs, m: Prm, x: StyIdx, outs: Seq<(ScanState, usize)>, tk: Seq<StyTask>, bnd: Seq<usize>, i: int)
    requires
        0 <= i <= tk.len(), tk.len() == outs.len(), bnd.len() == tk.len() + 1,
        forall|j: int| 0 <= j < tk.len() ==> (#[trigger] tk[j]).post(outs[j]),
        forall|j: int| 0 <= j < tk.len() ==> (#[trigger] tk[j]).t@ == t && tk[j].m@ == m && tk[j].x == x,
        forall|j: int| 0 <= j < tk.len() ==> (#[trigger] tk[j]).j0 == bnd[j] && tk[j].j1 == bnd[j + 1],
        forall|j: int| 0 <= j < tk.len() ==> #[trigger] outs[j].1 == bnd[j + 1],
    ensures pchunk_ok(t, m, x, bufs_cat(outs, i), bnd[0] as int, bnd[i] as int),
    decreases i,
{
    if i == 0 {
        lemma_pchunk_empty(t, m, x, bnd[0] as int);
    } else {
        lemma_bufs_chunk(t, m, x, outs, tk, bnd, i - 1);
        assert(tk[i - 1].post(outs[i - 1]));
        assert(outs[i - 1].1 == bnd[i]);
        lemma_pchunk_append(t, m, x, bufs_cat(outs, i - 1), buf_view(outs[i - 1].0.buf), bnd[0] as int, bnd[i - 1] as int, bnd[i] as int);
    }
}

/// Every task ran to the end of its positions.
fn all_done(outs: &Vec<(ScanState, usize)>, bnd: &Vec<usize>) -> (b: bool)
    requires bnd@.len() == outs@.len() + 1,
    ensures b ==> forall|j: int| 0 <= j < outs@.len() ==> #[trigger] outs@[j].1 == bnd@[j + 1],
{
    let nt = outs.len();
    let mut i: usize = 0;
    while i < nt
        invariant nt == outs@.len(), bnd@.len() == nt + 1, i <= nt,
            forall|j: int| 0 <= j < i ==> #[trigger] outs@[j].1 == bnd@[j + 1],
        decreases nt - i,
    {
        if outs[i].1 != bnd[i + 1] {
            return false;
        }
        i = i + 1;
    }
    true
}

/// A threshold that about 100 of the buffers' candidates reach: the 100th largest s_acctbal (or the least `i64`).
/// Its meaning is checked by the caller; only termination and bounds are proved here.
fn threshold_bufs(outs: &Vec<(ScanState, usize)>) -> (thr: i64)
{
    let nt = outs.len();
    let mut top: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < nt
        invariant nt == outs@.len(), i <= nt, top@.len() <= 100,
        decreases nt - i,
    {
        let b = &outs[i].0.buf;
        let nc = if b.len <= b.v.len() { b.len } else { b.v.len() };
        let mut x: usize = 0;
        while x < nc
            invariant nc <= b.v@.len(), x <= nc, top@.len() <= 100,
            decreases nc - x,
        {
            let v = b.v[x].acct;
            let tl = top.len();
            if tl < 100 || v > top[tl - 1] {
                if tl == 100 {
                    top.pop();
                }
                top.push(v);
                let mut p = top.len() - 1;
                while p > 0 && top[p - 1] < top[p]
                    invariant p < top@.len(), top@.len() <= 100,
                    decreases p,
                {
                    let tmp = top[p - 1];
                    let cur = top[p];
                    top.set(p - 1, cur);
                    top.set(p, tmp);
                    p = p - 1;
                }
            }
            x = x + 1;
        }
        i = i + 1;
    }
    if top.len() == 100 { top[99] } else { i64::MIN }
}

/// The buffers' candidates whose s_acctbal reaches `thr`, in task order.
fn select_bufs(outs: &Vec<(ScanState, usize)>, thr: i64) -> (r: Vec<Cand>)
    requires forall|j: int| 0 <= j < outs@.len() ==> buf_wf(#[trigger] outs@[j].0.buf),
    ensures r@ == select(bufs_cat(outs@, outs@.len() as int), ge_f(thr as int)),
{
    let nt = outs.len();
    let mut r: Vec<Cand> = Vec::new();
    let mut i: usize = 0;
    while i < nt
        invariant
            nt == outs@.len(), i <= nt,
            forall|j: int| 0 <= j < outs@.len() ==> buf_wf(#[trigger] outs@[j].0.buf),
            r@ == select(bufs_cat(outs@, i as int), ge_f(thr as int)),
        decreases nt - i,
    {
        let b = &outs[i].0.buf;
        let nc = b.len;
        let ghost pre = bufs_cat(outs@, i as int);
        proof { assert(buf_wf(outs@[i as int].0.buf)); }
        let mut x: usize = 0;
        while x < nc
            invariant
                nc == b.len, nc <= b.v@.len(), x <= nc,
                r@ == select(pre + b.v@.subrange(0, x as int), ge_f(thr as int)),
            decreases nc - x,
        {
            proof {
                assert(pre + b.v@.subrange(0, x + 1) =~= (pre + b.v@.subrange(0, x as int)).push(b.v@[x as int]));
                lemma_select_push(pre + b.v@.subrange(0, x as int), b.v@[x as int], ge_f(thr as int));
            }
            if b.v[x].acct >= thr {
                r.push(b.v[x]);
            }
            x = x + 1;
        }
        proof {
            assert(pre + b.v@.subrange(0, nc as int) =~= bufs_cat(outs@, i + 1));
        }
        i = i + 1;
    }
    r
}

/// Whether some buffer candidate's s_acctbal is below `thr` (when not, none is).
fn exists_below(outs: &Vec<(ScanState, usize)>, thr: i64) -> (b: bool)
    requires forall|j: int| 0 <= j < outs@.len() ==> buf_wf(#[trigger] outs@[j].0.buf),
    ensures !b ==> select(bufs_cat(outs@, outs@.len() as int), lt_f(thr as int)).len() == 0,
{
    let nt = outs.len();
    let mut i: usize = 0;
    while i < nt
        invariant
            nt == outs@.len(), i <= nt,
            forall|j: int| 0 <= j < outs@.len() ==> buf_wf(#[trigger] outs@[j].0.buf),
            select(bufs_cat(outs@, i as int), lt_f(thr as int)).len() == 0,
        decreases nt - i,
    {
        let b = &outs[i].0.buf;
        let nc = b.len;
        let ghost pre = bufs_cat(outs@, i as int);
        proof { assert(buf_wf(outs@[i as int].0.buf)); }
        let mut x: usize = 0;
        while x < nc
            invariant
                nc == b.len, nc <= b.v@.len(), x <= nc,
                select(pre + b.v@.subrange(0, x as int), lt_f(thr as int)).len() == 0,
            decreases nc - x,
        {
            proof {
                assert(pre + b.v@.subrange(0, x + 1) =~= (pre + b.v@.subrange(0, x as int)).push(b.v@[x as int]));
                lemma_select_push(pre + b.v@.subrange(0, x as int), b.v@[x as int], lt_f(thr as int));
            }
            if b.v[x].acct < thr {
                return true;
            }
            x = x + 1;
        }
        proof {
            assert(pre + b.v@.subrange(0, nc as int) =~= bufs_cat(outs@, i + 1));
        }
        i = i + 1;
    }
    false
}

/// All candidates of the part rows, from the entries of p_size `$1` of the composite index, by up to `workers` tasks.
fn scan_index(c: &Cols, lk: &Lookups, a: ScanArgs, x: &StyIdx, workers: usize,
    dispatch: &mut Dispatch, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>) -> (r: Result<(Vec<Cand>, i64, Ghost<Seq<Cand>>), QueryError>)
    requires scan_env(*c, *lk, a, t, m), styx_ok(*x, t.p), 1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(p) ==> picked_ok(t, m, p.2@, p.0@, p.1 as int),
        r matches Err(e) ==> e is WorkerFailed,
{
    let (e0, e1) = size_range(x, a.size, Ghost(t.p));
    proof {
        lemma_styx_shape(*x, t.p);
        lemma_offs_mono(*x, t.p, e0 as int, e1 as int);
        lemma_offs_mono(*x, t.p, e1 as int, x.nk as int);
    }
    let lo = x.offs[e0] as usize;
    let hi = x.offs[e1] as usize;
    let sel = select_entries(c, lk, x, e0, e1, Ghost(t), Ghost(m));
    let total = selected_count(x, e0, e1, &sel);
    // Tasks of at least about 3000 selected rows, at most 24: thread starts cost ~35 us each.
    let cap_t: usize = if workers < 24 { workers } else { 24 };
    let by_size: usize = total / 3072;
    let nt: usize = if by_size < 1 { 1 } else if by_size < cap_t { by_size } else { cap_t };
    if nt <= 1 {
        let dummy = Cand { part: 0, ps: 0, supp: 0, nation: 0, acct: 0 };
        let cap = total / 4 * 3 + 512;
        let mut st = ScanState { buf: CandBuf { v: vec![dummy; cap], len: 0 }, pend: vec![0usize; 128], sink: 0 };
        let next = scan_sel(c, lk, a, x, e0, e1, &sel, lo, hi, &mut st, Ghost(t), Ghost(m));
        // The candidates are the buffer's prefix (no copy).
        let blen = st.buf.len;
        let mut cands: Vec<Cand> = st.buf.v;
        cands.truncate(blen);
        proof { assert(cands@ =~= buf_view(st.buf)); }
        let ghost before = cands@;
        scan_pos_serial(c, lk, a, x, next, hi, &mut cands, Ghost(t), Ghost(m));
        proof {
            let seg = choose|seg: Seq<Cand>| cands@ == before + seg && pchunk_ok(t, m, *x, seg, next as int, hi as int);
            lemma_pchunk_append(t, m, *x, before, seg, lo as int, next as int, hi as int);
            lemma_pchunk_cands(t, m, *x, cands@, e0 as int, e1 as int);
        }
        let (sel, thr) = pick_from_vec(&cands, Ghost(t), Ghost(m));
        return Ok((sel, thr, Ghost(cands@)));
    }
    let bnd = sel_bounds(x, e0, e1, &sel, lo, hi, nt, total);
    let cap = total / nt / 4 * 3 + 512;
    let tasks = build_sty_tasks(c, lk, a, x, e0, e1, &sel, &bnd, nt, cap, Ghost(t), Ghost(m));
    let ghost tk = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(f) => {
            return Err(QueryError::WorkerFailed(f));
        },
    };
    if all_done(&outs, &bnd) {
        // Every task completed: pick straight from the task buffers (their concatenation is never built).
        let ghost all = bufs_cat(outs@, outs@.len() as int);
        proof {
            lemma_bufs_chunk(t, m, *x, outs@, tk, bnd@, tk.len() as int);
            lemma_pchunk_cands(t, m, *x, all, e0 as int, e1 as int);
            assert forall|j: int| 0 <= j < outs@.len() implies buf_wf(#[trigger] outs@[j].0.buf) by {
                assert(tk[j].post(outs@[j]));
            }
        }
        let mut thr = threshold_bufs(&outs);
        let mut sel = select_bufs(&outs, thr);
        if sel.len() < 100 && exists_below(&outs, thr) {
            thr = i64::MIN;
            sel = select_bufs(&outs, thr);
            proof { lemma_none_below_min(all); }
        }
        return Ok((sel, thr, Ghost(all)));
    }
    let cands = merge_sty_outs(c, lk, a, x, lo, hi, &bnd, &outs, Ghost(tk), Ghost(t), Ghost(m));
    proof { lemma_pchunk_cands(t, m, *x, cands@, e0 as int, e1 as int); }
    let (sel, thr) = pick_from_vec(&cands, Ghost(t), Ghost(m));
    Ok((sel, thr, Ghost(cands@)))
}

// ------------------------------------------------------------------------------------------------ output

/// A threshold that about 100 candidates' s_acctbal reach: the 100th largest (or the least `i64`). Its meaning is
/// checked by the caller (`count_ge`); only termination and bounds are proved here.
fn threshold(cands: &Vec<Cand>) -> (thr: i64)
{
    let nc = cands.len();
    let mut top: Vec<i64> = Vec::new();
    let mut x: usize = 0;
    while x < nc
        invariant nc == cands@.len(), x <= nc, top@.len() <= 100,
        decreases nc - x,
    {
        let v = cands[x].acct;
        let tl = top.len();
        if tl < 100 || v > top[tl - 1] {
            if tl == 100 {
                top.pop();
            }
            top.push(v);
            let mut p = top.len() - 1;
            while p > 0 && top[p - 1] < top[p]
                invariant p < top@.len(), top@.len() <= 100,
                decreases p,
            {
                let tmp = top[p - 1];
                let cur = top[p];
                top.set(p - 1, cur);
                top.set(p, tmp);
                p = p - 1;
            }
        }
        x = x + 1;
    }
    if top.len() == 100 { top[99] } else { i64::MIN }
}

/// Number of candidates whose s_acctbal reaches `thr`.
fn count_ge(cands: &Vec<Cand>, thr: i64) -> (n: usize)
    ensures n == select(cands@, ge_f(thr as int)).len(),
{
    let nc = cands.len();
    let mut n: usize = 0;
    let mut x: usize = 0;
    while x < nc
        invariant nc == cands@.len(), x <= nc, n == select(cands@.subrange(0, x as int), ge_f(thr as int)).len(), n <= x,
        decreases nc - x,
    {
        proof {
            assert(cands@.subrange(0, x + 1) =~= cands@.subrange(0, x as int).push(cands@[x as int]));
            lemma_select_push(cands@.subrange(0, x as int), cands@[x as int], ge_f(thr as int));
        }
        if cands[x].acct >= thr {
            n = n + 1;
        }
        x = x + 1;
    }
    proof { assert(cands@.subrange(0, nc as int) =~= cands@); }
    n
}

/// The output rows of the candidates reaching `thr`, in candidate order.
fn build_rows(c: &Cols, cands: &Vec<Cand>, thr: i64, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>) -> (rows: Vec<Vec<EVal>>)
    requires cols_ok(*c, t), forall|x: int| 0 <= x < cands@.len() ==> #[trigger] cand_ok(t, m, cands@[x]),
    ensures view_rows(rows@) == select(cands@, ge_f(thr as int)).map_values(row_f(t, m)),
{
    let nc = cands.len();
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut x: usize = 0;
    while x < nc
        invariant
            cols_ok(*c, t), nc == cands@.len(), x <= nc,
            forall|y: int| 0 <= y < cands@.len() ==> #[trigger] cand_ok(t, m, cands@[y]),
            view_rows(rows@) == select(cands@.subrange(0, x as int), ge_f(thr as int)).map_values(row_f(t, m)),
        decreases nc - x,
    {
        let ghost pre = cands@.subrange(0, x as int);
        proof {
            assert(cands@.subrange(0, x + 1) =~= pre.push(cands@[x as int]));
            lemma_select_push(pre, cands@[x as int], ge_f(thr as int));
        }
        if cands[x].acct >= thr {
            let r = out_row(c, cands[x], Ghost(t), Ghost(m));
            let ghost before = rows@;
            rows.push(r);
            proof {
                crate::link::outcome::lemma_view_rows_push(before, r);
                assert(select(pre, ge_f(thr as int)).push(cands@[x as int]).map_values(row_f(t, m))
                    =~= select(pre, ge_f(thr as int)).map_values(row_f(t, m)).push(out_row_spec(t, m, cands@[x as int])));
            }
        }
        x = x + 1;
    }
    proof { assert(cands@.subrange(0, nc as int) =~= cands@); }
    rows
}

/// The output rows of the candidates, in candidate order.
fn rows_of(c: &Cols, cands: &Vec<Cand>, Ghost(t): Ghost<Tabs>, Ghost(m): Ghost<Prm>) -> (rows: Vec<Vec<EVal>>)
    requires cols_ok(*c, t), forall|x: int| 0 <= x < cands@.len() ==> #[trigger] cand_ok(t, m, cands@[x]),
    ensures view_rows(rows@) == cands@.map_values(row_f(t, m)),
{
    let nc = cands.len();
    let mut rows: Vec<Vec<EVal>> = Vec::new();
    let mut x: usize = 0;
    while x < nc
        invariant
            cols_ok(*c, t), nc == cands@.len(), x <= nc,
            forall|y: int| 0 <= y < cands@.len() ==> #[trigger] cand_ok(t, m, cands@[y]),
            view_rows(rows@) == cands@.subrange(0, x as int).map_values(row_f(t, m)),
        decreases nc - x,
    {
        let r = out_row(c, cands[x], Ghost(t), Ghost(m));
        let ghost before = rows@;
        rows.push(r);
        proof {
            crate::link::outcome::lemma_view_rows_push(before, r);
            assert(cands@.subrange(0, x + 1).map_values(row_f(t, m))
                =~= cands@.subrange(0, x as int).map_values(row_f(t, m)).push(out_row_spec(t, m, cands@[x as int])));
        }
        x = x + 1;
    }
    proof { assert(cands@.subrange(0, nc as int) =~= cands@); }
    rows
}

/// The ORDER BY keys as executable keys.
fn order_keys() -> (keys: Vec<EOrderKey>)
    ensures view_keys(keys@) == q_keys(),
{
    let mut keys: Vec<EOrderKey> = Vec::new();
    keys.push(EOrderKey { col: 0, desc: true, nulls_first: true });
    keys.push(EOrderKey { col: 2, desc: false, nulls_first: false });
    keys.push(EOrderKey { col: 1, desc: false, nulls_first: false });
    keys.push(EOrderKey { col: 3, desc: false, nulls_first: false });
    proof { assert(view_keys(keys@) =~= q_keys()); }
    keys
}

/// No candidate's s_acctbal is below the least `i64`.
pub proof fn lemma_none_below_min(cs: Seq<Cand>)
    ensures select(cs, lt_f(i64::MIN as int)).len() == 0,
{
    lemma_select_members(cs, lt_f(i64::MIN as int));
    if select(cs, lt_f(i64::MIN as int)).len() > 0 {
        let c0 = select(cs, lt_f(i64::MIN as int))[0];
        assert(lt_f(i64::MIN as int)(c0));
    }
}

// ------------------------------------------------------------------------------------------------ the error answer

/// The first failing LIKE's error is the statement's meaning on every bound database.
proof fn lemma_err_answer(sv: StoresView, db0: Database, ps: Seq<Literal>, i: int, err: SqlError)
    requires
        bound_db(sv, db0),
        params_ok(ps),
        tabs_typed(tabs_of(db0)),
        0 <= i < tabs_of(db0).p.len(),
        like_res(tabs_of(db0).p[i][4], prm_of(ps).pat) == Err::<Val, SqlError>(err),
        forall|i2: int| 0 <= i2 < i ==> #[trigger] like_res(tabs_of(db0).p[i2][4], prm_of(ps).pat) is Ok,
        tabs_of(db0).s.len() > 0, tabs_of(db0).ps.len() > 0, tabs_of(db0).n.len() > 0, tabs_of(db0).r.len() > 0,
    ensures answer_meets(sv, ps, Ok::<Answer, QueryError>(Answer::SqlError(err))),
{
    assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(ps), Ok::<Answer, QueryError>(Answer::SqlError(err))) by {
        lemma_bound_same(sv, db0, db);
        lemma_eval_filter_err(db, ps, i, err);
        lemma_query_shape(ps);
        assert(denote_body(db, query_spec_at(ps)) == Err::<Relation, SqlError>(err));
    }
}

// ------------------------------------------------------------------------------------------------ the query

pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
    requires
        stores_ready(old(stores)@),
        param_domain(params@),
        1 <= workers <= MAX_WORKERS,
    ensures answer_meets(old(stores)@, params@, r),
{
    let ghost sv = stores@;
    let ghost db0 = choose|db: Database| #[trigger] bound_db(sv, db);
    proof {
        lemma_bound(sv, db0);
        lemma_params_ok(params@);
    }
    let ghost t = tabs_of(db0);
    let ghost m = prm_of(params@);
    let c = open_cols(stores, Ghost(cr_of(db0)), Ghost(sr_of(db0)));
    proof { lemma_tabs_typed(c, t); }
    // LIKE per p_type dictionary entry; a failing pattern on some part row is the statement's error.
    let (like_ok, like_err, any_err) = like_table(&c, params.p1, Ghost(t), Ghost(m));
    let nonempty = c.s.n > 0 && c.ps.n > 0 && c.n.n > 0 && c.r.n > 0;
    if any_err && nonempty {
        match first_like_error(&c, &like_err, Ghost(t), Ghost(m)) {
            Some((i, err)) => {
                proof { lemma_err_answer(sv, db0, params@, i as int, err); }
                return Ok(Answer::SqlError(err));
            },
            None => {},
        }
    }
    proof {
        if !any_err {
            lemma_like_all_from_entries(c, t, m, like_err@);
        } else if !nonempty {
            lemma_part_major(t);
            crate::link::join::lemma_product_index(t.s, t.ps);
            crate::link::join::lemma_product_index(crate::spec::relation::product_rows(t.s, t.ps), t.n);
            crate::link::join::lemma_product_index(
                crate::spec::relation::product_rows(crate::spec::relation::product_rows(t.s, t.ps), t.n), t.r);
            crate::link::join::lemma_product_index(t.p, rest_rows(t));
            assert(rest_rows(t).len() == 0) by (nonlinear_arith)
                requires
                    rest_rows(t).len() == crate::spec::relation::product_rows(crate::spec::relation::product_rows(t.s, t.ps), t.n).len() * t.r.len(),
                    crate::spec::relation::product_rows(crate::spec::relation::product_rows(t.s, t.ps), t.n).len()
                        == crate::spec::relation::product_rows(t.s, t.ps).len() * t.n.len(),
                    crate::spec::relation::product_rows(t.s, t.ps).len() == t.s.len() * t.ps.len(),
                    t.s.len() == 0 || t.ps.len() == 0 || t.n.len() == 0 || t.r.len() == 0;
            assert(prod5(t).len() == 0) by (nonlinear_arith) requires prod5(t).len() == t.p.len() * rest_rows(t).len(), rest_rows(t).len() == 0;
        }
    }
    // Nation and region lookups, dense keys.
    let (nat_tab, nkeys, nreg) = nation_lookups(&c, params.p2, Ghost(t), Ghost(m));
    let lk = Lookups { like_ok, nat_tab, nkeys, nreg };
    let (s_first, s_dense) = supp_dense(&c, Ghost(t));
    let (p_first, p_dense) = part_dense(&c, Ghost(t));
    let ps_first: i64 = if c.ps.n > 0 {
        assert(ps_row_ok(c.ps, t.ps[0], 0));
        proof { lemma_grp_bound(c.ps.n as int, c.ps.bs as int, c.ps.ng as int, 0); }
        c.ps.key_b[0] + c.ps.key_c[0] as i64
    } else {
        0
    };
    let ratio: usize = if c.p.n > 0 { c.ps.n / c.p.n } else { 0 };
    // The run layout of partsupp's ps_partkey (storage suppliers_psrun), used when it matches the part keys.
    let run = stores.suppliers_psrun.extent_i64(ppi::RUN, 0, 2);
    proof { assert(run@ =~= ppi::run_i64s(stores.suppliers_psrun@[ppi::RUN as int])); }
    let psrun: bool = run[0] >= 1 && ratio >= 1 && run[0] as u64 == ratio as u64 && run[1] == p_first;
    let a = ScanArgs { size: params.p0, s_first, s_dense, p_first, p_dense, ps_first, ratio, psrun };
    assert(scan_env(c, lk, a, t, m));
    // The candidates: from the walk of the suppliers by descending balance (storage suppliers_rank) when its indexes
    // are present; else (or past its budget) from the composite (p_size, p_type) index when it is a dense directory,
    // else by scanning every part row.
    let rk: Option<RankIdx> = if a.psrun && a.p_dense {
        open_rank(stores, c.s.n, Ghost(t), Ghost(rr_of(db0)))
    } else {
        None
    };
    let walked = match rk {
        Some(x) => walk(&c, &lk, a, &x, Ghost(t), Ghost(m)),
        None => None,
    };
    let picked = match walked {
        Some(p) => Ok(p),
        None => {
            let sx = open_styidx(stores, Ghost(xr_of(db0)), Ghost(t.p));
            match sx {
                Some(x) => scan_index(&c, &lk, a, &x, workers, dispatch, Ghost(t), Ghost(m)),
                None => match scan_all(&c, &lk, a, workers, dispatch, Ghost(t), Ghost(m)) {
                    Ok(cs) => {
                        proof { lemma_chunk_cands(t, m, cs@); }
                        let (sel, thr) = pick_from_vec(&cs, Ghost(t), Ghost(m));
                        Ok((sel, thr, Ghost(cs@)))
                    },
                    Err(e) => Err(e),
                },
            }
        },
    };
    // The rows reaching the 100th largest s_acctbal (or all rows), sorted, cut to 100.
    let (sel, thr, all) = match picked {
        Ok(p) => p,
        Err(e) => {
            return Err(e);
        },
    };
    let ghost allv = all@;
    proof {
        lemma_select_members(allv, ge_f(thr as int));
        assert forall|i: int| 0 <= i < sel@.len() implies #[trigger] cand_ok(t, m, sel@[i]) by {
            let y = choose|y: int| 0 <= y < allv.len() && allv[y] == sel@[i];
            assert(cand_ok(t, m, allv[y]));
        }
    }
    let rows = rows_of(&c, &sel, Ghost(t), Ghost(m));
    let keys = order_keys();
    let sorted = sort_rows_exec(&keys, rows);
    let out = slice_rows_exec(&sorted, 0, Some(100));
    let r = Ok(Answer::Rows(out));
    proof {
        assert forall|db: Database| #[trigger] bound_db(sv, db) implies outcome_ok(db, query_spec_at(params@), r) by {
            lemma_bound_same(sv, db0, db);
            lemma_final(db, params@, allv, thr as int);
        }
    }
    r
}

} // verus!
