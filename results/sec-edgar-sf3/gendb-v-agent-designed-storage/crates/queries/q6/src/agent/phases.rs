//! The four parallel phases and their partition: name ranges (phases A and D), buckets of pre pair codes (B
//! routes to them, C answers them), and the moves of the routing buffers between the phases.
use vstd::prelude::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::gendb_entry::work::{filled, put};
use crate::stores::num::interface as ni;
use crate::stores::pre::interface as pi;
use crate::stores::sub::interface as si;
use crate::stores::pre::interface::common::cols::u64s as pu64s;
use crate::agent::meaning::{p_uom, p_fy, ps_ok};
use crate::agent::views::*;
use crate::agent::fspec::*;
use crate::agent::load::{Inputs, loaded};
use crate::agent::filings::{Filing, FilingTask, FilingOut, filings_ok, empty_filing, stmt_key_ok};
use crate::agent::route::{RouteTask, RouteOut};
use crate::agent::pairs::{PairTask, PairOut, answers_ok, pd_ok, pair_ans, ANSWERED, local_ok};
use crate::agent::common::radix::RADIX_BUCKETS;
use crate::agent::join::{jinputs_ok, own_ok, JoinTask, JoinOut, Partial, TOP, empty_partial, groups_ok, rows_sum, lemma_rows_sum_mono};
use crate::agent::common::sums::*;
use crate::agent::assemble::lemma_isum_tsum;

verus! {

/// Everything a task reads: the whole parts, the run range of uom `$1`, the stmt key of `$2`, `$3`, the bucket
/// count.
#[derive(Clone, Copy)]
pub struct Ctx {
    pub inp: Inputs,
    pub run_adsh: &'static [u64],
    pub run_start: &'static [u64],
    pub nruns: usize,
    pub stmt_key: u64,
    pub fy_param: i64,
    pub nb: usize,
    pub u: Ghost<int>,
    pub ur_lo: Ghost<int>,
    pub sv: Ghost<StoresView>,
    pub ps: Ghost<Seq<Literal>>,
}

pub open spec fn ctx_ok(c: Ctx) -> bool {
    let sv = c.sv@;
    let ps = c.ps@;
    let np = sv.num;
    let u = c.u@;
    let ur_lo = c.ur_lo@;
    &&& loaded(c.inp, sv) && adsh_unique(sv) && ps_ok(ps)
    &&& 0 <= u < ni::uom_count(np) && ni::dict_entry(np, ni::P_UOM_OFF, u) == p_uom(ps)
    &&& ur_lo == ni::u64s(np, ni::P_UOM_RUNS)[u]
    &&& ur_lo + c.nruns == ni::u64s(np, ni::P_UOM_RUNS)[u + 1]
    &&& c.run_adsh@ == ni::u64s(np, ni::P_RUN_ADSH).subrange(ur_lo, ur_lo + c.nruns)
    &&& c.run_start@ == n_start(sv).subrange(ur_lo, ur_lo + c.nruns + 1)
    &&& stmt_key_ok(sv, ps, c.stmt_key)
    &&& c.fy_param == p_fy(ps)
    &&& 1 <= c.nb <= MAX_WORKERS
}

/// Cut points `0 = c[0] <= .. <= c[n] = last`.
pub open spec fn cuts_ok(c: Seq<u64>, n: int, last: int) -> bool {
    &&& c.len() == n + 1
    &&& c[0] == 0 && c[n] == last
    &&& forall|a: int, b: int| 0 <= a <= b <= n ==> #[trigger] c[a] <= #[trigger] c[b]
}

/// Name ranges balanced by the `sub` rows with fy = `$3` (performance only), and each range's count of such rows
/// (the capacity of its phase-A task; a range that needs more is rerun).
pub fn name_ranges(inp: &Inputs, fy_param: i64, w: usize) -> (r: (Vec<u64>, Vec<usize>))
    requires 1 <= w <= MAX_WORKERS,
    ensures cuts_ok(r.0@, w as int, inp.name_count as int), r.1@.len() == w,
{
    let name_count = inp.name_count;
    let mut hist: Vec<u64> = filled(name_count, 0u64);
    let mut total: u64 = 0;
    let n = if inp.fy.len() < inp.fy_valid.len() { inp.fy.len() } else { inp.fy_valid.len() };
    let n = if n < inp.name_codes.len() { n } else { inp.name_codes.len() };
    let mut j: usize = 0;
    while j < n
        invariant n <= inp.fy.len(), n <= inp.fy_valid.len(), n <= inp.name_codes.len(), hist@.len() == name_count,
        decreases n - j,
    {
        if inp.fy_valid[j] != 0 && inp.fy[j] as i64 == fy_param {
            let nm = inp.name_codes[j];
            if nm < name_count as u64 {
                let c = hist[nm as usize];
                if c < u64::MAX {
                    put(&mut hist, nm as usize, c + 1);
                }
                if total < u64::MAX {
                    total = total + 1;
                }
            }
        }
        j = j + 1;
    }
    let mut ncuts: Vec<u64> = Vec::new();
    let mut caps: Vec<usize> = Vec::new();
    ncuts.push(0);
    let mut nm: usize = 0;
    let mut acc: u64 = 0;
    let mut v: usize = 1;
    while v <= w
        invariant
            1 <= v <= w + 1, w <= MAX_WORKERS, hist@.len() == name_count, nm <= name_count,
            ncuts@.len() == v, caps@.len() == v - 1, ncuts@[0] == 0, ncuts@[v - 1] == nm,
            forall|a: int, b: int| 0 <= a <= b < v ==> #[trigger] ncuts@[a] <= #[trigger] ncuts@[b],
            v == w + 1 ==> nm == name_count,
        decreases w + 1 - v,
    {
        proof {
            assert((total as u128) * (v as u128) <= (u64::MAX as u128) * 64) by (nonlinear_arith)
                requires total <= u64::MAX, v <= 64;
        }
        let target: u128 = if v == w { u128::MAX } else { (total as u128) * (v as u128) / (w as u128) };
        let a0 = acc;
        let ghost nm0 = nm;
        while nm < name_count && (acc as u128) < target
            invariant nm0 <= nm <= name_count, hist@.len() == name_count, a0 <= acc,
            decreases name_count - nm,
        {
            let h = hist[nm];
            acc = if acc <= u64::MAX - h { acc + h } else { u64::MAX };
            nm = nm + 1;
        }
        proof {
            if v == w {
                assert((acc as u128) < u128::MAX);
            }
        }
        let ghost before = ncuts@;
        ncuts.push(nm as u64);
        let seg = acc - a0;
        caps.push(if seg as u128 <= usize::MAX as u128 { seg as usize } else { usize::MAX });
        proof {
            assert forall|a: int, b: int| 0 <= a <= b < v + 1 implies #[trigger] ncuts@[a] <= #[trigger] ncuts@[b] by {
                if b == v && a < v {
                    assert(ncuts@[a] == before[a] && before[a] <= before[v - 1]);
                } else if b < v {
                    assert(ncuts@[a] == before[a] && ncuts@[b] == before[b]);
                }
            }
        }
        v = v + 1;
    }
    (ncuts, caps)
}

/// Buckets of pre pair codes: `nb` ranges of about equal size, each cut moved down to the first code of its tag
/// (performance only).
pub fn bucket_cuts(tags: &[u64], npp: usize, nb: usize) -> (r: Vec<u64>)
    requires 1 <= nb <= MAX_WORKERS,
    ensures cuts_ok(r@, nb as int, npp as int), forall|v: int| 0 <= v <= nb ==> #[trigger] r@[v] <= npp,
{
    let mut cuts: Vec<u64> = Vec::new();
    cuts.push(0);
    let mut v: usize = 1;
    while v < nb
        invariant
            1 <= v <= nb, nb <= MAX_WORKERS, cuts@.len() == v, cuts@[0] == 0,
            forall|a: int, b: int| 0 <= a <= b < v ==> #[trigger] cuts@[a] <= #[trigger] cuts@[b],
            forall|a: int| 0 <= a < v ==> #[trigger] cuts@[a] <= npp,
        decreases nb - v,
    {
        let prev = cuts[v - 1];
        proof {
            assert((npp as u128) * (v as u128) <= (u64::MAX as u128) * 64) by (nonlinear_arith)
                requires npp <= u64::MAX, v <= 64;
        }
        let q = (npp as u128) * (v as u128) / (nb as u128);
        let mut c: u64 = if q <= npp as u128 { q as u64 } else { npp as u64 };
        while c > prev && (c as usize) < npp && (c as usize) < tags.len() && tags[c as usize] == tags[c as usize - 1]
            invariant prev < c ==> c <= npp,
            decreases c,
        {
            c = c - 1;
        }
        if c < prev {
            c = prev;
        }
        let ghost before = cuts@;
        cuts.push(c);
        proof {
            assert forall|a: int, b: int| 0 <= a <= b < v + 1 implies #[trigger] cuts@[a] <= #[trigger] cuts@[b] by {
                if b == v && a < v {
                    assert(cuts@[a] == before[a] && before[a] <= before[v - 1]);
                } else if b < v {
                    assert(cuts@[a] == before[a] && cuts@[b] == before[b]);
                }
            }
        }
        v = v + 1;
    }
    let ghost before = cuts@;
    cuts.push(npp as u64);
    proof {
        assert forall|a: int, b: int| 0 <= a <= b < nb + 1 implies #[trigger] cuts@[a] <= #[trigger] cuts@[b] by {
            if b == nb && a < nb {
                assert(cuts@[a] == before[a]);
            } else if b < nb {
                assert(cuts@[a] == before[a] && cuts@[b] == before[b]);
            }
        }
    }
    cuts
}

/// Phase-A tasks build their own adsh-rank hint (one pass over all `sub` rows) only when there are at most this many
/// of them; with more tasks that pass costs more than the binary searches it saves.
pub const RANK_HINT_MAX_TASKS: usize = 4;

/// The phase-A task of the names `[n_lo, n_hi)` with room for `cap` filings.
pub fn a_task(c: Ctx, cuts: &Vec<u64>, n_lo: u64, n_hi: u64, cap: usize) -> (t: FilingTask)
    requires ctx_ok(c), cuts@.len() == c.nb + 1, n_lo <= n_hi,
    ensures
        t.pre(), t.n_lo == n_lo, t.n_hi == n_hi, t.cap == cap, t.ns == c.inp.ns, t.sv == c.sv, t.ps == c.ps,
        t.nbuckets == c.nb,
{
    let inp = c.inp;
    FilingTask {
        fy: inp.fy, fy_valid: inp.fy_valid, name_codes: inp.name_codes, sadsh_off: inp.sadsh_off,
        sadsh_bytes: inp.sadsh_bytes, ns: inp.ns, adsh_order: inp.sadsh_order, norder: inp.norder,
        rank: if c.nb <= RANK_HINT_MAX_TASKS { vec![0u32; inp.ns] } else { Vec::new() }, fy_param: c.fy_param, n_lo, n_hi,
        nadsh_off: inp.nadsh_off, nadsh_bytes: inp.nadsh_bytes, nadsh_count: inp.nadsh_count,
        run_adsh: c.run_adsh, run_start: c.run_start, nruns: c.nruns,
        padsh_off: inp.padsh_off, padsh_bytes: inp.padsh_bytes, padsh_count: inp.padsh_count,
        adsh_subs: inp.adsh_subs, sub_start: inp.sub_start, sub_group: inp.sub_group, nsubs: inp.nsubs,
        group_stmt: inp.group_stmt, stmt_key: c.stmt_key, pre_tv: inp.pre_tv, npre: inp.npre,
        cuts: cuts.clone(), nbuckets: c.nb,
        out: vec![empty_filing(); cap], tmp: vec![empty_filing(); cap], cap,
        counts: filled(c.nb, 0u64),
        sv: c.sv, ps: c.ps, u: c.u, ur_lo: c.ur_lo,
    }
}

/// A finished phase-A output for the names `[lo, hi)`.
pub open spec fn a_done(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, a: FilingOut) -> bool {
    filings_ok(sv, ps, lo, hi, a) && !a.overflow
}

/// Phase A: the filings of every name range (a range that overflowed its capacity is rerun with room for every
/// `sub` row).
pub fn phase_a(c: Ctx, cuts: &Vec<u64>, ncuts: &Vec<u64>, caps: &Vec<usize>, w: usize, dispatch: &mut Dispatch)
    -> (r: Result<Vec<FilingOut>, WorkerFailure>)
    requires
        ctx_ok(c), cuts@.len() == c.nb + 1, cuts_ok(ncuts@, w as int, c.inp.name_count as int), caps@.len() == w,
        1 <= w <= MAX_WORKERS,
    ensures
        r matches Ok(outs) ==> outs@.len() == w
            && forall|k: int| 0 <= k < w ==> #[trigger] a_done(c.sv@, c.ps@, ncuts@[k] as int, ncuts@[k + 1] as int, outs@[k]),
{
    hide(crate::agent::filings::inputs_ok);
    let mut tasks: Vec<FilingTask> = Vec::new();
    let mut v: usize = 0;
    while v < w
        invariant
            ctx_ok(c), cuts@.len() == c.nb + 1, cuts_ok(ncuts@, w as int, c.inp.name_count as int), caps@.len() == w,
            v <= w, tasks@.len() == v,
            forall|i: int| 0 <= i < v ==> (#[trigger] tasks@[i]).pre() && tasks@[i].n_lo == ncuts@[i]
                && tasks@[i].n_hi == ncuts@[i + 1] && tasks@[i].sv == c.sv && tasks@[i].ps == c.ps && tasks@[i].ns == c.inp.ns,
        decreases w - v,
    {
        let t = a_task(c, cuts, ncuts[v], ncuts[v + 1], caps[v]);
        tasks.push(t);
        v = v + 1;
    }
    let ghost tg = tasks@;
    let mut outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    let ghost o0 = outs@;
    let mut k: usize = 0;
    while k < w
        invariant
            ctx_ok(c), cuts@.len() == c.nb + 1, cuts_ok(ncuts@, w as int, c.inp.name_count as int),
            k <= w, outs@.len() == w, o0.len() == w, tg.len() == w,
            forall|i: int| 0 <= i < w ==> (#[trigger] tg[i]).post(o0[i]) && tg[i].n_lo == ncuts@[i]
                && tg[i].n_hi == ncuts@[i + 1] && tg[i].sv == c.sv && tg[i].ps == c.ps && tg[i].ns == c.inp.ns,
            forall|i: int| k <= i < w ==> #[trigger] outs@[i] == o0[i],
            forall|i: int| 0 <= i < k ==> #[trigger] a_done(c.sv@, c.ps@, ncuts@[i] as int, ncuts@[i + 1] as int, outs@[i]),
        decreases w - k,
    {
        if outs[k].overflow {
            let t = a_task(c, cuts, ncuts[k], ncuts[k + 1], c.inp.ns);
            let o = t.run();
            put(&mut outs, k, o);
        } else {
            assert(tg[k as int].post(o0[k as int]));
        }
        k = k + 1;
    }
    Ok(outs)
}

/// Lengths of the loaded parts.
pub proof fn lemma_loaded_lens(t: Inputs, sv: StoresView)
    requires loaded(t, sv),
    ensures
        t.sub_start@.len() == t.nsubs + 1, t.sub_group@.len() == t.nsubs, t.group_stmt@.len() == t.ngroups,
        t.pre_tv@.len() == t.npre,
{
    assert(pi::pre_layout_ok(sv.pre));
    assert(pi::sub_count(sv.pre) == pu64s(sv.pre, pi::P_SUB_GROUP).len());
}

/// Phase B: route the selected rows' pair codes of each name range to bucket buffers (sized by phase A's counts).
pub fn phase_b(c: Ctx, cuts: &Vec<u64>, aouts: Vec<FilingOut>, w: usize, dispatch: &mut Dispatch)
    -> (r: Result<Vec<RouteOut>, WorkerFailure>)
    requires
        ctx_ok(c), cuts@.len() == c.nb + 1, aouts@.len() == w, w <= MAX_WORKERS,
        forall|k: int| 0 <= k < w ==> (#[trigger] aouts@[k]).len <= aouts@[k].filings@.len(),
    ensures
        r matches Ok(outs) ==> outs@.len() == w && forall|k: int| 0 <= k < w ==> (#[trigger] outs@[k]).filings@ == aouts@[k].filings@
            && outs@[k].nf == aouts@[k].len && outs@[k].bufs@.len() == c.nb && outs@[k].lens@.len() == c.nb,
{
    let ghost a0 = aouts@;
    proof { lemma_loaded_lens(c.inp, c.sv@); }
    let inp = c.inp;
    let mut aouts = aouts;
    let mut tasks: Vec<RouteTask> = Vec::new();
    let mut k: usize = 0;
    while k < w
        invariant
            ctx_ok(c), inp == c.inp, cuts@.len() == c.nb + 1, k <= w, a0.len() == w, aouts@ == a0.subrange(k as int, w as int),
            inp.sub_start@.len() == inp.nsubs + 1, inp.sub_group@.len() == inp.nsubs, inp.group_stmt@.len() == inp.ngroups,
            inp.pre_tv@.len() == inp.npre,
            forall|i: int| 0 <= i < w ==> (#[trigger] a0[i]).len <= a0[i].filings@.len(),
            tasks@.len() == k,
            forall|i: int| 0 <= i < k ==> (#[trigger] tasks@[i]).pre() && tasks@[i].filings@ == a0[i].filings@
                && tasks@[i].nf == a0[i].len && tasks@[i].nbuckets == c.nb,
        decreases w - k,
    {
        let a = aouts.remove(0);
        proof { assert(a == a0[k as int]); }
        let mut bufs: Vec<Vec<u64>> = Vec::new();
        let mut v: usize = 0;
        while v < c.nb
            invariant bufs@.len() == v, v <= c.nb,
            decreases c.nb - v,
        {
            let n: usize = if v < a.counts.len() && a.counts[v] <= usize::MAX as u64 { a.counts[v] as usize } else { 0 };
            bufs.push(vec![0u64; n]);
            v = v + 1;
        }
        let FilingOut { filings, len, counts: _, max_seg: _, overflow: _, pushed: _ } = a;
        tasks.push(RouteTask {
            filings, nf: len, cuts: cuts.clone(), nbuckets: c.nb, sub_start: inp.sub_start, sub_group: inp.sub_group,
            nsubs: inp.nsubs, group_stmt: inp.group_stmt, ngroups: inp.ngroups, stmt_key: c.stmt_key,
            pre_tv: inp.pre_tv, npre: inp.npre, bufs, lens: filled(c.nb, 0usize),
        });
        proof {
            assert(aouts@ =~= a0.subrange(k + 1, w as int));
        }
        k = k + 1;
    }
    let ghost tg = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    proof {
        assert forall|k: int| 0 <= k < w implies (#[trigger] outs@[k]).filings@ == a0[k].filings@
            && outs@[k].nf == a0[k].len && outs@[k].bufs@.len() == c.nb && outs@[k].lens@.len() == c.nb by {
            assert(tg[k].post(outs@[k]));
        }
    }
    Ok(outs)
}

/// Move buffer `[k][v]` out (an empty one is left).
fn take(bufs: &mut Vec<Vec<Vec<u64>>>, k: usize, v: usize) -> (r: Vec<u64>)
    requires k < old(bufs)@.len(), v < old(bufs)@[k as int]@.len(),
    ensures
        final(bufs)@.len() == old(bufs)@.len(),
        forall|a: int| 0 <= a < old(bufs)@.len() ==> #[trigger] final(bufs)@[a]@.len() == old(bufs)@[a]@.len(),
        r@ == old(bufs)@[k as int]@[v as int]@,
{
    let mut tmp: Vec<u64> = Vec::new();
    {
        let inner = vstd::std_specs::vec::vec_index_mut(bufs, k);
        let slot = vstd::std_specs::vec::vec_index_mut(inner, v);
        core::mem::swap(slot, &mut tmp);
    }
    tmp
}

/// Phase C: per bucket, the num pair of every routed pre pair code. Its inputs are the routed buffers of every
/// name range (`rbufs[k][v]`, lengths `rlens[k][v]`).
pub fn phase_c(c: Ctx, cuts: &Vec<u64>, rbufs: &mut Vec<Vec<Vec<u64>>>, rlens: &Vec<Vec<usize>>, w: usize,
    dispatch: &mut Dispatch) -> (r: Result<Vec<PairOut>, WorkerFailure>)
    requires
        ctx_ok(c), cuts_ok(cuts@, c.nb as int, c.inp.dicts.npp as int),
        forall|v: int| 0 <= v <= c.nb ==> #[trigger] cuts@[v] <= c.inp.dicts.npp,
        old(rbufs)@.len() == w, forall|k: int| 0 <= k < w ==> #[trigger] old(rbufs)@[k]@.len() == c.nb,
        rlens@.len() == w, forall|k: int| 0 <= k < w ==> #[trigger] rlens@[k]@.len() == c.nb,
        w <= MAX_WORKERS,
    ensures
        r matches Ok(outs) ==> outs@.len() == c.nb && forall|v: int| 0 <= v < c.nb
            ==> answers_ok(c.sv@, c.inp.dicts.npp as int, (#[trigger] outs@[v]).cbufs@, outs@[v].dbufs@, outs@[v].lens@)
                && outs@[v].cbufs@.len() == w,
{
    hide(ctx_ok);
    hide(pd_ok);
    let nb = c.nb;
    assert(pd_ok(c.inp.dicts, c.sv@) && nb <= MAX_WORKERS) by { reveal(ctx_ok); }
    let mut tasks: Vec<PairTask> = Vec::new();
    let mut v: usize = 0;
    while v < nb
        invariant
            pd_ok(c.inp.dicts, c.sv@), nb == c.nb, v <= nb, nb <= MAX_WORKERS, cuts_ok(cuts@, c.nb as int, c.inp.dicts.npp as int),
            forall|a: int| 0 <= a <= c.nb ==> #[trigger] cuts@[a] <= c.inp.dicts.npp,
            rbufs@.len() == w, forall|k: int| 0 <= k < w ==> #[trigger] rbufs@[k]@.len() == c.nb,
            rlens@.len() == w, forall|k: int| 0 <= k < w ==> #[trigger] rlens@[k]@.len() == c.nb,
            tasks@.len() == v,
            forall|i: int| 0 <= i < v ==> (#[trigger] tasks@[i]).pre() && tasks@[i].sv == c.sv
                && tasks@[i].dicts == c.inp.dicts && tasks@[i].nw == w,
        decreases nb - v,
    {
        let mut cb: Vec<Vec<u64>> = Vec::new();
        let mut db: Vec<Vec<u64>> = Vec::new();
        let mut lens: Vec<usize> = Vec::new();
        let mut k: usize = 0;
        while k < w
            invariant
                v < nb, nb == c.nb, k <= w,
                rbufs@.len() == w, forall|a: int| 0 <= a < w ==> #[trigger] rbufs@[a]@.len() == c.nb,
                rlens@.len() == w, forall|a: int| 0 <= a < w ==> #[trigger] rlens@[a]@.len() == c.nb,
                cb@.len() == k, db@.len() == k, lens@.len() == k,
                forall|i: int| 0 <= i < k ==> #[trigger] lens@[i] <= cb@[i]@.len() && lens@[i] <= db@[i]@.len(),
            decreases w - k,
        {
            let b = take(rbufs, k, v);
            let n = b.len();
            let l0 = rlens[k][v];
            let l = if l0 <= n { l0 } else { n };
            cb.push(b);
            db.push(vec![0u64; n]);
            lens.push(l);
            k = k + 1;
        }
        let p_lo = cuts[v] as usize;
        let p_hi = cuts[v + 1] as usize;
        tasks.push(PairTask {
            dicts: c.inp.dicts, p_lo, p_hi, map: vec![0u64; p_hi - p_lo], need: vec![0u8; p_hi - p_lo], cbufs: cb, dbufs: db, lens, nw: w, sv: c.sv,
        });
        v = v + 1;
    }
    let ghost tg = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    proof {
        assert forall|v: int| 0 <= v < c.nb implies answers_ok(c.sv@, c.inp.dicts.npp as int, (#[trigger] outs@[v]).cbufs@, outs@[v].dbufs@, outs@[v].lens@)
            && outs@[v].cbufs@.len() == w by {
            assert(tg[v].post(outs@[v]));
        }
    }
    Ok(outs)
}

/// One routed buffer with its answers: every listed code below `npp` is answered.
pub open spec fn entry_ok(sv: StoresView, npp: int, c: Seq<u64>, d: Seq<u64>, l: int) -> bool {
    &&& 0 <= l <= c.len() && l <= d.len()
    &&& forall|k: int| 0 <= k < l && c[k] < npp ==> #[trigger] pair_ans(sv, c[k] as int, d[k])
}

/// The answered buffers of every bucket (`pc[v][k]`, `pd[v][k]`, `pl[v][k]` for name range `k`).
pub open spec fn store_ok(sv: StoresView, npp: int, pc: Seq<Vec<Vec<u64>>>, pd: Seq<Vec<Vec<u64>>>, pl: Seq<Vec<usize>>,
    nb: int, w: int) -> bool {
    &&& pc.len() == nb && pd.len() == nb && pl.len() == nb
    &&& forall|v: int| 0 <= v < nb ==> (#[trigger] pc[v])@.len() == w && pd[v]@.len() == w && pl[v]@.len() == w
    &&& forall|v: int, k: int| 0 <= v < nb && 0 <= k < w ==> #[trigger] entry_ok(sv, npp, pc[v]@[k]@, pd[v]@[k]@, pl[v]@[k] as int)
}

/// Phase C's outputs as the answered buffers of every bucket.
pub fn c_store(Ghost(sv): Ghost<StoresView>, npp: usize, outs: Vec<PairOut>, nb: usize, w: usize)
    -> (r: (Vec<Vec<Vec<u64>>>, Vec<Vec<Vec<u64>>>, Vec<Vec<usize>>))
    requires
        outs@.len() == nb,
        forall|v: int| 0 <= v < nb ==> answers_ok(sv, npp as int, (#[trigger] outs@[v]).cbufs@, outs@[v].dbufs@, outs@[v].lens@)
            && outs@[v].cbufs@.len() == w,
    ensures store_ok(sv, npp as int, r.0@, r.1@, r.2@, nb as int, w as int),
{
    let ghost o0 = outs@;
    let mut outs = outs;
    let mut pc: Vec<Vec<Vec<u64>>> = Vec::new();
    let mut pd: Vec<Vec<Vec<u64>>> = Vec::new();
    let mut pl: Vec<Vec<usize>> = Vec::new();
    let mut v: usize = 0;
    while v < nb
        invariant
            v <= nb, o0.len() == nb, outs@ == o0.subrange(v as int, nb as int),
            forall|a: int| 0 <= a < nb ==> answers_ok(sv, npp as int, (#[trigger] o0[a]).cbufs@, o0[a].dbufs@, o0[a].lens@)
                && o0[a].cbufs@.len() == w,
            store_ok(sv, npp as int, pc@, pd@, pl@, v as int, w as int),
        decreases nb - v,
    {
        let o = outs.remove(0);
        proof { assert(o == o0[v as int]); }
        let PairOut { cbufs, dbufs, lens } = o;
        let ghost (pc0, pd0, pl0) = (pc@, pd@, pl@);
        pc.push(cbufs);
        pd.push(dbufs);
        pl.push(lens);
        proof {
            assert(outs@ =~= o0.subrange(v + 1, nb as int));
            assert forall|a: int, k: int| 0 <= a < v + 1 && 0 <= k < w implies #[trigger] entry_ok(sv, npp as int, pc@[a]@[k]@, pd@[a]@[k]@, pl@[a]@[k] as int) by {
                if a < v {
                    assert(pc@[a] == pc0[a] && pd@[a] == pd0[a] && pl@[a] == pl0[a]);
                } else {
                    assert(pc@[a] == cbufs && pd@[a] == dbufs && pl@[a] == lens);
                }
            }
        }
        v = v + 1;
    }
    (pc, pd, pl)
}

/// Move bucket `v`'s buffers of name range `k` out (empty ones, length 0, are left).
fn take3(Ghost(sv): Ghost<StoresView>, npp: usize, pc: &mut Vec<Vec<Vec<u64>>>, pd: &mut Vec<Vec<Vec<u64>>>,
    pl: &mut Vec<Vec<usize>>, v: usize, k: usize, Ghost(nb): Ghost<int>, Ghost(w): Ghost<int>) -> (r: (Vec<u64>, Vec<u64>, usize))
    requires store_ok(sv, npp as int, old(pc)@, old(pd)@, old(pl)@, nb, w), v < nb, k < w,
    ensures store_ok(sv, npp as int, final(pc)@, final(pd)@, final(pl)@, nb, w), entry_ok(sv, npp as int, r.0@, r.1@, r.2 as int),
{
    let ghost (pc0, pd0, pl0) = (pc@, pd@, pl@);
    proof { assert(pc0[v as int]@.len() == w && pd0[v as int]@.len() == w && pl0[v as int]@.len() == w); }
    let l = pl[v][k];
    let mut c: Vec<u64> = Vec::new();
    let mut d: Vec<u64> = Vec::new();
    {
        let inner = vstd::std_specs::vec::vec_index_mut(pc, v);
        let slot = vstd::std_specs::vec::vec_index_mut(inner, k);
        core::mem::swap(slot, &mut c);
    }
    {
        let inner = vstd::std_specs::vec::vec_index_mut(pd, v);
        let slot = vstd::std_specs::vec::vec_index_mut(inner, k);
        core::mem::swap(slot, &mut d);
    }
    {
        let li = vstd::std_specs::vec::vec_index_mut(pl, v);
        put(li, k, 0);
    }
    proof {
        assert(entry_ok(sv, npp as int, pc0[v as int]@[k as int]@, pd0[v as int]@[k as int]@, pl0[v as int]@[k as int] as int));
        assert forall|a: int| 0 <= a < nb implies (#[trigger] pc@[a])@.len() == w && pd@[a]@.len() == w && pl@[a]@.len() == w by {
            if a != v {
                assert(pc@[a] == pc0[a] && pd@[a] == pd0[a] && pl@[a] == pl0[a]);
            }
        }
        assert forall|a: int, b: int| 0 <= a < nb && 0 <= b < w implies #[trigger] entry_ok(sv, npp as int, pc@[a]@[b]@, pd@[a]@[b]@, pl@[a]@[b] as int) by {
            if a != v {
                assert(pc@[a] == pc0[a] && pd@[a] == pd0[a] && pl@[a] == pl0[a]);
            } else if b != k {
                assert(pc@[a]@[b] == pc0[a]@[b] && pd@[a]@[b] == pd0[a]@[b] && pl@[a]@[b] == pl0[a]@[b]);
            }
        }
    }
    (c, d, l)
}

/// A phase-D input: `nf` filings, sorted by name, whose selected rows fit in `usize`.
pub open spec fn dfil_ok(sv: StoresView, ps: Seq<Literal>, fl: Seq<Filing>, nf: int) -> bool {
    &&& 0 <= nf <= fl.len()
    &&& forall|x: int| 0 <= x < nf ==> filing_ok(sv, ps, #[trigger] fl[x])
    &&& forall|x: int, y: int| 0 <= x < y < nf ==> (#[trigger] fl[x]).nm <= (#[trigger] fl[y]).nm
    &&& rows_sum(fl, 0, nf) <= p_count(sv)
}

/// A finished phase-A output is a phase-D input.
pub proof fn lemma_a_dfil(sv: StoresView, ps: Seq<Literal>, lo: int, hi: int, a: FilingOut)
    requires a_done(sv, ps, lo, hi, a),
    ensures dfil_ok(sv, ps, a.filings@, a.len as int),
{
    broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms};
    let fl = a.filings@;
    let nf = a.len as int;
    let p = a.pushed@;
    assert forall|x: int| 0 <= x < nf implies filing_ok(sv, ps, #[trigger] fl[x]) by {
        let v = fl.subrange(0, nf)[x];
        assert(v == fl[x]);
        assert(fl.subrange(0, nf).contains(v));
        assert(p.to_multiset().count(v) > 0);
        assert(p.contains(v));
    }
    let h = |f: Filing| rows_of(f);
    lemma_isum_tsum(fl, nf, h);
    lemma_isum_ext(0, nf, |x: int| h(fl[x]), |x: int| fl[x].rows as int);
    lemma_tsum_perm(fl.subrange(0, nf), p, h);
}

/// The phase-D task of filings `filings[0..nf)` with the answered buffers and room for `cap` partials; a `local`
/// task answers its own pair codes (a need list and a map over all pre pair codes).
pub fn d_task(c: Ctx, cuts: &Vec<u64>, filings: Vec<Filing>, nf: usize, cbufs: Vec<Vec<u64>>, dbufs: Vec<Vec<u64>>,
    lens: Vec<usize>, cap: usize, local: bool, own: usize) -> (t: JoinTask)
    requires
        ctx_ok(c), cuts@.len() == c.nb + 1, dfil_ok(c.sv@, c.ps@, filings@, nf as int),
        answers_ok(c.sv@, c.inp.dicts.npp as int, cbufs@, dbufs@, lens@), lens@.len() == c.nb,
    ensures t.pre(), t.filings@ == filings@, t.nf == nf, t.cap == cap, t.sv == c.sv, t.ps == c.ps,
{
    let inp = c.inp;
    let (need, lmap): (Vec<u8>, Vec<u64>) = if local {
        (vec![0u8; inp.dicts.npp], vec![0u64; inp.dicts.npp])
    } else {
        (Vec::new(), Vec::new())
    };
    let codes: Vec<u64> = vec![0u64; own];
    let cans: Vec<u64> = vec![0u64; own];
    let counts: Vec<usize> = if own > 0 { vec![0usize; RADIX_BUCKETS] } else { Vec::new() };
    proof {
        reveal(own_ok);
        reveal(local_ok);
        assert forall|x: int| 0 <= x < need@.len() && #[trigger] need@[x] == ANSWERED implies pair_ans(c.sv@, x, lmap@[x]) by {
            assert(need@[x] == 0u8);
        }
    }
    JoinTask {
        filings, nf, dicts: inp.dicts, cuts: cuts.clone(), nbuckets: c.nb, cbufs, dbufs, lens,
        cursors: filled(c.nb, 0usize), sub_start: inp.sub_start, sub_group: inp.sub_group, nsubs: inp.nsubs,
        group_stmt: inp.group_stmt, stmt_key: c.stmt_key, pre_tv: inp.pre_tv, npre: inp.npre,
        plabel_codes: inp.plabel_codes, plabel_valid: inp.plabel_valid, nplabel: inp.nplabel,
        num_tv: inp.num_tv, num_val: inp.num_val, nrows: inp.nrows,
        parts: vec![empty_partial(); cap], tmp: vec![empty_partial(); cap], cap,
        top: vec![empty_partial(); TOP], need, lmap, codes, cans, ncodes: 0, counts, sv: c.sv, ps: c.ps,
    }
}

/// A finished phase-D output for filings `fl[0..nf)`.
pub open spec fn d_done(sv: StoresView, ps: Seq<Literal>, fl: Seq<Filing>, nf: int, o: JoinOut) -> bool {
    groups_ok(sv, ps, fl, nf, o) && !o.overflow && o.top@.len() == TOP
}

/// Rerun phase D for `o`'s filings without routed answers and with room for all their selected rows.
pub fn d_rerun(c: Ctx, cuts: &Vec<u64>, o: JoinOut, nf: usize) -> (r: JoinOut)
    requires ctx_ok(c), cuts@.len() == c.nb + 1, dfil_ok(c.sv@, c.ps@, o.filings@, nf as int),
    ensures d_done(c.sv@, c.ps@, o.filings@, nf as int, r),
{
    let ghost fl = o.filings@;
    let JoinOut { filings, top: _, len: _, cnt_over: _, mass_over: _, overflow: _, groups: _, rest: _ } = o;
    let mut tot: usize = 0;
    let mut x: usize = 0;
    proof { lemma_loaded_lens(c.inp, c.sv@); }
    while x < nf
        invariant
            ctx_ok(c), x <= nf, filings@ == fl, dfil_ok(c.sv@, c.ps@, fl, nf as int), c.inp.npre == p_count(c.sv@),
            tot as int == rows_sum(fl, 0, x as int),
        decreases nf - x,
    {
        proof {
            lemma_rows_sum_mono(fl, 0, 0, x + 1, nf as int);
            assert(rows_sum(fl, 0, x + 1) == rows_sum(fl, 0, x as int) + fl[x as int].rows);
        }
        tot = tot + filings[x].rows as usize;
        x = x + 1;
    }
    let mut cb: Vec<Vec<u64>> = Vec::new();
    let mut db: Vec<Vec<u64>> = Vec::new();
    let mut v: usize = 0;
    while v < c.nb
        invariant v <= c.nb, cb@.len() == v, db@.len() == v,
            forall|i: int| 0 <= i < v ==> (#[trigger] cb@[i])@.len() == 0 && db@[i]@.len() == 0,
        decreases c.nb - v,
    {
        cb.push(Vec::new());
        db.push(Vec::new());
        v = v + 1;
    }
    let t = d_task(c, cuts, filings, nf, cb, db, filled(c.nb, 0usize), tot, false, 0);
    t.run()
}

/// Per-buffer answers make answered lists.
proof fn lemma_entries_answers(sv: StoresView, npp: int, cs: Seq<Vec<u64>>, ds: Seq<Vec<u64>>, ls: Seq<usize>)
    requires
        cs.len() == ls.len() && ds.len() == ls.len(),
        forall|i: int| 0 <= i < ls.len() ==> #[trigger] entry_ok(sv, npp, cs[i]@, ds[i]@, ls[i] as int),
    ensures answers_ok(sv, npp, cs, ds, ls),
{
    assert forall|i: int, k: int| 0 <= i < ls.len() && 0 <= k < ls[i] && cs[i]@[k] < npp
        implies #[trigger] pair_ans(sv, cs[i]@[k] as int, ds[i]@[k]) by {
        assert(entry_ok(sv, npp, cs[i]@, ds[i]@, ls[i] as int));
    }
    assert forall|i: int| 0 <= i < ls.len() implies #[trigger] ls[i] <= cs[i]@.len() && ls[i] <= ds[i]@.len() by {
        assert(entry_ok(sv, npp, cs[i]@, ds[i]@, ls[i] as int));
    }
}

/// Phase D: the groups of every name range (a range whose partials overflowed is rerun with room for all).
pub fn phase_d(c: Ctx, cuts: &Vec<u64>, fls: Vec<Vec<Filing>>, nfs: &Vec<usize>, dcaps: &Vec<usize>,
    pc: &mut Vec<Vec<Vec<u64>>>, pd: &mut Vec<Vec<Vec<u64>>>, pl: &mut Vec<Vec<usize>>, w: usize, dispatch: &mut Dispatch)
    -> (r: Result<Vec<JoinOut>, WorkerFailure>)
    requires
        ctx_ok(c), cuts@.len() == c.nb + 1, fls@.len() == w, nfs@.len() == w, dcaps@.len() == w, w <= MAX_WORKERS,
        forall|k: int| 0 <= k < w ==> #[trigger] dfil_ok(c.sv@, c.ps@, fls@[k]@, nfs@[k] as int),
        store_ok(c.sv@, c.inp.dicts.npp as int, old(pc)@, old(pd)@, old(pl)@, c.nb as int, w as int),
    ensures
        r matches Ok(outs) ==> outs@.len() == w
            && forall|k: int| 0 <= k < w ==> #[trigger] d_done(c.sv@, c.ps@, fls@[k]@, nfs@[k] as int, outs@[k]),
{
    hide(ctx_ok);
    hide(jinputs_ok);
    let ghost sv = c.sv@;
    let ghost ps = c.ps@;
    let ghost f0 = fls@;
    let npp = c.inp.dicts.npp;
    let nb = c.nb;
    let mut fls = fls;
    let mut tasks: Vec<JoinTask> = Vec::new();
    let mut k: usize = 0;
    while k < w
        invariant
            ctx_ok(c), sv == c.sv@, ps == c.ps@, npp == c.inp.dicts.npp, nb == c.nb, cuts@.len() == c.nb + 1,
            k <= w, f0.len() == w, fls@ == f0.subrange(k as int, w as int), nfs@.len() == w, dcaps@.len() == w,
            forall|i: int| 0 <= i < w ==> #[trigger] dfil_ok(sv, ps, f0[i]@, nfs@[i] as int),
            store_ok(sv, npp as int, pc@, pd@, pl@, nb as int, w as int),
            tasks@.len() == k,
            forall|i: int| 0 <= i < k ==> (#[trigger] tasks@[i]).pre() && tasks@[i].filings@ == f0[i]@
                && tasks@[i].nf == nfs@[i] && tasks@[i].sv == c.sv && tasks@[i].ps == c.ps,
        decreases w - k,
    {
        let filings = fls.remove(0);
        proof { assert(filings == f0[k as int]); }
        let mut cb: Vec<Vec<u64>> = Vec::new();
        let mut db: Vec<Vec<u64>> = Vec::new();
        let mut lens: Vec<usize> = Vec::new();
        let mut v: usize = 0;
        while v < nb
            invariant
                k < w, v <= nb, store_ok(sv, npp as int, pc@, pd@, pl@, nb as int, w as int),
                cb@.len() == v, db@.len() == v, lens@.len() == v,
                forall|i: int| 0 <= i < v ==> #[trigger] entry_ok(sv, npp as int, cb@[i]@, db@[i]@, lens@[i] as int),
            decreases nb - v,
        {
            let (x, y, l) = take3(Ghost(sv), npp, pc, pd, pl, v, k, Ghost(nb as int), Ghost(w as int));
            let ghost (cb0, db0, l0) = (cb@, db@, lens@);
            cb.push(x);
            db.push(y);
            lens.push(l);
            proof {
                assert forall|i: int| 0 <= i < v + 1 implies #[trigger] entry_ok(sv, npp as int, cb@[i]@, db@[i]@, lens@[i] as int) by {
                    if i < v {
                        assert(cb@[i] == cb0[i] && db@[i] == db0[i] && lens@[i] == l0[i]);
                    }
                }
            }
            v = v + 1;
        }
        proof { lemma_entries_answers(sv, npp as int, cb@, db@, lens@); }
        let t = d_task(c, cuts, filings, nfs[k], cb, db, lens, dcaps[k], false, 0);
        tasks.push(t);
        proof { assert(fls@ =~= f0.subrange(k + 1, w as int)); }
        k = k + 1;
    }
    let ghost tg = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    let ghost o0 = outs@;
    let mut outs = outs;
    let mut fin: Vec<JoinOut> = Vec::new();
    let mut k: usize = 0;
    while k < w
        invariant
            ctx_ok(c), sv == c.sv@, ps == c.ps@, cuts@.len() == c.nb + 1,
            k <= w, f0.len() == w, nfs@.len() == w, o0.len() == w, tg.len() == w, outs@ == o0.subrange(k as int, w as int),
            forall|i: int| 0 <= i < w ==> #[trigger] dfil_ok(sv, ps, f0[i]@, nfs@[i] as int),
            forall|i: int| 0 <= i < w ==> (#[trigger] tg[i]).post(o0[i]) && tg[i].filings@ == f0[i]@
                && tg[i].nf == nfs@[i] && tg[i].sv == c.sv && tg[i].ps == c.ps,
            fin@.len() == k,
            forall|i: int| 0 <= i < k ==> #[trigger] d_done(sv, ps, f0[i]@, nfs@[i] as int, fin@[i]),
        decreases w - k,
    {
        let o = outs.remove(0);
        proof {
            assert(o == o0[k as int]);
            assert(tg[k as int].post(o));
        }
        let ghost fin0 = fin@;
        if o.overflow {
            let o2 = d_rerun(c, cuts, o, nfs[k]);
            fin.push(o2);
        } else {
            fin.push(o);
        }
        proof {
            assert(outs@ =~= o0.subrange(k + 1, w as int));
            assert forall|i: int| 0 <= i < k + 1 implies #[trigger] d_done(sv, ps, f0[i]@, nfs@[i] as int, fin@[i]) by {
                if i < k {
                    assert(fin@[i] == fin0[i]);
                }
            }
        }
        k = k + 1;
    }
    Ok(fin)
}

} // verus!
