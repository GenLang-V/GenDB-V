//! The partitioned plan of a round (`fast_counts`): phase A (`sel`) in waves of at most `workers` tasks over cuts of
//! the part rows (each task also decides a range of supplier rows for the subquery), the bitmap of excluded supplier
//! rows, then phase B (`gcount`) over at most `workers` ranges of partitions. Every local group's count is the size of
//! its set `answer::pset`. `Ok(None)` when the plan does not apply (supplier rows beyond `2^20`, part rows beyond
//! 32-bit offsets, a full region or scratch): the round then runs the general plan (`round::general_counts`).
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::parallel::{Dispatch, fork_join, MAX_WORKERS, WorkerTask};
use crate::gendb_entry::runtime::QueryError;
use super::tables::*;
use super::model::*;
use super::kernel::*;
use super::sel::*;
use super::gcount::*;
use super::answer::pset;
use super::split::*;
use super::round::{supp_task, lemma_cuts_mono, lemma_find};
use super::supp::{cc_row, comm_ok, supp_out_ok, SuppOut};
use super::common::marks::{lemma_zero_holds, bit_at, holds, mark_new};

verus! {

/// Task `k` of the cuts `bnd` (part rows) and `sb` (supplier rows).
pub open spec fn sel_task_at(e: PairEnv, ng: usize, np: usize, bnd: Seq<usize>, sb: Seq<usize>, k: int, tk: SelTask) -> bool {
    &&& tk.pre()
    &&& *tk.env == e
    &&& tk.ng == ng
    &&& tk.np == np
    &&& tk.lo == bnd[k]
    &&& tk.hi == bnd[k + 1]
    &&& tk.supp.s == e.c.s
    &&& tk.supp.lo == sb[k]
    &&& tk.supp.hi == sb[k + 1]
    &&& tk.supp.cap >= tk.supp.hi - tk.supp.lo
}

/// Output `k`: its pairs when finished, and its matching supplier rows.
pub open spec fn sel_done(e: PairEnv, np: usize, bnd: Seq<usize>, sb: Seq<usize>, k: int, o: SelOut) -> bool {
    &&& o.ok ==> sel_ok(*e.tabs, e.c, bnd[k] as int, bnd[k + 1] as int, np as int, o)
    &&& o.supp.done
    &&& supp_out_ok(e.c.s, sb[k] as int, sb[k + 1] as int, o.supp)
}

/// What the plan needs of a round.
pub open spec fn fast_pre(e: PairEnv, ng: int, np: int) -> bool {
    &&& env_ok(e, ng)
    &&& ng <= 64 * np
    &&& np < 0x10_0000
    &&& e.c.s.n <= 0x10_0000
    &&& e.c.p.n < 0xFFFF_FFFF
    &&& comm_ok(e.c.s)
}

/// One wave: the tasks `[k0, k1)` in one fork-join.
fn sel_wave(env: &Arc<PairEnv>, ng: usize, np: usize, bnd: &Vec<usize>, sb: &Vec<usize>, k0: usize, k1: usize,
    dispatch: &mut Dispatch) -> (r: Result<Vec<SelOut>, QueryError>)
    requires
        fast_pre(**env, ng as int, np as int),
        cuts(bnd@, env.c.p.n as int), cuts(sb@, env.c.s.n as int), sb@.len() == bnd@.len(),
        k0 <= k1 < bnd@.len(), k1 - k0 <= MAX_WORKERS,
    ensures
        r matches Err(e) ==> e is WorkerFailed,
        r matches Ok(outs) ==> outs@.len() == k1 - k0
            && forall|i: int| 0 <= i < outs@.len() ==> #[trigger] sel_done(**env, np, bnd@, sb@, k0 + i, outs@[i]),
{
    let pn = env.c.p.n;
    let sn = env.c.s.n;
    let ratio = env.ratio;
    let nk = bnd.len() - 1;
    let mut tasks: Vec<SelTask> = Vec::new();
    let mut k = k0;
    while k < k1
        invariant
            fast_pre(**env, ng as int, np as int),
            cuts(bnd@, pn as int), cuts(sb@, sn as int), sb@.len() == bnd@.len(), nk == bnd@.len() - 1,
            pn == env.c.p.n, sn == env.c.s.n, ratio == env.ratio,
            k0 <= k <= k1 <= nk, k1 - k0 <= MAX_WORKERS,
            tasks@.len() == k - k0,
            forall|i: int| 0 <= i < tasks@.len() ==> #[trigger] sel_task_at(**env, ng, np, bnd@, sb@, k0 + i, tasks@[i]),
        decreases k1 - k,
    {
        let lo = bnd[k];
        let hi = bnd[k + 1];
        proof {
            lemma_cuts_mono(bnd@, pn as int, k as int, k + 1);
            lemma_cuts_mono(bnd@, pn as int, k + 1, nk as int);
            lemma_cuts_mono(sb@, sn as int, k as int, k + 1);
            lemma_cuts_mono(sb@, sn as int, k + 1, nk as int);
        }
        let rows = hi - lo;
        // At least 2^23 entries each: the allocator then maps fresh zero pages instead of clearing them here.
        let pcap = if rows + 1 > 0x80_0000 { rows + 1 } else { 0x80_0000 };
        proof {
            let (ri, ti) = (rows as int, ratio as int);
            assert(ri * ti <= 0xFFFF_FFFF_FFFF_FFFFint * 0xFFFF_FFFF_FFFF_FFFFint) by (nonlinear_arith)
                requires 0 <= ri <= 0xFFFF_FFFF_FFFF_FFFFint, 0 <= ti <= 0xFFFF_FFFF_FFFF_FFFFint;
        }
        let w: u128 = (rows as u128) * (ratio as u128);
        let ocap: usize = if w <= 0x80_0000 { 0x80_0000 } else if w < 0xFFFF_FFFF { w as usize } else { 0xFFFF_FFFF };
        let st = supp_task(&env.c.s, sb[k], sb[k + 1]);
        let tk = SelTask {
            env: env.clone(),
            ng,
            np,
            lo,
            hi,
            ptmp: vec![0u32; pcap],
            pcode: vec![0u32; pcap],
            btab: [0u32; 256],
            ttab: [0u32; 256],
            stab: [0u32; 256],
            cv: [0u8; 8],
            hits: [0u8; 64],
            idx: [0u8; 64],
            out: vec![0u32; ocap],
            start: vec![0usize; np + 1],
            cur: vec![0usize; np + 1],
            supp: st,
        };
        proof {
            assert(sel_pre(**env, ng as int, np as int, lo as int, hi as int, tk.ptmp@, tk.start@, tk.cur@));
        }
        tasks.push(tk);
        proof {
            assert(sel_task_at(**env, ng, np, bnd@, sb@, k as int, tasks@[k - k0]));
        }
        k = k + 1;
    }
    let ghost ts = tasks@;
    proof {
        assert forall|i: int| 0 <= i < tasks@.len() implies #[trigger] tasks@[i].pre() by {
            assert(sel_task_at(**env, ng, np, bnd@, sb@, k0 + i, tasks@[i]));
        }
    }
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => {
            return Err(QueryError::WorkerFailed(e));
        },
    };
    proof {
        assert forall|i: int| 0 <= i < outs@.len() implies #[trigger] sel_done(**env, np, bnd@, sb@, k0 + i, outs@[i]) by {
            assert(sel_task_at(**env, ng, np, bnd@, sb@, k0 + i, ts[i]));
            assert(ts[i].post(outs@[i]));
            assert(ts[i].supp.post(outs@[i].supp));
        }
    }
    Ok(outs)
}

/// Outputs `all[..nk]` of the cuts.
pub open spec fn sels_done(e: PairEnv, np: usize, bnd: Seq<usize>, sb: Seq<usize>, all: Seq<SelOut>, nk: int) -> bool {
    forall|k: int| 0 <= k < nk ==> #[trigger] sel_done(e, np, bnd, sb, k, all[k])
}

proof fn lemma_sels_append(e: PairEnv, np: usize, bnd: Seq<usize>, sb: Seq<usize>, all: Seq<SelOut>, outs: Seq<SelOut>, k0: int)
    requires
        sels_done(e, np, bnd, sb, all, k0), all.len() == k0,
        forall|i: int| 0 <= i < outs.len() ==> #[trigger] sel_done(e, np, bnd, sb, k0 + i, outs[i]),
    ensures sels_done(e, np, bnd, sb, all + outs, k0 + outs.len()),
{
    let a1 = all + outs;
    assert forall|k: int| 0 <= k < k0 + outs.len() implies #[trigger] sel_done(e, np, bnd, sb, k, a1[k]) by {
        if k < k0 {
            assert(a1[k] == all[k]);
        } else {
            assert(a1[k] == outs[k - k0]);
            assert(sel_done(e, np, bnd, sb, k0 + (k - k0), outs[k - k0]));
        }
    }
}

/// Output `k` lists exactly the matching supplier rows of `[sb[k], sb[k + 1])`.
pub open spec fn sdone(s: SCols, sb: Seq<usize>, k: int, o: SelOut) -> bool {
    o.supp.done && supp_out_ok(s, sb[k] as int, sb[k + 1] as int, o.supp)
}

/// The bitmap of the supplier rows the subquery excludes, from the outputs' supplier lists.
fn excl_sel(s: &SCols, all: &Vec<SelOut>, sb: &Vec<usize>) -> (r: Vec<u64>)
    requires
        cuts(sb@, s.n as int), sb@.len() == all@.len() + 1,
        forall|k: int| 0 <= k < all@.len() ==> #[trigger] sdone(*s, sb@, k, all@[k]),
    ensures
        s.n <= 64 * r@.len(),
        forall|j: int| 0 <= j < s.n ==> #[trigger] bit_at(r@, j) == cc_row(*s, j),
{
    let mut excl: Vec<u64> = vec![0u64; s.n / 64 + 1];
    proof {
        lemma_zero_holds(excl@);
        assert(s.n <= 64 * (s.n / 64 + 1)) by (nonlinear_arith)
            requires s.n == 64 * (s.n / 64) + s.n % 64, s.n % 64 < 64;
    }
    let ghost mut set: Set<int> = Set::empty();
    let nout = all.len();
    let mut t: usize = 0;
    while t < nout
        invariant
            nout == all@.len(),
            cuts(sb@, s.n as int), sb@.len() == all@.len() + 1,
            forall|k: int| 0 <= k < all@.len() ==> #[trigger] sdone(*s, sb@, k, all@[k]),
            t <= nout,
            s.n <= 64 * excl@.len(),
            holds(excl@, set),
            forall|j: int| #[trigger] set.contains(j) ==> 0 <= j < s.n && cc_row(*s, j),
            forall|j: int| 0 <= j < sb@[t as int] && #[trigger] cc_row(*s, j) ==> set.contains(j),
        decreases nout - t,
    {
        let o: &SuppOut = &all[t].supp;
        let lo = sb[t];
        let hi = sb[t + 1];
        proof {
            lemma_cuts_mono(sb@, s.n as int, t as int, t + 1);
            lemma_cuts_mono(sb@, s.n as int, t + 1, nout as int);
            assert(sdone(*s, sb@, t as int, all@[t as int]));
            assert(supp_out_ok(*s, lo as int, hi as int, *o));
        }
        let mut q: usize = 0;
        while q < o.len
            invariant
                supp_out_ok(*s, lo as int, hi as int, *o),
                lo <= hi <= s.n,
                q <= o.len,
                s.n <= 64 * excl@.len(),
                holds(excl@, set),
                forall|j: int| #[trigger] set.contains(j) ==> 0 <= j < s.n && cc_row(*s, j),
                forall|j: int| 0 <= j < lo && #[trigger] cc_row(*s, j) ==> set.contains(j),
                forall|q2: int| 0 <= q2 < q ==> #[trigger] set.contains(o.rows@[q2] as int),
            decreases o.len - q,
        {
            let j = o.rows[q];
            assert(lo <= o.rows@[q as int] < hi && cc_row(*s, o.rows@[q as int] as int));
            let _ = mark_new(&mut excl, j, Ghost(set));
            proof {
                set = set.insert(j as int);
            }
            q = q + 1;
        }
        proof {
            assert forall|j: int| 0 <= j < hi && #[trigger] cc_row(*s, j) implies set.contains(j) by {
                if j >= lo {
                    let q2 = choose|q2: int| 0 <= q2 < o.len && o.rows@[q2] == j;
                    assert(set.contains(o.rows@[q2] as int));
                }
            }
        }
        t = t + 1;
    }
    proof {
        assert forall|j: int| 0 <= j < s.n implies #[trigger] bit_at(excl@, j) == cc_row(*s, j) by {
            if cc_row(*s, j) {
                assert(set.contains(j));
            }
        }
    }
    excl
}

/// Phase A's waves over the cuts `bnd` (part rows) and `sb` (supplier rows).
fn sel_waves(env: &Arc<PairEnv>, ng: usize, np: usize, workers: usize, bnd: &Vec<usize>, sb: &Vec<usize>,
    dispatch: &mut Dispatch) -> (r: Result<Vec<SelOut>, QueryError>)
    requires
        fast_pre(**env, ng as int, np as int),
        1 <= workers <= MAX_WORKERS,
        cuts(bnd@, env.c.p.n as int), cuts(sb@, env.c.s.n as int), sb@.len() == bnd@.len(),
    ensures
        r matches Err(e) ==> e is WorkerFailed,
        r matches Ok(all) ==> all@.len() == bnd@.len() - 1 && sels_done(**env, np, bnd@, sb@, all@, all@.len() as int),
{
    let nk = bnd.len() - 1;
    let er: &PairEnv = &**env;
    let mut all: Vec<SelOut> = Vec::new();
    let mut k0: usize = 0;
    while k0 < nk
        invariant
            *er == **env,
            fast_pre(**env, ng as int, np as int),
            1 <= workers <= MAX_WORKERS,
            cuts(bnd@, env.c.p.n as int), nk == bnd@.len() - 1,
            cuts(sb@, env.c.s.n as int), sb@.len() == nk + 1,
            k0 <= nk, all@.len() == k0,
            sels_done(**env, np, bnd@, sb@, all@, k0 as int),
        decreases nk - k0,
    {
        let k1 = if nk - k0 > workers { k0 + workers } else { nk };
        let outs = match sel_wave(env, ng, np, bnd, sb, k0, k1, dispatch) {
            Ok(o) => o,
            Err(e) => {
                return Err(e);
            },
        };
        let ghost a0 = all@;
        let ghost ov = outs@;
        let mut outs = outs;
        all.append(&mut outs);
        proof {
            lemma_sels_append(*er, np, bnd@, sb@, a0, ov, k0 as int);
            assert(all@ == a0 + ov);
        }
        k0 = k1;
    }
    Ok(all)
}

/// Every output finished.
fn all_ok(all: &Vec<SelOut>) -> (b: bool)
    ensures b == forall|k: int| 0 <= k < all@.len() ==> (#[trigger] all@[k]).ok,
{
    let nk = all.len();
    let mut k: usize = 0;
    while k < nk
        invariant nk == all@.len(), k <= nk, forall|k2: int| 0 <= k2 < k ==> (#[trigger] all@[k2]).ok,
        decreases nk - k,
    {
        if !all[k].ok {
            return false;
        }
        k = k + 1;
    }
    true
}

/// Finished outputs of the waves: their pairs and their supplier rows.
proof fn lemma_sels_ok(e: PairEnv, np: usize, bnd: Seq<usize>, sb: Seq<usize>, all: Seq<SelOut>)
    requires
        sels_done(e, np, bnd, sb, all, all.len() as int),
        forall|k: int| 0 <= k < all.len() ==> (#[trigger] all[k]).ok,
    ensures
        forall|k: int| 0 <= k < all.len() ==> #[trigger] sel_ok(*e.tabs, e.c, bnd[k] as int, bnd[k + 1] as int, np as int, all[k]),
        forall|k: int| 0 <= k < all.len() ==> #[trigger] sdone(e.c.s, sb, k, all[k]),
{
    assert forall|k: int| 0 <= k < all.len() implies #[trigger] sel_ok(*e.tabs, e.c, bnd[k] as int, bnd[k + 1] as int, np as int, all[k]) by {
        assert(sel_done(e, np, bnd, sb, k, all[k]));
        assert(all[k].ok);
    }
    assert forall|k: int| 0 <= k < all.len() implies #[trigger] sdone(e.c.s, sb, k, all[k]) by {
        assert(sel_done(e, np, bnd, sb, k, all[k]));
    }
}

/// Phase A: every output finished (else `None`), and the excluded supplier rows.
fn sel_phase(env: &Arc<PairEnv>, ng: usize, np: usize, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<Option<(Vec<SelOut>, Vec<usize>, Vec<u64>)>, QueryError>)
    requires
        fast_pre(**env, ng as int, np as int),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Err(e) ==> e is WorkerFailed,
        r matches Ok(Some((all, bnd, ex))) ==> {
            &&& cuts(bnd@, env.c.p.n as int)
            &&& all@.len() == bnd@.len() - 1
            &&& forall|k: int| 0 <= k < all@.len() ==>
                #[trigger] sel_ok(*env.tabs, env.c, bnd@[k] as int, bnd@[k + 1] as int, np as int, all@[k])
            &&& env.c.s.n <= 64 * ex@.len()
            &&& forall|j: int| 0 <= j < env.c.s.n ==> #[trigger] bit_at(ex@, j) == cc_row(env.c.s, j)
        },
{
    let pn = env.c.p.n;
    let sn = env.c.s.n;
    // About 1M part rows per task, at least one task per worker; whole part blocks.
    let want = pn / 0x10_0000 + 1;
    let ntask = if want > workers { want } else { workers };
    let b0 = split_range(pn, ntask, env.c.p.bs);
    let bnd = if b0.len() < 2 { pad_cuts(b0, pn, 2) } else { b0 };
    let nk = bnd.len() - 1;
    let sb = pad_cuts(split_range(sn, nk, 1), sn, nk + 1);
    let er: &PairEnv = &**env;
    let all = match sel_waves(env, ng, np, workers, &bnd, &sb, dispatch) {
        Ok(a) => a,
        Err(e) => {
            return Err(e);
        },
    };
    if !all_ok(&all) {
        return Ok(None);
    }
    proof {
        lemma_sels_ok(*er, np, bnd@, sb@, all@);
    }
    let ex = excl_sel(&env.c.s, &all, &sb);
    Ok(Some((all, bnd, ex)))
}

/// Scratch entries for the partitions `[q0, q1)`: the largest total of their regions over every output (saturating).
fn scratch_need(all: &Vec<SelOut>, q0: usize, q1: usize, Ghost(np): Ghost<int>, Ghost(sn): Ghost<int>) -> (mx: usize)
    requires outs_shape(all@, np, sn), q0 <= q1 <= np,
{
    let nt = all.len();
    let mut mx: usize = 0;
    let mut q = q0;
    while q < q1
        invariant outs_shape(all@, np, sn), q0 <= q <= q1 <= np, nt == all@.len(),
        decreases q1 - q,
    {
        let mut n: usize = 0;
        let mut t: usize = 0;
        while t < nt
            invariant outs_shape(all@, np, sn), q < np, nt == all@.len(), t <= nt,
            decreases nt - t,
        {
            proof {
                assert(regs_ok(all@[t as int].start@, all@[t as int].cur@, all@[t as int].out@, np, sn));
            }
            let d = all[t].cur[q] - all[t].start[q];
            n = if n <= usize::MAX - d { n + d } else { usize::MAX };
            t = t + 1;
        }
        if n > mx {
            mx = n;
        }
        q = q + 1;
    }
    mx
}

/// The weight of each partition: its entries over every output (saturating).
fn part_weights(all: &Vec<SelOut>, np: usize, Ghost(sn): Ghost<int>) -> (w: Vec<u64>)
    requires outs_shape(all@, np as int, sn),
    ensures w@.len() == np,
{
    let nt = all.len();
    let mut w: Vec<u64> = Vec::new();
    let mut q: usize = 0;
    while q < np
        invariant outs_shape(all@, np as int, sn), q <= np, nt == all@.len(), w@.len() == q,
        decreases np - q,
    {
        let mut n: u64 = 0;
        let mut t: usize = 0;
        while t < nt
            invariant outs_shape(all@, np as int, sn), q < np, nt == all@.len(), t <= nt,
            decreases nt - t,
        {
            proof {
                assert(regs_ok(all@[t as int].start@, all@[t as int].cur@, all@[t as int].out@, np as int, sn));
            }
            let d = (all[t].cur[q] - all[t].start[q]) as u64;
            n = if n <= u64::MAX - d { n + d } else { u64::MAX };
            t = t + 1;
        }
        w.push(n);
        q = q + 1;
    }
    w
}

/// Phase B: every local group's count (`None` when a partition did not fit its task's scratch).
fn grp_phase(outs: Arc<Vec<SelOut>>, excl: Arc<Vec<u64>>, sn: usize, np: usize, ng: usize, workers: usize,
    dispatch: &mut Dispatch) -> (r: Result<Option<Vec<u64>>, QueryError>)
    requires
        outs_shape(outs@, np as int, sn as int),
        sn <= 64 * excl@.len(),
        np < 0x10_0000,
        ng <= 64 * np,
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Err(e) ==> e is WorkerFailed,
        r matches Ok(Some(cs)) ==> cs@.len() == ng
            && forall|g: int| 0 <= g < ng ==> #[trigger] cs@[g] as int == dset2(outs@, excl@, sn as int, g).len(),
{
    // Ranges of partitions of about equal entry counts (partitions of unused codes are empty).
    let pb = weight_cuts(&part_weights(&*outs, np, Ghost(sn as int)), workers);
    let ntb = pb.len() - 1;
    let mut tasks: Vec<GrpTask> = Vec::new();
    let mut i: usize = 0;
    while i < ntb
        invariant
            outs_shape(outs@, np as int, sn as int), sn <= 64 * excl@.len(), np < 0x10_0000,
            cuts(pb@, np as int), ntb == pb@.len() - 1, ntb <= workers, workers <= MAX_WORKERS,
            i <= ntb, tasks@.len() == i,
            forall|i2: int| 0 <= i2 < i ==> (#[trigger] tasks@[i2]).pre() && tasks@[i2].outs@ == outs@
                && tasks@[i2].excl@ == excl@ && tasks@[i2].sn == sn && tasks@[i2].np == np
                && tasks@[i2].q0 == pb@[i2] && tasks@[i2].q1 == pb@[i2 + 1],
        decreases ntb - i,
    {
        let q0 = pb[i];
        let q1 = pb[i + 1];
        proof {
            lemma_cuts_mono(pb@, np as int, i as int, i + 1);
            lemma_cuts_mono(pb@, np as int, i + 1, ntb as int);
        }
        let mx = scratch_need(&*outs, q0, q1, Ghost(np as int), Ghost(sn as int));
        let cap = if mx < 0xFFFF_FFFF { mx + 1 } else { mx };
        let marks = vec![0u64; sn / 64 + 1];
        proof {
            lemma_zero_holds(marks@);
            assert(sn <= 64 * (sn / 64 + 1)) by (nonlinear_arith)
                requires sn == 64 * (sn / 64) + sn % 64, sn % 64 < 64;
            assert(64 * (q1 - q0) <= 64 * np) by (nonlinear_arith) requires q1 - q0 <= np;
        }
        let tk = GrpTask {
            outs: outs.clone(),
            excl: excl.clone(),
            sn,
            np,
            q0,
            q1,
            ents: vec![0u32; cap],
            loc: vec![0u32; cap],
            offs: vec![0usize; 65],
            marks,
            counts: vec![0u64; 64 * (q1 - q0)],
        };
        tasks.push(tk);
        i = i + 1;
    }
    let ghost ts = tasks@;
    let couts = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => {
            return Err(QueryError::WorkerFailed(e));
        },
    };
    let mut cs: Vec<u64> = Vec::new();
    let mut i: usize = 0;
    proof {
        lemma_cuts_mono(pb@, np as int, 0, ntb as int);
    }
    while i < ntb
        invariant
            cuts(pb@, np as int), ntb == pb@.len() - 1, couts@.len() == ntb, ts.len() == ntb,
            ng <= 64 * np,
            forall|i2: int| 0 <= i2 < ntb ==> (#[trigger] ts[i2]).post(couts@[i2]) && ts[i2].outs@ == outs@
                && ts[i2].excl@ == excl@ && ts[i2].sn == sn && ts[i2].q0 == pb@[i2] && ts[i2].q1 == pb@[i2 + 1],
            i <= ntb,
            cs@.len() == if 64 * pb@[i as int] < ng { 64 * pb@[i as int] } else { ng as int },
            forall|g: int| 0 <= g < cs@.len() ==> #[trigger] cs@[g] as int == dset2(outs@, excl@, sn as int, g).len(),
        decreases ntb - i,
    {
        let co = &couts[i];
        if !co.ok {
            return Ok(None);
        }
        proof {
            assert(ts[i as int].post(couts@[i as int]));
            lemma_cuts_mono(pb@, np as int, i as int, i + 1);
        }
        let cv = &co.counts;
        let ghost base = 64 * pb@[i as int];
        let mut h: usize = 0;
        while h < cv.len()
            invariant
                cv@.len() == 64 * (pb@[i + 1] - pb@[i as int]),
                base == 64 * pb@[i as int],
                pb@[i as int] <= pb@[i + 1],
                forall|g: int| 64 * pb@[i as int] <= g < 64 * pb@[i + 1] ==>
                    #[trigger] dset2(outs@, excl@, sn as int, g).len() == cv@[g - 64 * pb@[i as int]] as int,
                h <= cv@.len(),
                cs@.len() == if base + h < ng { base + h } else { ng as int },
                forall|g: int| 0 <= g < cs@.len() ==> #[trigger] cs@[g] as int == dset2(outs@, excl@, sn as int, g).len(),
            decreases cv@.len() - h,
        {
            if cs.len() < ng {
                let ghost c0 = cs@;
                cs.push(cv[h]);
                proof {
                    assert forall|g: int| 0 <= g < cs@.len() implies #[trigger] cs@[g] as int == dset2(outs@, excl@, sn as int, g).len() by {
                        if g < c0.len() {
                            assert(cs@[g] == c0[g]);
                        } else {
                            assert(g == base + h);
                        }
                    }
                }
            }
            h = h + 1;
        }
        i = i + 1;
    }
    proof {
        assert(pb@[ntb as int] == np);
    }
    Ok(Some(cs))
}

/// The outputs of the cuts of `[0, p.n)` have, together, exactly the round's pairs.
proof fn lemma_sel_cover(e: PairEnv, np: usize, bnd: Seq<usize>, all: Seq<SelOut>, g: int, x: int)
    requires
        cuts(bnd, e.c.p.n as int),
        all.len() == bnd.len() - 1,
        forall|k: int| 0 <= k < all.len() ==> #[trigger] sel_ok(*e.tabs, e.c, bnd[k] as int, bnd[k + 1] as int, np as int, all[k]),
        0 <= g < 64 * np,
    ensures in_any(all, g, x) <==> pair_in(*e.tabs, e.c, 0, e.c.p.n as int, g, x),
{
    let q = *e.tabs;
    let c = e.c;
    if in_any(all, g, x) {
        let t = choose|t: int| 0 <= t < all.len() && #[trigger] reg_has(all[t], g, x);
        assert(sel_ok(q, c, bnd[t] as int, bnd[t + 1] as int, np as int, all[t]));
        assert(pair_in(q, c, bnd[t] as int, bnd[t + 1] as int, g, x));
        let (j, i) = choose|j: int, i: int| bnd[t] <= j < bnd[t + 1] && #[trigger] pair_at(q, c, j, i, g, x);
        lemma_cuts_mono(bnd, c.p.n as int, t + 1, bnd.len() - 1);
        assert(pair_in(q, c, 0, c.p.n as int, g, x));
    }
    if pair_in(q, c, 0, c.p.n as int, g, x) {
        let (j, i) = choose|j: int, i: int| 0 <= j < c.p.n && #[trigger] pair_at(q, c, j, i, g, x);
        lemma_find(bnd, c.p.n as int, j, 0);
        let k = choose|k: int| 0 <= k < bnd.len() - 1 && bnd[k] <= j < #[trigger] bnd[k + 1];
        assert(sel_ok(q, c, bnd[k] as int, bnd[k + 1] as int, np as int, all[k]));
        assert(pair_in(q, c, bnd[k] as int, bnd[k + 1] as int, g, x));
        assert(reg_has(all[k], g, x));
    }
}

/// The partitioned plan's counts: `Some(cs)` with every local group's count, or `None` when it does not apply.
pub fn fast_counts(env: &Arc<PairEnv>, ng: usize, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<Option<Vec<u64>>, QueryError>)
    requires
        env_ok(**env, ng as int),
        ng <= 0x40000,
        1 <= workers <= MAX_WORKERS,
        comm_ok(env.c.s),
    ensures
        r matches Err(e) ==> e is WorkerFailed,
        r matches Ok(Some(cs)) ==> cs@.len() == ng
            && forall|g: int| 0 <= g < ng ==> #[trigger] cs@[g] as int == pset(*env.tabs, env.c, g).len(),
{
    if env.c.s.n > XLIM || env.c.p.n >= 0xFFFF_FFFF {
        return Ok(None);
    }
    let np = (ng + 63) / 64;
    proof {
        assert(ng <= 64 * np) by (nonlinear_arith) requires np == (ng + 63) / 64, ng >= 0;
    }
    let sn = env.c.s.n;
    let er: &PairEnv = &**env;
    let (all, bnd, ex) = match sel_phase(env, ng, np, workers, dispatch) {
        Ok(Some(t)) => t,
        Ok(None) => {
            return Ok(None);
        },
        Err(e) => {
            return Err(e);
        },
    };
    let ghost av = all@;
    let ghost exv = ex@;
    proof {
        assert(outs_shape(av, np as int, sn as int)) by {
            assert forall|t: int| 0 <= t < av.len() implies #[trigger] regs_ok(av[t].start@, av[t].cur@, av[t].out@, np as int, sn as int) by {
                assert(sel_ok(*env.tabs, env.c, bnd@[t] as int, bnd@[t + 1] as int, np as int, av[t]));
            }
        }
    }
    let outs = Arc::new(all);
    let excl = Arc::new(ex);
    let cs = match grp_phase(outs, excl, sn, np, ng, workers, dispatch) {
        Ok(Some(cs)) => cs,
        Ok(None) => {
            return Ok(None);
        },
        Err(e) => {
            return Err(e);
        },
    };
    proof {
        assert forall|g: int| 0 <= g < ng implies #[trigger] cs@[g] as int == pset(*env.tabs, env.c, g).len() by {
            let d2 = dset2(av, exv, sn as int, g);
            let ps = pset(*env.tabs, env.c, g);
            assert forall|x: int| #[trigger] d2.contains(x) == ps.contains(x) by {
                lemma_sel_cover(*er, np, bnd@, av, g, x);
            }
            assert(d2 =~= ps);
        }
    }
    Ok(Some(cs))
}

} // verus!
