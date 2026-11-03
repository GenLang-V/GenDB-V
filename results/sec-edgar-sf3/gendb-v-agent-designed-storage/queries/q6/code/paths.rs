//! The two ways from phase A's filings to every name range's groups: with one worker, phase D alone, its task
//! answering its own pair codes (`d_local`); with more, phases B, C and D (`d_routed`: routed pair codes answered
//! per bucket, so that no task needs a map over all pair codes).
use vstd::prelude::*;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::gendb_entry::work::filled;
use crate::agent::filings::{Filing, FilingOut};
use crate::agent::route::RouteOut;
use crate::agent::join::{jinputs_ok, JoinTask, JoinOut};
use crate::agent::phases::*;

verus! {

/// Phase-A outputs ready for phase D: `w` of them, each with its filings.
pub open spec fn a_ready(sv: StoresView, ps: Seq<Literal>, aouts: Seq<FilingOut>, w: int) -> bool {
    &&& aouts.len() == w
    &&& forall|k: int| 0 <= k < w ==> #[trigger] aouts[k].len <= aouts[k].filings@.len()
        && dfil_ok(sv, ps, aouts[k].filings@, aouts[k].len as int)
}

/// Every name range's groups, from its phase-A output.
pub open spec fn d_all(sv: StoresView, ps: Seq<Literal>, aouts: Seq<FilingOut>, outs: Seq<JoinOut>, w: int) -> bool {
    &&& outs.len() == w
    &&& forall|k: int| 0 <= k < w ==> #[trigger] d_done(sv, ps, aouts[k].filings@, aouts[k].len as int, outs[k])
}

/// Phase D over local tasks (one per phase-A output), each answering its own pair codes; a task that overflowed
/// its partial buffer is rerun (as in `phase_d`).
pub fn d_local(c: Ctx, cuts: &Vec<u64>, aouts: Vec<FilingOut>, dcaps: &Vec<usize>, w: usize, dispatch: &mut Dispatch)
    -> (r: Result<Vec<JoinOut>, WorkerFailure>)
    requires
        ctx_ok(c), cuts@.len() == c.nb + 1, a_ready(c.sv@, c.ps@, aouts@, w as int), dcaps@.len() == w,
        w <= MAX_WORKERS,
    ensures r matches Ok(outs) ==> d_all(c.sv@, c.ps@, aouts@, outs@, w as int),
{
    hide(ctx_ok);
    hide(jinputs_ok);
    let ghost sv = c.sv@;
    let ghost ps = c.ps@;
    let ghost a0 = aouts@;
    let mut aouts = aouts;
    let mut tasks: Vec<JoinTask> = Vec::new();
    let mut nfs: Vec<usize> = Vec::new();
    let mut k: usize = 0;
    while k < w
        invariant
            ctx_ok(c), sv == c.sv@, ps == c.ps@, cuts@.len() == c.nb + 1,
            k <= w, a_ready(sv, ps, a0, w as int), aouts@ == a0.subrange(k as int, w as int), dcaps@.len() == w,
            tasks@.len() == k, nfs@.len() == k, forall|i: int| 0 <= i < k ==> #[trigger] nfs@[i] == a0[i].len,
            forall|i: int| 0 <= i < k ==> (#[trigger] tasks@[i]).pre() && tasks@[i].filings@ == a0[i].filings@
                && tasks@[i].nf == a0[i].len && tasks@[i].sv == c.sv && tasks@[i].ps == c.ps,
        decreases w - k,
    {
        let a = aouts.remove(0);
        proof {
            assert(a == a0[k as int]);
            assert(a.len <= a.filings@.len() && dfil_ok(sv, ps, a.filings@, a.len as int));
        }
        let FilingOut { filings, len, counts: _, max_seg: _, overflow: _, pushed: _ } = a;
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
        let t = d_task(c, cuts, filings, len, cb, db, filled(c.nb, 0usize), dcaps[k], true, 0);
        tasks.push(t);
        nfs.push(len);
        proof { assert(aouts@ =~= a0.subrange(k + 1, w as int)); }
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
            k <= w, a_ready(sv, ps, a0, w as int), o0.len() == w, tg.len() == w, outs@ == o0.subrange(k as int, w as int),
            nfs@.len() == w, forall|i: int| 0 <= i < w ==> #[trigger] nfs@[i] == a0[i].len,
            forall|i: int| 0 <= i < w ==> (#[trigger] tg[i]).post(o0[i]) && tg[i].filings@ == a0[i].filings@
                && tg[i].nf == a0[i].len && tg[i].sv == c.sv && tg[i].ps == c.ps,
            fin@.len() == k,
            forall|i: int| 0 <= i < k ==> #[trigger] d_done(sv, ps, a0[i].filings@, a0[i].len as int, fin@[i]),
        decreases w - k,
    {
        let o = outs.remove(0);
        proof {
            assert(o == o0[k as int]);
            assert(tg[k as int].post(o));
            assert(a0[k as int].len <= a0[k as int].filings@.len() && dfil_ok(sv, ps, a0[k as int].filings@, a0[k as int].len as int));
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
            assert forall|i: int| 0 <= i < k + 1 implies #[trigger] d_done(sv, ps, a0[i].filings@, a0[i].len as int, fin@[i]) by {
                if i < k {
                    assert(fin@[i] == fin0[i]);
                }
            }
        }
        k = k + 1;
    }
    Ok(fin)
}

/// Phase D over tasks (one per phase-A output) that each list, sort and answer the pair codes of their own selected
/// rows (no map over all pair codes); a task that overflowed its partial buffer is rerun (as in `phase_d`).
pub fn d_self(c: Ctx, cuts: &Vec<u64>, aouts: Vec<FilingOut>, dcaps: &Vec<usize>, w: usize, dispatch: &mut Dispatch)
    -> (r: Result<Vec<JoinOut>, WorkerFailure>)
    requires
        ctx_ok(c), cuts@.len() == c.nb + 1, a_ready(c.sv@, c.ps@, aouts@, w as int), dcaps@.len() == w,
        w <= MAX_WORKERS,
    ensures r matches Ok(outs) ==> d_all(c.sv@, c.ps@, aouts@, outs@, w as int),
{
    hide(ctx_ok);
    hide(jinputs_ok);
    let ghost sv = c.sv@;
    let ghost ps = c.ps@;
    let ghost a0 = aouts@;
    let mut aouts = aouts;
    let mut tasks: Vec<JoinTask> = Vec::new();
    let mut nfs: Vec<usize> = Vec::new();
    let mut k: usize = 0;
    while k < w
        invariant
            ctx_ok(c), sv == c.sv@, ps == c.ps@, cuts@.len() == c.nb + 1,
            k <= w, a_ready(sv, ps, a0, w as int), aouts@ == a0.subrange(k as int, w as int), dcaps@.len() == w,
            tasks@.len() == k, nfs@.len() == k, forall|i: int| 0 <= i < k ==> #[trigger] nfs@[i] == a0[i].len,
            forall|i: int| 0 <= i < k ==> (#[trigger] tasks@[i]).pre() && tasks@[i].filings@ == a0[i].filings@
                && tasks@[i].nf == a0[i].len && tasks@[i].sv == c.sv && tasks@[i].ps == c.ps,
        decreases w - k,
    {
        let a = aouts.remove(0);
        proof {
            assert(a == a0[k as int]);
            assert(a.len <= a.filings@.len() && dfil_ok(sv, ps, a.filings@, a.len as int));
        }
        let FilingOut { filings, len, counts: _, max_seg: _, overflow: _, pushed: _ } = a;
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
        // room for the pair code of every selected row of the task's filings
        let mut own: usize = 0;
        let mut x: usize = 0;
        while x < len
            invariant x <= len, len <= filings@.len(),
            decreases len - x,
        {
            let ru = filings[x].rows as usize;
            if ru <= usize::MAX - own {
                own = own + ru;
            }
            x = x + 1;
        }
        let t = d_task(c, cuts, filings, len, cb, db, filled(c.nb, 0usize), dcaps[k], false, own);
        tasks.push(t);
        nfs.push(len);
        proof { assert(aouts@ =~= a0.subrange(k + 1, w as int)); }
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
            k <= w, a_ready(sv, ps, a0, w as int), o0.len() == w, tg.len() == w, outs@ == o0.subrange(k as int, w as int),
            nfs@.len() == w, forall|i: int| 0 <= i < w ==> #[trigger] nfs@[i] == a0[i].len,
            forall|i: int| 0 <= i < w ==> (#[trigger] tg[i]).post(o0[i]) && tg[i].filings@ == a0[i].filings@
                && tg[i].nf == a0[i].len && tg[i].sv == c.sv && tg[i].ps == c.ps,
            fin@.len() == k,
            forall|i: int| 0 <= i < k ==> #[trigger] d_done(sv, ps, a0[i].filings@, a0[i].len as int, fin@[i]),
        decreases w - k,
    {
        let o = outs.remove(0);
        proof {
            assert(o == o0[k as int]);
            assert(tg[k as int].post(o));
            assert(a0[k as int].len <= a0[k as int].filings@.len() && dfil_ok(sv, ps, a0[k as int].filings@, a0[k as int].len as int));
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
            assert forall|i: int| 0 <= i < k + 1 implies #[trigger] d_done(sv, ps, a0[i].filings@, a0[i].len as int, fin@[i]) by {
                if i < k {
                    assert(fin@[i] == fin0[i]);
                }
            }
        }
        k = k + 1;
    }
    Ok(fin)
}

/// Phases B, C and D: route the selected rows' pair codes to buckets, answer every bucket, join every name range.
pub fn d_routed(c: Ctx, cuts: &Vec<u64>, aouts: Vec<FilingOut>, dcaps: &Vec<usize>, w: usize, dispatch: &mut Dispatch)
    -> (r: Result<Vec<JoinOut>, WorkerFailure>)
    requires
        ctx_ok(c), c.nb == w, 1 <= w <= MAX_WORKERS,
        cuts_ok(cuts@, c.nb as int, c.inp.dicts.npp as int), forall|v: int| 0 <= v <= c.nb ==> #[trigger] cuts@[v] <= c.inp.dicts.npp,
        a_ready(c.sv@, c.ps@, aouts@, w as int), dcaps@.len() == w,
    ensures r matches Ok(outs) ==> d_all(c.sv@, c.ps@, aouts@, outs@, w as int),
{
    let ghost sv = c.sv@;
    let ghost ps = c.ps@;
    let ghost a_seq = aouts@;
    let nb = c.nb;
    // B: route the selected rows' pair codes
    let routs = match phase_b(c, cuts, aouts, w, dispatch) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    let ghost r0 = routs@;
    let mut routs = routs;
    let mut fls: Vec<Vec<Filing>> = Vec::new();
    let mut nfs: Vec<usize> = Vec::new();
    let mut rbufs: Vec<Vec<Vec<u64>>> = Vec::new();
    let mut rlens: Vec<Vec<usize>> = Vec::new();
    let mut k: usize = 0;
    while k < w
        invariant
            k <= w, r0.len() == w, routs@ == r0.subrange(k as int, w as int), a_seq.len() == w,
            forall|i: int| 0 <= i < w ==> (#[trigger] r0[i]).filings@ == a_seq[i].filings@ && r0[i].nf == a_seq[i].len
                && r0[i].bufs@.len() == nb && r0[i].lens@.len() == nb,
            fls@.len() == k, nfs@.len() == k, rbufs@.len() == k, rlens@.len() == k,
            forall|i: int| 0 <= i < k ==> (#[trigger] fls@[i])@ == a_seq[i].filings@ && nfs@[i] == a_seq[i].len
                && rbufs@[i]@.len() == nb && rlens@[i]@.len() == nb,
        decreases w - k,
    {
        let r = routs.remove(0);
        proof { assert(r == r0[k as int]); }
        let RouteOut { filings, nf, bufs, lens } = r;
        fls.push(filings);
        nfs.push(nf);
        rbufs.push(bufs);
        rlens.push(lens);
        proof { assert(routs@ =~= r0.subrange(k + 1, w as int)); }
        k = k + 1;
    }
    // C: answer every bucket's routed codes
    proof {
        assert forall|k: int| 0 <= k < w implies #[trigger] rbufs@[k]@.len() == nb && rlens@[k]@.len() == nb by {
            assert(fls@[k]@ == a_seq[k].filings@);
        }
        assert forall|k: int| 0 <= k < w implies #[trigger] rlens@[k]@.len() == nb by {
            assert(fls@[k]@ == a_seq[k].filings@);
        }
        assert forall|k: int| 0 <= k < w implies #[trigger] dfil_ok(sv, ps, fls@[k]@, nfs@[k] as int) by {
            assert(fls@[k]@ == a_seq[k].filings@);
        }
    }
    let pouts = match phase_c(c, cuts, &mut rbufs, &rlens, w, dispatch) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    let (mut pc, mut pd, mut pl) = c_store(Ghost(sv), c.inp.dicts.npp, pouts, nb, w);
    // D: join and group every name range
    let ghost f0 = fls@;
    let gouts = match phase_d(c, cuts, fls, &nfs, dcaps, &mut pc, &mut pd, &mut pl, w, dispatch) {
        Ok(o) => o,
        Err(e) => return Err(e),
    };
    proof {
        assert forall|k: int| 0 <= k < w implies #[trigger] d_done(sv, ps, a_seq[k].filings@, a_seq[k].len as int, gouts@[k]) by {
            assert(d_done(c.sv@, c.ps@, f0[k]@, nfs@[k] as int, gouts@[k]));
            assert(f0[k]@ == a_seq[k].filings@ && nfs@[k] == a_seq[k].len);
        }
    }
    Ok(gouts)
}

} // verus!
