//! The passes of a call: the part pass and the nation directory (`build_dir`), then the lineitem pass split into
//! `workers` consecutive row ranges (`line_pass`; one worker scans on the calling thread, in blocks of `SBLK` rows),
//! merged in range order.
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::agent::tables::*;
use crate::agent::line::*;
use crate::agent::cols::*;
use crate::agent::lookup::*;
use crate::agent::partpass::*;
use crate::agent::acc::*;
use crate::agent::stages::*;

verus! {

/// The part pass, the coarse filter and the nation directory.
pub fn build_dir(c: &Cols, pnat: &[u8], preg: &[u8], ptyp: &'static [u8], workers: usize, dispatch: &mut Dispatch,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Result<Dir, WorkerFailure>)
    requires
        cols_ok(*c, sv), 1 <= workers <= MAX_WORKERS,
        pnat@ == nat_of(ps), preg@ == reg_of(ps), ptyp@ == typ_of(ps),
    ensures r matches Ok(d) ==> dir_ok(d, sv, ps),
{
    let plen = ptyp.len();
    let pc = PartCols { key: c.p_key, offs: c.p_toffs, bytes: c.p_tbytes, nb: c.p_tnb, pat: ptyp, plen, np: c.np };
    let (pbits, pos0) = match part_pass(pc, workers, dispatch, Ghost(sv), Ghost(typ_of(ps))) {
        Ok(x) => x,
        Err(e) => { return Err(e); },
    };
    let coarse = build_coarse(&pbits, c.np);
    let natd = build_natdir(c, pnat, preg, Ghost(sv), Ghost(ps));
    let pos = pos0 && (c.np as u64) < 0x4000_0000_0000_0000;
    Ok(Dir { pbits, coarse, pos, nat: natd })
}

/// The lineitem pass: the totals of all lineitem rows.
pub fn line_pass(c: Cols, dir: Arc<Dir>, pat: &'static [u8], plen: usize, workers: usize, dispatch: &mut Dispatch,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Result<Acc, WorkerFailure>)
    requires
        scan_ok(c, *dir, sv, ps), pat@ == typ_of(ps), plen == pat@.len(), 1 <= workers <= MAX_WORKERS,
    ensures r matches Ok(a) ==> acc_ok(a, sv, ps, 0, n_l(sv) as int),
{
    let nl = c.nl;
    if workers == 1 {
        let mut u1 = Box::new([0u32; SBLK]);
        let mut u2 = Box::new([0u32; SBLK]);
        let mut b3 = Box::new([0usize; SBLK]);
        let mut b4 = Box::new([0usize; SBLK]);
        let mut b5 = Box::new([0usize; SBLK]);
        let acc = scan_range(&c, &*dir, pat, plen, 0, nl, &mut *u1, &mut *u2, &mut *b3, &mut *b4, &mut *b5,
            Ghost(sv), Ghost(ps));
        return Ok(acc);
    }
    let q = nl / workers;
    let rm = nl % workers;
    let mut tasks: Vec<LineTask> = Vec::new();
    let mut lo: usize = 0;
    let mut k: usize = 0;
    while k < workers
        invariant
            scan_ok(c, *dir, sv, ps), pat@ == typ_of(ps), plen == pat@.len(),
            1 <= workers <= MAX_WORKERS, k <= workers, nl == c.nl, q == nl / workers, rm == nl % workers,
            tasks@.len() == k,
            lo == split_at(nl as int, workers as int, k as int),
            forall|t: int| 0 <= t < k ==> (#[trigger] tasks@[t]).pre()
                && tasks@[t].sv@ == sv && tasks@[t].ps@ == ps
                && tasks@[t].lo == split_at(nl as int, workers as int, t)
                && tasks@[t].hi == split_at(nl as int, workers as int, t + 1),
        decreases workers - k,
    {
        proof { lemma_split(nl as int, workers as int, k as int); }
        let hi = lo + q + if k < rm { 1 } else { 0 };
        let task = LineTask {
            cols: c, dir: dir.clone(), pat, plen, lo, hi,
            u1: Box::new([0u32; BLOCK]), u2: Box::new([0u32; BLOCK]), b3: Box::new([0usize; BLOCK]),
            b4: Box::new([0usize; BLOCK]), b5: Box::new([0usize; BLOCK]),
            sv: Ghost(sv), ps: Ghost(ps),
        };
        tasks.push(task);
        lo = hi;
        k = k + 1;
    }
    let ghost tasks0 = tasks@;
    let outs = match fork_join(dispatch, tasks) {
        Ok(o) => o,
        Err(e) => { return Err(e); },
    };
    let ghost outs0 = outs@;
    proof {
        assert forall|u: int| 0 <= u < workers implies acc_ok(#[trigger] outs0[u], sv, ps,
            split_at(nl as int, workers as int, u), split_at(nl as int, workers as int, u + 1)) by {
            assert(tasks0[u].post(outs0[u]));
        }
        lemma_split(nl as int, workers as int, 0);
    }
    let mut acc = acc_zero(Ghost(sv), Ghost(ps), Ghost(0));
    let mut t: usize = 0;
    while t < workers
        invariant
            1 <= workers, t <= workers, outs@ == outs0, outs0.len() == workers, nl == c.nl,
            forall|u: int| 0 <= u < workers ==> acc_ok(#[trigger] outs0[u], sv, ps,
                split_at(nl as int, workers as int, u), split_at(nl as int, workers as int, u + 1)),
            acc_ok(acc, sv, ps, 0, split_at(nl as int, workers as int, t as int)),
        decreases workers - t,
    {
        proof { lemma_split(nl as int, workers as int, t as int); }
        acc = acc_merge(acc, outs[t], Ghost(sv), Ghost(ps), Ghost(0), Ghost(split_at(nl as int, workers as int, t as int)),
            Ghost(split_at(nl as int, workers as int, t + 1)));
        t = t + 1;
    }
    proof { lemma_split(nl as int, workers as int, (workers - 1) as int); }
    Ok(acc)
}

} // verus!
