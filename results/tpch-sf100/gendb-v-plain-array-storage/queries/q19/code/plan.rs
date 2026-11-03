//! The lineitem pass over all rows: one `ScanTask` per even range of rows (`parts::split_at`), joined by
//! `fork_join` and merged in range order (blocks of `TASK_BLOCK` rows); with one worker (or few rows) the whole
//! table is scanned on the calling thread (blocks of `BLOCK` rows).
use vstd::prelude::*;
use std::sync::Arc;
use crate::spec::ast::Literal;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::agent::line::*;
use crate::agent::bind::*;
use crate::agent::keymap::*;
use crate::agent::parts::{split_at, lemma_split};
use crate::agent::scan::*;

verus! {

/// Rows per task below which the scan stays on the calling thread.
pub const MIN_TASK_ROWS: usize = 1_048_576;

/// The totals of all lineitem rows.
pub fn line_pass(c: ScanCols, x: Bind, km: Arc<KeyMap>, workers: usize, dispatch: &mut Dispatch,
    Ghost(sv): Ghost<StoresView>, Ghost(ps): Ghost<Seq<Literal>>) -> (r: Result<Acc, WorkerFailure>)
    requires scan_inputs_ok(c, x, *km, sv, ps), 1 <= workers <= MAX_WORKERS,
    ensures r matches Ok(a) ==> acc_ok(a, tot(sv, ps, 0, c.line.nl as int)),
{
    let nl = c.line.nl;
    let mut nt = workers;
    if nl / MIN_TASK_ROWS < nt {
        nt = nl / MIN_TASK_ROWS;
    }
    if nt <= 1 {
        let mut sel: Vec<u32> = vec![0u32; BLOCK];
        let mut sel2: Vec<u32> = vec![0u32; BLOCK];
        let mut tags: Vec<u8> = vec![0u8; BLOCK];
        let acc = scan_range(&c, &x, &*km, 0, nl, &mut sel, &mut sel2, &mut tags, Ghost(sv), Ghost(ps));
        return Ok(acc);
    }
    let q = nl / nt;
    let rm = nl % nt;
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut lo: usize = 0;
    let mut k: usize = 0;
    while k < nt
        invariant
            scan_inputs_ok(c, x, *km, sv, ps), 2 <= nt <= MAX_WORKERS, k <= nt, nl == c.line.nl,
            q == nl / nt, rm == nl % nt,
            tasks@.len() == k,
            lo == split_at(nl as int, nt as int, k as int),
            forall|t: int| 0 <= t < k ==> (#[trigger] tasks@[t]).pre()
                && tasks@[t].sv@ == sv && tasks@[t].ps@ == ps
                && tasks@[t].lo == split_at(nl as int, nt as int, t)
                && tasks@[t].hi == split_at(nl as int, nt as int, t + 1),
        decreases nt - k,
    {
        proof { lemma_split(nl as int, nt as int, k as int); }
        let hi = lo + q + if k < rm { 1 } else { 0 };
        let task = ScanTask { cols: c, bind: x, km: km.clone(), lo, hi, sel: vec![0u32; TASK_BLOCK],
            sel2: vec![0u32; TASK_BLOCK], tags: vec![0u8; TASK_BLOCK],
            sv: Ghost(sv), ps: Ghost(ps) };
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
        assert forall|u: int| 0 <= u < nt implies acc_ok(#[trigger] outs0[u],
            tot(sv, ps, split_at(nl as int, nt as int, u), split_at(nl as int, nt as int, u + 1))) by {
            assert(tasks0[u].post(outs0[u]));
        }
        lemma_split(nl as int, nt as int, 0);
        lemma_tot_empty(sv, ps, 0);
    }
    let mut acc = acc_new();
    let mut t: usize = 0;
    while t < nt
        invariant
            2 <= nt, t <= nt, outs@ == outs0, outs0.len() == nt, nl == c.line.nl,
            forall|u: int| 0 <= u < nt ==> acc_ok(#[trigger] outs0[u],
                tot(sv, ps, split_at(nl as int, nt as int, u), split_at(nl as int, nt as int, u + 1))),
            acc_ok(acc, tot(sv, ps, 0, split_at(nl as int, nt as int, t as int))),
        decreases nt - t,
    {
        let ghost (a, b) = (split_at(nl as int, nt as int, t as int), split_at(nl as int, nt as int, t + 1));
        proof {
            lemma_split(nl as int, nt as int, t as int);
            lemma_tot_bounds(sv, ps, 0, b);
            lemma_tot_split(sv, ps, 0, a, b);
        }
        acc = acc_merge(acc, outs[t], Ghost(tot(sv, ps, 0, a)), Ghost(tot(sv, ps, a, b)));
        t = t + 1;
    }
    proof { lemma_split(nl as int, nt as int, (nt - 1) as int); }
    Ok(acc)
}

} // verus!
