//! The lineitem pass over all rows: one `ScanTask` per even range of rows (`parts::split_at`), joined by
//! `fork_join` and merged in range order; with one worker (or few rows) the whole table is scanned on the calling
//! thread.
use vstd::prelude::*;
use std::sync::Arc;
use crate::gendb_entry::stores::StoresView;
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;
use crate::agent::tables::*;
use crate::agent::line::*;
use crate::agent::bounds::*;
use crate::agent::parts::{split_at, lemma_split};
use crate::agent::scan::*;

verus! {

/// Rows per task below which the scan stays on the calling thread.
pub const MIN_TASK_ROWS: usize = 1_048_576;

/// The totals of all lineitem rows.
pub fn line_pass(c: ScanCols, x: Window, bits: Arc<Vec<u64>>, pos: bool, workers: usize, dispatch: &mut Dispatch,
    Ghost(sv): Ghost<StoresView>) -> (r: Result<Acc, WorkerFailure>)
    requires scan_inputs_ok(c, x, (*bits)@, pos, sv), 1 <= workers <= MAX_WORKERS,
    ensures r matches Ok(a) ==> acc_ok(a, tot(sv, win_of(x), 0, n_l(sv) as int)),
{
    let nl = c.nl;
    let ghost w = win_of(x);
    let mut nt = workers;
    if nl / MIN_TASK_ROWS < nt {
        nt = nl / MIN_TASK_ROWS;
    }
    if nt <= 1 {
        let mut sel: Vec<u32> = vec![0u32; BLOCK];
        let mut pkb: Vec<i64> = vec![0i64; BLOCK];
        let mut vb: Vec<i128> = vec![0i128; BLOCK];
        let acc = scan_range(&c, &x, &*bits, pos, 0, nl, &mut sel, &mut pkb, &mut vb, Ghost(sv));
        return Ok(acc);
    }
    let q = nl / nt;
    let rm = nl % nt;
    let mut tasks: Vec<ScanTask> = Vec::new();
    let mut lo: usize = 0;
    let mut k: usize = 0;
    while k < nt
        invariant
            scan_inputs_ok(c, x, (*bits)@, pos, sv), 2 <= nt <= MAX_WORKERS, k <= nt, nl == c.nl,
            q == nl / nt, rm == nl % nt,
            tasks@.len() == k,
            lo == split_at(nl as int, nt as int, k as int),
            forall|t: int| 0 <= t < k ==> (#[trigger] tasks@[t]).pre()
                && tasks@[t].sv@ == sv && tasks@[t].win == x
                && tasks@[t].lo == split_at(nl as int, nt as int, t)
                && tasks@[t].hi == split_at(nl as int, nt as int, t + 1),
        decreases nt - k,
    {
        proof { lemma_split(nl as int, nt as int, k as int); }
        let hi = lo + q + if k < rm { 1 } else { 0 };
        let task = ScanTask { cols: c, win: x, bits: bits.clone(), pos, lo, hi, sel: vec![0u32; BLOCK], pkb: vec![0i64; BLOCK], vb: vec![0i128; BLOCK], sv: Ghost(sv) };
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
            tot(sv, w, split_at(nl as int, nt as int, u), split_at(nl as int, nt as int, u + 1))) by {
            assert(tasks0[u].post(outs0[u]));
        }
        lemma_split(nl as int, nt as int, 0);
        lemma_tot_empty(sv, w, 0);
    }
    let mut acc = acc_new();
    let mut t: usize = 0;
    while t < nt
        invariant
            2 <= nt, t <= nt, outs@ == outs0, outs0.len() == nt, nl == c.nl,
            w == win_of(x),
            forall|u: int| 0 <= u < nt ==> acc_ok(#[trigger] outs0[u],
                tot(sv, w, split_at(nl as int, nt as int, u), split_at(nl as int, nt as int, u + 1))),
            acc_ok(acc, tot(sv, w, 0, split_at(nl as int, nt as int, t as int))),
        decreases nt - t,
    {
        let ghost (a, b) = (split_at(nl as int, nt as int, t as int), split_at(nl as int, nt as int, t + 1));
        proof {
            lemma_split(nl as int, nt as int, t as int);
            lemma_tot_bounds(sv, w, 0, b);
            lemma_tot_split(sv, w, 0, a, b);
        }
        acc = acc_merge(acc, outs[t], Ghost(tot(sv, w, 0, a)), Ghost(tot(sv, w, a, b)));
        t = t + 1;
    }
    proof { lemma_split(nl as int, nt as int, (nt - 1) as int); }
    Ok(acc)
}

} // verus!
