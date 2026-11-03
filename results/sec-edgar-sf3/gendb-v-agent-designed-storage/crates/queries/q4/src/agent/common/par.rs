//! Running a list of worker tasks within a thread budget: one `fork_join` when the tasks fit the budget (at most
//! `workers` threads), otherwise every task in order on the calling thread (no extra thread).
use vstd::prelude::*;
use crate::gendb_entry::parallel::{Dispatch, WorkerTask, fork_join, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;

verus! {

pub fn run_tasks<T: WorkerTask>(dispatch: &mut Dispatch, workers: usize, tasks: Vec<T>) -> (r: Result<Vec<T::Output>, WorkerFailure>)
    requires
        workers <= MAX_WORKERS,
        forall|i: int| 0 <= i < tasks@.len() ==> #[trigger] tasks@[i].pre(),
    ensures
        r matches Ok(outs) ==> outs@.len() == tasks@.len()
            && forall|i: int| 0 <= i < tasks@.len() ==> #[trigger] tasks@[i].post(outs@[i]),
{
    if tasks.len() > 1 && tasks.len() <= workers {
        return fork_join(dispatch, tasks);
    }
    let ghost orig = tasks@;
    let n = tasks.len();
    let mut tasks = tasks;
    // Pop from the back, run, and restore task order at the end.
    let mut rev: Vec<T::Output> = Vec::new();
    while tasks.len() > 0
        invariant
            tasks@ == orig.subrange(0, tasks@.len() as int),
            rev@.len() + tasks@.len() == n, n == orig.len(),
            forall|i: int| 0 <= i < orig.len() ==> #[trigger] orig[i].pre(),
            forall|k: int| 0 <= k < rev@.len() ==> #[trigger] orig[n - 1 - k].post(rev@[k]),
        decreases tasks@.len(),
    {
        let t = tasks.pop().unwrap();
        proof { assert(t == orig[tasks@.len() as int]); }
        let o = t.run();
        rev.push(o);
    }
    let mut outs: Vec<T::Output> = Vec::new();
    while rev.len() > 0
        invariant
            rev@.len() + outs@.len() == n, n == orig.len(),
            forall|k: int| 0 <= k < rev@.len() ==> #[trigger] orig[n - 1 - k].post(rev@[k]),
            forall|i: int| 0 <= i < outs@.len() ==> #[trigger] orig[i].post(outs@[i]),
        decreases rev@.len(),
    {
        let o = rev.pop().unwrap();
        proof { assert(orig[n - 1 - rev@.len()].post(o)); }
        outs.push(o);
    }
    Ok(outs)
}

} // verus!
