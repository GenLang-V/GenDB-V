//! Running a batch of worker tasks either on the calling thread, one after another (a serial path: no thread is
//! spawned, for a call allowed one worker), or one thread per task (`fork_join`); either way every output meets its
//! task's `post`.
use vstd::prelude::*;
use crate::gendb_entry::parallel::{fork_join, Dispatch, WorkerTask, MAX_WORKERS};
use crate::gendb_entry::runtime::WorkerFailure;

verus! {

/// Run `tasks` (serially on the calling thread when `serial`), outputs in task order.
pub fn run_tasks<T: WorkerTask>(dispatch: &mut Dispatch, tasks: Vec<T>, serial: bool)
    -> (r: Result<Vec<T::Output>, WorkerFailure>)
    requires
        serial || tasks.len() <= MAX_WORKERS,
        forall|i: int| 0 <= i < tasks.len() ==> #[trigger] tasks@[i].pre(),
    ensures
        r matches Ok(outs) ==> outs.len() == tasks.len()
            && forall|i: int| 0 <= i < tasks.len() ==> #[trigger] tasks@[i].post(outs@[i]),
{
    if !serial {
        return fork_join(dispatch, tasks);
    }
    let ghost orig = tasks@;
    let mut tasks = tasks;
    let mut outs: Vec<T::Output> = Vec::new();
    proof {
        assert(tasks@ =~= orig.subrange(0, orig.len() as int));
    }
    while tasks.len() > 0
        invariant
            outs@.len() <= orig.len(),
            tasks@ == orig.subrange(outs@.len() as int, orig.len() as int),
            forall|i: int| 0 <= i < orig.len() ==> #[trigger] orig[i].pre(),
            forall|i: int| 0 <= i < outs@.len() ==> #[trigger] orig[i].post(outs@[i]),
        decreases tasks.len(),
    {
        let t = tasks.remove(0);
        let ghost i = outs@.len() as int;
        proof {
            assert(t == orig[i]);
        }
        let o = t.run();
        outs.push(o);
        proof {
            assert(tasks@ =~= orig.subrange(outs@.len() as int, orig.len() as int));
        }
    }
    Ok(outs)
}

} // verus!
