// FRAMEWORK FILE: verified fork/join for GenDB Verus candidates (`verification/obligations/gendb_entry/parallel.rs`).
//
// Copied unchanged into every candidate crate as `crate::gendb_entry::parallel`. Authors cannot
// edit it. It is checked by Verus with `--no-cheating` together with the candidate and contains
// no `assume`, `admit` or `external_body`.
//
// Agent code cannot name vstd/std threads (refusal list rule `direct_thread`; Verus rejects
// `std::thread`), so its threads come from `fork_join`. The author chooses the partition (the list
// of tasks and what each covers) and the merge (code over the returned outputs), and proves both;
// nothing here assumes coverage or merge. `fork_join` spawns one vstd thread per task (at most
// MAX_WORKERS per call) and joins every handle it created before it returns, on every path (a
// failed join still joins the rest). That is a property of each call, not a global thread bound:
// agent code may also call the public entry functions (non-recursively; Verus refuses cycles),
// which run with their own `Dispatch`.
//
// The `workers` argument of a query or build is the maximum number of threads available to that call, not a
// requirement: a call may use fewer tasks per `fork_join`, or none (a serial path), whenever that is faster.
//
// Worker bodies are `no_unwind`: `WorkerTask::run` carries the signature, every implementation
// inherits it, and Verus refuses any call in it that may unwind (allocation such as `Vec::new` /
// `Vec::with_capacity`, thread spawning, the entry functions, helpers not themselves `no_unwind`).
// Outputs: allocate each task's output on the calling thread (`work::filled`, `work::TaskBuffer::new`), move it
// into the task and fill it in `run` with `work::put` / `v[i] = x` / `TaskBuffer::push` (all `no_unwind`; vstd's
// `Vec::set` is not). The thread body is exactly `task.run()`. So a failed join (`WorkerFailure`) cannot come from
// checked code: it means a trusted component broke (std/vstd thread/join semantics), not a
// query outcome that author code can choose.
// Trusted: vstd `spawn`/`join` specs (std threads; join returns `Err` only if the thread
// unwound; join happens-before; thread-creation failure aborts the process) and fair scheduling
// for termination of `join`.
use vstd::prelude::*;
use vstd::thread::{spawn, JoinHandle};
use super::runtime::{join_worker, WorkerFailure};

verus! {

/// Largest task count of one `fork_join` call (= the host's worker bound `gendb_runtime::abi::MAX_WORKERS`).
pub const MAX_WORKERS: usize = 64;

/// One unit of work that `fork_join` runs on its own thread. Implemented by the author.
pub trait WorkerTask: Sized + Send + 'static {
    type Output: Send + 'static;

    /// What `run` needs (for example: its row range is inside the input).
    spec fn pre(&self) -> bool;

    /// What `run` guarantees about its output (for example: the partial SUM of its row range).
    spec fn post(&self, out: Self::Output) -> bool;

    /// The row range `[lo, hi)` this task covers, reported as dispatch evidence only. No proof
    /// uses it; coverage is proved through `pre`/`post`.
    fn declared_rows(&self) -> (u64, u64)
        no_unwind;

    /// The worker body. `no_unwind` (inherited by every implementation): it cannot allocate,
    /// spawn or otherwise call anything that may unwind.
    fn run(self) -> (out: Self::Output)
        requires self.pre(),
        ensures self.post(out),
        no_unwind;
}

/// Dispatch evidence of one entry call: worker threads spawned and joined by `fork_join` calls
/// that received this value, and their declared row ranges. Fields are private and the constructor
/// is visible only inside `crate::gendb_entry`, so agent code cannot create or reset one.
/// Descriptive evidence only; not a proof input.
pub struct Dispatch {
    spawned: u64,
    joined: u64,
    ranges: Vec<(u64, u64)>,
}

impl Dispatch {
    pub(super) fn new() -> Dispatch {
        Dispatch { spawned: 0, joined: 0, ranges: Vec::new() }
    }

    pub(super) fn into_parts(self) -> (u64, u64, Vec<(u64, u64)>) {
        (self.spawned, self.joined, self.ranges)
    }
}

fn saturating_add(a: u64, b: u64) -> (r: u64)
    ensures r == if a + b <= u64::MAX { (a + b) as u64 } else { u64::MAX },
{
    if a <= u64::MAX - b { a + b } else { u64::MAX }
}

/// Verified pass-through of vstd `spawn`: the task's postcondition reaches the joiner.
fn spawn_worker<T: WorkerTask>(task: T) -> (h: JoinHandle<T::Output>)
    requires task.pre(),
    ensures forall|ret: T::Output| #[trigger] h.predicate(ret) ==> task.post(ret),
{
    spawn(move || -> (out: T::Output)
        requires task.pre(),
        ensures task.post(out),
    { task.run() })
}

/// Run every task on its own thread and join them all. `Ok` carries each task's output in task
/// order with its `post`; `Err` carries the token of a real failed join, created only by
/// `crate::gendb_entry::runtime::join_worker`. Because every thread body is a `no_unwind` `run`, `Err` is
/// possible only if the trusted thread/join semantics fail. `fork_join` itself may unwind (vstd
/// `spawn`, `Vec` growth have no `no_unwind` spec); an unwind on the calling thread aborts the
/// process in the shim and produces no status.
pub fn fork_join<T: WorkerTask>(dispatch: &mut Dispatch, tasks: Vec<T>) -> (r: Result<Vec<T::Output>, WorkerFailure>)
    requires
        tasks.len() <= MAX_WORKERS,
        forall|i: int| 0 <= i < tasks.len() ==> #[trigger] tasks@[i].pre(),
    ensures
        r matches Ok(outs) ==> outs.len() == tasks.len()
            && forall|i: int| 0 <= i < tasks.len() ==> #[trigger] tasks@[i].post(outs@[i]),
{
    let ghost orig = tasks@;
    let n = tasks.len();
    // Dispatch evidence in task order.
    let mut i: usize = 0;
    while i < n
        invariant n == tasks.len(), i <= n,
        decreases n - i,
    {
        let rows = tasks[i].declared_rows();
        dispatch.ranges.push(rows);
        i = i + 1;
    }
    let mut tasks = tasks;
    // Spawn from the back: handles[k] runs orig[n - 1 - k].
    let mut handles: Vec<JoinHandle<T::Output>> = Vec::new();
    let mut spawned: usize = 0;
    while tasks.len() > 0
        invariant
            n == orig.len(),
            n <= MAX_WORKERS,
            spawned == handles.len(),
            tasks@ == orig.subrange(0, tasks.len() as int),
            handles.len() + tasks.len() == n,
            forall|i: int| 0 <= i < orig.len() ==> #[trigger] orig[i].pre(),
            forall|k: int, ret: T::Output| 0 <= k < handles.len() && #[trigger] handles@[k].predicate(ret)
                ==> orig[n - 1 - k].post(ret),
        decreases tasks.len(),
    {
        let task = tasks.pop().unwrap();
        let h = spawn_worker(task);
        handles.push(h);
        spawned = spawned + 1;
    }
    // Join from the back of `handles`, i.e. in task order; every handle is joined.
    let mut outs: Vec<T::Output> = Vec::new();
    let mut failure: Option<WorkerFailure> = None;
    let mut joined: usize = 0;
    while handles.len() > 0
        invariant
            n == orig.len(),
            spawned == n,
            handles.len() + joined == n,
            failure is None ==> outs.len() == joined,
            failure is None ==> forall|i: int| 0 <= i < outs.len() ==> #[trigger] orig[i].post(outs@[i]),
            forall|k: int, ret: T::Output| 0 <= k < handles.len() && #[trigger] handles@[k].predicate(ret)
                ==> orig[n - 1 - k].post(ret),
        decreases handles.len(),
    {
        let h = handles.pop().unwrap();
        match join_worker(h) {
            Ok(v) => {
                if failure.is_none() {
                    outs.push(v);
                }
            },
            Err(e) => {
                failure = Some(e);
            },
        }
        joined = joined + 1;
    }
    assert(spawned == n && joined == n && handles.len() == 0);
    dispatch.spawned = saturating_add(dispatch.spawned, spawned as u64);
    dispatch.joined = saturating_add(dispatch.joined, joined as u64);
    match failure {
        Some(e) => Err(e),
        None => Ok(outs),
    }
}

} // verus!
