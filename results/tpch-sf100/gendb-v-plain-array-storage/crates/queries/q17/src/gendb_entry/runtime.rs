// FRAMEWORK FILE: runtime outcome types of GenDB Verus candidates (`verification/obligations/gendb_entry/runtime.rs`).
//
// Copied unchanged into every candidate crate as `crate::gendb_entry::runtime`. Authors cannot edit
// it. It is checked by Verus with `--no-cheating` together with the candidate and contains no
// `assume`, `admit` or `external_body`.
//
// `WorkerFailure` has a private field, so only `join_worker` below can create one; the fixed
// `parallel::fork_join` calls it on the join of each `no_unwind` worker. Author code therefore
// cannot produce `QueryError::WorkerFailed` except by forwarding a token from `fork_join`.
use vstd::prelude::*;
use vstd::thread::JoinHandle;

verus! {

/// Query and build errors. `InvalidInput`: the input is outside the declared column domain.
/// `Malformed`: a data representation does not decode. `WorkerFailed`: a joined worker thread failed;
/// the token has a private field, so only framework code in this module can create it.
pub enum QueryError { InvalidInput, Malformed, WorkerFailed(WorkerFailure) }

pub struct WorkerFailure { _private: () }

/// Verified pass-through of vstd `JoinHandle::join`: the only constructor of `WorkerFailure`.
/// `Ok` carries the joined closure's postcondition; `Err` means the joined thread failed.
pub fn join_worker<T>(h: JoinHandle<T>) -> (r: Result<T, WorkerFailure>)
    ensures r matches Ok(v) ==> h.predicate(v),
{
    match h.join() {
        Ok(v) => Ok(v),
        Err(_) => Err(WorkerFailure { _private: () }),
    }
}

} // verus!
