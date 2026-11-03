//! How serving runs a stored library: one fresh worker child per served call, so the library and its mapped parts
//! are retained only by that child (see [`crate::worker`]).

use super::error::ServeError;
use crate::abi::{CallOutcome, StatementArgument};
use crate::worker::{CallObservation, MappedStorageUse, StorageUseInput, WorkerRequest, spawn};
use gendb_storage::io::PartAccess;
use std::cell::RefCell;
use std::path::{Path, PathBuf};

/// Runs query calls of admitted libraries in worker children. Every call gets a fresh evidence directory
/// `<work>/serve-<workers>-<n>`; the child runs the binding `repetitions` times (for example 1 warm + 3 hot) and the
/// last call is the served one. `timeout_seconds` and `range_capacity` are the caller's declared contracts.
pub struct WorkerExecutor {
    worker: PathBuf,
    work: PathBuf,
    timeout_seconds: u64,
    range_capacity: u64,
    repetitions: u32,
    calls: RefCell<Vec<CallOutcome>>,
}

impl WorkerExecutor {
    /// `worker`: the executable run as `<worker> worker REQUEST RESULT`.
    pub fn new(worker: &Path, work: &Path, timeout_seconds: u64, range_capacity: u64, repetitions: u32) -> Self {
        Self {
            worker: worker.to_owned(),
            work: work.to_owned(),
            timeout_seconds,
            range_capacity,
            repetitions,
            calls: RefCell::default(),
        }
    }

    /// Run the query entry of `library` over the stored `parts` at `arguments` and `workers` in one child; returns
    /// the last call.
    pub fn query(
        &self,
        library: &Path,
        parts: &Path,
        arguments: &[StatementArgument],
        workers: u32,
    ) -> Result<CallOutcome, ServeError> {
        let request = WorkerRequest::for_query(
            library,
            Some(parts),
            vec![arguments.to_vec()],
            vec![workers],
            self.repetitions,
            self.range_capacity,
        );
        let result = spawn(&self.worker, &self.fresh_evidence_directory(workers), &request, self.timeout_seconds)?;
        let calls: Vec<CallOutcome> = result.observations.into_iter().map(|observation| observation.outcome).collect();
        let served = calls.last().cloned().ok_or(ServeError::NoCall)?;
        *self.calls.borrow_mut() = calls;
        Ok(served)
    }

    /// Run the v4 query entry of `library` over its storage uses `uses` (declared use order, mapped with `access`) at
    /// `arguments` and `workers` in one child; returns the last call with its per-use request counters and process
    /// I/O, and the stored bytes of every use.
    pub fn query_storages(
        &self,
        library: &Path,
        uses: &[StorageUseInput],
        access: PartAccess,
        arguments: &[StatementArgument],
        workers: u32,
    ) -> Result<StorageQueryCall, ServeError> {
        let request = WorkerRequest::for_storage_query(
            library,
            uses.to_vec(),
            access,
            vec![arguments.to_vec()],
            vec![workers],
            self.repetitions,
            self.range_capacity,
        );
        let result = spawn(&self.worker, &self.fresh_evidence_directory(workers), &request, self.timeout_seconds)?;
        let served = result.observations.last().cloned().ok_or(ServeError::NoCall)?;
        *self.calls.borrow_mut() = result.observations.into_iter().map(|observation| observation.outcome).collect();
        Ok(StorageQueryCall { served, storage_uses: result.storage_uses })
    }

    /// Every call of the latest [`Self::query`] or [`Self::query_storages`], in order (repetition 0 first).
    pub fn calls(&self) -> Vec<CallOutcome> {
        self.calls.borrow().clone()
    }

    fn fresh_evidence_directory(&self, workers: u32) -> PathBuf {
        (0..)
            .map(|ordinal| self.work.join(format!("serve-{workers}-{ordinal}")))
            .find(|directory| !directory.exists())
            .expect("an unbounded ordinal range always has an unused name")
    }
}

/// The served call of a v4 query ([`WorkerExecutor::query_storages`]): the last call (outcome with per-use request
/// counters, readable answer, process I/O) and what every storage use mapped (parts, stored bytes).
#[derive(Clone, Debug)]
pub struct StorageQueryCall {
    pub served: CallObservation,
    pub storage_uses: Vec<MappedStorageUse>,
}
