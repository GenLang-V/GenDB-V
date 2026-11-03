//! Parent side: run one request in a fresh child process and read its result. A limited engine job's child that the
//! watchdog stopped, or that died by a signal, is read as an unfinished result ([`spawn`]). A caller done with the full
//! answers of a result it read may store it again with every answer over a bound cut ([`store_bounded_result`]).
//!
//! The child runs under `timeout` as the leader of its own process group, owned by the controller's stop
//! (`process_stop`): the user's stop sends that group SIGTERM, and the kernel does when the controller dies; a child
//! ended by the user's stop is never read as a result (the waiting thread parks).

use super::error::WorkerError;
use super::protocol::{UNFINISHED_EXIT_CODE, Unfinished, WorkerRequest, WorkerResult};
use super::stored_answer::{AnswerBound, bounded_observation};
use gendb_storage::io::STORAGE_RESERVE_REFUSAL;
use serde::{Deserialize, Serialize};
use std::os::unix::process::CommandExt;
use std::path::Path;

/// The subcommand word of the worker executable: `<executable> worker REQUEST RESULT` (`gendb worker`, see
/// [`super::worker_main`]).
pub const WORKER_SUBCOMMAND: &str = "worker";

/// Evidence file names inside the run's work directory (unchanged from the earlier GenDB version).
const REQUEST_FILE: &str = "verus-run.request.json";
const RESULT_FILE: &str = "verus-run.result.json";
const STDERR_FILE: &str = "verus-run.stderr";

/// How a child ended without a result, exactly as the OS reported it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ChildFailure {
    pub exit_code: Option<i32>,
    pub signal: Option<i32>,
    pub stderr: String,
}

impl ChildFailure {
    /// The caller's timeout ended the child: `timeout` exits 124 after SIGTERM, 137 after the SIGKILL that follows
    /// the 2-second grace period.
    pub fn timed_out(&self) -> bool {
        matches!(self.exit_code, Some(124 | 137))
    }

    /// The child refused a write at the storage free-space reserve (`gendb_storage::io::PartFilesWriter`): it exited
    /// 1 with that refusal as its last stderr line, as [`super::worker_main`] reports a refusal.
    pub fn stopped_at_storage_reserve(&self) -> bool {
        self.exit_code == Some(1)
            && self.stderr.trim_end().lines().last().is_some_and(|line| line.starts_with(STORAGE_RESERVE_REFUSAL))
    }
}

/// Write `request` into the fresh evidence directory `work`, run `<worker> worker REQUEST RESULT` there under
/// `timeout --kill-after=2s <timeout_seconds>s` (the caller's declared bound; `TMPDIR` = `work`), keep its stderr, and
/// read the result. A child that exits unsuccessfully is [`WorkerError::ChildFailed`]; request, result and stderr stay
/// in `work` as evidence.
///
/// A limited request ([`WorkerRequest::is_limited`]) has two more outcomes, both `Ok` with
/// [`WorkerResult::unfinished`] set: exit status [`UNFINISHED_EXIT_CODE`] with the watchdog's result (the calls before
/// the stopped one and the stopped call); and a child ended by a signal ([`Unfinished::ChildFailure`]: no observation
/// survives). The caller's bound (`timeout`'s exit 124 or 137) stays a [`WorkerError::ChildFailed`] (the framework's
/// backstop, never a cell result), as do refusals and other exit statuses.
pub fn spawn(
    worker: &Path,
    work: &Path,
    request: &WorkerRequest,
    timeout_seconds: u64,
) -> Result<WorkerResult, WorkerError> {
    use std::os::unix::process::ExitStatusExt;
    std::fs::create_dir_all(work).map_err(WorkerError::file(work))?;
    let request_path = work.join(REQUEST_FILE);
    let result_path = work.join(RESULT_FILE);
    let bytes = serde_json::to_vec_pretty(request).map_err(WorkerError::json(&request_path))?;
    std::fs::write(&request_path, bytes).map_err(WorkerError::file(&request_path))?;
    crate::process_stop::park_if_stopping();
    let mut command = std::process::Command::new("timeout");
    command
        .args(["--kill-after=2s", &format!("{timeout_seconds}s")])
        .arg(worker)
        .arg(WORKER_SUBCOMMAND)
        .arg(&request_path)
        .arg(&result_path)
        .env("TMPDIR", work)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .process_group(0);
    crate::process_stop::die_with_controller(&mut command, libc::SIGTERM);
    let child = command.spawn().map_err(WorkerError::file(worker))?;
    let owned = crate::process_stop::own_group(child.id(), libc::SIGTERM, "worker child (timeout's process group)");
    let output = child.wait_with_output();
    drop(owned);
    crate::process_stop::park_if_stopping();
    let output = output.map_err(WorkerError::file(worker))?;
    let stderr_path = work.join(STDERR_FILE);
    std::fs::write(&stderr_path, &output.stderr).map_err(WorkerError::file(&stderr_path))?;
    let failure = ChildFailure {
        exit_code: output.status.code(),
        signal: output.status.signal(),
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
    };
    let stopped = request.is_limited() && failure.exit_code == Some(i32::from(UNFINISHED_EXIT_CODE));
    if request.is_limited() && failure.signal.is_some() {
        return Ok(child_failure_result(request, failure));
    }
    if !output.status.success() && !stopped {
        return Err(WorkerError::ChildFailed(failure));
    }
    let bytes = std::fs::read(&result_path).map_err(WorkerError::file(&result_path))?;
    let result: WorkerResult = serde_json::from_slice(&bytes).map_err(WorkerError::json(&result_path))?;
    if stopped != result.unfinished.is_some() {
        return Err(WorkerError::Request("a stopped child writes an unfinished result, and only a stopped child does"));
    }
    Ok(result)
}

/// Store `result`, read from the child of the evidence directory `work`, again in its result file with every rows answer
/// over `bound` stored as its summary and first rows (`super::stored_answer`), when it has one; returns how many answers
/// were cut (0: the file is left as the child wrote it). For a caller that has finished with the full answers (it
/// compared them): from here on the file is evidence only. Written to a staged file, then renamed over the result.
pub fn store_bounded_result(work: &Path, result: &WorkerResult, bound: AnswerBound) -> Result<usize, WorkerError> {
    let mut cut = 0;
    let observations = result
        .observations
        .iter()
        .map(|observation| match bounded_observation(observation, bound) {
            Some(bounded) => {
                cut += 1;
                bounded
            }
            None => observation.clone(),
        })
        .collect();
    if cut == 0 {
        return Ok(0);
    }
    let bounded = WorkerResult {
        abi: result.abi,
        purpose: result.purpose,
        library: result.library.clone(),
        input_columns: result.input_columns,
        column_rows: result.column_rows.clone(),
        bindings: result.bindings.clone(),
        observations,
        parts: result.parts.clone(),
        storage_uses: result.storage_uses.clone(),
        echoes: result.echoes.clone(),
        unfinished: result.unfinished.clone(),
    };
    let (result_path, staged) = (work.join(RESULT_FILE), work.join(format!("{RESULT_FILE}.bounded")));
    let bytes = serde_json::to_vec_pretty(&bounded).map_err(WorkerError::json(&staged))?;
    std::fs::write(&staged, bytes).map_err(WorkerError::file(&staged))?;
    std::fs::rename(&staged, &result_path).map_err(WorkerError::file(&result_path))?;
    Ok(cut)
}

/// The result of a limited child that died by a signal before writing one: nothing observed, the failure as reported.
fn child_failure_result(request: &WorkerRequest, failure: ChildFailure) -> WorkerResult {
    WorkerResult {
        abi: request.abi,
        purpose: request.purpose,
        library: request.library.clone(),
        input_columns: 0,
        column_rows: vec![],
        bindings: request.bindings.clone(),
        observations: vec![],
        parts: None,
        storage_uses: vec![],
        echoes: vec![],
        unfinished: Some(Unfinished::ChildFailure(failure)),
    }
}
