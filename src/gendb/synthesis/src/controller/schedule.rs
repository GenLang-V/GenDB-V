//! Several author sessions with bounded concurrency. Scheduling is ordinary GenDB code: each session owns its
//! directory, ledger, author and role; roles may share retained immutable inputs. A failed session leaves a
//! resumable framework error record and does not stop the others. A session that names a closed source session runs
//! as a reselection without an author (`controller::reselect`) under the same records. The sessions of `gendb import`
//! (`controller::import`) run on the same pool ([`in_parallel`]) with the same records ([`record_framework_error`],
//! [`record_results`]).

use super::author::AuthorTransport;
use super::records;
use super::reselect::reselect;
use super::role::SynthesisRole;
use super::run::{RunRequest, run};
use super::ControllerError;
use serde_json::{Value, json};
use std::path::{Path, PathBuf};

/// One session to run.
pub struct ScheduledSession<A, R> {
    /// The session's run directory.
    pub directory: PathBuf,
    pub request: RunRequest,
    pub author: A,
    pub role: R,
    /// A closed session to reselect from instead of calling the author (`controller::reselect`); `None`: the author
    /// session (`controller::run`).
    pub reselect_from: Option<PathBuf>,
    /// Called once with the session's summary when it closes without a framework error (for example, to write the
    /// readable output home); its own failures are its to record.
    pub on_close: Option<CloseHook>,
}

/// What runs after a session closes (see [`ScheduledSession::on_close`]).
pub type CloseHook = Box<dyn FnOnce(&Value) + Send>;

/// Run `sessions` in order, at most `max_concurrent` at a time (a new session starts as soon as one finishes), each on
/// its own thread with its own single-threaded async runtime. Returns one result per session, in order: its summary,
/// or a `framework_error` record. The results are also written to `summary_dir` as a new
/// `workload-summary[-N].json`, with `workload-summary-latest.json` naming it.
pub fn run_sessions<A: AuthorTransport + Send, R: SynthesisRole + Send>(
    sessions: Vec<ScheduledSession<A, R>>,
    summary_dir: &Path,
    max_concurrent: usize,
) -> Result<Vec<Value>, ControllerError> {
    let results = in_parallel(sessions, max_concurrent, |session| run_one(session).unwrap_or_else(|error| json!({"status":"framework_error","error":error})))?;
    record_results(summary_dir, &results)?;
    Ok(results)
}

/// Run `work` over `items` in order, at most `max_concurrent` at a time (a new item starts as soon as one finishes),
/// each on a thread of its own. One result per item, in order; a panic is the item's `framework_error` result.
pub(super) fn in_parallel<S: Send>(items: Vec<S>, max_concurrent: usize, work: impl Fn(S) -> Value + Sync) -> Result<Vec<Value>, ControllerError> {
    if max_concurrent == 0 {
        return Err(ControllerError::InvalidRequest("session concurrency must be positive".into()));
    }
    let count = items.len();
    let pending = std::sync::Mutex::new(items.into_iter().enumerate());
    let finished = std::sync::Mutex::new(vec![Value::Null; count]);
    std::thread::scope(|scope| {
        for _ in 0..max_concurrent.min(count) {
            scope.spawn(|| loop {
                let next = pending.lock().map(|mut queue| queue.next()).ok().flatten();
                let Some((index, item)) = next else { break };
                let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| work(item)))
                    .unwrap_or_else(|_| json!({"status":"framework_error","error":"session controller panicked"}));
                if let Ok(mut finished) = finished.lock() {
                    finished[index] = result;
                }
            });
        }
    });
    finished.into_inner().map_err(|_| ControllerError::Session("a session thread poisoned the result list".into()))
}

/// Record the sessions' `results` in `summary_dir` as a new `workload-summary[-N].json`, with
/// `workload-summary-latest.json` naming it.
pub(super) fn record_results(summary_dir: &Path, results: &[Value]) -> Result<(), ControllerError> {
    records::create_dir(summary_dir)?;
    let record = records::next_free_record(summary_dir, "workload-summary.json", "workload-summary");
    records::write_new_json(&record, &results)?;
    let name = record.file_name().and_then(|name| name.to_str()).unwrap_or_default().to_string();
    records::write_json_atomic(&summary_dir.join("workload-summary-latest.json"), &json!({"format_version":1,"record":name}))?;
    Ok(())
}

/// One session on the current thread. A controller error is recorded as a new resumable framework error record in
/// the session directory; the session, calls, limits and frozen evidence stay as they are.
fn run_one<A: AuthorTransport, R: SynthesisRole>(mut session: ScheduledSession<A, R>) -> Result<Value, String> {
    let result = match tokio::runtime::Builder::new_current_thread().enable_all().build() {
        Ok(runtime) => {
            let ScheduledSession { directory, request, author, role, reselect_from, .. } = &mut session;
            let session_run = async {
                match reselect_from {
                    Some(source) => reselect(request, directory, source, author, role).await,
                    None => run(request, directory, author, role).await,
                }
            };
            runtime.block_on(session_run).map_err(|error| error.to_string())
        }
        Err(error) => Err(error.to_string()),
    };
    let error = match result {
        Ok(summary) => {
            if let Some(hook) = session.on_close.take() {
                hook(&summary);
            }
            return Ok(summary);
        }
        Err(error) => error,
    };
    record_framework_error(&session.directory, error)
}

/// A session controller's `error`, recorded as a new resumable framework error record in the session `directory`; the
/// session, calls, limits and frozen evidence stay as they are. Returns the record.
pub(super) fn record_framework_error(directory: &Path, error: String) -> Result<Value, String> {
    records::create_dir(directory).map_err(|e| e.to_string())?;
    let stamp = format!("framework-error-{}-{}", records::now_unix_ms(), std::process::id());
    let path = records::next_free_record(directory, &format!("{stamp}-0.json"), &stamp);
    let record = json!({"status":"framework_error","error":error,"resumable":true,
        "error_record":path,"ledger":directory.join("ledger.json"),
        "scope":"session controller failed; existing session, calls, limits and frozen evidence retained"});
    records::write_new_json(&path, &record).map_err(|e| e.to_string())?;
    Ok(record)
}
