//! The author sessions of a workload run: the workload storage session (phase 4, when the request asks for it) and
//! then every ready query's session (phase 5); a query that names `reselect_from` runs its session as a reselection
//! without an author (`controller::reselect`), and one that names `continue_from` starts its author session from that
//! earlier session's admitted candidate (`RunRequest::continue_from`). Each role is retained on its own owner thread, which also answers the
//! author's local tools, and every session runs under the generic session loop (`controller::run`) through
//! `controller::schedule`. Session directories: `<run>/workload-storage/session` and `<run>/queries/query-NNNN`
//! (`controller::layout`).

use super::WorkloadError;
use super::authors::HostLeasedAuthor;
use super::lifecycle::{query_directory, storage_session_directory, storage_summary_directory};
use super::preparation::{PreparedData, PreparedQuery};
use crate::controller::author::AuthorTransport;
use crate::controller::hardware::observe_host;
use crate::controller::request::WorkloadRequest;
use crate::controller::run::RunRequest;
use crate::controller::schedule::{CloseHook, ScheduledSession, run_sessions};
use crate::controller::session::RetainedRole;
use crate::prompts::policy::{CORRECTNESS_OBJECTIVE, PERFORMANCE_OBJECTIVE, STORAGE_OBJECTIVE};
use crate::query::QuerySession;
use crate::query::role::{QueryAuthorRole, QueryRoleConfig};
use crate::tools::bench::{BenchConfig, Workbench};
use crate::workload::{StorageAuthorRole, StorageRoleConfig};
use gendb_frontend::parser::SqlParser;
use serde_json::{Value, json};
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// Directory under `TMPDIR` for the retained sessions' Unix sockets (a socket path must stay under 100 bytes, so the
/// run directory itself is usually too deep).
const SOCKET_SUBDIRECTORY: &str = "sockets";

/// The bench of a session over `statements`.
pub(super) fn bench(request: &WorkloadRequest, data: &PreparedData, statements: Vec<Arc<QuerySession>>, parser: &SqlParser) -> Workbench {
    let config = BenchConfig {
        library: request.library.clone(),
        locks: request.host_locks.clone(),
        parser: parser.clone(),
        live_bytes_allowance: request.data_allowance.as_ref().map(|allowance| allowance.live_bytes),
        storage_policy: request.storage_policy.clone(),
        asset_upkeep: None,
    };
    Workbench::new(config, data.capture.clone(), statements)
}

/// Run the workload storage session over every ready statement of `queries` with `author`, and return its summary
/// (or its framework error record).
pub fn run_storage_session<A: AuthorTransport + Send>(
    request: &WorkloadRequest,
    root: &Path,
    queries: &[PreparedQuery],
    data: &PreparedData,
    author: HostLeasedAuthor<A>,
    parser: &SqlParser,
) -> Result<Value, WorkloadError> {
    let storage = request.workload_storage.as_ref().ok_or_else(|| WorkloadError::invalid("the workload storage phase was not requested"))?;
    // `queries` is in request order, so each ready statement's objective is its request query's.
    let (statements, runtime_targets): (Vec<Arc<QuerySession>>, Vec<_>) = queries
        .iter()
        .zip(&request.queries)
        .filter_map(|(query, requested)| match query {
            PreparedQuery::Ready(session) => Some((session.clone(), requested.objective.runtime_targets().to_vec())),
            PreparedQuery::Refused(_) => None,
        })
        .unzip();
    let config = StorageRoleConfig { hardware: json!(request.hardware), observed_hardware: observe_host(), runtime_targets };
    let role = StorageAuthorRole::new(bench(request, data, statements.clone(), parser), config);
    let directory = storage_session_directory(root);
    let role = RetainedRole::start(role, &directory, &socket_directory()?)?;
    // Part of the session's ledger identity, so it stays the same across restarts.
    let task = json!({"role":"workload_storage","objective":STORAGE_OBJECTIVE,"statements":statements.iter().map(|s| &s.statement().sql).collect::<Vec<_>>(),
        "threads":request.hardware.threads});
    let run_request = RunRequest { format_version: 1, task, limits: storage.limits.clone(), continue_from: None };
    let library = request.library.clone();
    let on_close = output_hook(request, &directory, move |home, session| {
        crate::output::write_workload(home, &crate::output::WorkloadOutput { session, library: &library }).map(drop)
    });
    let session = ScheduledSession { directory, request: run_request, author, role, reselect_from: None, on_close };
    let mut completed = run_sessions(vec![session], &storage_summary_directory(root), 1)?;
    Ok(completed.pop().unwrap_or(Value::Null))
}

/// Run the author session of every ready query of `queries` (in request order; `authors[i]` is query `i`'s) and
/// return one outcome per query in request order: the session's summary, its framework error record, or the query's
/// refusal record.
pub fn run_query_sessions<A: AuthorTransport + Send>(
    request: &WorkloadRequest,
    root: &Path,
    queries: Vec<PreparedQuery>,
    data: &PreparedData,
    authors: Vec<HostLeasedAuthor<A>>,
    parser: &SqlParser,
) -> Result<Vec<Value>, WorkloadError> {
    let sockets = socket_directory()?;
    let mut outcomes: Vec<Option<Value>> = Vec::with_capacity(queries.len());
    let mut sessions = Vec::new();
    for ((index, query), author) in queries.into_iter().enumerate().zip(authors) {
        match query {
            PreparedQuery::Refused(record) => outcomes.push(Some(record)),
            PreparedQuery::Ready(session) => {
                let directory = query_directory(root, index);
                let (role, run_request) = query_session(request, index, session, data, parser);
                let role = RetainedRole::start(role, &directory, &sockets)?;
                let reselect_from = request.queries[index].reselect_from.clone();
                let query = request.queries[index].clone();
                let library = request.library.clone();
                let on_close = output_hook(request, &directory, move |home, session| {
                    let name = query.name.clone().unwrap_or_else(|| format!("q{:02}", index + 1));
                    crate::output::write_query(home, &crate::output::QueryOutput { name: &name, request: &query, session, library: &library }).map(drop)
                });
                sessions.push(ScheduledSession { directory, request: run_request, author, role, reselect_from, on_close });
                outcomes.push(None);
            }
        }
    }
    // The request's value may differ from the run's `request.json` (a scheduling control, `lifecycle::record_request`).
    eprintln!("queries: {} sessions, {} at a time (max_concurrent_queries)", sessions.len(), request.max_concurrent_queries.min(sessions.len()));
    let mut completed = run_sessions(sessions, &root.join("queries"), request.max_concurrent_queries)?.into_iter();
    Ok(outcomes.into_iter().map(|outcome| outcome.unwrap_or_else(|| completed.next().unwrap_or(Value::Null))).collect())
}

/// Query `index`'s role and the run request of its author session: the bench over its statement and the run's shared
/// capture, the role configuration (hardware, the objective's runtime targets) and the task record with the user's
/// limits. The objective itself travels in the session (`QuerySession::performance`).
pub fn query_session(request: &WorkloadRequest, index: usize, session: Arc<QuerySession>, data: &PreparedData, parser: &SqlParser) -> (QueryAuthorRole, RunRequest) {
    let query = &request.queries[index];
    let early_stop = query.objective.early_stop();
    let config = QueryRoleConfig { hardware: json!(request.hardware), observed_hardware: observe_host(), runtime_targets: query.objective.runtime_targets().to_vec(), early_stop };
    let objective = if query.objective.is_execution_time() { PERFORMANCE_OBJECTIVE } else { CORRECTNESS_OBJECTIVE };
    // Part of the session's ledger identity, so it stays the same across restarts; the policy decides from the
    // prepared context, `stop_after_first_eligible` and `early_stop` are recorded for readers. `early_stop` appears only
    // when set, so a session without it keeps its identity, and a resume cannot add or change it.
    let mut task = json!({"sql":query.sql,"objective":objective,"stop_after_first_eligible":query.objective.is_correctness(),"threads":request.hardware.threads});
    if let Some(stop) = early_stop {
        task["early_stop"] = json!(stop);
    }
    let role = QueryAuthorRole::new(bench(request, data, vec![session], parser), config);
    (role, RunRequest { format_version: 1, task, limits: query.limits.clone(), continue_from: query.continue_from.clone() })
}

/// Serializes writes into the output home (sessions close on their own threads; the top-level README is shared).
static OUTPUT_HOME_WRITES: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// The close hook of the session in `directory` that writes its folders into the request's output home with `write`
/// (`None` when the request names no output home). A failure never changes the session's result: it is recorded as
/// `<directory>/output-error-<ms>.json`, and `gendb output` can write the folders again from the session.
fn output_hook(
    request: &WorkloadRequest,
    directory: &Path,
    write: impl FnOnce(&Path, &Path) -> Result<(), crate::output::OutputError> + Send + 'static,
) -> Option<CloseHook> {
    let home = request.output_home.clone()?;
    let directory = directory.to_path_buf();
    Some(Box::new(move |_summary: &Value| {
        let _serial = OUTPUT_HOME_WRITES.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
        if let Err(error) = write(&home, &directory) {
            let record = directory.join(format!("output-error-{}.json", crate::controller::records::now_unix_ms()));
            let _ = crate::controller::records::write_json_atomic(&record, &json!({"output_home":home,"error":error.to_string()}));
        }
    }))
}

/// `$TMPDIR/sockets`: the configured scratch directory, never an implicit system default. Any depth works: sockets are
/// bound and reached through a short `/proc/self/fd` name (`controller::session`).
pub(crate) fn socket_directory() -> Result<PathBuf, WorkloadError> {
    let scratch = std::env::var_os("TMPDIR").map(PathBuf::from).filter(|path| path.is_absolute());
    let scratch = scratch.ok_or_else(|| WorkloadError::Scratch("TMPDIR must name an absolute scratch directory (the retained sessions' sockets live under it)".into()))?;
    // Canonical, so the recorded socket paths name the real directory.
    let scratch = scratch.canonicalize().map_err(|e| WorkloadError::Scratch(format!("TMPDIR {}: {e}", scratch.display())))?;
    Ok(scratch.join(SOCKET_SUBDIRECTORY))
}
