//! One workload run of the public controller: the user's request in, the workload's shared storages, every query's
//! author session, admitted packages and one workload summary out. The controller itself owns the run's lifecycle,
//! data preparation, author sessions, iteration/money accounting and evaluation; no external script sequences a
//! storage or a query.
//!
//! Phases (`synthesize`):
//! 1. request: read and validate ([`WorkloadRequest`]); authors' capabilities checked before any file is written;
//! 2. lifecycle ([`lifecycle`]): the immutable `request.json`; a restart returns a closed summary unless something is
//!    resumable; every author's readiness is checked before any data is read;
//! 3. preparation ([`preparation`]): statements, one shared prepared capture, and each statement's preflight; refusals
//!    close their query before any author call;
//! 4. workload storage (when `workload_storage` is requested): one storage author session over every ready statement
//!    designs, proves, builds and admits shared storages ([`sessions::run_storage_session`]); the query phase starts
//!    only once this session is closed;
//!    with `workload_storage.stop_before_queries` the run ends here: its summary is closed, every ready query
//!    `not_started`, and no query author is called;
//! 5. queries: each ready query's retained role and its author run under the generic session loop (`controller::run`),
//!    at most `max_concurrent_queries` at a time; each reads admitted storages or creates its own;
//! 6. finalization: the workload summary (storage session, queries in request order, preparation, per-role author
//!    accounting, provider capabilities).
//!
//! `preflight` runs phases 1–3 without authors (a dry run before paying for authors); `serve` is the serving route
//! ([`serving`]); `prepare-flat-storage` prepares the fixed flat storages of a `fixed_flat` request once
//! ([`flat_preparation`]), and under `fixed_flat` phase 3 stops before any preflight unless they are prepared;
//! `import` admits the packages of a published run folder without any author ([`import`]).
//!
//! Trust: outside the TCB. Admission decisions are `gendb_verification::admission`'s; the controller only sequences
//! them and records what happened.

pub mod authors;
pub mod continuation;
pub mod flat_preparation;
pub mod import;
pub mod lifecycle;
pub mod preparation;
pub mod render;
pub mod reselection;
pub mod serving;
pub mod sessions;

#[cfg(test)]
mod flat_fixture;
#[cfg(test)]
mod public_fixture;
#[cfg(test)]
mod preflight_reuse_fixture;

use super::ControllerError;
use super::author::{AuthorTransport, Capability};
use super::crash_dumps;
use super::limits::{Money, SpendPolicy};
use super::records::{self, RecordError};
use super::request::{RequestError, WorkloadRequest};
use super::run::predispatch_recovery_available;
use authors::{HostLeasedAuthor, WorkloadAuthors, inspect_authors};
use gendb_frontend::parser::{ParserError, SqlParser};
use gendb_storage::import::ImportError;
use gendb_verification::admission::AdmissionError;
use lifecycle::{Route, is_resumable, latest_summary, publish_summary, query_directory, record_request, record_route, storage_session_directory};
use crate::prompts::policy::{CORRECTNESS_OBJECTIVE, PERFORMANCE_OBJECTIVE};
use preparation::{PreparedQuery, PreparedWorkload, prepare_workload};
use serde_json::{Value, json};
use std::fmt;
use std::path::{Path, PathBuf};

/// Why a workload run stopped before its summary. Query-level refusals and author outcomes are not errors; they are
/// recorded results.
#[derive(Debug)]
pub enum WorkloadError {
    Request(RequestError),
    Record(RecordError),
    /// The host lock files cannot be used.
    HostLocks(String),
    /// Query `query`'s author provider is unusable (inspection or readiness).
    Author { query: usize, detail: String },
    /// The workload storage author's provider is unusable (inspection or readiness).
    StorageAuthor(String),
    /// The SQL frontend cannot run.
    Frontend(ParserError),
    /// The workload's source columns cannot be prepared.
    Preparation(ImportError),
    /// Serving a statement failed outside a recorded serving outcome.
    Serving(AdmissionError),
    /// The session controller failed.
    Controller(ControllerError),
    /// The controller's scratch directory is not configured.
    Scratch(String),
}

impl WorkloadError {
    pub fn invalid(detail: impl Into<String>) -> Self {
        WorkloadError::Request(RequestError::Invalid(detail.into()))
    }
}

impl fmt::Display for WorkloadError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WorkloadError::Request(error) => write!(f, "request: {error}"),
            WorkloadError::Record(error) => write!(f, "{error}"),
            WorkloadError::HostLocks(detail) => write!(f, "host locks: {detail}"),
            WorkloadError::Author { query, detail } => write!(f, "author of query {query}: {detail}"),
            WorkloadError::StorageAuthor(detail) => write!(f, "workload storage author: {detail}"),
            WorkloadError::Frontend(error) => write!(f, "SQL frontend: {error}"),
            WorkloadError::Preparation(error) => write!(f, "data preparation: {error}"),
            WorkloadError::Serving(error) => write!(f, "serving: {error}"),
            WorkloadError::Controller(error) => write!(f, "{error}"),
            WorkloadError::Scratch(detail) => write!(f, "scratch directory: {detail}"),
        }
    }
}

impl std::error::Error for WorkloadError {}

impl From<RequestError> for WorkloadError {
    fn from(error: RequestError) -> Self {
        WorkloadError::Request(error)
    }
}

impl From<RecordError> for WorkloadError {
    fn from(error: RecordError) -> Self {
        WorkloadError::Record(error)
    }
}

impl From<ControllerError> for WorkloadError {
    fn from(error: ControllerError) -> Self {
        WorkloadError::Controller(error)
    }
}

/// Synthesize `request` (read from `request_path`) in the run directory `run_dir` (`gendb synthesize`): the workload
/// storage author session (when requested) and one Claude Code author session per query, configured by the request
/// and inspected before any other work (evidence under `<run>/author-inspection`). `framework_executable` is the running gendb binary: it runs candidate libraries
/// (`gendb worker`) and serves the authors' local tools (`gendb author-tools mcp`). Returns the workload summary.
pub async fn synthesize(request_path: &Path, run_dir: &Path, framework_executable: &Path) -> Result<Value, WorkloadError> {
    // Before any child starts: every process of the run inherits it; the outcome is observed, never assumed (crash_dumps).
    let _ = crash_dumps::contain();
    let request = WorkloadRequest::read(request_path)?;
    request.validate()?;
    records::create_dir(run_dir)?;
    let root = run_dir.canonicalize().map_err(|e| RecordError::new(run_dir, e))?;
    let authors = inspect_authors(
        &request.author_executable,
        request.author_model,
        framework_executable,
        &root,
        request.queries.len(),
        request.workload_storage.is_some(),
    )?;
    run_workload(&request, &root, authors, framework_executable).await
}

/// The workload run with the given authors (`authors.queries[i]` writes query `i`; `authors.storage` the workload
/// storages, present exactly when the request asks for the storage phase); phases in the module doc. Every author's
/// capability is checked before anything is written and its readiness before any data is read. A restart of a run
/// whose latest summary is closed returns that summary unless a session can resume.
pub async fn run_workload<A: AuthorTransport + Send>(
    request: &WorkloadRequest,
    run_dir: &Path,
    authors: WorkloadAuthors<A>,
    framework_executable: &Path,
) -> Result<Value, WorkloadError> {
    request.validate()?;
    refuse_engine_request(request)?;
    if authors.queries.len() != request.queries.len() || request.max_concurrent_queries == 0 {
        return Err(WorkloadError::invalid("one author per query and a positive max_concurrent_queries are required"));
    }
    if authors.storage.is_some() != request.workload_storage.is_some() {
        return Err(WorkloadError::invalid("a storage author is given exactly when the request asks for the workload storage phase"));
    }
    let mut capabilities: Vec<Capability> = authors.queries.iter().map(AuthorTransport::capability).collect();
    if let Some(refusal) = capability_refusal(request, &capabilities, authors.storage.as_ref().map(AuthorTransport::capability).as_ref())? {
        return Ok(refusal);
    }
    let root = open_run_directory(request, run_dir)?;
    let lease = |author: A| HostLeasedAuthor::new(author, request.host_locks.clone());
    let mut storage_author = authors.storage.map(lease);
    let mut query_authors: Vec<_> = authors.queries.into_iter().map(lease).collect();
    if let Some(summary) = latest_summary(&root)?
        && !is_resumable(&summary)
        && !session_recovery_pending(&root, &summary, storage_author.as_ref(), &query_authors)?
    {
        return Ok(summary);
    }
    if let Some(author) = storage_author.as_mut() {
        author.preflight().map_err(WorkloadError::StorageAuthor)?;
        capabilities.push(author.capability());
    }
    for (query, author) in query_authors.iter_mut().enumerate() {
        author.preflight().map_err(|detail| WorkloadError::Author { query, detail })?;
    }
    let parser = SqlParser::from_environment().map_err(WorkloadError::Frontend)?;
    let prepared = prepare_workload(request, &root, &parser, framework_executable).await?;
    let preparation = preparation_summary(&prepared);
    let (storage_summary, queries) = match &prepared.data {
        None => (Value::Null, query_readiness(&prepared)),
        Some(data) => {
            let storage_summary = match storage_author {
                Some(author) => sessions::run_storage_session(request, &root, &prepared.queries, data, author, &parser)?,
                None => Value::Null,
            };
            if storage_summary["status"] == "closed" && request.stops_before_queries() {
                (storage_summary, queries_not_started(&prepared.queries))
            } else if storage_summary.is_null() || storage_summary["status"] == "closed" {
                (storage_summary, sessions::run_query_sessions(request, &root, prepared.queries, data, query_authors, &parser)?)
            } else {
                // The query phase waits for a closed storage session (a resumable one continues on restart).
                let waiting = prepared
                    .queries
                    .iter()
                    .map(|query| match query {
                        PreparedQuery::Refused(record) => record.clone(),
                        PreparedQuery::Ready(_) => json!({"status":"waiting_for_workload_storage","resumable":true}),
                    })
                    .collect();
                (storage_summary, waiting)
            }
        }
    };
    let accounting = author_accounting(&storage_summary, &queries);
    let mut summary = json!({"status":"closed","workload_storage":storage_summary,"queries":queries,"author_accounting":accounting,
        "preparation":preparation,"provider_capabilities":capabilities,"storage_policy":request.storage_policy.author_view(),
        "scope":"statements and one shared data preparation; the workload storage session when requested; then one persistent verified author session per ready query with independent evaluation, qualification and serving"});
    if is_resumable(&summary) || storage_resumable(&summary["workload_storage"]) {
        summary["status"] = json!("resumable");
    }
    if request.stops_before_queries() {
        // Where later requests reuse the capture from (`prepared_workload`): a storage may have extended it.
        summary["prepared_workload_for_later_requests"] = json!(prepared.data.as_ref().map(|data| data.capture.current().root().to_path_buf()));
    }
    publish_summary(&root, &summary)?;
    Ok(summary)
}

/// Per query of a run that stops after the workload storage phase: its refusal, or `not_started` (closed, not
/// resumable; a later request over the same library runs it).
fn queries_not_started(queries: &[PreparedQuery]) -> Vec<Value> {
    queries
        .iter()
        .map(|query| match query {
            PreparedQuery::Refused(record) => record.clone(),
            PreparedQuery::Ready(session) => not_started(&session.statement().key_v4_id),
        })
        .collect()
}

fn not_started(statement_key: &str) -> Value {
    json!({"status":"not_started","statement_key":statement_key,
        "reason":"workload_storage.stop_before_queries: this run ran the workload storage phase only; a later request over the same library runs the query"})
}

/// The storage session needs a restart: it did not close (framework error, unresolved accounting).
fn storage_resumable(storage: &Value) -> bool {
    !storage.is_null() && storage["status"] != "closed"
}

/// Provider-reported cost, tokens, calls and iterations per author role and their sum. Receipts stay the authority;
/// this adds the session summaries' own totals. Framework work is never counted as author cost.
fn author_accounting(storage: &Value, queries: &[Value]) -> Value {
    let session = |role: &str, summary: &Value| {
        json!({"role":role,"status":summary["status"],"reported_cost_usd":summary["reported_cost_usd"],"known_reported_cost_usd":summary["known_reported_cost_usd"],
            "cost_complete":summary["cost_complete"],"calls":summary["calls"],"iterations":summary["iterations"],"tokens":summary.pointer("/accounting/tokens"),
            "author_elapsed_ms":summary["author_elapsed_ms"],"ledger":summary["ledger"]})
    };
    let mut sessions: Vec<Value> = vec![];
    if !storage.is_null() {
        sessions.push(session("workload_storage", storage));
    }
    sessions.extend(queries.iter().enumerate().filter(|(_, q)| q.get("calls").is_some()).map(|(i, q)| session(&format!("query-{i:04}"), q)));
    let mut total = Money::default();
    let mut complete = true;
    for s in &sessions {
        let known = s["known_reported_cost_usd"].as_str().and_then(|text| Money::parse(text).ok());
        match known.map(|known| total.checked_sum(known)) {
            Some(Ok(sum)) => total = sum,
            _ => complete = false,
        }
        complete &= s["cost_complete"] == true;
    }
    json!({"sessions":sessions,"known_reported_cost_usd_total":total,"cost_complete":complete,
        "scope":"actual provider-reported author cost per role (workload storage author, each query author); framework workers and the controller are not included; raw receipts in each session's calls/ are authoritative"})
}

/// A capability no session can use, as the closed outcome returned before anything is written: a persistent session
/// is required, and a hard billed-dollar guard (`strict_usd`) needs a transport that can enforce one.
fn capability_refusal(request: &WorkloadRequest, capabilities: &[Capability], storage: Option<&Capability>) -> Result<Option<Value>, WorkloadError> {
    if let (Some(capability), Some(storage_request)) = (storage, &request.workload_storage) {
        if !capability.persistent_sessions {
            return Err(WorkloadError::StorageAuthor("a persistent author session is required".into()));
        }
        if storage_request.limits.spend_policy == SpendPolicy::StrictUsd && !capability.hard_usd_cap {
            return Ok(Some(json!({"status":"unsupported_capability","role":"workload_storage",
                "reason":"the transport cannot enforce a hard billed-dollar cap; select estimated_usd explicitly",
                "provider":capability,"inference_dispatched":false,"data_prepared":false})));
        }
    }
    for (query, capability) in capabilities.iter().enumerate() {
        if !capability.persistent_sessions {
            return Err(WorkloadError::Author { query, detail: "a persistent author session is required".into() });
        }
        if request.queries[query].limits.spend_policy == SpendPolicy::StrictUsd && !capability.hard_usd_cap {
            return Ok(Some(json!({"status":"unsupported_capability","query":query,
                "reason":"the transport cannot enforce a hard billed-dollar cap; select estimated_usd explicitly",
                "provider":capability,"inference_dispatched":false,"data_prepared":false})));
        }
    }
    Ok(None)
}

/// A closed summary still continues when some session proves a pre-dispatch recovery (its last call never launched a
/// provider) or recovered after that summary was published.
fn session_recovery_pending<A: AuthorTransport>(
    root: &Path,
    summary: &Value,
    storage: Option<&HostLeasedAuthor<A>>,
    authors: &[HostLeasedAuthor<A>],
) -> Result<bool, WorkloadError> {
    if let Some(author) = storage
        && predispatch_recovery_available(&storage_session_directory(root), author, Some(&summary["workload_storage"]))?
    {
        return Ok(true);
    }
    for (index, author) in authors.iter().enumerate() {
        if predispatch_recovery_available(&query_directory(root, index), author, Some(&summary["queries"][index]))? {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Dry run of `request` in the run directory `run_dir`: phases 1–3 (request, lifecycle, preparation) without any
/// author. `framework_executable` is the gendb binary, which runs candidate libraries as `gendb worker`. Writes a new
/// `preflight[-N].json` (never a workload summary, so a later `synthesize` of the same run continues normally) and
/// returns it.
pub async fn preflight(request_path: &Path, run_dir: &Path, framework_executable: &Path) -> Result<Value, WorkloadError> {
    // Before any child starts: every process of the run inherits it; the outcome is observed, never assumed (crash_dumps).
    let _ = crash_dumps::contain();
    let request = WorkloadRequest::read(request_path)?;
    request.validate()?;
    refuse_engine_request(&request)?;
    let root = open_run_directory(&request, run_dir)?;
    let parser = SqlParser::from_environment().map_err(WorkloadError::Frontend)?;
    let prepared = prepare_workload(&request, &root, &parser, framework_executable).await?;
    let record = json!({"format_version":1,"status":"preflight_complete","inference_dispatched":false,
        "queries":query_readiness(&prepared),"preparation":preparation_summary(&prepared),
        "scope":"statements, data preparation and each query's preflight and prepared-data references; no author was inspected or called"});
    let path = records::next_free_record(&root, "preflight.json", "preflight");
    records::write_new_json(&path, &record)?;
    Ok(record)
}

/// Serve `request` (`gendb serve`): see [`serving::serve_workload`].
pub fn serve(request_path: &Path, run_dir: &Path, framework_executable: &Path) -> Result<Value, WorkloadError> {
    // Before any child starts: every process of the run inherits it; the outcome is observed, never assumed (crash_dumps).
    let _ = crash_dumps::contain();
    let request = WorkloadRequest::read(request_path)?;
    refuse_engine_request(&request)?;
    serving::serve_workload(&request, run_dir, framework_executable)
}

/// An engine request (`engine` section) runs only with `gendb engine synthesize`; the workload routes refuse it.
fn refuse_engine_request(request: &WorkloadRequest) -> Result<(), WorkloadError> {
    match request.engine {
        Some(_) => Err(WorkloadError::invalid("this is an engine request (engine section): run it with gendb engine synthesize, or serve its versions with gendb serve-engine")),
        None => Ok(()),
    }
}

/// Create the synthesis run directory, record or compare its route and immutable request, and return its canonical
/// path.
fn open_run_directory(request: &WorkloadRequest, run_dir: &Path) -> Result<PathBuf, WorkloadError> {
    records::create_dir(run_dir)?;
    let root = run_dir.canonicalize().map_err(|e| RecordError::new(run_dir, e))?;
    record_route(&root, Route::Synthesis)?;
    record_request(&root, &serde_json::to_value(request).map_err(|e| WorkloadError::invalid(e.to_string()))?)?;
    Ok(root)
}

/// Per query, in request order: ready (statement key, preflight record, reference mode and per-binding reference
/// outcome) or its refusal record.
fn query_readiness(prepared: &PreparedWorkload) -> Vec<Value> {
    prepared
        .queries
        .iter()
        .map(|query| match query {
            PreparedQuery::Refused(record) => record.clone(),
            PreparedQuery::Ready(session) => {
                let statement = session.statement();
                let references: Vec<Value> = statement
                    .bindings
                    .iter()
                    .zip(&session.references)
                    .map(|(binding, reference)| match reference {
                        Ok(exact) => json!({"binding":binding.name,"reference":"exact","rows":exact.rows.len()}),
                        Err(none) => json!({"binding":binding.name,"reference":"none","reason":none.0}),
                    })
                    .collect();
                let objective = if session.performance { PERFORMANCE_OBJECTIVE } else { CORRECTNESS_OBJECTIVE };
                json!({"status":"ready","sql":statement.sql,"statement_key":statement.key_v4_id,"objective":objective,
                    "preflight":statement.directory.join("preflight.json"),"reference_mode":session.preflight.prepared.name(),
                    "references":references,"inputs":session.inputs.archive,"worker_counts":session.worker_counts})
            }
        })
        .collect()
}

fn preparation_summary(prepared: &PreparedWorkload) -> Value {
    match &prepared.data {
        None => json!({"data_prepared":false,"reason":"every statement was refused before data preparation"}),
        Some(data) => json!({"data_prepared":true,"method":data.report.method,"preparation_ns":data.preparation_ns,
            "source_version":data.source.source_snapshot(),"record":data.record}),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::controller::author::AuthorCall;
    use crate::controller::hardware::Hardware;
    use crate::controller::ledger::Ledger;
    use crate::controller::limits::tests::limits;
    use crate::controller::request::QueryRequest;
    use crate::controller::test_support::{FixtureAuthor, scratch_root};
    use crate::query::host_locks::HostLocks;
    use gendb_storage::import::DatasetSpec;

    fn request(root: &Path) -> WorkloadRequest {
        WorkloadRequest {
            format_version: 2,
            dataset: DatasetSpec { tables: vec![] },
            queries: vec![QueryRequest { name: None, sql: "fixture".into(), limits: limits(), parameters: vec![], test_bindings: vec![], arguments: vec![], objective: Default::default(), preflight_from: None, reselect_from: None, continue_from: None }],
            hardware: Hardware { threads: vec![1] },
            max_concurrent_queries: 1,
            max_concurrent_preparations: None,
            author_executable: "unused".into(),
            author_model: Default::default(),
            library: root.join("library"),
            host_locks: HostLocks { activity_lock: root.join("activity.lock"), build_lock: root.join("build.lock"), race_lock: root.join("race.lock") },
            prepared_workload: None,
            data_allowance: None,
            output_home: None,
            workload_storage: None,
            part_access: None,
            storage_policy: Default::default(),
            integrity_constraints: None,
            validation: Default::default(),
            engine: None,
        }
    }

    #[test]
    fn a_query_not_started_after_the_storage_phase_is_closed_not_resumable() {
        let summary = json!({"status":"closed","queries":[not_started("k"),{"status":"refused"}]});
        assert!(!is_resumable(&summary) && !storage_resumable(&json!({"status":"closed"})));
        assert!(author_accounting(&Value::Null, summary["queries"].as_array().unwrap())["sessions"].as_array().unwrap().is_empty(), "no query author is accounted");
    }

    fn unready() -> FixtureAuthor {
        FixtureAuthor { ready: false, prove: true, ..FixtureAuthor::default() }
    }

    /// Earlier version's `predispatch_recovery_public_preflight_and_existing_summary_routing`: an unready author stops the run before
    /// any data preparation; a closed summary is returned without readiness checks; a query session whose calls were
    /// all refused before dispatch reopens the run (and meets the same readiness check), leaving the summary unchanged.
    #[tokio::test]
    async fn author_readiness_precedes_data_and_closed_summaries_route_by_session_recovery() {
        let root = scratch_root("workload-routing");
        let request = request(&root);
        let exe = Path::new("unused-worker");
        let error = run_workload(&request, &root, WorkloadAuthors { storage: None, queries: vec![unready()] }, exe).await.unwrap_err();
        assert!(matches!(&error, WorkloadError::Author { query: 0, detail } if detail == "fixture adapter unavailable"), "{error}");
        assert!(root.join("request.json").is_file());
        assert!(!lifecycle::data_root(&root).exists());

        let summary = json!({"status":"closed","queries":[{"status":"closed","reason":"retry_limit"}]});
        publish_summary(&root, &summary).unwrap();
        assert_eq!(run_workload(&request, &root, WorkloadAuthors { storage: None, queries: vec![unready()] }, exe).await.unwrap(), summary);

        let directory = query_directory(&root, 0);
        let mut ledger = Ledger::open(&directory, json!({"fixture":true}), limits()).unwrap();
        let unleased = HostLocks { activity_lock: "relative.lock".into(), ..request.host_locks.clone() };
        let mut author = HostLeasedAuthor::new(unready(), unleased);
        for _ in 0..2 {
            let call = ledger.begin_call().unwrap();
            let call_dir = directory.join(format!("calls/{:04}", call.id));
            records::create_dir(&call_dir).unwrap();
            let session = ledger.state.session_id.clone();
            let workspace = directory.join("author");
            let receipt = author.invoke(&AuthorCall { call: &call, session_id: &session, resume: false, prompt: "p", workspace: &workspace, call_dir: &call_dir, limits: &limits() });
            assert!(receipt.predispatch_refusal());
            records::write_new_json(&call_dir.join("receipt.json"), &receipt).unwrap();
            ledger.settle(receipt).unwrap();
        }
        ledger.state.closed = Some(json!({"status":"closed","reason":"retry_limit"}));
        ledger.save().unwrap();
        drop(ledger);
        let error = run_workload(&request, &root, WorkloadAuthors { storage: None, queries: vec![unready()] }, exe).await.unwrap_err();
        assert!(matches!(error, WorkloadError::Author { query: 0, .. }));
        assert_eq!(latest_summary(&root).unwrap().unwrap(), summary);
        assert!(!lifecycle::data_root(&root).exists());
    }

    #[test]
    fn a_format_1_request_is_refused_with_the_fields_that_differ() {
        let root = scratch_root("workload-format-1-request");
        records::create_dir(&root).unwrap();
        let path = root.join("request.json");
        records::write_new_json(&path, &json!({"format_version":1,"authoring":"verus_rust","worker":"w","hardware":{"threads":[1],"memory_limit_bytes":1}})).unwrap();
        let error = WorkloadRequest::read(&path).unwrap_err();
        let RequestError::FormatOne { v7_fields } = &error else { panic!("{error}") };
        assert_eq!(v7_fields.len(), 3, "{error}");
        assert!(error.to_string().contains("earlier GenDB version"));
    }
}
