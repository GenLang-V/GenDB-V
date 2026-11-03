//! The import route (`gendb import REQUEST.json PUBLISHED_DIR RUN_DIR`): the packages of a published run folder
//! (`crate::published`, for example GenDB-V's `results/<workload>/<run>/`) admitted into the request's library without
//! any author, over the request's own dataset at any scale. `gendb serve` and `gendb evaluate` then run them like
//! synthesized packages.
//!
//! Phases:
//! 1. request: read and validated as for `synthesize`; an engine request, or a query naming `reselect_from` or
//!    `continue_from`, is refused. The published folder is read, and every request query must match exactly one
//!    published query by its template text (otherwise the import is refused before anything is written);
//! 2. lifecycle: the run's immutable `request.json`, its published folder (`published.json`) and route `import`; a
//!    rerun names the same request and folder, and a rerun of a closed import returns its summary;
//! 3. preparation (`preparation::prepare_workload`, as for `synthesize`): statements, the capture of the request's
//!    dataset, every statement's preflight under the request's validation policy; refusals close their query;
//! 4. storages (not under `fixed_flat`): every published storage the ready queries read, with the storages it is built
//!    from, sources first. Each is seeded from its published author files and manifest, frozen with fresh framework
//!    files, verified and compiled whole, built over this run's data and registered in the library: the path of the
//!    `storage_register` tool (`Workbench::check_storage`, `Workbench::register`). `<run>/storages/<name>-v<N>/
//!    registration.json` (written last) makes a rerun reuse it; a refused attempt is recorded beside it and refuses
//!    the storages built from it and the queries that read them. Under `fixed_flat` the queries read the prepared
//!    flat storages (`gendb prepare-flat-storage` with the same request first);
//! 5. queries: one import session per ready query (`controller::import`, at most `max_concurrent_queries` at once):
//!    its author files frozen with fresh framework files over the admitted storages, evaluated, qualified and closed by
//!    the query role;
//! 6. summary: what was admitted and what was refused, with the reason; `prepared_workload` names this run's prepared
//!    data, which the serving request (`gendb serve`) and the evaluation request (`gendb evaluate`) read.
//!
//! The import writes no output home (the published folder is the readable output); a request's `output_home` and
//! `workload_storage` are not used.
//!
//! Trust: outside the TCB, like the controller. Nothing published is trusted; admission decisions are those of the
//! normal storage and query paths.

use super::lifecycle::{Route, is_resumable, latest_summary, publish_summary, query_directory, record_refusal, record_request, record_route};
use super::preparation::{PreparedData, PreparedQuery, prepare_workload};
use super::sessions::{bench, query_session, socket_directory};
use super::{WorkloadError, preparation_summary, refuse_engine_request};
use crate::controller::crash_dumps;
use crate::controller::import::{ImportCandidate, ImportSession, run_import_sessions};
use crate::controller::records::{self, RecordError, now_unix_ms};
use crate::controller::request::WorkloadRequest;
use crate::controller::session::RetainedRole;
use crate::published::{PublishedQuery, PublishedRun, PublishedStorage, seed_storage_workspace};
use crate::query::QuerySession;
use crate::storage::freeze::freeze_storage;
use gendb_artifacts::verus as library_records;
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_frontend::parser::SqlParser;
use gendb_verification::admission::{AdmissionError, FailureClass};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// The record of an admitted imported storage (`<run>/storages/<name>-v<N>/registration.json`), written last.
const REGISTRATION_FILE: &str = "registration.json";
/// The run's published folder (`<run>/published.json`), written once.
const PUBLISHED_FILE: &str = "published.json";

/// Import the published packages of `published_dir` for `request` (read from `request_path`) in the run directory
/// `run_dir` (see the module documentation). `framework_executable` is the running gendb binary (it runs candidate
/// libraries as `gendb worker`). Returns the import summary.
pub async fn import(request_path: &Path, published_dir: &Path, run_dir: &Path, framework_executable: &Path) -> Result<Value, WorkloadError> {
    // Before any child starts: every process of the run inherits it; the outcome is observed, never assumed.
    let _ = crash_dumps::contain();
    let request = WorkloadRequest::read(request_path)?;
    request.validate()?;
    refuse_engine_request(&request)?;
    if let Some(index) = request.queries.iter().position(|q| q.reselect_from.is_some() || q.continue_from.is_some()) {
        return Err(WorkloadError::invalid(format!("queries[{index}] names reselect_from or continue_from: an import admits published packages, not another session's")));
    }
    let published = PublishedRun::read(published_dir).map_err(|e| WorkloadError::invalid(format!("published run: {e}")))?;
    let matched = match_queries(&request, &published)?;
    records::create_dir(run_dir)?;
    let root = run_dir.canonicalize().map_err(|e| RecordError::new(run_dir, e))?;
    record_route(&root, Route::Import)?;
    record_request(&root, &serde_json::to_value(&request).map_err(|e| WorkloadError::invalid(e.to_string()))?)?;
    record_published(&root, &published.root)?;
    if let Some(summary) = latest_summary(&root)?
        && summary["status"] == "closed"
    {
        return Ok(summary);
    }
    let parser = SqlParser::from_environment().map_err(WorkloadError::Frontend)?;
    let prepared = prepare_workload(&request, &root, &parser, framework_executable).await?;
    let preparation = preparation_summary(&prepared);
    let Some(data) = prepared.data.as_ref() else {
        let queries: Vec<Value> = prepared.queries.iter().map(|q| match q {
            PreparedQuery::Refused(record) => record.clone(),
            PreparedQuery::Ready(_) => unreachable!("data is prepared when a statement is ready"),
        }).collect();
        return finish(&root, &request, &published, &matched, vec![], queries, preparation, None);
    };
    let ready: Vec<Arc<QuerySession>> = prepared.queries.iter().filter_map(|q| match q {
        PreparedQuery::Ready(session) => Some(session.clone()),
        PreparedQuery::Refused(_) => None,
    }).collect();
    let ready_published: Vec<&PublishedQuery> = prepared.queries.iter().zip(&matched).filter(|(q, _)| matches!(q, PreparedQuery::Ready(_))).map(|(_, p)| *p).collect();
    let (storages, storage_records) = match request.storage_policy.is_fixed_flat() {
        true => (StorageUses::Flat(flat_packages(&request, data, &ready)?), vec![]),
        false => {
            let plan = published.storage_plan(&ready_published).map_err(|e| WorkloadError::invalid(format!("published run: {e}")))?;
            let (outcomes, records) = import_storages(&request, &root, &plan, &published, data, ready, &parser)?;
            (StorageUses::Imported(outcomes), records)
        }
    };
    let queries = import_queries(&request, &root, &published, &matched, prepared.queries, data, &storages, &parser)?;
    finish(&root, &request, &published, &matched, storage_records, queries, preparation, Some(data.source.root().to_path_buf()))
}

/// Record the run's published folder once (`<run>/published.json`), or refuse a rerun that names another one.
fn record_published(root: &Path, published: &Path) -> Result<(), WorkloadError> {
    let path = root.join(PUBLISHED_FILE);
    if !path.exists() {
        return Ok(records::write_new_json(&path, &json!({"format_version":1,"published_run":published}))?);
    }
    let recorded: Value = records::read_json(&path)?;
    if recorded["published_run"] != json!(published) {
        return Err(WorkloadError::invalid(format!("this run imports {}; use another run directory to import {}", recorded["published_run"], published.display())));
    }
    Ok(())
}

/// Each request query's published package: the one published query with the same template text. Any query without
/// exactly one refuses the import (named), before anything is written.
fn match_queries<'a>(request: &WorkloadRequest, published: &'a PublishedRun) -> Result<Vec<&'a PublishedQuery>, WorkloadError> {
    let mut matched = vec![];
    let mut unmatched = vec![];
    for (index, query) in request.queries.iter().enumerate() {
        match published.queries_for_sql(&query.sql).as_slice() {
            [one] => matched.push(*one),
            found => unmatched.push(format!("queries[{index}] ({}): {} published queries have its template text", query.name.as_deref().unwrap_or("unnamed"), found.len())),
        }
    }
    if !unmatched.is_empty() {
        let names: Vec<&str> = published.queries.iter().map(|q| q.name.as_str()).collect();
        return Err(WorkloadError::invalid(format!(
            "published_package_missing: every request query needs the published query with the same template text (query.sql) in {} (published: {}); {}",
            published.root.display(),
            names.join(", "),
            unmatched.join("; ")
        )));
    }
    Ok(matched)
}

/// The admitted package of each storage a query reads.
enum StorageUses {
    /// `fixed_flat`: the library's current flat package of each storage name.
    Flat(BTreeMap<String, ContentId>),
    /// Otherwise: per published storage (`<name>-v<N>`), its imported package or why it was refused.
    Imported(BTreeMap<String, Result<ContentId, String>>),
}

impl StorageUses {
    /// The admitted packages `query` reads, in use order, or why one has none.
    fn of(&self, published: &PublishedRun, query: &PublishedQuery) -> Result<Vec<(String, ContentId)>, String> {
        query
            .uses
            .iter()
            .map(|name| {
                let package = match self {
                    StorageUses::Flat(packages) => packages
                        .get(name)
                        .copied()
                        .ok_or_else(|| format!("flat_storage_not_prepared: the query reads {name}, which is not a prepared flat storage of this library")),
                    StorageUses::Imported(outcomes) => {
                        let storage = published.storage_read_by(&query.crate_src, name)?;
                        match outcomes.get(&storage.label()) {
                            Some(Ok(package)) => Ok(*package),
                            Some(Err(reason)) => Err(format!("published_storage_refused: storage {} was not imported ({reason})", storage.label())),
                            None => Err(format!("storage {} was not planned", storage.label())),
                        }
                    }
                }?;
                Ok((name.clone(), package))
            })
            .collect()
    }
}

/// Under `fixed_flat`: the current flat package of every table's flat storage (prepared by `gendb prepare-flat-storage`;
/// `prepare_workload` has already refused a library without them).
fn flat_packages(request: &WorkloadRequest, data: &PreparedData, ready: &[Arc<QuerySession>]) -> Result<BTreeMap<String, ContentId>, WorkloadError> {
    let store = ObjectStore::open(&request.library).map_err(|e| WorkloadError::invalid(format!("library: {e}")))?;
    let capture = gendb_storage::versions::CurrentCapture::of(&data.capture.current()).map_err(|e| WorkloadError::invalid(e.to_string()))?;
    let Some(statement) = ready.first() else { return Ok(BTreeMap::new()) };
    let schema = &statement.statement().instance.doc.tables;
    let ready = crate::storage::flat::flat_readiness(&store, schema, &capture).map_err(|e| WorkloadError::invalid(e.to_string()))?;
    let records = ready.map_err(|missing| WorkloadError::invalid(format!("flat_storage_not_prepared: {}", missing.join("; "))))?;
    records
        .iter()
        .map(|record| {
            let name = record["storage"].as_str().unwrap_or_default().to_string();
            let package = serde_json::from_value(record["package"].clone()).map_err(|e| WorkloadError::invalid(format!("flat storage {name}: {e}")))?;
            Ok((name, package))
        })
        .collect()
}

/// Phase 4: import every planned storage in order on one bench over the ready statements (the workload storage
/// session's bench). Returns each storage's outcome by label and the summary records in plan order.
fn import_storages(
    request: &WorkloadRequest,
    root: &Path,
    plan: &[&PublishedStorage],
    published: &PublishedRun,
    data: &PreparedData,
    statements: Vec<Arc<QuerySession>>,
    parser: &SqlParser,
) -> Result<(BTreeMap<String, Result<ContentId, String>>, Vec<Value>), WorkloadError> {
    let mut outcomes: BTreeMap<String, Result<ContentId, String>> = BTreeMap::new();
    let mut summaries = vec![];
    if plan.is_empty() {
        return Ok((outcomes, summaries));
    }
    let directory = root.join("storages");
    let mut bench = bench(request, data, statements, parser);
    let workspace = bench.open_workspace(&directory.join("author")).map_err(|e| WorkloadError::invalid(format!("storage import workspace: {e}")))?;
    let store = bench.store().map_err(|e| WorkloadError::invalid(format!("library: {e}")))?;
    for storage in plan {
        let label = storage.label();
        let storage_dir = directory.join(&label);
        records::create_dir(&storage_dir)?;
        let registration = storage_dir.join(REGISTRATION_FILE);
        if registration.exists() {
            let record: Value = records::read_json(&registration)?;
            let package: Option<ContentId> = serde_json::from_value(record["package"].clone()).ok();
            let versions = library_records::storage_versions(&store, &storage.name).map_err(|e| WorkloadError::invalid(format!("library: {e}")))?;
            if let Some(package) = package.filter(|p| versions.iter().any(|(_, admitted)| admitted.package == *p)) {
                outcomes.insert(label.clone(), Ok(package));
                summaries.push(storage_outcome(&label, &record, &registration));
                continue;
            }
        }
        let sources: Result<Vec<(String, ContentId)>, String> = published.sources_of(storage).and_then(|sources| {
            sources
                .iter()
                .map(|source| match outcomes.get(&source.label()) {
                    Some(Ok(package)) => Ok((source.name.clone(), *package)),
                    Some(Err(reason)) => Err(format!("its source storage {} was not imported ({reason})", source.label())),
                    None => Err(format!("its source storage {} was not planned before it", source.label())),
                })
                .collect()
        });
        let attempt = storage_dir.join(format!("attempt-{}", now_unix_ms()));
        let outcome = sources.map_err(AdmissionError::refusal).and_then(|sources| {
            let manifest = seed_storage_workspace(storage, &sources, &workspace).map_err(AdmissionError::tool)?;
            records::create_dir(&attempt).map_err(AdmissionError::tool)?;
            let frozen_dir = attempt.join("frozen");
            let frozen = freeze_storage(&workspace, &manifest, &frozen_dir, bench.schema(), Some(&store), &BTreeMap::new())?;
            let (mut checked, _) = bench.check_storage(&frozen, &frozen_dir, &attempt.join("check"), &BTreeSet::new())?;
            let registered_by = json!({"role":"import","published_storage":storage.crate_src,"run":root});
            let admitted = bench.register(&mut checked, &frozen, registered_by)?;
            Ok((admitted, checked))
        });
        match outcome {
            Ok((admitted, checked)) => {
                let record = json!({"format_version":1,"storage":label,"name":storage.name,"published_storage":storage.crate_src,"attempt":attempt,
                    "package":admitted.package,"admission":admitted.admission,"asset":admitted.asset,"admitted_now":admitted.admitted_now,"check":checked.record});
                records::write_new_json(&registration, &record)?;
                eprintln!("import: storage {label} admitted (package {})", admitted.package);
                outcomes.insert(label.clone(), Ok(admitted.package));
                summaries.push(storage_outcome(&label, &record, &registration));
            }
            Err(error) => {
                let path = storage_dir.join(format!("refusal-{}.json", now_unix_ms()));
                let record = json!({"format_version":1,"storage":label,"published_storage":storage.crate_src,"attempt":attempt,
                    "failure_class":error.class,"error":error.to_string(),"resumable":error.class == FailureClass::ToolFailure});
                records::write_new_json(&path, &record)?;
                eprintln!("import: storage {label} refused ({})", error);
                outcomes.insert(label.clone(), Err(error.to_string()));
                summaries.push(json!({"storage":label,"status":"refused","failure_class":error.class,"error":error.to_string(),
                    "resumable":record["resumable"],"record":path}));
            }
        }
    }
    Ok((outcomes, summaries))
}

/// The summary entry of an admitted storage.
fn storage_outcome(label: &str, record: &Value, path: &Path) -> Value {
    json!({"storage":label,"status":"admitted","package":record["package"],"admission":record["admission"],"asset":record["asset"],
        "admitted_now":record["admitted_now"],"record":path})
}

/// Phase 5: one import session per ready query whose storages are admitted; the others are refused by name. Returns
/// one outcome per request query, in request order.
#[allow(clippy::too_many_arguments)]
fn import_queries(
    request: &WorkloadRequest,
    root: &Path,
    published: &PublishedRun,
    matched: &[&PublishedQuery],
    queries: Vec<PreparedQuery>,
    data: &PreparedData,
    storages: &StorageUses,
    parser: &SqlParser,
) -> Result<Vec<Value>, WorkloadError> {
    let sockets = socket_directory()?;
    let mut outcomes: Vec<Option<Value>> = vec![];
    let mut sessions = vec![];
    for (index, query) in queries.into_iter().enumerate() {
        let source = matched[index];
        let session = match query {
            PreparedQuery::Refused(record) => {
                outcomes.push(Some(record));
                continue;
            }
            PreparedQuery::Ready(session) => session,
        };
        match storages.of(published, source) {
            Err(reason) => {
                let record = json!({"status":"refused","sql":request.queries[index].sql,"error":reason,"failure_class":"published_storage_refused",
                    "inference_dispatched":false,"calls":0,"iterations":0,"published_query":source.name,
                    "reason":"refused before its import session: a storage it reads has no admitted package in this import"});
                record_refusal(root, index, &record)?;
                outcomes.push(Some(record));
            }
            Ok(uses) => {
                let directory = query_directory(root, index);
                let (role, run_request) = query_session(request, index, session, data, parser);
                let role = RetainedRole::start(role, &directory, &sockets)?;
                let candidate = ImportCandidate { published_run: published.root.clone(), query: source.clone(), uses };
                sessions.push(ImportSession { directory, request: run_request, role, candidate, on_close: None });
                outcomes.push(None);
            }
        }
    }
    eprintln!("import: {} query sessions, {} at a time (max_concurrent_queries)", sessions.len(), request.max_concurrent_queries.min(sessions.len()));
    let mut completed = run_import_sessions(sessions, &root.join("queries"), request.max_concurrent_queries)?.into_iter();
    Ok(outcomes.into_iter().map(|outcome| outcome.unwrap_or_else(|| completed.next().unwrap_or(Value::Null))).collect())
}

/// Phase 6: the import summary (closed, or resumable when a session or a storage stopped in the framework), published
/// as the run's newest summary. `matched`: each request query's published query.
#[allow(clippy::too_many_arguments)]
fn finish(
    root: &Path,
    request: &WorkloadRequest,
    published: &PublishedRun,
    matched: &[&PublishedQuery],
    storages: Vec<Value>,
    sessions: Vec<Value>,
    preparation: Value,
    prepared_workload: Option<PathBuf>,
) -> Result<Value, WorkloadError> {
    let queries: Vec<Value> = request
        .queries
        .iter()
        .zip(sessions)
        .enumerate()
        .map(|(index, (query, outcome))| query_outcome(root, index, query.name.as_deref(), &matched[index].name, outcome))
        .collect();
    let admitted: Vec<&Value> = queries.iter().filter(|q| q["status"] == "admitted").map(|q| &q["query"]).collect();
    let mut summary = json!({"status":"closed","route":"import","published_run":published.root,
        "admitted":{"storages":storages.iter().filter(|s| s["status"] == "admitted").map(|s| &s["storage"]).collect::<Vec<_>>(),"queries":admitted},
        "refused":storages.iter().filter(|s| s["status"] != "admitted").chain(queries.iter().filter(|q| q["status"] != "admitted")).collect::<Vec<_>>(),
        "storages":storages,"queries":queries,"preparation":preparation,"storage_policy":request.storage_policy.kind(),
        "prepared_workload":prepared_workload,"library":request.library,"inference_dispatched":false,"reported_cost_usd":"0",
        "not_used":{"output_home":request.output_home,"workload_storage":request.workload_storage.is_some()},
        "scope":"published packages admitted without an author: each published crate's author files frozen with this run's framework files, verified and compiled whole by Verus, storages built over this run's data, queries evaluated and qualified under the request's validation policy; serve them with gendb serve (prepared_workload above) or measure them with gendb evaluate"});
    let storage_resumable = summary["storages"].as_array().is_some_and(|s| s.iter().any(|s| s["resumable"] == true));
    if is_resumable(&summary) || storage_resumable {
        summary["status"] = json!("resumable");
    }
    publish_summary(root, &summary)?;
    Ok(summary)
}

/// The summary entry of request query `index` (`name`, importing the published query `published`): admitted (with its
/// admission), refused (with why) or a framework error; `session` names the full record.
fn query_outcome(root: &Path, index: usize, name: Option<&str>, published: &str, outcome: Value) -> Value {
    let qualified = outcome["qualification"][0]["result"]["qualified"] == true;
    let status = match outcome["status"].as_str() {
        Some("closed") if qualified => "admitted",
        Some("framework_error" | "accounting_unresolved") => "framework_error",
        _ => "refused",
    };
    let error = [&outcome["qualification"][0]["result"]["error"], &outcome["trajectory"][0]["evaluation"]["error"], &outcome["error"]]
        .into_iter()
        .find(|e| !e.is_null())
        .cloned()
        .unwrap_or(Value::Null);
    json!({"query":name.map(str::to_string).unwrap_or_else(|| format!("query-{index:04}")),"status":status,
        "published_query":published,
        "admission":outcome["qualification"][0]["result"]["admission"],"error":if status == "admitted" { Value::Null } else { error },
        "resumable":status == "framework_error","session":query_directory(root, index).join("summary.json")})
}
