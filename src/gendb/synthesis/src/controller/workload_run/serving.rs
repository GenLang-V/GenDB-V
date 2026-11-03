//! The serving route (`gendb serve`): every requested statement is served from its admitted package at every requested
//! argument binding and worker count, over an existing prepared source. No author, synthesis, proof, build or
//! reference comparison. Stored parts are mapped with the request's optional `part_access` advice (default: normal
//! readahead, no page drop), recorded per cell. Under a `physical_only` storage policy a package that reads a storage
//! the policy excludes is not served (`storage::policy`).

use super::WorkloadError;
use super::lifecycle::{Route, latest_summary, publish_summary, record_request, record_route};
use crate::controller::records;
use crate::controller::request::WorkloadRequest;
use crate::query::serving::{ServeRequest, serve_statement};
use gendb_artifacts::ObjectStore;
use gendb_frontend::parser::SqlParser;
use gendb_storage::import::PreparedSource;
use serde_json::{Value, json};
use std::path::Path;
use std::time::Instant;

/// Serve `request` in the run directory `root` with `worker` (the gendb executable) running each package. A restart
/// of a run that already published a summary returns that summary.
pub fn serve_workload(request: &WorkloadRequest, root: &Path, worker: &Path) -> Result<Value, WorkloadError> {
    request.validate()?;
    let prepared = request
        .prepared_workload
        .as_deref()
        .ok_or_else(|| WorkloadError::invalid("serving requires prepared_workload: source preparation happens at synthesis, not while serving"))?;
    records::create_dir(root)?;
    let root = root.canonicalize().map_err(|e| records::RecordError::new(root, e))?;
    record_route(&root, Route::Serving)?;
    if record_request(&root, &serde_json::to_value(request).map_err(|e| WorkloadError::invalid(e.to_string()))?)?
        && let Some(summary) = latest_summary(&root)?
    {
        return Ok(summary);
    }
    let waiting = Instant::now();
    let _lease = request.host_locks.activity().map_err(WorkloadError::HostLocks)?;
    let queue_ns = waiting.elapsed().as_nanos();
    let started = Instant::now();
    let mut result = match PreparedSource::open(prepared, &request.dataset) {
        Err(reason) => json!({"status":"unsupported","reason":reason.to_string()}),
        Ok(source) => serve_statements(request, &root, &source, worker)?,
    };
    result["synthesis_disabled"] = json!(true);
    for zero in ["author_inspections", "author_dispatches", "persistent_builds", "reference_comparisons"] {
        result[zero] = json!(0);
    }
    result["reported_cost_usd"] = json!("0");
    result["queue_ns"] = json!(queue_ns);
    result["machine_ns"] = json!(started.elapsed().as_nanos());
    publish_summary(&root, &result)?;
    Ok(result)
}

fn serve_statements(request: &WorkloadRequest, root: &Path, source: &PreparedSource, worker: &Path) -> Result<Value, WorkloadError> {
    let parser = SqlParser::from_environment().map_err(WorkloadError::Frontend)?;
    let store = ObjectStore::open_existing(&request.library).map_err(|e| WorkloadError::invalid(format!("library {}: {e}", request.library.display())))?;
    let mut cells = vec![];
    for (index, query) in request.queries.iter().enumerate() {
        let serve = ServeRequest {
            sql: &query.sql,
            parameters: &query.parameters,
            integrity_constraints: request.integrity_constraints.as_ref(),
            arguments: &query.arguments,
            storage_policy: &request.storage_policy,
        };
        let work = root.join("verus-serving").join(format!("query-{index:04}"));
        cells.extend(serve_statement(&parser, &store, source, &serve, worker, &request.hardware.threads, request.part_access.unwrap_or_default(), &work).map_err(WorkloadError::Serving)?);
    }
    let all_executed = cells.iter().all(|cell| cell["status"] == "executed");
    Ok(json!({"status":if all_executed {"executed"} else {"unsupported"},"queries":cells,"source_version":source.source_snapshot(),
        "storage_policy":request.storage_policy.kind()}))
}
