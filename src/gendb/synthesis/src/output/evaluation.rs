//! The final evaluation (`gendb evaluate REQUEST.json BINDINGS.json HOME`): every named query of a workload
//! request is served from its admitted package at every binding of a named binding file (the hidden random bindings,
//! `bindings/hidden.json`) and every configured worker count, with the unchanged protocol: one child per
//! cell runs 1 warm + 3 hot library calls; the cell's time is the median of the 3 hot wall times. Every cell holds the
//! exclusive timing lease of the request's host locks, so no timing overlaps another measurement or a build.
//!
//! Results: `HOME/evaluation/README.md` (per query, binding and worker count: GenDB median, and the baseline target
//! when `HOME/baselines/hidden_results.json` has one) and `HOME/records/evaluation/<query>.json` (every cell: the four
//! wall times, the served answer and the records it came from). No synthesis, proof, build or reference comparison.
//!
//! Binding file (written by the baseline worker): `{"queries": {"Q01": [{"binding_id": "h0", "arguments":
//! ["1998-09-02"]}, ..]}}`; a query named `q01` in the request reads key `Q01`. `arguments` are the argument texts of the
//! free parameters in slot order; instead, `params` may map parameter names (the request's `parameters[].name`) to values.
//! JSON numbers are taken as their text.

use super::{OutputError, io_error, ms, read_json, write_home_readme, write_json, write_text};
use crate::controller::request::WorkloadRequest;
use gendb_artifacts::ObjectStore;
use gendb_frontend::params::arguments_by_name;
use gendb_frontend::parser::SqlParser;
use gendb_runtime::serve::{AdmittedPackage, WorkerExecutor, admitted_package, serve};
use gendb_storage::import::PreparedSource;
use gendb_storage::versions::CurrentCapture;
use gendb_verification::admission::execution::{CHILD_TIMEOUT_SECONDS, RANGE_CAPACITY};
use gendb_verification::admission::prepare_statement;
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::path::Path;

/// Calls per cell: 1 warm, then the hot ones.
const CALLS_PER_CELL: u32 = 4;

/// Evaluate every named query of the workload request at `request_path` over the bindings at `bindings_path`, writing
/// into the output `home`. `worker` is the gendb executable (run as `gendb worker`). Returns the summary record.
pub fn evaluate(request_path: &Path, bindings_path: &Path, home: &Path, worker: &Path) -> Result<Value, OutputError> {
    let request: WorkloadRequest = serde_json::from_str(&std::fs::read_to_string(request_path).map_err(|e| io_error(request_path, e))?)
        .map_err(|e| io_error(request_path, e))?;
    request.validate().map_err(|e| OutputError(format!("request: {e}")))?;
    let bindings = read_json(bindings_path).ok_or_else(|| OutputError(format!("{}: not a JSON binding file", bindings_path.display())))?;
    let prepared = request.prepared_workload.as_deref().ok_or_else(|| OutputError("evaluation needs prepared_workload (the prepared source of the synthesis run)".into()))?;
    let source = PreparedSource::open(prepared, &request.dataset).map_err(|e| OutputError(format!("prepared source: {e}")))?;
    let parser = SqlParser::from_environment().map_err(|e| OutputError(format!("frontend: {e}")))?;
    let store = ObjectStore::open_existing(&request.library).map_err(|e| io_error(&request.library, e))?;
    let current = CurrentCapture::of(&source).map_err(|e| OutputError(format!("current capture: {e}")))?;
    let baselines = read_json(&home.join("baselines/hidden_results.json")).unwrap_or(Value::Null);
    let work = home.join("records/evaluation/work");
    let mut summary = vec![];
    for query in &request.queries {
        let Some(name) = query.name.as_deref() else { continue };
        let key = binding_key(name, &bindings["queries"]);
        let cells = evaluate_query(&EvaluationContext { request: &request, parser: &parser, store: &store, source: &source, current: &current, worker, work: &work.join(name) }, query, &bindings["queries"][&key])?;
        let record = json!({"query":name,"bindings_key":key,"bindings_file":bindings_path,"protocol":"1 warm + 3 hot library calls in one worker child per cell; median of the 3 hot wall times; exclusive timing lease per cell",
            "cells":cells});
        write_json(&home.join("records/evaluation").join(format!("{name}.json")), &record)?;
        summary.push((name.to_string(), key, cells));
    }
    write_text(&home.join("evaluation/README.md"), &readme(&summary, &baselines, bindings_path))?;
    write_text(&home.join("records/evaluation/README.md"), "# Evaluation records\n\nOne `<query>.json` per query: every cell's four wall times (warm first), median, served answer and package records. `work/` holds the worker children's evidence.\n")?;
    write_home_readme(home)?;
    Ok(json!({"queries":summary.iter().map(|(n, _, c)| json!({"query":n,"cells":c.len(),"executed":c.iter().filter(|x| x["status"] == "executed").count()})).collect::<Vec<_>>()}))
}

/// The binding-file key of a query name: `q1`/`q01` -> `Q01` (the TPC-H files), or `Q1` when `queries` (the file's
/// `queries`) has that key and not `Q01` (the SEC-EDGAR files); other names unchanged.
fn binding_key(name: &str, queries: &Value) -> String {
    match name.strip_prefix(['q', 'Q']).and_then(|n| n.parse::<u32>().ok()) {
        Some(n) if queries.get(format!("Q{n:02}")).is_none() && queries.get(format!("Q{n}")).is_some() => format!("Q{n}"),
        Some(n) => format!("Q{n:02}"),
        None => name.to_string(),
    }
}

struct EvaluationContext<'a> {
    request: &'a WorkloadRequest,
    parser: &'a SqlParser,
    store: &'a ObjectStore,
    source: &'a PreparedSource,
    current: &'a CurrentCapture,
    worker: &'a Path,
    work: &'a Path,
}

/// Every cell of one query: each binding of `bindings` (the query's array of the binding file) at each worker count.
fn evaluate_query(cx: &EvaluationContext<'_>, query: &crate::controller::request::QueryRequest, bindings: &Value) -> Result<Vec<Value>, OutputError> {
    let unsupported = |reason: String| Ok(vec![json!({"status":"unsupported","reason":reason})]);
    let statement = match prepare_statement(cx.parser, cx.source.dataset(), cx.request.integrity_constraints.as_ref(), &query.sql, &query.parameters, &[], &[], &cx.work.join("statement")) {
        Ok(s) => s,
        Err(refused) => return unsupported(refused.error.to_string()),
    };
    let admitted = admitted_package(cx.store, &statement.instance).map_err(|e| OutputError(e.to_string()))?;
    // Under fixed_flat only packages over the prepared flat storages, without static items, are measured.
    if cx.request.storage_policy.is_fixed_flat()
        && let Some(admitted) = &admitted
        && let Some(reason) = crate::storage::flat::served_package_refusal(cx.store, cx.current, admitted).map_err(|e| OutputError(e.to_string()))?
    {
        return unsupported(reason);
    }
    match admitted {
        None => return unsupported("no admitted package for this statement".into()),
        Some(AdmittedPackage::StoredDataV4 { resolved, .. }) => {
            let uses = resolved.package.storage_uses.iter().map(|u| (u.name.as_str(), u.package));
            if let Some(reason) = cx.request.storage_policy.ineligible_use(cx.store, uses).map_err(|e| OutputError(e.to_string()))? {
                return unsupported(reason);
            }
        }
        Some(AdmittedPackage::SavedV3 { .. }) => {}
    }
    let list = bindings.as_array().cloned().unwrap_or_default();
    if list.is_empty() {
        return unsupported("the binding file has no bindings for this query".into());
    }
    let mut cells = vec![];
    for binding in &list {
        let id = binding["binding_id"].as_str().unwrap_or("?").to_string();
        let text = |v: &Value| v.as_str().map(String::from).unwrap_or_else(|| v.to_string());
        let texts = match binding["arguments"].as_array() {
            Some(arguments) => Ok(arguments.iter().map(text).collect()),
            None => {
                let named: BTreeMap<String, String> = binding["params"].as_object().into_iter().flatten().map(|(k, v)| (k.clone(), text(v))).collect();
                arguments_by_name(&query.parameters, &named)
            }
        };
        let texts = match texts {
            Ok(t) => t,
            Err(reason) => {
                cells.push(json!({"binding":id,"status":"unsupported","reason":reason}));
                continue;
            }
        };
        for workers in &cx.request.hardware.threads {
            cells.push(measure_cell(cx, &statement.instance, &id, &texts, *workers)?);
        }
    }
    Ok(cells)
}

/// One cell under the exclusive timing lease: 1 warm + 3 hot calls in one child.
fn measure_cell(cx: &EvaluationContext<'_>, instance: &gendb_frontend::params::Instance, binding: &str, texts: &[String], workers: usize) -> Result<Value, OutputError> {
    let executor = WorkerExecutor::new(cx.worker, &cx.work.join(binding), CHILD_TIMEOUT_SECONDS, RANGE_CAPACITY, CALLS_PER_CELL);
    let _lease = cx.request.host_locks.timing().map_err(|e| OutputError(format!("timing lease: {e}")))?;
    let access = cx.request.part_access.unwrap_or_default();
    let mut cell = match serve(cx.store, instance, texts, cx.current, access, &executor, workers as u32) {
        Ok(served) => {
            let walls: Vec<u64> = executor.calls().iter().map(|c| c.usage.wall_ns).collect();
            let mut hot: Vec<u64> = walls.iter().skip(1).copied().collect();
            hot.sort_unstable();
            let median = (hot.len() == 3).then(|| hot[1]);
            let record = served.record().map_err(|e| OutputError(e.to_string()))?;
            json!({"status":"executed","wall_ns":walls,"median_ns":median,"answer":record["answer"],"package":record["package"],"claim":record["claim"],
                "storage_assets":record["storage_assets"],"dispatch":record["dispatch"]})
        }
        Err(reason) => json!({"status":"unsupported","reason":reason.to_string()}),
    };
    cell["binding"] = json!(binding);
    cell["arguments"] = json!(texts);
    cell["workers"] = json!(workers);
    cell["part_access"] = json!(access);
    Ok(cell)
}

/// `evaluation/README.md`: per query a table of binding x worker count with the GenDB median and, when the baselines
/// file has the cell, the target (fastest baseline) and the speedup.
fn readme(summary: &[(String, String, Vec<Value>)], baselines: &Value, bindings_path: &Path) -> String {
    let mut t = format!(
        "# Final evaluation\n\nGenDB served from the admitted packages at the hidden bindings (`{}`), 1 warm + 3 hot library calls per cell, median of the hot calls, one cell at a time under the timing lock. Targets: the fastest of DuckDB and Umbra on the same bindings (`baselines/hidden_results.json`), when present. Raw cells: `records/evaluation/<query>.json`.\n\n**Timing boundaries differ.** A GenDB cell is the wall time of one call of the admitted query library inside the worker process, over stored parts already mapped (no process start, no plan or compile step, no client transfer; the answer is returned as the result wire, not fetched by a client). A baseline cell is the engine's prepared EXECUTE plus fetching every result row into the client (for Umbra including the client connection's IPC). Answers are not compared here.\n",
        bindings_path.display()
    );
    let mut speedups = vec![];
    for (name, key, cells) in summary {
        t.push_str(&format!("\n## {name}\n\n| Binding | Workers | GenDB ms | Target ms | Speedup |\n|---|---:|---:|---:|---:|\n"));
        for c in cells {
            let binding = c["binding"].as_str().unwrap_or("-");
            let workers = c["workers"].as_u64().map(|w| w.to_string()).unwrap_or_else(|| "-".into());
            let median = c["median_ns"].as_u64();
            let target_ms = baselines[key][binding][&workers]["target_ms"].as_f64();
            let speedup = match (median, target_ms) {
                (Some(m), Some(t)) if m > 0 => Some(t * 1e6 / m as f64),
                _ => None,
            };
            speedups.extend(speedup);
            let status = if c["status"] == "executed" { median.map(ms).unwrap_or_else(|| "-".into()) } else { format!("{} ({})", c["status"].as_str().unwrap_or("?"), c["reason"].as_str().unwrap_or("")) };
            t.push_str(&format!(
                "| {binding} | {workers} | {status} | {} | {} |\n",
                target_ms.map(|x| format!("{x:.3}")).unwrap_or_else(|| "-".into()),
                speedup.map(|s| format!("{s:.2}x")).unwrap_or_else(|| "-".into())
            ));
        }
    }
    if !speedups.is_empty() {
        let geomean = (speedups.iter().map(|s| s.ln()).sum::<f64>() / speedups.len() as f64).exp();
        t.push_str(&format!("\nGeometric mean speedup over {} cells with a target: {geomean:.2}x.\n", speedups.len()));
    }
    t
}

#[cfg(test)]
mod tests {
    use super::*;

    /// TPC-H files key `Q01`, the SEC-EDGAR files `Q1`; a name the file lacks keeps the padded form.
    #[test]
    fn binding_keys_follow_the_file() {
        let tpch = json!({"Q01": [], "Q22": []});
        let sec = json!({"Q1": [], "Q24": []});
        assert_eq!([binding_key("q01", &tpch), binding_key("q1", &tpch), binding_key("q22", &tpch)], ["Q01", "Q01", "Q22"]);
        assert_eq!([binding_key("q1", &sec), binding_key("q24", &sec), binding_key("q3", &sec)], ["Q1", "Q24", "Q03"]);
        assert_eq!(binding_key("readings-count", &sec), "readings-count");
    }
}
