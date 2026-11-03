//! The user's benchmark inputs of a request: each query's visible benchmark bindings (from a
//! bindings file in the layout of the TPC-H `bindings/visible.json`, `gendb.tpch.bindings.v1`; a concrete statement
//! lists one binding without arguments) and its runtime targets (from the baselines file
//! `baselines/targets.json`: per query, binding and worker count the DuckDB and Umbra hot medians and `target_ms`, the
//! faster one), written into each query's `objective` as an execution-time objective with the user's early stop.
//!
//! Only visible bindings reach authors: a bindings file whose `kind` is not `visible` is refused, so hidden evaluation
//! bindings can never become benchmark bindings of a synthesis request.
//!
//! Every target's provenance ends with the setting the baselines ran in: the targets file's optional top-level
//! `baseline_setting` text (for example `"untuned, SEC-EDGAR keys declared"`), or, when the file has none (the TPC-H
//! baselines file), [`TPCH_BASELINE_SETTING`], so TPC-H requests are written as before the field existed.
//!
//! A provenance names only the engines the cell has a time of (`duckdb_ms`, `umbra_ms`): both, as "the faster of
//! DuckDB (..) and Umbra (..)"; or one (the DuckDB helper's targets file, `baselines/duckdb_baselines.py`), as
//! "DuckDB (..)", and that target then names its system ([`RuntimeTarget::system`]), so the author's goal and target
//! table name that one engine.

use super::request::{QueryObjective, WorkloadRequest};
use crate::prompts::{EarlyStop, RuntimeTarget};
use gendb_verification::admission::BenchmarkBinding;
use serde_json::Value;

/// The baseline setting of a targets file without `baseline_setting`: the TPC-H SF100 baselines.
pub const TPCH_BASELINE_SETTING: &str = "untuned, TPC-H keys declared";

/// Set the objective of every query of `request` whose benchmark key (`keys[i]`, for example `Q01`; empty: leave the
/// query as it is) is in `visible` and `targets`: its visible bindings, a target per (binding, configured worker
/// count), and the early stop at `min_speedup`. A concrete statement (no free parameter) has exactly one visible
/// binding, without arguments: its targets are those of that binding, written for the statement's implicit binding
/// (no `binding` name, no `objective.bindings`), as the request's objective rules require.
pub fn apply_benchmark_inputs(request: &mut WorkloadRequest, keys: &[String], visible: &Value, targets: &Value, targets_file: &str, min_speedup: u32) -> Result<(), String> {
    if visible["kind"] != "visible" {
        return Err(format!("the bindings file has kind {}; only visible bindings may be given to authors", visible["kind"]));
    }
    if keys.len() != request.queries.len() {
        return Err(format!("{} keys for {} queries", keys.len(), request.queries.len()));
    }
    let setting = baseline_setting(targets, targets_file)?;
    let threads = request.hardware.threads.clone();
    for (query, key) in request.queries.iter_mut().zip(keys).filter(|(_, key)| !key.is_empty()) {
        let listed = visible["queries"][key.as_str()].as_array().ok_or_else(|| format!("{key}: no visible bindings"))?;
        let template = query.is_template();
        let mut bindings = vec![];
        let mut cells = vec![];
        for binding in listed {
            let name = binding["binding_id"].as_str().ok_or_else(|| format!("{key}: a binding without binding_id"))?.to_string();
            let arguments: Vec<String> = serde_json::from_value(binding["arguments"].clone()).map_err(|e| format!("{key} {name}: arguments: {e}"))?;
            if !template && (listed.len() != 1 || !arguments.is_empty()) {
                return Err(format!("{key}: a concrete statement takes exactly one visible binding, without arguments"));
            }
            for &workers in &threads {
                let cell = &targets[key.as_str()][name.as_str()][workers.to_string()];
                let target_ms = cell["target_ms"].as_f64().ok_or_else(|| format!("{key} {name} @ {workers}: no target_ms in {targets_file}"))?;
                let timed = TargetSource::timed_engines(cell);
                if timed.is_empty() {
                    return Err(format!("{key} {name} @ {workers}: no engine time (duckdb_ms, umbra_ms) in {targets_file}"));
                }
                let provenance = TargetSource::provenance(targets_file, key, &name, workers, &timed, setting);
                // One engine's time: the target names that engine as its system (the goal then names it alone).
                let system = (timed.len() == 1).then(|| timed[0].0.to_string());
                cells.push(RuntimeTarget {
                    binding: template.then(|| name.clone()),
                    workers,
                    median_ns: (target_ms * 1e6).round() as u64,
                    provenance,
                    timing_scope: "median of 3 hot runs after 1 warm run, wall clock of query execution including result fetch".into(),
                    system,
                });
            }
            if template {
                bindings.push(BenchmarkBinding { name, arguments });
            }
        }
        query.objective = QueryObjective::ExecutionTime { bindings, targets: cells, early_stop: Some(EarlyStop { min_speedup }) };
    }
    Ok(())
}

/// The targets file's `baseline_setting` (a non-empty string), or [`TPCH_BASELINE_SETTING`] when the field is absent.
fn baseline_setting<'a>(targets: &'a Value, targets_file: &str) -> Result<&'a str, String> {
    match targets.get("baseline_setting") {
        None => Ok(TPCH_BASELINE_SETTING),
        Some(Value::String(text)) if !text.trim().is_empty() => Ok(text),
        Some(other) => Err(format!("{targets_file}: baseline_setting must be a non-empty string, found {other}")),
    }
}

/// The engines a target file can compare, each with the field of its time in a cell, in the order a provenance names
/// them.
const TARGET_ENGINES: [(&str, &str); 2] = [("DuckDB", "duckdb_ms"), ("Umbra", "umbra_ms")];

/// What the provenance of a runtime target from a baselines file states (written by [`TargetSource::provenance`],
/// read back by [`TargetSource::parse`] for the prompts): the file, the benchmark key, the binding, the worker count,
/// each engine's hot median in ms (as written) and the closing remark, the baseline setting (for example "untuned,
/// TPC-H keys declared").
#[derive(Clone, Debug, PartialEq)]
pub struct TargetSource {
    pub file: String,
    pub key: String,
    pub binding: String,
    pub workers: usize,
    /// `(engine, ms)` in the order written.
    pub engine_ms: Vec<(String, String)>,
    pub remark: String,
}

impl TargetSource {
    /// The engines with a time in `cell` (its `duckdb_ms` / `umbra_ms` numbers), with that time, in provenance order.
    fn timed_engines(cell: &Value) -> Vec<(&'static str, &Value)> {
        TARGET_ENGINES.iter().filter(|(_, field)| cell[*field].is_number()).map(|(engine, field)| (*engine, &cell[*field])).collect()
    }

    /// The provenance text of one target cell from its timed engines (one or both, [`TargetSource::timed_engines`]);
    /// `setting` is the baseline setting that closes it.
    fn provenance(file: &str, key: &str, binding: &str, workers: usize, timed: &[(&str, &Value)], setting: &str) -> String {
        let engines: Vec<String> = timed.iter().map(|(engine, ms)| format!("{engine} ({ms})")).collect();
        let comparison = if engines.len() == 1 { engines[0].clone() } else { format!("the faster of {}", engines.join(" and ")) };
        format!("{file} {key} {binding} {workers} threads: {comparison} ms, {setting}")
    }

    /// The parts of a provenance written by [`TargetSource::provenance`] (both engines or one); `None` for any other text.
    pub fn parse(provenance: &str) -> Option<TargetSource> {
        let (cell, comparison) = provenance.split_once(" threads: ")?;
        let mut words = cell.rsplitn(4, ' ');
        let workers = words.next()?.parse().ok()?;
        let binding = words.next()?.to_string();
        let key = words.next()?.to_string();
        let file = words.next()?.to_string();
        let (engines, remark) = comparison.split_once(" ms, ")?;
        let (parts, expected): (Vec<&str>, usize) = match engines.strip_prefix("the faster of ") {
            Some(both) => (both.split(" and ").collect(), TARGET_ENGINES.len()),
            None => (vec![engines], 1),
        };
        let mut engine_ms = vec![];
        for part in parts {
            let (engine, _) = TARGET_ENGINES.iter().find(|(engine, _)| part.starts_with(engine))?;
            let ms = part.strip_prefix(engine)?.trim().strip_prefix('(')?.strip_suffix(')')?;
            engine_ms.push((engine.to_string(), ms.to_string()));
        }
        (engine_ms.len() == expected).then(|| TargetSource { file, key, binding, workers, engine_ms, remark: remark.to_string() })
    }

    /// The engine whose time set the target (the faster one; both names when they tie).
    pub fn setting_engine(&self) -> String {
        let times: Vec<(&str, f64)> = self.engine_ms.iter().filter_map(|(engine, ms)| Some((engine.as_str(), ms.parse().ok()?))).collect();
        let fastest = times.iter().map(|(_, ms)| *ms).fold(f64::INFINITY, f64::min);
        times.iter().filter(|(_, ms)| *ms == fastest).map(|(engine, _)| *engine).collect::<Vec<_>>().join(" = ")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn target_provenance_reads_back_with_its_setting_engine() {
        let text = TargetSource::provenance("/b/targets.json", "Q06", "v0", 32, &TargetSource::timed_engines(&json!({"duckdb_ms": 45.299, "umbra_ms": 46.1})), TPCH_BASELINE_SETTING);
        assert_eq!(text, "/b/targets.json Q06 v0 32 threads: the faster of DuckDB (45.299) and Umbra (46.1) ms, untuned, TPC-H keys declared", "the TPC-H text is unchanged");
        let source = TargetSource::parse(&text).unwrap();
        assert_eq!((source.file.as_str(), source.key.as_str(), source.binding.as_str(), source.workers), ("/b/targets.json", "Q06", "v0", 32));
        assert_eq!(source.engine_ms, [("DuckDB".to_string(), "45.299".to_string()), ("Umbra".to_string(), "46.1".to_string())]);
        assert_eq!((source.setting_engine().as_str(), source.remark.as_str()), ("DuckDB", "untuned, TPC-H keys declared"));
        assert_eq!(TargetSource::parse("fixture engine, fixture host"), None);
    }

    /// A targets file names its own baseline setting; one without the field (the TPC-H file) keeps the TPC-H text, and
    /// a malformed field is refused rather than written into author inputs.
    #[test]
    fn baseline_setting_comes_from_the_targets_file() {
        let tpch = json!({"Q06": {"v0": {"1": {"target_ms": 1.0}}}});
        assert_eq!(baseline_setting(&tpch, "t.json"), Ok(TPCH_BASELINE_SETTING));
        let sec = json!({"baseline_setting": "untuned, SEC-EDGAR keys declared", "Q4": {}});
        assert_eq!(baseline_setting(&sec, "t.json"), Ok("untuned, SEC-EDGAR keys declared"));
        let text = TargetSource::provenance("/s/targets.json", "Q4", "v1", 1, &TargetSource::timed_engines(&json!({"duckdb_ms": 10.5, "umbra_ms": 9.25})), baseline_setting(&sec, "t.json").unwrap());
        let source = TargetSource::parse(&text).unwrap();
        assert_eq!((source.key.as_str(), source.setting_engine().as_str(), source.remark.as_str()), ("Q4", "Umbra", "untuned, SEC-EDGAR keys declared"));
        for bad in [json!({"baseline_setting": ""}), json!({"baseline_setting": 3})] {
            assert!(baseline_setting(&bad, "t.json").unwrap_err().starts_with("t.json: baseline_setting must be a non-empty string"));
        }
    }

    /// A template gets named benchmark bindings and per-binding targets (as for TPC-H); a concrete statement gets its
    /// one visible binding's targets on its implicit binding, so the written request passes the objective rules.
    #[test]
    fn templates_and_concrete_statements_get_valid_objectives() {
        let limits = json!(crate::controller::limits::tests::limits());
        let request = |concrete_bindings: Value| -> (WorkloadRequest, Value) {
            let request: WorkloadRequest = serde_json::from_value(json!({"format_version":2,"dataset":{"tables":[]},
                "queries":[{"sql":"SELECT $1","limits":limits,"parameters":[{"index":1,"type":"integer","binding":{"free":{}}}]},
                           {"sql":"SELECT 1","limits":limits}],
                "hardware":{"threads":[1,4]},"max_concurrent_queries":1,"author_executable":"claude","library":"library",
                "barriers":{"activity_lock":"/l/a","build_lock":"/l/b","race_lock":"/l/r"}})).unwrap();
            let visible = json!({"kind":"visible","queries":{"Q2":[{"binding_id":"v0","arguments":["2022"]},{"binding_id":"v1","arguments":["2023"]}],
                "Q1":concrete_bindings}});
            (request, visible)
        };
        let cell = json!({"1":{"duckdb_ms":2.0,"umbra_ms":1.0,"target_ms":1.0},"4":{"duckdb_ms":1.0,"umbra_ms":1.5,"target_ms":1.0}});
        let targets = json!({"baseline_setting":"untuned, SEC-EDGAR keys declared","Q2":{"v0":cell,"v1":cell},"Q1":{"v0":cell}});
        let keys = ["Q2".to_string(), "Q1".to_string()];

        let (mut written, visible) = request(json!([{"binding_id":"v0","arguments":[]}]));
        apply_benchmark_inputs(&mut written, &keys, &visible, &targets, "/s/targets.json", 5).unwrap();
        written.validate().unwrap();
        let (template, concrete) = (&written.queries[0].objective, &written.queries[1].objective);
        assert_eq!(template.benchmark_bindings().iter().map(|b| b.name.as_str()).collect::<Vec<_>>(), ["v0", "v1"]);
        assert!(template.runtime_targets().iter().all(|t| t.binding.is_some()) && template.runtime_targets().len() == 4);
        assert!(concrete.benchmark_bindings().is_empty() && concrete.runtime_targets().len() == 2);
        assert!(concrete.runtime_targets().iter().all(|t| t.binding.is_none() && t.provenance.ends_with("ms, untuned, SEC-EDGAR keys declared")));

        for listed in [json!([{"binding_id":"v0","arguments":[]},{"binding_id":"v1","arguments":[]}]), json!([{"binding_id":"v0","arguments":["1"]}])] {
            let (mut refused, visible) = request(listed);
            let error = apply_benchmark_inputs(&mut refused, &keys, &visible, &targets, "/s/targets.json", 5).unwrap_err();
            assert_eq!(error, "Q1: a concrete statement takes exactly one visible binding, without arguments");
        }
    }

    /// A cell with DuckDB's time only (the DuckDB helper's targets file) names DuckDB alone, and its target names DuckDB
    /// as its system; a cell with no engine time is refused.
    #[test]
    fn a_single_engine_cell_names_only_that_engine() {
        let limits = json!(crate::controller::limits::tests::limits());
        let mut request: WorkloadRequest = serde_json::from_value(json!({"format_version":2,"dataset":{"tables":[]},
            "queries":[{"sql":"SELECT $1","limits":limits,"parameters":[{"index":1,"type":"integer","binding":{"free":{}}}]}],
            "hardware":{"threads":[1]},"max_concurrent_queries":1,"author_executable":"claude","library":"library",
            "barriers":{"activity_lock":"/l/a","build_lock":"/l/b","race_lock":"/l/r"}})).unwrap();
        let visible = json!({"kind":"visible","queries":{"Q1":[{"binding_id":"v0","arguments":["4"]}]}});
        let targets = json!({"baseline_setting":"DuckDB 1.5.6, keys declared","Q1":{"v0":{"1":{"duckdb_ms":12.5,"target_ms":12.5,"agreement":"single_engine"}}}});
        apply_benchmark_inputs(&mut request, &["Q1".to_string()], &visible, &targets, "/w/targets.json", 5).unwrap();
        request.validate().unwrap();
        let target = &request.queries[0].objective.runtime_targets()[0];
        assert_eq!(target.provenance, "/w/targets.json Q1 v0 1 threads: DuckDB (12.5) ms, DuckDB 1.5.6, keys declared");
        assert_eq!((target.system.as_deref(), target.set_by().as_str()), (Some("DuckDB"), "DuckDB"));
        let source = TargetSource::parse(&target.provenance).unwrap();
        assert_eq!((source.engine_ms.len(), source.setting_engine().as_str(), source.remark.as_str()), (1, "DuckDB", "DuckDB 1.5.6, keys declared"));
        let untimed = json!({"Q1":{"v0":{"1":{"target_ms":12.5}}}});
        let error = apply_benchmark_inputs(&mut request, &["Q1".to_string()], &visible, &untimed, "/w/targets.json", 5).unwrap_err();
        assert_eq!(error, "Q1 v0 @ 1: no engine time (duckdb_ms, umbra_ms) in /w/targets.json");
    }
}
