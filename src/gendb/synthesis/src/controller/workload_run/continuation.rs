//! The workload checks of `queries[i].continue_from`, made right after the statement is prepared and before any data
//! preparation or preflight. The named directory must be the closed query session `<run>/queries/query-NNNN` of an
//! earlier synthesis run (`controller::reselect::closed_source`) that admitted exactly one candidate whose frozen copy
//! it retains (`query::incumbent::admitted_candidate`). That run's request must have asked for the same statement under
//! the same correctness conditions: SQL text, parameters with their modes and domains, admission bindings and storage
//! policy kind. The objective (benchmark bindings, targets, early stop), worker counts, limits and data allowance may
//! differ: the incumbent is frozen and evaluated afresh in this run, under this run's policy and budget. The session's
//! recorded statement key must be this prepared statement's (schema, statement, parameters, output). Each mismatch is
//! named (`continue_source_invalid: <what>`) and refuses the query before any author or framework work.

use super::reselection::source_run;
use crate::controller::records;
use crate::controller::request::WorkloadRequest;
use crate::controller::reselect::closed_source;
use crate::query::incumbent::{SOURCE_REFUSAL, admitted_candidate};
use serde_json::Value;
use std::path::PathBuf;

/// Check query `index`'s `continue_from` against its prepared statement (`statement_key`: its key v4): the canonical
/// source session directory, or the named refusal.
pub fn check_source(request: &WorkloadRequest, index: usize, statement_key: &str) -> Result<PathBuf, String> {
    let query = &request.queries[index];
    let named = query.continue_from.as_deref().ok_or_else(|| format!("{SOURCE_REFUSAL}: queries[{index}] names no source session"))?;
    let renamed = |error: String| error.replacen(crate::controller::reselect::SOURCE_REFUSAL, SOURCE_REFUSAL, 1);
    let source = named.canonicalize().map_err(|e| format!("{SOURCE_REFUSAL}: {}: {e}", named.display()))?;
    let (run, source_index) = source_run(&source).map_err(renamed)?;
    closed_source(&source).map_err(renamed)?;
    let recorded: WorkloadRequest = records::read_json(&run.join("request.json")).map_err(|e| format!("{SOURCE_REFUSAL}: the source run's request: {e}"))?;
    let earlier = recorded.queries.get(source_index).ok_or_else(|| format!("{SOURCE_REFUSAL}: the source run's request has no query {source_index}"))?;
    let differences = [
        ("sql", earlier.sql == query.sql),
        ("parameters (modes and domains)", earlier.parameters == query.parameters),
        ("test_bindings (admission bindings)", earlier.test_bindings == query.test_bindings),
        ("storage_policy kind", recorded.storage_policy.kind() == request.storage_policy.kind()),
    ];
    if let Some((field, _)) = differences.iter().find(|(_, same)| !same) {
        return Err(format!("{SOURCE_REFUSAL}: {field} of queries[{index}] differs from the source run's queries[{source_index}] ({})", run.display()));
    }
    let context: Value = records::read_json(&source.join("context.json")).map_err(|e| format!("{SOURCE_REFUSAL}: the source session's context: {e}"))?;
    if context["statement_key"].as_str() != Some(statement_key) {
        return Err(format!(
            "{SOURCE_REFUSAL}: the source session's statement key {} is not this statement's {statement_key} (schema, statement, parameters or output differ)",
            context["statement_key"]
        ));
    }
    admitted_candidate(&source)?;
    Ok(source)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::controller::ledger::Ledger;
    use crate::controller::limits::tests::limits;
    use crate::controller::test_support::scratch_root;
    use serde_json::json;

    /// A request over one template query (paths absolute), continuing from `source` when given.
    fn recorded(root: &std::path::Path, continue_from: Option<&std::path::Path>) -> Value {
        let mut query = json!({"sql":"SELECT 1 WHERE $1 > 0","limits":limits(),
            "parameters":[{"index":1,"type":"integer","binding":{"free":{}}}],"test_bindings":[["3"]],
            "objective":{"kind":"execution_time","bindings":[{"name":"b","arguments":["5"]}]}});
        if let Some(source) = continue_from {
            query["continue_from"] = json!(source);
        }
        json!({"format_version":2,"dataset":{"tables":[]},"queries":[query],"hardware":{"threads":[1,4]},"max_concurrent_queries":1,
            "author_executable":"claude","library":root.join("library"),
            "barriers":{"activity_lock":root.join("a.lock"),"build_lock":root.join("b.lock"),"race_lock":root.join("r.lock")},
            "storage_policy":{"kind":"physical_only"}})
    }

    /// A closed source session of query 0 with statement key `k`; with `admitted`, iteration 1 qualified with its
    /// frozen records retained.
    fn source_run(root: &std::path::Path, admitted: bool) -> PathBuf {
        let session = root.join("earlier/queries/query-0000");
        records::create_dir(&session).unwrap();
        records::write_new_json(&root.join("earlier/request.json"), &recorded(root, None)).unwrap();
        records::write_new_json(&session.join("context.json"), &json!({"statement_key":"k"})).unwrap();
        let mut ledger = Ledger::open(&session, json!({"request":{"task":{"sql":"q"}}}), limits()).unwrap();
        ledger.state.closed = Some(json!({"status":"closed","cost_complete":true,"reason":"early_stop_min_speedup"}));
        if admitted {
            ledger.state.trials.push(serde_json::from_value(json!({"iteration":1,"call_id":1,"status":"evaluated",
                "candidate":{"candidate_manifest":"verus-query.json","rationale":"r","data_access_analysis":"d"}})).unwrap());
            let frozen = session.join("iterations/0001/frozen");
            records::create_dir(&frozen).unwrap();
            for record in ["candidate.json", "manifest.json"] {
                records::write_new_json(&frozen.join(record), &json!({})).unwrap();
            }
            records::write_new_json(&session.join("iterations/0001/qualification.json"), &json!({"qualified":true})).unwrap();
        }
        ledger.save().unwrap();
        session
    }

    fn request(value: Value) -> WorkloadRequest {
        serde_json::from_value(value).unwrap()
    }

    /// The statement and its correctness conditions must match; the objective, worker counts and limits may differ; the
    /// source must have admitted a candidate.
    #[test]
    fn a_source_must_be_a_closed_session_of_the_same_statement_that_admitted_a_candidate() {
        let root = scratch_root("continuation-source");
        let source = source_run(&root, true);
        let same = recorded(&root, Some(&source));
        assert_eq!(check_source(&request(same.clone()), 0, "k").unwrap(), source.canonicalize().unwrap());
        let refused = |value: Value, key: &str| check_source(&request(value), 0, key).unwrap_err();
        assert!(refused(same.clone(), "other").contains("statement key"));
        let mut changed = same.clone();
        changed["queries"][0]["test_bindings"] = json!([["4"]]);
        assert!(refused(changed, "k").contains("test_bindings"));
        let mut changed = same.clone();
        changed["storage_policy"] = json!({"kind":"unrestricted"});
        assert!(refused(changed, "k").contains("storage_policy"));
        let mut changed = same.clone();
        changed["queries"][0]["objective"]["targets"] = json!([{"binding":"b","workers":1,"median_ns":7,"provenance":"ReferenceDB","timing_scope":"s"}]);
        changed["hardware"]["threads"] = json!([1]);
        changed["queries"][0]["limits"]["max_iterations"] = json!(1);
        assert!(check_source(&request(changed), 0, "k").is_ok(), "the objective, worker counts and limits may differ");
        let error = refused(recorded(&root, Some(&root.join("earlier"))), "k");
        assert!(error.starts_with(SOURCE_REFUSAL) && error.contains("not a query session directory"), "{error}");
        let none_root = scratch_root("continuation-source-unadmitted");
        let unadmitted = source_run(&none_root, false);
        assert!(refused(recorded(&none_root, Some(&unadmitted)), "k").contains("admitted 0 candidates"));
        std::fs::remove_dir_all(root).unwrap();
        std::fs::remove_dir_all(none_root).unwrap();
    }
}
