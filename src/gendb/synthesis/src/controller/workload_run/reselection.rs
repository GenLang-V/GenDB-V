//! The workload checks of `queries[i].reselect_from`, made right after the statement is prepared and before any data
//! preparation or preflight. The named directory must be the closed query session `<run>/queries/query-NNNN` of an
//! earlier synthesis run (`controller::reselect::closed_source`). That run's request must have asked for the same
//! query under the same conditions: SQL text, parameters with their modes and domains, admission bindings, objective
//! (benchmark bindings, targets, early stop), worker counts, data allowance and storage policy kind. The session's
//! recorded statement key must be this prepared statement's (schema, statement, parameters, output). Each mismatch
//! is named (`reselect_source_invalid: <what>`) and refuses the query before any author or framework work. The
//! reselection session rechecks closure and task under its own lock.

use crate::controller::records;
use crate::controller::request::WorkloadRequest;
use crate::controller::reselect::{SOURCE_REFUSAL, closed_source};
use serde_json::Value;
use std::path::{Path, PathBuf};

/// Check query `index`'s `reselect_from` against its prepared statement (`statement_key`: its key v4, which covers the
/// schema, statement, parameters and output): the canonical source session directory, or the named refusal.
pub fn check_source(request: &WorkloadRequest, index: usize, statement_key: &str) -> Result<PathBuf, String> {
    let query = &request.queries[index];
    let named = query.reselect_from.as_deref().ok_or_else(|| format!("{SOURCE_REFUSAL}: queries[{index}] names no source session"))?;
    let source = named.canonicalize().map_err(|e| format!("{SOURCE_REFUSAL}: {}: {e}", named.display()))?;
    let (run, source_index) = source_run(&source)?;
    closed_source(&source)?;
    let recorded: WorkloadRequest = records::read_json(&run.join("request.json")).map_err(|e| format!("{SOURCE_REFUSAL}: the source run's request: {e}"))?;
    let earlier = recorded.queries.get(source_index).ok_or_else(|| format!("{SOURCE_REFUSAL}: the source run's request has no query {source_index}"))?;
    let differences = [
        ("sql", earlier.sql == query.sql),
        ("parameters (modes and domains)", earlier.parameters == query.parameters),
        ("test_bindings (admission bindings)", earlier.test_bindings == query.test_bindings),
        ("objective (kind, benchmark bindings, targets, early stop)", earlier.objective == query.objective),
        ("hardware.threads (worker counts)", recorded.hardware.threads == request.hardware.threads),
        ("data_allowance", recorded.data_allowance == request.data_allowance),
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
    Ok(source)
}

/// The run directory and query index of the query session directory `<run>/queries/query-NNNN` (refusals start with
/// `reselect_source_invalid`; `continuation` names its own class).
pub(super) fn source_run(source: &Path) -> Result<(PathBuf, usize), String> {
    let shape = || format!("{SOURCE_REFUSAL}: {} is not a query session directory <run>/queries/query-NNNN", source.display());
    let name = source.file_name().and_then(|n| n.to_str()).ok_or_else(shape)?;
    let index = name.strip_prefix("query-").filter(|digits| digits.len() == 4).and_then(|digits| digits.parse().ok()).ok_or_else(shape)?;
    let queries = source.parent().filter(|p| p.file_name().is_some_and(|n| n == "queries")).ok_or_else(shape)?;
    let run = queries.parent().ok_or_else(shape)?;
    Ok((run.to_path_buf(), index))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::controller::ledger::Ledger;
    use crate::controller::limits::tests::limits;
    use crate::controller::test_support::scratch_root;
    use serde_json::json;

    /// A request over one template query, as the source run recorded it (paths absolute).
    fn recorded(root: &Path, reselect_from: Option<&Path>) -> Value {
        let mut query = json!({"sql":"SELECT 1 WHERE $1 > 0","limits":limits(),
            "parameters":[{"index":1,"type":"integer","binding":{"free":{}}}],"test_bindings":[["3"]],
            "objective":{"kind":"execution_time","bindings":[{"name":"b","arguments":["5"]}]}});
        if let Some(source) = reselect_from {
            query["reselect_from"] = json!(source);
        }
        json!({"format_version":2,"dataset":{"tables":[]},"queries":[query],"hardware":{"threads":[1,4]},"max_concurrent_queries":1,
            "author_executable":"claude","library":root.join("library"),
            "barriers":{"activity_lock":root.join("a.lock"),"build_lock":root.join("b.lock"),"race_lock":root.join("r.lock")},
            "storage_policy":{"kind":"physical_only"}})
    }

    /// A closed source session of query 0 with statement key `k` (open when `closed` is false).
    fn source_run(root: &Path, closed: bool) -> PathBuf {
        let session = root.join("earlier/queries/query-0000");
        records::create_dir(&session).unwrap();
        records::write_new_json(&root.join("earlier/request.json"), &recorded(root, None)).unwrap();
        records::write_new_json(&session.join("context.json"), &json!({"statement_key":"k"})).unwrap();
        let mut ledger = Ledger::open(&session, json!({"request":{"task":{"sql":"q"}}}), limits()).unwrap();
        if closed {
            ledger.state.closed = Some(json!({"status":"closed","cost_complete":true,"reason":"iteration_limit"}));
            ledger.save().unwrap();
        }
        session
    }

    fn request(value: Value) -> WorkloadRequest {
        serde_json::from_value(value).unwrap()
    }

    #[test]
    fn a_source_must_be_a_closed_session_of_the_same_query_under_the_same_conditions() {
        let root = scratch_root("reselection-source");
        let source = source_run(&root, true);
        let same = recorded(&root, Some(&source));
        assert_eq!(check_source(&request(same.clone()), 0, "k").unwrap(), source.canonicalize().unwrap());
        let refused = |value: Value, key: &str| check_source(&request(value), 0, key).unwrap_err();
        assert!(refused(same.clone(), "other").contains("statement key"), "the prepared statement differs");
        let mut changed = same.clone();
        changed["queries"][0]["test_bindings"] = json!([["4"]]);
        assert!(refused(changed, "k").contains("test_bindings"));
        let mut changed = same.clone();
        changed["queries"][0]["parameters"][0]["binding"] = json!({"free":{"min":"0","max":"9"}});
        assert!(refused(changed, "k").contains("parameters"));
        let mut changed = same.clone();
        changed["queries"][0]["objective"]["bindings"][0]["arguments"] = json!(["6"]);
        assert!(refused(changed, "k").contains("objective"));
        let mut changed = same.clone();
        changed["hardware"]["threads"] = json!([1]);
        assert!(refused(changed, "k").contains("hardware.threads"));
        let mut changed = same.clone();
        changed["data_allowance"] = json!({"live_bytes":1});
        assert!(refused(changed, "k").contains("data_allowance"));
        let mut changed = same.clone();
        changed["storage_policy"] = json!({"kind":"unrestricted"});
        assert!(refused(changed, "k").contains("storage_policy"));
        let mut changed = same.clone();
        changed["queries"][0]["limits"]["max_iterations"] = json!(1);
        assert!(check_source(&request(changed), 0, "k").is_ok(), "the user's author limits do not matter to a reselection");
        assert!(refused(recorded(&root, Some(&root.join("earlier"))), "k").contains("not a query session directory"));
        assert!(refused(recorded(&root, Some(&root.join("missing/queries/query-0000"))), "k").starts_with(SOURCE_REFUSAL));
        let open_root = scratch_root("reselection-open-source");
        let open = source_run(&open_root, false);
        assert!(refused(recorded(&open_root, Some(&open)), "k").contains("is open"));
    }
}
