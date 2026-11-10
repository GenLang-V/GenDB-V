//! Records of one workload run directory across controller processes: the immutable request, per-query refusal
//! records, and the workload summaries (every summary is a new record; `summary-latest.json` names the newest).
//!
//! ```text
//! <run>/request.json                       the request, written once; a restart must present the same request
//! <run>/route.json                         which route owns the run (synthesis, serving, import, ...), written once
//! <run>/summary[-N].json                   workload summaries, never replaced   summary-latest.json  newest one
//! <run>/workload-preparation-<ms>-<pid>.json  data preparation of one controller process
//! <run>/workload-storage/session/          the workload storage author session (controller::layout)
//! <run>/workload-storage/                  its session summaries (workload-summary[-N].json)
//! <run>/queries/query-NNNN/                one query: its author session (controller::layout) or its refusal
//! <run>/author-inspection/query-NNNN/      provider inspection evidence of that query's author
//! <run>/author-inspection/workload-storage/ provider inspection evidence of the storage author
//! <run>/data/                              the run's prepared source root (gendb_storage::import)
//! <run>/data-extension-<ms>/, data-current.json  capture extensions and the newest root (storage::capture)
//! <run>/budget-raise[-N].json              a general engine run's budget raises on relaunch, in order (record_request)
//! <run>/request-change[-N].json            a general engine run's other allowed request changes on relaunch (record_request)
//! ```

use crate::controller::limits::{Money, request_without_retired_turn_cap};
use crate::controller::records::{self, RecordError};
use serde_json::{Value, json};
use std::path::{Component, Path, PathBuf};

/// Pointer to the newest workload summary.
const LATEST_SUMMARY: &str = "summary-latest.json";

/// The directory of query `index`.
pub fn query_directory(root: &Path, index: usize) -> PathBuf {
    root.join("queries").join(format!("query-{index:04}"))
}

/// Provider inspection evidence of query `index`'s author.
pub fn author_inspection_directory(root: &Path, index: usize) -> PathBuf {
    root.join("author-inspection").join(format!("query-{index:04}"))
}

/// The workload storage author's session directory.
pub fn storage_session_directory(root: &Path) -> PathBuf {
    root.join("workload-storage").join("session")
}

/// Where the workload storage session's summaries are recorded.
pub fn storage_summary_directory(root: &Path) -> PathBuf {
    root.join("workload-storage")
}

/// Provider inspection evidence of the workload storage author.
pub fn storage_inspection_directory(root: &Path) -> PathBuf {
    root.join("author-inspection").join("workload-storage")
}

/// The run's prepared source root.
pub fn data_root(root: &Path) -> PathBuf {
    root.join("data")
}

/// The route that owns a run directory. The same request drives both routes, so a run directory belongs to one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Route {
    /// `synthesize` and its dry run `preflight`.
    Synthesis,
    /// `serve`.
    Serving,
    /// `prepare-flat-storage` (the fixed flat storages of a `fixed_flat` request).
    FlatPreparation,
    /// `engine synthesize` (the schema-engine target, `engine::rounds`).
    Engine,
    /// `import` (a published run's packages admitted without an author, `workload_run::import`).
    Import,
}

impl Route {
    fn name(self) -> &'static str {
        match self {
            Route::Synthesis => "synthesis",
            Route::Serving => "serving",
            Route::FlatPreparation => "flat_storage_preparation",
            Route::Engine => "engine",
            Route::Import => "import",
        }
    }
}

/// Record the run directory's route, or check that a restart uses the same route.
pub fn record_route(root: &Path, route: Route) -> Result<(), RecordError> {
    let path = root.join("route.json");
    if !path.exists() {
        return records::write_new_json(&path, &json!({"format_version":1,"route":route.name()}));
    }
    let recorded: Value = records::read_json(&path)?;
    if recorded["route"] != route.name() {
        return Err(RecordError::new(&path, format!("this run directory belongs to the {} route; use another run directory for {}", recorded["route"], route.name())));
    }
    Ok(())
}

/// The record of a run's one validation policy transition (`record_request`).
pub const VALIDATION_TRANSITION: &str = "validation-transition.json";

/// The first record of a general engine run's budget raises (`record_request`); later ones are `budget-raise-1.json`,
/// `budget-raise-2.json`, ... in order, and the newest one's `to` is the run's budget.
pub const BUDGET_RAISE: &str = "budget-raise.json";
/// The stem of the later budget raise records.
const BUDGET_RAISE_STEM: &str = "budget-raise";

/// The first record of a general engine run's other allowed request changes on relaunch (`record_request`): setting
/// [`ONE_ENGINE_FIELD`], changing [`TIMED_CALLS_FIELD`]; later ones are `request-change-1.json`, `request-change-2.json`,
/// ... in order, each naming its `field`, and a field's newest record's `to` is the run's value from then on.
pub const REQUEST_CHANGE: &str = "request-change.json";
/// The stem of the later request change records.
const REQUEST_CHANGE_STEM: &str = "request-change";
/// The request field a general engine run's relaunch may set, never unset: only a version that is one engine can be
/// accepted (`controller::request::EngineWorkloads::require_one_engine`).
pub const ONE_ENGINE_FIELD: &str = "engine.workloads.require_one_engine";
/// The request field a general engine run's relaunch may change either way: the hot calls of every timed cell of its
/// development timings (`controller::request::EngineRequest::timed_calls`, absent 3).
pub const TIMED_CALLS_FIELD: &str = "engine.timed_calls";

/// Record `request` as the run's immutable `request.json`, or check that a restarted run presents the same request
/// (the retired author-turn guard and the scheduling controls `max_concurrent_queries`, `max_concurrent_preparations`,
/// `engine.pause_after_round` and `engine.pause_after_session` are ignored in the comparison, and on the general engine
/// line also `engine.branches`: the user may relaunch a general run with another number of branches).
/// Returns whether the run already existed.
///
/// A run recorded under the default validation policy (`tests_and_references`) may resume once under `formal_proofs`
/// with an otherwise identical request: `request.json` stays as written, and `validation-transition.json` records the
/// old and new policy and when; later restarts compare against the request with the new policy.
///
/// On the general engine line a relaunch may raise the run's budget `engine.limits.max_cost_usd`, never lower it
/// ([`check_budget_raise`]): `request.json` stays as written, each raise is a new record `budget-raise[-N].json`, and
/// later relaunches compare against the newest raise. Likewise it may set [`ONE_ENGINE_FIELD`], never unset it
/// ([`check_one_engine_change`]), and change [`TIMED_CALLS_FIELD`] ([`check_timed_calls_change`]): each change is a new
/// record `request-change[-N].json`.
pub fn record_request(root: &Path, request: &Value) -> Result<bool, RecordError> {
    let path = root.join("request.json");
    if !path.exists() {
        records::write_new_json(&path, request)?;
        return Ok(false);
    }
    let mut recorded: Value = records::read_json(&path)?;
    let transition = root.join(VALIDATION_TRANSITION);
    if transition.exists() {
        let record: Value = records::read_json(&transition)?;
        recorded["validation"] = record["to"].clone();
    }
    // The query and preparation concurrencies and an engine run's review pauses are scheduling controls
    // (`WorkloadRequest::max_concurrent_queries` and `max_concurrent_preparations`, `EngineRequest::pause_after_round`
    // and `pause_after_session`): a relaunch with fewer query slots resumes the open sessions in request order, the
    // others waiting for a slot with their records unchanged (`controller::schedule`); so is the general line's number
    // of branch slots (`EngineRequest::branches`): every branch's records stay, and only slots up to the count get new
    // sessions. A schema-line request has no `branches` (it is refused there). The general line's budget is compared
    // on its own: a relaunch may raise it (`check_budget_raise`); so are its one-engine rule (a relaunch may set it,
    // `check_one_engine_change`) and its timed calls (a relaunch may change them, `check_timed_calls_change`).
    let identity = |mut request: Value| {
        if let Some(fields) = request.as_object_mut() {
            fields.remove("max_concurrent_queries");
            fields.remove("max_concurrent_preparations");
        }
        if let Some(engine) = request.get_mut("engine").and_then(Value::as_object_mut) {
            engine.remove("pause_after_round");
            engine.remove("pause_after_session");
            if engine.get("line").and_then(Value::as_str) == Some("general") {
                engine.remove("branches");
                engine.remove("timed_calls");
                if let Some(limits) = engine.get_mut("limits").and_then(Value::as_object_mut) {
                    limits.remove("max_cost_usd");
                }
                if let Some(workloads) = engine.get_mut("workloads").and_then(Value::as_object_mut) {
                    workloads.remove("require_one_engine");
                }
            }
        }
        request_without_retired_turn_cap(request)
    };
    if identity(recorded.clone()) == identity(request.clone()) {
        if request.pointer("/engine/line").and_then(Value::as_str) == Some("general") {
            check_budget_raise(root, &recorded, request)?;
            check_one_engine_change(root, &recorded, request)?;
            check_timed_calls_change(root, &recorded, request)?;
        }
        return Ok(true);
    }
    let without_validation = |mut request: Value| {
        request.as_object_mut().map(|fields| fields.remove("validation"));
        identity(request)
    };
    let to_formal = recorded.get("validation").is_none() && request["validation"]["kind"] == "formal_proofs";
    if to_formal && without_validation(recorded) == without_validation(request.clone()) {
        records::write_new_json(&transition, &json!({"format_version":1,"from":{"kind":"tests_and_references"},"to":request["validation"],
            "at_unix_ms":records::now_unix_ms(),"request":path,
            "meaning":"the run's request.json is unchanged; from this restart on the run uses the validation policy `to` (no tiny cases, evaluator builds or reference engine runs). Evidence written under `from` is kept and is not reused as evidence of `to`"}))?;
        return Ok(true);
    }
    Err(RecordError::new(&path, "immutable workload request differs"))
}

/// A general engine run's relaunch budget (`engine.limits.max_cost_usd` of `request`) against the run's budget: the
/// newest raise's `to`, else the recorded request's. The same budget is accepted as is; a higher one is recorded as the
/// next `budget-raise[-N].json` (from, to, when) and accepted; a lower one, or one that is not a set dollar amount, is
/// refused (the run's spend records stay as they are, and the run reads the presented budget).
fn check_budget_raise(root: &Path, recorded: &Value, request: &Value) -> Result<(), RecordError> {
    let request_path = root.join("request.json");
    let dollars = |text: Option<&str>, what: &str, path: &Path| -> Result<Money, RecordError> {
        let text = text.unwrap_or_default();
        Money::parse(text)
            .ok()
            .filter(|budget| !budget.is_unset())
            .ok_or_else(|| RecordError::new(path, format!("{what} {text:?} is not a set dollar amount")))
    };
    fn budget_text(request: &Value) -> Option<&str> {
        request.pointer("/engine/limits/max_cost_usd").and_then(Value::as_str)
    }
    let (current, current_from) = match latest_record(root, BUDGET_RAISE, BUDGET_RAISE_STEM) {
        Some(path) => {
            let raise: Value = records::read_json(&path)?;
            (dollars(raise["to"].as_str(), "the newest budget raise's `to`", &path)?, path)
        }
        None => (dollars(budget_text(recorded), "the recorded request's engine.limits.max_cost_usd", &request_path)?, request_path.clone()),
    };
    let presented = dollars(budget_text(request), "the relaunch request's engine.limits.max_cost_usd", &request_path)?;
    if presented < current {
        return Err(RecordError::new(
            &request_path,
            format!(
                "a relaunch may raise the general line's budget engine.limits.max_cost_usd, never lower it: the run's budget is {} ({}), the request has {}",
                current.decimal(),
                current_from.display(),
                presented.decimal()
            ),
        ));
    }
    if presented > current {
        let path = records::next_free_record(root, BUDGET_RAISE, BUDGET_RAISE_STEM);
        records::write_new_json(&path, &json!({"format_version":1,"from":current,"to":presented,"at_unix_ms":records::now_unix_ms(),"request":request_path,
            "meaning":"the user raised the run's budget on relaunch: request.json is unchanged; from this launch on the run's budget is `to`, and a later relaunch may present `to` or more, never less"}))?;
    }
    Ok(())
}

/// A general engine run's relaunch value of [`ONE_ENGINE_FIELD`] (in `request`) against the run's: the field's newest
/// change's `to`, else the recorded request's (absent is false). The same value is accepted as is; setting it is recorded as the
/// next `request-change[-N].json` (field, from, to, when) and accepted; unsetting it is refused (the run's versions
/// since then were accepted under it).
fn check_one_engine_change(root: &Path, recorded: &Value, request: &Value) -> Result<(), RecordError> {
    let request_path = root.join("request.json");
    let set = |request: &Value| request.pointer("/engine/workloads/require_one_engine") == Some(&Value::Bool(true));
    let (current, current_from) = match latest_change(root, ONE_ENGINE_FIELD)? {
        Some((change, path)) => (change["to"] == true, path),
        None => (set(recorded), request_path.clone()),
    };
    match (current, set(request)) {
        (true, false) => Err(RecordError::new(
            &request_path,
            format!("a relaunch may set {ONE_ENGINE_FIELD}, never unset it: the run requires one engine ({}), the request does not", current_from.display()),
        )),
        (false, true) => {
            let path = records::next_free_record(root, REQUEST_CHANGE, REQUEST_CHANGE_STEM);
            records::write_new_json(&path, &json!({"format_version":1,"field":ONE_ENGINE_FIELD,"from":false,"to":true,"at_unix_ms":records::now_unix_ms(),"request":request_path,
                "meaning":"the run's request was changed on relaunch: request.json is unchanged; from this launch on only a version that is one engine can be accepted (a later relaunch must keep the field set)"}))?;
            Ok(())
        }
        _ => Ok(()),
    }
}

/// A general engine run's relaunch value of [`TIMED_CALLS_FIELD`] (in `request`, absent 3) against the run's: the
/// field's newest change's `to`, else the recorded request's. A different value is recorded as the next
/// `request-change[-N].json` (field, from, to, when) and accepted: from this launch on the run's development timings
/// make that many hot calls per cell (cells timed before keep their recorded calls, `race.json` `calls_per_cell`).
fn check_timed_calls_change(root: &Path, recorded: &Value, request: &Value) -> Result<(), RecordError> {
    let timed_calls = |request: &Value| request.pointer("/engine/timed_calls").and_then(Value::as_u64).unwrap_or(u64::from(crate::engine::protocol::DEFAULT_TIMED_CALLS));
    let current = match latest_change(root, TIMED_CALLS_FIELD)? {
        Some((change, path)) => change["to"].as_u64().ok_or_else(|| RecordError::new(&path, "a timed-calls change without a number `to`"))?,
        None => timed_calls(recorded),
    };
    let presented = timed_calls(request);
    if presented != current {
        let path = records::next_free_record(root, REQUEST_CHANGE, REQUEST_CHANGE_STEM);
        records::write_new_json(&path, &json!({"format_version":1,"field":TIMED_CALLS_FIELD,"from":current,"to":presented,"at_unix_ms":records::now_unix_ms(),"request":root.join("request.json"),
            "meaning":"the run's request was changed on relaunch: request.json is unchanged; from this launch on every timed cell of the run's development timings is 1 warm call and `to` hot calls, its time the median hot call (cells timed before keep their recorded calls)"}))?;
    }
    Ok(())
}

/// The newest request change record of `field` (`request-change[-N].json`), with its path, if any.
fn latest_change(root: &Path, field: &str) -> Result<Option<(Value, PathBuf)>, RecordError> {
    let mut latest = None;
    let mut ordinal = 0usize;
    loop {
        let path = if ordinal == 0 { root.join(REQUEST_CHANGE) } else { root.join(format!("{REQUEST_CHANGE_STEM}-{ordinal}.json")) };
        if !path.exists() {
            return Ok(latest);
        }
        let change: Value = records::read_json(&path)?;
        if change["field"] == field {
            latest = Some((change, path));
        }
        ordinal += 1;
    }
}

/// The newest of a run's numbered records `first`, then `<stem>-1.json`, `<stem>-2.json`, ... (the budget raises, the
/// request changes), if any.
fn latest_record(root: &Path, first: &str, stem: &str) -> Option<PathBuf> {
    let mut latest = None;
    let mut ordinal = 0usize;
    loop {
        let path = if ordinal == 0 { root.join(first) } else { root.join(format!("{stem}-{ordinal}.json")) };
        if !path.exists() {
            return latest;
        }
        latest = Some(path);
        ordinal += 1;
    }
}

/// The newest workload summary: the record `summary-latest.json` names, or `summary.json` of a run published before
/// that pointer existed. `None` when no summary was published.
pub fn latest_summary(root: &Path) -> Result<Option<Value>, RecordError> {
    let pointer = root.join(LATEST_SUMMARY);
    let path = if pointer.exists() {
        let record: Value = records::read_json(&pointer)?;
        let name = record["record"].as_str().filter(|_| record["format_version"] == 1);
        let local = name.map(Path::new).filter(|p| matches!(p.components().collect::<Vec<_>>().as_slice(), [Component::Normal(_)]));
        let Some(name) = local else {
            return Err(RecordError::new(&pointer, "the latest-summary pointer must name a local record (format 1)"));
        };
        let path = root.join(name);
        if !path.exists() {
            return Err(RecordError::new(&path, "latest workload summary record absent"));
        }
        path
    } else {
        root.join("summary.json")
    };
    if !path.exists() {
        return Ok(None);
    }
    records::read_json(&path).map(Some)
}

/// Publish `summary` as a new record and point `summary-latest.json` at it; earlier summaries stay unchanged.
pub fn publish_summary(root: &Path, summary: &Value) -> Result<PathBuf, RecordError> {
    let path = records::next_free_record(root, "summary.json", "summary");
    records::write_new_json(&path, summary)?;
    let name = path.file_name().and_then(|n| n.to_str()).unwrap_or_default();
    records::write_json_atomic(
        &root.join(LATEST_SUMMARY),
        &json!({"format_version":1,"record":name,"scope":"latest outcome pointer; all prior workload summary records remain immutable"}),
    )?;
    Ok(path)
}

/// A published summary that a restart continues: some query ended in a framework error or with unresolved accounting,
/// or is marked resumable.
pub fn is_resumable(summary: &Value) -> bool {
    summary["queries"].as_array().is_some_and(|queries| {
        queries.iter().any(|query| matches!(query["status"].as_str(), Some("framework_error" | "accounting_unresolved")) || query["resumable"] == true)
    })
}

/// Write a query's refusal as its `summary.json` (replaced when a restart refuses it again).
pub fn record_refusal(root: &Path, index: usize, refusal: &Value) -> Result<(), RecordError> {
    let directory = query_directory(root, index);
    records::create_dir(&directory)?;
    records::write_json_atomic(&directory.join("summary.json"), refusal)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn summaries_are_new_records_and_resumable_outcomes_continue() {
        let root = crate::controller::test_support::scratch_root("workload-summaries");
        records::create_dir(&root).unwrap();
        let partial = json!({"status":"closed","queries":[{"status":"framework_error","error":"x"},{"status":"closed","calls":2}]});
        records::write_new_json(&root.join("summary.json"), &partial).unwrap();
        let original = std::fs::read(root.join("summary.json")).unwrap();
        assert!(is_resumable(&latest_summary(&root).unwrap().unwrap()));
        let complete = json!({"status":"closed","queries":[{"status":"closed","calls":2},{"status":"closed","calls":2}]});
        assert_eq!(publish_summary(&root, &complete).unwrap(), root.join("summary-1.json"));
        assert_eq!(std::fs::read(root.join("summary.json")).unwrap(), original);
        let latest = latest_summary(&root).unwrap().unwrap();
        assert_eq!(latest, complete);
        assert!(!is_resumable(&latest));
        assert!(is_resumable(&json!({"queries":[{"status":"accounting_unresolved"}]})));
    }

    #[test]
    fn a_run_directory_belongs_to_one_route() {
        let root = crate::controller::test_support::scratch_root("workload-route");
        records::create_dir(&root).unwrap();
        record_route(&root, Route::Synthesis).unwrap();
        record_route(&root, Route::Synthesis).unwrap();
        assert!(record_route(&root, Route::Serving).is_err());
    }

    /// The query and preparation concurrencies are scheduling controls: a relaunch may lower or raise them (a paused
    /// run resumes with fewer sessions at a time), `request.json` stays as written, and every other field still counts.
    #[test]
    fn a_restart_may_change_the_query_and_preparation_concurrency() {
        let root = crate::controller::test_support::scratch_root("workload-request-concurrency");
        records::create_dir(&root).unwrap();
        let request = |queries: usize, preparations: usize, sql: &str| {
            json!({"format_version":2,"queries":[{"sql":sql}],"max_concurrent_queries":queries,"max_concurrent_preparations":preparations})
        };
        assert!(!record_request(&root, &request(10, 8, "q")).unwrap());
        let written = std::fs::read(root.join("request.json")).unwrap();
        assert!(record_request(&root, &request(4, 8, "q")).unwrap());
        assert!(record_request(&root, &request(2, 1, "q")).unwrap());
        assert_eq!(std::fs::read(root.join("request.json")).unwrap(), written, "request.json stays as written");
        assert!(record_request(&root, &request(4, 8, "other")).is_err(), "a changed query is still refused");
    }

    #[test]
    fn a_restart_must_present_the_same_request() {
        let root = crate::controller::test_support::scratch_root("workload-request");
        records::create_dir(&root).unwrap();
        let request = json!({"format_version":2,"queries":[{"sql":"q","limits":{"max_author_tool_turns":4}}]});
        assert!(!record_request(&root, &request).unwrap());
        let retired_turns_changed = json!({"format_version":2,"queries":[{"sql":"q","limits":{"max_author_tool_turns":9}}]});
        assert!(record_request(&root, &retired_turns_changed).unwrap());
        assert!(record_request(&root, &json!({"format_version":2,"queries":[]})).is_err());
    }

    /// A general engine run's relaunch may set the one-engine rule (`engine.workloads.require_one_engine`), like a
    /// budget raise: `request.json` stays as written, the change is one record, the same value again records nothing,
    /// unsetting it is refused, and no other field may change with it.
    #[test]
    fn a_general_relaunch_may_set_the_one_engine_rule_never_unset_it() {
        let root = crate::controller::test_support::scratch_root("request-one-engine-change");
        records::create_dir(&root).unwrap();
        let request = |one_engine: Option<bool>, budget: &str| {
            let mut request = json!({"format_version":2,"engine":{"line":"general","limits":{"max_cost_usd":budget},"workloads":{"name":"tpch","members":[]}}});
            if let Some(one_engine) = one_engine {
                request["engine"]["workloads"]["require_one_engine"] = json!(one_engine);
            }
            request
        };
        assert!(!record_request(&root, &request(None, "1000")).unwrap());
        let written = std::fs::read(root.join("request.json")).unwrap();
        assert!(record_request(&root, &request(Some(false), "1000")).unwrap() && !root.join(REQUEST_CHANGE).exists(), "false is the absent value: no change");
        assert!(record_request(&root, &request(Some(true), "1000")).unwrap(), "setting it is accepted");
        let change: Value = records::read_json(&root.join(REQUEST_CHANGE)).unwrap();
        assert_eq!((change["field"].as_str(), change["from"].as_bool(), change["to"].as_bool()), (Some(ONE_ENGINE_FIELD), Some(false), Some(true)), "{change}");
        assert!(record_request(&root, &request(Some(true), "1000")).unwrap() && !root.join("request-change-1.json").exists(), "the same value again records nothing");
        let unset = record_request(&root, &request(None, "1000")).unwrap_err().to_string();
        assert!(unset.contains("never unset it") && unset.contains(REQUEST_CHANGE), "{unset}");
        assert!(record_request(&root, &request(Some(true), "1500")).unwrap() && root.join(BUDGET_RAISE).exists(), "a budget raise beside it");
        let mut other = request(Some(true), "1500");
        other["engine"]["workloads"]["name"] = json!("sec");
        assert!(record_request(&root, &other).is_err(), "no other field may change");
        assert_eq!(std::fs::read(root.join("request.json")).unwrap(), written, "request.json stays as written");
        std::fs::remove_dir_all(&root).unwrap();
    }

    /// A general engine run's relaunch may change its timed calls (`engine.timed_calls`, absent 3) either way: absent and
    /// 3 are the same value (no record), each change is one record naming the field beside the one-engine rule's, and
    /// the one-engine rule still reads its own newest record.
    #[test]
    fn a_general_relaunch_may_change_the_timed_calls_with_a_record() {
        let root = crate::controller::test_support::scratch_root("request-timed-calls-change");
        records::create_dir(&root).unwrap();
        let request = |timed_calls: Option<u32>, one_engine: bool| {
            let mut request = json!({"format_version":2,"engine":{"line":"general","limits":{"max_cost_usd":"1000"},"workloads":{"name":"tpch","members":[]}}});
            if let Some(timed_calls) = timed_calls {
                request["engine"]["timed_calls"] = json!(timed_calls);
            }
            if one_engine {
                request["engine"]["workloads"]["require_one_engine"] = json!(true);
            }
            request
        };
        assert!(!record_request(&root, &request(None, false)).unwrap());
        let written = std::fs::read(root.join("request.json")).unwrap();
        assert!(record_request(&root, &request(Some(3), false)).unwrap() && !root.join(REQUEST_CHANGE).exists(), "3 is the absent value: no change");
        assert!(record_request(&root, &request(Some(5), true)).unwrap(), "a change beside the one-engine rule is accepted");
        let changes: Vec<Value> = [REQUEST_CHANGE, "request-change-1.json"].iter().map(|f| records::read_json(&root.join(f)).unwrap()).collect();
        let fields: Vec<(&str, &Value, &Value)> = changes.iter().map(|c| (c["field"].as_str().unwrap(), &c["from"], &c["to"])).collect();
        assert_eq!(fields, [(ONE_ENGINE_FIELD, &json!(false), &json!(true)), (TIMED_CALLS_FIELD, &json!(3), &json!(5))]);
        assert!(record_request(&root, &request(Some(5), true)).unwrap() && !root.join("request-change-2.json").exists(), "the same values again record nothing");
        assert!(record_request(&root, &request(None, true)).unwrap(), "back to the default");
        let back: Value = records::read_json(&root.join("request-change-2.json")).unwrap();
        assert_eq!((back["field"].as_str(), back["from"].as_u64(), back["to"].as_u64()), (Some(TIMED_CALLS_FIELD), Some(5), Some(3)), "{back}");
        assert!(record_request(&root, &request(None, false)).unwrap_err().to_string().contains("never unset it"), "the one-engine rule reads its own record");
        assert_eq!(std::fs::read(root.join("request.json")).unwrap(), written, "request.json stays as written");
        std::fs::remove_dir_all(&root).unwrap();
    }
}
