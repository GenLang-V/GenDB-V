//! Framework-observed trajectory of one author session: author-local job counts, unchanged resubmission detection
//! and the counters of the final summary. Everything here is read from durable records of the run; nothing is
//! measured again.

use super::layout::RunLayout;
use super::ledger::{LedgerState, Trial};
use super::records::{self, RecordError};
use serde::Serialize;
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

/// Counts of the author's local diagnostic jobs (`calls/*/local-jobs`). Local jobs are diagnostics: they never count
/// as submissions and never replace official evaluation.
#[derive(Clone, Debug, Default, Serialize, PartialEq)]
pub struct LocalJobSummary {
    pub jobs: u64,
    pub by_action: BTreeMap<String, u64>,
    /// `trial` and `profile` jobs.
    pub local_trials: u64,
    pub failed_jobs: u64,
    /// The last job record (by call, then job id): status, action, error class and where the full record is.
    pub latest: Value,
}

/// Job records of one `local-jobs` directory: `<job>/result.json` directories and flat refusal records. Service
/// bookkeeping files and records without a final status are not jobs.
fn job_records(jobs: &Path) -> Result<Vec<(PathBuf, Value)>, RecordError> {
    let mut found = vec![];
    for entry in fs::read_dir(jobs).map_err(|e| RecordError::new(jobs, e))? {
        let path = entry.map_err(|e| RecordError::new(jobs, e))?.path();
        let record = if path.is_dir() { path.join("result.json") } else { path };
        let service_file = record.file_name().is_some_and(|name| name == "service.json" || name == "service-finished.json");
        if !record.is_file() || service_file {
            continue;
        }
        let value: Value = records::read_json(&record)?;
        if value["status"] == "completed" || value["status"] == "refused" {
            found.push((record, value));
        }
    }
    Ok(found)
}

/// The call directories of the session in call order, with their call numbers (`calls/NNNN`).
fn call_directories(layout: &RunLayout) -> Result<Vec<(u64, PathBuf)>, RecordError> {
    let calls = layout.calls();
    if !calls.is_dir() {
        return Ok(vec![]);
    }
    let mut found = vec![];
    for entry in fs::read_dir(&calls).map_err(|e| RecordError::new(&calls, e))? {
        let path = entry.map_err(|e| RecordError::new(&calls, e))?.path();
        if let Some(call) = path.file_name().and_then(|name| name.to_str()).and_then(|name| name.parse::<u64>().ok()) {
            found.push((call, path));
        }
    }
    found.sort();
    Ok(found)
}

/// The job records of one call directory's `local-jobs`, by job id, each (job id, action) once (one job may leave a
/// result and a service refusal record).
fn call_jobs(call_dir: &Path) -> Result<Vec<(PathBuf, Value)>, RecordError> {
    let jobs = call_dir.join("local-jobs");
    if !jobs.is_dir() {
        return Ok(vec![]);
    }
    let mut records = job_records(&jobs)?;
    records.sort_by_key(|(path, value)| (value["job_id"].as_u64().unwrap_or(0), path.clone()));
    let mut seen = std::collections::BTreeSet::new();
    records.retain(|(_, value)| seen.insert((value["job_id"].as_u64().unwrap_or(0), value["action"].as_str().unwrap_or("unknown").to_string())));
    Ok(records)
}

/// Summarize the author-local job records of the calls `include` selects (by call number).
pub fn local_job_summary(layout: &RunLayout, include: impl Fn(u64) -> bool) -> Result<LocalJobSummary, RecordError> {
    let mut summary = LocalJobSummary { latest: Value::Null, ..Default::default() };
    for (call, call_dir) in call_directories(layout)?.into_iter().filter(|(call, _)| include(*call)) {
        for (record, value) in call_jobs(&call_dir)? {
            let action = value["action"].as_str().unwrap_or("unknown").to_string();
            summary.jobs += 1;
            if matches!(action.as_str(), "trial" | "profile") {
                summary.local_trials += 1;
            }
            *summary.by_action.entry(action).or_default() += 1;
            if value["status"] == "refused" {
                summary.failed_jobs += 1;
            }
            summary.latest = json!({"call":call,"status":value["status"],"action":value["action"],"job_id":value["job_id"],
                "error":value["error"],"failure_class":value["failure_class"],"result_status":value.pointer("/result/status"),
                "workers":value.pointer("/result/workers"),"result_record":record,"diagnostic_only":true});
        }
    }
    Ok(summary)
}

/// One local trial or profile as the next attempt's handoff lists it: when, which crate version (`crate_version`, a
/// short identity of the frozen author sources), verified or not, and per (binding, workers) cell its status and hot
/// median.
fn local_trial_entry(call: &str, record: &Value, path: &Path) -> Value {
    let result = &record["result"];
    let cells: Vec<Value> = result
        .pointer("/real_data/cells")
        .and_then(Value::as_array)
        .into_iter()
        .flatten()
        .map(|cell| json!({"binding":cell["binding"],"workers":cell["workers"],"status":cell["status"],"median_hot_ns":cell["median_hot_wall_ns"]}))
        .collect();
    let job = path.parent().and_then(|dir| dir.file_name()).and_then(|name| name.to_str()).unwrap_or_default();
    // The job's request names the workload statement of a diagnostic query (workload role only).
    let request: Value = path.parent().and_then(|dir| fs::read(dir.join("request.json")).ok()).and_then(|b| serde_json::from_slice(&b).ok()).unwrap_or_default();
    json!({"call":call,"job_id":record["job_id"],"job":job,"statement":request["arguments"]["statement"],"action":record["action"],"status":record["status"],
        "crate_version":result["crate_version"],"verified":record["verification"] != "verification_not_run",
        "failure_class":record["failure_class"],"cells":cells,"record":path})
}

/// GenDB's facts for the fresh provider session of a new attempt (with the author's notes) that starts with call
/// `current_call`: the log of every local trial and profile of the earlier calls (crate version, cells, times, verified
/// or not), what `code_of` says about each submission's frozen code (`RolePolicy::submission_code`), the author's
/// `NOTES.md` text, and the paths where the code and records stay. The official per-submission results are added by
/// the role policy, which knows the targets. Nothing before the first provider session: the first session of the
/// first attempt has no handoff (a fresh session replacing an exhausted one of the same attempt gets it).
pub fn attempt_handoff(layout: &RunLayout, state: &LedgerState, current_call: u64, code_of: impl Fn(&Trial) -> Value) -> Result<Value, RecordError> {
    let earlier_session = state.calls.iter().any(|call| call.receipt.as_ref().is_some_and(|receipt| receipt.raw_result.is_some()));
    if state.trials.is_empty() && !earlier_session {
        return Ok(Value::Null);
    }
    let mut trials = vec![];
    for (call, call_dir) in call_directories(layout)?.into_iter().filter(|(call, _)| *call < current_call) {
        let call = format!("{call:04}");
        for (path, record) in call_jobs(&call_dir)?.iter().filter(|(_, r)| matches!(r["action"].as_str(), Some("trial" | "profile"))) {
            trials.push(local_trial_entry(&call, record, path));
        }
    }
    let submission_code: Vec<Value> = state.trials.iter().map(|trial| json!({"iteration":trial.iteration,"code":code_of(trial)})).collect();
    let workspace = layout.workspace();
    let notes_path = workspace.join(super::layout::NOTES_FILE);
    let notes = fs::read_to_string(&notes_path).ok();
    Ok(json!({"local_trials":trials,"submission_code":submission_code,
        "notes":{"file":notes_path,"text":notes},
        "paths":{"workspace":workspace,"earlier_prompts":layout.calls(),"submission_records":layout.iterations()}}))
}

/// A frozen candidate with every captured module source path replaced by the file's bytes, so two submissions
/// compare equal exactly when every non-path field and every source byte is equal.
#[derive(PartialEq)]
struct EffectiveCandidate {
    candidate: Value,
    sources: Vec<Vec<u8>>,
}

/// Convention for roles: a frozen candidate lists its captured sources as `modules[].source` paths.
fn effective_candidate(frozen_candidate: &Path) -> Result<Option<EffectiveCandidate>, RecordError> {
    if !frozen_candidate.is_file() {
        return Ok(None);
    }
    let mut candidate: Value = records::read_json(frozen_candidate)?;
    let mut sources = vec![];
    if let Some(modules) = candidate.get_mut("modules").and_then(Value::as_array_mut) {
        for (index, module) in modules.iter_mut().enumerate() {
            if let Some(source) = module.get("source").and_then(Value::as_str).map(PathBuf::from) {
                sources.push(fs::read(&source).map_err(|e| RecordError::new(&source, e))?);
                module["source"] = json!(format!("captured-source-modules-{index}"));
            }
        }
    }
    Ok(Some(EffectiveCandidate { candidate, sources }))
}

/// The earliest prior submission whose frozen candidate is effectively identical to `frozen_candidate`, with its
/// evaluation. Only candidates with captured modules are compared. A prior evaluation that failed in the framework
/// (`Trial::framework_failure`) judged nothing about the candidate and is never reused.
pub fn unchanged_prior_submission(
    layout: &RunLayout,
    frozen_candidate: &Path,
    prior_trials: &[Trial],
) -> Result<Option<(u32, Value)>, RecordError> {
    let has_modules = records::read_json::<Value>(frozen_candidate)?.get("modules").is_some_and(Value::is_array);
    let Some(current) = has_modules.then(|| effective_candidate(frozen_candidate)).transpose()?.flatten() else {
        return Ok(None);
    };
    for trial in prior_trials.iter().filter(|trial| !trial.framework_failure()) {
        if effective_candidate(&layout.frozen_candidate(trial.iteration))?.as_ref() == Some(&current) {
            return Ok(Some((trial.iteration, trial.evaluation.clone())));
        }
    }
    Ok(None)
}

/// Separate counters of author calls, submissions, distinct code versions, measured improvements and local jobs.
#[derive(Clone, Debug, Serialize)]
pub struct TrajectoryAccounting {
    pub author_calls: usize,
    /// Calls without a successful candidate output (including unsettled ones).
    pub failed_author_calls: usize,
    pub candidate_submissions: usize,
    /// Ineligible submissions that were not unchanged resubmissions.
    pub failed_submissions: usize,
    pub duplicate_submissions: usize,
    pub distinct_code_versions: usize,
    pub timed_submitted_trials: usize,
    /// New code versions with a median below the best earlier median of this run at some (binding, worker count) cell.
    pub improvements: u64,
    /// The transport's per-call tool visibility record (`tool-capabilities.json`), when it wrote one.
    pub tool_capabilities: Vec<Value>,
    pub local: LocalJobSummary,
}

pub fn trajectory_accounting(layout: &RunLayout, state: &LedgerState) -> Result<TrajectoryAccounting, RecordError> {
    let tool_capabilities = state
        .calls
        .iter()
        .map(|call| {
            let path = layout.call(call.id).join("tool-capabilities.json");
            let snapshot: Value = if path.is_file() { records::read_json(&path)? } else { Value::Null };
            Ok(json!({"call_id":call.id,"record":path,"visible_tools":snapshot["visible_tools"],
                "required_tools":snapshot["required_tools"],"missing_required_tools":snapshot["missing_required_tools"],
                "mcp_servers":snapshot["mcp_servers"]}))
        })
        .collect::<Result<Vec<_>, RecordError>>()?;
    let failed_author_calls = state
        .calls
        .iter()
        .filter(|call| call.receipt.as_ref().is_none_or(|receipt| receipt.outcome != "success" || receipt.output.is_none()))
        .count();
    let failed_submissions =
        state.trials.iter().filter(|trial| !trial.eligible() && !trial.is_unchanged_resubmission()).count();
    let timed_submitted_trials = state
        .trials
        .iter()
        .filter(|trial| trial.evaluation["measurements"].as_array().is_some_and(|cells| !cells.is_empty()))
        .count();
    let mut versions: Vec<EffectiveCandidate> = vec![];
    let mut duplicate_submissions = 0usize;
    let mut best_median_ns = BTreeMap::<(String, u64), u64>::new();
    let mut improvements = 0u64;
    for trial in &state.trials {
        // A submission without a frozen candidate (for example a failed freeze) counts as a new version.
        let new_version = match effective_candidate(&layout.frozen_candidate(trial.iteration))? {
            None => true,
            Some(version) if versions.contains(&version) => false,
            Some(version) => {
                versions.push(version);
                true
            }
        };
        if !new_version {
            duplicate_submissions += 1;
            continue;
        }
        let mut improved = false;
        for (binding, workers, median_ns) in trial.medians() {
            let best = best_median_ns.entry((binding, workers)).or_insert(median_ns);
            improved |= median_ns < *best;
            *best = (*best).min(median_ns);
        }
        improvements += u64::from(improved);
    }
    Ok(TrajectoryAccounting {
        author_calls: state.calls.len(),
        failed_author_calls,
        candidate_submissions: state.trials.len(),
        failed_submissions,
        duplicate_submissions,
        distinct_code_versions: versions.len(),
        timed_submitted_trials,
        improvements,
        tool_capabilities,
        local: local_job_summary(layout, |_| true)?,
    })
}
