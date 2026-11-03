//! A session without an author that recovers an evaluated candidate of a closed session ("reselection"). The user
//! names a closed session of the same task (`queries[i].reselect_from`). This session selects the best of that
//! session's eligible candidates that the run's policy still admits, evaluates a copy of it afresh, qualifies it and
//! closes like any session (the role's resolution, for a query: serving from library records). It is not a synthesis
//! submission: no author is invoked, this session's provider usage is zero, and the source session's usage stays
//! counted once, in the source session.
//!
//! Phases (each durable before the next, so a restarted controller repeats no completed import, evaluation,
//! qualification or closure):
//! 1. open this session's ledger (its resume identity names the source) and return an existing closure;
//! 2. check the source ([`closed_source`]): a closed ledger with complete accounting and the same task, otherwise
//!    refused by name (`reselect_source_invalid`);
//! 3. prepare the role context (as `run` does, without configuring the author, which is never called);
//! 4. select, once (`reselection.json`): the source's eligible trials in the source's own qualification order (recorded
//!    score, one candidate for every measured cell); a trial whose frozen candidate is not retained, or whose recorded
//!    evaluation the run's policy no longer admits (`SynthesisRole::policy_exclusion`), is passed over before any copy
//!    or build; the first remaining one is selected and every later one is `not_tried`;
//! 5. import the selected frozen candidate into `iterations/NNNN` (the source's iteration number) through the role
//!    (`SynthesisRole::import_frozen`), then write its provenance (`source.json`) last; an import interrupted before
//!    that record is this session's own partial copy and is started again;
//! 6. evaluate the copy afresh (`evaluation.json`) and, when it is eligible, qualify it (`qualification.json`); a
//!    failure is recorded and closes the session without a fallback candidate or an author call;
//! 7. close: the role's resolution (`resolution.json`, reused when an earlier process wrote it) and the summary; the
//!    ledger closes.
//!
//! The source session is only read. Its ledger, evaluations, qualifications, receipts and summary stay as they are.

use super::ControllerError;
use super::author::AuthorTransport;
use super::layout::RunLayout;
use super::ledger::{Ledger, LedgerState, Trial, TrialStatus};
use super::records::{self, RecordError};
use super::role::{RolePolicy, SynthesisRole};
use super::run::{RunRequest, evaluation_digest, evaluation_error, prepare_context, qualification_digest, qualification_order, qualify_recorded, role_error};
use serde_json::{Value, json};
use std::fs;
use std::path::Path;
use std::time::Instant;

/// The class of every refusal of a reselection source.
pub const SOURCE_REFUSAL: &str = "reselect_source_invalid";

/// The selection record of a reselection session, written once.
pub const SELECTION_FILE: &str = "reselection.json";

/// Provenance of an imported candidate (`iterations/NNNN/source.json`); written last, it marks the import complete.
pub const SOURCE_FILE: &str = "source.json";

/// The summary `reason` of a reselection session.
pub const RESELECTED: &str = "reselected_from_closed_session";

/// How the candidate is selected (recorded in `reselection.json`).
const SELECTION_RULE: &str = "the source session's own qualification order (eligible trials by recorded score_ns, ties in iteration order; one candidate for every measured cell); a trial whose frozen candidate is not retained or whose recorded evaluation the run's policy no longer admits is passed over before any copy or build; the first remaining trial is selected and evaluated afresh; a failed fresh evaluation or qualification closes the session without trying another candidate or calling an author";

/// The closed source session at `source`: its ledger state, refused by name unless the session is closed with
/// complete accounting.
pub fn closed_source(source: &Path) -> Result<LedgerState, String> {
    let ledger = RunLayout::new(source).ledger();
    let state: LedgerState = records::read_json(&ledger).map_err(|e| format!("{SOURCE_REFUSAL}: the source session's ledger: {e}"))?;
    match &state.closed {
        Some(closed) if closed["status"] == "closed" && closed["cost_complete"] == true => Ok(state),
        Some(closed) => Err(format!(
            "{SOURCE_REFUSAL}: source session {} closed with status {} and cost_complete {}; only a closed session with complete accounting is reselected",
            source.display(),
            closed["status"],
            closed["cost_complete"]
        )),
        None => Err(format!("{SOURCE_REFUSAL}: source session {} is open; only a closed session is reselected", source.display())),
    }
}

/// Run the reselection session in `root` from the closed session `source`. `author` is the session's configured
/// transport: it is recorded in the resume identity and never invoked. Returns the session summary (also written to
/// `summary.json`).
pub async fn reselect<A: AuthorTransport, R: SynthesisRole>(
    request: &RunRequest,
    root: &Path,
    source: &Path,
    author: &A,
    role: &mut R,
) -> Result<Value, ControllerError> {
    request.validate()?;
    records::create_dir(root)?;
    let root = root.canonicalize().map_err(|e| RecordError::new(root, e))?;
    let layout = RunLayout::new(&root);
    let capability = author.capability();
    let mut ledger = Ledger::open(&root, json!({"request":request,"author":capability,"reselect_from":source}), request.limits.clone())?;
    if let Some(closed) = &ledger.state.closed {
        return Ok(closed.clone());
    }
    let source = source.canonicalize().map_err(|e| ControllerError::InvalidRequest(format!("{SOURCE_REFUSAL}: {}: {e}", source.display())))?;
    let source_state = closed_source(&source).map_err(ControllerError::InvalidRequest)?;
    if source_state.request["request"]["task"] != request.task {
        return Err(ControllerError::InvalidRequest(format!("{SOURCE_REFUSAL}: source session {} ran another task", source.display())));
    }
    for directory in [layout.workspace(), layout.iterations()] {
        records::create_dir(&directory)?;
    }
    let reason = if layout.context().exists() { "controller_process_resume" } else { "initial_run" };
    let context = prepare_context(role, request, &layout, reason).await?;
    let selection = select(role, &layout, &source, &source_state).await?;
    let selected = selection["selected_iteration"].as_u64().and_then(|n| source_state.trials.iter().find(|t| u64::from(t.iteration) == n));
    let mut trials = vec![];
    let mut qualification = vec![];
    if let Some(source_trial) = selected {
        let trial = import_and_evaluate(role, &layout, &source, source_trial).await?;
        if trial.eligible() {
            qualification.push(qualify_recorded(role, &layout, trial.iteration, &trial.evaluation).await?);
        }
        trials.push(trial);
    }
    let started = Instant::now();
    let resolution = if layout.resolution().exists() {
        records::read_json(&layout.resolution())?
    } else {
        let resolution = role.close(&trials, &qualification).await.map_err(role_error("close"))?;
        records::write_json_atomic(&layout.resolution(), &resolution)?;
        resolution
    };
    let close_elapsed_ms = started.elapsed().as_millis() as u64;
    let totals = ledger.totals()?;
    let trajectory: Vec<Value> = trials
        .iter()
        .map(|trial| {
            json!({"iteration":trial.iteration,"directory":layout.iteration(trial.iteration),"source":layout.iteration(trial.iteration).join(SOURCE_FILE),
                "evaluation":evaluation_digest(&trial.evaluation),"evaluation_record":layout.evaluation(trial.iteration),
                "framework_elapsed_ms":trial.framework_elapsed_ms})
        })
        .collect();
    let source_closed = source_state.closed.as_ref().expect("closed_source checked the closure");
    let summary = json!({"status":"closed","reason":RESELECTED,"inference_dispatched":false,
        "objective":role.policy().objective_status(&context, &trials),
        "session_id":ledger.state.session_id,"provider":capability,"limits":request.limits,
        "iterations":0,"calls":ledger.state.calls.len(),
        "reported_cost_usd":totals.spent,"known_reported_cost_usd":totals.spent,"outstanding_reservation_usd":totals.reserved,
        "cost_complete":!totals.usage_unknown,"cost_kind":"provider_reported","accounting":ledger.accounting(None)?,"author_elapsed_ms":0,
        "reselection":{"record":layout.root().join(SELECTION_FILE),"source":selection["source"],"selected_iteration":selection["selected_iteration"],
            "candidates":selection["candidates"]},
        "source_accounting":{"session":source,"session_id":source_state.session_id,"summary":RunLayout::new(&source).summary(),
            "reported_cost_usd":source_closed["reported_cost_usd"],"calls":source_closed["calls"],"iterations":source_closed["iterations"],
            "tokens":source_closed.pointer("/accounting/tokens"),
            "counting":"counted once in the source session; not added to this session or its workload"},
        "trajectory":trajectory,"qualification":qualification_digest(&layout, &qualification),
        "close_framework_elapsed_ms":close_elapsed_ms,"resolution":resolution,"resolution_record":layout.resolution(),"ledger":layout.ledger(),
        "scope":"no author call and no synthesis submission: a closed session's evaluated candidate, selected under the run's policy, imported, evaluated afresh, qualified and closed by the role; framework evaluation, qualification and close times are this session's own"});
    ledger.state.closed = Some(summary.clone());
    ledger.save()?;
    records::write_json_atomic(&layout.summary(), &summary)?;
    Ok(summary)
}

/// The selection of this session: its record when an earlier process wrote it, else the decision over the source's
/// eligible trials ([`SELECTION_RULE`]), recorded once.
async fn select<R: SynthesisRole>(role: &mut R, layout: &RunLayout, source: &Path, state: &LedgerState) -> Result<Value, ControllerError> {
    let path = layout.root().join(SELECTION_FILE);
    if path.exists() {
        return Ok(records::read_json(&path)?);
    }
    let source_layout = RunLayout::new(source);
    let mut selected = None;
    let mut candidates = vec![];
    for trial in qualification_order(&state.trials) {
        let iteration = trial.iteration;
        let (decision, reason) = if selected.is_some() {
            ("not_tried", Value::Null)
        } else if !source_layout.frozen(iteration).is_dir() || !source_layout.frozen_candidate(iteration).is_file() {
            ("incomplete_source", json!("the source session does not retain this frozen candidate"))
        } else if let Some(reason) = role.policy_exclusion(&trial.evaluation).await.map_err(role_error("policy exclusion"))? {
            ("policy_excluded", json!(reason))
        } else {
            selected = Some(iteration);
            ("selected", Value::Null)
        };
        candidates.push(json!({"iteration":iteration,"call_id":trial.call_id,"score_ns":trial.evaluation["score_ns"],
            "evaluation_record":trial.evaluation_record.clone().unwrap_or_else(|| source_layout.evaluation(iteration)),
            "decision":decision,"reason":reason}));
    }
    let closed = state.closed.as_ref().unwrap_or(&Value::Null);
    let record = json!({"format_version":1,"rule":SELECTION_RULE,
        "source":{"session":source,"session_id":state.session_id,"closed_reason":closed["reason"],"summary":source_layout.summary(),
            "trials":state.trials.len(),"eligible_trials":candidates.len()},
        "candidates":candidates,"selected_iteration":selected,"recorded_unix_ms":records::now_unix_ms()});
    records::write_new_json(&path, &record)?;
    Ok(record)
}

/// Import the selected source trial into this session (unless an earlier process completed the import), then
/// evaluate the copy afresh (unless its evaluation is recorded). The returned trial is this session's view of the
/// candidate; it is not a ledger submission (`call_id` 0: no call of this session produced it).
async fn import_and_evaluate<R: SynthesisRole>(role: &mut R, layout: &RunLayout, source: &Path, source_trial: &Trial) -> Result<Trial, ControllerError> {
    let iteration = source_trial.iteration;
    let source_layout = RunLayout::new(source);
    let directory = layout.iteration(iteration);
    let provenance = directory.join(SOURCE_FILE);
    if !provenance.exists() {
        if directory.exists() {
            // Only this session writes here, and nothing is evaluated before the provenance record: a partial copy.
            fs::remove_dir_all(&directory).map_err(|e| RecordError::new(&directory, e))?;
        }
        records::create_dir(&directory)?;
        let started = Instant::now();
        let candidate = role.import_frozen(&source_layout.frozen(iteration), &layout.frozen(iteration)).await.map_err(role_error("import"))?;
        records::write_new_json(&layout.frozen_candidate(iteration), &candidate)?;
        records::write_new_json(
            &provenance,
            &json!({"format_version":1,"source_session":source,"source_iteration":source_layout.iteration(iteration),
                "source_frozen":source_layout.frozen(iteration),"source_frozen_candidate":source_layout.frozen_candidate(iteration),
                "source_evaluation_record":source_trial.evaluation_record.clone().unwrap_or_else(|| source_layout.evaluation(iteration)),
                "source_status":source_trial.evaluation["status"],"source_score_ns":source_trial.evaluation["score_ns"],
                "source_call_id":source_trial.call_id,"import_framework_elapsed_ms":started.elapsed().as_millis() as u64,
                "copied":"the frozen sources and their metadata only (no evaluation or qualification outputs); location metadata rebased onto this copy"}),
        )?;
    }
    let candidate: Value = records::read_json(&layout.frozen_candidate(iteration))?;
    let (evaluation, framework_elapsed_ms) = if layout.evaluation(iteration).exists() {
        (records::read_json(&layout.evaluation(iteration))?, None)
    } else {
        let started = Instant::now();
        let evaluation = role.evaluate(&layout.frozen(iteration), &candidate).await.unwrap_or_else(evaluation_error);
        records::write_new_json(&layout.evaluation(iteration), &evaluation)?;
        (evaluation, Some(started.elapsed().as_millis() as u64))
    };
    Ok(Trial {
        iteration,
        call_id: 0,
        candidate: source_trial.candidate.clone(),
        status: TrialStatus::Evaluated,
        evaluation,
        framework_elapsed_ms,
        directory: Some(directory),
        recovery_records: vec![],
        evaluation_record: None,
    })
}

#[cfg(test)]
mod tests;
