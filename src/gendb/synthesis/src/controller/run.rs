//! The generic author-session state machine. The author proposes; this controller counts calls and submissions,
//! evaluates, feeds back, qualifies and closes, for any `SynthesisRole`.
//!
//! One `run` of a session directory goes through these phases in order (each is durable before the next starts, so a
//! controller that stops anywhere resumes from its records without replaying a paid author call):
//!
//! 1. open the ledger (same request, provider and active limits when resuming); a proven pre-dispatch transport
//!    refusal may reopen its closure once;
//! 2. return an existing closure, or refuse an unsupported capability before any preparation;
//! 3. reconcile calls that were dispatched but never settled, from durable receipts or the transport's own records;
//!    unresolved usage before any submission stops here with `accounting_unresolved`;
//! 4. prepare the role's context;
//! 5. finish evaluations interrupted after submission, then apply framework repair revisions to retained frozen
//!    submissions (never dispatching an author); a continuing session (`RunRequest::continue_from`) establishes its
//!    incumbent: the earlier session's admitted candidate written into the workspace, frozen and evaluated as iteration
//!    0 (`Session::establish_incumbent`), which then competes in the search stop, selection and qualification like a
//!    submission without being one;
//! 6. search: author call → settle receipt → submit → freeze → evaluate (or reuse an unchanged prior result), until a
//!    ledger guard, the role policy, the unchanged-resubmission rule or the operator's stop record (`operator-stop.json`,
//!    [`record_operator_stop`], read before every call) stops it; after a call the provider ended
//!    (rate limit, other API error, exhausted context, refused account) `provider_wait` decides whether to wait for the
//!    provider, start a fresh provider session, or stop with a named refusal;
//! 7. qualify eligible trials, best score first, until one qualifies;
//! 8. close: the role's resolution, accounting and the summary. A run whose usage is still unknown is summarized
//!    but stays open (resumable) until usage is reconciled.
//!
//! Internal author trials (local jobs) are diagnostics only; submissions are evaluated here and final measurements
//! belong to the role's qualification/close stages.

use super::ControllerError;
use super::author::{AuthorCall, AuthorTransport, CandidateSubmission, Capability};
use super::layout::{INCUMBENT_ITERATION, RunLayout};
use super::ledger::{Accounting, Call, Ledger, LedgerState, LedgerStop, Receipt, RepairRecord, Trial, TrialStatus, UsageScope, attribute_repeated_checker_failure, framework_failure};
use super::limits::{Limits, Money, SpendPolicy, count_guard};
use super::provider_wait::{self, ProviderWait};
use super::records::{self, RecordError};
use super::role::{PromptInput, QualificationAttempt, RolePolicy, SynthesisRole, call_event, local_jobs_event};
use super::trajectory::{self, TrajectoryAccounting};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::Instant;

/// One author session request (`format_version` 1). `task` is the role's task description; it is part of the resume
/// identity and is passed to `SynthesisRole::prepare`.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RunRequest {
    pub format_version: u32,
    pub task: Value,
    pub limits: Limits,
    /// A closed session of an earlier run to continue from (`queries[].continue_from`): the candidate it admitted is
    /// this session's incumbent (`Session::establish_incumbent`). Part of the resume identity. Absent: the session
    /// starts without an incumbent, and the request keeps its identity.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub continue_from: Option<PathBuf>,
}

impl RunRequest {
    pub(super) fn validate(&self) -> Result<(), ControllerError> {
        if self.format_version != 1 {
            return Err(ControllerError::InvalidRequest("unsupported integrated run format".into()));
        }
        self.limits.validate().map_err(ControllerError::InvalidRequest)
    }
}

/// Why the search stopped (the summary's `reason`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StopReason {
    /// The submission guard is reached.
    IterationLimit,
    /// Provider-reported cost plus outstanding reservations reached the dollar guard.
    BudgetLimit,
    /// Some call's usage is unknown, so no further call may start.
    UsageUnknown,
    /// The current iteration used all its attempts without a submission.
    RetryLimit,
    /// The role's objective needs only one eligible candidate (for example a correctness objective).
    FirstEligibleCandidate,
    /// The candidate qualified first (`qualification_order`) is at least the user's `early_stop.min_speedup` times
    /// faster than the runtime target at every configured worker count (execution-time objective).
    EarlyStopMinSpeedup,
    /// The transport refused the call before launching a provider process (proven); retrying would loop.
    AuthorReadinessRefusal,
    /// The same invalid structured output was refused with the same outcome twice in a row.
    UnchangedInvalidOutput,
    /// An unchanged resubmission while the objective is not unmet.
    UnchangedEffectiveCandidate,
    /// A second consecutive unchanged resubmission while the objective is unmet.
    UnchangedAfterContinueObjectiveUnmet,
    /// The role hands the work on to a fresh author session after an evaluated submission (a general-engine session
    /// whose author asked for a fresh session, whose provider compacted its context, or whose run moves up the scale
    /// ladder; `engine::sessions`).
    FreshSession,
    /// The operator recorded a stop of this session (`operator-stop.json`, [`record_operator_stop`]): no further author
    /// call; the session qualifies its best candidate and closes as usual.
    OperatorStop,
}

impl StopReason {
    pub fn as_str(self) -> &'static str {
        match self {
            StopReason::IterationLimit => "iteration_limit",
            StopReason::BudgetLimit => "budget_limit",
            StopReason::UsageUnknown => "usage_unknown",
            StopReason::RetryLimit => "retry_limit",
            StopReason::FirstEligibleCandidate => "first_eligible_candidate",
            StopReason::EarlyStopMinSpeedup => "early_stop_min_speedup",
            StopReason::AuthorReadinessRefusal => "author_readiness_refusal",
            StopReason::UnchangedInvalidOutput => "unchanged_invalid_output",
            StopReason::UnchangedEffectiveCandidate => "unchanged_effective_candidate",
            StopReason::UnchangedAfterContinueObjectiveUnmet => "unchanged_after_continue_objective_unmet",
            StopReason::FreshSession => "fresh_session",
            StopReason::OperatorStop => "operator_stop",
        }
    }
}

impl From<LedgerStop> for StopReason {
    fn from(stop: LedgerStop) -> Self {
        match stop {
            LedgerStop::IterationLimit => StopReason::IterationLimit,
            LedgerStop::UsageUnknown => StopReason::UsageUnknown,
            LedgerStop::BudgetLimit => StopReason::BudgetLimit,
            LedgerStop::RetryLimit => StopReason::RetryLimit,
        }
    }
}

/// After an unchanged resubmission: while the objective is `"unmet"` the search continues once; a second consecutive
/// unchanged resubmission stops it unmet. Any other objective status closes the search. Ledger guards still apply.
pub fn unchanged_resubmission_stop(objective: &Value, trials: &[Trial]) -> Option<StopReason> {
    if objective["status"] != "unmet" {
        return Some(StopReason::UnchangedEffectiveCandidate);
    }
    let previous_unchanged = trials.len() > 1 && trials[trials.len() - 2].is_unchanged_resubmission();
    previous_unchanged.then_some(StopReason::UnchangedAfterContinueObjectiveUnmet)
}

/// The eligible trials in the order they are qualified: ascending score, ties in iteration order. The first one is
/// the candidate the session selects unless its qualification fails.
pub fn qualification_order(trials: &[Trial]) -> Vec<&Trial> {
    let mut eligible: Vec<&Trial> = trials.iter().filter(|trial| trial.eligible()).collect();
    eligible.sort_by(|a, b| a.score_ns().total_cmp(&b.score_ns()));
    eligible
}

/// The field a render-only author's incumbent evaluation carries (`AuthorTransport::render_only`): the source
/// session's recorded evaluation shown instead of a fresh one. Such an evaluation is never qualified.
pub const RENDER_ONLY_FIELD: &str = "render_only";

/// Record the operator's stop of the author session in `session` (`gendb operator-stop SESSION_DIR REASON`): its
/// controller makes no further author call. A call in progress ends normally (or when the operator interrupts its
/// provider process group); before the next call the session stops with `operator_stop`, qualifies its best candidate
/// (a continuing session's incumbent included) and closes as usual; a relaunched controller does the same. Written once
/// (`operator-stop.json`; a second request returns the first record); refused for a directory without a ledger or a
/// closed session. Never signals a process.
pub fn record_operator_stop(session: &Path, reason: &str) -> Result<Value, String> {
    let layout = RunLayout::new(session);
    let state: LedgerState = records::read_json(&layout.ledger()).map_err(|e| format!("{} is not an author session: {e}", session.display()))?;
    if state.closed.is_some() {
        return Err(format!("{} is closed ({}); nothing to stop", session.display(), state.closed.as_ref().map_or(Value::Null, |c| c["reason"].clone())));
    }
    if layout.operator_stop().exists() {
        return records::read_json(&layout.operator_stop()).map_err(|e| e.to_string());
    }
    if reason.trim().is_empty() {
        return Err("the stop needs a reason".into());
    }
    let record = json!({"format_version":1,"by":"operator","reason":reason,"recorded_unix_ms":records::now_unix_ms(),
        "calls_so_far":state.calls.len(),"submissions_so_far":state.iterations,
        "meaning":"no further author call in this session; it qualifies its best candidate and closes with reason operator_stop"});
    records::write_new_json(&layout.operator_stop(), &record).map_err(|e| e.to_string())?;
    Ok(record)
}

/// The ledger's resume identity of a session.
fn run_identity(request: &RunRequest, capability: &Capability) -> Value {
    json!({"request":request,"author":capability})
}

fn author_error(stage: &'static str) -> impl FnOnce(String) -> ControllerError {
    move |detail| ControllerError::Author { stage, detail }
}

pub(super) fn role_error(stage: &'static str) -> impl FnOnce(String) -> ControllerError {
    move |detail| ControllerError::Role { stage, detail }
}

/// An evaluation stage error becomes the submission's recorded outcome.
pub(super) fn evaluation_error(error: String) -> Value {
    json!({"eligible":false,"status":"evaluation_error","error":error})
}

fn budget_enforcement(capability: &Capability, limits: &Limits) -> &'static str {
    if capability.hard_usd_cap && limits.spend_policy == SpendPolicy::StrictUsd { "strict_cap" } else { "stop_guard" }
}

/// Every call so far is a settled zero-usage transport refusal whose durable receipt matches the ledger and which the
/// transport proves was never launched.
fn predispatch_recovery_proven<A: AuthorTransport>(
    layout: &RunLayout,
    state: &LedgerState,
    author: &A,
) -> Result<bool, ControllerError> {
    if !state.predispatch_recovery_candidate() {
        return Ok(false);
    }
    for call in &state.calls {
        let receipt_path = layout.receipt(call.id);
        if !receipt_path.is_file()
            || Some(&records::read_json::<Receipt>(&receipt_path)?) != call.receipt.as_ref()
            || !author.definitely_not_dispatched(&layout.call(call.id)).map_err(author_error("dispatch proof"))?
        {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Metadata-only routing check for a workload controller deciding whether a published session summary may resume.
/// The actual recovery is rechecked by `run` under the ledger lock with an unchanged request identity.
pub fn predispatch_recovery_available<A: AuthorTransport>(
    root: &Path,
    author: &A,
    published: Option<&Value>,
) -> Result<bool, ControllerError> {
    let layout = RunLayout::new(root);
    if !layout.ledger().exists() {
        return Ok(false);
    }
    let state: LedgerState = records::read_json(&layout.ledger())?;
    // A crash after the atomic recovery write may leave an older published summary: continue that open ledger, but
    // never authorize a second recovery.
    if state.closed.is_none() && !state.predispatch_recoveries.is_empty() {
        return Ok(true);
    }
    // A recovered session can finish before its workload publishes a new summary. Advance from that stale summary
    // without reopening the now closed ledger; only this recovery's exact prior closure is superseded.
    if let Some(published) = published {
        let superseded = published.is_object()
            && state.closed.as_ref() != Some(published)
            && state.predispatch_recoveries.iter().any(|recovery| &recovery["prior_closed"] == published);
        if superseded {
            return Ok(true);
        }
    }
    predispatch_recovery_proven(&layout, &state, author)
}

/// Record why a call was found unsettled when the controller restarted (`interruption-<ms>.json` in its directory):
/// the controller stopped while the call was dispatched, and the last provider heartbeat the transport wrote, if any.
/// Evidence only; the receipt (or its absence) decides the accounting.
fn record_interruption(call_dir: &Path, call: &Call, recovered: Option<&Receipt>) -> Result<(), ControllerError> {
    if !call_dir.is_dir() {
        return Ok(());
    }
    let heartbeat = call_dir.join("heartbeat.json");
    let last_heartbeat: Value = if heartbeat.is_file() { records::read_json(&heartbeat).unwrap_or(Value::Null) } else { Value::Null };
    records::write_json_atomic(
        &call_dir.join(format!("interruption-{}.json", records::now_unix_ms())),
        &json!({"call_id":call.id,"iteration":call.iteration,"attempt":call.attempt,"provider_session":call.provider_session,
            "found":"dispatched without a settled receipt when the controller (re)started",
            "last_heartbeat":last_heartbeat,"receipt_recovered":recovered.map(|r| &r.outcome),
            "next":"a retry of this attempt resumes its provider session when the transport shows the session exists"}),
    )?;
    Ok(())
}

/// Calls found unsettled when the controller (re)started.
struct UnsettledCalls {
    /// Reserved calls the transport proves were never launched: dispatched again as the same call.
    not_dispatched: BTreeMap<u64, Call>,
    /// Some dispatched call has no receipt and no recoverable evidence: its usage is unknown.
    usage_unresolved: bool,
}

/// What one author call produced.
enum CallOutcome {
    /// A settled call with a validated candidate output.
    Candidate(Call),
    /// No candidate; the iteration may retry within its guard.
    NoCandidate,
    Stop(StopReason),
}

/// Run one author session to closure, or to a resumable stop, in `root`. Capability refusals happen before any
/// preparation or author invocation. Returns the session summary (also written to `summary.json`).
pub async fn run<A: AuthorTransport, R: SynthesisRole>(
    request: &RunRequest,
    root: &Path,
    author: &mut A,
    role: &mut R,
) -> Result<Value, ControllerError> {
    request.validate()?;
    records::create_dir(root)?;
    let root = root.canonicalize().map_err(|e| RecordError::new(root, e))?;
    let layout = RunLayout::new(&root);
    let capability = author.capability();
    let mut ledger = Ledger::open(&root, run_identity(request, &capability), request.limits.clone())?;
    if predispatch_recovery_proven(&layout, &ledger.state, author)? {
        // A failed readiness check must not reopen the closure.
        author.preflight().map_err(author_error("preflight"))?;
        record_predispatch_recovery(&layout, &mut ledger, &capability)?;
    }
    if let Some(closed) = &ledger.state.closed {
        return Ok(closed.clone());
    }
    if request.limits.spend_policy == SpendPolicy::StrictUsd && !capability.hard_usd_cap {
        return close_unsupported_capability(&layout, &mut ledger, &capability);
    }
    if !capability.persistent_sessions {
        return Err(ControllerError::InvalidRequest("persistent author session required".into()));
    }
    author.preflight().map_err(author_error("preflight"))?;
    for directory in [layout.workspace(), layout.calls(), layout.iterations()] {
        records::create_dir(&directory)?;
    }
    let policy = role.policy();
    let mut session = Session { request, layout, capability, ledger, author, role, policy, context: Value::Null, feedback: vec![] };
    let mut unsettled = session.reconcile_unsettled_calls()?;
    if unsettled.usage_unresolved && session.ledger.state.trials.is_empty() && session.ledger.totals()?.usage_unknown {
        return session.summarize_unresolved_before_preparation();
    }
    session.prepare().await?;
    session.finish_interrupted_evaluations().await?;
    session.apply_framework_repairs().await?;
    session.establish_incumbent().await?;
    let stop = session.search(&mut unsettled).await?;
    let qualification = session.qualify_best().await?;
    session.close(stop, qualification).await
}

/// Archive the closure being recovered and authorize the one automatic pre-dispatch recovery: the calls, session,
/// request and limits stay; these setup refusals no longer count as retries.
fn record_predispatch_recovery(layout: &RunLayout, ledger: &mut Ledger, capability: &Capability) -> Result<(), ControllerError> {
    let prior_summary: Option<Value> =
        if layout.summary().exists() { Some(records::read_json(&layout.summary())?) } else { None };
    let recovery = json!({"format_version":1,"reason":"proven pre-dispatch activity transport refusal",
        "recovered_unix_ms":records::now_unix_ms(),"call_ids":ledger.state.calls.iter().map(|call| call.id).collect::<Vec<_>>(),
        "prior_closed":ledger.state.closed,"prior_summary":prior_summary,
        "provider":capability,"accounting":ledger.accounting(None)?,
        "evidence":"durable matching zero-cost receipt; transport proves no author process launched",
        "action":"retain calls, session, request and limits; exclude these setup failures from model-call retry accounting",
        "automatic_recovery_limit":1});
    ledger.state.predispatch_recoveries.push(recovery);
    ledger.state.closed = None;
    Ok(ledger.save()?)
}

fn close_unsupported_capability(layout: &RunLayout, ledger: &mut Ledger, capability: &Capability) -> Result<Value, ControllerError> {
    let summary = json!({"status":"unsupported_capability",
        "reason":"selected transport cannot enforce a hard dollar cap; estimated_usd (legacy name for the provider-cost stop guard) must be explicitly selected",
        "provider":capability,"inference_dispatched":false});
    ledger.state.closed = Some(summary.clone());
    ledger.save()?;
    records::write_json_atomic(&layout.summary(), &summary)?;
    Ok(summary)
}

/// Prepare the role context in the session's workspace and record it: `context.json` the first time, else
/// `context-preparation-<ms>.json` beside it, plus this preparation's wall time and `reason` (`preparation-<ms>.json`).
pub(super) async fn prepare_context<R: SynthesisRole>(role: &mut R, request: &RunRequest, layout: &RunLayout, reason: &str) -> Result<Value, ControllerError> {
    let started = Instant::now();
    let context = role.prepare(request, &layout.workspace()).await.map_err(role_error("prepare"))?;
    let root = layout.root();
    let context_record = if layout.context().exists() {
        root.join(format!("context-preparation-{}.json", records::now_unix_ms()))
    } else {
        layout.context()
    };
    records::write_json_atomic(&context_record, &context)?;
    records::write_json_atomic(
        &root.join(format!("preparation-{}.json", records::now_unix_ms())),
        &json!({"elapsed_ms":started.elapsed().as_millis(),"context_record":context_record,"reason":reason}),
    )?;
    Ok(context)
}

/// Qualify the eligible candidate frozen at `iteration` with its `evaluation`, or reuse its recorded qualification
/// (`qualification.json`), so a resumed controller never qualifies a candidate twice. A qualify stage error is the
/// recorded result (`"qualified": false`).
pub(super) async fn qualify_recorded<R: SynthesisRole>(role: &mut R, layout: &RunLayout, iteration: u32, evaluation: &Value) -> Result<QualificationAttempt, ControllerError> {
    let path = layout.qualification(iteration);
    let result = if path.exists() {
        records::read_json(&path)?
    } else {
        let started = Instant::now();
        let mut result = match role.qualify(&layout.frozen(iteration), evaluation).await {
            Ok(result) => result,
            Err(error) => json!({"qualified":false,"error":error}),
        };
        if let Some(fields) = result.as_object_mut() {
            fields.insert("framework_elapsed_ms".into(), json!(started.elapsed().as_millis() as u64));
        }
        records::write_json_atomic(&path, &result)?;
        result
    };
    Ok(QualificationAttempt { iteration, result })
}

/// The closing summary of a session (`summary.json`, and the ledger closure when accounting is complete).
#[derive(Serialize)]
struct RunSummary<'a> {
    /// `closed`, or `accounting_unresolved` (resumable) when some usage is unknown.
    status: &'static str,
    reason: &'static str,
    objective: Value,
    session_id: &'a str,
    provider: &'a Capability,
    limits: &'a Limits,
    remaining_limits: Value,
    iterations: u32,
    calls: usize,
    reported_cost_usd: Option<Money>,
    known_reported_cost_usd: Money,
    outstanding_reservation_usd: Money,
    cost_complete: bool,
    cost_kind: &'static str,
    budget_enforcement: &'static str,
    known_budget_overshoot_usd: Money,
    budget_overshoot_complete: bool,
    accounting: Accounting,
    iteration_accounting: Vec<Value>,
    trajectory_accounting: TrajectoryAccounting,
    author_elapsed_ms: u128,
    trajectory: Vec<Value>,
    /// A continuing session's incumbent (iteration 0): its provenance record and evaluation digest.
    #[serde(skip_serializing_if = "Option::is_none")]
    incumbent: Option<Value>,
    qualification: Vec<Value>,
    resolution: Value,
    resolution_record: PathBuf,
    ledger: PathBuf,
}

/// Evaluation fields kept in the summary's trajectory (the full evaluation stays in its record).
pub(super) fn evaluation_digest(evaluation: &Value) -> Value {
    let mut digest = serde_json::Map::new();
    for (key, value) in evaluation.as_object().into_iter().flatten() {
        let kept = key.ends_with("_ns")
            || key.ends_with("_ms")
            || matches!(key.as_str(), "status" | "error" | "failure_class" | "eligible" | "qualified");
        if kept {
            digest.insert(key.clone(), value.clone());
        }
    }
    if let Some(cells) = evaluation["measurements"].as_array() {
        let cells = cells.iter().map(|cell| {
            json!({"binding":cell["binding"],"workers":cell["workers"],"status":cell["status"],"median_ns":cell["median_ns"],
                "samples_ns":cell["samples_ns"],"boundary":cell["boundary"]})
        });
        digest.insert("measurements".into(), Value::Array(cells.collect()));
    }
    Value::Object(digest)
}

/// The qualification fields kept in a summary (the full result stays in `qualification.json`).
pub(super) fn qualification_digest(layout: &RunLayout, qualification: &[QualificationAttempt]) -> Vec<Value> {
    qualification
        .iter()
        .map(|attempt| {
            let result = &attempt.result;
            json!({"iteration":attempt.iteration,
                "result":{"qualified":result["qualified"],"admission":result["admission"],"error":result["error"],
                    "framework_elapsed_ms":result["framework_elapsed_ms"]},
                "qualification_record":layout.qualification(attempt.iteration)})
        })
        .collect()
}

/// One session's live state between phases.
struct Session<'a, A: AuthorTransport, R: SynthesisRole> {
    request: &'a RunRequest,
    layout: RunLayout,
    capability: Capability,
    ledger: Ledger,
    author: &'a mut A,
    role: &'a mut R,
    policy: R::Policy,
    /// The prepared role context (null until `prepare`).
    context: Value,
    /// Author feedback events, in order (see `PromptInput::feedback`).
    feedback: Vec<Value>,
}

impl<A: AuthorTransport, R: SynthesisRole> Session<'_, A, R> {
    /// Settle calls left without a receipt by an interrupted controller. No zero-cost settlement is inferred and no
    /// paid call is replayed.
    fn reconcile_unsettled_calls(&mut self) -> Result<UnsettledCalls, ControllerError> {
        let mut not_dispatched = BTreeMap::new();
        let unsettled: Vec<Call> = self.ledger.state.calls.iter().filter(|call| call.receipt.is_none()).cloned().collect();
        for call in unsettled {
            let call_dir = self.layout.call(call.id);
            let receipt_path = self.layout.receipt(call.id);
            let receipt = if receipt_path.exists() {
                Some(records::read_json::<Receipt>(&receipt_path)?)
            } else {
                let session_id = self.ledger.state.provider_session_of(&call).to_string();
                let recovered = self
                    .author
                    .recover_receipt(&call, &session_id, &call_dir, &self.layout.workspace())
                    .map_err(author_error("receipt recovery"))?;
                record_interruption(&call_dir, &call, recovered.as_ref())?;
                if let Some(receipt) = &recovered {
                    records::write_json_atomic(&receipt_path, receipt)?;
                }
                recovered
            };
            if let Some(receipt) = receipt {
                self.ledger.settle(receipt)?;
            } else if self.author.definitely_not_dispatched(&call_dir).map_err(author_error("dispatch proof"))? {
                records::create_dir(&call_dir)?;
                records::write_json_atomic(
                    &call_dir.join(format!("undispatched-recovery-{}.json", records::now_unix_ms())),
                    &json!({"call_id":call.id,"iteration":call.iteration,"reason":"transport proves process was never launched",
                        "action":"retain and dispatch the same reserved call; no usage receipt inferred"}),
                )?;
                not_dispatched.insert(call.id, call);
            } else if self.author.usage_scope() == Some(UsageScope::Session) && self.author.provider_session_exists(&call_dir) {
                // The retry of this attempt resumes the session; its session total includes this call's usage.
                self.ledger.await_session_resume(call.id)?;
            }
        }
        let usage_unresolved = self
            .ledger
            .state
            .calls
            .iter()
            .any(|call| call.receipt.is_none() && !call.usage_in_resumed_session && !not_dispatched.contains_key(&call.id));
        Ok(UnsettledCalls { not_dispatched, usage_unresolved })
    }

    /// Stop before preparation: a dispatched call's usage is unknown and nothing was submitted.
    fn summarize_unresolved_before_preparation(&self) -> Result<Value, ControllerError> {
        let totals = self.ledger.totals()?;
        let limits = &self.request.limits;
        let summary = json!({"status":"accounting_unresolved","reason":StopReason::UsageUnknown.as_str(),
            "session_id":self.ledger.state.session_id,"provider":self.capability,"reported_cost_usd":null,
            "known_reported_cost_usd":totals.spent,"accounting":self.ledger.accounting(None)?,
            "outstanding_reservation_usd":totals.reserved,"cost_complete":false,"cost_kind":"provider_reported",
            "budget_enforcement":budget_enforcement(&self.capability, limits),
            "known_budget_overshoot_usd":totals.spent.saturating_sub(limits.max_cost_usd),"budget_overshoot_complete":false,
            "iterations":0,"calls":self.ledger.state.calls.len(),"ledger":self.layout.ledger(),"resumable":true});
        records::write_json_atomic(&self.layout.summary(), &summary)?;
        Ok(summary)
    }

    /// Prepare the role context and give it to the author transport. A resumed controller prepares again.
    async fn prepare(&mut self) -> Result<(), ControllerError> {
        let reason = if self.ledger.state.calls.is_empty() { "initial_run" } else { "controller_process_resume" };
        let context = prepare_context(self.role, self.request, &self.layout, reason).await?;
        self.author.configure_context(&context).map_err(author_error("configure context"))?;
        self.context = context;
        Ok(())
    }

    /// Evaluate submissions counted before an interruption. A frozen candidate is evaluated again locally; an
    /// incomplete freeze is not reconstructed from mutable author files. No author call is replayed.
    async fn finish_interrupted_evaluations(&mut self) -> Result<(), ControllerError> {
        for index in 0..self.ledger.state.trials.len() {
            if self.ledger.state.trials[index].status != TrialStatus::Submitted {
                continue;
            }
            let iteration = self.ledger.state.trials[index].iteration;
            let evaluation_path = self.layout.evaluation(iteration);
            let evaluation = if evaluation_path.exists() {
                records::read_json(&evaluation_path)?
            } else {
                let evaluation = if self.layout.frozen_candidate(iteration).exists() {
                    let candidate: Value = records::read_json(&self.layout.frozen_candidate(iteration))?;
                    self.role.evaluate(&self.layout.frozen(iteration), &candidate).await.unwrap_or_else(evaluation_error)
                } else {
                    json!({"eligible":false,"status":"interrupted_source_capture",
                        "error":"submission counted; incomplete freeze is not reconstructed from mutable author files"})
                };
                records::create_dir(&self.layout.iteration(iteration))?;
                records::write_new_json(&evaluation_path, &evaluation)?;
                evaluation
            };
            let trial = &mut self.ledger.state.trials[index];
            trial.status = TrialStatus::Evaluated;
            trial.evaluation = evaluation;
            trial.directory = Some(self.layout.iteration(iteration));
            self.ledger.save()?;
        }
        Ok(())
    }

    /// Reevaluate retained frozen submissions named by the policy's repair revisions. The original evaluation record
    /// stays; each reevaluation is durable (`reevaluation-<revision>.json`) before the ledger update, so another
    /// interruption neither reruns it nor replays a charged author call.
    async fn apply_framework_repairs(&mut self) -> Result<(), ControllerError> {
        for index in 0..self.ledger.state.trials.len() {
            let trial = &self.ledger.state.trials[index];
            let Some(revision) = self.policy.repair_revision(&trial.evaluation) else {
                continue;
            };
            if !revision.bytes().all(|c| c.is_ascii_alphanumeric() || c == b'-' || c == b'_') {
                return Err(ControllerError::InvalidRequest(format!("invalid framework repair revision {revision:?}")));
            }
            if trial.recovery_records.iter().any(|record| record.revision == revision) {
                continue;
            }
            let iteration = trial.iteration;
            let candidate_path = self.layout.frozen_candidate(iteration);
            if !candidate_path.exists() {
                continue;
            }
            let record_path = self.layout.reevaluation(iteration, revision);
            let record: Value = if record_path.exists() {
                records::read_json(&record_path)?
            } else {
                let started = Instant::now();
                let candidate: Value = records::read_json(&candidate_path)?;
                let evaluation =
                    self.role.evaluate(&self.layout.frozen(iteration), &candidate).await.unwrap_or_else(evaluation_error);
                let trial = &self.ledger.state.trials[index];
                let prior_record = trial.evaluation_record.clone().unwrap_or_else(|| self.layout.evaluation(iteration));
                let record = json!({"revision":revision,"reason":"framework repair of retained frozen submission",
                    "prior_evaluation":trial.evaluation,"prior_evaluation_record":prior_record,"evaluation":evaluation,
                    "framework_elapsed_ms":started.elapsed().as_millis() as u64,"author_dispatched":false});
                records::write_json_atomic(&record_path, &record)?;
                record
            };
            let trial = &mut self.ledger.state.trials[index];
            trial.recovery_records.push(RepairRecord {
                revision: revision.to_string(),
                record: record_path.clone(),
                framework_elapsed_ms: record["framework_elapsed_ms"].as_u64(),
            });
            trial.evaluation = record["evaluation"].clone();
            trial.evaluation_record = Some(record_path);
            self.ledger.save()?;
        }
        Ok(())
    }

    /// A continuing session's incumbent (`RunRequest::continue_from`), established once before the search and recorded
    /// as `LedgerState::incumbent` (iteration 0, call 0; never a counted submission). Durable steps:
    /// 1. the role writes the source session's admitted candidate into the workspace (`seed_incumbent`), and it is frozen
    ///    like a submission into `iterations/0000`; its provenance (`incumbent.json`, written last) marks both done, and
    ///    a directory without it is this session's own partial work (no author call precedes it), renamed aside
    ///    (`0000-partial-<ms>`) and redone.
    ///    A freeze refusal (for example a source rule the current framework adds) is the incumbent's recorded outcome;
    /// 2. its evaluation (`evaluation.json`), fresh as for a submission; a framework failure is evaluated once more and,
    ///    failing again, stops the session resumably before any author call. Under a render-only author the source
    ///    session's recorded evaluation stands in, marked [`RENDER_ONLY_FIELD`].
    async fn establish_incumbent(&mut self) -> Result<(), ControllerError> {
        let Some(source) = self.request.continue_from.clone() else { return Ok(()) };
        if self.ledger.state.incumbent.is_some() {
            return Ok(());
        }
        let iteration = INCUMBENT_ITERATION;
        let directory = self.layout.iteration(iteration);
        let started = Instant::now();
        if !self.layout.incumbent().exists() {
            if directory.exists() {
                // This session's own partial work (frozen files may be read-only): kept aside, never reused.
                let aside = self.layout.iterations().join(format!("{iteration:04}-partial-{}", records::now_unix_ms()));
                std::fs::rename(&directory, &aside).map_err(|e| RecordError::new(&directory, e))?;
            }
            records::create_dir(&directory)?;
            let workspace = self.layout.workspace();
            let seeded = self.role.seed_incumbent(&source, &workspace).await.map_err(role_error("seed incumbent"))?;
            let freeze_error = match self.role.freeze(&workspace, &self.layout.frozen(iteration), &seeded.submission).await {
                Ok(candidate) => {
                    records::write_json_atomic(&self.layout.frozen_candidate(iteration), &candidate)?;
                    None
                }
                Err(error) => Some(error),
            };
            records::write_new_json(
                &self.layout.incumbent(),
                &json!({"format_version":1,"source_session":source,"submission":seeded.submission,"source_evaluation":seeded.source_evaluation,
                    "provenance":seeded.provenance,"freeze_error":freeze_error,
                    "meaning":"the admitted candidate of the source session, written into this session's workspace by the role and frozen here with the current framework; this session's incumbent, never one of its counted submissions"}),
            )?;
        }
        let record: Value = records::read_json(&self.layout.incumbent())?;
        let evaluation = if self.layout.evaluation(iteration).exists() {
            records::read_json(&self.layout.evaluation(iteration))?
        } else {
            let evaluation = self.evaluate_incumbent(&record).await?;
            records::write_new_json(&self.layout.evaluation(iteration), &evaluation)?;
            evaluation
        };
        let mut candidate = record["submission"].clone();
        candidate["incumbent"] = json!({"record":self.layout.incumbent(),"source_session":record["source_session"],"provenance":record["provenance"]});
        self.ledger.state.incumbent = Some(Trial {
            iteration,
            call_id: 0,
            candidate,
            status: TrialStatus::Evaluated,
            evaluation,
            framework_elapsed_ms: Some(started.elapsed().as_millis() as u64),
            directory: Some(directory),
            recovery_records: vec![],
            evaluation_record: None,
        });
        Ok(self.ledger.save()?)
    }

    /// The incumbent's evaluation from its provenance `record` (see `establish_incumbent`).
    async fn evaluate_incumbent(&mut self, record: &Value) -> Result<Value, ControllerError> {
        let iteration = INCUMBENT_ITERATION;
        if let Some(error) = record["freeze_error"].as_str() {
            return Ok(json!({"eligible":false,"status":"freeze_error","error":error}));
        }
        if self.author.render_only() {
            let recorded = record["source_evaluation"].as_str().map(PathBuf::from).ok_or_else(|| ControllerError::Protocol("incumbent record without source_evaluation".into()))?;
            let mut evaluation: Value = records::read_json(&recorded)?;
            evaluation[RENDER_ONLY_FIELD] = json!({"recorded_evaluation":recorded,
                "meaning":"render-only author: the source session's recorded evaluation of this candidate is shown instead of a fresh one; nothing was verified, run or timed for this session, and it is never qualified"});
            return Ok(evaluation);
        }
        let candidate: Value = records::read_json(&self.layout.frozen_candidate(iteration))?;
        let evaluation = self.role.evaluate(&self.layout.frozen(iteration), &candidate).await.unwrap_or_else(evaluation_error);
        let evaluation = if framework_failure(&evaluation) { self.evaluate_again_after_framework_failure(iteration, evaluation).await? } else { evaluation };
        if framework_failure(&evaluation) {
            let record = self.layout.iteration(iteration).join(format!("framework-failure-{}.json", records::now_unix_ms()));
            records::write_json_atomic(&record, &evaluation)?;
            return Err(ControllerError::Role {
                stage: "evaluate incumbent",
                detail: format!("the incumbent failed in the framework on two evaluations ({}); no author was called; resume after the framework is fixed", evaluation["error"]),
            });
        }
        Ok(evaluation)
    }

    /// The search loop: one author call or one submission per step, until something stops it.
    async fn search(&mut self, unsettled: &mut UnsettledCalls) -> Result<StopReason, ControllerError> {
        self.feedback = self.ledger.state.competing_trials().iter().map(|trial| json!(trial)).collect();
        loop {
            if let Some(stop) = self.policy.search_stop(&self.context, &self.ledger.state.competing_trials()) {
                return Ok(stop);
            }
            if self.layout.operator_stop().exists() {
                return Ok(StopReason::OperatorStop);
            }
            // A settled call whose candidate was not submitted yet resumes without a new author call.
            let call = match self.ledger.state.settled_unsubmitted_call().cloned() {
                Some(call) => call,
                None => {
                    if unsettled.usage_unresolved {
                        return Ok(StopReason::UsageUnknown);
                    }
                    let (call, after_wait) = match unsettled.not_dispatched.pop_first() {
                        Some((_, call)) => (call, None),
                        None => {
                            if let Some(stop) = self.ledger.stop_reason()? {
                                return Ok(stop.into());
                            }
                            let wait = provider_wait::wait_before_next_call(&self.ledger.state, &self.layout, &*self.author)?;
                            if let Some(wait) = &wait {
                                provider_wait::wait_for_deadline(&mut *self.author, &self.layout, wait)?;
                            }
                            (self.ledger.begin_call()?, wait)
                        }
                    };
                    self.refresh_shared_facts().await;
                    match self.call_author(call, after_wait.as_ref())? {
                        CallOutcome::Candidate(call) => call,
                        CallOutcome::NoCandidate => continue,
                        CallOutcome::Stop(stop) => return Ok(stop),
                    }
                }
            };
            let trial = self.submit_and_evaluate(call).await?;
            if trial.is_unchanged_resubmission() {
                let objective = self.policy.objective_status(&self.context, &self.ledger.state.competing_trials());
                if let Some(stop) = unchanged_resubmission_stop(&objective, &self.ledger.state.trials) {
                    return Ok(stop);
                }
            }
        }
    }

    /// Merge the role's refreshed shared facts into the context before an author call. A failed refresh keeps the
    /// earlier facts and says so in them (`refresh_error`): it never stops the session.
    async fn refresh_shared_facts(&mut self) {
        match self.role.refresh_shared_facts().await {
            Ok(Value::Object(facts)) => {
                for (key, value) in facts {
                    self.context[key] = value;
                }
            }
            Ok(_) => {}
            Err(error) => {
                if self.context["storage_budget"].is_object() {
                    self.context["storage_budget"]["refresh_error"] = json!(format!("not refreshed before this call ({error}); the facts are from an earlier read"));
                }
            }
        }
    }

    /// Prompt, invoke and settle one author call, and record its feedback. The call runs in the provider session the
    /// ledger assigns before dispatch: fresh for a new attempt, the interrupted session for a retry of the same attempt
    /// (unless that session's context is exhausted). A call that resumes its session after a provider wait
    /// (`after_wait`) sends only the short continuation message; the session already holds the full prompt.
    fn call_author(&mut self, call: Call, after_wait: Option<&ProviderWait>) -> Result<CallOutcome, ControllerError> {
        let layout = &self.layout;
        let author = &*self.author;
        let call = self.ledger.assign_provider_session(call.id, |earlier| provider_wait::session_resumable(author, layout, earlier))?;
        let resume = self.ledger.state.resumes_provider_session(&call);
        let prompt = match after_wait.filter(|_| resume) {
            Some(wait) => provider_wait::continuation_prompt(wait, &self.layout.prompt(call.id)),
            None => {
                let ledger_view = self.ledger.author_view(call.id)?;
                let handoff = if resume {
                    Value::Null
                } else {
                    let policy = &self.policy;
                    trajectory::attempt_handoff(&self.layout, &self.ledger.state, call.id, |trial| {
                        policy.submission_code(&self.layout.frozen(trial.iteration), &trial.candidate, Some(&self.layout.workspace()))
                    })?
                };
                self.policy.author_prompt(&PromptInput {
                    context: &self.context,
                    feedback: &self.feedback,
                    iteration: call.iteration,
                    submission: self.ledger.state.counted_submissions() + 1,
                    limits: &self.request.limits,
                    ledger: &ledger_view,
                    prompt_file: &self.layout.prompt(call.id),
                    handoff: &handoff,
                })
            }
        };
        let call_dir = self.layout.call(call.id);
        records::create_dir(&call_dir)?;
        let session_id = self.ledger.state.provider_session_of(&call).to_string();
        let receipt = self.author.invoke(&AuthorCall {
            call: &call,
            session_id: &session_id,
            resume,
            prompt: &prompt,
            workspace: &self.layout.workspace(),
            call_dir: &call_dir,
            limits: &self.request.limits,
        });
        records::write_json_atomic(&self.layout.receipt(call.id), &receipt)?;
        self.ledger.settle(receipt.clone())?;
        self.feedback.push(call_event(&call, &receipt));
        if let Some(jobs) = local_jobs_event(&self.layout, &call)? {
            self.feedback.push(jobs);
        }
        // A deterministic local setup failure is not retried in a loop; a corrected preflight may use the single
        // durable pre-dispatch recovery on the next run.
        if receipt.predispatch_refusal() && self.author.definitely_not_dispatched(&call_dir).map_err(author_error("dispatch proof"))? {
            return Ok(CallOutcome::Stop(StopReason::AuthorReadinessRefusal));
        }
        if receipt.output.is_none() {
            return Ok(if self.repeated_invalid_output(call.iteration) {
                CallOutcome::Stop(StopReason::UnchangedInvalidOutput)
            } else {
                CallOutcome::NoCandidate
            });
        }
        let settled = self.ledger.state.call(call.id).cloned().ok_or(ControllerError::Protocol(format!("call {} vanished", call.id)))?;
        Ok(CallOutcome::Candidate(settled))
    }

    /// The last two calls of `iteration` returned the same invalid structured output and were refused with the same
    /// outcome, after the author had seen that error: no progress.
    fn repeated_invalid_output(&self, iteration: u32) -> bool {
        let receipts: Vec<&Receipt> = self
            .ledger
            .state
            .calls
            .iter()
            .filter(|call| call.iteration == iteration)
            .filter_map(|call| call.receipt.as_ref())
            .collect();
        let structured = |receipt: &Receipt| {
            receipt.raw_result.as_ref().map(|raw| raw["structured_output"].clone()).filter(|output| !output.is_null())
        };
        match receipts.as_slice() {
            [.., earlier, latest] => {
                earlier.output.is_none()
                    && earlier.outcome == latest.outcome
                    && structured(earlier).is_some()
                    && structured(earlier) == structured(latest)
            }
            _ => false,
        }
    }

    /// Count the call's candidate as the next iteration, then freeze and evaluate it (durably, in that order).
    async fn submit_and_evaluate(&mut self, call: Call) -> Result<Trial, ControllerError> {
        let output = call
            .receipt
            .and_then(|receipt| receipt.output)
            .ok_or_else(|| ControllerError::Protocol(format!("candidate output of call {} missing", call.id)))?;
        let submission: CandidateSubmission = serde_json::from_value(output.clone())
            .map_err(|e| ControllerError::Protocol(format!("candidate submission of call {}: {e}", call.id)))?;
        submission.validate().map_err(ControllerError::Protocol)?;
        let iteration = self.ledger.submit(call.id, output)?;
        records::create_dir(&self.layout.iteration(iteration))?;
        let started = Instant::now();
        let mut evaluation = self.freeze_and_evaluate(iteration, &submission).await?;
        if framework_failure(&evaluation) && self.layout.frozen_candidate(iteration).exists() {
            evaluation = self.evaluate_again_after_framework_failure(iteration, evaluation).await?;
        }
        records::write_json_atomic(&self.layout.evaluation(iteration), &evaluation)?;
        let trial = self.ledger.state.trials.last_mut().expect("submit recorded the trial");
        trial.status = TrialStatus::Evaluated;
        trial.evaluation = evaluation;
        trial.framework_elapsed_ms = Some(started.elapsed().as_millis() as u64);
        trial.directory = Some(self.layout.iteration(iteration));
        let trial = trial.clone();
        self.feedback.push(json!(trial));
        self.ledger.save()?;
        if trial.framework_failure() {
            // The framework failed twice on the same frozen candidate: stop resumably (the ledger stays open, the
            // submission is recorded and not counted) so the framework can be fixed before the author is called again.
            return Err(ControllerError::Role {
                stage: "evaluate",
                detail: format!("submission {iteration} failed in the framework on two evaluations ({}); not counted; resume after the framework is fixed", trial.evaluation["error"]),
            });
        }
        Ok(trial)
    }

    /// A framework failure judged nothing about the candidate: record it beside the iteration and evaluate the same
    /// frozen candidate once more. The second evaluation is the submission's evaluation; the first stays on record.
    async fn evaluate_again_after_framework_failure(&mut self, iteration: u32, failed: Value) -> Result<Value, ControllerError> {
        let record = self.layout.iteration(iteration).join("framework-failure-1.json");
        records::write_json_atomic(&record, &failed)?;
        let candidate: Value = records::read_json(&self.layout.frozen_candidate(iteration))?;
        let mut evaluation = self.role.evaluate(&self.layout.frozen(iteration), &candidate).await.unwrap_or_else(evaluation_error);
        attribute_repeated_checker_failure(&failed, &mut evaluation);
        evaluation["earlier_framework_failure"] = json!({"record":record,"status":failed["status"],"error":failed["error"],
            "meaning":"the first evaluation of this frozen candidate failed in the framework (not the candidate); it was evaluated once more and this is that evaluation"});
        Ok(evaluation)
    }

    /// Freeze a submission and evaluate it, or reuse the result of an effectively identical earlier submission
    /// (never remeasured, never counted as an improvement). Role stage errors become the recorded evaluation.
    async fn freeze_and_evaluate(&mut self, iteration: u32, submission: &CandidateSubmission) -> Result<Value, ControllerError> {
        let frozen = self.layout.frozen(iteration);
        let candidate = match self.role.freeze(&self.layout.workspace(), &frozen, submission).await {
            Ok(candidate) => candidate,
            Err(error) => return Ok(json!({"eligible":false,"status":"freeze_error","error":error})),
        };
        let frozen_candidate = self.layout.frozen_candidate(iteration);
        records::write_json_atomic(&frozen_candidate, &candidate)?;
        // The attempt's notes as submitted (the workspace file is rewritten by later attempts); absent notes copy nothing.
        let notes = self.layout.workspace().join(super::layout::NOTES_FILE);
        if notes.is_file() {
            std::fs::copy(&notes, self.layout.iteration_notes(iteration))
                .map_err(|e| ControllerError::Role { stage: "freeze", detail: format!("copy {} to iteration {iteration}: {e}", notes.display()) })?;
        }
        // The incumbent, then the earlier submissions (the last trial is this one).
        let competing = self.ledger.state.competing_trials();
        let earlier = &competing[..competing.len().saturating_sub(1)];
        if let Some((prior_iteration, prior_evaluation)) =
            trajectory::unchanged_prior_submission(&self.layout, &frozen_candidate, earlier)?
        {
            return Ok(json!({"eligible":false,"status":"unchanged_effective_candidate",
                "duplicate_effective_candidate":true,"duplicate_of_iteration":prior_iteration,
                "reused_score_ns":prior_evaluation["score_ns"],"reused_evaluation":prior_evaluation,
                "qualification_runs":0,"timed_measurements":0,
                "reason":"source, plan, parameters and assets are unchanged; prior result reused"}));
        }
        Ok(self.role.evaluate(&frozen, &candidate).await.unwrap_or_else(evaluation_error))
    }

    /// Qualify eligible trials (the incumbent included) in ascending score order until one qualifies. A recorded
    /// evaluation shown for a render-only author ([`RENDER_ONLY_FIELD`]) is never qualified.
    async fn qualify_best(&mut self) -> Result<Vec<QualificationAttempt>, ControllerError> {
        let competing = self.ledger.state.competing_trials();
        let candidates: Vec<(u32, Value)> = qualification_order(&competing)
            .into_iter()
            .filter(|trial| trial.evaluation.get(RENDER_ONLY_FIELD).is_none())
            .map(|trial| (trial.iteration, trial.evaluation.clone()))
            .collect();
        let mut attempts = vec![];
        for (iteration, evaluation) in candidates {
            let attempt = qualify_recorded(self.role, &self.layout, iteration, &evaluation).await?;
            let qualified = attempt.qualified();
            attempts.push(attempt);
            if qualified {
                break;
            }
        }
        Ok(attempts)
    }

    /// Record the role's resolution and the summary; close the ledger when accounting is complete.
    async fn close(mut self, stop: StopReason, qualification: Vec<QualificationAttempt>) -> Result<Value, ControllerError> {
        let competing = self.ledger.state.competing_trials();
        let resolution = self.role.close(&competing, &qualification).await.map_err(role_error("close"))?;
        records::write_json_atomic(&self.layout.resolution(), &resolution)?;
        let state = &self.ledger.state;
        let limits = &self.request.limits;
        let totals = self.ledger.totals()?;
        let iteration_accounting = (1..=state.last_attempted_iteration())
            .map(|iteration| Ok(json!({"iteration":iteration,"accounting":self.ledger.accounting(Some(iteration))?})))
            .collect::<Result<Vec<Value>, ControllerError>>()?;
        let trajectory = state
            .trials
            .iter()
            .map(|trial| {
                let directory = self.layout.iteration(trial.iteration);
                json!({"iteration":trial.iteration,"call_id":trial.call_id,"directory":directory,
                    "evaluation":evaluation_digest(&trial.evaluation),
                    "evaluation_record":trial.evaluation_record.clone().unwrap_or_else(|| self.layout.evaluation(trial.iteration)),
                    "recovery_records":trial.recovery_records})
            })
            .collect();
        let qualification_digest = qualification_digest(&self.layout, &qualification);
        let remaining_submissions = count_guard(limits.max_iterations)
            .as_u64()
            .map_or(json!("unset"), |limit| json!(limit.saturating_sub(u64::from(state.counted_submissions()))));
        let complete = !totals.usage_unknown;
        let summary = RunSummary {
            status: if complete { "closed" } else { "accounting_unresolved" },
            reason: stop.as_str(),
            objective: self.policy.objective_status(&self.context, &competing),
            session_id: &state.session_id,
            provider: &self.capability,
            limits,
            remaining_limits: json!({"candidate_submissions":remaining_submissions,"not_counted_framework_failures":state.uncounted_framework_failures(),
                "provider_cost_usd":limits.max_cost_usd.remaining_after(totals.spent),"model_turn_cap":null}),
            iterations: state.iterations,
            calls: state.calls.len(),
            reported_cost_usd: complete.then_some(totals.spent),
            known_reported_cost_usd: totals.spent,
            outstanding_reservation_usd: totals.reserved,
            cost_complete: complete,
            cost_kind: "provider_reported",
            budget_enforcement: budget_enforcement(&self.capability, limits),
            known_budget_overshoot_usd: totals.spent.saturating_sub(limits.max_cost_usd),
            budget_overshoot_complete: complete,
            accounting: self.ledger.accounting(None)?,
            iteration_accounting,
            trajectory_accounting: trajectory::trajectory_accounting(&self.layout, state)?,
            author_elapsed_ms: state.calls.iter().filter_map(|call| call.receipt.as_ref()).map(|r| r.elapsed_ms as u128).sum(),
            trajectory,
            incumbent: state.incumbent.as_ref().map(|trial| {
                json!({"iteration":trial.iteration,"record":self.layout.incumbent(),"directory":trial.directory,
                    "evaluation":evaluation_digest(&trial.evaluation),"evaluation_record":self.layout.evaluation(trial.iteration)})
            }),
            qualification: qualification_digest,
            resolution,
            resolution_record: self.layout.resolution(),
            ledger: self.layout.ledger(),
        };
        let summary = serde_json::to_value(&summary).map_err(|e| RecordError::new(&self.layout.summary(), e))?;
        // A session with unknown usage stays open: its calls can be reconciled and the run resumed.
        if complete {
            self.ledger.state.closed = Some(summary.clone());
            self.ledger.save()?;
        }
        records::write_json_atomic(&self.layout.summary(), &summary)?;
        Ok(summary)
    }
}

#[cfg(test)]
mod tests;
