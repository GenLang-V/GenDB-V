//! The durable ledger of one author session: calls with their reservations and provider receipts, counted usage,
//! candidate submissions (trials) and the closure.
//!
//! Invariants:
//! - A call is recorded (with its stop-guard reservation) before the author is invoked. A call without a settled
//!   receipt keeps its reservation: its usage is unknown, never zero.
//! - Receipts are provider observations. They are stored unchanged; counting derives from them (`counted_usage`).
//! - Provider-reported dollars do not depend on the spend policy; the dollar guard stops new calls, it is not a cap.
//! - A submission is recorded before it is evaluated and consumes its iteration number whatever the evaluation says.
//!   It counts against the submission guard unless its evaluation was a framework failure ([`Trial::framework_failure`]:
//!   the framework, not the candidate, failed); such a submission is recorded and its author is told it was not
//!   counted.
//! - Each call runs in a provider session chosen before dispatch (`Call::provider_session`,
//!   [`Ledger::assign_provider_session`]): a retry of the same iteration resumes the interrupted session of that attempt,
//!   and the first call of a new iteration resumes the session that produced the previous submission when the role's
//!   evaluation of that submission asked for it ([`CONTINUE_PROVIDER_SESSION`]); either only when the caller says the
//!   session can continue (it exists and its context is not exhausted). Otherwise the call starts a fresh session.
//! - One controller owns a run directory at a time (`controller.lock`), and a resumed run must present the same
//!   request, provider and active limits.

use super::limits::{Limits, Money, MoneyError, count_guard, request_without_retired_turn_cap};
use super::records::{self, RecordError};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use crate::file_lock::FileLock;
use std::fs::OpenOptions;
use std::path::{Path, PathBuf};

/// Outcome prefix of a call that a transport refused before launching any provider process (for example a missing
/// activity lease). Only such a receipt with zero usage can take part in pre-dispatch recovery.
pub const PREDISPATCH_REFUSAL_PREFIX: &str = "activity_lock_refusal:";

/// Provider token counters of one receipt.
#[derive(Clone, Debug, Default, Serialize, Deserialize, PartialEq, Eq)]
pub struct Tokens {
    pub input: u64,
    pub output: u64,
    pub cache_read: u64,
    pub cache_creation: u64,
}

impl Tokens {
    fn is_zero(&self) -> bool {
        *self == Tokens::default()
    }

    /// Counter-wise `self - earlier`; `None` when any counter decreased.
    fn increment_over(&self, earlier: &Tokens) -> Option<Tokens> {
        Some(Tokens {
            input: self.input.checked_sub(earlier.input)?,
            output: self.output.checked_sub(earlier.output)?,
            cache_read: self.cache_read.checked_sub(earlier.cache_read)?,
            cache_creation: self.cache_creation.checked_sub(earlier.cache_creation)?,
        })
    }

    /// Counter-wise sum; `false` when a counter overflowed (it then saturates).
    fn accumulate(&mut self, other: &Tokens) -> bool {
        let mut exact = true;
        for (sum, value) in [
            (&mut self.input, other.input),
            (&mut self.output, other.output),
            (&mut self.cache_read, other.cache_read),
            (&mut self.cache_creation, other.cache_creation),
        ] {
            match sum.checked_add(value) {
                Some(total) => *sum = total,
                None => {
                    *sum = u64::MAX;
                    exact = false;
                }
            }
        }
        exact
    }
}

/// What a receipt's provider cost and tokens cover, as the provider adapter declares from the inspected semantics of
/// that provider version. Never inferred from magnitudes; absent means unknown.
///
/// Fields of one provider result need not share a scope. For Claude Code 2.1.280, `total_cost_usd`, `modelUsage` and
/// `duration_api_ms` are session totals, while `duration_ms` and the top-level `usage` cover the invocation. The
/// adapter derives `Receipt::tokens` from `modelUsage`, so both counted fields of such a receipt are session totals;
/// `elapsed_ms` is always the controller-observed wall time of the invocation.
#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum UsageScope {
    /// This invocation only.
    Invocation,
    /// Everything reported in the receipt's provider session (its `session_id`) up to and including this invocation.
    Session,
}

/// How one call's usage was derived from its receipt.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CountingBasis {
    /// An invocation total, counted as it is.
    Invocation,
    /// The first session total of its provider session, counted whole.
    SessionFirst,
    /// A later session total, counted by its increment over the previous total of the same session.
    SessionIncrement,
    /// Undeclared scope: the raw receipt is counted (may overcount a session total) and flagged.
    ScopeUnknown,
    /// A session total below its predecessor without a declared reset: this and every later receipt of the session
    /// have unknown usage.
    ScopeConflict,
    /// No settled receipt.
    NoReceipt,
    /// No receipt of its own (an interrupted call): its usage is inside the session total that a later call resuming
    /// the same provider session reported, and that call's increment counts it; counted here as zero.
    InResumedSessionTotal,
}

/// One call's counted usage (`LedgerState::counted_usage`). Cost and tokens are derived separately; either may be
/// unknown.
#[derive(Clone, Debug, PartialEq)]
pub struct CountedUsage {
    pub cost: Option<Money>,
    pub tokens: Option<Tokens>,
    pub basis: CountingBasis,
}

impl CountedUsage {
    fn unknown(basis: CountingBasis) -> Self {
        Self { cost: None, tokens: None, basis }
    }
}

/// The provider's receipt of one author call, as settled in the ledger.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct Receipt {
    pub call_id: u64,
    pub session_id: String,
    pub ended_unix_ms: u64,
    /// Controller-observed wall time of this invocation.
    pub elapsed_ms: u64,
    /// Provider-reported cost recorded by the adapter (historical records spell it `estimated_cost_usd`).
    #[serde(rename = "provider_reported_cost_usd", alias = "estimated_cost_usd")]
    pub reported_cost_usd: Option<Money>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub billed_cost_usd: Option<Money>,
    pub tokens: Option<Tokens>,
    pub outcome: String,
    /// The provider's terminal result, retained unchanged.
    pub raw_result: Option<Value>,
    /// The validated candidate submission, when the call produced one.
    pub output: Option<Value>,
    /// Declared scope of `tokens` and the provider cost; `None` (historical receipts, uninspected versions) is unknown.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub usage_scope: Option<UsageScope>,
}

impl Receipt {
    /// The shape of a transport refusal before any provider launch: zero cost, no tokens, no result, no time. The
    /// shape alone is insufficient; the transport must also prove that nothing was launched.
    pub fn predispatch_refusal(&self) -> bool {
        self.outcome.starts_with(PREDISPATCH_REFUSAL_PREFIX)
            && self.raw_result.is_none()
            && self.output.is_none()
            && self.elapsed_ms == 0
            && self.provider_cost() == Some(Money::default())
            && self.billed_cost_usd.is_none_or(|cost| cost == Money::default())
            && self.tokens.as_ref().is_none_or(Tokens::is_zero)
    }

    /// The provider-reported cost: the terminal result's `total_cost_usd`, else the recorded cost, else the billed
    /// cost. These are alternative observations, never additional charges.
    pub fn provider_cost(&self) -> Option<Money> {
        self.raw_result.as_ref().and_then(reported_total_cost).or(self.reported_cost_usd).or(self.billed_cost_usd)
    }
}

/// `total_cost_usd` of a provider terminal result (a JSON number or string), exactly.
pub fn reported_total_cost(raw_result: &Value) -> Option<Money> {
    let value = raw_result.get("total_cost_usd")?;
    Money::parse(&value.as_str().map(str::to_owned).unwrap_or_else(|| value.to_string())).ok()
}

/// One author call.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Call {
    /// 1-based, in dispatch order.
    pub id: u64,
    /// The candidate iteration this call works towards (submissions so far + 1).
    pub iteration: u32,
    /// 1-based attempt within the iteration, excluding recovered pre-dispatch refusals.
    pub attempt: u32,
    pub started_unix_ms: u64,
    /// Stop-guard reservation: the guard minus known spend and other reservations when the call started.
    pub reservation_usd: Money,
    pub receipt: Option<Receipt>,
    /// The provider session this call runs in, chosen before dispatch (`Ledger::assign_provider_session`). Absent in
    /// historical ledgers, whose calls all ran in the ledger's one `session_id`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub provider_session: Option<String>,
    /// The call continues `provider_session` (an interrupted call of the same attempt started it) instead of creating it.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub resumes_provider_session: bool,
    /// An interrupted call without a receipt whose provider session exists and reports session-scoped totals: the
    /// call that resumes the session settles its usage (`CountingBasis::InResumedSessionTotal`), so it does not stop
    /// the run as unknown usage meanwhile (`Ledger::totals`).
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub usage_in_resumed_session: bool,
}

#[derive(Clone, Copy, Debug, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum TrialStatus {
    /// Counted; its evaluation has not been recorded yet.
    Submitted,
    Evaluated,
}

/// A framework repair reevaluation of a retained frozen submission (`RolePolicy::repair_revision`).
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct RepairRecord {
    pub revision: String,
    pub record: PathBuf,
    pub framework_elapsed_ms: Option<u64>,
}

/// One counted candidate submission and its evaluation.
///
/// The evaluation is role-defined JSON. The controller reads only: `eligible` (bool), `score_ns` (number; lower is
/// better), `status`, `error`, `failure_class`, `measurements` (cells with `binding`, `workers`, `status`, `median_ns`,
/// `samples_ns`, `boundary`) and `duplicate_effective_candidate` (set by the controller for an unchanged resubmission).
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
pub struct Trial {
    pub iteration: u32,
    pub call_id: u64,
    /// The submission exactly as settled in the call's receipt.
    pub candidate: Value,
    pub status: TrialStatus,
    #[serde(default, skip_serializing_if = "Value::is_null")]
    pub evaluation: Value,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub framework_elapsed_ms: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub directory: Option<PathBuf>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub recovery_records: Vec<RepairRecord>,
    /// The record of the current evaluation when a repair replaced the original `evaluation.json`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub evaluation_record: Option<PathBuf>,
}

impl Trial {
    pub fn eligible(&self) -> bool {
        self.evaluation["eligible"] == true
    }

    /// The evaluation's score; a missing score ranks last.
    pub fn score_ns(&self) -> f64 {
        self.evaluation["score_ns"].as_f64().unwrap_or(f64::INFINITY)
    }

    /// An unchanged resubmission whose prior result was reused.
    pub fn is_unchanged_resubmission(&self) -> bool {
        self.evaluation["duplicate_effective_candidate"] == true
    }

    /// The evaluation failed in the framework and judged nothing about the candidate: it never counts against the
    /// submission guard and its verdict is never reused ([`framework_failure`]).
    pub fn framework_failure(&self) -> bool {
        framework_failure(&self.evaluation)
    }

    /// `(binding, workers, median_ns)` of every measurement cell that has a worker count and a median (`binding`: the
    /// cell's binding name, empty when not recorded).
    pub fn medians(&self) -> impl Iterator<Item = (String, u64, u64)> + '_ {
        self.evaluation["measurements"]
            .as_array()
            .into_iter()
            .flatten()
            .filter_map(|cell| Some((cell["binding"].as_str().unwrap_or_default().to_string(), cell["workers"].as_u64()?, cell["median_ns"].as_u64()?)))
    }
}

/// An evaluation that failed in the framework rather than on the candidate: a role-stage `evaluation_error`, or a
/// `tool_failure` (toolchain, child worker or framework service; `FailureClass::ToolFailure`) other than a query child
/// reaching the framework's time bound, which a slow or non-terminating candidate can cause and which therefore counts.
/// The evidence rule for the toolchain: a `rust_verify` failure (signal such as the OOM killer, internal panic) that
/// repeats when the same frozen candidate is evaluated again is the candidate's (its code drives the checker there)
/// and counts; the controller marks it `attributed_to_candidate` ([`attribute_repeated_checker_failure`]).
pub fn framework_failure(evaluation: &Value) -> bool {
    if evaluation["attributed_to_candidate"] == true {
        return false;
    }
    match evaluation["status"].as_str() {
        Some("evaluation_error") => true,
        Some("tool_failure") => !evaluation["error"].as_str().is_some_and(|error| error.contains(CHILD_TIMEOUT_TEXT)),
        _ => false,
    }
}

/// Mark `second` (the re-evaluation of a frozen candidate whose first evaluation `first` failed in the framework) as the
/// candidate's own failure when both are `rust_verify` failures of its crate check: the checker failed twice on the
/// same code, so the evidence points at the code, not at a transient framework fault. Other repeated framework
/// failures stay framework failures (not counted; the controller stops resumably).
pub fn attribute_repeated_checker_failure(first: &Value, second: &mut Value) {
    let checker = |e: &Value| e["status"] == "tool_failure" && e["error"].as_str().is_some_and(|error| error.contains(CHECKER_TEXT));
    if checker(first) && checker(second) {
        second["attributed_to_candidate"] = json!(true);
        second["attribution"] = json!("the Verus checker (rust_verify) failed on this candidate's crate on both evaluations (for example killed by a signal such as the OOM killer, or an internal panic): attributed to the candidate's code and counted. Simplify or split the proof that drives the checker (verify modules or functions separately to find it)");
    }
}

/// Text every `rust_verify` outcome of a crate check names (`gendb_verification::verus::run`).
const CHECKER_TEXT: &str = "rust_verify";

/// The error text of a query child that reached the framework's time bound (`admission::execution`).
const CHILD_TIMEOUT_TEXT: &str = "child worker timed out";

/// Why no further author call may start.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LedgerStop {
    IterationLimit,
    /// Some call's usage is unknown, so the dollar guard cannot be evaluated.
    UsageUnknown,
    BudgetLimit,
    RetryLimit,
}

impl LedgerStop {
    pub fn as_str(self) -> &'static str {
        match self {
            LedgerStop::IterationLimit => "iteration_limit",
            LedgerStop::UsageUnknown => "usage_unknown",
            LedgerStop::BudgetLimit => "budget_limit",
            LedgerStop::RetryLimit => "retry_limit",
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum LedgerError {
    InvalidLimits(String),
    Record(RecordError),
    Money(MoneyError),
    /// Another controller holds this run's lock.
    AlreadyOwned,
    /// A resumed run presented a different request, provider or active limits (or an unknown ledger format).
    ResumeIdentityDiffers,
    Closed,
    Stopped(LedgerStop),
    ReceiptSessionMismatch,
    UnknownCall(u64),
    ConflictingDuplicateReceipt(u64),
    ReceiptBeforeDispatch(u64),
    UsageEvidenceRequired,
    UnsettledCall(u64),
    ReconciliationConflict(&'static str),
    CandidateMismatch(u64),
}

impl fmt::Display for LedgerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LedgerError::InvalidLimits(detail) => f.write_str(detail),
            LedgerError::Record(error) => write!(f, "{error}"),
            LedgerError::Money(error) => write!(f, "{error}"),
            LedgerError::AlreadyOwned => f.write_str("run already owned by another controller"),
            LedgerError::ResumeIdentityDiffers => {
                f.write_str("persisted request/limits differ; resume cannot replace budget")
            }
            LedgerError::Closed => f.write_str("run is closed"),
            LedgerError::Stopped(stop) => f.write_str(stop.as_str()),
            LedgerError::ReceiptSessionMismatch => f.write_str("receipt session mismatch"),
            LedgerError::UnknownCall(id) => write!(f, "unknown call {id}"),
            LedgerError::ConflictingDuplicateReceipt(id) => write!(f, "conflicting duplicate receipt for call {id}"),
            LedgerError::ReceiptBeforeDispatch(id) => write!(f, "receipt of call {id} ends before dispatch"),
            LedgerError::UsageEvidenceRequired => f.write_str("provider usage evidence required"),
            LedgerError::UnsettledCall(id) => {
                write!(f, "settle invocation identity/outcome of call {id} before usage reconciliation")
            }
            LedgerError::ReconciliationConflict(detail) => f.write_str(detail),
            LedgerError::CandidateMismatch(id) => write!(f, "candidate of call {id} does not match next settled call"),
        }
    }
}

impl std::error::Error for LedgerError {}

impl From<RecordError> for LedgerError {
    fn from(error: RecordError) -> Self {
        LedgerError::Record(error)
    }
}

impl From<MoneyError> for LedgerError {
    fn from(error: MoneyError) -> Self {
        LedgerError::Money(error)
    }
}

/// Known spend and outstanding reservations over all calls.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpendTotals {
    /// Sum of counted costs.
    pub spent: Money,
    /// Sum of reservations of calls whose cost is unknown.
    pub reserved: Money,
    /// Some call's cost is unknown.
    pub usage_unknown: bool,
}

/// Disjoint usage totals of a set of calls (the whole session or one iteration). Partial totals stay labelled;
/// absent usage is never zero.
#[derive(Clone, Debug, Serialize, PartialEq)]
pub struct Accounting {
    pub calls: usize,
    pub call_ids: Vec<u64>,
    pub author_elapsed_ms: u128,
    /// Complete counted cost, or null when any cost is unknown.
    pub provider_reported_cost_usd: Option<Money>,
    pub known_provider_reported_cost_usd: Money,
    pub cost_complete: bool,
    pub tokens: Option<Tokens>,
    pub observed_token_lower_bound: Tokens,
    pub tokens_complete: bool,
    pub counting: &'static str,
    pub counted_by_call: Vec<CountedCall>,
    /// No settled receipt was counted with an unknown scope.
    pub scope_complete: bool,
    /// Plain sum of every receipt's provider cost, for comparison (overcounts session totals).
    pub raw_receipt_sum_usd: Money,
}

#[derive(Clone, Debug, Serialize, PartialEq)]
pub struct CountedCall {
    pub call_id: u64,
    pub usage_scope: Option<UsageScope>,
    pub basis: CountingBasis,
}

/// The serialized ledger (`ledger.json`, format 1).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct LedgerState {
    pub format_version: u32,
    /// Resume identity: the run request and the provider capability.
    pub request: Value,
    /// The provider session id of this author session.
    pub session_id: String,
    pub limits: Limits,
    /// Counted submissions.
    pub iterations: u32,
    pub calls: Vec<Call>,
    #[serde(default)]
    pub receipt_reconciliations: Vec<Value>,
    #[serde(default)]
    pub predispatch_recoveries: Vec<Value>,
    /// Archived: the native shared-design stage refreshed its request context here. Read and preserved for
    /// historical ledgers only; the active controller never adds entries.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub preparation_context_revisions: Vec<Value>,
    pub trials: Vec<Trial>,
    /// A continuing session's incumbent (`RunRequest::continue_from`): the admitted candidate of an earlier session,
    /// written into the workspace, frozen and evaluated before the first author call, as iteration 0 with call 0. It
    /// competes in selection, early stop and qualification like a submission ([`LedgerState::competing_trials`]) but
    /// is never a counted submission. Absent for every other session (whose ledger keeps its form).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub incumbent: Option<Trial>,
    /// The final summary once the run closed with complete accounting.
    pub closed: Option<Value>,
}

impl LedgerState {
    /// The candidates the session selects from: the incumbent (when the session continues from one), then every
    /// submission in iteration order.
    pub fn competing_trials(&self) -> Vec<Trial> {
        self.incumbent.iter().chain(&self.trials).cloned().collect()
    }

    /// Counted usage per call, in call order, from each receipt's declared `usage_scope` (see `CountingBasis`). Raw
    /// receipts are never changed.
    pub fn counted_usage(&self) -> Vec<CountedUsage> {
        // Latest session totals per provider session; a session is conflicted once a total decreased.
        let mut session_totals: BTreeMap<&str, (Option<Money>, Option<Tokens>)> = BTreeMap::new();
        let mut conflicted: BTreeSet<&str> = BTreeSet::new();
        self.calls
            .iter()
            .enumerate()
            .map(|(index, call)| {
                let Some(receipt) = &call.receipt else {
                    let session = self.provider_session_of(call);
                    let resumed = call.usage_in_resumed_session
                        && self.calls[index + 1..].iter().any(|later| {
                            later.receipt.as_ref().is_some_and(|r| r.usage_scope == Some(UsageScope::Session) && r.session_id == session)
                        });
                    return if resumed {
                        CountedUsage { cost: Some(Money::default()), tokens: Some(Tokens::default()), basis: CountingBasis::InResumedSessionTotal }
                    } else {
                        CountedUsage::unknown(CountingBasis::NoReceipt)
                    };
                };
                let (cost, tokens) = (receipt.provider_cost(), receipt.tokens.clone());
                match receipt.usage_scope {
                    Some(UsageScope::Invocation) => CountedUsage { cost, tokens, basis: CountingBasis::Invocation },
                    None => CountedUsage { cost, tokens, basis: CountingBasis::ScopeUnknown },
                    Some(UsageScope::Session) => {
                        let session = receipt.session_id.as_str();
                        let first = !session_totals.contains_key(session);
                        let (prior_cost, prior_tokens) = session_totals
                            .get(session)
                            .cloned()
                            .unwrap_or((Some(Money::default()), Some(Tokens::default())));
                        // `Some(None)`: both totals are known and this one decreased.
                        let cost_step = cost.zip(prior_cost).map(|(total, prior)| total.0.checked_sub(prior.0).map(Money));
                        let token_step = tokens.as_ref().zip(prior_tokens.as_ref()).map(|(total, prior)| total.increment_over(prior));
                        let latest = session_totals.entry(session).or_insert((None, None));
                        if cost.is_some() {
                            latest.0 = cost;
                        }
                        if tokens.is_some() {
                            latest.1 = tokens;
                        }
                        let decreased = matches!(cost_step, Some(None)) || matches!(token_step, Some(None));
                        if decreased || conflicted.contains(session) {
                            conflicted.insert(session);
                            CountedUsage::unknown(CountingBasis::ScopeConflict)
                        } else {
                            let basis = if first { CountingBasis::SessionFirst } else { CountingBasis::SessionIncrement };
                            CountedUsage { cost: cost_step.flatten(), tokens: token_step.flatten(), basis }
                        }
                    }
                }
            })
            .collect()
    }

    /// A call excluded from retry counting by an earlier pre-dispatch recovery.
    pub fn excluded_predispatch_call(&self, id: u64) -> bool {
        self.predispatch_recoveries.iter().any(|recovery| {
            recovery["call_ids"].as_array().is_some_and(|ids| ids.iter().any(|value| value.as_u64() == Some(id)))
        })
    }

    /// Only closure eligible for the one automatic pre-dispatch recovery: every call so far is a settled zero-usage
    /// transport refusal of this session, nothing was submitted, and the run is open or closed by the retry limit or
    /// the readiness refusal.
    pub fn predispatch_recovery_candidate(&self) -> bool {
        self.predispatch_recoveries.is_empty()
            && self.iterations == 0
            && self.trials.is_empty()
            && self.limits.max_iterations > 0
            && self.limits.max_cost_usd > Money::default()
            && !self.calls.is_empty()
            && self.calls.iter().all(|call| {
                call.receipt.as_ref().is_some_and(|receipt| {
                    receipt.call_id == call.id && receipt.session_id == self.provider_session_of(call) && receipt.predispatch_refusal()
                })
            })
            && self.closed.as_ref().is_none_or(|closed| {
                closed["status"] == "closed"
                    && matches!(closed["reason"].as_str(), Some("retry_limit" | "author_readiness_refusal"))
            })
    }

    pub fn call(&self, id: u64) -> Option<&Call> {
        self.calls.iter().find(|call| call.id == id)
    }

    /// Calls of `iteration` that count as attempts.
    fn attempts_of(&self, iteration: u32) -> usize {
        self.calls
            .iter()
            .filter(|call| call.iteration == iteration && !self.excluded_predispatch_call(call.id))
            .count()
    }

    /// A settled call of the next iteration whose candidate was not submitted yet (the controller stopped between
    /// settling and submitting).
    pub fn settled_unsubmitted_call(&self) -> Option<&Call> {
        self.calls.iter().find(|call| {
            call.iteration == self.iterations + 1 && call.receipt.as_ref().is_some_and(|receipt| receipt.output.is_some())
        })
    }

    /// Whether the provider session already exists (another call has a provider result), so a call resumes it.
    pub fn provider_session_started(&self, except_call: u64) -> bool {
        self.calls.iter().any(|call| {
            call.id != except_call && call.receipt.as_ref().is_some_and(|receipt| receipt.raw_result.is_some())
        })
    }

    /// Submissions that count against the submission guard: every recorded submission except framework failures. A
    /// submission not yet evaluated counts.
    pub fn counted_submissions(&self) -> u32 {
        self.trials.iter().filter(|trial| !trial.framework_failure()).count() as u32
    }

    /// Submissions recorded but not counted (framework failures).
    pub fn uncounted_framework_failures(&self) -> Vec<u32> {
        self.trials.iter().filter(|trial| trial.framework_failure()).map(|trial| trial.iteration).collect()
    }

    /// The provider session of `call`: its own, or the ledger's one session for a historical call.
    pub fn provider_session_of<'a>(&'a self, call: &'a Call) -> &'a str {
        call.provider_session.as_deref().unwrap_or(&self.session_id)
    }

    /// Whether `call` continues an existing provider session: recorded with the call, or (historical calls without a
    /// recorded session) whenever another call of the ledger's one session produced a provider result.
    pub fn resumes_provider_session(&self, call: &Call) -> bool {
        if call.provider_session.is_some() { call.resumes_provider_session } else { self.provider_session_started(call.id) }
    }

    /// The last iteration any call worked towards.
    pub fn last_attempted_iteration(&self) -> u32 {
        self.calls.last().map(|call| call.iteration).unwrap_or(0)
    }

    /// The call whose provider session the first call of `iteration` continues, by the role's choice: the call that
    /// produced the submission of `iteration - 1`, when that submission's evaluation chose
    /// `next_call.provider_session == "continue"` ([`CONTINUE_PROVIDER_SESSION`]). An unchanged resubmission carries the
    /// reused evaluation's choice. `None`: the iteration starts a fresh provider session.
    pub fn session_continued_into(&self, iteration: u32) -> Option<&Call> {
        let trial = self.trials.iter().find(|trial| trial.iteration + 1 == iteration)?;
        let evaluation = &trial.evaluation;
        let choice = evaluation.pointer("/next_call/provider_session").or_else(|| evaluation.pointer("/reused_evaluation/next_call/provider_session"));
        if choice.and_then(Value::as_str) == Some(CONTINUE_PROVIDER_SESSION) { self.call(trial.call_id) } else { None }
    }
}

/// The role's choice, in a submission's evaluation (`next_call.provider_session`), that the next iteration's first call
/// continue the provider session that produced the submission (`Ledger::assign_provider_session`); any other value or
/// none starts a fresh provider session.
pub const CONTINUE_PROVIDER_SESSION: &str = "continue";

/// An open ledger: the state plus the run lock held until drop.
pub struct Ledger {
    pub state: LedgerState,
    root: PathBuf,
    _lock: FileLock,
}

/// Resume identity: the request and provider without provider cost wording and without the retired turn setting.
fn resume_identity(mut identity: Value) -> Value {
    if let Some(author) = identity.get_mut("author").and_then(Value::as_object_mut) {
        author.remove("cost_semantics");
    }
    request_without_retired_turn_cap(identity)
}

fn acquire_run_lock(root: &Path) -> Result<FileLock, LedgerError> {
    let path = root.join("controller.lock");
    let lock = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(&path)
        .map_err(|e| RecordError::new(&path, e))?;
    FileLock::acquire(lock, libc::LOCK_EX | libc::LOCK_NB).map_err(|_| LedgerError::AlreadyOwned)
}

impl Ledger {
    /// Open `root/ledger.json`, creating a new session (with a fresh session id) or resuming the persisted one. A
    /// resumed ledger must have the same request/provider identity and active limits; it is not rewritten.
    pub fn open(root: &Path, identity: Value, limits: Limits) -> Result<Self, LedgerError> {
        limits.validate().map_err(LedgerError::InvalidLimits)?;
        records::create_dir(root)?;
        let lock = acquire_run_lock(root)?;
        let path = root.join("ledger.json");
        if !path.exists() {
            let state = LedgerState {
                format_version: 1,
                request: identity,
                session_id: records::random_uuid()?,
                limits,
                iterations: 0,
                calls: vec![],
                receipt_reconciliations: vec![],
                predispatch_recoveries: vec![],
                preparation_context_revisions: vec![],
                trials: vec![],
                incumbent: None,
                closed: None,
            };
            let ledger = Self { state, root: root.to_path_buf(), _lock: lock };
            ledger.save()?;
            return Ok(ledger);
        }
        let state: LedgerState = records::read_json(&path)?;
        if state.format_version != 1
            || !state.limits.same_active_limits(&limits)
            || resume_identity(state.request.clone()) != resume_identity(identity)
        {
            return Err(LedgerError::ResumeIdentityDiffers);
        }
        Ok(Self { state, root: root.to_path_buf(), _lock: lock })
    }

    pub fn save(&self) -> Result<(), LedgerError> {
        Ok(records::write_json_atomic(&self.root.join("ledger.json"), &self.state)?)
    }

    pub fn totals(&self) -> Result<SpendTotals, LedgerError> {
        let mut totals = SpendTotals { spent: Money::default(), reserved: Money::default(), usage_unknown: false };
        for (call, counted) in self.state.calls.iter().zip(self.state.counted_usage()) {
            match counted.cost {
                Some(cost) => totals.spent = totals.spent.checked_sum(cost)?,
                None => {
                    totals.reserved = totals.reserved.checked_sum(call.reservation_usd)?;
                    // An interrupted call awaiting its session's resumption is settled by the resuming call.
                    totals.usage_unknown |= !call.usage_in_resumed_session;
                }
            }
        }
        Ok(totals)
    }

    /// The first guard that forbids another author call, in order: submissions, unknown usage, dollars, retries.
    pub fn stop_reason(&self) -> Result<Option<LedgerStop>, LedgerError> {
        let state = &self.state;
        if state.counted_submissions() >= state.limits.max_iterations {
            return Ok(Some(LedgerStop::IterationLimit));
        }
        let totals = self.totals()?;
        if totals.usage_unknown {
            return Ok(Some(LedgerStop::UsageUnknown));
        }
        if !state.limits.max_cost_usd.is_unset() && totals.spent.checked_sum(totals.reserved)? >= state.limits.max_cost_usd {
            return Ok(Some(LedgerStop::BudgetLimit));
        }
        if state.attempts_of(state.iterations + 1) > state.limits.max_retries_per_iteration as usize {
            return Ok(Some(LedgerStop::RetryLimit));
        }
        Ok(None)
    }

    /// Record a new call of the next iteration with its stop-guard reservation (durable before dispatch).
    pub fn begin_call(&mut self) -> Result<Call, LedgerError> {
        if self.state.closed.is_some() {
            return Err(LedgerError::Closed);
        }
        if let Some(stop) = self.stop_reason()? {
            return Err(LedgerError::Stopped(stop));
        }
        let totals = self.totals()?;
        let iteration = self.state.iterations + 1;
        let guard = self.state.limits.max_cost_usd;
        let call = Call {
            id: self.state.calls.len() as u64 + 1,
            iteration,
            attempt: self.state.attempts_of(iteration) as u32 + 1,
            started_unix_ms: records::now_unix_ms(),
            // Below the guard here (stop_reason passed), so the subtraction cannot underflow.
            reservation_usd: if guard.is_unset() { Money::UNSET } else { Money(guard.0 - totals.spent.0 - totals.reserved.0) },
            receipt: None,
            provider_session: None,
            resumes_provider_session: false,
            usage_in_resumed_session: false,
        };
        self.state.calls.push(call.clone());
        self.save()?;
        Ok(call)
    }

    /// Choose and record (durably, before dispatch) the provider session of `call_id`: a call that already has one keeps
    /// it. Otherwise it resumes an existing provider session when `started(that session's call)` says the session
    /// exists and can continue:
    /// - a retry of an iteration: the session of the latest earlier call of the same iteration (an attempt interrupted
    ///   before it submitted);
    /// - the first call of a new iteration: the session of the call whose submission the previous iteration counted,
    ///   when the role's evaluation of that submission chose to continue it ([`LedgerState::session_continued_into`]);
    ///
    /// else it starts a fresh session. Without the role's choice every new iteration starts a fresh provider session.
    pub fn assign_provider_session(&mut self, call_id: u64, started: impl Fn(&Call) -> bool) -> Result<Call, LedgerError> {
        let index = self.state.calls.iter().position(|call| call.id == call_id).ok_or(LedgerError::UnknownCall(call_id))?;
        if self.state.calls[index].provider_session.is_none() {
            let iteration = self.state.calls[index].iteration;
            let previous = match self.state.calls[..index].iter().rev().find(|call| call.iteration == iteration) {
                Some(retried) => Some(retried),
                None => self.state.session_continued_into(iteration),
            };
            let (session, resumes) = match previous.filter(|call| started(call)) {
                Some(call) => (self.state.provider_session_of(call).to_string(), true),
                None => (records::random_uuid()?, false),
            };
            let call = &mut self.state.calls[index];
            call.provider_session = Some(session);
            call.resumes_provider_session = resumes;
            self.save()?;
        }
        Ok(self.state.calls[index].clone())
    }

    /// Mark interrupted call `call_id` as settled by the call that resumes its provider session (durable).
    pub fn await_session_resume(&mut self, call_id: u64) -> Result<(), LedgerError> {
        let call = self.state.calls.iter_mut().find(|call| call.id == call_id).ok_or(LedgerError::UnknownCall(call_id))?;
        if !call.usage_in_resumed_session {
            call.usage_in_resumed_session = true;
            self.save()?;
        }
        Ok(())
    }

    /// Settle a call's receipt once; an identical duplicate is accepted, a different one refused.
    pub fn settle(&mut self, receipt: Receipt) -> Result<(), LedgerError> {
        let call_id = receipt.call_id;
        let expected_session = self.state.call(call_id).map(|call| self.state.provider_session_of(call).to_string()).ok_or(LedgerError::UnknownCall(call_id))?;
        if receipt.session_id != expected_session {
            return Err(LedgerError::ReceiptSessionMismatch);
        }
        let call =
            self.state.calls.iter_mut().find(|call| call.id == call_id).ok_or(LedgerError::UnknownCall(call_id))?;
        if let Some(prior) = &call.receipt {
            return if *prior == receipt { Ok(()) } else { Err(LedgerError::ConflictingDuplicateReceipt(call_id)) };
        }
        if receipt.ended_unix_ms < call.started_unix_ms {
            return Err(LedgerError::ReceiptBeforeDispatch(call_id));
        }
        call.receipt = Some(receipt);
        self.save()
    }

    /// Fill previously unknown usage of a settled call from a separately obtained provider receipt. Known values
    /// cannot change; the prior receipt and the provenance are kept in `receipt_reconciliations`. Candidate claims are
    /// not usage authority.
    pub fn reconcile_usage(
        &mut self,
        call_id: u64,
        reported_cost: Option<Money>,
        billed_cost: Option<Money>,
        tokens: Option<Tokens>,
        provider_evidence: Value,
    ) -> Result<(), LedgerError> {
        fn fill<T: PartialEq>(slot: &mut Option<T>, value: Option<T>) -> Result<(), LedgerError> {
            if let Some(value) = value {
                if slot.as_ref().is_some_and(|known| *known != value) {
                    return Err(LedgerError::ReconciliationConflict("reconciliation conflicts with known usage"));
                }
                *slot = Some(value);
            }
            Ok(())
        }
        if provider_evidence.is_null() {
            return Err(LedgerError::UsageEvidenceRequired);
        }
        let call =
            self.state.calls.iter_mut().find(|call| call.id == call_id).ok_or(LedgerError::UnknownCall(call_id))?;
        let prior = call.receipt.clone().ok_or(LedgerError::UnsettledCall(call_id))?;
        for cost in [reported_cost, billed_cost].into_iter().flatten() {
            if prior.provider_cost().is_some_and(|known| known != cost) {
                return Err(LedgerError::ReconciliationConflict("reconciliation conflicts with known provider cost"));
            }
        }
        if reported_cost.zip(billed_cost).is_some_and(|(reported, billed)| reported != billed) {
            return Err(LedgerError::ReconciliationConflict("reconciliation contains conflicting provider costs"));
        }
        let mut next = prior.clone();
        fill(&mut next.reported_cost_usd, reported_cost)?;
        fill(&mut next.billed_cost_usd, billed_cost)?;
        fill(&mut next.tokens, tokens)?;
        if prior == next {
            return Ok(());
        }
        self.state.receipt_reconciliations.push(json!({"call_id":call_id,"prior":prior,"reconciled":next,
            "provider_evidence":provider_evidence,"recorded_unix_ms":records::now_unix_ms()}));
        call.receipt = Some(next);
        self.save()
    }

    /// Count the settled call's candidate as the next iteration (durable before evaluation). Failures consume this
    /// same iteration.
    pub fn submit(&mut self, call_id: u64, candidate: Value) -> Result<u32, LedgerError> {
        if self.state.counted_submissions() >= self.state.limits.max_iterations {
            return Err(LedgerError::Stopped(LedgerStop::IterationLimit));
        }
        let call = self.state.call(call_id).ok_or(LedgerError::UnknownCall(call_id))?;
        if call.iteration != self.state.iterations + 1
            || call.receipt.as_ref().and_then(|receipt| receipt.output.as_ref()) != Some(&candidate)
        {
            return Err(LedgerError::CandidateMismatch(call_id));
        }
        self.state.iterations += 1;
        self.state.trials.push(Trial {
            iteration: self.state.iterations,
            call_id,
            candidate,
            status: TrialStatus::Submitted,
            evaluation: Value::Null,
            framework_elapsed_ms: None,
            directory: None,
            recovery_records: vec![],
            evaluation_record: None,
        });
        self.save()?;
        Ok(self.state.iterations)
    }

    /// Usage totals of every call, or of the calls of one iteration.
    pub fn accounting(&self, iteration: Option<u32>) -> Result<Accounting, LedgerError> {
        let mut accounting = Accounting {
            calls: 0,
            call_ids: vec![],
            author_elapsed_ms: 0,
            provider_reported_cost_usd: None,
            known_provider_reported_cost_usd: Money::default(),
            cost_complete: true,
            tokens: None,
            observed_token_lower_bound: Tokens::default(),
            tokens_complete: true,
            counting: "per call by the receipt's declared usage_scope (counted_usage); scope_unknown counts the raw receipt",
            counted_by_call: vec![],
            scope_complete: true,
            raw_receipt_sum_usd: Money::default(),
        };
        let selected = self
            .state
            .calls
            .iter()
            .zip(self.state.counted_usage())
            .filter(|(call, _)| iteration.is_none_or(|i| call.iteration == i));
        for (call, counted) in selected {
            accounting.calls += 1;
            accounting.call_ids.push(call.id);
            let Some(receipt) = &call.receipt else {
                accounting.cost_complete = false;
                accounting.tokens_complete = false;
                continue;
            };
            accounting.author_elapsed_ms += receipt.elapsed_ms as u128;
            accounting.counted_by_call.push(CountedCall { call_id: call.id, usage_scope: receipt.usage_scope, basis: counted.basis });
            accounting.scope_complete &= counted.basis != CountingBasis::ScopeUnknown;
            accounting.raw_receipt_sum_usd =
                accounting.raw_receipt_sum_usd.checked_sum(receipt.provider_cost().unwrap_or_default())?;
            match counted.cost {
                Some(cost) => {
                    accounting.known_provider_reported_cost_usd = accounting.known_provider_reported_cost_usd.checked_sum(cost)?
                }
                None => accounting.cost_complete = false,
            }
            match &counted.tokens {
                Some(tokens) => accounting.tokens_complete &= accounting.observed_token_lower_bound.accumulate(tokens),
                None => accounting.tokens_complete = false,
            }
        }
        accounting.provider_reported_cost_usd =
            accounting.cost_complete.then_some(accounting.known_provider_reported_cost_usd);
        accounting.tokens = accounting.tokens_complete.then(|| accounting.observed_token_lower_bound.clone());
        Ok(accounting)
    }

    /// The author-facing LEDGER of a prompt ([`LedgerState::author_view`] over this ledger's file).
    pub fn author_view(&self, current_call: u64) -> Result<Value, LedgerError> {
        self.state.author_view(current_call, &self.root.join("ledger.json"))
    }
}

impl LedgerState {
    /// The author-facing LEDGER of the prompt of `current_call`: counted provider cost of the earlier calls (a resumed
    /// session total once, by increment), guards, submissions, and the earlier calls that ended without a candidate.
    /// The current call has no receipt yet; it is shown by its stop-guard reservation only. Every per-call receipt
    /// stays in `ledger_file` (`calls[]`), so the view's size does not grow with the number of calls: earlier calls are
    /// a count, and consecutive calls of one iteration that ended without a candidate with the same outcome class
    /// (the outcome before its first `:`, for example repeated provider errors whose texts differ only in details) are
    /// one run with its first and last call, its count and its last outcome.
    pub fn author_view(&self, current_call: u64, ledger_file: &Path) -> Result<Value, LedgerError> {
        let mut spent = Money::default();
        let mut spent_complete = true;
        let mut earlier_calls = 0u64;
        let mut runs_without_candidate: Vec<Value> = vec![];
        for (call, counted) in self.calls.iter().zip(self.counted_usage()).filter(|(call, _)| call.id != current_call) {
            earlier_calls += 1;
            match counted.cost {
                Some(cost) => spent = spent.checked_sum(cost)?,
                None => spent_complete = false,
            }
            let receipt = call.receipt.as_ref();
            if receipt.is_some_and(|receipt| receipt.output.is_some()) {
                continue;
            }
            let outcome = receipt.map_or("no receipt (interrupted)".to_string(), |receipt| receipt.outcome.clone());
            let class = outcome.split(':').next().unwrap_or_default().to_string();
            match runs_without_candidate.last_mut() {
                Some(run) if run["last_call"] == call.id - 1 && run["iteration"] == call.iteration && run["outcome_class"] == class.as_str() => {
                    run["last_call"] = json!(call.id);
                    run["calls"] = json!(run["calls"].as_u64().unwrap_or(1) + 1);
                    run["last_outcome"] = json!(outcome);
                }
                _ => runs_without_candidate.push(json!({"first_call":call.id,"last_call":call.id,"calls":1,"iteration":call.iteration,
                    "outcome_class":class,"last_outcome":outcome})),
            }
        }
        let this_call = self.call(current_call).map(|call| {
            json!({"call":call.id,"iteration":call.iteration,"attempt":call.attempt,"stop_guard_usd":call.reservation_usd})
        });
        let submission_limit = count_guard(self.limits.max_iterations);
        let remaining_submissions = submission_limit
            .as_u64()
            .map_or(json!("unset"), |limit| json!(limit.saturating_sub(u64::from(self.counted_submissions()))));
        Ok(json!({
            "max_cost_usd":self.limits.max_cost_usd,"spent_usd":spent,"spent_complete":spent_complete,
            "remaining_usd":self.limits.max_cost_usd.remaining_after(spent),
            "this_call":this_call,
            "submissions":{"used":self.counted_submissions(),"limit":submission_limit,"remaining_including_this_call":remaining_submissions,
                "not_counted_framework_failures":self.uncounted_framework_failures()},
            "earlier_calls":earlier_calls,"runs_without_candidate":runs_without_candidate,
            "file":ledger_file
        }))
    }
}

#[cfg(test)]
mod tests;
