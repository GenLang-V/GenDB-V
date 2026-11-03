//! Hooks through which a synthesis role plugs into the generic author-session loop.
//!
//! A role is what one author session produces and how GenDB judges it: the verified query role (a Verus/Rust
//! implementation of one SQL statement, `synthesis::query`), and the workload storage role (verified builders and
//! readers of shared storage, `synthesis::workload`). The controller is the same for every role: it owns the ledger,
//! the author calls, submission counting, feedback order, unchanged-resubmission reuse, qualification order and
//! closure. A role supplies two things:
//!
//! - [`SynthesisRole`]: the stateful stages. `prepare` writes the author's inputs and returns the context;
//!   `freeze` snapshots a submission; `evaluate` judges a frozen candidate; `qualify` re-checks the best eligible
//!   candidate before it can be selected; `close` records the role's resolution. A stage error of `freeze`,
//!   `evaluate` or `qualify` is recorded as that submission's outcome; a `prepare` or `close` error stops the run as a
//!   resumable framework error. Two optional stages serve a no-author reselection (`controller::reselect`):
//!   `policy_exclusion` judges a recorded evaluation against the run's policy, `import_frozen` copies another
//!   session's frozen candidate. One optional stage serves a session that continues from an earlier session's
//!   admitted candidate (`RunRequest::continue_from`): `seed_incumbent` writes that candidate into the workspace.
//! - [`RolePolicy`]: pure decisions over the prepared context and the ledger's trials: the author prompt, the
//!   objective, an early search stop and framework repair revisions, plus what a retained submission's frozen code is
//!   (read from its records only). A policy value is cheap to clone and sendable,
//!   so a retained role service can answer it without its owner thread.

use super::layout::RunLayout;
use super::ledger::{Call, Receipt, Trial};
use super::limits::Limits;
use super::records::RecordError;
use super::trajectory::local_job_summary;
use super::author::CandidateSubmission;
use super::run::{RunRequest, StopReason};
use serde_json::{Value, json};
use std::path::Path;

/// The feedback event of a settled author call (`PromptInput::feedback`): its call, iteration and attempt, the
/// outcome, the provider-reported cost and the tokens.
pub fn call_event(call: &Call, receipt: &Receipt) -> Value {
    json!({"call":call.id,"iteration":call.iteration,"attempt":call.attempt,"author_outcome":receipt.outcome,
        "provider_reported_cost_usd":receipt.provider_cost(),"tokens":receipt.tokens})
}

/// The local-jobs feedback event of a settled author call: the jobs that call ran (`local_jobs`) and the session's jobs
/// up to and including it (`session_local_jobs`); `None` when the call ran none.
pub fn local_jobs_event(layout: &RunLayout, call: &Call) -> Result<Option<Value>, RecordError> {
    let of_call = local_job_summary(layout, |id| id == call.id)?;
    if of_call.jobs == 0 {
        return Ok(None);
    }
    let session = local_job_summary(layout, |id| id <= call.id)?;
    Ok(Some(json!({"call":call.id,"iteration":call.iteration,"local_jobs":of_call,"session_local_jobs":session})))
}

/// Inputs of one author prompt.
pub struct PromptInput<'a> {
    /// The context returned by `SynthesisRole::prepare`.
    pub context: &'a Value,
    /// Feedback events in order: every trial (as serialized), then per call its [`call_event`], its
    /// [`local_jobs_event`] when the call ran local jobs, and each newly evaluated trial.
    pub feedback: &'a [Value],
    /// The iteration this call works towards (the submission's record number, framework failures included).
    pub iteration: u32,
    /// The submission this call works towards as the guard counts it (counted submissions + 1; framework failures are
    /// not counted).
    pub submission: u32,
    pub limits: &'a Limits,
    /// `Ledger::author_view` of this call.
    pub ledger: &'a Value,
    /// Where this call's complete prompt is saved before the call starts (`RunLayout::prompt`): the prompt names it so
    /// the author can reread it.
    pub prompt_file: &'a Path,
    /// The handoff from earlier attempts when this call starts a fresh provider session after one or more submissions
    /// or after an earlier provider session (`controller::trajectory::attempt_handoff`: GenDB's facts and the author's
    /// `NOTES.md`); null when the call continues a session or is the first session's first call.
    pub handoff: &'a Value,
}

pub trait RolePolicy: Clone + Send + 'static {
    /// The complete prompt of one author call.
    fn author_prompt(&self, input: &PromptInput) -> String;

    /// The role's objective over the trials so far. The controller reads only `"status"`: `"unmet"` keeps the search
    /// open after one unchanged resubmission (see `run::unchanged_resubmission_stop`); any other status closes it.
    fn objective_status(&self, _context: &Value, _trials: &[Trial]) -> Value {
        json!({"status":"not_configured","reason":"this role declares no objective"})
    }

    /// Stop the search before the next author call (for example `StopReason::FirstEligibleCandidate` for a
    /// correctness objective). Ledger guards apply independently.
    fn search_stop(&self, _context: &Value, _trials: &[Trial]) -> Option<StopReason> {
        None
    }

    /// What the next attempt should know about the code of a retained submission (frozen under `frozen_dir`, submitted
    /// as `candidate`): for example a short identity of its frozen code and, given the author `workspace`, whether it
    /// still holds the same code. Read from the frozen records and the workspace only; nothing is evaluated. Default:
    /// nothing (`Null`).
    fn submission_code(&self, _frozen_dir: &Path, _candidate: &Value, _workspace: Option<&Path>) -> Value {
        Value::Null
    }

    /// A narrowly identified framework repair that may reevaluate a retained frozen submission with this recorded
    /// evaluation when an unfinished run resumes. Revisions are `[A-Za-z0-9_-]+`; each is applied once per trial and
    /// never dispatches an author.
    fn repair_revision(&self, _evaluation: &Value) -> Option<&'static str> {
        None
    }
}

#[allow(async_fn_in_trait)]
pub trait SynthesisRole {
    type Policy: RolePolicy;

    fn policy(&self) -> Self::Policy;

    /// Prepare the author's inputs in `workspace`; the returned context is recorded and drives the policy.
    async fn prepare(&mut self, request: &RunRequest, workspace: &Path) -> Result<Value, String>;

    /// Snapshot a submission into `frozen_dir` (a fresh directory); `Ok` is the frozen candidate value.
    async fn freeze(&mut self, workspace: &Path, frozen_dir: &Path, submission: &CandidateSubmission) -> Result<Value, String>;

    /// Judge a frozen candidate; the evaluation contract is documented on `Trial`.
    async fn evaluate(&mut self, frozen_dir: &Path, candidate: &Value) -> Result<Value, String>;

    /// Re-check an eligible candidate before selection; `"qualified": true` selects it.
    async fn qualify(&mut self, frozen_dir: &Path, evaluation: &Value) -> Result<Value, String>;

    /// The prepared-context facts other sessions change meanwhile, recomputed now (for example the shared storage
    /// budget), merged into the context before every author call; `Null`: none. Never touches author code or prepared
    /// proof and data artifacts.
    async fn refresh_shared_facts(&mut self) -> Result<Value, String> {
        Ok(Value::Null)
    }

    /// Record the role's resolution of the session (for example admission and publication of the selection).
    async fn close(&mut self, trials: &[Trial], qualification: &[QualificationAttempt]) -> Result<Value, String>;

    /// Why the run's policy no longer admits a candidate with this recorded evaluation, judged on the record alone
    /// (`None`: admitted). A reselection (`controller::reselect`) asks before any copy or evaluation; the fresh
    /// evaluation and qualification still apply every policy check. Default: nothing is excluded.
    async fn policy_exclusion(&mut self, _evaluation: &Value) -> Result<Option<String>, String> {
        Ok(None)
    }

    /// Copy the frozen candidate retained in `source` (another session's frozen directory) into the fresh directory
    /// `frozen_dir` for a fresh evaluation: its frozen sources and metadata only, location metadata rebased onto the
    /// copy, never the source's evaluation outputs; `source` is only read. `Ok` is the frozen candidate value as
    /// `freeze` would return it for the copy. Default: the role cannot import (a reselection refuses).
    async fn import_frozen(&mut self, _source: &Path, _frozen_dir: &Path) -> Result<Value, String> {
        Err("this role cannot import a frozen candidate of another session".into())
    }

    /// Write the admitted candidate of the closed session `source` into the author `workspace` as the incumbent of a
    /// continuing session (`RunRequest::continue_from`): its author files, in the layout a submission of this role
    /// names, so that `freeze` with the returned submission freezes it with the current framework. `source` is only
    /// read. Default: the role cannot continue from an incumbent (the session stops before any author call).
    async fn seed_incumbent(&mut self, _source: &Path, _workspace: &Path) -> Result<SeededIncumbent, String> {
        Err("this role cannot continue from an earlier session's admitted candidate".into())
    }
}

/// The incumbent a role wrote into the author workspace (`SynthesisRole::seed_incumbent`).
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize, PartialEq)]
pub struct SeededIncumbent {
    /// The submission that freezes the seeded workspace: the source submission's manifest path, rationale and data
    /// access analysis.
    pub submission: CandidateSubmission,
    /// The source session's recorded evaluation of that candidate: shown, marked, by a render-only author instead of a
    /// fresh evaluation (`AuthorTransport::render_only`); never used otherwise.
    pub source_evaluation: std::path::PathBuf,
    /// Where it came from and what was written (recorded in the incumbent's `incumbent.json`).
    pub provenance: Value,
}

/// One qualification of an eligible trial, in the order tried.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize, PartialEq)]
pub struct QualificationAttempt {
    pub iteration: u32,
    /// The role's qualification record plus `framework_elapsed_ms`.
    pub result: Value,
}

impl QualificationAttempt {
    pub fn qualified(&self) -> bool {
        self.result["qualified"] == true
    }
}
