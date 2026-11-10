//! The general line's acceptance of submissions: the
//! stages of a general-line session (`engine::role` in session mode) and the timing of admitted versions that version
//! 0 and the scale ladder reuse (`engine::branches`).
//!
//! A submission is evaluated under the development plan ([`EngineBench::submission_plan`],
//! `engine::protocol::development`; the full protocol is for the final numbers only, `engine::final_evaluation`; its
//! timed cells are 1 warm + `engine.timed_calls` hot calls, by default 3 as the final plan's, the median hot call the
//! cell's time), every step gating:
//! 1. freeze and scans (`engine::submission::freeze_engine` under the general line's rule set). A refusal there is
//!    evaluated as an attempt like any other outcome ([`REFUSED_CANDIDATE_KIND`]), so every submission's evaluation
//!    names the next call's provider session and every refused submission is a node of the tree;
//! 2. the whole-crate Verus run (`--no-cheating`, 0 errors) and its compiled library;
//! 3. storages: the new storages built, the storage policy and the budget rule (plain storage
//!    only is allowed as is; changed storage within the original data size at the current scale;
//!    `engine::role::GeneralInputs::budget_rule`);
//! 4. the interleaved timing against the parent at the current scale (`engine::race`), each side of a cell 1 warm call
//!    and the run's timed hot calls (the median hot call is the cell's time), every answer compared with the saved
//!    answers; each pair after the host's quiet-moment gate, and the suspicious pairs timed again once at the end;
//! 5. the score decision (`engine::score`): not better, the submission is an attempt and the branch head stays;
//! 6. every variant with AST bytes of its own, at the first scale of the ladder (every template finishes there), one
//!    call each at 64 workers for its answer only (a session at a later scale resolves the candidate's storages there
//!    with its checked storages, a derived storage's asset built by its verified builder: `Workbench::at_capture`); no
//!    qualification at the other visible bindings;
//! 7. admission under the library's budget lock with its lineage (`gendb_artifacts::verus::VerusEngineLineageV1`), the
//!    version folder and node; then the main-line head ([`MainLineCase::step`]): an accepted merge becomes it; a branch
//!    version whose parent is the main-line head (at the current scale and timing binding) takes the decision of its
//!    acceptance race, which already timed it against the head (adopted, recorded as such, not timed again); any other
//!    branch version whose score beats the main-line head's recorded score is timed against it, and the winner is the
//!    main-line head (the library's selection record and `main-line.jsonl`).
//!
//! No profile follows an admission (the author's `profile` tool and the final evaluation profile). Each evaluation
//! records its plan and the wall time of each step it ran (`steps`), which the next call's facts show. The admission
//! also promotes the session's builds of its new storages at other captures into the library (the first scale's, for
//! the variants: `trials_promoted`), and once the verdict is recorded, a run with one branch releases the library's
//! superseded derived storage assets (`engine::asset_upkeep`).
//!
//! The parent is the branch head (a merge session's and a rebase's, `base: main_line_head`: the main-line head). A
//! wrong answer of the candidate refuses it and is flagged for the operator (`flags.jsonl`); a wrong answer or failure of an
//! admitted parent is an incident: the evaluation fails in the framework (the run stops resumably) and is flagged.
//! Every evaluated submission is appended to the findings log and the tree views are rewritten. Then the scale ladder
//! is checked over the tree (`engine::branches::ladder_check`): when its move is due, the evaluation ends the session
//! (`engine::sessions::session_end`, `scale_move`), so that the run can move.
//!
//! **Admission happens once per frozen submission**, whenever the controller stops. Before the library admission the
//! evaluation writes its intent beside the frozen submission (`admitting.json`, [`AdmissionIntent`]: the build, the
//! evidence and what the records keep); after it, the admission (`admitted.json`), before the version folder. The
//! admission decides the budget rule of the current scale again, under the library's budget lock. A resumed evaluation that finds the intent without the admission looks in the library for the admission of
//! the same frozen candidate ([`admitted_version_of`]: the version whose build was frozen in the same directory with
//! the same author files) and adopts it, or, when there is none (the controller stopped before admitting), admits from
//! the intent: no second admission, Verus run or timing. Version 0 follows the same rule (`engine::branches`). An
//! attempt is recorded likewise (`attempt.json`, `recorded.json`).
//!
//! **Stage runs** (`engine::stage`): the role's stage makes every freeze a workload's crate and every
//! admission the stage admission. A submission freezes every workload's crate (a kept crate refused at freeze is an
//! attempt); steps 2-6 above are the goal workload's, whose score decides; a goal not better is an attempt and no kept
//! workload runs. Then every kept workload in its library: whole-crate Verus, storages and its budget, its interleaved
//! timing against the parent's side of that workload (recorded and shown, never deciding: no guard), its variants at its
//! first scale (`engine::stage::evaluate_kept_workloads`; a refusal there is an attempt, a wrong answer flagged). The
//! admission's intent holds every crate; the goal is admitted first and every kept crate after it as the same library
//! version (`engine::stage::admit_in_lockstep`), each once on resume; the version folder holds every workload's
//! records (`engine::stage::records`), the evaluation record names `kept_workloads`, the main line selects the version
//! in every library, the findings entry carries every kept workload's effect, and each library releases its superseded
//! assets. A stage crate evaluated outside its stage run (a re-evaluation) is refused as a framework error.
//!
//! **Runs of several workloads** (`engine.workloads`, `engine::stage`): the same steps over
//! every workload, in this order, each gating (`engine::stage::members`): every workload's crate frozen (a refusal is an
//! attempt); Verus on every crate, the primary's first; every workload's storages (a check workload is exempt from the
//! budget rule); every check workload's answers at every visible binding before any timing (a wrong answer is
//! flagged); the primary's interleaved timing against its parent, then every other counted workload's against the
//! parent's side of it; the **combined decision** (the sums of the counted workloads' scores of these races,
//! `engine::score::CombinedScore`; no guard per workload): not better, the submission is an attempt with every counted
//! workload's race recorded and every kept workload `not_run`; then every kept workload's timing (recorded, never
//! deciding); then every workload's variants at its first scale. Every workload's status goes to `members.json` and the
//! combined decision to `combined.json` of the evaluation (its record's `members` and `combined`). The admission and the records are the stage run's, over every workload: every crate in
//! its library in lockstep, the version folder with every workload's records, `combined_score` and the one-engine
//! record `general`, the main line selecting it in every library (one line of versions: the accepted version's parent
//! is the main-line head, so its combined decision is the main-line decision), the findings entry with every workload's
//! effect and the combined decision. When the request sets the one-engine rule (`engine.workloads.require_one_engine`,
//! `engine::stage::one_engine`), a submission that is not one engine is refused right after the freeze, and while the
//! head is not one engine the first correct one-engine submission is accepted and becomes the head even when its
//! combined score is not better (`one_engine_transition` in the combined decision, the version and the main line).
//!
//! **Re-evaluation** (`gendb engine re-evaluate`, `engine::re_evaluation`): the same steps for a recorded attempt that
//! was judged not better ([`EngineBench::re_evaluate_attempt`], [`JudgedFrom::RecordedAttempt`]): the Verus run recorded
//! at its first evaluation (no second run), its recorded race with the suspicious pairs timed again, and, when it is now
//! better, the variants, the admission and every record of an acceptance, through the same admission intent and files
//! beside the frozen submission (so an interrupted re-evaluation resumes without a second admission).

use super::branches::{due_scale_move, ladder_check};
use super::facts::EncodedStatement;
use super::protocol::{DEFAULT_TIMED_CALLS, EvaluationPlan, VariantRun, development, hot_calls_text};
use super::re_evaluation::ReEvaluationPlan;
use super::quiet::{HostClock, QuietGate};
use super::race::{Contender, RaceError, RaceHost, RaceReport, RaceSetup, RecordedRace, Side, race, retime_recorded};
use super::timing::read_load_average;
use super::role::{EngineBench, EngineCells, copy_tree, float_free, storage_inputs, storage_view, write_matrix};
use super::score::{CellResult, CellStatus, ScaleScore, ScoreError, score};
use super::sessions::{ProviderContext, SessionKind, next_call, session_end};
use super::submission::{CRATE_DIRECTORY, EngineManifest, FrozenEngine, GENERATION_IDENTITY, SubmissionBase, engine_version_id};
use super::timing::{EngineMatrix, EngineStatement, MatrixKind, check_answers, run_matrix_recording_failures, run_official_recording_failures};
use super::tree::{
    self, ADOPTED_ACCEPTANCE_RACE, MainLineChange, NodeKind, RecordedScore, TreeNode, VersionTree, append_finding, append_flag, append_main_line, node_directory,
    record_scale_score, take_attempt_directory, version_id, version_number,
};
use super::stage::members::MemberStatuses;
use super::stage::{self, LineageOf, MemberKeep};
use crate::controller::author::CandidateSubmission;
use crate::controller::layout::{NOTES_FILE, RunLayout};
use crate::controller::ledger::LedgerState;
use crate::controller::limits::Money;
use crate::controller::records::{self, now_unix_ms, read_json, write_json_atomic};
use crate::controller::run::RunRequest;
use crate::controller::Trial;
use crate::file_lock::FileLock;
use crate::query::candidate::{FrozenUse, StorageSource};
use crate::query::compile::agent_modules;
use crate::storage::engine_library::{NewEngineStorage, admit_engine_version_on_line, check_engine_storage_uses, engine_assets, library_bytes};
use crate::storage::library_lock::{BUDGET_LOCK, LibraryLock};
use crate::storage::payload::PayloadHolder;
use crate::storage::{catalog, flat};
use crate::tools::{AuthorRole, TrialVerification};
use gendb_artifacts::verus::{
    EngineVersion, VERUS_ENGINE_LINEAGE_KIND, VerusEngineLineageV1, VerusEngineSelectionV1, VerusSourceOwnerV1, VerusStorageUseV1, check_build_evidence,
    engine_versions, library_path, select_engine_version,
};
use gendb_artifacts::{ContentId, ObjectStore, blob_id};
use gendb_runtime::worker::{AnswerBound, StorageUseInput};
use gendb_storage::versions::CurrentCapture;
use gendb_verification::admission::engine::{EngineAdmission, EngineCandidate, EngineRunner, EngineSchema, SkippedTemplate, qualify_finished_templates};
use gendb_verification::admission::{AdmissionError, FailureClass};
use gendb_verification::obligations::ENGINE_TRUSTED_ASSUMPTIONS;
use gendb_verification::verus::engine_rules::EngineLine;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

/// `kind` of a submission refused at freeze in a general-line session: its evaluation records the attempt.
pub const REFUSED_CANDIDATE_KIND: &str = "verus_engine_refused";
/// Record kind of an interleaved timing's summary stored as evidence (admission, selection).
pub const ENGINE_RACE_KIND: &str = "gendb.verus.engine-race.v1";
/// Record kind of the qualification and variants of the finished templates (admission evidence).
pub const ENGINE_FINISHED_CHECKS_KIND: &str = "gendb.verus.engine-finished-checks.v1";
/// The admission of a frozen submission (its node and record), written beside it before its version folder.
const ADMITTED_FILE: &str = "admitted.json";
/// The intent to admit a frozen submission ([`AdmissionIntent`]), written beside it before the library admission.
pub(super) const ADMITTING_FILE: &str = "admitting.json";
/// Crash points of the trial (test builds only, [`crash_point`]): just before and just after the library admission.
#[cfg(test)]
pub(super) const CRASH_BEFORE_ADMISSION: &str = "before_engine_admission";
#[cfg(test)]
pub(super) const CRASH_AFTER_ADMISSION: &str = "after_engine_admission";
/// Crash point of the trial (test builds only): just after a submission's workspace storages are registered, before the
/// engine's library admission.
#[cfg(test)]
pub(super) const CRASH_AFTER_STORAGE_REGISTRATION: &str = "after_storage_registration";
/// The main-line decision after an admission, written beside the frozen submission.
const MAIN_LINE_DECISION_FILE: &str = "main-line.json";
/// The verdict of a frozen submission, written beside it once every record is complete.
const RECORDED_FILE: &str = "recorded.json";
/// The lock of the main-line head under the engine directory.
const MAIN_LINE_LOCK: &str = "main-line.lock";

/// The claim of an accepted general-line version.
const ACCEPTED_CLAIM: &str = "Verus checked the whole frozen engine crate (framework files, toolkit, copied storage interfaces and the agent) with 0 errors against the fixed engine entry under the recorded TCB and the general line's source rules: the engine claim is the correctness claim. It beat its parent in one interleaved timing of the development plan (@CELL@; more finished cells, or as many and a smaller normalized time), and every answer of the timing and of the variants (at the first scale of the ladder) agreed with the saved answers of other engines (agreement and echo are checks of the trusted base, not proof)";

/// The claim of the first one-engine version of a run of several workloads accepted by the one-engine rule
/// (`engine::stage::one_engine`): the same proof and answer checks, without the timing claim.
const ONE_ENGINE_TRANSITION_CLAIM: &str = "Verus checked every workload's whole frozen engine crate (framework files, toolkit, copied storage interfaces and the agent) with 0 errors against the fixed engine entry under the recorded TCB and the run's source rules: the engine claim is the correctness claim. It is the first one-engine version of the line, accepted by the request's one-engine rule although its combined score is not better than its parent's: every check workload's answers and every counted cell of its interleaved timings (@CELL@) finished and agreed with the saved answers of other engines, and so did its variants (agreement and echo are checks of the trusted base, not proof)";

/// The claim of an accepted version: [`ONE_ENGINE_TRANSITION_CLAIM`] for one the one-engine rule accepted (its
/// evaluation's `parts`), else [`ACCEPTED_CLAIM`], each with its timings' cell (`timed_calls` hot calls after the warm
/// one, `engine.timed_calls`).
fn accepted_claim(parts: &Value, timed_calls: u32) -> String {
    let claim = if parts["combined"][stage::one_engine::ONE_ENGINE_TRANSITION].is_object() { ONE_ENGINE_TRANSITION_CLAIM } else { ACCEPTED_CLAIM };
    claim.replace("@CELL@", &format!("1 warm + {} per cell, the median hot call the cell's time", hot_calls_text(timed_calls)))
}

/// How an attempt's reason starts when the score decision (step 5) refused it: the attempts `gendb engine re-evaluate`
/// takes.
pub(super) const NOT_BETTER_REASON: &str = "not better than its parent";

/// The wall time of each step one evaluation ran, in order (`steps` of the evaluation record; the next call's facts
/// show them). A step that failed is timed too.
#[derive(Debug, Default)]
pub(super) struct StepTimes(Vec<(String, u64)>);

impl StepTimes {
    /// Run `work` as step `step` and record its wall time in ms.
    pub(super) fn time<T>(&mut self, step: impl Into<String>, work: impl FnOnce() -> T) -> T {
        let step = step.into();
        let started = Instant::now();
        let outcome = work();
        self.0.push((step, started.elapsed().as_millis() as u64));
        outcome
    }

    pub(super) fn record(&self) -> Value {
        json!(self.0.iter().map(|(step, ms)| json!({"step":step,"elapsed_ms":ms})).collect::<Vec<_>>())
    }
}

/// One version ready to run at the current capture: its compiled library and the storage inputs of its uses.
pub(super) struct Runnable {
    /// The version (`v003`) or the candidate's label.
    pub label: String,
    pub library: PathBuf,
    pub inputs: Vec<StorageUseInput>,
}

/// What the controller recorded about one submission: the iteration, the call that produced it, its manifest (absent
/// when the freeze refused it before reading one), its rationale, the iteration's notes and its provider-reported cost.
pub(super) struct SubmissionFacts {
    iteration: u32,
    call_id: u64,
    manifest: Option<EngineManifest>,
    rationale: String,
    notes: Option<PathBuf>,
    cost: Value,
}

impl SubmissionFacts {
    /// Read from the session's ledger and the frozen submission (`<session>/iterations/NNNN/frozen`).
    pub(super) fn read(session_dir: &Path, frozen_dir: &Path) -> Result<Self, AdmissionError> {
        let iteration = frozen_dir.parent().and_then(|d| d.file_name()).and_then(|n| n.to_str()).and_then(|n| n.parse::<u32>().ok())
            .ok_or_else(|| AdmissionError::tool(format!("{} is not a session's frozen submission", frozen_dir.display())))?;
        let layout = RunLayout::new(session_dir);
        let ledger: LedgerState = read_json(&layout.ledger()).map_err(AdmissionError::tool)?;
        let trial = ledger.trials.iter().find(|t| t.iteration == iteration).ok_or_else(|| AdmissionError::tool(format!("iteration {iteration} is not in the session's ledger")))?;
        let manifest_path = frozen_dir.join("manifest.json");
        let manifest = if manifest_path.is_file() { Some(read_json(&manifest_path).map_err(AdmissionError::tool)?) } else { None };
        let (mut spent, mut complete) = (Money::default(), true);
        let mut calls = vec![];
        for (call, counted) in ledger.calls.iter().zip(ledger.counted_usage()).filter(|(c, _)| c.iteration == iteration) {
            calls.push(json!({"call":call.id,"provider_session":ledger.provider_session_of(call),"basis":format!("{:?}", counted.basis)}));
            match counted.cost.map(|c| spent.checked_sum(c)) {
                Some(Ok(sum)) => spent = sum,
                _ => complete = false,
            }
        }
        let notes = Some(layout.iteration_notes(iteration)).filter(|p| p.is_file());
        Ok(Self {
            iteration,
            call_id: trial.call_id,
            manifest,
            rationale: trial.candidate["rationale"].as_str().unwrap_or_default().to_string(),
            notes,
            cost: json!({"known_provider_reported_cost_usd":spent,"complete":complete,"calls":calls,
                "scope":"provider-reported cost of the calls towards this submission (the session's calls since its previous submission), counted once by the ledger's rules"}),
        })
    }
}

/// How a submission was judged. `parts`: what a run of several workloads adds to the evaluation record, as an object of
/// its keys (a stage run's `kept_workloads`, `engine::stage::KeptStatus`; a run of several workloads' `members` and
/// `combined`, `engine::stage::members`); `Null` in a run of one workload.
enum Verdict {
    /// Admitted as a version (`record`: the version's record).
    Accepted { node: TreeNode, record: Value, merge_accepted: bool, main_line: Value, parts: Value },
    /// Recorded as an attempt (`flagged`: the operator must look at it).
    Attempt { node: TreeNode, flagged: bool, parts: Value },
}

/// A step's failure: the candidate's (an attempt, flagged when an answer was wrong) or the framework's.
pub(super) enum Failure {
    Candidate { reason: String, flagged: bool, score: Option<RecordedScore> },
    Framework(AdmissionError),
}

impl From<AdmissionError> for Failure {
    /// A tool failure is the framework's; every other class is the candidate's.
    fn from(error: AdmissionError) -> Self {
        if error.class == FailureClass::ToolFailure { Failure::Framework(error) } else { Failure::Candidate { reason: error.to_string(), flagged: false, score: None } }
    }
}

/// The parent a submission is judged against, with how it was chosen.
pub(super) struct Parent {
    pub(super) id: String,
    pub(super) chosen: &'static str,
}

/// What steps 1-6 of an accepted submission produced for its admission (step 7): its score, its record (without the
/// admission), and what the admission needs.
struct Prepared {
    score: RecordedScore,
    record: Value,
    build: Value,
    evidence: Vec<(String, Value)>,
    /// A run of several workloads: every other workload's preparation for its admission.
    kept: Vec<MemberKeep>,
}

/// Where a judged submission's build and interleaved timing come from (module documentation).
#[derive(Clone, Copy, Debug)]
pub(super) enum JudgedFrom<'a> {
    /// Its own evaluation: the whole-crate Verus run now and one interleaved timing against its parent.
    Submission,
    /// The re-evaluation of a recorded attempt: the whole-crate Verus run recorded in `build` (its `run.json` and
    /// library; not run again) and the attempt's race recorded at `race`, its suspicious pairs timed again
    /// (`engine::race::retime_recorded`).
    RecordedAttempt { build: &'a Path, race: &'a Path },
}

/// What the re-evaluation of a recorded attempt became ([`EngineBench::re_evaluate_attempt`]).
pub(super) enum ReEvaluated {
    /// Admitted as the version `node` (`already`: by an earlier re-evaluation, returned as recorded), with its main-line
    /// decision.
    Admitted { node: TreeNode, main_line: Value, already: bool },
    /// Still not admitted: why, whether an answer was wrong (flagged for the operator), and its score when it was timed.
    NotAdmitted { reason: String, flagged: bool, score: Option<RecordedScore> },
}

/// The engine whose finished templates a plan checks (step 6): its compiled library and its storage inputs at the
/// current scale; for a submission also its frozen storage uses and frozen directory, resolved again at the ladder's
/// first scale when the run is at a later one (`None`: an admitted version, checked at the current scale only).
pub(super) struct CheckedEngine<'a> {
    pub library: &'a Path,
    pub inputs: &'a [StorageUseInput],
    pub frozen: Option<(&'a [FrozenUse], &'a Path)>,
}

/// The intent to admit one frozen submission (`admitting.json`, module documentation): what the library admission
/// needs (the evaluation's whole-crate build record, the evidence records by kind, the evaluation directory) and what
/// the caller records with the admission (`keep`: a session submission's node and record, or version 0's timing).
/// Written before the admission; read back only by a resumed evaluation. (An intent written before the current
/// budget rule also holds the old rule's `rule`; it is ignored, and the admission decides the current scale's rule.)
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub(super) struct AdmissionIntent {
    pub evaluation: PathBuf,
    pub build: Value,
    pub evidence: Vec<(String, Value)>,
    pub keep: Value,
    pub written_unix_ms: u64,
}

impl AdmissionIntent {
    /// The intent recorded at `path`, if any.
    pub(super) fn read(path: &Path) -> Result<Option<Self>, AdmissionError> {
        if path.is_file() { read_json(path).map(Some).map_err(AdmissionError::tool) } else { Ok(None) }
    }

    pub(super) fn write(&self, path: &Path) -> Result<(), AdmissionError> {
        write_json_atomic(path, self).map_err(AdmissionError::tool)
    }
}

/// What a session submission's intent keeps: the node (its id is the library's version, known after the admission),
/// the record and the parent.
#[derive(serde::Serialize, serde::Deserialize)]
struct SubmissionKeep {
    node: TreeNode,
    record: Value,
    parent: String,
    /// A run of several workloads: every other workload's crate to admit after the primary's (absent elsewhere).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    kept: Vec<MemberKeep>,
}

impl EngineBench<'_> {
    /// The hot calls of every timed cell of the run's development timings (`engine.timed_calls`,
    /// `GeneralInputs::timed_calls`; every workload of a run shares it).
    pub(super) fn timed_calls(&self) -> u32 {
        self.inputs().general.as_ref().map_or(DEFAULT_TIMED_CALLS, |g| g.timed_calls)
    }

    /// The plan every submission is evaluated under (module documentation): the development plan at the run's timed
    /// calls.
    pub(super) fn submission_plan(&self) -> EvaluationPlan {
        development(self.timed_calls())
    }

    // ------------------------------------------------------------------------------------------------ session stages

    /// Prepare a general-line session's workspace once (seeded from its seed version, the branch's notebook carried, a
    /// merge's inputs added; `engine::sessions::seed_session_workspace`), then, on every preparation, the author
    /// contract and the general-line facts.
    pub(super) fn prepare_session(&mut self, request: &RunRequest, workspace: &Path) -> Result<Value, AdmissionError> {
        let config = self.config;
        let session = config.session()?;
        let general = config.inputs.general.as_ref().ok_or_else(|| AdmissionError::tool("a general-line session without general inputs"))?;
        let workspace = self.bench.open_workspace(workspace)?;
        let seed_record = session.directory.join("seed.json");
        let tree = VersionTree::read(&config.engine_dir).map_err(AdmissionError::tool)?;
        let seeded: Value = if seed_record.is_file() {
            read_json(&seed_record).map_err(AdmissionError::tool)?
        } else {
            let mut record = super::sessions::seed_session_workspace(&workspace, &config.engine_dir, &session.record, &tree)?;
            // A run of several workloads: the seed's workload modules, and the seed run's history (a stage run) or the
            // version's families and plans and the root's other sides (`engine::stage`).
            if let Some(stage) = self.stage {
                stage::seed_stage_workspace(&workspace, &config.engine_dir, &session.record.seed, stage.form, &mut record)?;
            }
            records::write_new_json(&seed_record, &record).map_err(AdmissionError::tool)?;
            record
        };
        let label = format!("{} session {} ({:?}), seeded from {}", session.record.branch, session.record.number, session.record.kind, session.record.seed);
        let mut context = self.write_author_contract(request, &workspace, &[], &label)?;
        let spend = session.spend.now().map_err(AdmissionError::tool)?;
        let library = library_bytes(&self.bench.config.library)?;
        let branches = &general.branches;
        let directions: Vec<Value> = branches.iter().map(|b| json!({"branch":b,"head":tree.branch_head(b),"direction":branch_direction(&tree, b)})).collect();
        let fields = context.as_object_mut().ok_or_else(|| AdmissionError::tool("contract facts are not an object"))?;
        // The schema line's prompt (used until the general-line prompt is wired) reads `round` and `engine`.
        fields.insert("round".into(), json!({"number":session.record.number,"seed":{"kind":"version","description":label,"version":session.record.seed},
            "notes":{"file":workspace.join(NOTES_FILE),"from":seeded["notes_from"],"text":seeded["notes_text"]}}));
        fields.insert("engine".into(), json!({"training":config.inputs.training_facts,"versions":[],"rounds":[],"limits":config.inputs.engine_limits,
            "stop_rule":"none: the general line stops only when its budget is used or the user stops it; beating both baselines at a scale is a milestone"}));
        fields.insert("general".into(), json!({
            "line":"general",
            "session":session.record,"seed_record":seed_record,"seeded":seeded,
            "branch":{"name":session.record.branch,"head":tree.branch_head(&session.record.branch),"direction":branch_direction(&tree, &session.record.branch),
                "direction_required":direction_required(branches.len(), session.record.kind, &tree, &session.record.branch)},
            "branches":directions,"main_line_head":tree.main_line_head(),
            "scale":{"name":general.scale.name,"index":general.scale_index,"of":general.scales,"last":general.last_scale(),
                "plain_storage_bytes":general.plain_storage_bytes,"plain_storages":general.plain_storages,
                "original_data_bytes":general.scale.original_data_bytes,"original_data_record":general.scale.original_data_record},
            "budget_rule":crate::prompts::engine_contract::BUDGET_RULE_TEXT,
            "limits":{"call_limit_seconds":general.call_limits.call_limit_ns / 1_000_000_000,"anon_memory_limit_bytes":general.call_limits.anon_memory_limit_bytes,
                "meaning":"framework limits of every engine call, the same for every version: a call over the time or memory limit leaves its cell unfinished"},
            "timed_calls":general.timed_calls,
            "spend":{"spent_usd":spend.spent,"reserved_usd":spend.reserved,"complete":spend.complete,"budget_usd":session.spend.budget,"left_usd":session.spend.budget.remaining_after(spend.spent)},
            "library_bytes":library,
            "storage_assets":crate::storage::asset_release::storage_assets_facts(&self.bench.config.library),
            "files":{"tree":config.engine_dir.join("tree.json"),"tree_markdown":config.engine_dir.join("TREE.md"),"findings":config.engine_dir.join(tree::FINDINGS_MARKDOWN),
                "versions":config.engine_dir.join("versions"),"attempts":config.engine_dir.join("attempts"),"previous_session":session.record.previous}}));
        // The prompt's main direction (`engine.emphasis`), only when the request sets one: a run without it keeps its
        // context as before, and its prompt has no main-direction section.
        if let Some(emphasis) = general.emphasis {
            context["general"]["emphasis"] = json!(emphasis.name());
        }
        // A continued run (`engine.seed_version`): the seed and which templates are new to it, only when set.
        if let Some(seed) = &general.seed {
            let training: Vec<String> = config.inputs.training.templates.iter().map(|t| t.name.clone()).collect();
            context["general"]["seed"] = seed.view(&training);
        }
        context["files"]["versions_records"] = json!(config.engine_dir.join("versions"));
        context["files"]["tree"] = json!(config.engine_dir.join("TREE.md"));
        context["files"]["findings"] = json!(config.engine_dir.join(tree::FINDINGS_MARKDOWN));
        // A stage run: the stage view (the stage fixture) and the seed run's history.
        if let Some(view) = self.stage_view() {
            context["general"]["stage"] = view;
            let history = workspace.join(stage::root::STAGE_ONE_DIRECTORY);
            if history.is_dir() {
                context["files"]["stage1"] = json!(history);
            }
        }
        // A run of several workloads: the workloads view and the combined score (the workloads fixture) and the root's other sides;
        // the one-engine rule only when the request sets it (the prompt states it then).
        if let Some((workloads, combined)) = self.workloads_view() {
            context["general"]["workloads"] = workloads;
            context["general"]["combined_score"] = combined;
            if self.stage.is_some_and(|stage| stage.require_one_engine) {
                context["general"]["require_one_engine"] = json!(true);
            }
            let sides = workspace.join(stage::root::ROOT_SIDES_DIRECTORY);
            if sides.is_dir() {
                context["files"]["root_sides"] = json!(sides);
            }
        }
        Ok(context)
    }

    /// Freeze a general-line submission: the frozen engine, or (an author-side refusal) the refused candidate that its
    /// evaluation records as an attempt. A tool failure stays the controller's freeze error.
    pub(super) fn freeze_session_submission(&mut self, workspace: &Path, frozen_dir: &Path, submission: &CandidateSubmission) -> Result<Value, AdmissionError> {
        match self.freeze_submission(workspace, frozen_dir, submission) {
            // A run of several workloads: every other workload's crate too; a
            // refusal there makes an attempt.
            Ok(frozen) => match self.freeze_side_crates(workspace, frozen_dir, submission)? {
                None => Ok(json!(frozen.engine)),
                Some((workload, error)) => Ok(json!({"kind":REFUSED_CANDIDATE_KIND,"failure_class":error.class,"error":format!("workload {workload}: {error}"),"refused_at":"freeze","workload":workload})),
            },
            Err(error) if error.class == FailureClass::ToolFailure => Err(error),
            Err(error) => {
                // A refusal before the freeze made its directory (a missing or invalid manifest): the directory is made
                // here, so the evaluation records the refusal as an attempt like any other.
                fs::create_dir_all(frozen_dir).map_err(AdmissionError::tool)?;
                Ok(json!({"kind":REFUSED_CANDIDATE_KIND,"failure_class":error.class,"error":error.to_string(),"refused_at":"freeze"}))
            }
        }
    }

    /// The evaluation of a general-line submission (module documentation). Every outcome but a framework failure is
    /// recorded as a version or an attempt; the evaluation names the next call's provider session.
    pub(super) fn evaluate_session_submission(&mut self, dir: &Path, frozen_dir: &Path, candidate: &Value) -> Value {
        let mut steps = StepTimes::default();
        let result = (|| -> Result<Value, AdmissionError> {
            let config = self.config;
            let session = config.session()?;
            let facts = SubmissionFacts::read(&session.directory, frozen_dir)?;
            let context = ProviderContext::of_call(&session.directory, facts.call_id).map_err(AdmissionError::tool)?;
            let verdict = match self.judge(dir, frozen_dir, candidate, &facts, &mut steps) {
                Ok(verdict) => verdict,
                Err(Failure::Framework(error)) => return Err(error),
                // `judge` records the candidate's failures as attempts; one reaching here failed while being recorded.
                Err(Failure::Candidate { reason, .. }) => return Err(AdmissionError::tool(format!("recording the submission failed: {reason}"))),
            };
            let merge_accepted = matches!(verdict, Verdict::Accepted { merge_accepted: true, .. });
            let asked = facts.manifest.as_ref().and_then(|m| m.next_session);
            let general = self.inputs().general.as_ref().ok_or_else(|| AdmissionError::tool("a general-line session without general inputs"))?;
            let tree = VersionTree::read(&config.engine_dir).map_err(AdmissionError::tool)?;
            tree.write_views(&config.engine_dir, &general.branches).map_err(AdmissionError::tool)?;
            // The ladder over the tree after this verdict: a due move ends the session, so that the run can move. A stage
            // run has no ladder.
            let ladder = if self.stage.is_some() { super::branches::LadderDecision::Stay(super::branches::STAGE_LADDER_OFF.into()) } else { ladder_check(general, &tree) };
            let end = session_end(asked, &context, merge_accepted, due_scale_move(general, &ladder));
            let next = next_call(end.as_deref(), &context);
            let (mut evaluation, parts) = match verdict {
                Verdict::Accepted { node, record, merge_accepted, main_line, parts } => (json!({"kind":"verus_engine","eligible":true,"accepted":true,"status":"version_accepted",
                    "claim":accepted_claim(&parts, self.timed_calls()),"node":node.id,"version":node.id,"parents":node.parents,"branch":node.branch,"score":node.score,"directory":node.directory(&config.engine_dir),
                    "version_record":node.directory(&config.engine_dir).join("version.json"),"admission":record["admission"]["admission"],
                    "library_version":record["admission"]["library_version"],"merge_accepted":merge_accepted,"main_line":main_line,"next_call":next}), parts),
                Verdict::Attempt { node, flagged, parts } => (json!({"kind":"verus_engine","eligible":false,"accepted":false,"status":"attempt","node":node.id,
                    "parents":node.parents,"branch":node.branch,"score":node.score,"error":node.reason,"failure_class":"attempt","flagged_for_root":flagged,
                    "directory":node.directory(&config.engine_dir),"next_call":next}), parts),
            };
            // A stage run: the kept workloads' statuses (the stage fixture); a run of several workloads: every workload's
            // status and the combined decision (the workloads fixture); a run with one workload records as before.
            add_parts(&mut evaluation, &parts);
            Ok(evaluation)
        })();
        let mut evaluation = result.unwrap_or_else(|error| json!({"kind":"verus_engine","eligible":false,"status":error.class,"failure_class":error.class,"error":error.to_string()}));
        evaluation["plan"] = self.submission_plan().record();
        evaluation["steps"] = steps.record();
        evaluation
    }


    /// Judge one submission and record it (module documentation, steps 1-7), each step's wall time in `steps`. Only a
    /// framework failure is an `Err`. A verdict recorded by an earlier evaluation of the same frozen submission is
    /// returned as recorded; an admission recorded before an interruption has its records finished, and an admission
    /// intended before one is made once from its intent ([`EngineBench::admit_intended`]): no second admission or timing.
    fn judge(&mut self, dir: &Path, frozen_dir: &Path, candidate: &Value, facts: &SubmissionFacts, steps: &mut StepTimes) -> Result<Verdict, Failure> {
        let config = self.config;
        let engine_dir = &config.engine_dir;
        let session = config.session()?;
        if let Some(verdict) = recorded_verdict(frozen_dir)? {
            return Ok(verdict);
        }
        let admitted_file = frozen_dir.join(ADMITTED_FILE);
        if admitted_file.is_file() {
            let admitted: Value = read_json(&admitted_file).map_err(AdmissionError::tool)?;
            let node: TreeNode = serde_json::from_value(admitted["node"].clone()).map_err(AdmissionError::tool)?;
            let parent = admitted["parent"].as_str().unwrap_or_default().to_string();
            return self.finish_accepted(dir, frozen_dir, facts, node, admitted["record"].clone(), &parent, steps);
        }
        let tree = VersionTree::read(engine_dir).map_err(AdmissionError::tool)?;
        let kind = if session.record.kind == SessionKind::Merge { NodeKind::Merge } else { NodeKind::Branch };
        let node = |accepted: bool, id: String, parent: &str, score: Option<RecordedScore>, reason: Option<String>| TreeNode {
            format_version: 1,
            id,
            accepted,
            kind,
            branch: if kind == NodeKind::Merge { tree::MAIN.to_string() } else { session.record.branch.clone() },
            parents: match (kind, &session.record.merge_from) {
                (NodeKind::Merge, Some(branch_head)) if branch_head != parent => vec![parent.to_string(), branch_head.clone()],
                _ => vec![parent.to_string()],
            },
            scale: session.record.scale.clone(),
            score,
            reason,
            session: Some(session.directory.clone()),
            iteration: Some(facts.iteration),
            direction: facts.manifest.as_ref().and_then(|m| m.direction.clone()),
            rationale: Some(facts.rationale.clone()),
            created_unix_ms: now_unix_ms(),
        };
        let intent_file = frozen_dir.join(ADMITTING_FILE);
        // The evaluation directory whose records (race, checks) the submission's records name: this evaluation's, or the
        // interrupted one's when its intent is resumed.
        let mut evaluation = dir.to_path_buf();
        let (parent, outcome) = match AdmissionIntent::read(&intent_file)? {
            // Steps 1-6 passed before an interruption: admit once from the intent.
            Some(intent) => {
                let keep: SubmissionKeep = serde_json::from_value(intent.keep.clone()).map_err(AdmissionError::tool)?;
                evaluation = intent.evaluation.clone();
                (keep.parent, steps.time("admission", || self.admit_intended(frozen_dir, &intent)))
            }
            None => {
                let parent = self.parent_of(&tree, facts)?;
                let outcome = self.accept(dir, frozen_dir, candidate, facts, &parent, &tree, steps, JudgedFrom::Submission).and_then(|prepared| {
                    let keep = SubmissionKeep { node: node(true, String::new(), &parent.id, Some(prepared.score), None), record: prepared.record, parent: parent.id.clone(), kept: prepared.kept };
                    let intent = AdmissionIntent { evaluation: dir.to_path_buf(), build: prepared.build, evidence: prepared.evidence, keep: json!(keep), written_unix_ms: now_unix_ms() };
                    intent.write(&intent_file)?;
                    steps.time("admission", || self.admit_intended(frozen_dir, &intent))
                });
                (parent.id, outcome)
            }
        };
        match outcome {
            Ok((node, record)) => {
                write_json_atomic(&admitted_file, &json!({"node":node,"record":record,"parent":parent})).map_err(AdmissionError::tool)?;
                self.finish_accepted(dir, frozen_dir, facts, node, record, &parent, steps)
            }
            Err(Failure::Candidate { reason, flagged, score }) => {
                let label = if kind == NodeKind::Merge { tree::MAIN.to_string() } else { session.record.branch.clone() };
                let (id, folder) = take_attempt_directory(engine_dir, &label).map_err(AdmissionError::tool)?;
                let node = node(false, id, &parent, score, Some(reason.clone()));
                let parts = self.parts_of_attempt(&evaluation, candidate);
                self.record_attempt(&evaluation, frozen_dir, candidate, facts, &node, &folder, flagged, &parts)?;
                if flagged {
                    append_flag(engine_dir, &json!({"at_unix_ms":now_unix_ms(),"node":node.id,"kind":"candidate_answer","reason":reason,"evaluation":evaluation})).map_err(AdmissionError::tool)?;
                }
                self.log_finding(&node, &parent, facts, false, Some(&reason), Some(&evaluation), &parts).map_err(Failure::Framework)?;
                let mut recorded = json!({"accepted":false,"node":node,"flagged":flagged});
                add_parts(&mut recorded, &parts);
                write_json_atomic(&frozen_dir.join(RECORDED_FILE), &recorded).map_err(AdmissionError::tool)?;
                Ok(Verdict::Attempt { node, flagged, parts })
            }
            Err(Failure::Framework(error)) => Err(Failure::Framework(error)),
        }
    }

    /// The admission of a session submission from its intent (step 7): admitted once ([`EngineBench::admit_from_intent`]),
    /// its node numbered by the library's version and its record completed with the admission. A refusal at admission
    /// is the candidate's (an attempt).
    fn admit_intended(&mut self, frozen_dir: &Path, intent: &AdmissionIntent) -> Result<(TreeNode, Value), Failure> {
        let engine: FrozenEngine = read_json(&frozen_dir.join("candidate.json")).map_err(AdmissionError::tool)?;
        let keep: SubmissionKeep = serde_json::from_value(intent.keep.clone()).map_err(AdmissionError::tool)?;
        let admission = self.admit_from_intent(frozen_dir, &engine, intent)?;
        let library_version = admission["library_version"].as_u64().ok_or_else(|| AdmissionError::tool("an admission without its library version"))?;
        let mut node = keep.node;
        node.id = version_id(library_version - 1);
        let mut record = keep.record;
        record["admission"] = admission;
        // A run of several workloads: every other crate after the primary's, as the same library version
        // (`engine::stage`). The primary's library has admitted the version, so any failure here is the framework's
        // (flagged), never an attempt.
        let admitted = stage::admit_in_lockstep(library_version, &keep.kept, |other| self.admit_side(other)).map_err(|error| {
            let _ = append_flag(&self.config.engine_dir, &json!({"at_unix_ms":now_unix_ms(),"node":node.id,"kind":"incident","reason":format!("another workload's admission failed after the primary's: {error}")}));
            Failure::Framework(AdmissionError::tool(format!("incident: {error}; flagged for the operator")))
        })?;
        for (keep, (name, admission)) in keep.kept.iter().zip(admitted) {
            let mut kept = keep.record.clone();
            kept["admission"] = admission;
            record["workloads"][name.as_str()] = kept;
        }
        Ok((node, record))
    }

    /// Admit a frozen submission from its recorded intent, once (module documentation): the library's admission of the
    /// same frozen candidate when it holds one (the controller stopped after admitting it, before recording it), else
    /// the admission now. Returns the admission record with `library_version`.
    pub(super) fn admit_from_intent(&mut self, frozen_dir: &Path, engine: &FrozenEngine, intent: &AdmissionIntent) -> Result<Value, AdmissionError> {
        let store = self.bench.store()?;
        if let Some(version) = admitted_version_of(&store, frozen_dir, engine)? {
            return Ok(self.adopted_admission(&version));
        }
        #[cfg(test)]
        crash_point(CRASH_BEFORE_ADMISSION);
        let evidence: Vec<(&str, Value)> = intent.evidence.iter().map(|(kind, record)| (kind.as_str(), record.clone())).collect();
        let record = self.admit(frozen_dir, engine, &intent.build, evidence, &intent.evaluation)?;
        #[cfg(test)]
        crash_point(CRASH_AFTER_ADMISSION);
        Ok(record)
    }

    /// The admission record of an admitted version read back from the library (an admission adopted on resume): every
    /// record id of the admission, its version and uses and the run's rule set; what only the interrupted evaluation
    /// knew is named as not recovered (the storage policy it checked is among the admission's evidence).
    fn adopted_admission(&self, version: &EngineVersion) -> Value {
        let package = &version.package;
        let admission = EngineAdmission {
            admission: version.admission_id,
            version: version.version,
            package: version.package_id,
            build: package.build,
            tcb: package.tcb,
            implementations: package.implementations.clone(),
            storage_uses: package.storage_uses.clone(),
            evidence: version.admission.evidence.clone(),
        };
        let mut record = admission.record();
        record["library_version"] = json!(version.version);
        record["uses"] = json!(package.storage_uses);
        record["rule_set"] = self.inputs().rules.record();
        record["recovered"] = json!({"how":"adopted: the library already held this frozen submission's admission when its evaluation resumed (the controller stopped after the admission, before recording it); it was not admitted again",
            "library_version":version.version,"admission":version.admission_id,"at_unix_ms":now_unix_ms(),
            "not_recovered":"storage_policy_before_registration and registrations of the interrupted evaluation (the storage policy checked at admission is among the admission's evidence)"});
        record
    }

    /// The records of an admitted submission (step 7 after the admission): the version folder, the main-line head
    /// (its decision kept beside the frozen submission, so a resumed evaluation does not time it again), the findings
    /// entry and the recorded verdict. The submission plan profiles nothing ([`EngineBench::submission_plan`]); a plan
    /// with a profile records it with the admission first (never gating; not run again on resume).
    #[allow(clippy::too_many_arguments)]
    fn finish_accepted(&mut self, dir: &Path, frozen_dir: &Path, facts: &SubmissionFacts, node: TreeNode, mut record: Value, parent: &str, steps: &mut StepTimes) -> Result<Verdict, Failure> {
        if record["profile"].is_null() && !node_directory(&self.config.engine_dir, &node.id, true).join(tree::NODE_FILE).is_file() {
            let plan = self.submission_plan();
            record["profile"] = if plan.profile {
                steps.time("profile", || self.profile_admitted(&node, &record, dir))
            } else {
                json!({"status":"not_run","plan":plan.name,
                    "reason":"the development evaluation profiles nothing after an admission: the profile tool profiles on request, and the final evaluation (gendb engine final-evaluation) profiles the version"})
            };
            write_json_atomic(&frozen_dir.join(ADMITTED_FILE), &json!({"node":node,"record":record,"parent":parent})).map_err(AdmissionError::tool)?;
        }
        // The measured effect is the race of the evaluation that judged it: the evaluation record names its race file,
        // which is an earlier evaluation's when this one resumed an admission (adopted, or admitted from its intent).
        // `record_version` returns the version record, which keeps that file only under `times`.
        let judged_in = record["race"].as_str().and_then(|race| Path::new(race).parent()).map_or_else(|| dir.to_path_buf(), Path::to_path_buf);
        let parts = parts_of_record(&record);
        let effects = stage_effects(&record);
        // A run of several workloads decided by the combined score (or the one-engine rule's transition), which also
        // decides the main line.
        let combined = stage::one_engine::CombinedVerdict::of_record(&record["combined"]);
        let record = steps.time("records", || self.record_version(frozen_dir, facts, &node, record))?;
        let merge_accepted = node.kind == NodeKind::Merge;
        let main_line_file = frozen_dir.join(MAIN_LINE_DECISION_FILE);
        let main_line = if main_line_file.is_file() {
            read_json(&main_line_file).map_err(AdmissionError::tool)?
        } else {
            let decided = steps.time("main_line", || self.update_main_line(&node, dir, merge_accepted, combined)).map_err(Failure::Framework)?;
            write_json_atomic(&main_line_file, &decided).map_err(AdmissionError::tool)?;
            decided
        };
        self.log_finding(&node, parent, facts, true, None, Some(&judged_in), &effects).map_err(Failure::Framework)?;
        // The verdict keeps the parts of a run of several workloads with the record (`recorded_verdict` reads them there).
        let mut recorded_record = record.clone();
        add_parts(&mut recorded_record, &parts);
        write_json_atomic(&frozen_dir.join(RECORDED_FILE), &json!({"accepted":true,"node":node,"record":recorded_record,"merge_accepted":merge_accepted,"main_line":main_line}))
            .map_err(AdmissionError::tool)?;
        // The run library's superseded derived storage assets, released once the heads are decided; here only when this
        // evaluation is the only one (one branch; `engine::asset_upkeep`). Never gating. A stage run releases them in
        // every workload's library.
        if self.inputs().general.as_ref().is_some_and(|g| g.branches.len() == 1) {
            let why = format!("admission of {}", node.id);
            match self.stage {
                None => {
                    super::asset_upkeep::release_pass(&self.bench.config.library, &self.config.engine_dir, &why);
                }
                Some(stage) => {
                    super::asset_upkeep::release_workload_pass(&self.bench.config.library, &self.config.engine_dir, &why, &stage.workload);
                    for side in &stage.sides {
                        super::asset_upkeep::release_workload_pass(&side.view.library, &self.config.engine_dir, &why, &side.name);
                    }
                }
            }
        }
        Ok(Verdict::Accepted { node, record, merge_accepted, main_line, parts })
    }

    /// The re-evaluation of the recorded attempt `plan` into `dir` (`engine::re_evaluation`; module documentation): its
    /// development evaluation again with its recorded build and race ([`JudgedFrom::RecordedAttempt`]), and, when it is
    /// now better, its admission and every record of an acceptance ([`EngineBench::finish_accepted`]: the version
    /// folder, the main-line head, the findings entry and the verdict beside the frozen submission). Resumable like a
    /// submission's evaluation: an admission intended or made by an interrupted re-evaluation is finished, never made
    /// twice; an attempt already admitted by a re-evaluation is returned as recorded. Only a framework failure is an
    /// `Err`.
    pub(super) fn re_evaluate_attempt(&mut self, dir: &Path, plan: &ReEvaluationPlan, steps: &mut StepTimes) -> Result<ReEvaluated, AdmissionError> {
        let session = self.config.session()?;
        let frozen_dir = plan.frozen_dir.as_path();
        let facts = SubmissionFacts::read(&session.directory, frozen_dir)?;
        let parent = plan.parent.clone();
        if let Some(Verdict::Accepted { node, main_line, .. }) = recorded_verdict(frozen_dir).map_err(framework_only)? {
            return Ok(ReEvaluated::Admitted { node, main_line, already: true });
        }
        let admitted_file = frozen_dir.join(ADMITTED_FILE);
        let intent_file = frozen_dir.join(ADMITTING_FILE);
        let outcome = if admitted_file.is_file() {
            let admitted: Value = read_json(&admitted_file).map_err(AdmissionError::tool)?;
            let node: TreeNode = serde_json::from_value(admitted["node"].clone()).map_err(AdmissionError::tool)?;
            Ok((node, admitted["record"].clone()))
        } else if let Some(intent) = AdmissionIntent::read(&intent_file)? {
            steps.time("admission", || self.admit_intended(frozen_dir, &intent))
        } else {
            let tree = VersionTree::read(&self.config.engine_dir).map_err(AdmissionError::tool)?;
            let candidate: Value = read_json(&frozen_dir.join("candidate.json")).map_err(AdmissionError::tool)?;
            let chosen = Parent { id: parent.clone(), chosen: "the parent of its first evaluation, still a head (re-evaluation)" };
            let from = JudgedFrom::RecordedAttempt { build: &plan.build, race: &plan.race };
            self.accept(dir, frozen_dir, &candidate, &facts, &chosen, &tree, steps, from).and_then(|prepared| {
                let node = TreeNode { accepted: true, id: String::new(), score: Some(prepared.score), reason: None, created_unix_ms: now_unix_ms(), ..plan.node.clone() };
                let mut record = prepared.record;
                record["re_evaluation"] = plan.record(dir);
                let keep = SubmissionKeep { node, record, parent: parent.clone(), kept: prepared.kept };
                let intent = AdmissionIntent { evaluation: dir.to_path_buf(), build: prepared.build, evidence: prepared.evidence, keep: json!(keep), written_unix_ms: now_unix_ms() };
                intent.write(&intent_file)?;
                steps.time("admission", || self.admit_intended(frozen_dir, &intent))
            })
        };
        match outcome {
            Ok((node, record)) => {
                write_json_atomic(&admitted_file, &json!({"node":node,"record":record,"parent":parent})).map_err(AdmissionError::tool)?;
                match self.finish_accepted(dir, frozen_dir, &facts, node, record, &parent, steps).map_err(framework_only)? {
                    Verdict::Accepted { node, main_line, .. } => Ok(ReEvaluated::Admitted { node, main_line, already: false }),
                    Verdict::Attempt { .. } => Err(AdmissionError::tool("an admitted re-evaluation was recorded as an attempt")),
                }
            }
            Err(Failure::Candidate { reason, flagged, score }) => {
                if flagged {
                    append_flag(&self.config.engine_dir, &json!({"at_unix_ms":now_unix_ms(),"node":plan.attempt,"kind":"candidate_answer","reason":reason,"evaluation":dir,"re_evaluation":true}))
                        .map_err(AdmissionError::tool)?;
                }
                Ok(ReEvaluated::NotAdmitted { reason, flagged, score })
            }
            Err(Failure::Framework(error)) => Err(error),
        }
    }

    /// The parent of a submission: a merge session's is the main-line head; a branch session's is the branch head, or
    /// the main-line head when the manifest asks for it (`base: main_line_head`).
    fn parent_of(&self, tree: &VersionTree, facts: &SubmissionFacts) -> Result<Parent, AdmissionError> {
        let session = self.config.session()?;
        let main = tree.main_line_head().ok_or_else(|| AdmissionError::tool("the main line has no head (version 0 is not prepared)"))?;
        let base = facts.manifest.as_ref().and_then(|m| m.base);
        Ok(match (session.record.kind, base) {
            (SessionKind::Merge, _) => Parent { id: main.to_string(), chosen: "the main-line head (merge session)" },
            (SessionKind::Branch, Some(SubmissionBase::MainLineHead)) => Parent { id: main.to_string(), chosen: "the main-line head (base: main_line_head)" },
            (SessionKind::Branch, _) => Parent {
                id: tree.branch_head(&session.record.branch).ok_or_else(|| AdmissionError::tool("the branch has no head"))?.to_string(),
                chosen: "the branch head",
            },
        })
    }

    /// Steps 1-6 and the admission's inputs (module documentation): the score, the record and what the admission needs.
    /// `from` says where the build and the timing come from (a submission's own, or a recorded attempt's).
    #[allow(clippy::too_many_arguments)]
    fn accept(&mut self, dir: &Path, frozen_dir: &Path, candidate: &Value, facts: &SubmissionFacts, parent: &Parent, tree: &VersionTree, steps: &mut StepTimes, from: JudgedFrom<'_>) -> Result<Prepared, Failure> {
        // A run of several workloads has its own order over every workload (`engine::stage::members`).
        if let Some(stage) = self.stage.filter(|s| s.is_members()) {
            return self.accept_members(stage, dir, frozen_dir, candidate, facts, parent, tree, steps, from);
        }
        let config = self.config;
        let session = config.session()?;
        let inputs = config.inputs.clone();
        let general = inputs.general.as_ref().ok_or_else(|| AdmissionError::tool("a general-line session without general inputs"))?;
        // 1. Freeze and scans (refused at freeze: the controller's candidate says so).
        if candidate["kind"] == REFUSED_CANDIDATE_KIND {
            return Err(Failure::Candidate { reason: candidate["error"].as_str().unwrap_or("refused at freeze").to_string(), flagged: false, score: None });
        }
        let engine: FrozenEngine = serde_json::from_value(candidate.clone()).map_err(AdmissionError::tool)?;
        // A stage run's crates are evaluated by its sessions only, with every kept workload (module documentation).
        if engine.workload.is_some() != self.stage.is_some() {
            return Err(Failure::Framework(AdmissionError::tool(
                "a stage run's crate is evaluated only by a session of its stage run (with its kept workloads); a re-evaluation of a stage attempt is not supported",
            )));
        }
        self.check_direction(facts, tree)?;
        // 2. The whole-crate Verus run and compile (a recorded attempt's: its first evaluation's run, read back).
        let locks = self.bench.config.locks.clone();
        let build = match from {
            JudgedFrom::Submission => steps.time("verus", || self.builds.compile(&locks, &engine, frozen_dir, &dir.join("verus-build"), true))?,
            JudgedFrom::RecordedAttempt { build, .. } => steps.time("verus_recorded", || self.builds.recorded(&engine, frozen_dir, build))?,
        };
        // 3. Storages, the storage policy and the budget rule (plain storage only as is; changed storage within the
        // original data size at this scale); the parent's admitted storages.
        let rule = self.budget_rule()?;
        let (storages, storage_policy, parent_run) = steps.time("storages", || -> Result<_, Failure> {
            let storages = self.storages(&engine, frozen_dir, dir, TrialVerification::WholeCrate)?;
            let storage_policy = self.check_storage_policy(&engine, frozen_dir, &storages, &rule)?;
            let parent_run = self.admitted_runnable(&parent.id, &dir.join("parent-storages")).map_err(Failure::Framework)?;
            Ok((storages, storage_policy, parent_run))
        })?;
        let store = self.bench.store()?;
        // 4. The interleaved timing against the parent, under the submission plan.
        let candidate_run = Runnable { label: format!("{} iteration {}", session.record.branch, facts.iteration), library: build.library.clone(), inputs: storage_inputs(&storages) };
        let parent_record = recorded_cells(&config.engine_dir, &parent.id, &general.scale.name);
        let plan = self.submission_plan();
        let raced = steps.time("interleaved_timing", || match from {
            JudgedFrom::Submission => self.race_runnables(&parent_run, &candidate_run, parent_record.as_deref(), plan.cell_calls, &dir.join("race")),
            JudgedFrom::RecordedAttempt { race, .. } => RecordedRace::read(race)
                .map_err(|e| RaceError::Score(ScoreError(format!("the attempt's recorded race: {e}"))))
                .and_then(|recorded| self.retime_runnables(&parent_run, &candidate_run, parent_record.as_deref(), plan.cell_calls, recorded, &dir.join("race"))),
        });
        let report = match raced {
            Ok(report) => report,
            Err(error) => return Err(race_failure(&config.engine_dir, &parent.id, error)),
        };
        let race_file = dir.join("race.json");
        write_json_atomic(&race_file, &json!(report)).map_err(AdmissionError::tool)?;
        let candidate_score = RecordedScore::of(&general.scale.name, &report.candidate_score, &race_file);
        // 5. The score decision.
        if !report.candidate_better {
            let (p, c) = (&report.parent_score.score, &report.candidate_score.score);
            let retimed = match report.retimed_pairs {
                0 => String::new(),
                n => format!("; {n} pair(s) timed again because a side was much slower than the parent's recorded time (race.json, `retimed`)"),
            };
            return Err(Failure::Candidate {
                reason: format!("{NOT_BETTER_REASON} {} ({}) in one interleaved timing: finished cells {} vs {}, normalized time {} vs {} (parent first){retimed}",
                    parent.id, parent.chosen, p.finished, c.finished, p.normalized_time, c.normalized_time),
                flagged: false,
                score: Some(candidate_score),
            });
        }
        // 6. The finished templates' checks under the submission plan: the variants' answers at the ladder's first scale.
        let subject = CheckedEngine { library: &build.library, inputs: &candidate_run.inputs, frozen: Some((&engine.storage_uses, frozen_dir)) };
        let checks = steps.time("variants", || self.check_finished_templates(&plan, &subject, &report.candidate_score, dir)).map_err(|f| match f {
            Failure::Candidate { reason, flagged, .. } => Failure::Candidate { reason, flagged, score: Some(candidate_score.clone()) },
            other => other,
        })?;
        let lineage_of = self.lineage_of()?;
        // 6b. A stage run: every kept workload in its library (`engine::stage`). Recorded and
        // shown, never deciding; a refusal there is an attempt with the goal's score.
        let kept = match self.stage {
            Some(stage) if !stage.sides.is_empty() => {
                let names: Vec<String> = stage.sides.iter().map(|k| k.name.clone()).collect();
                stage::evaluate_kept_workloads(&names, dir, |name| {
                    let side = stage.side(name).ok_or_else(|| Failure::Framework(AdmissionError::tool(format!("{name} is not a kept workload of this run"))))?;
                    self.evaluate_kept_side(side, frozen_dir, dir, parent, &lineage_of, tree, steps).map_err(|failure| failure.of_kept(name, &candidate_score))
                })?
            }
            _ => vec![],
        };
        // 7. The admission's inputs: the lineage, the race summary and the checks as evidence.
        let lineage = VerusEngineLineageV1 {
            branch: lineage_of.branch.clone(),
            kind: lineage_of.kind.clone(),
            parents: lineage_parents(tree, &store, parent, lineage_of.merge_from.as_deref(), lineage_of.session_kind)?,
        };
        let race_summary = float_free(&race_summary(&report, &race_file));
        let evidence = vec![(VERUS_ENGINE_LINEAGE_KIND.to_string(), json!(lineage)), (ENGINE_RACE_KIND.to_string(), race_summary.clone()),
            (ENGINE_FINISHED_CHECKS_KIND.to_string(), float_free(&checks))];
        let mut record = json!({"race":race_file,"race_summary":race_summary,"finished_checks":checks,"storage_policy_at_evaluation":storage_policy,
            "storage":{"assets":storages.iter().map(storage_view).collect::<Vec<_>>(),"budget_rule":rule},
            "build":build.record,"crate_version":engine_version_id(&engine, frozen_dir)?,"parent":parent.id,"parent_chosen":parent.chosen,
            "candidate_cells":report.candidate_score.cells.iter().map(|c| CellResult { template: c.template.clone(), workers: c.workers, status: c.status }).collect::<Vec<_>>()});
        if self.stage.is_some() {
            record["kept_workloads"] = self.kept_workloads_of(dir);
        }
        Ok(Prepared { score: candidate_score, record, build: build.record, evidence, kept })
    }

    /// [`EngineBench::accept`] of a run of several workloads (module documentation; `engine::stage::members`): the order
    /// over every workload, each workload's status in `members.json`, the combined decision in `combined.json`; the
    /// record of an accepted submission carries `members` and `combined`, and every other workload's admission inputs.
    /// A failure after the primary's timing keeps the primary's score (the attempt's node score). Only a submission's own
    /// evaluation runs here (a re-evaluation of such an attempt is not supported).
    #[allow(clippy::too_many_arguments)]
    fn accept_members(&mut self, stage: &stage::StageRole, dir: &Path, frozen_dir: &Path, candidate: &Value, facts: &SubmissionFacts, parent: &Parent, tree: &VersionTree, steps: &mut StepTimes,
        from: JudgedFrom<'_>) -> Result<Prepared, Failure> {
        let session = self.config.session()?;
        let members = stage.members();
        let mut statuses = MemberStatuses::start(dir, &members)?;
        // 1. Freeze and scans: the refused crate names its workload (the primary's when none).
        if candidate["kind"] == REFUSED_CANDIDATE_KIND {
            let reason = candidate["error"].as_str().unwrap_or("refused at freeze").to_string();
            statuses.refused(candidate["workload"].as_str().unwrap_or(&stage.workload), "freeze", &reason)?;
            return Err(Failure::Candidate { reason, flagged: false, score: None });
        }
        if !matches!(from, JudgedFrom::Submission) {
            return Err(Failure::Framework(AdmissionError::tool("a run of several workloads evaluates a submission once; a re-evaluation of its attempt is not supported")));
        }
        let engine: FrozenEngine = serde_json::from_value(candidate.clone()).map_err(AdmissionError::tool)?;
        if engine.workload.is_none() {
            return Err(Failure::Framework(AdmissionError::tool("a run of several workloads' submission without its workload crate")));
        }
        self.check_direction(facts, tree)?;
        let lineage_of = self.lineage_of()?;
        let label = format!("{} iteration {}", session.record.branch, facts.iteration);
        let engine_dir = self.config.engine_dir.clone();
        let mut work = stage::members::BenchSteps::new(self, stage, engine, frozen_dir, dir, parent, steps, label)?;
        // The request's one-engine rule (`engine.workloads.require_one_engine`), over the frozen crates and the parent.
        let one_engine = match stage.require_one_engine {
            true => Some(stage::one_engine::OneEngineRule::of(&work.member_records(), &engine_dir, &parent.id)?),
            false => None,
        };
        let decided = stage::members::evaluate_members(&members, &mut work, &mut statuses, parent, dir, one_engine.as_ref());
        let combined = match decided {
            Ok(combined) => combined,
            Err(Failure::Candidate { reason, flagged, score }) => return Err(Failure::Candidate { reason, flagged, score: score.or_else(|| work.primary_score()) }),
            Err(framework) => return Err(framework),
        };
        let finished = work.finish(&lineage_of, tree)?;
        let mut record = finished.record;
        record["members"] = json!(statuses.statuses());
        record["combined"] = combined;
        Ok(Prepared { score: finished.score, record, build: finished.build, evidence: finished.evidence, kept: finished.others })
    }

    /// A branch's first submission states its direction when several branches search at once (refused otherwise).
    fn check_direction(&self, facts: &SubmissionFacts, tree: &VersionTree) -> Result<(), Failure> {
        let session = self.config.session()?;
        let branches = self.inputs().general.as_ref().map_or(1, |g| g.branches.len());
        if direction_required(branches, session.record.kind, tree, &session.record.branch) && facts.manifest.as_ref().and_then(|m| m.direction.as_ref()).is_none() {
            return Err(Failure::Candidate {
                reason: "refusal: branch_direction_required: a branch's first submission states its direction (verus-engine.json `direction`: the areas it explores, how it differs from the other branches, what it expects to gain)".into(),
                flagged: false,
                score: None,
            });
        }
        Ok(())
    }

    /// The lineage of this session's submissions in every library: its branch (a merge's is `main`), kind and parents.
    fn lineage_of(&self) -> Result<LineageOf, AdmissionError> {
        let session = self.config.session()?;
        let merge = session.record.kind == SessionKind::Merge;
        Ok(LineageOf {
            branch: if merge { tree::MAIN.to_string() } else { session.record.branch.clone() },
            kind: if merge { "merge".into() } else { "branch".into() },
            merge_from: session.record.merge_from.clone(),
            session_kind: session.record.kind,
        })
    }

    /// [`EngineBench::check_finished_templates`] with any failure as its text (version 0's checks and the final
    /// evaluation's, which are the framework's).
    pub(super) fn finished_checks(&mut self, plan: &EvaluationPlan, subject: &CheckedEngine<'_>, scored: &ScaleScore, dir: &Path) -> Result<Value, String> {
        self.check_finished_templates(plan, subject, scored, dir).map_err(|failure| match failure {
            Failure::Candidate { reason, .. } => reason,
            Failure::Framework(error) => error.to_string(),
        })
    }

    /// The checks of the templates not unfinished in `scored` (the engine's timing at the current scale) under `plan`
    /// (step 6; `engine::protocol`): the qualification at every visible binding when the plan has it, and the variants
    /// as the plan runs them ([`selected_variants`]: at the first scale every one, at the evaluated scale those of the
    /// templates finished at every worker count). A wrong answer refuses the candidate
    /// (flagged); an unfinished call is recorded, never refused; a variant whose answer was not compared with its
    /// template's saved answers refuses it.
    pub(super) fn check_finished_templates(&mut self, plan: &EvaluationPlan, subject: &CheckedEngine<'_>, scored: &ScaleScore, dir: &Path) -> Result<Value, Failure> {
        let all = self.config.inputs.clone();
        let finished = finished_templates(scored, &all.workers);
        let mut skipped: Vec<SkippedTemplate> = vec![];
        for cell in &scored.cells {
            if let CellStatus::Unfinished { reason } = cell.status
                && !skipped.iter().any(|s| s.template == cell.template)
            {
                skipped.push(SkippedTemplate { template: cell.template.clone(), workers: cell.workers, reason });
            }
        }
        let qualification = if !plan.qualification {
            json!({"status":"not_run","plan":plan.name,"reason":"the development evaluation has no qualification at the other visible bindings; the final evaluation (gendb engine final-evaluation) runs it"})
        } else if all.training.other_bindings().is_empty() {
            json!({"status":"not_run","reason":"the scale has no visible binding besides the timing binding, where the timing compared every answer"})
        } else {
            let _lease = self.bench.config.locks.timing().map_err(AdmissionError::tool)?;
            qualify_finished_templates(&self.runner(subject.library, subject.inputs), &all.checks.templates, &skipped, &dir.join("qualification")).map_err(|e| answer_failure(e, "qualification"))?
        };
        let variants = match plan.variants {
            VariantRun::TimedAtScale => self.timed_variants(subject, &finished, dir)?,
            VariantRun::AnswersAtFirstScale => self.variant_answers(subject, &finished, dir)?,
        };
        let skipped: Vec<Value> = skipped.iter().map(|s| json!({"template":s.template,"workers":s.workers,"reason":s.reason})).collect();
        Ok(json!({"plan":plan.record(),"finished_templates":finished,"skipped_templates":skipped,
            "skip_rule":"a template with an unfinished cell at the timing binding is not qualified; at the evaluated scale the variants of a template not finished at every worker count are not run (a call there would only reach the limit); at the first scale every variant runs",
            "qualification":qualification,"qualification_bindings":if plan.qualification { all.training.other_bindings() } else { vec![] },"variants":variants}))
    }

    /// The variants of the `finished` templates timed at the current scale (the final plan; version 0): 1 warm + 1 hot
    /// call each at 64 workers, every failing cell recorded, then judged: a tool failure is the framework's, a refused
    /// answer or an uncompared one refuses the candidate (flagged). Returns the matrix's compact view (`file`: the
    /// matrix) with its count of unfinished cells.
    fn timed_variants(&self, subject: &CheckedEngine<'_>, finished: &BTreeSet<String>, dir: &Path) -> Result<Value, Failure> {
        let all = self.inputs();
        let variants = selected_variants(VariantRun::TimedAtScale, &all.statements.variants, finished);
        let cells = EngineCells { runner: self.runner(subject.library, subject.inputs), checks: &all.checks, adhoc: &[], bound: None };
        let locks = self.bench.config.locks.clone();
        let matrix = run_matrix_recording_failures(&cells, MatrixKind::Variants, &variants, &[VariantRun::TimedAtScale.workers()], &dir.join("variants"), || locks.timing())
            .map_err(|e| answer_failure(e, "variants"))?;
        if let Some(failed) = matrix.failed.iter().find(|f| f.class == FailureClass::ToolFailure.name()) {
            return Err(Failure::Framework(AdmissionError::tool(format!("variant {} at {} workers: {}", failed.variant.as_ref().map_or("-", |v| v.id.as_str()), failed.workers, failed.error))));
        }
        if let Some(failed) = matrix.failed.first() {
            return Err(Failure::Candidate {
                reason: format!("refusal: a variant's answer was refused: {} at {} workers ({}: {})", failed.variant.as_ref().map_or("-", |v| v.id.as_str()), failed.workers, failed.class, failed.error),
                flagged: true,
                score: None,
            });
        }
        if let Some(cell) = matrix.unchecked_cells().first() {
            return Err(Failure::Candidate { reason: format!("refusal: variant {} at {} workers was not checked against its template's saved answers ({})", cell.variant.as_ref().map_or("-", |v| v.id.as_str()), cell.workers, cell.status), flagged: true, score: None });
        }
        let mut view = write_matrix(&matrix, &dir.join("variant-matrix.json"))?;
        view["unfinished_cells"] = json!(matrix.unfinished.len());
        Ok(view)
    }

    /// The answers of every variant with AST bytes of its own at the ladder's first scale (the development plan;
    /// [`selected_variants`], `finished` not narrowing it): one call each at 64 workers, no time read. At the first scale the engine runs over `subject`'s storages; at a later scale
    /// over its storages resolved at the first scale's capture ([`EngineBench::first_scale_uses`]). A tool failure is
    /// the framework's; a refused answer, or a finished call whose answer was not compared with its template's saved
    /// answers, refuses the candidate (flagged); an unfinished call is recorded. Writes `variant-answers.json`.
    pub(super) fn variant_answers(&mut self, subject: &CheckedEngine<'_>, finished: &BTreeSet<String>, dir: &Path) -> Result<Value, Failure> {
        let general = self.inputs().general.clone().ok_or_else(|| AdmissionError::tool("variants at the first scale without general inputs"))?;
        let at_first_scale = VariantRun::AnswersAtFirstScale.scale_index(general.scale_index) == general.scale_index;
        let (inputs, uses) =
            if at_first_scale { (self.config.inputs.clone(), subject.inputs.to_vec()) } else { self.first_scale_uses(subject, &dir.join("first-scale-storages"))? };
        let scale = inputs.general.as_ref().map_or_else(|| general.scale.name.clone(), |g| g.scale.name.clone());
        let workers = VariantRun::AnswersAtFirstScale.workers();
        let variants = selected_variants(VariantRun::AnswersAtFirstScale, &inputs.statements.variants, finished);
        let runner = EngineRunner {
            runner: &inputs.sessions.first().ok_or_else(|| AdmissionError::tool("the first scale's inputs have no prepared template"))?.1.runner,
            library: subject.library,
            uses: &uses,
            access: inputs.part_access,
            limits: Some(general.call_limits),
            answer_bound: Some(AnswerBound::STORED),
        };
        let cells = EngineCells { runner, checks: &inputs.checks, adhoc: &[], bound: None };
        let locks = self.bench.config.locks.clone();
        let answers = check_answers(&cells, &variants, workers, &dir.join("variants"), || locks.timing()).map_err(|e| answer_failure(e, &format!("a variant's answer at {scale}")))?;
        if let Some(cell) = answers.iter().find(|c| c.unfinished.is_none() && !c.checked) {
            return Err(Failure::Candidate {
                reason: format!("refusal: variant {} at {scale}, {workers} workers, was not checked against its template's saved answers ({})", cell.variant.as_ref().map_or("-", |v| v.id.as_str()), cell.status),
                flagged: true,
                score: None,
            });
        }
        let file = dir.join("variant-answers.json");
        write_json_atomic(&file, &json!(answers)).map_err(AdmissionError::tool)?;
        let unfinished: Vec<Value> = answers.iter().filter_map(|c| c.unfinished.map(|reason| json!({"variant":c.variant.as_ref().map(|v| &v.id),"reason":reason}))).collect();
        Ok(json!({"run":VariantRun::AnswersAtFirstScale,"scale":scale,"workers":workers,"calls_per_variant":VariantRun::AnswersAtFirstScale.calls(),"file":file,
            "variants":answers.len(),"agreed":answers.iter().filter(|c| c.checked).count(),"unfinished":unfinished,
            "not_run":inputs.statements.record["variants"]["not_timed"],
            "meaning":"each variant's answer at the first scale of the ladder, one call, compared with its template's saved answers there; no time is read"}))
    }

    /// The candidate's storages resolved at the ladder's first scale (a session at a later scale): the session's bench
    /// views the first scale's capture for the resolution ([`crate::tools::bench::Workbench::at_capture`]), so a
    /// workspace storage it checked is built there by its verified builder and an admitted storage's asset is found or
    /// built as at a scale move. Returns the first scale's inputs and the storage inputs there.
    fn first_scale_uses(&mut self, subject: &CheckedEngine<'_>, out: &Path) -> Result<(std::sync::Arc<super::role::EngineInputs>, Vec<StorageUseInput>), Failure> {
        let first = self.first_scale().ok_or_else(|| AdmissionError::tool("an evaluation at a later scale without the first scale's inputs (the run prepares them)"))?;
        let (uses, frozen_dir) = subject.frozen.ok_or_else(|| AdmissionError::tool("the variants at the first scale need the candidate's frozen storage uses"))?;
        let statements = first.inputs.sessions.iter().map(|(_, s)| s.clone()).collect();
        let storages = self.bench.at_capture(first.capture.clone(), statements, |bench| bench.resolve_uses_as(uses, frozen_dir, out, TrialVerification::WholeCrate))?;
        Ok((first.inputs, storage_inputs(&storages)))
    }

    /// Register the candidate's new storages and admit it (step 7), under the library's budget lock: the storage policy
    /// of its uses with the new storages, their registration, and the admission with `evidence` under `rule` and the
    /// general line's rules. Returns the admission record with `library_version`.
    ///
    /// Resumable (module documentation): a workspace storage that this admission registered before an interruption
    /// (its registration names this frozen submission) is used as the admitted package it now is, never registered
    /// again ([`registered_by_admission`]); each attempt writes its evidence into a fresh `admission[-N]` directory of
    /// the evaluation.
    fn admit(&mut self, frozen_dir: &Path, engine: &FrozenEngine, build: &Value, evidence: Vec<(&str, Value)>, dir: &Path) -> Result<Value, AdmissionError> {
        let work = fresh_directory(dir, "admission")?;
        let registered_by = json!({"role":AuthorRole::Engine,"session":self.bench.session_root()?,"admission":frozen_dir});
        let store = self.bench.store()?;
        let earlier = registered_by_admission(&store, &engine.storage_uses, &registered_by)?;
        let storage_uses: Vec<FrozenUse> = engine
            .storage_uses
            .iter()
            .map(|u| match earlier.iter().find(|r| r.name == u.name) {
                Some(registered) => FrozenUse { source: StorageSource::Admitted { package: registered.package }, ..u.clone() },
                None => u.clone(),
            })
            .collect();
        let mut checked = self.bench.check_workspace_uses(&storage_uses, frozen_dir, &work)?;
        let verus_run: Value = read_json(Path::new(build["record"].as_str().unwrap_or_default())).map_err(AdmissionError::tool)?;
        let items: Vec<Value> = build["items"].as_array().cloned().unwrap_or_default();
        let inputs = self.config.inputs.clone();
        let rule = &self.budget_rule()?;
        let statement = inputs.sessions[0].1.statement();
        let schema = EngineSchema { tables: &statement.instance.doc.tables, ddl: &statement.schema_ddl, frontend: &statement.instance.doc.frontend };
        let capture = CurrentCapture::of(&self.bench.capture.current()).map_err(AdmissionError::tool)?;
        let policy = self.bench.config.storage_policy.clone();
        let lock = LibraryLock::acquire(&store, BUDGET_LOCK)?;
        let workspace_indices: Vec<usize> = checked.workspace.iter().map(|(index, _, _)| *index).collect();
        let admitted_uses: Vec<VerusStorageUseV1> = checked.uses.iter().enumerate().filter(|(i, _)| !workspace_indices.contains(i)).map(|(_, (name, package, _))| VerusStorageUseV1 { name: name.clone(), package: *package }).collect();
        let holders: Vec<PayloadHolder> = checked.workspace.iter().map(|(_, c, f)| PayloadHolder::of_manifest(&f.manifest, Some(c.package))).collect::<Result<_, _>>()?;
        let new: Vec<NewEngineStorage<'_>> = holders.iter().zip(&checked.workspace).map(|(holder, (_, c, _))| NewEngineStorage { holder: holder.clone(), asset_directory: &c.asset_directory }).collect();
        let before_registration = check_engine_storage_uses(&store, &capture, self.schema(), &policy, rule, &admitted_uses, &new)?;
        drop(new);
        let registrations = self.bench.register_checked(&store, &lock, checked.workspace.iter_mut().map(|(_, c, f)| (c, &*f)).collect(), &registered_by, &policy.standing())?;
        #[cfg(test)]
        crash_point(CRASH_AFTER_STORAGE_REGISTRATION);
        let registered = checked.registered(registrations);
        let uses: Vec<VerusStorageUseV1> = registered.iter().map(|(name, package, _)| VerusStorageUseV1 { name: name.clone(), package: *package }).collect();
        // This session's builds of these storages at other captures (a later scale's variants at the first scale) are
        // their assets there now (`query::assets::TrialAssets::promote_admitted`). Never gating.
        let trials_promoted = self.bench.promote_session_trials(&store, &uses.iter().map(|u| u.package).collect()).unwrap_or_else(|e| json!({"error":e.to_string()}));
        let (_, assets) = engine_assets(&store, &uses, &capture)?;
        let candidate = EngineCandidate {
            frozen_root: &frozen_dir.join("crate"),
            verus_run: &verus_run,
            uses: uses.clone(),
            generation_identity: GENERATION_IDENTITY,
            constants: inputs.rules.constants(),
            modules: agent_modules(&engine.agent_modules(), &items),
            evidence,
            assets,
        };
        let admitted = match self.stage {
            Some(_) => admit_stage_version(&lock, &store, &capture, &policy, rule, schema, candidate, &inputs.rules)?,
            None => admit_engine_version_on_line(&lock, &store, &capture, &policy, rule, EngineLine::General, schema, candidate)?,
        };
        drop(lock);
        let mut record = admitted.record();
        record["library_version"] = json!(admitted.version);
        record["uses"] = json!(uses);
        record["storage_policy_before_registration"] = before_registration;
        record["registrations"] = json!(registered.iter().filter_map(|(_, _, r)| r.as_ref().map(|r| json!(r))).collect::<Vec<_>>());
        if !earlier.is_empty() {
            record["registrations_reused"] = json!({"storages":earlier,
                "meaning":"registered by an earlier attempt of this admission, which stopped before the engine was admitted; used as admitted, not registered again (the storage policy above was checked with them already admitted)"});
        }
        record["rule_set"] = inputs.rules.record();
        record["trials_promoted"] = trials_promoted;
        Ok(record)
    }

    // ------------------------------------------------------------------------------------------------ versions and races

    /// The profile of a timed version (`engine::profile::profile_version`): every official statement at the
    /// worker count of its largest gap in `scored`, under the timing lease, after the timing; written under
    /// `dir` (`PROFILE.md`, `profile/`). Never gating: a failure is recorded as the profile's error.
    pub(super) fn profile_runnable(&self, label: &str, library: &Path, inputs: &[StorageUseInput], scored: &ScaleScore, dir: &Path) -> Value {
        let all = self.inputs();
        let Some(general) = all.general.as_ref() else { return json!({"status":"not_run","reason":"no general inputs"}) };
        let subject = super::profile::ProfileSubject { runner: self.bench.runner(), library, uses: inputs, access: all.part_access, limits: general.call_limits };
        let statements: Vec<EngineStatement> = all.statements.official.iter().map(|s| s.statement.clone()).collect();
        let locks = self.bench.config.locks.clone();
        let started = std::time::Instant::now();
        let outcome = super::profile::profile_version(&subject, scored, &statements, &dir.join("profile-work"), || locks.timing()).and_then(|profiles| {
            super::profile::write_profile(dir, &format!("{label} at {}", general.scale.name), &profiles).map_err(AdmissionError::tool)?;
            Ok(profiles.len())
        });
        match outcome {
            Ok(statements) => json!({"status":"profiled","statements":statements,"report":dir.join(super::profile::PROFILE_FILE),"records":dir.join(super::profile::PROFILE_DIRECTORY),
                "elapsed_ns":started.elapsed().as_nanos() as u64,"method":super::profile::PROFILE_METHOD}),
            Err(error) => json!({"status":"failed","error":error.to_string(),"meaning":"profiles are diagnostics: never gating"}),
        }
    }

    /// The profile of the admitted version `node` (its score recomputed from the cells its admission recorded).
    fn profile_admitted(&mut self, node: &TreeNode, record: &Value, dir: &Path) -> Value {
        let inputs = self.config.inputs.clone();
        let limit = inputs.general.as_ref().map_or(u64::MAX, |g| g.call_limits.call_limit_ns);
        let outcome = serde_json::from_value::<Vec<CellResult>>(record["candidate_cells"].clone())
            .map_err(|e| e.to_string())
            .and_then(|cells| score(&inputs.baselines, &inputs.training.timing_binding, &inputs.workers, limit, &cells).map_err(|e| e.to_string()))
            .and_then(|scored| self.admitted_runnable(&node.id, &dir.join("profile-storages")).map(|run| (scored, run)).map_err(|e| e.to_string()));
        match outcome {
            Ok((scored, run)) => self.profile_runnable(&node.id, &run.library, &run.inputs, &scored, dir),
            Err(error) => json!({"status":"failed","error":error,"meaning":"profiles are diagnostics: never gating"}),
        }
    }

    /// An admitted version ready to run at the current capture (its library, and its storages' assets: a derived
    /// storage's asset for a new capture is built by its verified builder; a flat storage's comes only from the capture,
    /// `gendb prepare-flat-storage`, and is refused when missing).
    pub(super) fn admitted_runnable(&mut self, id: &str, out: &Path) -> Result<Runnable, AdmissionError> {
        let store = self.bench.store()?;
        let number = version_number(id).ok_or_else(|| AdmissionError::tool(format!("{id} is not a version id")))?;
        let version = engine_versions(&store).map_err(AdmissionError::tool)?.into_iter().find(|v| v.version == number + 1)
            .ok_or_else(|| AdmissionError::tool(format!("{id} is not an admitted engine version of {}", self.bench.config.library.display())))?;
        let build = check_build_evidence(&store, version.package.build).map_err(AdmissionError::tool)?;
        let library = library_path(&store, &build).map_err(AdmissionError::tool)?;
        let uses = version.package.storage_uses.clone();
        let capture = CurrentCapture::of(&self.bench.capture.current()).map_err(AdmissionError::tool)?;
        let mut frozen = vec![];
        for u in &uses {
            let is_flat = flat::flat_ineligibility(&store, u.package, &u.name)?.is_none();
            if is_flat && engine_assets(&store, std::slice::from_ref(u), &capture).is_err() {
                return Err(AdmissionError::tool(format!("{}; run gendb prepare-flat-storage for this scale's capture into the run library, then relaunch", flat::not_prepared(&u.name))));
            }
            let (_, declaration) = catalog::admitted_storage(&store, u.package)?;
            frozen.push(FrozenUse { name: u.name.clone(), source: StorageSource::Admitted { package: u.package }, declaration });
        }
        let resolved = self.bench.resolve_uses_as(&frozen, out, out, TrialVerification::WholeCrate)?;
        Ok(Runnable { label: id.to_string(), library, inputs: storage_inputs(&resolved) })
    }

    /// Time `parent` and `candidate` interleaved over the official cells of the current scale (`engine::race`), `calls`
    /// calls per side of a cell (the plan's, `engine::protocol::EvaluationPlan::cell_calls`), each pair after the host's
    /// quiet-moment gate (`engine::quiet`), the suspicious pairs timed again once.
    pub(super) fn race_runnables(&self, parent: &Runnable, candidate: &Runnable, parent_record: Option<&[CellResult]>, calls: u32, work: &Path) -> Result<RaceReport, RaceError> {
        self.timed_race(parent, candidate, parent_record, calls, work, None)
    }

    /// The re-timing of `recorded`, an earlier race of `parent` and `candidate` at the current scale
    /// (`engine::race::retime_recorded`): its suspicious pairs timed again once, as [`EngineBench::race_runnables`] times
    /// pairs, its other pairs reused.
    pub(super) fn retime_runnables(&self, parent: &Runnable, candidate: &Runnable, parent_record: Option<&[CellResult]>, calls: u32, recorded: RecordedRace, work: &Path) -> Result<RaceReport, RaceError> {
        self.timed_race(parent, candidate, parent_record, calls, work, Some(recorded))
    }

    /// A race of the current scale's official cells on this host (the timing lease, the load average, the quiet-moment
    /// gate): timed whole, or the re-timing of `recorded`.
    fn timed_race(&self, parent: &Runnable, candidate: &Runnable, parent_record: Option<&[CellResult]>, calls: u32, work: &Path, recorded: Option<RecordedRace>) -> Result<RaceReport, RaceError> {
        let inputs = self.inputs();
        let limit = inputs.general.as_ref().map_or(u64::MAX, |g| g.call_limits.call_limit_ns);
        let statements: Vec<EngineStatement> = inputs.statements.official.iter().map(|s| s.statement.clone()).collect();
        let setup = RaceSetup { statements: &statements, workers: &inputs.workers, baselines: &inputs.baselines, call_limit_ns: limit, calls, parent_record, work };
        let parent_cells = EngineCells { runner: self.runner(&parent.library, &parent.inputs), checks: &inputs.checks, adhoc: &[], bound: None };
        let candidate_cells = EngineCells { runner: self.runner(&candidate.library, &candidate.inputs), checks: &inputs.checks, adhoc: &[], bound: None };
        let locks = self.bench.config.locks.clone();
        let gate = QuietGate::for_host();
        let host = RaceHost { timing_lease: || locks.timing(), load_average: read_load_average, wait_for_quiet: || Some(gate.wait(read_load_average, &HostClock::start())) };
        let (parent, candidate) = (Contender { version: &parent.label, runner: &parent_cells }, Contender { version: &candidate.label, runner: &candidate_cells });
        match recorded {
            None => race(&setup, parent, candidate, &host),
            Some(recorded) => retime_recorded(&setup, parent, candidate, recorded, &host),
        }
    }

    /// Time one version alone over the official cells of the current scale, `calls` calls per cell (the plan's), every
    /// failing cell recorded (version 0, a main-line head without a rival at a new scale): the matrix and its score.
    pub(super) fn time_alone(&self, run: &Runnable, calls: u32, work: &Path) -> Result<(EngineMatrix, ScaleScore), AdmissionError> {
        let matrix = self.official_matrix(run, calls, work)?;
        let scored = self.score_matrix(&matrix)?;
        Ok((matrix, scored))
    }

    /// The official cells of the current scale for one version, `calls` calls per cell, every failing cell recorded
    /// (`timing::run_official_recording_failures`).
    pub(super) fn official_matrix(&self, run: &Runnable, calls: u32, work: &Path) -> Result<EngineMatrix, AdmissionError> {
        let inputs = self.inputs();
        let statements: Vec<EngineStatement> = inputs.statements.official.iter().map(|s| s.statement.clone()).collect();
        let cells = EngineCells { runner: self.runner(&run.library, &run.inputs), checks: &inputs.checks, adhoc: &[], bound: None };
        let locks = self.bench.config.locks.clone();
        run_official_recording_failures(&cells, &statements, &inputs.workers, calls, work, || locks.timing())
    }

    /// The score of an official matrix at the current scale (`engine::score`); a matrix with a failed cell has none.
    pub(super) fn score_matrix(&self, matrix: &EngineMatrix) -> Result<ScaleScore, AdmissionError> {
        let inputs = self.inputs();
        let limit = inputs.general.as_ref().map_or(u64::MAX, |g| g.call_limits.call_limit_ns);
        let results = matrix.cell_results(Some(limit)).map_err(|e| AdmissionError::refusal(e.to_string()))?;
        score(&inputs.baselines, &inputs.training.timing_binding, &inputs.workers, limit, &results).map_err(|e| AdmissionError::tool(e.to_string()))
    }

    /// After an acceptance (step 7; [`MainLineCase::step`]), under the run's main-line lock: an accepted merge becomes
    /// the main-line head; a branch version whose acceptance race timed it against the main-line head itself (its
    /// parent, at the current scale and timing binding) takes that race's decision, adopted and not timed again; any
    /// other branch version whose recorded score beats the head's is timed against it, and the winner is the head.
    ///
    /// A run of several workloads (`combined`: the accepted version's combined decision) searches on one line
    /// (`engine::stage::StageRun::prepare`): its acceptance race was against the main-line head, so the combined decision
    /// is adopted as the main-line decision (the first one-engine version accepted by the one-engine rule becomes the
    /// head, [`EngineBench::decide_one_engine_transition`]); any other case there is a framework error.
    fn update_main_line(&mut self, accepted: &TreeNode, dir: &Path, merge: bool, combined: Option<stage::one_engine::CombinedVerdict>) -> Result<Value, AdmissionError> {
        use stage::one_engine::CombinedVerdict;
        let engine_dir = self.config.engine_dir.clone();
        let _lock = main_line_lock(&engine_dir)?;
        let tree = VersionTree::read(&engine_dir).map_err(AdmissionError::tool)?;
        let main = tree.main_line_head().ok_or_else(|| AdmissionError::tool("the main line has no head"))?.to_string();
        let scale = accepted.scale.clone();
        let ours = accepted.score.clone().ok_or_else(|| AdmissionError::tool("an accepted version without a score"))?;
        // The acceptance race is the timing `ours` was read from (`EngineBench::accept`).
        let acceptance = RaceOutcome::read(&ours.record, &ours.scale)?;
        let inputs = self.inputs();
        let current = inputs.general.as_ref().ok_or_else(|| AdmissionError::tool("a general-line acceptance without general inputs"))?.scale.name.clone();
        let head = TimedVersion { version: main.clone(), scale: current, binding: inputs.training.timing_binding.clone() };
        let head_score = tree.score_at(&main, &scale);
        let case = MainLineCase { accepted: &accepted.id, merge, score: &ours, head_score: head_score.as_ref(), raced_against: acceptance.as_ref().map(|a| &a.against), head: &head };
        match case.step() {
            MainLineStep::AlreadyHead => Ok(json!({"changed":false,"head":main,"reason":"already the main-line head"})),
            MainLineStep::Merge => {
                self.select(&accepted.id, &main, "merge", &scale, Some(&ours.record), None)?;
                Ok(json!({"changed":true,"head":accepted.id,"previous":main,"reason":"an accepted merge beat the main-line head in its interleaved timing"}))
            }
            MainLineStep::NotDue => {
                Ok(json!({"changed":false,"head":main,"reason":format!("{}'s recorded score is not better than the main-line head {main}'s at {scale}", accepted.id)}))
            }
            MainLineStep::AdoptAcceptanceRace => {
                let mut race = acceptance.ok_or_else(|| AdmissionError::tool("the acceptance race to adopt has no record"))?;
                // A run of several workloads: the combined score over every counted workload's race decided, or the
                // one-engine rule accepted the first one-engine version.
                match combined {
                    Some(CombinedVerdict::OneEngineTransition) => return self.decide_one_engine_transition(accepted, &race),
                    Some(verdict) => race.candidate_better = verdict == CombinedVerdict::Better,
                    None => {}
                }
                self.decide_main_line(accepted, &race, true)
            }
            step if combined.is_some() => Err(AdmissionError::tool(format!(
                "a run of several workloads searches on one line of versions, where an accepted version's parent is the main-line head; the main-line step {step:?} of {} has no combined decision",
                accepted.id
            ))),
            MainLineStep::Race => {
                let parent = self.admitted_runnable(&main, &dir.join("main-line/parent-storages"))?;
                let candidate = self.admitted_runnable(&accepted.id, &dir.join("main-line/candidate-storages"))?;
                let parent_record = recorded_cells(&engine_dir, &main, &scale);
                let report = self.race_runnables(&parent, &candidate, parent_record.as_deref(), self.submission_plan().cell_calls, &dir.join("main-line/race")).map_err(|e| match e {
                    RaceError::Cell { ref version, .. } => {
                        let _ = append_flag(&engine_dir, &json!({"at_unix_ms":now_unix_ms(),"node":version,"kind":"incident","reason":format!("an admitted version failed in the main-line race: {e}")}));
                        AdmissionError::tool(format!("incident: an admitted version failed in the main-line race ({e}); flagged for the operator"))
                    }
                    other => AdmissionError::tool(format!("main-line race: {other}")),
                })?;
                let race_file = dir.join("main-line/race.json");
                write_json_atomic(&race_file, &json!(report)).map_err(AdmissionError::tool)?;
                let race = RaceOutcome {
                    against: TimedVersion { version: main, scale: scale.clone(), binding: report.binding.clone() },
                    against_score: RecordedScore::of(&scale, &report.parent_score, &race_file),
                    candidate_better: report.candidate_better,
                    file: race_file,
                };
                self.decide_main_line(accepted, &race, false)
            }
        }
    }

    /// The main-line decision from one interleaved timing of `accepted` against the head (`race.against`), run for this
    /// decision or `adopted` (its acceptance race): the head's score there recorded, and the winner the head. The
    /// decision record is the same in both cases but for the adoption note.
    fn decide_main_line(&self, accepted: &TreeNode, race: &RaceOutcome, adopted: bool) -> Result<Value, AdmissionError> {
        let main = &race.against.version;
        let why = if adopted { ADOPTED_ACCEPTANCE_RACE } else { "main_line_race" };
        record_scale_score(&self.config.engine_dir, main, &race.against_score, why).map_err(AdmissionError::tool)?;
        let mut decided = if race.candidate_better {
            self.select(&accepted.id, main, "race", &accepted.scale, Some(&race.file), adopted.then_some(ADOPTED_ACCEPTANCE_RACE))?;
            json!({"changed":true,"head":accepted.id,"previous":main,"race":race.file,"reason":"it beat the main-line head in one interleaved timing"})
        } else {
            json!({"changed":false,"head":main,"race":race.file,"reason":"the main-line head kept its place in one interleaved timing"})
        };
        if adopted {
            decided["adopted"] = json!({"from":ADOPTED_ACCEPTANCE_RACE,"race":race.file,"meaning":ADOPTION_MEANING});
        }
        Ok(decided)
    }

    /// The main-line decision for the first one-engine version of a line whose head is not one engine, accepted by the
    /// one-engine rule (`engine::stage::one_engine`) although its combined score is not better: the head's score in the
    /// acceptance race recorded (as [`EngineBench::decide_main_line`] does), and the version the head, with the reason
    /// `one_engine_transition` and that race (adopted) for reporting.
    fn decide_one_engine_transition(&self, accepted: &TreeNode, race: &RaceOutcome) -> Result<Value, AdmissionError> {
        use stage::one_engine::ONE_ENGINE_TRANSITION;
        let main = &race.against.version;
        record_scale_score(&self.config.engine_dir, main, &race.against_score, ADOPTED_ACCEPTANCE_RACE).map_err(AdmissionError::tool)?;
        self.select(&accepted.id, main, ONE_ENGINE_TRANSITION, &accepted.scale, Some(&race.file), Some(ADOPTED_ACCEPTANCE_RACE))?;
        Ok(json!({"changed":true,"head":accepted.id,"previous":main,"race":race.file,"rule":ONE_ENGINE_TRANSITION,
            "reason":"the first one-engine version of the line: the head, although its combined score is not better than the previous head's in its acceptance race (the request's one-engine rule)",
            "adopted":{"from":ADOPTED_ACCEPTANCE_RACE,"race":race.file,"meaning":ADOPTION_MEANING}}))
    }

    /// Record `version` as the main-line head: the library's selection record (evidence: the deciding timing's summary),
    /// then `main-line.jsonl`. `adopted` names a deciding timing that was not run for this decision
    /// ([`MainLineChange::adopted`]).
    pub(super) fn select(&self, version: &str, previous: &str, reason: &str, scale: &str, race: Option<&Path>, adopted: Option<&str>) -> Result<(), AdmissionError> {
        let store = self.bench.store()?;
        let library_reason = match adopted {
            Some(adopted) => format!("{reason}, timing adopted from its {}", adopted.replace('_', " ")),
            None => reason.to_string(),
        };
        let selection = select_version(&store, version, &library_reason, race)?;
        // A stage run selects the version in every workload's library (they admit every version in lockstep).
        for side in self.stage.map(|s| s.sides.as_slice()).unwrap_or_default() {
            let kept = ObjectStore::open_existing(&side.view.library).map_err(|e| AdmissionError::tool(format!("{}: {e}", side.view.library.display())))?;
            select_version(&kept, version, &library_reason, race).map_err(|e| AdmissionError::tool(format!("workload {}: {e}", side.name)))?;
        }
        append_main_line(&self.config.engine_dir, &MainLineChange {
            version: version.into(),
            previous: Some(previous.to_string()).filter(|p| !p.is_empty()),
            reason: reason.into(),
            scale: scale.into(),
            race: race.map(Path::to_path_buf),
            adopted: adopted.map(String::from),
            selection,
            at_unix_ms: now_unix_ms(),
        })
        .map_err(AdmissionError::tool)
    }

    // ------------------------------------------------------------------------------------------------ records

    /// The version folder: code, reading view, manifests, notes, the evaluation's records, `version.json`
    /// and `node.json` (written last: the tree reads only complete folders).
    fn record_version(&self, frozen_dir: &Path, facts: &SubmissionFacts, node: &TreeNode, record: Value) -> Result<Value, AdmissionError> {
        let engine_dir = &self.config.engine_dir;
        let target = node.directory(engine_dir);
        if target.join(tree::NODE_FILE).is_file() {
            return read_json(&target.join("version.json")).map_err(AdmissionError::tool);
        }
        let engine: FrozenEngine = read_json(&frozen_dir.join("candidate.json")).map_err(AdmissionError::tool)?;
        let staging = target.with_file_name(format!(".staging-{}-{}", node.id, now_unix_ms()));
        fs::create_dir_all(&staging).map_err(AdmissionError::tool)?;
        // A version of several workloads' code is the shared engine and every workload's module (and in a run of
        // several workloads the default module, families and plans; `engine::stage::records`).
        copy_submission(&staging, frozen_dir, self.stage.is_none().then_some(&engine), facts)?;
        if let Some(stage) = self.stage {
            let crates: Vec<(&str, PathBuf)> = std::iter::once((stage.workload.as_str(), frozen_dir.to_path_buf()))
                .chain(stage.sides.iter().map(|k| (k.name.as_str(), stage::side_frozen_dir(stage.form, frozen_dir, &k.name))))
                .collect();
            let crates: Vec<(&str, &Path)> = crates.iter().map(|(w, d)| (*w, d.as_path())).collect();
            if stage.is_members() { stage::records::write_members_code(&staging, &crates)? } else { stage::records::write_stage_code(&staging, &crates)? }
        }
        let uses: Vec<VerusStorageUseV1> = serde_json::from_value(record["admission"]["uses"].clone()).map_err(AdmissionError::tool)?;
        if let Some(manifest) = &facts.manifest {
            let seed = match self.stage {
                Some(stage) => {
                    let side_uses = |name: &str| serde_json::from_value::<Vec<VerusStorageUseV1>>(record["workloads"][name]["admission"]["uses"].clone()).unwrap_or_default();
                    let workloads: Vec<(String, Vec<VerusStorageUseV1>)> =
                        std::iter::once((stage.workload.clone(), uses.clone())).chain(stage.sides.iter().map(|k| (k.name.clone(), side_uses(&k.name)))).collect();
                    if stage.is_members() { stage::records::members_seed_manifest(manifest, &workloads) } else { stage::records::stage_seed_manifest(manifest, &workloads) }
                }
                None => EngineManifest {
                    crate_dir: CRATE_DIRECTORY.into(),
                    storage_uses: uses.iter().map(|u| crate::query::candidate::StorageUseDeclaration::admitted(&u.name, u.package)).collect(),
                    ..manifest.for_seed()
                },
            };
            write_value(&staging.join("seed-manifest.json"), &json!(seed))?;
        }
        let cells: Vec<CellResult> = serde_json::from_value(record["candidate_cells"].clone()).map_err(AdmissionError::tool)?;
        write_value(&staging.join("cells").join(format!("{}.json", node.scale)), &json!(cells))?;
        // The evaluation's records under their own names (`race.json`, `variant-answers.json` or `variant-matrix.json`,
        // `PROFILE.md`), from where the record names them (a resumed evaluation has a fresh directory).
        let named = |pointer: &str| record.pointer(pointer).and_then(Value::as_str).map(PathBuf::from).filter(|p| p.is_file());
        for pointer in ["/race", "/finished_checks/variants/file", "/profile/report"] {
            if let Some((from, name)) = named(pointer).and_then(|from| from.file_name().map(|name| (from.clone(), name.to_owned()))) {
                fs::copy(&from, staging.join(name)).map_err(AdmissionError::tool)?;
            }
        }
        if let Some(from) = named("/profile/records").filter(|p| p.is_dir()) {
            copy_tree(&from, &staging.join(super::profile::PROFILE_DIRECTORY), false)?;
        }
        write_value(&staging.join("admission.json"), &record["admission"])?;
        let mut version = self.version_record(node, facts, &record, &target)?;
        // A stage version: every workload's records and its `version.json` `workloads` (the stage fixture); a version of a run
        // of several workloads also its `combined_score` and `general` (the workloads fixture).
        match self.stage {
            Some(stage) if stage.is_members() => {
                let (workloads, combined, general) = self.write_member_workloads(&staging, &target, node, &record, &engine)?;
                version["workloads"] = workloads;
                version["combined_score"] = combined;
                version["general"] = general;
                // Accepted by the one-engine rule as the first one-engine version (only then: other versions as before).
                let transition = &record["combined"][stage::one_engine::ONE_ENGINE_TRANSITION];
                if transition.is_object() {
                    version[stage::one_engine::ONE_ENGINE_TRANSITION] = transition.clone();
                }
            }
            Some(_) => version["workloads"] = self.write_stage_workloads(&staging, &target, node, &record, &engine)?,
            None => {}
        }
        write_value(&staging.join("version.json"), &version)?;
        write_value(&staging.join("receipts.json"), &facts.cost)?;
        let readme = version_readme(&version) + &crate::output::engine::general::workloads_readme(&version).unwrap_or_default();
        fs::write(staging.join("README.md"), readme).map_err(AdmissionError::tool)?;
        write_value(&staging.join(tree::NODE_FILE), &json!(node))?;
        fs::rename(&staging, &target).map_err(|e| AdmissionError::tool(format!("{} -> {}: {e}", staging.display(), target.display())))?;
        Ok(version)
    }

    /// `version.json` of a general-line version.
    fn version_record(&self, node: &TreeNode, facts: &SubmissionFacts, record: &Value, target: &Path) -> Result<Value, AdmissionError> {
        let inputs = self.inputs();
        let general = inputs.general.as_ref().ok_or_else(|| AdmissionError::tool("general inputs"))?;
        let statement = inputs.sessions[0].1.statement();
        let ddl_sha256: String = Sha256::digest(statement.schema_ddl.as_bytes()).iter().map(|b| format!("{b:02x}")).collect();
        let session = self.config.session()?;
        let mut times = serde_json::Map::new();
        times.insert(general.scale.name.clone(), json!({"score":node.score,"race":record["race"],"summary":record["race_summary"]}));
        let mut version = json!({"format_version":1,"version":node.id,"accepted":true,"directory":target,"node":node,
            "parents":node.parents,"branch":node.branch,"kind":node.kind,
            "goal":{"schema":{"ddl_sha256":ddl_sha256,"declared_constraints":record["admission"]["package"]},
                "workload":{"training_set":inputs.training.identity,"templates":inputs.training.templates.len(),"timing_binding":inputs.training.timing_binding,"workers":inputs.workers},
                "hardware":crate::controller::hardware::observe_host(),"scale":general.scale.name},
            "assumptions":{"entry_identity":gendb_verification::obligations::ENGINE_ENTRY_IDENTITY,
                "trusted_assumptions":ENGINE_TRUSTED_ASSUMPTIONS.iter().map(|a| a.id).collect::<Vec<_>>(),"rule_set":inputs.rules.record(),
                "storage_policy":self.bench.config.storage_policy.kind(),"budget_rule":record["storage"]["budget_rule"]},
            "proof":{"verification":record["build"]["verification"],"wall_ns":record["build"]["wall_ns"],"crate_version":record["crate_version"],
                "toolkit_digest":super::submission::toolkit_digest()},
            "storage":{"uses":record["admission"]["uses"],"serving_bytes":record["storage_policy_at_evaluation"]["serving_bytes"],
                "budget_bytes":general.scale.original_data_bytes,"budget":"the original data size at this scale, the bound on changed storage (a version reading only the plain storage is allowed as is)",
                "plain_storage_bytes":general.plain_storage_bytes,
                "decision":record["storage_policy_at_evaluation"]["budget_decision"]},
            "times":times,
            "cost":facts.cost,"session":session.record,"iteration":facts.iteration,
            "library_bytes_after_admission":library_bytes(&self.bench.config.library)?,
            "direction":node.direction,"rationale":facts.rationale,"findings":facts.manifest.as_ref().map(|m| m.findings.clone()).unwrap_or_default(),
            "profile":record["profile"],
            "admission":record["admission"],"finished_checks":record["finished_checks"]});
        // A version admitted by the re-evaluation of a recorded attempt names it (`engine::re_evaluation`).
        if !record["re_evaluation"].is_null() {
            version["re_evaluation"] = record["re_evaluation"].clone();
        }
        Ok(version)
    }

    /// An attempt's folder: its code (when it was frozen), notes, the evaluation's records and `node.json` (last).
    #[allow(clippy::too_many_arguments)]
    fn record_attempt(&self, dir: &Path, frozen_dir: &Path, candidate: &Value, facts: &SubmissionFacts, node: &TreeNode, folder: &Path, flagged: bool, parts: &Value) -> Result<(), AdmissionError> {
        let engine: Option<FrozenEngine> = (candidate["kind"] != REFUSED_CANDIDATE_KIND).then(|| serde_json::from_value(candidate.clone()).ok()).flatten();
        copy_submission(folder, frozen_dir, engine.as_ref(), facts)?;
        if dir.join("race.json").is_file() {
            fs::copy(dir.join("race.json"), folder.join("race.json")).map_err(AdmissionError::tool)?;
        }
        let mut attempt = json!({"format_version":1,"attempt":node.id,"accepted":false,"node":node,"reason":node.reason,"flagged_for_root":flagged,
            "evaluation":dir,"cost":facts.cost,"candidate":candidate});
        // A run of several workloads: every workload's status (and the combined decision), and each timed other
        // workload's race beside the primary's.
        add_parts(&mut attempt, parts);
        let statuses = parts["kept_workloads"].as_array().or_else(|| parts["members"].as_array());
        for other in statuses.into_iter().flatten() {
            if let (Some(name), Some(race)) = (other["name"].as_str(), other["race"].as_str().map(Path::new).filter(|r| r.is_file() && *r != dir.join("race.json").as_path())) {
                let target = folder.join(tree::WORKLOADS_DIRECTORY).join(name).join("race.json");
                fs::create_dir_all(target.parent().unwrap_or(folder)).map_err(AdmissionError::tool)?;
                fs::copy(race, target).map_err(AdmissionError::tool)?;
            }
        }
        write_value(&folder.join("attempt.json"), &attempt)?;
        write_value(&folder.join("receipts.json"), &facts.cost)?;
        tree::write_node(&self.config.engine_dir, node).map(drop).map_err(AdmissionError::tool)
    }

    /// One findings entry: the node, its branch and parent, the change, the measured effect against the
    /// parent (from the evaluation's interleaved timing) and the author's findings.
    /// In a run of several workloads, `stage` adds its part: `workloads` (each other workload's role, scale and effect,
    /// from its race against the parent's side, or its check) and `combined` (the combined decision) for a version,
    /// `kept_workloads` (a stage run's statuses) or `members` and `combined` for an attempt; `Null` fields are left out,
    /// so a run with one workload logs as before.
    #[allow(clippy::too_many_arguments)]
    fn log_finding(&self, node: &TreeNode, parent: &str, facts: &SubmissionFacts, accepted: bool, reason: Option<&str>, dir: Option<&Path>, stage: &Value) -> Result<(), AdmissionError> {
        let race: Option<Value> = dir.map(|d| d.join("race.json")).filter(|p| p.is_file()).and_then(|p| read_json(&p).ok());
        let effect = race.as_ref().map(race_effect);
        let mut entry = json!({"at_unix_ms":now_unix_ms(),"node":node.id,"branch":node.branch,"parent":parent,"accepted":accepted,"reason":reason,
            "change":facts.rationale,"effect":effect,"findings":facts.manifest.as_ref().map(|m| m.findings.clone()).unwrap_or_default(),"direction":node.direction});
        for (key, value) in stage.as_object().into_iter().flatten().filter(|(_, v)| !v.is_null()) {
            entry[key.as_str()] = value.clone();
        }
        append_finding(&self.config.engine_dir, &entry).map_err(AdmissionError::tool)
    }

    /// A stage run's kept workloads' statuses in the evaluation `dir` (`engine::stage::kept_statuses`); `Null` elsewhere.
    fn kept_workloads_of(&self, dir: &Path) -> Value {
        match self.stage {
            Some(stage) => json!(stage::kept_statuses(dir, &stage.sides.iter().map(|k| k.name.clone()).collect::<Vec<_>>())),
            None => Value::Null,
        }
    }

    /// The parts of an attempt's records of a run of several workloads (`Null` in a run of one workload): a stage run's
    /// kept workloads' statuses (a kept crate refused at freeze, which the refused candidate names, is that workload's
    /// refusal); a run of several workloads' every workload's status and the combined decision, as its evaluation `dir`
    /// recorded them (a crate refused at freeze is that workload's refusal at `freeze`).
    fn parts_of_attempt(&self, dir: &Path, candidate: &Value) -> Value {
        let Some(stage) = self.stage else { return Value::Null };
        let refused_at_freeze = candidate["kind"] == REFUSED_CANDIDATE_KIND;
        if stage.is_members() {
            let mut statuses = json!(MemberStatuses::read(dir, &stage.members()));
            if refused_at_freeze {
                let workload = candidate["workload"].as_str().unwrap_or(&stage.workload);
                for status in statuses.as_array_mut().into_iter().flatten().filter(|s| s["name"] == workload && s["status"] == "not_run") {
                    status["status"] = json!("refused");
                    status["step"] = json!("freeze");
                    status["reason"] = json!(candidate["error"].as_str().and_then(|e| e.lines().next()).unwrap_or_default());
                }
            }
            return json!({"members":statuses,"combined":stage::members::recorded_combined(dir)});
        }
        let mut statuses = self.kept_workloads_of(dir);
        if let (Some(workload), true) = (candidate["workload"].as_str(), refused_at_freeze) {
            for status in statuses.as_array_mut().into_iter().flatten().filter(|s| s["name"] == workload) {
                status["status"] = json!("refused");
                status["reason"] = candidate["error"].clone();
            }
        }
        json!({"kept_workloads":statuses})
    }
}

/// The keys a run of several workloads adds to an evaluation's records ([`Verdict`]'s `parts`).
const PART_KEYS: [&str; 3] = ["kept_workloads", "members", "combined"];

/// The parts recorded in `record` (an accepted version's record, or a recorded verdict): its [`PART_KEYS`], or `Null`
/// when it has none (a run of one workload).
fn parts_of_record(record: &Value) -> Value {
    let parts: serde_json::Map<String, Value> = PART_KEYS.iter().filter_map(|key| record.get(*key).filter(|v| !v.is_null()).map(|v| (key.to_string(), v.clone()))).collect();
    if parts.is_empty() { Value::Null } else { Value::Object(parts) }
}

/// Add the parts `parts` (an object, or `Null`) to `record`, each key whose value is not null.
fn add_parts(record: &mut Value, parts: &Value) {
    for (key, value) in parts.as_object().into_iter().flatten().filter(|(_, v)| !v.is_null()) {
        record[key.as_str()] = value.clone();
    }
}

/// The measured effect of one race report (`race.json`): both sides' finished cells and normalized time, the cells
/// faster and slower, and the ratio per cell.
fn race_effect(r: &Value) -> Value {
    let ratios: Vec<f64> = r["pairs"].as_array().into_iter().flatten().filter_map(|p| p["candidate_over_parent"].as_f64()).collect();
    json!({"parent_finished":r["parent_score"]["score"]["finished"],"finished":r["candidate_score"]["score"]["finished"],
        "parent_normalized_time":r["parent_score"]["score"]["normalized_time"],"normalized_time":r["candidate_score"]["score"]["normalized_time"],
        "cells_faster":ratios.iter().filter(|x| **x < 1.0).count(),"cells_slower":ratios.iter().filter(|x| **x > 1.0).count(),
        "per_cell":r["pairs"].as_array().into_iter().flatten().map(|p| json!({"template":p["template"],"workers":p["workers"],"ratio":p["candidate_over_parent"]})).collect::<Vec<_>>()})
}

/// The findings entry's part of an accepted version's record of a run of several workloads (`log_finding`): every other
/// workload's role, scale and effect from its race (a stage run's kept workloads; in a run of several workloads also a
/// check workload's answers, `check`) and, in a run of several workloads, the combined decision; `{}` without other
/// workloads.
fn stage_effects(record: &Value) -> Value {
    let Some(workloads) = record["workloads"].as_object().filter(|w| !w.is_empty()) else { return json!({}) };
    let effects: serde_json::Map<String, Value> = workloads
        .iter()
        .map(|(name, other)| {
            let race: Option<Value> = other["race"].as_str().map(Path::new).filter(|p| p.is_file()).and_then(|p| read_json(p).ok());
            let mut effect = json!({"role":other["role"],"scale":other["scale"],"effect":race.as_ref().map(race_effect)});
            if other["check"].is_object() {
                effect["check"] = json!({"calls":other["check"]["calls"],"agreed":other["check"]["agreed"]});
            }
            (name.clone(), effect)
        })
        .collect();
    let mut part = json!({"workloads":effects});
    if record["combined"].is_object() {
        part["combined"] = record["combined"].clone();
    }
    part
}

/// [`admit_engine_version_on_line`] for one crate of a stage run (module documentation): holding the library's budget
/// lock, the storage policy of its uses under `rule` (its record joins the evidence), then the stage admission under the
/// run's stage rule set (`admission::engine::admit_stage_engine`: uniform flat access, the stage TCB and source checks).
#[allow(clippy::too_many_arguments)]
fn admit_stage_version(
    _budget_lock: &LibraryLock,
    store: &ObjectStore,
    capture: &CurrentCapture,
    policy: &crate::storage::policy::StoredDataPolicy,
    rule: &crate::storage::engine_library::BudgetRule,
    schema: EngineSchema<'_>,
    mut candidate: EngineCandidate<'_>,
    rules: &gendb_verification::verus::engine_rules::EngineRuleSet,
) -> Result<EngineAdmission, AdmissionError> {
    let storage_policy = check_engine_storage_uses(store, capture, schema.tables, policy, rule, &candidate.uses, &[])?;
    candidate.evidence.push((crate::storage::engine_library::ENGINE_STORAGE_POLICY_KIND, storage_policy));
    let clause_text = |text: &str, name: &str| crate::query::source_items::requires_ensures(text, name);
    gendb_verification::admission::engine::admit_stage_engine(store, schema, candidate, rules, &clause_text)
}

/// The verdict recorded beside a frozen submission by an earlier evaluation (`recorded.json`), if any.
fn recorded_verdict(frozen_dir: &Path) -> Result<Option<Verdict>, Failure> {
    let path = frozen_dir.join(RECORDED_FILE);
    if !path.is_file() {
        return Ok(None);
    }
    let recorded: Value = read_json(&path).map_err(AdmissionError::tool)?;
    let node: TreeNode = serde_json::from_value(recorded["node"].clone()).map_err(AdmissionError::tool)?;
    Ok(Some(if recorded["accepted"] == true {
        Verdict::Accepted { node, record: recorded["record"].clone(), merge_accepted: recorded["merge_accepted"] == true, main_line: recorded["main_line"].clone(),
            parts: parts_of_record(&recorded["record"]) }
    } else {
        Verdict::Attempt { node, flagged: recorded["flagged"] == true, parts: parts_of_record(&recorded) }
    }))
}

/// The library's admitted engine version of the frozen submission in `frozen_dir`, if any (module documentation): the
/// version whose build was frozen at `<frozen_dir>/crate` with exactly the frozen crate's author files (paths and
/// bytes, by blob id). A frozen directory is created once per submission and never reused, so this is the submission's
/// own admission; a version built there from other author files is a framework error.
pub(super) fn admitted_version_of(store: &ObjectStore, frozen_dir: &Path, engine: &FrozenEngine) -> Result<Option<EngineVersion>, AdmissionError> {
    let root = frozen_dir.join("crate");
    for version in engine_versions(store).map_err(AdmissionError::tool)?.into_iter().rev() {
        let build = check_build_evidence(store, version.package.build).map_err(AdmissionError::tool)?;
        if build.frozen_directory != root {
            continue;
        }
        let built: BTreeMap<&str, ContentId> = build.sources.iter().filter(|s| s.owner == VerusSourceOwnerV1::Agent).map(|s| (s.path.as_str(), s.blob)).collect();
        let mut same = built.len() == engine.author_files.len();
        for file in &engine.author_files {
            let bytes = fs::read(root.join("src").join(file)).map_err(|e| AdmissionError::tool(format!("{}: {e}", root.join("src").join(file).display())))?;
            same &= built.get(file.as_str()) == Some(&blob_id(&bytes));
        }
        if !same {
            return Err(AdmissionError::tool(format!(
                "library version {} was built from {} with other author files than its frozen submission now holds",
                version.version,
                root.display()
            )));
        }
        return Ok(Some(version));
    }
    Ok(None)
}

/// A workspace storage that an earlier attempt of one admission registered (`EngineBench::admit`).
#[derive(Clone, Debug, serde::Serialize)]
struct EarlierRegistration {
    name: String,
    package: ContentId,
    admission: ContentId,
}

/// The workspace storages among `uses` that the library already holds as registered by the same admission as
/// `registered_by` (the registration's `registered_by` record names the role and the frozen submission it was admitted
/// with): each name's newest such version. A frozen directory is created once per submission and never reused, so
/// these are this admission's own registrations from an attempt that stopped before the engine was admitted.
fn registered_by_admission(store: &ObjectStore, uses: &[FrozenUse], registered_by: &Value) -> Result<Vec<EarlierRegistration>, AdmissionError> {
    let mut earlier = vec![];
    for storage_use in uses.iter().filter(|u| matches!(u.source, StorageSource::Workspace { .. })) {
        for (admission, version) in gendb_artifacts::verus::storage_versions(store, &storage_use.name).map_err(AdmissionError::tool)? {
            let recorded = &catalog::description_of(store, version.package, &storage_use.name)?["registered_by"];
            if recorded["role"] == registered_by["role"] && recorded["admission"] == registered_by["admission"] {
                earlier.push(EarlierRegistration { name: storage_use.name.clone(), package: version.package, admission });
                break;
            }
        }
    }
    Ok(earlier)
}

/// A fresh directory `<parent>/<name>` (or `<name>-1`, `<name>-2`, ... when it exists): every attempt of a resumable step
/// writes its evidence apart from the attempts before it.
pub(super) fn fresh_directory(parent: &Path, name: &str) -> Result<PathBuf, AdmissionError> {
    fs::create_dir_all(parent).map_err(AdmissionError::tool)?;
    for ordinal in 0u32.. {
        let dir = if ordinal == 0 { parent.join(name) } else { parent.join(format!("{name}-{ordinal}")) };
        match fs::create_dir(&dir) {
            Ok(()) => return Ok(dir),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(AdmissionError::tool(format!("{}: {error}", dir.display()))),
        }
    }
    unreachable!("an unbounded ordinal range")
}

/// Test builds only: end this process with SIGKILL at `point` when the environment's `GENDB_TEST_CRASH_AT` names it, so
/// the general line's trial can check that a relaunch resumes from the records (`engine::general_trial`). Call sites
/// are `#[cfg(test)]` too: no other build has a crash point.
#[cfg(test)]
pub(super) fn crash_point(point: &str) {
    if std::env::var("GENDB_TEST_CRASH_AT").is_ok_and(|named| named == point) {
        eprintln!("crash point {point}: SIGKILL (test)");
        // SAFETY: kill(2) on this process with a valid signal number; it does not return.
        unsafe {
            libc::kill(libc::getpid(), libc::SIGKILL);
        }
    }
}

/// Whether a newly accepted branch version is timed against the main-line head: when its recorded score
/// is better than the head's recorded score at the same scale, or the head has none there. Recorded scores come from
/// different windows, so this only decides whether to time; the interleaved timing decides the head.
pub fn main_line_race_due(ours: &RecordedScore, main_line_head: Option<&RecordedScore>) -> bool {
    main_line_head.is_none_or(|theirs| ours.better_than(theirs))
}

/// What a main-line decision records about an adopted timing (`main-line.json`, `adopted.meaning`).
const ADOPTION_MEANING: &str = "the main-line head was this version's parent at the same scale and timing binding, so its acceptance race already was the interleaved timing of the version against the main-line head: its result decides, and nothing is timed again";

/// The version one interleaved timing ran as the parent (the incumbent), at which scale and timing binding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TimedVersion {
    pub version: String,
    pub scale: String,
    pub binding: String,
}

/// What the main-line decision after an acceptance knows.
pub struct MainLineCase<'a> {
    /// The accepted version, and whether it is a merge.
    pub accepted: &'a str,
    pub merge: bool,
    /// Its recorded score (read from its acceptance race) and the head's recorded score at that scale.
    pub score: &'a RecordedScore,
    pub head_score: Option<&'a RecordedScore>,
    /// The parent its acceptance race timed it against (`None`: no record of that race).
    pub raced_against: Option<&'a TimedVersion>,
    /// The main-line head, at the current scale and timing binding.
    pub head: &'a TimedVersion,
}

/// How the main-line head is decided after an acceptance ([`MainLineCase::step`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MainLineStep {
    /// The accepted version already is the head.
    AlreadyHead,
    /// An accepted merge becomes the head: it was judged against the head.
    Merge,
    /// The acceptance race timed the version against the head itself, here: its result decides, nothing is timed again.
    AdoptAcceptanceRace,
    /// Its recorded score is not better than the head's: no timing, the head stays.
    NotDue,
    /// It is timed against the head in one interleaved timing; the winner is the head.
    Race,
}

impl MainLineCase<'_> {
    /// The step: the head itself and merges first; then, when the acceptance race's parent is the head at
    /// the same scale and timing binding, that race is the interleaved timing of the version against the head and is
    /// adopted, whatever the recorded scores from other windows say; otherwise a timing when the recorded score is
    /// better ([`main_line_race_due`]). A rebase onto another head, a branch head that is not the main-line head, a head
    /// that moved on during the evaluation, or another scale or binding is timed again.
    pub fn step(&self) -> MainLineStep {
        if self.accepted == self.head.version {
            MainLineStep::AlreadyHead
        } else if self.merge {
            MainLineStep::Merge
        } else if self.raced_against == Some(self.head) {
            MainLineStep::AdoptAcceptanceRace
        } else if main_line_race_due(self.score, self.head_score) {
            MainLineStep::Race
        } else {
            MainLineStep::NotDue
        }
    }
}

/// One interleaved timing of an accepted version as the main-line decision reads it: its record, the parent side
/// (whom it timed the version against, and where) with that side's score, and whether the version was better.
struct RaceOutcome {
    file: PathBuf,
    against: TimedVersion,
    against_score: RecordedScore,
    candidate_better: bool,
}

impl RaceOutcome {
    /// The acceptance race recorded at `file` (`race.json`, an `engine::race::RaceReport`), timed at `scale`; `None`
    /// when there is no such record.
    fn read(file: &Path, scale: &str) -> Result<Option<Self>, AdmissionError> {
        if !file.is_file() {
            return Ok(None);
        }
        let race: Value = read_json(file).map_err(AdmissionError::tool)?;
        let malformed = |field: &str| AdmissionError::tool(format!("{}: the race record has no valid `{field}`", file.display()));
        let text = |field: &str| race[field].as_str().map(String::from).ok_or_else(|| malformed(field));
        let parent = &race["parent_score"];
        let against_score = RecordedScore {
            scale: scale.into(),
            score: serde_json::from_value(parent["score"].clone()).map_err(|_| malformed("parent_score.score"))?,
            cells: parent["cells_total"].as_u64().ok_or_else(|| malformed("parent_score.cells_total"))? as usize,
            beats_both: parent["beats_both"].as_bool().ok_or_else(|| malformed("parent_score.beats_both"))?,
            record: file.to_path_buf(),
        };
        Ok(Some(Self {
            file: file.to_path_buf(),
            against: TimedVersion { version: text("parent")?, scale: scale.into(), binding: text("binding")? },
            against_score,
            candidate_better: race["candidate_better"].as_bool().ok_or_else(|| malformed("candidate_better"))?,
        }))
    }
}

/// The cells a version recorded at `scale` (`versions/vNNN/cells/<scale>.json`), for a race's skips.
pub(super) fn recorded_cells(engine_dir: &Path, version: &str, scale: &str) -> Option<Vec<CellResult>> {
    let path = node_directory(engine_dir, version, true).join("cells").join(format!("{scale}.json"));
    read_json(&path).ok()
}

/// Record a version's cells at `scale` (a later timing: version 0, a scale move); kept when already recorded.
pub(super) fn record_cells(engine_dir: &Path, version: &str, scale: &str, scored: &ScaleScore) -> Result<(), AdmissionError> {
    let path = node_directory(engine_dir, version, true).join("cells").join(format!("{scale}.json"));
    if path.is_file() {
        return Ok(());
    }
    let cells: Vec<CellResult> = scored.cells.iter().map(|c| CellResult { template: c.template.clone(), workers: c.workers, status: c.status }).collect();
    write_value(&path, &json!(cells))
}

/// The variants `run` runs among `variants` (the variants with AST bytes of their own): those of the templates in
/// `finished` when it runs only the finished templates' (`VariantRun::finished_templates_only`), else every one.
fn selected_variants(run: VariantRun, variants: &[EncodedStatement], finished: &BTreeSet<String>) -> Vec<EngineStatement> {
    variants.iter().filter(|v| !run.finished_templates_only() || finished.contains(&v.statement.template)).map(|v| v.statement.clone()).collect()
}

/// The templates whose cells finished at every worker count.
fn finished_templates(scored: &ScaleScore, workers: &[usize]) -> BTreeSet<String> {
    let mut finished: BTreeMap<&str, usize> = BTreeMap::new();
    for cell in scored.cells.iter().filter(|c| c.status.is_finished()) {
        *finished.entry(cell.template.as_str()).or_default() += 1;
    }
    finished.into_iter().filter(|(_, n)| *n == workers.len()).map(|(t, _)| t.to_string()).collect()
}

/// A race that ended without a report: the candidate's wrong answer is its attempt (flagged); a parent's failure is an
/// incident (flagged, and the framework stops); a lease or score failure is the framework's.
pub(super) fn race_failure(engine_dir: &Path, parent: &str, error: RaceError) -> Failure {
    match error {
        RaceError::Cell { side: Side::Candidate, error, template, workers, .. } if error.class != FailureClass::ToolFailure => Failure::Candidate {
            reason: format!("refusal: an answer in the interleaved timing was refused ({template} at {workers} workers): {error}"),
            flagged: true,
            score: None,
        },
        RaceError::Cell { side: Side::Parent, ref error, ref template, workers, .. } if error.class != FailureClass::ToolFailure => {
            let _ = append_flag(engine_dir, &json!({"at_unix_ms":now_unix_ms(),"node":parent,"kind":"incident","reason":format!("admitted version {parent} failed at {template}, {workers} workers: {error}")}));
            Failure::Framework(AdmissionError::tool(format!("incident: admitted parent {parent} failed in the interleaved timing ({template} at {workers} workers): {error}; flagged for the operator")))
        }
        other => Failure::Framework(AdmissionError::tool(format!("interleaved timing: {other}"))),
    }
}

/// A qualification or variant step's error: a tool failure is the framework's, any other a refused answer (flagged).
pub(super) fn answer_failure(error: AdmissionError, step: &str) -> Failure {
    if error.class == FailureClass::ToolFailure {
        Failure::Framework(error)
    } else {
        Failure::Candidate { reason: format!("refusal: {step}: {error}"), flagged: true, score: None }
    }
}

/// A step that fails only in the framework (recording, reading records): a candidate failure there is a framework error.
fn framework_only(failure: Failure) -> AdmissionError {
    match failure {
        Failure::Framework(error) => error,
        Failure::Candidate { reason, .. } => AdmissionError::tool(format!("recording the re-evaluation failed: {reason}")),
    }
}

/// The lineage parents (engine package ids): the parent, and a merge's branch head.
pub(super) fn lineage_parents(tree: &VersionTree, store: &ObjectStore, parent: &Parent, merge_from: Option<&str>, kind: SessionKind) -> Result<Vec<ContentId>, AdmissionError> {
    let mut ids = vec![parent.id.clone()];
    if kind == SessionKind::Merge && let Some(branch_head) = merge_from && branch_head != parent.id {
        ids.push(branch_head.to_string());
    }
    let versions = engine_versions(store).map_err(AdmissionError::tool)?;
    ids.iter()
        .map(|id| {
            let number = version_number(id).filter(|_| tree.version(id).is_some()).ok_or_else(|| AdmissionError::tool(format!("{id} is not a version of the tree")))?;
            versions.iter().find(|v| v.version == number + 1).map(|v| v.package_id).ok_or_else(|| AdmissionError::tool(format!("{id} is not admitted")))
        })
        .collect()
}

/// The compact record of an interleaved timing stored as evidence: who, when, the scores and how many children ran.
pub(super) fn race_summary(report: &RaceReport, file: &Path) -> Value {
    json!({"parent":report.parent,"candidate":report.candidate,"binding":report.binding,"window_start_unix_ms":report.window_start_unix_ms,"window_end_unix_ms":report.window_end_unix_ms,
        "parent_score":report.parent_score.score,"candidate_score":report.candidate_score.score,"candidate_better":report.candidate_better,
        "children_run":report.children_run,"parent_children_skipped":report.parent_children_skipped,"retimed_pairs":report.retimed_pairs,"reused":report.reused,
        "calls_per_cell":report.calls_per_cell,"rule":report.rule,"file":file})
}

/// The branch's stated direction: its newest node that states one.
pub(super) fn branch_direction(tree: &VersionTree, branch: &str) -> Option<String> {
    tree.of_branch(branch).filter(|n| n.direction.is_some()).max_by_key(|n| n.created_unix_ms).and_then(|n| n.direction.clone())
}

/// Whether the next submission of `branch` must state a direction: only when several branches search at once (each
/// states how it differs from the others) and the branch has stated none. On one line (one branch)
/// `direction` is optional: one short line on what the session works on.
pub(super) fn direction_required(branches: usize, kind: SessionKind, tree: &VersionTree, branch: &str) -> bool {
    branches > 1 && kind == SessionKind::Branch && branch_direction(tree, branch).is_none()
}

/// Hold the run's main-line lock (`engine/main-line.lock`) until dropped.
pub(super) fn main_line_lock(engine_dir: &Path) -> Result<FileLock, AdmissionError> {
    records::create_dir(engine_dir).map_err(AdmissionError::tool)?;
    let path = engine_dir.join(MAIN_LINE_LOCK);
    let file = fs::OpenOptions::new().create(true).truncate(false).write(true).open(&path).map_err(|e| AdmissionError::tool(format!("{}: {e}", path.display())))?;
    FileLock::acquire(file, libc::LOCK_EX).map_err(|e| AdmissionError::tool(format!("{}: {e}", path.display())))
}

/// Append the library's selection record of `version` (evidence: the deciding timing's summary, when given).
pub(super) fn select_version(store: &ObjectStore, version: &str, reason: &str, race: Option<&Path>) -> Result<ContentId, AdmissionError> {
    let number = version_number(version).ok_or_else(|| AdmissionError::tool(format!("{version} is not a version id")))?;
    let admitted = engine_versions(store).map_err(AdmissionError::tool)?.into_iter().find(|v| v.version == number + 1)
        .ok_or_else(|| AdmissionError::tool(format!("{version} is not admitted")))?;
    let mut evidence = vec![];
    if let Some(race) = race.filter(|p| p.is_file()) {
        let report: Value = read_json(race).map_err(AdmissionError::tool)?;
        let summary = json!({"parent":report["parent"],"candidate":report["candidate"],"binding":report["binding"],"window_start_unix_ms":report["window_start_unix_ms"],
            "window_end_unix_ms":report["window_end_unix_ms"],"parent_score":report["parent_score"]["score"],"candidate_score":report["candidate_score"]["score"],
            "candidate_better":report["candidate_better"],"file":race});
        evidence.push(store.put(1, ENGINE_RACE_KIND, &float_free(&summary)).map_err(AdmissionError::tool)?);
    }
    let selection = VerusEngineSelectionV1 { package: admitted.package_id, admission: admitted.admission_id, reason: format!("{reason} ({version})"), evidence };
    select_engine_version(store, &selection).map(|(id, _)| id).map_err(|e| AdmissionError::tool(format!("selecting {version}: {e}")))
}

/// Copy a submission's code (when frozen), its reading view, frozen manifest and notes into `target`.
fn copy_submission(target: &Path, frozen_dir: &Path, engine: Option<&FrozenEngine>, facts: &SubmissionFacts) -> Result<(), AdmissionError> {
    fs::create_dir_all(target).map_err(AdmissionError::tool)?;
    if let Some(engine) = engine {
        let crate_src = frozen_dir.join("crate/src");
        copy_tree(&crate_src.join("agent"), &target.join("code/agent"), false)?;
        if frozen_dir.join("storages").is_dir() {
            copy_tree(&frozen_dir.join("storages"), &target.join("code/storages"), false)?;
        }
        for file in engine.author_files.iter().filter(|f| f.starts_with("agent/") && f.ends_with(".rs")) {
            let text = fs::read_to_string(crate_src.join(file)).map_err(AdmissionError::tool)?;
            let view = target.join("code-view").join(format!("{file}.md"));
            fs::create_dir_all(view.parent().unwrap_or(target)).map_err(AdmissionError::tool)?;
            fs::write(view, crate::output::code_view(&text)).map_err(AdmissionError::tool)?;
        }
    }
    if let Some(manifest) = &facts.manifest {
        write_value(&target.join("manifest.json"), &json!(manifest))?;
    }
    if let Some(notes) = &facts.notes {
        fs::copy(notes, target.join(NOTES_FILE)).map_err(AdmissionError::tool)?;
    }
    Ok(())
}

fn write_value(path: &Path, value: &Value) -> Result<(), AdmissionError> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(AdmissionError::tool)?;
    }
    fs::write(path, format!("{}\n", serde_json::to_string_pretty(value).map_err(AdmissionError::tool)?)).map_err(AdmissionError::tool)
}

/// `README.md` of a general-line version.
fn version_readme(version: &Value) -> String {
    let score = &version["node"]["score"];
    // The first one-engine version accepted by the one-engine rule did not beat its parent.
    let decided = if version[stage::one_engine::ONE_ENGINE_TRANSITION].is_object() {
        "It was accepted as the first one-engine version of the line (the request's one-engine rule), although its combined score is not better than its parent's; its races are recorded (`race.json`, `version.json` `one_engine_transition`)"
    } else {
        "It beat its parent in one interleaved timing (`race.json`)"
    };
    format!(
        "# Engine version {}\n\nBranch {}, kind {}, parents {}. Scale {}: {} of {} cells finished, normalized time {} (the sum over worker counts of the engine's total over the faster baseline's total). {decided}.\n\nStorage: {} serving bytes; the budget for changed storage is {} bytes ({}).\n\nDirection: {}\n\nRecords: `version.json` (goal, assumptions, proof, storage, times, cost), `node.json`, `admission.json`, `race.json` (per cell 1 warm call and the run's timed hot calls, `calls_per_cell`; the cell's time the median hot call), `cells/`, `variant-answers.json` (the variants' answers at the first scale of the ladder), `receipts.json`; `code/` holds the author's sources (code and proofs), `code-view/` their reading view, `NOTES.md` the branch notebook at submission.\n",
        version["version"].as_str().unwrap_or("-"),
        version["branch"].as_str().unwrap_or("-"),
        version["kind"].as_str().unwrap_or("-"),
        version["parents"].as_array().map(|p| p.iter().filter_map(Value::as_str).collect::<Vec<_>>().join(", ")).unwrap_or_default(),
        score["scale"].as_str().unwrap_or("-"),
        score["score"]["finished"],
        score["cells"],
        score["score"]["normalized_time"].as_str().unwrap_or("-"),
        version["storage"]["serving_bytes"],
        version["storage"]["budget_bytes"],
        version["storage"]["decision"].as_str().unwrap_or("-"),
        version["direction"].as_str().unwrap_or("not restated")
    )
}

/// The qualification stage of a general-line session: the evaluation already decided and recorded the version.
pub fn recorded_acceptance(evaluation: &Value) -> Value {
    json!({"qualified":evaluation["accepted"] == true,"version":evaluation["version"],"directory":evaluation["directory"],
        "admission":evaluation["admission"],
        "meaning":"a general-line submission is admitted at its evaluation (it beat its parent in one interleaved timing); nothing is qualified again"})
}

/// The resolution of a general-line session: every version and attempt its submissions became.
pub fn session_resolution(trials: &[Trial], trial_assets: Value) -> Value {
    let nodes: Vec<Value> = trials.iter().map(|t| json!({"iteration":t.iteration,"node":t.evaluation["node"],"accepted":t.evaluation["accepted"],"status":t.evaluation["status"],
        "parents":t.evaluation["parents"],"error":t.evaluation["error"]})).collect();
    let versions: Vec<&Value> = trials.iter().filter(|t| t.evaluation["accepted"] == true).map(|t| &t.evaluation["node"]).collect();
    json!({"status":if versions.is_empty() { "no_version" } else { "versions_accepted" },"versions":versions,"submissions":nodes,"trial_assets":trial_assets,
        "next":"the branch continues in a fresh session from its head and its notebook (a merge session first when its head has gains the main line has not taken)"})
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::score::{NormalizedTime, Score};

    fn recorded(scale: &str, finished: usize, g: u64) -> RecordedScore {
        RecordedScore { scale: scale.into(), score: Score { finished, normalized_time: NormalizedTime::from_billionths(g) }, cells: 66, beats_both: false, record: PathBuf::new() }
    }

    /// Every submission is evaluated under the development plan (its race 1 warm call and the run's timed hot calls
    /// per cell, by default 3, its variants at the first scale for their answers, no qualification and no profile), and
    /// the evaluation records the wall time of each step it ran, in order, a failed step included. The claim names the
    /// cell.
    #[test]
    fn submissions_are_evaluated_under_the_development_plan_with_step_times() {
        let plan = development(DEFAULT_TIMED_CALLS);
        assert!(plan.cell_calls == 4 && !plan.qualification && !plan.profile);
        assert_eq!(plan.variants, VariantRun::AnswersAtFirstScale);
        assert!(accepted_claim(&json!({}), 3).contains("one interleaved timing of the development plan (1 warm + 3 hot calls per cell, the median hot call the cell's time; more finished cells"));
        assert!(accepted_claim(&json!({}), 1).contains("(1 warm + 1 hot call per cell, the median hot call the cell's time;"));
        let mut steps = StepTimes::default();
        assert_eq!(steps.time("verus", || 7), 7);
        assert!(steps.time("interleaved_timing", || Err::<(), _>("refused")).is_err());
        let record = steps.record();
        let names: Vec<&str> = record.as_array().unwrap().iter().map(|s| s["step"].as_str().unwrap()).collect();
        assert_eq!(names, ["verus", "interleaved_timing"]);
        assert!(record[0]["elapsed_ms"].is_u64());
    }

    /// The development evaluation checks every variant with AST bytes of its own at the
    /// first scale, whatever the race finished; the final plan (at the evaluated scale) only the finished templates'.
    #[test]
    fn every_variant_runs_at_the_first_scale() {
        use super::super::timing::VariantOf;
        let variant = |template: &str, kind: &str| EncodedStatement {
            echo: String::new(),
            statement: EngineStatement { template: template.into(), variant: Some(VariantOf { id: format!("{template}-{kind}"), kind: kind.into() }), binding: "v0".into(), ast: vec![1] },
            translate_ns: 0,
            encode_ns: 0,
        };
        let variants = [variant("Q01", "wrapped_tables"), variant("Q09", "from_permutation"), variant("Q21", "between_expansion")];
        let finished = BTreeSet::from(["Q01".to_string()]);
        let names = |run: VariantRun| -> Vec<String> { selected_variants(run, &variants, &finished).iter().map(|s| s.name().to_string()).collect() };
        assert_eq!(names(development(DEFAULT_TIMED_CALLS).variants), ["Q01-wrapped_tables", "Q09-from_permutation", "Q21-between_expansion"], "every variant at the first scale");
        assert_eq!(names(super::super::protocol::FINAL.variants), ["Q01-wrapped_tables"], "the final plan: the finished templates' only");
    }

    /// An admission intent written before the current budget rule (with the old rule's `rule`, as the live run's records hold
    /// it) still reads: the field is ignored and the admission decides the current scale's rule.
    #[test]
    fn an_intent_with_the_old_budget_rule_still_reads() {
        let root = crate::controller::test_support::scratch_root("acceptance-old-intent");
        let file = root.join(ADMITTING_FILE);
        let old = json!({"evaluation":"/e","build":{},"evidence":[],"keep":{"k":1},"written_unix_ms":1,
            "rule":{"rule":"original_data_size","budget_bytes":1_100_693_130u64,"scale":"sf1","parent":null,"parent_serving_bytes":null,"within_required":false}});
        fs::create_dir_all(&root).unwrap();
        write_json_atomic(&file, &old).unwrap();
        let intent = AdmissionIntent::read(&file).unwrap().unwrap();
        assert_eq!((intent.evaluation, intent.keep), (PathBuf::from("/e"), json!({"k":1})));
        fs::remove_dir_all(&root).ok();
    }

    /// Done-check 3 (the main-line head after an interleaved timing): a branch version is timed against the main-line
    /// head only when its recorded score is better (more finished cells, or as many and a smaller normalized time) or
    /// the head has no score at that scale; the timing then decides.
    #[test]
    fn a_main_line_race_is_due_only_for_a_better_recorded_score() {
        let head = recorded("sf1", 40, 9_000_000_000);
        assert!(main_line_race_due(&recorded("sf1", 41, 99_000_000_000), Some(&head)), "more finished cells");
        assert!(main_line_race_due(&recorded("sf1", 40, 8_999_999_999), Some(&head)), "as many, faster");
        assert!(!main_line_race_due(&recorded("sf1", 40, 9_000_000_000), Some(&head)), "equal is not better");
        assert!(!main_line_race_due(&recorded("sf1", 39, 1), Some(&head)));
        assert!(!main_line_race_due(&recorded("sf10", 66, 1), Some(&head)), "scores at different scales are not compared");
        assert!(main_line_race_due(&recorded("sf10", 1, 1), None), "a head without a score at this scale is timed");
    }

    /// The main-line step after an acceptance: the acceptance race is adopted exactly when it timed the version against
    /// the main-line head itself at the current scale and timing binding; every other branch version is timed against
    /// the head when its recorded score is better; the head itself and merges keep their own paths.
    #[test]
    fn the_acceptance_race_decides_the_main_line_only_when_its_parent_is_the_head_here() {
        let at = |version: &str, scale: &str, binding: &str| TimedVersion { version: version.into(), scale: scale.into(), binding: binding.into() };
        let head = at("v004", "sf1", "v0");
        let head_score = recorded("sf1", 40, 9_000_000_000);
        let (better, worse) = (recorded("sf1", 41, 99_000_000_000), recorded("sf1", 39, 1));
        let step = |accepted: &str, merge: bool, score: &RecordedScore, raced: Option<TimedVersion>| {
            MainLineCase { accepted, merge, score, head_score: Some(&head_score), raced_against: raced.as_ref(), head: &head }.step()
        };
        // The parent was the head, here: the acceptance race decides, also against recorded scores from other windows.
        assert_eq!(step("v007", false, &better, Some(at("v004", "sf1", "v0"))), MainLineStep::AdoptAcceptanceRace);
        assert_eq!(step("v007", false, &worse, Some(at("v004", "sf1", "v0"))), MainLineStep::AdoptAcceptanceRace, "the same-window race decides");
        // The parent was another version (a branch head that is not the main-line head, a rebase onto a head that has
        // moved on since): timed when the recorded score is better.
        assert_eq!(step("v007", false, &better, Some(at("v003", "sf1", "v0"))), MainLineStep::Race);
        assert_eq!(step("v007", false, &worse, Some(at("v003", "sf1", "v0"))), MainLineStep::NotDue);
        // The head timed at another scale or binding, or no record of the race: never adopted.
        assert_eq!(step("v007", false, &better, Some(at("v004", "sf10", "v0"))), MainLineStep::Race);
        assert_eq!(step("v007", false, &better, Some(at("v004", "sf1", "v1"))), MainLineStep::Race);
        assert_eq!(step("v007", false, &better, None), MainLineStep::Race);
        assert_eq!(step("v007", false, &worse, None), MainLineStep::NotDue);
        // A merge becomes the head; the head itself stays.
        assert_eq!(step("v007", true, &worse, Some(at("v004", "sf1", "v0"))), MainLineStep::Merge);
        assert_eq!(step("v004", false, &better, Some(at("v003", "sf1", "v0"))), MainLineStep::AlreadyHead);
    }

    /// The acceptance race's record is read as the decision needs it: whom it timed against, where, that side's score
    /// and the verdict; a missing record is `None` and a malformed one a framework error.
    #[test]
    fn an_acceptance_race_record_reads_back() {
        let dir = crate::controller::test_support::scratch_root("engine-acceptance-race-outcome");
        fs::create_dir_all(&dir).unwrap();
        let file = dir.join("race.json");
        assert!(RaceOutcome::read(&file, "sf1").unwrap().is_none());
        let race = json!({"parent":"v000","candidate":"b1 iteration 1","binding":"v0","candidate_better":true,
            "parent_score":{"score":{"finished":6,"normalized_time":"11757.158031220"},"cells_total":66,"beats_both":false}});
        write_json_atomic(&file, &race).unwrap();
        let outcome = RaceOutcome::read(&file, "sf1").unwrap().unwrap();
        assert_eq!(outcome.against, TimedVersion { version: "v000".into(), scale: "sf1".into(), binding: "v0".into() });
        assert_eq!((outcome.against_score.score.finished, outcome.against_score.cells, outcome.against_score.record.as_path()), (6, 66, file.as_path()));
        assert_eq!(outcome.against_score.score.normalized_time, NormalizedTime::from_billionths(11_757_158_031_220));
        assert!(outcome.candidate_better);
        write_json_atomic(&file, &json!({"parent":"v000"})).unwrap();
        assert!(RaceOutcome::read(&file, "sf1").is_err());
    }

    /// A session's resolution lists every node its submissions became; its qualification stage only reports the
    /// admission the evaluation made.
    #[test]
    fn session_resolution_and_recorded_acceptance() {
        let trial = |iteration: u32, evaluation: Value| -> Trial {
            serde_json::from_value(json!({"iteration":iteration,"call_id":iteration,"candidate":{},"status":"evaluated","evaluation":evaluation})).unwrap()
        };
        let trials = [trial(1, json!({"accepted":false,"node":"b1-a001","status":"attempt"})), trial(2, json!({"accepted":true,"node":"v003","status":"version_accepted",
            "version":"v003","admission":"abc"}))];
        let resolution = session_resolution(&trials, json!({}));
        assert_eq!((resolution["status"].as_str(), resolution["versions"][0].as_str(), resolution["submissions"].as_array().unwrap().len()), (Some("versions_accepted"), Some("v003"), 2));
        assert_eq!(recorded_acceptance(&trials[1].evaluation)["qualified"], true);
        assert_eq!(recorded_acceptance(&trials[0].evaluation)["qualified"], false);
    }
}
