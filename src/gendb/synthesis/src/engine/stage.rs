//! Runs of the general line with several workloads: one engine for several workloads, each with its own crate
//! (`src/agent/**` with its module), library, scale, storage budget and saved answers. Two request forms
//! (`controller::request::WorkloadRequest::workload_set`), served by the same code:
//! - **stage runs** (`engine.stage`):
//!   the request's own workload is the goal (its score decides every submission); every `engine.stage.kept_workloads`
//!   entry is a kept workload, verified, timed against the parent and shown for every accepted version, never deciding
//!   (no guard). Each crate is frozen by `engine::submission::freeze_stage_engine`;
//! - **runs of several workloads** (`engine.workloads`): the
//!   request's own workload is the primary, every member has a role ([`MemberRole`]): `counted` workloads decide
//!   together through the combined score (`engine::score::CombinedScore`, the primary is always counted), `check`
//!   workloads are verified and answered on every submission before any timing (gating, never timed), `kept` workloads
//!   are as in a stage run. Each crate is frozen by `engine::submission::freeze_member_crate` (the shared engine, the
//!   workload's own module or the shared default module, and its storage family instances).
//!
//! There is no scale ladder in either: every workload stays at the last scale of its request, and its variants are
//! checked at its first scale.
//!
//! - [`StageRun`]: the workloads as one controller process prepares them (`engine::rounds::prepare_stage_inputs`), the
//!   primary (the stage's goal) first.
//! - [`StageRole`]: what an engine role of such a run knows: the crate it freezes and admits (its workload among every
//!   workload), its role, the seed, its workload's first scale, and for a session's role every other workload
//!   ([`MemberSide`]) its evaluations also verify, check or time, and admit. Another workload is reached through the
//!   session's own bench viewing that workload's library, capture and prepared statements ([`WorkloadBench::enter`]),
//!   with its own inputs, so every step of the general line (freeze, Verus, storages and budget, race, variants,
//!   admission) runs unchanged on it.
//! - A stage submission's kept workloads, after the goal's score decided it was better and its
//!   own variants agreed: [`evaluate_kept_workloads`] runs every kept workload's steps in order
//!   ([`EngineBench::evaluate_kept_side`]: whole-crate Verus, its storages, the storage policy and its budget, the
//!   interleaved timing against the parent's side of that workload at its scale, recorded and never deciding, then its
//!   variants' answers at its first scale), the first refusal refusing the submission (flagged for the operator when an answer
//!   was wrong); their statuses go to `<evaluation>/kept-workloads.json` as the evaluation record's `kept_workloads`
//!   (the stage fixture). A goal not better leaves every kept workload `not_run`.
//! - A submission of a run of several workloads: [`members`] (every workload's status with the step that
//!   refused it, the check workloads' answers, the counted workloads' races and the combined decision; the workloads fixture),
//!   under the request's one-engine rule when it sets one ([`one_engine`]: `engine.workloads.require_one_engine`).
//! - Admission: an accepted submission is admitted in every library: the primary first (its library version names the
//!   version), then every other crate, which must take the same library version ([`admit_in_lockstep`]: the libraries
//!   stay in lockstep, `vNNN` is version NNN + 1 of each).
//! - [`records`]: a version's folder (the shared code and every workload's module, each workload's records, its
//!   `version.json` `workloads`, its seed manifest; in a run of several workloads also the families, plans, the combined
//!   score and the one-engine record).
//! - [`root`]: `gendb engine prepare` of such a run: the root `v000` with one side per workload.
//! - [`view`]: the context's view of the workloads (a stage run's `stage`, the stage fixture; a run of several workloads'
//!   `workloads` and `combined_score`, the workloads fixture), refreshed before each call.
//!
//! Trust: nothing here is proof. Each crate is verified whole by Verus; the composition, the lockstep check, the combined
//! decision and the records are host code used for decisions and records.

pub mod members;
pub mod one_engine;
pub mod records;
pub mod root;
pub mod view;

use super::acceptance::{
    CheckedEngine, ENGINE_FINISHED_CHECKS_KIND, ENGINE_RACE_KIND, Failure, Parent, Runnable, StepTimes, lineage_parents, race_failure, race_summary,
};
use super::role::{EngineBench, EngineRoleConfig, EngineRoleMode, FirstScale, float_free, storage_inputs};
use super::rounds::{PreparedEngine, prepare_stage_inputs};
use super::sessions::SessionKind;
use super::submission::{Frozen, FrozenEngine, MemberCrate, StageCrate};
use super::tree::{RecordedScore, VersionTree};
use crate::controller::author::CandidateSubmission;
use crate::controller::records::{read_json, write_json_atomic};
use crate::controller::request::{MemberRole, Seed, SeedVersion, WorkloadForm, WorkloadRequest};
use crate::controller::workload_run::WorkloadError;
use crate::prompts::engine_contract::WorkloadRole;
use crate::query::QuerySession;
use crate::storage::capture::SharedCapture;
use crate::storage::policy::StoredDataPolicy;
use crate::tools::TrialVerification;
use crate::tools::bench::Workbench;
use gendb_artifacts::ContentId;
use gendb_artifacts::verus::{VERUS_ENGINE_LINEAGE_KIND, VerusEngineLineageV1};
use gendb_frontend::parser::SqlParser;
use gendb_verification::admission::{AdmissionError, FailureClass};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// Where a submission's crate of workload `name` (not the primary) is frozen beside the primary's: `<frozen>/kept/<name>`
/// in a stage run, `<frozen>/workloads/<name>` in a run of several workloads.
pub fn side_frozen_dir(form: WorkloadForm, frozen_dir: &Path, name: &str) -> PathBuf {
    frozen_dir.join(side_directory(form)).join(name)
}

/// Where one evaluation keeps workload `name`'s records (not the primary's): `<evaluation>/kept/<name>` in a stage run,
/// `<evaluation>/workloads/<name>` in a run of several workloads.
pub fn side_evaluation_dir(form: WorkloadForm, dir: &Path, name: &str) -> PathBuf {
    dir.join(side_directory(form)).join(name)
}

/// The directory of the other workloads' records beside the primary's ([`side_frozen_dir`], [`side_evaluation_dir`]).
fn side_directory(form: WorkloadForm) -> &'static str {
    match form {
        WorkloadForm::Workloads => super::tree::WORKLOADS_DIRECTORY,
        _ => "kept",
    }
}

/// [`side_frozen_dir`] of a stage run: `<frozen>/kept/<name>`.
pub fn kept_frozen_dir(frozen_dir: &Path, name: &str) -> PathBuf {
    side_frozen_dir(WorkloadForm::Stage, frozen_dir, name)
}

/// [`side_evaluation_dir`] of a stage run: `<evaluation>/kept/<name>`.
pub fn kept_evaluation_dir(dir: &Path, name: &str) -> PathBuf {
    side_evaluation_dir(WorkloadForm::Stage, dir, name)
}

/// The kept workloads' statuses of one evaluation of a stage run (`<evaluation>/kept-workloads.json`).
pub const KEPT_STATUS_FILE: &str = "kept-workloads.json";

/// How records name a workload's role: a stage run's `goal` and `kept` (the stage fixture), a run of several workloads' member
/// roles `counted`, `check` and `kept` (the workloads fixture).
pub fn role_name(form: WorkloadForm, primary: bool, role: MemberRole) -> &'static str {
    match form {
        WorkloadForm::Workloads => role.name(),
        _ if primary => WorkloadRole::Goal.name(),
        _ => WorkloadRole::Kept.name(),
    }
}

// ------------------------------------------------------------------------------------------------ the run's workloads

/// One workload of a run of several workloads, prepared at its last scale (no ladder).
pub struct StageWorkload {
    /// Its name: its module directory `workloads/<name>/` and its key in records.
    pub name: String,
    /// What it decides (the stage's goal is counted, its kept workloads kept).
    pub role: MemberRole,
    /// The primary workload: the run's own request (a stage run's goal).
    pub primary: bool,
    /// Its request: the run's request for the primary, the workload's request file for every other (its library,
    /// storage policy, scales and saved answers).
    pub request: WorkloadRequest,
    /// Its inputs at its last scale (the primary's statements under `engine/scales/<s>/`, every other's under
    /// `engine/kept/<name>/scales/<s>/` in a stage run, `engine/workloads/<name>/scales/<s>/` in a run of several
    /// workloads), carrying the run's rule set.
    pub prepared: PreparedEngine,
    /// Its first scale, where its submissions' variants are checked, when that is not its last.
    pub first_scale: Option<FirstScale>,
    /// A run of several workloads: the seed of its side of the root (`None`: the primary seed out of the box, else
    /// version 0). A stage run's workloads carry none (the stage seed is the run's).
    pub seed: Option<Seed>,
    /// A run of several workloads: its plain flat storages `(name, package)` in table order (the sources of every family
    /// instance it composes; `engine::submission::members::plain_flat_storages`). Empty in a stage run.
    pub flat_storages: Vec<(String, ContentId)>,
}

impl StageWorkload {
    /// The scale it is timed (or checked) at.
    pub fn scale(&self) -> String {
        self.prepared.inputs.general.as_ref().map_or_else(String::new, |g| g.scale.name.clone())
    }

    /// The scale its variants are checked at: its first scale, else its own.
    pub fn first_scale_name(&self) -> String {
        first_scale_name(self.first_scale.as_ref()).unwrap_or_else(|| self.scale())
    }

    /// Its role in the contract files of a stage workload (`Goal` for the primary, whose catalog is the contract's own).
    pub fn contract_role(&self) -> WorkloadRole {
        if self.primary { WorkloadRole::Goal } else { WorkloadRole::Kept }
    }
}

/// The scale name of a first scale's inputs.
fn first_scale_name(first: Option<&FirstScale>) -> Option<String> {
    first.and_then(|f| f.inputs.general.as_ref().map(|g| g.scale.name.clone()))
}

/// A run of several workloads as one controller process prepares it.
pub struct StageRun {
    /// `Stage` or `Workloads` (`WorkloadForm::One` is not such a run).
    pub form: WorkloadForm,
    /// The primary workload (a stage run's goal).
    pub primary: StageWorkload,
    /// Every other workload, in request order.
    pub others: Vec<StageWorkload>,
    /// The primary seed: a stage run's seed version (`Seed::Run`), a run of several workloads' `engine.workloads.seed`.
    pub seed: Option<Seed>,
    /// A run of several workloads: only a version that is one engine can be accepted (`engine.workloads.require_one_engine`;
    /// [`one_engine`]). Always false in a stage run.
    pub require_one_engine: bool,
}

impl StageRun {
    /// Prepare every workload (`engine::rounds::prepare_stage_inputs`: the primary under `engine/scales/<s>/`, every other
    /// under its own directory, records reused on a relaunch). A request of one workload is refused; so is a run of
    /// several workloads with more than one branch (its main-line decision across workloads is the acceptance's own,
    /// made on one line of versions).
    pub async fn prepare(request: &WorkloadRequest, root: &Path, parser: &SqlParser, framework_executable: &Path) -> Result<Self, WorkloadError> {
        let set = request.workload_set()?;
        if set.form == WorkloadForm::One {
            return Err(WorkloadError::invalid("engine: a run of several workloads needs engine.stage or engine.workloads"));
        }
        let engine = request.engine()?;
        if set.form == WorkloadForm::Workloads && engine.branches.unwrap_or(1) > 1 {
            return Err(WorkloadError::invalid(
                "engine.workloads: a run of several workloads searches on one line of versions (engine.branches 1): each accepted version beats its parent, the main-line head, by the combined score, so no main-line race across workloads is needed",
            ));
        }
        let inputs = prepare_stage_inputs(request, &set, root, parser, framework_executable).await?;
        let mut workloads = inputs.workloads.into_iter().map(|w| StageWorkload {
            primary: w.primary,
            name: w.name,
            role: w.role,
            request: w.request,
            prepared: w.prepared,
            first_scale: w.first_scale,
            seed: w.seed,
            flat_storages: w.flat_storages,
        });
        let primary = workloads.next().ok_or_else(|| WorkloadError::invalid("engine: a run of several workloads without its primary workload"))?;
        Ok(Self { form: set.form, primary, others: workloads.collect(), seed: set.seed, require_one_engine: engine.requires_one_engine() })
    }

    /// Every workload, the primary first.
    pub fn workloads(&self) -> impl Iterator<Item = &StageWorkload> {
        std::iter::once(&self.primary).chain(&self.others)
    }

    /// Every workload's name, the primary first.
    pub fn names(&self) -> Vec<String> {
        self.workloads().map(|w| w.name.clone()).collect()
    }

    /// The workload `name`.
    pub fn workload(&self, name: &str) -> Option<&StageWorkload> {
        self.workloads().find(|w| w.name == name)
    }

    /// How records name the role of `w` ([`role_name`]).
    pub fn role_name(&self, w: &StageWorkload) -> &'static str {
        role_name(self.form, w.primary, w.role)
    }

    /// A stage run's seed version (its run's accepted version every side starts from).
    pub fn stage_seed(&self) -> Result<&SeedVersion, AdmissionError> {
        match &self.seed {
            Some(Seed::Run { version, .. }) => Ok(version),
            _ => Err(AdmissionError::tool("a stage run without its seed version")),
        }
    }

    /// The seed version's folder (`<run>/engine/versions/<version>`) of a stage run.
    pub fn seed_directory(&self) -> Result<PathBuf, AdmissionError> {
        Ok(self.stage_seed()?.directory())
    }

    /// The role over the one workload `name` (framework work: a final evaluation, a stage root's side): its crate (the
    /// manifest has an entry for every workload) and first scale, no other workload.
    pub fn workload_role(&self, name: &str) -> StageRole {
        self.role_of(name, self.names())
    }

    /// The role of the root's side of workload `name` (`stage::root`): in a run of several workloads the side's
    /// workspace names only its own workload (`MemberCrate { workloads: [name] }`); in a stage run the stage-form
    /// manifest names every workload ([`StageRun::workload_role`]).
    pub fn side_role(&self, name: &str) -> StageRole {
        match self.form {
            WorkloadForm::Workloads => self.role_of(name, vec![name.to_string()]),
            _ => self.workload_role(name),
        }
    }

    /// The role over `name` whose freeze expects the manifest entries `workloads`.
    fn role_of(&self, name: &str, workloads: Vec<String>) -> StageRole {
        let w = self.workload(name);
        StageRole {
            form: self.form,
            workload: name.to_string(),
            role: w.map_or(MemberRole::Counted, |w| w.role),
            primary: self.primary.name.clone(),
            workloads,
            seed: self.seed.clone(),
            first_scale: w.and_then(|w| w.first_scale.clone()),
            flat_storages: w.map(|w| w.flat_storages.clone()).unwrap_or_default(),
            seeds: self.seeds(),
            sides: vec![],
            require_one_engine: self.require_one_engine,
        }
    }

    /// Each workload's seed as the request gives it, by name (`null` without one; the primary's is the primary seed).
    fn seeds(&self) -> Value {
        Value::Object(self.workloads().map(|w| (w.name.clone(), if w.primary { json!(self.seed) } else { json!(w.seed) })).collect())
    }

    /// The role of a session: the primary's crate, and every other workload reached through the session's bench.
    pub fn session_role(&self, engine_dir: &Path) -> StageRole {
        let sides = self
            .others
            .iter()
            .map(|w| MemberSide {
                name: w.name.clone(),
                role: w.role,
                config: EngineRoleConfig { engine_dir: engine_dir.to_path_buf(), inputs: w.prepared.inputs.clone(), mode: EngineRoleMode::Framework },
                view: WorkloadBench::of(&w.request, &w.prepared),
                stage: self.workload_role(&w.name),
            })
            .collect();
        StageRole { sides, ..self.workload_role(&self.primary.name) }
    }
}

/// Another handle on the same prepared inputs and capture (the primary's inputs are a session's own): every part shared
/// or copied, nothing prepared again.
pub fn share_prepared(prepared: &PreparedEngine) -> PreparedEngine {
    let data = &prepared.data;
    PreparedEngine {
        inputs: prepared.inputs.clone(),
        data: crate::controller::workload_run::preparation::PreparedData {
            source: data.source.clone(),
            capture: data.capture.clone(),
            report: data.report.clone(),
            preparation_ns: data.preparation_ns,
            record: data.record.clone(),
        },
    }
}

/// The run summary's part of a run of several workloads: every workload with its role, scale, library and the main-line
/// head's recorded score on it (a stage run's `stage`; a run of several workloads' `workloads`, with the head's
/// combined score).
pub fn run_summary(run: &StageRun, engine_dir: &Path) -> Value {
    let tree = VersionTree::read(engine_dir).unwrap_or_default();
    let head = tree.main_line_head().map(String::from);
    let workloads: Vec<Value> = run
        .workloads()
        .map(|w| {
            let score = head.as_deref().and_then(|h| tree.workload_score(h, &w.name)).map(|s| json!(s.score));
            json!({"name":w.name,"role":run.role_name(w),"scale":w.scale(),"first_scale":w.first_scale_name(),"library":w.request.library,"head_score":score})
        })
        .collect();
    match run.form {
        WorkloadForm::Workloads => json!({"primary":run.primary.name,"seed":run.seed,"head":head,"workloads":workloads,
            "combined_score":head.as_deref().and_then(|h| tree.combined_score(h)),"combined_rule":super::score::COMBINED_RULE,
            "meaning":"a run of several workloads: the combined score over the counted workloads decided every version; every check workload was verified and answered, every kept workload timed and shown, never deciding"}),
        _ => json!({"goal":run.primary.name,"seed":run.stage_seed().ok(),"head":head,"workloads":workloads,
            "meaning":"a stage run: the goal's score decided every version; every kept workload was verified, timed against the parent and is shown, never deciding"}),
    }
}

// ------------------------------------------------------------------------------------------------ roles

/// What an engine role of a run of several workloads knows (`engine::role::EngineAuthorRole::with_stage`).
#[derive(Clone)]
pub struct StageRole {
    pub form: WorkloadForm,
    /// The workload whose crate this role freezes and admits, and its role.
    pub workload: String,
    pub role: MemberRole,
    /// The primary workload (a stage run's goal).
    pub primary: String,
    /// The workloads the manifest has an entry for, which this role's freeze expects, the primary first: every
    /// workload, or (the root's side of a run of several workloads) only this one.
    pub workloads: Vec<String>,
    /// The primary seed.
    pub seed: Option<Seed>,
    /// Its workload's first scale (variants), when not its own scale.
    pub first_scale: Option<FirstScale>,
    /// A run of several workloads: its workload's plain flat storages (the family instances' sources).
    pub flat_storages: Vec<(String, ContentId)>,
    /// Every workload's seed as the request gives it, by name (the contract's `workloads.json`).
    pub seeds: Value,
    /// A session's role: every other workload; empty for a role over one workload.
    pub sides: Vec<MemberSide>,
    /// Only a version that is one engine can be accepted ([`StageRun::require_one_engine`]).
    pub require_one_engine: bool,
}

impl StageRole {
    /// Freeze this role's crate from `context` (`engine::submission::freeze_stage_engine` in a stage run,
    /// `freeze_member_crate` in a run of several workloads).
    pub fn freeze(&self, context: &super::submission::EngineFreeze<'_>, frozen_dir: &Path, submission: &CandidateSubmission) -> Result<Frozen, AdmissionError> {
        match self.form {
            WorkloadForm::Workloads => {
                let member = MemberCrate { workload: &self.workload, workloads: &self.workloads, flat_storages: &self.flat_storages };
                super::submission::freeze_member_crate(context, &member, frozen_dir, submission)
            }
            _ => super::submission::freeze_stage_engine(context, &StageCrate { workload: &self.workload, workloads: &self.workloads }, frozen_dir, submission),
        }
    }

    /// The other workload `name`.
    pub fn side(&self, name: &str) -> Option<&MemberSide> {
        self.sides.iter().find(|k| k.name == name)
    }

    /// A run of several workloads (`engine.workloads`), not a stage run.
    pub fn is_members(&self) -> bool {
        self.form == WorkloadForm::Workloads
    }

    /// The other workloads of role `role`, in order.
    pub fn sides_of(&self, role: MemberRole) -> impl Iterator<Item = &MemberSide> {
        self.sides.iter().filter(move |s| s.role == role)
    }

    /// Every workload's name and role, this role's first.
    pub fn members(&self) -> Vec<(String, MemberRole)> {
        std::iter::once((self.workload.clone(), self.role)).chain(self.sides.iter().map(|s| (s.name.clone(), s.role))).collect()
    }

    /// How records name the role of workload `name` of this run ([`role_name`]).
    pub fn role_name_of(&self, name: &str) -> &'static str {
        let role = if name == self.workload { self.role } else { self.side(name).map_or(MemberRole::Kept, |s| s.role) };
        role_name(self.form, name == self.primary, role)
    }
}

/// Another workload as a session's role reaches it: its role, its inputs (the role configuration of its framework
/// work), the parts of the session bench that are its own, and its crate.
#[derive(Clone)]
pub struct MemberSide {
    pub name: String,
    pub role: MemberRole,
    pub config: EngineRoleConfig,
    pub view: WorkloadBench,
    pub stage: StageRole,
}

/// The parts of a session's bench that belong to one workload: its library, storage policy, capture and prepared
/// statements (whose first gives the bench its schema and engine runner).
#[derive(Clone)]
pub struct WorkloadBench {
    pub library: PathBuf,
    pub storage_policy: StoredDataPolicy,
    pub capture: SharedCapture,
    pub statements: Vec<Arc<QuerySession>>,
}

impl WorkloadBench {
    /// The parts of the workload of `request` prepared as `prepared`.
    pub fn of(request: &WorkloadRequest, prepared: &PreparedEngine) -> Self {
        Self {
            library: request.library.clone(),
            storage_policy: request.storage_policy.clone(),
            capture: prepared.data.capture.clone(),
            statements: prepared.inputs.sessions.iter().map(|(_, s)| s.clone()).collect(),
        }
    }

    /// Run `work` with `bench` viewing this workload (its library, storage policy, capture and statements), then give
    /// the bench its own parts back, whatever `work` returns. Everything else of the bench stays shared: the workspace,
    /// the session's checked storages (keyed by their sources) and trial assets, the host locks and the parser.
    pub fn enter<T>(&self, bench: &mut Workbench, work: impl FnOnce(&mut Workbench) -> T) -> T {
        let own = self.exchange(bench);
        let outcome = work(bench);
        own.exchange(bench);
        outcome
    }

    /// Give `bench` these parts; returns the parts it had.
    fn exchange(&self, bench: &mut Workbench) -> WorkloadBench {
        WorkloadBench {
            library: std::mem::replace(&mut bench.config.library, self.library.clone()),
            storage_policy: std::mem::replace(&mut bench.config.storage_policy, self.storage_policy.clone()),
            capture: std::mem::replace(&mut bench.capture, self.capture.clone()),
            statements: std::mem::replace(&mut bench.statements, self.statements.clone()),
        }
    }
}

// ------------------------------------------------------------------------------------------------ a submission's other workloads

/// What one other workload's steps of an accepted submission produced for its admission:
/// its frozen crate, its evaluation directory, its whole-crate build, the evidence of its admission and its record.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct MemberKeep {
    pub name: String,
    pub frozen: PathBuf,
    pub evaluation: PathBuf,
    pub build: Value,
    pub evidence: Vec<(String, Value)>,
    /// `role`, `scale`, `race` (its race report, when timed), `race_summary`, `score` (its recorded score there, when
    /// timed), `check` (a check workload's answers), `finished_checks`, `storage_policy_at_evaluation`, `storage`,
    /// `build`, `crate_version`, `candidate_cells`, `parent`, `module_report`, `member` (a run of several workloads' crate
    /// record), and the admission once made (`admission`).
    pub record: Value,
}

/// A kept workload's status in one evaluation of a stage run (the stage fixture, the evaluation record's `kept_workloads[]`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct KeptStatus {
    pub name: String,
    /// `not_run` (the goal decided first), `refused` (one of its steps refused the submission) or `timed` (verified,
    /// its storages checked and timed against the parent's side).
    pub status: String,
    /// The refusal, else `None`.
    pub reason: Option<String>,
    /// Its race report when timed.
    pub race: Option<PathBuf>,
}

impl KeptStatus {
    fn not_run(name: &str) -> Self {
        Self { name: name.into(), status: "not_run".into(), reason: None, race: None }
    }
}

/// The kept workloads' statuses of the evaluation in `dir` (every one `not_run` when none of them ran: the goal was not
/// better, or the submission was refused before).
pub fn kept_statuses(dir: &Path, names: &[String]) -> Vec<KeptStatus> {
    read_json(&dir.join(KEPT_STATUS_FILE)).unwrap_or_else(|_| names.iter().map(|n| KeptStatus::not_run(n)).collect())
}

/// After the goal's score decided the submission was better and its own variants agreed: every
/// kept workload (`names`, in order) through `evaluate` (its steps; real: [`EngineBench::evaluate_kept_side`]). A slower
/// or unfinished kept timing never refuses (no guard); the first refusal refuses the submission (its reason names the
/// workload; flagged when an answer was wrong) and the later workloads stay `not_run`. The statuses are written to
/// `<dir>/kept-workloads.json` after every workload, so the evaluation record names them whatever the outcome.
pub(super) fn evaluate_kept_workloads(names: &[String], dir: &Path, mut evaluate: impl FnMut(&str) -> Result<MemberKeep, Failure>) -> Result<Vec<MemberKeep>, Failure> {
    let mut statuses: Vec<KeptStatus> = names.iter().map(|n| KeptStatus::not_run(n)).collect();
    let write = |statuses: &[KeptStatus]| write_json_atomic(&dir.join(KEPT_STATUS_FILE), &statuses).map_err(AdmissionError::tool);
    fs::create_dir_all(dir).map_err(AdmissionError::tool)?;
    write(&statuses)?;
    let mut kept = vec![];
    for (index, name) in names.iter().enumerate() {
        match evaluate(name) {
            Ok(keep) => {
                statuses[index] = KeptStatus { name: name.clone(), status: "timed".into(), reason: None, race: keep.record["race"].as_str().map(PathBuf::from) };
                write(&statuses)?;
                kept.push(keep);
            }
            Err(Failure::Candidate { reason, flagged, score }) => {
                statuses[index] = KeptStatus { name: name.clone(), status: "refused".into(), reason: Some(reason.clone()), race: None };
                write(&statuses)?;
                return Err(Failure::Candidate { reason, flagged, score });
            }
            Err(framework) => return Err(framework),
        }
    }
    Ok(kept)
}

/// The admission of every other crate of an accepted submission: each admitted
/// in its library by `admit` (once: adopted when its library holds it), after the primary's admission as library
/// version `primary_library_version`. Every other library must admit it as that same library version (the libraries
/// stay in lockstep); otherwise it is a framework error (the caller flags it for the operator). Returns each workload's
/// admission record.
pub(super) fn admit_in_lockstep(primary_library_version: u64, others: &[MemberKeep], mut admit: impl FnMut(&MemberKeep) -> Result<Value, AdmissionError>) -> Result<Vec<(String, Value)>, AdmissionError> {
    let mut admissions = vec![];
    for keep in others {
        let admission = admit(keep)?;
        let version = admission["library_version"].as_u64().ok_or_else(|| AdmissionError::tool(format!("workload {}: an admission without its library version", keep.name)))?;
        if version != primary_library_version {
            return Err(AdmissionError::tool(format!(
                "library_lockstep_broken: workload {} admitted the version as its library's version {version}, the goal's library as {primary_library_version}; every library of a stage run admits every accepted version, in the same order",
                keep.name
            )));
        }
        admissions.push((keep.name.clone(), admission));
    }
    Ok(admissions)
}

/// The lineage of a submission's admission in any library: its branch and kind, and how its parents are found
/// (`engine::acceptance::lineage_parents` over that library's versions).
#[derive(Clone, Debug)]
pub(super) struct LineageOf {
    pub branch: String,
    pub kind: String,
    pub merge_from: Option<String>,
    pub session_kind: SessionKind,
}

impl Failure {
    /// The same failure with its reason naming the workload `name`, and `score` (the primary's score when it was timed:
    /// an attempt keeps it) when given.
    pub(super) fn of_workload(self, name: &str, score: Option<&RecordedScore>) -> Failure {
        match self {
            Failure::Candidate { reason, flagged, score: own } => Failure::Candidate { reason: format!("workload {name}: {reason}"), flagged, score: score.cloned().or(own) },
            Failure::Framework(error) => Failure::Framework(AdmissionError::new(error.class, format!("workload {name}: {}", error.message))),
        }
    }

    /// [`Failure::of_workload`] after the goal's score decided (a stage run's kept workload).
    pub(super) fn of_kept(self, name: &str, score: &RecordedScore) -> Failure {
        self.of_workload(name, Some(score))
    }
}

impl EngineBench<'_> {
    /// Run `work` on the other workload `side`: the session's bench viewing its library, capture and statements
    /// ([`WorkloadBench::enter`]), with its inputs and its crate.
    pub(super) fn on_side<T>(&mut self, side: &MemberSide, work: impl FnOnce(&mut EngineBench<'_>) -> T) -> T {
        let builds = &mut *self.builds;
        side.view.enter(self.bench, |bench| work(&mut EngineBench { bench, config: &side.config, builds, stage: Some(&side.stage) }))
    }

    /// Freeze every other workload's crate of a submission beside the primary's,
    /// from the same workspace and manifest: `Ok(None)` when every one froze; `Ok(Some((workload, refusal)))` for the
    /// first refused (the submission is an attempt); `Err` for a tool failure.
    pub(super) fn freeze_side_crates(&mut self, workspace: &Path, frozen_dir: &Path, submission: &CandidateSubmission) -> Result<Option<(String, AdmissionError)>, AdmissionError> {
        let Some(stage) = self.stage else { return Ok(None) };
        for side in &stage.sides {
            let dir = side_frozen_dir(stage.form, frozen_dir, &side.name);
            if let Some(parent) = dir.parent() {
                fs::create_dir_all(parent).map_err(AdmissionError::tool)?;
            }
            match self.on_side(side, |other| other.freeze_submission(workspace, &dir, submission)) {
                Ok(_) => {}
                Err(error) if error.class == FailureClass::ToolFailure => return Err(error),
                Err(error) => return Ok(Some((side.name.clone(), error))),
            }
        }
        Ok(None)
    }

    /// One kept workload's steps of a submission the decision accepted (module documentation), in
    /// the evaluation directory of the workload: its crate frozen beside the primary's is verified whole, its storages
    /// resolved and checked (policy, single copy, its budget rule), timed interleaved against the parent's side of the
    /// workload at its scale (recorded, never deciding), and its variants' answers checked at its first scale. A
    /// candidate's failure names the workload; a wrong answer is flagged; an admitted parent's failure is an incident.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn evaluate_kept_side(&mut self, side: &MemberSide, frozen_dir: &Path, dir: &Path, parent: &Parent, lineage: &LineageOf, tree: &VersionTree, steps: &mut StepTimes) -> Result<MemberKeep, Failure> {
        let form = side.stage.form;
        let frozen = side_frozen_dir(form, frozen_dir, &side.name);
        let evaluation = side_evaluation_dir(form, dir, &side.name);
        fs::create_dir_all(&evaluation).map_err(AdmissionError::tool)?;
        let engine: FrozenEngine = read_json(&frozen.join("candidate.json")).map_err(AdmissionError::tool)?;
        let engine_dir = self.config.engine_dir.clone();
        let name = side.name.clone();
        self.on_side(side, |kept| kept.kept_steps(&name, &engine, &frozen, &evaluation, parent, lineage, tree, &engine_dir, steps))
    }

    /// [`EngineBench::evaluate_kept_side`] on the kept workload's view of the bench.
    #[allow(clippy::too_many_arguments)]
    fn kept_steps(&mut self, name: &str, engine: &FrozenEngine, frozen: &Path, dir: &Path, parent: &Parent, lineage: &LineageOf, tree: &VersionTree, engine_dir: &Path, steps: &mut StepTimes) -> Result<MemberKeep, Failure> {
        let general = self.inputs().general.clone().ok_or_else(|| AdmissionError::tool(format!("workload {name}: no general inputs")))?;
        let locks = self.bench.config.locks.clone();
        let build = steps.time(format!("{name}:verus"), || self.builds.compile(&locks, engine, frozen, &dir.join("verus-build"), true))?;
        let rule = self.budget_rule()?;
        let (storages, storage_policy, parent_run) = steps.time(format!("{name}:storages"), || -> Result<_, Failure> {
            let storages = self.storages(engine, frozen, dir, TrialVerification::WholeCrate)?;
            let storage_policy = self.check_storage_policy(engine, frozen, &storages, &rule)?;
            let parent_run = self.admitted_runnable(&parent.id, &dir.join("parent-storages")).map_err(Failure::Framework)?;
            Ok((storages, storage_policy, parent_run))
        })?;
        let candidate_run = Runnable { label: format!("{} ({name})", parent_run.label.replace(&parent.id, "candidate")), library: build.library.clone(), inputs: storage_inputs(&storages) };
        let parent_record = records::workload_cells(engine_dir, &parent.id, name, &general.scale.name);
        let plan = self.submission_plan();
        let raced = steps.time(format!("{name}:interleaved_timing"), || self.race_runnables(&parent_run, &candidate_run, parent_record.as_deref(), plan.cell_calls, &dir.join("race")));
        let report = raced.map_err(|error| race_failure(engine_dir, &parent.id, error))?;
        let race_file = dir.join("race.json");
        write_json_atomic(&race_file, &json!(report)).map_err(AdmissionError::tool)?;
        let score = RecordedScore::of(&general.scale.name, &report.candidate_score, &race_file);
        let subject = CheckedEngine { library: &build.library, inputs: &candidate_run.inputs, frozen: Some((&engine.storage_uses, frozen)) };
        let checks = steps.time(format!("{name}:variants"), || self.check_finished_templates(&plan, &subject, &report.candidate_score, dir))?;
        let store = self.bench.store()?;
        let parents = lineage_parents(tree, &store, parent, lineage.merge_from.as_deref(), lineage.session_kind)?;
        let lineage = VerusEngineLineageV1 { branch: lineage.branch.clone(), kind: lineage.kind.clone(), parents };
        let summary = float_free(&race_summary(&report, &race_file));
        let evidence = vec![(VERUS_ENGINE_LINEAGE_KIND.to_string(), json!(lineage)), (ENGINE_RACE_KIND.to_string(), summary.clone()), (ENGINE_FINISHED_CHECKS_KIND.to_string(), float_free(&checks))];
        let mut record = json!({"role":"kept","scale":general.scale.name,"race":race_file,"race_summary":summary,"score":score,"finished_checks":checks,
            "storage_policy_at_evaluation":storage_policy,"storage":{"assets":storages.iter().map(super::role::storage_view).collect::<Vec<_>>(),"budget_rule":rule},
            "build":build.record,"crate_version":super::submission::engine_version_id(engine, frozen)?,"parent":parent.id,
            "candidate_cells":report.candidate_score.cells.iter().map(|c| super::score::CellResult { template: c.template.clone(), workers: c.workers, status: c.status }).collect::<Vec<_>>(),
            "module_report":engine.workload.as_ref().map(|w| w.module_report.clone())});
        // A run of several workloads: its crate's record (module, families, inherited storages, plans; the workloads fixture's `general`).
        if let Some(member) = engine.workload.as_ref().and_then(|w| w.member.as_ref()) {
            record["member"] = json!(member);
        }
        Ok(MemberKeep { name: name.to_string(), frozen: frozen.to_path_buf(), evaluation: dir.to_path_buf(), build: build.record, evidence, record })
    }

    /// Admit the other workload `keep` in its library, once: the library's
    /// admission of the same frozen crate when it holds one, else the admission now (`EngineBench::admit_from_intent`).
    /// Returns the admission record with `library_version`.
    pub(super) fn admit_side(&mut self, keep: &MemberKeep) -> Result<Value, AdmissionError> {
        let stage = self.stage.ok_or_else(|| AdmissionError::tool("another workload's admission outside a run of several workloads"))?;
        let side = stage.side(&keep.name).ok_or_else(|| AdmissionError::tool(format!("{} is not a workload of this run", keep.name)))?;
        let engine: FrozenEngine = read_json(&keep.frozen.join("candidate.json")).map_err(AdmissionError::tool)?;
        let intent = super::acceptance::AdmissionIntent { evaluation: keep.evaluation.clone(), build: keep.build.clone(), evidence: keep.evidence.clone(), keep: Value::Null,
            written_unix_ms: crate::controller::records::now_unix_ms() };
        self.on_side(side, |other| other.admit_from_intent(&keep.frozen, &engine, &intent))
    }
}

/// A session's workspace of a run of several workloads beyond the general line's seeding
/// (`engine::sessions::seed_session_workspace`), recorded in the seed record as `stage`:
/// - a stage run: the seed version's workload modules (`code/workloads/<name>/**` as `engine/workloads/<name>/**`,
///   writable) and the seed run's history (`stage1/` of the root's folder, read-only);
/// - a run of several workloads: the version's modules (`code/workloads/**`, the own modules and the default module, as
///   `engine/workloads/**`), its storage families (`code/families/<family>/**` as `storages/<family>/**`) and plans
///   (`code/plans/**` as `engine/plans/**`), all writable, with the manifest's family sources named at their workspace
///   paths; and the root's other sides (`root-sides/` of the root's folder, read-only).
pub fn seed_stage_workspace(workspace: &Path, engine_dir: &Path, seed_version: &str, form: WorkloadForm, record: &mut Value) -> Result<(), AdmissionError> {
    use super::role::{copy_tree, make_writable};
    use super::submission::members::{VERSION_FAMILIES_DIRECTORY, WORKSPACE_FAMILIES_DIRECTORY};
    use super::submission::{CRATE_DIRECTORY, PLANS_DIRECTORY, WORKLOADS_DIRECTORY};
    let seed = super::tree::node_directory(engine_dir, seed_version, true);
    // A seeding that a stop interrupted is redone over what it left (its copies keep the frozen read-only modes).
    let writable_copy = |from: &Path, to: &Path| -> Result<bool, AdmissionError> {
        if !from.is_dir() {
            return Ok(false);
        }
        if to.is_dir() {
            make_writable(to)?;
        }
        copy_tree(from, to, false)?;
        make_writable(to)?;
        Ok(true)
    };
    let read_only_copy = |from: &Path, to: &Path| -> Result<bool, AdmissionError> {
        if !from.is_dir() {
            return Ok(false);
        }
        if to.is_dir() {
            make_writable(to)?;
        }
        copy_tree(from, to, true)?;
        Ok(true)
    };
    let modules = seed.join("code").join(super::tree::WORKLOADS_DIRECTORY);
    let target = workspace.join(CRATE_DIRECTORY).join(WORKLOADS_DIRECTORY);
    let has_modules = writable_copy(&modules, &target)?;
    let root_folder = super::tree::node_directory(engine_dir, super::tree::ROOT_VERSION, true);
    if form != WorkloadForm::Workloads {
        let history = root_folder.join(root::STAGE_ONE_DIRECTORY);
        let history_copy = workspace.join(root::STAGE_ONE_DIRECTORY);
        let has_history = read_only_copy(&history, &history_copy)?;
        record["stage"] = json!({"workload_modules":has_modules.then_some(&target),"stage1":has_history.then_some(&history_copy),
            "meaning":"a stage run's session: every workload's module of the seed version under engine/workloads/<name>/, and the seed run's version tree and findings under stage1/ (read-only)"});
        return Ok(());
    }
    let families = workspace.join(WORKSPACE_FAMILIES_DIRECTORY);
    let has_families = writable_copy(&seed.join("code").join(VERSION_FAMILIES_DIRECTORY), &families)?;
    let plans = workspace.join(CRATE_DIRECTORY).join(PLANS_DIRECTORY);
    let has_plans = writable_copy(&seed.join("code").join(PLANS_DIRECTORY), &plans)?;
    // The manifest names each family's source as the workspace holds it (the version's names it under code/).
    let manifest_file = workspace.join(super::submission::MANIFEST_FILE);
    let manifest: super::submission::EngineManifest = read_json(&manifest_file).map_err(AdmissionError::tool)?;
    let manifest = super::submission::EngineManifest { families: manifest.families.iter().map(|f| super::submission::FamilyDeclaration {
        name: f.name.clone(), source: Path::new(WORKSPACE_FAMILIES_DIRECTORY).join(&f.name).join(crate::storage::family::FAMILY_MANIFEST_FILE) }).collect(), ..manifest };
    write_json_atomic(&manifest_file, &manifest).map_err(AdmissionError::tool)?;
    let sides = root_folder.join(root::ROOT_SIDES_DIRECTORY);
    let sides_copy = workspace.join(root::ROOT_SIDES_DIRECTORY);
    let has_sides = read_only_copy(&sides, &sides_copy)?;
    record["stage"] = json!({"workload_modules":has_modules.then_some(&target),"families":has_families.then_some(&families),"plans":has_plans.then_some(&plans),
        "root_sides":has_sides.then_some(&sides_copy),
        "meaning":"a run of several workloads' session: the version's modules under engine/workloads/ (own modules and the default module), its storage families under storages/<family>/ and plans under engine/plans/ (writable), and the root's other sides under root-sides/ (read-only)"});
    Ok(())
}

/// The contract of a stage session's role (`prompts::engine_contract::write_stage_engine_contract`): the goal workload
/// from the role's own inputs, capture and library, every kept workload from its own (its storages' interfaces copied
/// under `<root>/admitted-storages/`).
pub(super) fn stage_contract(bench: &EngineBench<'_>, root: &Path, stage: &StageRole) -> Result<crate::prompts::engine_contract::StageContract, AdmissionError> {
    use crate::prompts::engine_contract::{StageContract, WorkloadContract};
    let open = |library: &Path| gendb_artifacts::ObjectStore::open_existing(library).map_err(|e| AdmissionError::tool(format!("{}: {e}", library.display())));
    let first = |own: &EngineRoleConfig, first: Option<&FirstScale>| first_scale_name(first).or_else(|| own.inputs.general.as_ref().map(|g| g.scale.name.clone())).unwrap_or_default();
    let library = &bench.bench.config.library;
    let mut workloads = vec![WorkloadContract::prepare(root, &stage.workload, WorkloadRole::Goal, bench.inputs(), &bench.bench.capture.current(), &open(library)?,
        &bench.bench.config.storage_policy, library, &first(bench.config, stage.first_scale.as_ref()))?];
    for side in &stage.sides {
        workloads.push(WorkloadContract::prepare(root, &side.name, WorkloadRole::Kept, &side.config.inputs, &side.view.capture.current(), &open(&side.view.library)?,
            &side.view.storage_policy, &side.view.library, &first(&side.config, side.stage.first_scale.as_ref()))?);
    }
    let seed = match &stage.seed {
        Some(Seed::Run { version, .. }) => json!({"run":version.run,"version":version.version}),
        _ => Value::Null,
    };
    Ok(StageContract { goal: stage.primary.clone(), seed, workloads })
}

/// The contract of a session's role in a run of several workloads (`prompts::engine_contract::
/// write_workloads_engine_contract`): every workload with its role, the primary from the role's own inputs, capture and
/// library, every other from its own, and each workload's seed as the request gives it.
pub(super) fn members_contract(bench: &EngineBench<'_>, root: &Path, stage: &StageRole) -> Result<crate::prompts::engine_contract::WorkloadsContract, AdmissionError> {
    use crate::prompts::engine_contract::{MemberContract, WorkloadsContract};
    let open = |library: &Path| gendb_artifacts::ObjectStore::open_existing(library).map_err(|e| AdmissionError::tool(format!("{}: {e}", library.display())));
    let first = |own: &EngineRoleConfig, first: Option<&FirstScale>| first_scale_name(first).or_else(|| own.inputs.general.as_ref().map(|g| g.scale.name.clone())).unwrap_or_default();
    let library = &bench.bench.config.library;
    let mut members = vec![MemberContract::prepare(root, &stage.workload, stage.role, true, bench.inputs(), &bench.bench.capture.current(), &open(library)?,
        &bench.bench.config.storage_policy, library, &first(bench.config, stage.first_scale.as_ref()))?];
    for side in &stage.sides {
        members.push(MemberContract::prepare(root, &side.name, side.role, false, &side.config.inputs, &side.view.capture.current(), &open(&side.view.library)?,
            &side.view.storage_policy, &side.view.library, &first(&side.config, side.stage.first_scale.as_ref()))?);
    }
    Ok(WorkloadsContract { primary: stage.primary.clone(), seeds: stage.seeds.clone(), members })
}

#[cfg(test)]
mod tests;
