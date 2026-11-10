//! The engine role. It plugs into the
//! generic session loop (`controller::run`) through `SynthesisRole`, on the retained owner thread
//! (`controller::session::RetainedRole`), as the query and workload roles do. Two modes ([`EngineRoleMode`]):
//! - **round** (the schema-engine line): one author session per round ending with one submission, below;
//! - **session** (the general line): one session of a branch or a merge, where every submission is decided at its
//!   evaluation against its parent in one interleaved timing and the session goes on (`engine::acceptance`,
//!   `engine::sessions`).
//!
//! Stages of a round:
//! - `prepare`: once per round, seeds the workspace ([`seed_workspace`]: the latest version's sources, the previous
//!   round's workspace before `v1` exists, or an empty engine crate), copies every earlier version read-only and
//!   carries `NOTES.md`; then, on every preparation (a resumed controller too), writes the contract bundle, the crate map
//!   `ENGINE_MAP.md` and the tool context (`prompts::engine_contract`) and returns the context. Author files are never
//!   touched after the seed;
//! - `refresh_shared_facts`: the storage budget and catalog before every call;
//! - `freeze`: `engine::submission::freeze_engine`;
//! - `evaluate` ([`EngineBench::evaluate_frozen`]), every step gating: the whole-crate verify-and-compile run; the
//!   storage assets of the uses and their storage policy as the serving storage will stand once this version is
//!   selected (`storage::engine_library::check_engine_storage_uses`); qualification (`admission::engine::
//!   qualify_templates`: every template at every visible binding, one call at 64 workers, against its saved answers,
//!   with the AST echo); the variant matrix (the timed variants at 64 workers, 1 warm + 1 hot, each against its
//!   template's saved answers). Eligible exactly when all of it passed;
//! - `qualify` ([`EngineBench::qualify_evaluated`]): the submission's workspace storages checked (session cache), then
//!   under the library's budget lock: the storage policy of the uses with the new storages
//!   (`check_engine_storage_uses`), their registration (`Workbench::register_checked`), and the admission and
//!   publication of the version on the library's engine stream (`storage::engine_library::admit_engine_version`;
//!   admitting selects it). Then, the lock released, the official timing of the admitted version over its admitted
//!   assets ([`EngineBench::time_admitted`]: the official matrix, each failing cell recorded, the totals with the stop
//!   decision (`engine::timing`, `engine::totals`), the variant ratio report, and when the stop holds the other visible
//!   bindings). Timing records and never gates: a version is never un-admitted. Then the version folder
//!   (`engine::rounds::write_version`);
//! - `close`: the round's resolution (a new version, or the round's attempt).
//!
//! Every engine call is one checked cell of `admission::engine::EngineRunner::cell` (one fresh worker child,
//! the echo and the saved-answer comparison), under the host's exclusive timing lease; on the general line the runner
//! carries the stored-answer bound (a cell without saved answers stores each answer over it as its summary and first
//! rows; a failed cell's evidence is stored the same way after its comparison). The author's engine tools
//! (`check`, `verify`, `compile`, `trial`, `profile`; `LocalJobs`) run the same freeze, builds and cells as diagnostics;
//! the storage tools and `catalog` run through the session bench.
//!
//! A **run of several workloads** (`engine::stage`: a stage run, or `engine.workloads`) gives the
//! role its stage ([`EngineAuthorRole::with_stage`]): every freeze is that workload's crate
//! (`submission::freeze_stage_engine`, or `submission::freeze_member_crate` with its family instances), every admission
//! the stage admission (`admission::engine::admit_stage_engine`) under the workload's budget rule (a check workload is
//! exempt: [`EngineBench::budget_rule`]), and a session's role also reaches the other workloads: its contract is the
//! stage contract (`prompts::engine_contract::write_stage_engine_contract`) or the workloads contract
//! (`write_workloads_engine_contract`), its context and refreshed facts carry the stage view or the workloads view and
//! the combined score (`engine::stage::view`), and every tool takes `workload` (default the goal or primary): another
//! workload's job runs on the session's bench viewing that workload's library, capture and statements, with its inputs
//! and its crate.

use super::facts::{EncodedStatement, EncodedStatements, EngineChecks, TrainingSet};
use super::rounds::{self, RoundSeed};
use super::sessions::{GeneralSessionPolicy, RunSpend, SessionRecord};
use crate::controller::request::EngineScale;
use crate::controller::PromptInput;
use super::submission::{EngineBuild, EngineBuilds, EngineFreeze, EngineManifest, FrozenEngine, GENERATION_IDENTITY, MANIFEST_FILE, engine_version_id, freeze_engine};
use super::timing::{CellRequest, EngineCellRunner, EngineMatrix, EngineStatement, MatrixKind, run_matrix, run_matrix_recording_failures, variant_ratios};
use super::totals::{Baselines, TotalsReport, totals};
use crate::controller::author::{CandidateSubmission, resolve_candidate_manifest};
use crate::controller::layout::NOTES_FILE;
use crate::controller::limits::Limits;
use crate::controller::records::{now_unix_ms, read_json, write_json_atomic, write_new_json};
use crate::controller::session::{LocalJobs, LocalSessionEndpoint};
use crate::controller::{QualificationAttempt, RunRequest, SynthesisRole, Trial};
use crate::prompts::brief::search_index::ReuseLibrary;
use crate::prompts::engine_contract::{self, CONTRACT_DIRECTORY, ENGINE_MAP_FILE, EngineContractInputs, VERSIONS_DIRECTORY};
use crate::prompts::engine_policy::EnginePolicy;
use crate::controller::RolePolicy;
use crate::controller::StopReason;
use crate::query::QuerySession;
use crate::query::compile::agent_modules;
use crate::query::evaluation::{DEFAULT_TRIAL_HOT_CALLS, ResolvedStorage};
use crate::query::role::{fresh_evaluation_dir, protect_eligible_assets, release_trial_assets};
use crate::storage::capture::SharedCapture;
use crate::storage::engine_library::{BudgetRule, NewEngineStorage, admit_engine_version, check_engine_storage_uses, engine_assets};
use crate::storage::freeze::write_workspace_framework;
use crate::storage::library_lock::{BUDGET_LOCK, LibraryLock};
use crate::storage::payload::PayloadHolder;
use crate::tools::bench::{UNVERIFIED_LABEL, Workbench};
use crate::tools::{self, AuthorRole, LocalJobArguments, ToolAction, ToolWorkload, TrialVerification};
use super::stage::StageRole;
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_artifacts::verus::VerusStorageUseV1;
use gendb_registry::CrateKind;
use gendb_runtime::worker::StorageUseInput;
use gendb_storage::import::DatasetSpec;
use gendb_storage::io::PartAccess;
use gendb_storage::versions::CurrentCapture;
use gendb_verification::admission::bindings::CONCRETE_BINDING;
use gendb_verification::admission::engine::{ENGINE_QUALIFICATION_KIND, EngineCandidate, EngineRunner, EngineSchema, QUALIFICATION_WORKERS, TemplateCheck, qualify_templates};
use gendb_verification::admission::execution::PROFILE_REPETITIONS;
use gendb_verification::admission::{AdmissionError, BenchmarkBinding, IntegrityConstraints, ValidationPolicy};
use gendb_runtime::worker::{AnswerBound, CallLimits};
use gendb_verification::verus::engine_rules::EngineRuleSet;
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;

/// The claim of an eligible engine evaluation.
const EVALUATED_CLAIM: &str = "Verus checked the whole frozen engine crate (framework files, the toolkit, the copied storage interfaces and the agent) with 0 errors against the fixed engine entry under the recorded TCB: the engine claim is the correctness claim. Every training template at every visible binding and every timed variant returned answers agreeing with the saved answers of other engines where given, with the echo of its AST equal to the host's rendering (agreement and echo are checks of the trusted base, not proof). The official timing follows admission and never gates it";

/// Record kind of a version's variant matrix (every timed variant against its template's saved answers), stored with
/// its admission. The official timing follows admission and lives in the version folder.
pub const ENGINE_VARIANTS_KIND: &str = "gendb.verus.engine-variants.v1";

/// The engine run's inputs, prepared once per controller process and shared by every round.
pub struct EngineInputs {
    pub training: TrainingSet,
    /// The prepared templates in training order: `(name, session)`.
    pub sessions: Vec<(String, Arc<QuerySession>)>,
    /// The statement of every template and variant every cell is checked against.
    pub checks: EngineChecks,
    pub statements: EncodedStatements,
    /// `engine::facts::training_facts`.
    pub training_facts: Value,
    pub baselines: Baselines,
    /// The run's engine source rules (its line, the training templates' constants and, on the general line, the
    /// schema's names): applied at freeze and admission.
    pub rules: EngineRuleSet,
    /// The configured worker counts (every official cell).
    pub workers: Vec<usize>,
    /// The user's engine controls (shown to the author).
    pub engine_limits: Limits,
    pub hardware: Value,
    pub observed_hardware: Value,
    /// The seeded storages `(name, package)`, in seed order.
    pub seeded: Vec<(String, ContentId)>,
    /// The request's read-only reuse libraries (`engine.reuse_libraries`): their admitted code is offered in the author's
    /// search index and `admitted-code/`; nothing else reads them.
    pub reuse_libraries: Vec<PathBuf>,
    /// Kernel advice for mapping stored parts in every engine child.
    pub part_access: PartAccess,
    /// The request's dataset, declared constraints and numeric tolerance: the author's own statements (`trial` with
    /// `sql`) are prepared over them.
    pub dataset: DatasetSpec,
    pub constraints: Option<IntegrityConstraints>,
    pub numeric_relative_tolerance: String,
    /// The general line's scale and limits these inputs were prepared for (`None`: the schema line).
    pub general: Option<GeneralInputs>,
}

/// What the general line adds to the inputs of one scale.
#[derive(Clone)]
pub struct GeneralInputs {
    /// The scale (its name, capture, bindings, baselines, saved answers and original data size, a reported fact).
    pub scale: EngineScale,
    /// The plain storages: the seeded storage packages version 0 reads (the generated flat storage of every table). A
    /// version reading only these is allowed as is at every scale.
    pub plain_storages: BTreeSet<ContentId>,
    /// The plain storage's bytes at this scale (reported beside the budget), measured from the run library when these
    /// inputs are prepared (`storage::engine_library::plain_storage_bytes`).
    pub plain_storage_bytes: u64,
    /// Its position in the ladder, and the ladder's length.
    pub scale_index: usize,
    pub scales: usize,
    /// The name of the ladder's next scale (`None` at the last scale).
    pub next_scale: Option<String>,
    /// The per-call limits of every engine call (`engine.call_limit_seconds`, `engine.anon_memory_limit_bytes`).
    pub call_limits: CallLimits,
    /// The hot calls of every timed cell of the run's development timings (`engine.timed_calls`, default 3;
    /// `engine::protocol::development`); every workload of a run shares it.
    pub timed_calls: u32,
    /// The run's branch slots (`b1`, ...).
    pub branches: Vec<String>,
    /// The run's budget of engine-agent calls.
    pub budget_usd: crate::controller::limits::Money,
    /// The request's `engine.emphasis`: the prompt's main direction from the first version (`None`: the prompt as
    /// before). A session's context carries it as `general.emphasis` only when set.
    pub emphasis: Option<crate::controller::request::EngineEmphasis>,
    /// A continued run's seed (`engine.seed_version`) and its run's training templates (`None`: a run from version 0).
    /// A session's context carries it as `general.seed` only when set.
    pub seed: Option<SeedFacts>,
}

/// A continued run's seed as the prompt states it (`engine.seed_version`): the seed version, and
/// the names of its run's training templates, which the prompt tells apart from the templates new to the engine.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SeedFacts {
    pub seed: crate::controller::request::SeedVersion,
    /// The names of the seed run's training templates (`<run>/request.json` `engine.templates`).
    pub templates: Vec<String>,
}

impl SeedFacts {
    /// The seed `seed` with its run's training templates, read from the run's recorded request and that request's
    /// `templates.json` (names only).
    pub fn read(seed: &crate::controller::request::SeedVersion) -> Result<Self, String> {
        let request: Value = read_json(&seed.run.join("request.json")).map_err(|e| format!("engine.seed_version: the seed run's request: {e}"))?;
        let file = request["engine"]["templates"].as_str().ok_or("engine.seed_version: the seed run's request names no engine.templates")?;
        let index: Value = read_json(Path::new(file)).map_err(|e| format!("engine.seed_version: the seed run's templates {file}: {e}"))?;
        let templates = index["templates"].as_object().ok_or_else(|| format!("engine.seed_version: {file} has no templates object"))?.keys().cloned().collect();
        Ok(Self { seed: seed.clone(), templates })
    }

    /// `general.seed` of a session's context over the run's training templates `training`: the seed version, the
    /// templates its run was built for and the templates new to it (each in training order).
    pub fn view(&self, training: &[String]) -> Value {
        let (built_for, new): (Vec<&String>, Vec<&String>) = training.iter().partition(|t| self.templates.contains(t));
        json!({"run":self.seed.run,"version":self.seed.version,"seed_templates":built_for,"new_templates":new})
    }
}

impl GeneralInputs {
    /// The last scale of the ladder (the run stays there).
    pub fn last_scale(&self) -> bool {
        self.scale_index + 1 == self.scales
    }

    /// The storage budget rule at this scale (the template runs' allowance): a version reading only
    /// the plain storages is allowed as is; any other version's serving storage stays within the original data size
    /// here (`engine.scales[].original_data_bytes`).
    pub fn budget_rule(&self) -> BudgetRule {
        BudgetRule::OriginalDataSize { original_data_bytes: self.scale.original_data_bytes, scale: self.scale.name.clone(), plain_storages: self.plain_storages.clone() }
    }
}

/// What the rounds controller gives the role of one round (the schema line).
#[derive(Clone)]
pub struct RoundConfig {
    pub round: u32,
    pub seed: RoundSeed,
    /// The version number an accepted submission of this round becomes.
    pub next_version: u32,
    /// `{"versions": [...], "rounds": [...]}` of earlier rounds (`engine::rounds::EngineState::author_view`).
    pub history: Value,
}

/// What the branch driver gives the role of one general-line session.
#[derive(Clone)]
pub struct SessionConfig {
    pub record: SessionRecord,
    /// The session's directory (`engine::sessions::session_directory`).
    pub directory: PathBuf,
    /// The run's spend over every session, checked before every call.
    pub spend: RunSpend,
    /// The prompt of every call (the general line's engine prompt).
    pub prompt: fn(&PromptInput) -> String,
    /// The ladder's first scale, where a session at a later scale checks its submissions' variants
    /// (`engine::protocol::VariantRun::AnswersAtFirstScale`); `None` for a session at the first scale.
    pub first_scale: Option<FirstScale>,
}

/// The inputs and the capture of the ladder's first scale, prepared once per controller process by the run
/// (`engine::rounds::prepare_engine_scale` at index 0, which reuses the run's records under `engine/scales/<first>/`).
#[derive(Clone)]
pub struct FirstScale {
    pub inputs: Arc<EngineInputs>,
    pub capture: SharedCapture,
}

impl FirstScale {
    /// The first scale's inputs and capture as the run prepared them.
    pub fn of(prepared: &rounds::PreparedEngine) -> Self {
        Self { inputs: prepared.inputs.clone(), capture: prepared.data.capture.clone() }
    }
}

/// The role's mode: a round of the schema line, a session of the general line, or framework work of the general line
/// without an author (version 0, the timing at a scale move: `engine::branches`), which runs no session stage.
#[derive(Clone)]
pub enum EngineRoleMode {
    Round(RoundConfig),
    Session(SessionConfig),
    Framework,
}

/// The role's configuration.
#[derive(Clone)]
pub struct EngineRoleConfig {
    /// `<run>/engine`.
    pub engine_dir: PathBuf,
    pub inputs: Arc<EngineInputs>,
    pub mode: EngineRoleMode,
}

/// The engine role of one round's or one general-line session's author session.
pub struct EngineAuthorRole {
    bench: Workbench,
    config: EngineRoleConfig,
    builds: EngineBuilds,
    /// A run of several workloads' role: its crate, and for a session the other workloads (`engine::stage`); `None`
    /// elsewhere.
    stage: Option<StageRole>,
}

/// The role's state one stage or local job works on: the session bench, the round's or session's configuration and
/// the session's compiled engine libraries (disjoint borrows of the role, so a local job can run inside the bench's job
/// record).
pub(super) struct EngineBench<'a> {
    pub(super) bench: &'a mut Workbench,
    pub(super) config: &'a EngineRoleConfig,
    pub(super) builds: &'a mut EngineBuilds,
    /// The role's stage (a run of several workloads), else `None`.
    pub(super) stage: Option<&'a StageRole>,
}

/// Runs the matrix cells through the checked cell (`EngineRunner::cell`) over one compiled engine and its storages:
/// each statement against the check of its template, its variant or (a local job's own statement) `adhoc`.
pub(super) struct EngineCells<'a> {
    pub(super) runner: EngineRunner<'a>,
    pub(super) checks: &'a EngineChecks,
    pub(super) adhoc: &'a [TemplateCheck],
    /// An author-requested bound of each child in seconds (local jobs only).
    pub(super) bound: Option<u64>,
}

impl EngineCellRunner for EngineCells<'_> {
    fn run_cell(&self, cell: CellRequest<'_>, work: &Path) -> Result<Value, AdmissionError> {
        let statement = cell.statement;
        let check = self
            .checks
            .check_of(statement)
            .or_else(|| self.adhoc.iter().find(|c| c.name == statement.template))
            .ok_or_else(|| AdmissionError::tool(format!("statement {} has no check", statement.name())))?;
        if let Some(parent) = work.parent() {
            fs::create_dir_all(parent).map_err(AdmissionError::tool)?;
        }
        self.runner.cell(check, &statement.binding, &statement.ast, cell.workers, cell.calls, work, self.bound)
    }
}

/// `value` with every non-integer number written as its decimal text: the library's identity-bearing records hold no
/// floating point (`gendb_artifacts`), and admission stores a version's evidence there (ratios and margins are reports).
pub(super) fn float_free(value: &Value) -> Value {
    match value {
        Value::Number(n) if !(n.is_i64() || n.is_u64()) => Value::String(n.to_string()),
        Value::Array(items) => Value::Array(items.iter().map(float_free).collect()),
        Value::Object(fields) => Value::Object(fields.iter().map(|(k, v)| (k.clone(), float_free(v))).collect()),
        other => other.clone(),
    }
}

/// The worker's storage uses of resolved storages, in use order.
pub(super) fn storage_inputs(storages: &[ResolvedStorage]) -> Vec<StorageUseInput> {
    storages.iter().map(|s| StorageUseInput { name: s.name.to_string(), parts_directory: s.parts.clone() }).collect()
}

/// One storage as the evaluation and the feedback show it.
pub(super) fn storage_view(s: &ResolvedStorage) -> Value {
    json!({"name":s.name.to_string(),"package":s.package,"admitted":s.admitted,"asset":s.asset,"storage_bytes":s.storage_bytes,"build_wall_ns":s.build_wall_ns,
        "asset_reused":!s.asset_built_now})
}

/// The compact form of a matrix: per cell its statement, binding, workers, status and median (the full records stay in
/// the matrix file).
fn matrix_view(matrix: &EngineMatrix, file: &Path) -> Value {
    json!({"kind":matrix.kind,"calls_per_cell":matrix.calls_per_cell,"workers":matrix.workers,"file":file,
        "cells":matrix.cells.iter().map(|c| json!({"statement":c.variant.as_ref().map_or(c.template.as_str(), |v| v.id.as_str()),"binding":c.binding,"workers":c.workers,
            "status":c.status,"checked":c.checked,"median_ns":c.median_ns,"warm_ns":c.warm_ns,"hot_ns":c.hot_ns})).collect::<Vec<_>>(),"failed":matrix.failed})
}

pub(super) fn write_matrix(matrix: &EngineMatrix, file: &Path) -> Result<Value, AdmissionError> {
    write_json_atomic(file, &json!(matrix)).map_err(AdmissionError::tool)?;
    Ok(matrix_view(matrix, file))
}

/// Open a read-only reuse library (`engine.reuse_libraries`): `ObjectStore::open_existing` creates nothing, and its
/// one reader (the search index) only reads admitted records and source blobs.
pub fn open_reuse_library(path: &Path) -> Result<ObjectStore, AdmissionError> {
    ObjectStore::open_existing(path).map_err(|e| AdmissionError::missing_input(format!("engine.reuse_libraries: {}: {e}", path.display())))
}

impl EngineAuthorRole {
    pub fn new(bench: Workbench, config: EngineRoleConfig) -> Self {
        Self { bench, config, builds: EngineBuilds::default(), stage: None }
    }

    /// The same role in a run of several workloads (module documentation).
    pub fn with_stage(self, stage: StageRole) -> Self {
        Self { stage: Some(stage), ..self }
    }

    /// The role's working view (framework work of the general line runs through it directly, without a session).
    pub(super) fn view(&mut self) -> EngineBench<'_> {
        EngineBench { bench: &mut self.bench, config: &self.config, builds: &mut self.builds, stage: self.stage.as_ref() }
    }
}

impl EngineRoleConfig {
    /// The round of a schema-line role (a tool failure in session mode: only round stages ask).
    fn round(&self) -> Result<&RoundConfig, AdmissionError> {
        match &self.mode {
            EngineRoleMode::Round(round) => Ok(round),
            _ => Err(AdmissionError::tool("a round stage ran outside a schema-engine round")),
        }
    }

    /// The session of a general-line role (a tool failure in the other modes).
    pub(super) fn session(&self) -> Result<&SessionConfig, AdmissionError> {
        match &self.mode {
            EngineRoleMode::Session(session) => Ok(session),
            _ => Err(AdmissionError::tool("a general-line session stage ran outside a general-line session")),
        }
    }
}

impl EngineBench<'_> {
    pub(super) fn inputs(&self) -> &EngineInputs {
        &self.config.inputs
    }

    pub(super) fn schema(&self) -> &[gendb_frontend::ast::TableDef] {
        self.bench.schema()
    }

    /// The first scale of this role's ladder, where its submissions' variants are checked when it is not its own: a
    /// session's, else a stage workload's (`engine::stage::StageRole::first_scale`).
    pub(super) fn first_scale(&self) -> Option<FirstScale> {
        match &self.config.mode {
            EngineRoleMode::Session(session) => session.first_scale.clone(),
            _ => self.stage.and_then(|stage| stage.first_scale.clone()),
        }
    }

    /// Prepare the round's workspace (module documentation) and return its context.
    fn prepare_workspace(&mut self, request: &RunRequest, workspace: &Path) -> Result<Value, AdmissionError> {
        let config = self.config;
        let round = config.round()?;
        let workspace = self.bench.open_workspace(workspace)?;
        let round_dir = self.bench.session_root()?;
        let seed_record = round_dir.join("seed.json");
        let seeded = if seed_record.is_file() {
            read_json(&seed_record).map_err(AdmissionError::tool)?
        } else {
            let record = seed_workspace(&workspace, &round.seed, &self.inputs().seeded)?;
            write_new_json(&seed_record, &record).map_err(AdmissionError::tool)?;
            record
        };
        let versions: Vec<Value> = round.history["versions"].as_array().cloned().unwrap_or_default();
        let version_name = round.seed.version.as_deref().unwrap_or("no version yet");
        let mut context = self.write_author_contract(request, &workspace, &versions, &format!("round {}, seeded from {version_name}", round.round))?;
        let inputs = &self.config.inputs;
        let notes = workspace.join(NOTES_FILE);
        let fields = context.as_object_mut().ok_or_else(|| AdmissionError::tool("contract facts are not an object"))?;
        fields.insert("round".into(), json!({"number":round.round,"seed":{"kind":round.seed.kind,"description":round.seed.description,"version":round.seed.version},
            "seed_record":seed_record,"next_version":round.next_version,
            "notes":{"file":notes,"from":seeded["notes_from"],"text":seeded["notes_text"]}}));
        fields.insert("engine".into(), json!({"training":inputs.training_facts,"versions":round.history["versions"],"rounds":round.history["rounds"],
            "limits":inputs.engine_limits,"stop_rule":super::totals::STOP_RULE}));
        context["files"]["versions_records"] = json!(self.config.engine_dir.join("versions"));
        context["files"]["rounds"] = json!(self.config.engine_dir.join("rounds"));
        Ok(context)
    }

    /// The author contract of the workspace (`prompts::engine_contract`: the contract bundle with the earlier
    /// `versions`), the crate map `ENGINE_MAP.md` (headed `map_label`) and the tool context; returns the context with
    /// the common fields (scope, task, limits, hardware, storage policy).
    pub(super) fn write_author_contract(&mut self, request: &RunRequest, workspace: &Path, versions: &[Value], map_label: &str) -> Result<Value, AdmissionError> {
        let store = self.bench.store()?;
        let capture = self.bench.capture.current();
        let inputs = &self.config.inputs;
        let reuse_stores = inputs.reuse_libraries.iter().map(|path| open_reuse_library(path)).collect::<Result<Vec<_>, _>>()?;
        let reuse_libraries: Vec<ReuseLibrary<'_>> = inputs.reuse_libraries.iter().zip(&reuse_stores).map(|(path, store)| ReuseLibrary { path, store }).collect();
        let contract_inputs = EngineContractInputs {
            sessions: &inputs.sessions,
            training: &inputs.training_facts,
            versions,
            limits: &inputs.engine_limits,
            store: &store,
            capture: &capture,
            hardware: &inputs.hardware,
            observed_hardware: &inputs.observed_hardware,
            free_bytes: crate::query::assets::free_bytes_at(workspace),
            data_allowance: self.bench.config.live_bytes_allowance,
            storage_policy: &self.bench.config.storage_policy,
            seeded: &inputs.seeded,
            reuse_libraries: &reuse_libraries,
            general: inputs.general.as_ref().map(|general| engine_contract::GeneralContract { engine_dir: &self.config.engine_dir, rules: &inputs.rules, inputs: general }),
        };
        let mut context = match self.stage.filter(|_| inputs.general.is_some()) {
            Some(stage) if stage.is_members() => engine_contract::write_workloads_engine_contract(workspace, &contract_inputs, &super::stage::members_contract(self, workspace, stage)?)?,
            Some(stage) => engine_contract::write_stage_engine_contract(workspace, &contract_inputs, &super::stage::stage_contract(self, workspace, stage)?)?,
            None => engine_contract::write_engine_contract(workspace, &contract_inputs)?,
        };
        let map = engine_contract::engine_map(&workspace.join(super::submission::CRATE_DIRECTORY).join("src"), map_label)?;
        fs::write(workspace.join(ENGINE_MAP_FILE), map).map_err(AdmissionError::tool)?;
        let mut tool_context = self.bench.tool_context(AuthorRole::Engine, workspace.join(CONTRACT_DIRECTORY).join("index.json"))?;
        for (statement, (name, _)) in tool_context.statements.iter_mut().zip(&inputs.sessions) {
            statement.name = Some(name.clone());
        }
        tool_context.engine_bindings = std::iter::once(inputs.training.timing_binding.clone()).chain(inputs.training.other_bindings()).collect();
        // A run of several workloads' tools take `workload`: every workload with its templates and visible bindings, the
        // primary (a stage run's goal) first; in a run of several workloads also its role.
        if let Some(stage) = self.stage {
            let of = |name: &str, inputs: &EngineInputs| ToolWorkload {
                name: name.to_string(),
                templates: inputs.training.templates.iter().map(|t| t.name.clone()).collect(),
                bindings: std::iter::once(inputs.training.timing_binding.clone()).chain(inputs.training.other_bindings()).collect(),
                role: stage.is_members().then(|| stage.role_name_of(name).to_string()),
            };
            tool_context.workloads = std::iter::once(of(&stage.workload, inputs)).chain(stage.sides.iter().map(|k| of(&k.name, &k.config.inputs))).collect();
        }
        write_json_atomic(&workspace.join(tools::CONTEXT_FILE), &tool_context).map_err(AdmissionError::tool)?;
        let fields = context.as_object_mut().ok_or_else(|| AdmissionError::tool("contract facts are not an object"))?;
        fields.insert("scope".into(), json!(if inputs.general.is_some() { engine_contract::GENERAL_SCOPE } else { engine_contract::SCOPE }));
        fields.insert("authoring".into(), json!("verus_rust_engine"));
        fields.insert("task".into(), request.task.clone());
        fields.insert("limits".into(), json!(request.limits.active()));
        fields.insert("hardware".into(), inputs.hardware.clone());
        fields.insert("observed_hardware".into(), inputs.observed_hardware.clone());
        fields.insert("storage_policy".into(), self.bench.config.storage_policy.author_view());
        Ok(context)
    }

    /// The budget rule of this role's workload at its scale (`GeneralInputs::budget_rule`); a check
    /// workload of a run of several workloads is exempt (no storage budget, `BudgetRule::Allowance`
    /// without an allowance).
    pub(super) fn budget_rule(&self) -> Result<BudgetRule, AdmissionError> {
        if self.stage.is_some_and(|s| s.is_members() && s.role == crate::controller::request::MemberRole::Check) {
            return Ok(BudgetRule::Allowance { allowance_bytes: None });
        }
        Ok(self.inputs().general.as_ref().ok_or_else(|| AdmissionError::tool("a general-line budget rule without general inputs"))?.budget_rule())
    }

    /// Resolve the storages of a frozen engine (an admitted package's asset, or a workspace storage checked and built).
    pub(super) fn storages(&mut self, engine: &FrozenEngine, frozen_dir: &Path, out: &Path, verification: TrialVerification) -> Result<Vec<ResolvedStorage>, AdmissionError> {
        self.bench.resolve_uses_as(&engine.storage_uses, frozen_dir, out, verification)
    }

    /// The storage policy of the submission's storages as the serving storage will stand once this version is selected
    /// (`storage::engine_library::check_engine_storage_uses`): every admitted use eligible, applicable and built, the
    /// new (workspace) storages with them holding each column once, within the budget.
    pub(super) fn check_storage_policy(&self, engine: &FrozenEngine, frozen_dir: &Path, storages: &[ResolvedStorage], budget: &BudgetRule) -> Result<Value, AdmissionError> {
        let store = self.bench.store()?;
        let capture = CurrentCapture::of(&self.bench.capture.current()).map_err(AdmissionError::tool)?;
        let admitted: Vec<VerusStorageUseV1> = storages.iter().filter(|s| s.admitted).map(|s| VerusStorageUseV1 { name: s.name.to_string(), package: s.package }).collect();
        let mut holders = vec![];
        for (storage, resolved) in engine.storage_uses.iter().zip(storages).filter(|(_, s)| !s.admitted) {
            let (_, frozen) = FrozenEngine::workspace_storage(frozen_dir, &storage.name)?;
            holders.push((PayloadHolder::of_manifest(&frozen.manifest, None)?, resolved.parts.clone()));
        }
        let new: Vec<NewEngineStorage<'_>> = holders.iter().map(|(holder, parts)| NewEngineStorage { holder: holder.clone(), asset_directory: parts }).collect();
        check_engine_storage_uses(&store, &capture, self.schema(), &self.bench.config.storage_policy, budget, &admitted, &new)
    }

    /// The engine runner over a compiled engine library and its storages, with the general line's per-call limits and
    /// stored-answer bound (none on the schema line: its cells run as before).
    pub(super) fn runner<'b>(&'b self, library: &'b Path, storages: &'b [StorageUseInput]) -> EngineRunner<'b> {
        let general = self.inputs().general.as_ref();
        let (limits, answer_bound) = (general.map(|general| general.call_limits), general.map(|_| AnswerBound::STORED));
        EngineRunner { runner: self.bench.runner(), library, uses: storages, access: self.inputs().part_access, limits, answer_bound }
    }

    /// Run `statements` as one matrix of `kind` at `workers` through the checked cells, each cell under the timing lease.
    pub(super) fn matrix(&self, build: &EngineBuild, storages: &[StorageUseInput], kind: MatrixKind, statements: &[&EncodedStatement], workers: &[usize], work: &Path) -> Result<EngineMatrix, AdmissionError> {
        let cells = EngineCells { runner: self.runner(&build.library, storages), checks: &self.inputs().checks, adhoc: &[], bound: None };
        let matrix_statements: Vec<EngineStatement> = statements.iter().map(|s| s.statement.clone()).collect();
        let locks = self.bench.config.locks.clone();
        run_matrix(&cells, kind, &matrix_statements, workers, work, || locks.timing())
    }

    /// The official matrix of an admitted version: [`EngineBench::matrix`], each failing cell recorded instead of ending
    /// the matrix (`timing::run_matrix_recording_failures`).
    pub(super) fn recorded_matrix(&self, build: &EngineBuild, storages: &[StorageUseInput], statements: &[&EncodedStatement], workers: &[usize], work: &Path) -> Result<EngineMatrix, AdmissionError> {
        let cells = EngineCells { runner: self.runner(&build.library, storages), checks: &self.inputs().checks, adhoc: &[], bound: None };
        let matrix_statements: Vec<EngineStatement> = statements.iter().map(|s| s.statement.clone()).collect();
        let locks = self.bench.config.locks.clone();
        run_matrix_recording_failures(&cells, MatrixKind::Official, &matrix_statements, workers, work, || locks.timing())
    }

    /// The evaluation of a frozen engine (module documentation): `Ok` is the eligible evaluation record. Every step
    /// gates; nothing here is timed for the totals.
    fn evaluate_frozen(&mut self, dir: &Path, frozen_dir: &Path, engine: &FrozenEngine) -> Result<Value, AdmissionError> {
        let started = Instant::now();
        let locks = self.bench.config.locks.clone();
        let build = self.builds.compile(&locks, engine, frozen_dir, &dir.join("verus-build"), true)?;
        let compiled_ns = started.elapsed().as_nanos() as u64;
        let storages = self.storages(engine, frozen_dir, dir, TrialVerification::WholeCrate)?;
        let policy = self.check_storage_policy(engine, frozen_dir, &storages, &BudgetRule::Allowance { allowance_bytes: self.bench.config.live_bytes_allowance })?;
        let uses = storage_inputs(&storages);
        let qualification = {
            let _lease = self.bench.config.locks.timing().map_err(AdmissionError::tool)?;
            qualify_templates(&self.runner(&build.library, &uses), &self.inputs().checks.templates, &dir.join("qualification"))?
        };
        let qualification_file = dir.join("qualification.json");
        write_json_atomic(&qualification_file, &qualification).map_err(AdmissionError::tool)?;
        let inputs = self.config.inputs.clone();
        let variant_statements: Vec<&EncodedStatement> = inputs.statements.variants.iter().collect();
        let variants = self.matrix(&build, &uses, MatrixKind::Variants, &variant_statements, &[QUALIFICATION_WORKERS], &dir.join("variants"))?;
        let unchecked: Vec<String> = variants.unchecked_cells().iter().map(|c| format!("{} at {} workers ({})", c.variant.as_ref().map_or("-", |v| v.id.as_str()), c.workers, c.status)).collect();
        if !unchecked.is_empty() {
            return Err(AdmissionError::execution(format!("variant answers not checked against their templates' saved answers: {}", unchecked.join("; "))));
        }
        let variants_view = write_matrix(&variants, &dir.join("variant-matrix.json"))?;
        Ok(json!({"kind":"verus_engine","eligible":true,"status":"verified_qualified","claim":EVALUATED_CLAIM,
            "crate_version":engine_version_id(engine, frozen_dir)?,
            "verus":{"detail":build.record["detail"],"outcome":build.record["outcome"],"wall_ns":build.record["wall_ns"],"record":build.record["record"],
                "verification":build.record["verification"]},
            "build":build.record,"compile_elapsed_ns":compiled_ns,
            "storage":{"assets":storages.iter().map(storage_view).collect::<Vec<_>>(),"policy":policy},
            "qualification":{"status":qualification["status"],"workers":qualification["workers"],"cells_compared":qualification["cells_compared"],
                "cells_without_saved_answers":qualification["cells_without_saved_answers"],"file":qualification_file},
            "variants":{"matrix":variants_view,"timed":inputs.statements.variants.len(),"not_timed":inputs.statements.record["variants"]["not_timed"],"workers":QUALIFICATION_WORKERS},
            "official_timing":"after admission, of the admitted version (qualify); it records and never gates",
            "framework_evaluation_ns":started.elapsed().as_nanos() as u64}))
    }

    /// Accept an eligible evaluation as the next version (module documentation, `qualify`): its workspace storages
    /// checked; under the library's budget lock the storage policy of its uses with the new storages, their
    /// registration, and the admission and publication of the version on the engine stream; then, with the lock
    /// released, the official timing of the admitted version ([`EngineBench::time_admitted`]); then the version folder.
    fn qualify_evaluated(&mut self, frozen_dir: &Path, evaluation: &Value) -> Result<Value, AdmissionError> {
        if evaluation["eligible"] != true {
            return Err(AdmissionError::refusal("only an eligible (verified and qualified) engine submission becomes a version"));
        }
        let config = self.config;
        let round = config.round()?;
        let engine: FrozenEngine = read_json(&frozen_dir.join("candidate.json")).map_err(AdmissionError::tool)?;
        let work = frozen_dir.join("qualification");
        fs::create_dir_all(&work).map_err(AdmissionError::tool)?;
        let registered_by = json!({"role":AuthorRole::Engine,"session":self.bench.session_root()?,"qualification":frozen_dir});
        let mut checked = self.bench.check_workspace_uses(&engine.storage_uses, frozen_dir, &work)?;
        let build = &evaluation["build"];
        let verus_run: Value = read_json(Path::new(build["record"].as_str().unwrap_or_default())).map_err(AdmissionError::tool)?;
        let items: Vec<Value> = build["items"].as_array().cloned().unwrap_or_default();
        let read = |key: &str| -> Value { evaluation.pointer(key).and_then(Value::as_str).and_then(|f| read_json::<Value>(Path::new(f)).ok()).unwrap_or(Value::Null) };
        let evidence = vec![(ENGINE_QUALIFICATION_KIND, float_free(&read("/qualification/file"))), (ENGINE_VARIANTS_KIND, float_free(&read("/variants/matrix/file")))];
        let inputs = self.config.inputs.clone();
        let statement = inputs.sessions[0].1.statement();
        let schema = EngineSchema { tables: &statement.instance.doc.tables, ddl: &statement.schema_ddl, frontend: &statement.instance.doc.frontend };
        let store = self.bench.store()?;
        let capture = CurrentCapture::of(&self.bench.capture.current()).map_err(AdmissionError::tool)?;
        let policy = self.bench.config.storage_policy.clone();
        let allowance = self.bench.config.live_bytes_allowance;
        let (admitted, uses, registered, storage_policy) = {
            let lock = LibraryLock::acquire(&store, BUDGET_LOCK)?;
            let workspace_indices: Vec<usize> = checked.workspace.iter().map(|(index, _, _)| *index).collect();
            let admitted_uses: Vec<VerusStorageUseV1> = checked.uses.iter().enumerate().filter(|(i, _)| !workspace_indices.contains(i))
                .map(|(_, (name, package, _))| VerusStorageUseV1 { name: name.clone(), package: *package }).collect();
            let holders: Vec<PayloadHolder> = checked.workspace.iter().map(|(_, c, f)| PayloadHolder::of_manifest(&f.manifest, Some(c.package))).collect::<Result<_, _>>()?;
            let new: Vec<NewEngineStorage<'_>> = holders.iter().zip(&checked.workspace).map(|(holder, (_, c, _))| NewEngineStorage { holder: holder.clone(), asset_directory: &c.asset_directory }).collect();
            let storage_policy = check_engine_storage_uses(&store, &capture, self.schema(), &policy, &BudgetRule::Allowance { allowance_bytes: allowance }, &admitted_uses, &new)?;
            drop(new);
            let registrations = self.bench.register_checked(&store, &lock, checked.workspace.iter_mut().map(|(_, c, f)| (c, &*f)).collect(), &registered_by, &policy.standing())?;
            let registered = checked.registered(registrations);
            let uses: Vec<VerusStorageUseV1> = registered.iter().map(|(name, package, _)| VerusStorageUseV1 { name: name.clone(), package: *package }).collect();
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
            let admitted = admit_engine_version(&lock, &store, &capture, &policy, allowance, schema, candidate)?;
            (admitted, uses, registered, storage_policy)
        };
        let admission = admitted.record();
        let timing = self.time_admitted(&engine, frozen_dir, &uses, evaluation, &work.join("timing"));
        write_json_atomic(&work.join("timing.json"), &timing).map_err(AdmissionError::tool)?;
        let version = round.next_version;
        let directory = rounds::write_version(&rounds::VersionWrite {
            engine_dir: &self.config.engine_dir,
            version,
            round: round.round,
            frozen_dir,
            engine: &engine,
            uses: &uses.iter().map(|u| (u.name.clone(), u.package)).collect::<Vec<_>>(),
            evaluation,
            admission: &admission,
            timing: &timing,
            training: &self.inputs().training_facts,
        })?;
        Ok(json!({"qualified":true,"kind":"verus_engine_version","version":version,"library_version":admitted.version,"directory":directory,"admission":admission,
            "storage_policy_before_registration":storage_policy,"timing":{"status":timing["status"],"stop":timing["stop"],"file":work.join("timing.json")},
            "registrations":registered.iter().filter_map(|(_, _, r)| r.as_ref().map(|r| json!(r))).collect::<Vec<_>>()}))
    }

    /// The official timing of an admitted version over its admitted storage assets (module documentation): the
    /// official matrix with every failing cell recorded (its template then has no total at that worker count, so the
    /// stop cannot hold); the totals and the stop decision; the variant ratio report against the evaluation's variant
    /// matrix; and, when the stop holds, the other visible bindings. Timing records and never gates: an error is
    /// recorded as the timing's status, and the version stays admitted.
    fn time_admitted(&mut self, engine: &FrozenEngine, frozen_dir: &Path, uses: &[VerusStorageUseV1], evaluation: &Value, dir: &Path) -> Value {
        let started = Instant::now();
        let mut timing = self.official_timing(engine, frozen_dir, uses, evaluation, dir).unwrap_or_else(|e| {
            json!({"status":"failed","class":e.class,"error":e.message,"totals":null,
                "stop":{"stop":false,"rule":super::totals::STOP_RULE,"reasons":[format!("the official timing failed: {e}")]},"other_bindings":[]})
        });
        timing["timing_ns"] = json!(started.elapsed().as_nanos() as u64);
        timing["meaning"] = json!("the official timing of the admitted version: it records and never gates acceptance");
        timing
    }

    fn official_timing(&mut self, engine: &FrozenEngine, frozen_dir: &Path, uses: &[VerusStorageUseV1], evaluation: &Value, dir: &Path) -> Result<Value, AdmissionError> {
        let locks = self.bench.config.locks.clone();
        // The evaluation's whole-crate build of the same frozen crate (the session cache; built again only if missing).
        let build = self.builds.compile(&locks, engine, frozen_dir, &dir.join("verus-build"), false)?;
        let store = self.bench.store()?;
        let capture = CurrentCapture::of(&self.bench.capture.current()).map_err(AdmissionError::tool)?;
        let (inputs_uses, _) = engine_assets(&store, uses, &capture)?;
        let inputs = self.config.inputs.clone();
        let official: Vec<&EncodedStatement> = inputs.statements.official.iter().collect();
        let matrix = self.recorded_matrix(&build, &inputs_uses, &official, &inputs.workers, &dir.join("official"))?;
        let official_view = write_matrix(&matrix, &dir.join("official-matrix.json"))?;
        let medians = matrix.medians(&inputs.training.timing_binding).map_err(|e| AdmissionError::tool(e.to_string()))?;
        let report = totals(&inputs.baselines, &medians, &inputs.workers).map_err(|e| AdmissionError::tool(e.to_string()))?;
        let variants: EngineMatrix = read_json(Path::new(evaluation["variants"]["matrix"]["file"].as_str().unwrap_or_default())).map_err(AdmissionError::tool)?;
        let ratios = variant_ratios(&matrix, &variants);
        let ratio_file = dir.join("variant-ratios.json");
        write_json_atomic(&ratio_file, &json!(ratios)).map_err(AdmissionError::tool)?;
        let other_bindings = if report.stop.stop { self.other_bindings(&build, &inputs_uses, dir)? } else { vec![] };
        let failed = matrix.failed.len() + other_bindings.iter().map(|o| o["matrix"]["failed"].as_array().map_or(0, Vec::len)).sum::<usize>();
        Ok(json!({"status":if failed == 0 { "timed" } else { "timed_with_failed_cells" },"failed_cells":failed,"official":official_view,"totals":report,"stop":report.stop,
            "variants":{"ratios":{"summary":ratios.summary,"without_template":ratios.without_template,"note":ratios.note,"file":ratio_file}},
            "other_bindings":other_bindings,"storage_assets":"the admitted version's assets for the current capture (storage::engine_library::engine_assets)"}))
    }

    /// For a version whose official totals meet the stop: every other visible binding's matrix and totals (reported,
    /// never a stop condition), failing cells recorded.
    fn other_bindings(&self, build: &EngineBuild, uses: &[StorageUseInput], dir: &Path) -> Result<Vec<Value>, AdmissionError> {
        let inputs = self.config.inputs.clone();
        let mut results = vec![];
        for (binding, statements) in &inputs.statements.other_bindings {
            let statements: Vec<&EncodedStatement> = statements.iter().collect();
            let matrix = self.recorded_matrix(build, uses, &statements, &inputs.workers, &dir.join(format!("binding-{binding}")))?;
            let view = write_matrix(&matrix, &dir.join(format!("binding-{binding}-matrix.json")))?;
            let medians = matrix.medians(binding).map_err(|e| AdmissionError::tool(e.to_string()))?;
            let report: TotalsReport = totals(&inputs.baselines, &medians, &inputs.workers).map_err(|e| AdmissionError::tool(e.to_string()))?;
            results.push(json!({"binding":binding,"matrix":view,"totals":report,"meaning":"reported for the stopping version; never a stop condition"}));
        }
        Ok(results)
    }

    // ------------------------------------------------------------------------------------------------ engine tools

    /// One engine tool (`check`, `verify`, `compile`, `trial`, `profile`): freeze the named engine manifest into the job,
    /// then the action.
    fn engine_job(&mut self, workspace: &Path, job: &Path, action: ToolAction, arguments: &LocalJobArguments) -> Result<Value, AdmissionError> {
        if arguments.statement.is_some() || arguments.arguments.is_some() {
            return Err(AdmissionError::missing_input("statement and arguments are not engine-tool arguments: use templates, binding or sql"));
        }
        let input = arguments.candidate.as_ref().expect("checked: engine tools carry a candidate");
        let (_, relative) = resolve_candidate_manifest(workspace, input).map_err(AdmissionError::missing_input)?;
        let submission = CandidateSubmission { candidate_manifest: relative, rationale: "local job".into(), data_access_analysis: "diagnostic snapshot".into() };
        let frozen_dir = job.join("frozen");
        let frozen = self.freeze_submission(workspace, &frozen_dir, &submission)?;
        let engine = &frozen.engine;
        let artifacts = json!({"frozen_candidate":frozen_dir.join("candidate.json"),"frozen_crate":frozen_dir.join("crate"),"author_files":engine.author_files,
            "storage_uses":engine.storage_uses.iter().map(|u| &u.name).collect::<Vec<_>>(),"crate_version":engine_version_id(engine, &frozen_dir)?});
        let locks = self.bench.config.locks.clone();
        let verus_dir = job.join("verus");
        match action {
            ToolAction::Check => {
                let rewritten = write_workspace_framework(&frozen.workspace_crate, &frozen.framework)?;
                return Ok(json!({"status":"accepted","artifacts":artifacts,"workspace_framework_rewritten":rewritten,"workspace_framework":frozen.workspace_crate.join("src"),
                    "checks":"manifest, storage uses, coverage of every column of every table, storage composition, central source rule, static items, engine rules, framework files; items are checked against Verus output by verify/compile"}));
            }
            ToolAction::Verify if !arguments.modules.is_empty() => {
                let krate = engine.crate_in(&frozen_dir);
                let run = crate::query::compile::verify_modules(&locks, &krate, CrateKind::Engine, &engine.compiler, &arguments.modules, &verus_dir)?;
                return Ok(json!({"status":"verified_modules","scope":arguments.modules,"verification":run["verification"],"detail":run["detail"],"wall_ns":run["wall_ns"],
                    "record":verus_dir.join("run.json"),"artifacts":artifacts,"note":"module-scoped diagnostic run: NOT a whole-crate verification; submissions are always verified whole"}));
            }
            ToolAction::Verify => {
                let (record, reused) = self.builds.verify(&locks, engine, &frozen_dir, &verus_dir)?;
                return Ok(json!({"status":"verified","reused":reused,"verification":record["verification"],"record":record["record"],"artifacts":artifacts}));
            }
            _ => {}
        }
        let verification = arguments.verification();
        let build = match verification {
            TrialVerification::WholeCrate => self.builds.compile(&locks, engine, &frozen_dir, &verus_dir, false)?,
            TrialVerification::NotRun => self.builds.compile_unverified(&locks, engine, &frozen_dir, &verus_dir)?,
        };
        let build_view = json!({"reused":build.reused,"record":build.record});
        if action == ToolAction::Compile {
            return Ok(json!({"status":"compiled","build":build_view,"artifacts":artifacts}));
        }
        let storages = self.storages(engine, &frozen_dir, job, verification)?;
        let mut result = self.run_engine_cells(&build, &storages, job, action, arguments)?;
        if verification == TrialVerification::NotRun {
            result["status"] = json!("diagnostic_unverified");
            result["verification"] = json!(UNVERIFIED_LABEL);
            result["note"] = json!("diagnostic_unverified: this library was compiled with rust_verify --no-verify, so no proof obligation of the engine crate was checked; the run and comparisons are real, but the result is never a submission, proof or official measurement");
        }
        result["build"] = build_view;
        result["artifacts"] = artifacts;
        result["storage"] = json!(storages.iter().map(storage_view).collect::<Vec<_>>());
        Ok(result)
    }

    /// Freeze a submission (or a tool's snapshot) of the workspace's engine manifest.
    pub(super) fn freeze_submission(&mut self, workspace: &Path, frozen_dir: &Path, submission: &CandidateSubmission) -> Result<super::submission::Frozen, AdmissionError> {
        let substitutes = BTreeMap::new();
        let inputs = self.config.inputs.clone();
        let context = EngineFreeze {
            workspace,
            schema: self.schema(),
            library: &self.bench.config.library,
            substitutes: &substitutes,
            policy: &self.bench.config.storage_policy,
            rules: &inputs.rules,
        };
        match self.stage {
            Some(stage) => stage.freeze(&context, frozen_dir, submission),
            None => freeze_engine(&context, frozen_dir, submission),
        }
    }

    /// The cells of a trial or profile: the named templates at one binding (default every template at the timing
    /// binding), or the author's own statements; every requested worker count; each cell in one fresh child under the
    /// timing lease.
    fn run_engine_cells(&self, build: &EngineBuild, storages: &[ResolvedStorage], job: &Path, action: ToolAction, arguments: &LocalJobArguments) -> Result<Value, AdmissionError> {
        let inputs = self.config.inputs.clone();
        let binding = arguments.binding.clone().unwrap_or_else(|| inputs.training.timing_binding.clone());
        let mut adhoc = vec![];
        let statements: Vec<EncodedStatement> = if !arguments.sql.is_empty() {
            if !arguments.templates.is_empty() || arguments.binding.is_some() {
                return Err(AdmissionError::missing_input("sql runs your own statements: give either sql or templates/binding"));
            }
            let (checks, encoded) = self.prepare_adhoc(&arguments.sql, job)?;
            adhoc = checks;
            encoded
        } else {
            let at_binding: Vec<&EncodedStatement> = if binding == inputs.training.timing_binding {
                inputs.statements.official.iter().collect()
            } else {
                inputs.statements.at_binding(&binding).ok_or_else(|| AdmissionError::missing_input(format!("binding {binding} is not a visible binding")))?.iter().collect()
            };
            let wanted: Vec<&EncodedStatement> =
                if arguments.templates.is_empty() { at_binding } else { at_binding.into_iter().filter(|s| arguments.templates.contains(&s.statement.template)).collect() };
            if let Some(unknown) = arguments.templates.iter().find(|t| !inputs.training.templates.iter().any(|x| &x.name == *t)) {
                return Err(AdmissionError::missing_input(format!("{unknown} is not a training template")));
            }
            wanted.into_iter().cloned().collect()
        };
        if action == ToolAction::Profile && (statements.len() != 1 || arguments.workers.is_none()) {
            return Err(AdmissionError::missing_input("profile runs one cell: workers and exactly one template or one sql statement"));
        }
        let workers: Vec<usize> = match arguments.workers {
            Some(w) if inputs.workers.contains(&w) => vec![w],
            Some(w) => return Err(AdmissionError::missing_input(format!("workers {w} is not a configured worker count {:?}", inputs.workers))),
            None => inputs.workers.clone(),
        };
        let uses = storage_inputs(storages);
        // The general line profiles with the sampler (`engine::profile`): self time per function, under the call limits.
        if let (ToolAction::Profile, Some(general), [statement], [w]) = (action, inputs.general.as_ref(), statements.as_slice(), workers.as_slice()) {
            let subject = super::profile::ProfileSubject { runner: self.bench.runner(), library: &build.library, uses: &uses, access: inputs.part_access, limits: general.call_limits };
            let profile = {
                let _lease = self.bench.config.locks.timing().map_err(AdmissionError::tool)?;
                super::profile::profile_statement(&subject, &statement.statement, *w, &job.join("profile-work"))?
            };
            super::profile::write_profile(job, &format!("{} at {w} workers", statement.statement.name()), std::slice::from_ref(&profile)).map_err(AdmissionError::tool)?;
            return Ok(json!({"status":"completed","profile":profile,"report":job.join(super::profile::PROFILE_FILE),"method":super::profile::PROFILE_METHOD,
                "meaning":"a diagnostic: never a submission, proof or official measurement"}));
        }
        let calls = if action == ToolAction::Profile { PROFILE_REPETITIONS } else { 1 + arguments.hot_calls.unwrap_or(DEFAULT_TRIAL_HOT_CALLS) };
        let cells = EngineCells { runner: self.runner(&build.library, &uses), checks: &inputs.checks, adhoc: &adhoc, bound: arguments.timeout_seconds };
        let locks = self.bench.config.locks.clone();
        let mut records = vec![];
        let mut sums: BTreeMap<usize, u64> = BTreeMap::new();
        for statement in &statements {
            for &w in &workers {
                let request = CellRequest { statement: &statement.statement, workers: w, calls };
                let record = {
                    let _lease = locks.timing().map_err(AdmissionError::tool)?;
                    cells.run_cell(request, &job.join("cells").join(statement.statement.name()).join(format!("w{w}")))?
                };
                // The answers stored bounded (general line, the author's own statements over the bound), beside the status.
                let stored_answers = record.get("stored_answers").cloned();
                let median = record["median_hot_wall_ns"].as_u64();
                let baseline = inputs.baselines.cell(&statement.statement.template, &statement.statement.binding, w);
                if let (Some(m), true) = (median, statement.statement.variant.is_none()) {
                    *sums.entry(w).or_default() += m;
                }
                let mut entry = json!({"statement":statement.statement.name(),"binding":statement.statement.binding,"workers":w,"status":record["status"],
                    "echo":record["echo"],"comparison":record["comparison"],"warm_wall_ns":record["warm_wall_ns"],"hot_wall_ns":record["hot_wall_ns"],"median_hot_wall_ns":median,
                    "baseline":baseline.map(|b| json!({"umbra_ns":b.umbra_ns,"duckdb_ns":b.duckdb_ns,"faster_ns":b.faster_ns()})),
                    "ratio_to_faster":baseline.zip(median).map(|(b, m)| m as f64 / b.faster_ns().max(1) as f64),
                    "record":record});
                if let Some(stored_answers) = stored_answers {
                    entry["stored_answers"] = stored_answers;
                }
                records.push(entry);
            }
        }
        let every_template = arguments.sql.is_empty() && statements.len() == inputs.training.templates.len();
        let names: BTreeSet<&str> = inputs.training.templates.iter().map(|t| t.name.as_str()).collect();
        let job_totals: Vec<Value> = if every_template {
            workers
                .iter()
                .filter_map(|w| {
                    let (duckdb, umbra) = inputs.baselines.totals(&names, &binding, *w).ok()?;
                    let engine = *sums.get(w)?;
                    let (target, _) = super::totals::target_of(duckdb, umbra);
                    Some(json!({"workers":w,"engine_ns":engine,"umbra_ns":umbra,"duckdb_ns":duckdb,"target_ns":target,"margin":target as f64 / engine.max(1) as f64}))
                })
                .collect()
        } else {
            vec![]
        };
        Ok(json!({"status":"completed","binding":if arguments.sql.is_empty() { json!(binding) } else { Value::Null },"workers":workers,"calls_per_cell":calls,
            "cells":records,"totals":job_totals,
            "totals_meaning":"present only when every training template ran: the sum of this job's medians per worker count against the saved baselines' totals (one job, not the official protocol)"}))
    }

    /// The author's own statements (no parameters): each prepared over the run's dataset like the templates
    /// (`TemplateCheck::prepare`, statement records under the job; no saved answers, so its cells are `not_compared`,
    /// and on the general line their children store each answer over `AnswerBound::STORED` as its row count, digest
    /// and first rows) and encoded at its one binding.
    fn prepare_adhoc(&self, sql: &[String], job: &Path) -> Result<(Vec<TemplateCheck>, Vec<EncodedStatement>), AdmissionError> {
        let inputs = self.inputs();
        let validation = ValidationPolicy::FormalProofs { numeric_relative_tolerance: inputs.numeric_relative_tolerance.clone(), required_engines: vec![], saved_answers: vec![] };
        let (mut checks, mut encoded) = (vec![], vec![]);
        for (index, text) in sql.iter().enumerate() {
            let name = format!("sql-{index}");
            let started = Instant::now();
            let mut check = TemplateCheck::prepare(&self.bench.config.parser, &inputs.dataset, inputs.constraints.as_ref(), &validation, &name, &name, text, &[], &[], &job.join("statements").join(&name))
                .map_err(|e| AdmissionError::new(e.class, format!("sql[{index}]: {e}")))?;
            check.bindings = vec![BenchmarkBinding { name: CONCRETE_BINDING.into(), arguments: vec![] }];
            let translate_ns = started.elapsed().as_nanos() as u64;
            let started = Instant::now();
            let ast = check.ast(CONCRETE_BINDING)?;
            encoded.push(EncodedStatement {
                echo: gendb_sqlspec::evaluator::echo_text(&ast.document),
                statement: EngineStatement { template: name, variant: None, binding: CONCRETE_BINDING.into(), ast: ast.bytes },
                translate_ns,
                encode_ns: started.elapsed().as_nanos() as u64,
            });
            checks.push(check);
        }
        Ok((checks, encoded))
    }
}

/// The agent stub of an empty engine crate.
const AGENT_STUB: &str = "\
//! The engine (author-owned). `crate::agent::engine` answers every supported query over the stored data; its
//! signature and obligation are in the contract (obligations.json `engine`, fixed/engine_entry.rs). Run the `check`
//! tool first: it writes the crate's framework files for the storage uses in verus-engine.json.
use vstd::prelude::*;

verus! {

// pub fn engine(stores: &mut Stores, q: &EOrderedQuery, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)
//     requires stores_ready(old(stores)@), supported(view_ordered(*q)), 1 <= workers <= MAX_WORKERS,
//     ensures answer_meets(old(stores)@, view_ordered(*q), r),

} // verus!
";

/// Workspace entries the framework generates in every round (never copied from a previous round's workspace).
const GENERATED_ENTRIES: [&str; 11] = [
    "contract", "reference", "admitted-storages", "admitted-code", VERSIONS_DIRECTORY, "verus-tmp", "local-tool.json", "search-index.json", "search-index.txt", ENGINE_MAP_FILE,
    "verus-engine-example.json",
];

/// Seed the round's workspace once (module documentation) and return the seed record: what was copied from where,
/// and the carried notes.
pub fn seed_workspace(workspace: &Path, seed: &RoundSeed, seeded: &[(String, ContentId)]) -> Result<Value, AdmissionError> {
    let crate_src = workspace.join(super::submission::CRATE_DIRECTORY).join("src");
    let copied: Vec<String> = match (&seed.kind, &seed.from) {
        (rounds::SeedKind::Version, Some(version)) => {
            // The author's own copy: writable (the version folder's code keeps the frozen crate's read-only modes).
            copy_tree(&version.join("code/agent"), &crate_src.join("agent"), false)?;
            make_writable(&crate_src.join("agent"))?;
            if version.join("code/storages").is_dir() {
                copy_tree(&version.join("code/storages"), &workspace.join("new-storages"), false)?;
                make_writable(&workspace.join("new-storages"))?;
            }
            fs::copy(version.join("seed-manifest.json"), workspace.join(MANIFEST_FILE)).map_err(AdmissionError::tool)?;
            vec!["engine/src/agent".into(), MANIFEST_FILE.into()]
        }
        (rounds::SeedKind::PreviousRound, Some(previous)) => {
            let mut copied = vec![];
            for entry in fs::read_dir(previous).map_err(AdmissionError::tool)? {
                let path = entry.map_err(AdmissionError::tool)?.path();
                let name = path.file_name().and_then(|n| n.to_str()).unwrap_or_default().to_string();
                if GENERATED_ENTRIES.contains(&name.as_str()) || name == NOTES_FILE {
                    continue;
                }
                let target = workspace.join(&name);
                if path.is_dir() { copy_tree(&path, &target, false)? } else { copy_file(&path, &target)? }
                copied.push(name);
            }
            copied
        }
        _ => {
            fs::create_dir_all(crate_src.join("agent")).map_err(AdmissionError::tool)?;
            fs::write(crate_src.join("agent/mod.rs"), AGENT_STUB).map_err(AdmissionError::tool)?;
            write_json_atomic(&workspace.join(MANIFEST_FILE), &json!(EngineManifest::example(seeded))).map_err(AdmissionError::tool)?;
            vec!["engine/src/agent/mod.rs (stub)".into(), MANIFEST_FILE.into()]
        }
    };
    let notes_text = match &seed.notes {
        Some(notes) if notes.is_file() => {
            fs::copy(notes, workspace.join(NOTES_FILE)).map_err(AdmissionError::tool)?;
            Some(fs::read_to_string(notes).map_err(AdmissionError::tool)?)
        }
        _ => None,
    };
    // Each copy is named by its run folder (`versions/vNNN/`), as in the run's records and the output home.
    let versions_dir = workspace.join(VERSIONS_DIRECTORY);
    let copies: Vec<(String, &PathBuf)> = seed.versions.iter().map(|(name, dir)| (dir.file_name().map_or_else(|| name.clone(), |f| f.to_string_lossy().into_owned()), dir)).collect();
    for (name, directory) in &copies {
        for part in ["code", "manifest.json", NOTES_FILE, "README.md"] {
            let from = directory.join(part);
            if from.is_dir() {
                copy_tree(&from, &versions_dir.join(name).join(part), true)?;
            } else if from.is_file() {
                copy_file(&from, &versions_dir.join(name).join(part))?;
                set_read_only(&versions_dir.join(name).join(part))?;
            }
        }
    }
    Ok(json!({"format_version":1,"seed":seed,"copied":copied,"notes_from":notes_text.as_ref().map(|_| seed.description.clone()),"notes_text":notes_text,
        "read_only_versions":copies.iter().map(|(name, _)| versions_dir.join(name)).collect::<Vec<_>>(),"seeded_unix_ms":now_unix_ms()}))
}

fn copy_file(from: &Path, to: &Path) -> Result<(), AdmissionError> {
    if let Some(parent) = to.parent() {
        fs::create_dir_all(parent).map_err(AdmissionError::tool)?;
    }
    fs::copy(from, to).map(drop).map_err(|e| AdmissionError::tool(format!("copy {} to {}: {e}", from.display(), to.display())))
}

fn set_read_only(path: &Path) -> Result<(), AdmissionError> {
    use std::os::unix::fs::PermissionsExt;
    fs::set_permissions(path, fs::Permissions::from_mode(0o444)).map_err(AdmissionError::tool)
}

/// Give the owner write permission on every file under `dir`: the seeded author files, which [`copy_tree`] copies with
/// the frozen crate's read-only modes (contents unchanged).
pub(crate) fn make_writable(dir: &Path) -> Result<(), AdmissionError> {
    use std::os::unix::fs::PermissionsExt;
    for entry in fs::read_dir(dir).map_err(|e| AdmissionError::tool(format!("{}: {e}", dir.display())))? {
        let entry = entry.map_err(AdmissionError::tool)?;
        let kind = entry.file_type().map_err(AdmissionError::tool)?;
        if kind.is_dir() {
            make_writable(&entry.path())?;
        } else if kind.is_file() {
            let mode = entry.metadata().map_err(AdmissionError::tool)?.permissions().mode();
            fs::set_permissions(entry.path(), fs::Permissions::from_mode(mode | 0o200)).map_err(AdmissionError::tool)?;
        }
    }
    Ok(())
}

/// Copy the tree `from` to `to` (files only, symbolic links skipped); `read_only` marks every copied file read-only.
pub(crate) fn copy_tree(from: &Path, to: &Path, read_only: bool) -> Result<(), AdmissionError> {
    fs::create_dir_all(to).map_err(AdmissionError::tool)?;
    for entry in fs::read_dir(from).map_err(|e| AdmissionError::tool(format!("{}: {e}", from.display())))? {
        let entry = entry.map_err(AdmissionError::tool)?;
        let kind = entry.file_type().map_err(AdmissionError::tool)?;
        let target = to.join(entry.file_name());
        if kind.is_dir() {
            copy_tree(&entry.path(), &target, read_only)?;
        } else if kind.is_file() {
            copy_file(&entry.path(), &target)?;
            if read_only {
                set_read_only(&target)?;
            }
        }
    }
    Ok(())
}

/// The role's policy: the schema line's round policy, or a general-line session's.
#[derive(Clone)]
pub enum EngineRolePolicy {
    Round(EnginePolicy),
    Session(GeneralSessionPolicy),
}

impl RolePolicy for EngineRolePolicy {
    fn author_prompt(&self, input: &PromptInput) -> String {
        match self {
            Self::Round(policy) => policy.author_prompt(input),
            Self::Session(policy) => policy.author_prompt(input),
        }
    }

    fn objective_status(&self, context: &Value, trials: &[Trial]) -> Value {
        match self {
            Self::Round(policy) => policy.objective_status(context, trials),
            Self::Session(policy) => policy.objective_status(context, trials),
        }
    }

    fn search_stop(&self, context: &Value, trials: &[Trial]) -> Option<StopReason> {
        match self {
            Self::Round(policy) => policy.search_stop(context, trials),
            Self::Session(policy) => policy.search_stop(context, trials),
        }
    }

    fn submission_code(&self, frozen_dir: &Path, candidate: &Value, workspace: Option<&Path>) -> Value {
        match self {
            Self::Round(policy) => policy.submission_code(frozen_dir, candidate, workspace),
            Self::Session(policy) => policy.submission_code(frozen_dir, candidate, workspace),
        }
    }
}

impl SynthesisRole for EngineAuthorRole {
    type Policy = EngineRolePolicy;

    fn policy(&self) -> EngineRolePolicy {
        match &self.config.mode {
            EngineRoleMode::Session(session) => EngineRolePolicy::Session(GeneralSessionPolicy { prompt: session.prompt, spend: session.spend.clone() }),
            _ => EngineRolePolicy::Round(EnginePolicy),
        }
    }

    async fn prepare(&mut self, request: &RunRequest, workspace: &Path) -> Result<Value, String> {
        match self.config.mode {
            EngineRoleMode::Session(_) => self.view().prepare_session(request, workspace),
            _ => self.view().prepare_workspace(request, workspace),
        }
        .map_err(|e| e.to_string())
    }

    /// The storage budget as it stands now (the catalog and budget files of the contract are rewritten too); in a
    /// general-line session also the run's spend, the library's bytes and its storage assets (the
    /// head's derived bytes, the free space, the floor and the rule: `storage::asset_release`).
    async fn refresh_shared_facts(&mut self) -> Result<Value, String> {
        let facts = self.bench.refresh_shared_facts().map_err(|e| e.to_string())?;
        match &self.config.mode {
            EngineRoleMode::Round(_) | EngineRoleMode::Framework => Ok(json!({"storage_budget":facts["storage_budget"]})),
            EngineRoleMode::Session(session) => {
                let spend = session.spend.now().map_err(|e| e.to_string())?;
                let library = crate::storage::engine_library::library_bytes(&self.bench.config.library).map_err(|e| e.to_string())?;
                let assets = crate::storage::asset_release::storage_assets_facts(&self.bench.config.library);
                let mut refreshed = json!({"storage_budget":facts["storage_budget"],"run_spend":{"spent_usd":spend.spent,"reserved_usd":spend.reserved,"complete":spend.complete,
                    "budget_usd":session.spend.budget,"left_usd":session.spend.budget.remaining_after(spend.spent)},"library_bytes":library,"storage_assets":assets});
                // A stage run: the stage view as it stands now (the stage fixture, the top-level `stage`); a run of several
                // workloads: the workloads view and the combined score (the workloads fixture, the top-level `workloads` and
                // `combined_score`).
                let view = self.view();
                if let Some(stage) = view.stage_view() {
                    refreshed["stage"] = stage;
                }
                if let Some((workloads, combined)) = view.workloads_view() {
                    refreshed["workloads"] = workloads;
                    refreshed["combined_score"] = combined;
                }
                Ok(refreshed)
            }
        }
    }

    async fn freeze(&mut self, workspace: &Path, frozen_dir: &Path, submission: &CandidateSubmission) -> Result<Value, String> {
        match self.config.mode {
            EngineRoleMode::Session(_) => self.view().freeze_session_submission(workspace, frozen_dir, submission).map_err(|e| e.to_string()),
            _ => self.view().freeze_submission(workspace, frozen_dir, submission).map(|frozen| json!(frozen.engine)).map_err(|e| e.to_string()),
        }
    }

    async fn evaluate(&mut self, frozen_dir: &Path, candidate: &Value) -> Result<Value, String> {
        let started = Instant::now();
        let dir = fresh_evaluation_dir(frozen_dir).map_err(|e| e.to_string())?;
        let mut result = match self.config.mode {
            EngineRoleMode::Round(_) | EngineRoleMode::Framework => {
                let outcome = serde_json::from_value::<FrozenEngine>(candidate.clone())
                    .map_err(AdmissionError::tool)
                    .and_then(|engine| self.view().evaluate_frozen(&dir, frozen_dir, &engine));
                match outcome {
                    Ok(value) => value,
                    Err(error) => json!({"kind":"verus_engine","eligible":false,"status":error.class,"failure_class":error.class,"error":error.to_string()}),
                }
            }
            EngineRoleMode::Session(_) => self.view().evaluate_session_submission(&dir, frozen_dir, candidate),
        };
        result["framework_evaluation_ns"] = json!(started.elapsed().as_nanos() as u64);
        result["record"] = json!(dir.join("engine-evaluation.json"));
        protect_eligible_assets(&mut self.bench, &mut result, &dir);
        write_new_json(&dir.join("engine-evaluation.json"), &result).map_err(|e| e.to_string())?;
        Ok(result)
    }

    async fn qualify(&mut self, frozen_dir: &Path, evaluation: &Value) -> Result<Value, String> {
        match self.config.mode {
            EngineRoleMode::Session(_) => Ok(super::acceptance::recorded_acceptance(evaluation)),
            _ => self.view().qualify_evaluated(frozen_dir, evaluation).map_err(|e| e.to_string()),
        }
    }

    /// A round's resolution: the new version, or the round's attempt (the next round starts from the latest version).
    /// A session's: every version and attempt its submissions became, and why it ended.
    async fn close(&mut self, trials: &[Trial], qualification: &[QualificationAttempt]) -> Result<Value, String> {
        let round = match &self.config.mode {
            EngineRoleMode::Round(round) => round.round,
            EngineRoleMode::Framework => return Err("no author session runs in framework mode".into()),
            EngineRoleMode::Session(_) => {
                let trial_assets = release_trial_assets(&mut self.bench, trials, trials.iter().any(|t| t.evaluation["accepted"] == true));
                return Ok(super::acceptance::session_resolution(trials, trial_assets));
            }
        };
        let accepted = qualification.iter().find(|q| q.qualified());
        let trial_assets = release_trial_assets(&mut self.bench, trials, accepted.is_some());
        Ok(match accepted {
            Some(q) => json!({"status":"version_accepted","round":round,"version":q.result["version"],"directory":q.result["directory"],
                "iteration":q.iteration,"trial_assets":trial_assets}),
            None => {
                let last = trials.last();
                json!({"status":"attempt","round":round,"iteration":last.map(|t| t.iteration),
                    "evaluation_status":last.map(|t| t.evaluation["status"].clone()),"failure_class":last.map(|t| t.evaluation["failure_class"].clone()),
                    "qualification_error":qualification.last().map(|q| q.result["error"].clone()),
                    "next":"the next round starts again from the latest version (or this round's workspace while no version exists)","trial_assets":trial_assets})
            }
        })
    }
}

impl LocalJobs for EngineAuthorRole {
    fn attach_local_session(&mut self, endpoint: &LocalSessionEndpoint) {
        self.bench.attach(endpoint);
    }

    /// The bench writes the job record; the engine tools run in [`EngineBench::engine_job`], the storage tools and
    /// `catalog` in the bench. On the general line, `storage_check` and `storage_register` also report the schema-name
    /// rule's findings over the storage's own interface and builder files ([`schema_name_feedback`]).
    async fn run_local_job(&mut self, evidence_root: &Path, action: &str, arguments: Value, job_id: u64) -> Result<Value, String> {
        let Self { bench, config, builds, stage } = self;
        let other = job_workload(stage.as_ref(), &arguments).map_err(|e| e.to_string())?;
        // `catalog` rewrites the contract's own catalog files, which are the primary's (a stage run's goal's); another
        // workload's catalog is its contract file `workloads/<name>/storages.json` and each registration's `use_as`.
        if let (Some(side), true) = (other, action == ToolAction::Catalog.name()) {
            let primary = if stage.as_ref().is_some_and(StageRole::is_members) { "primary" } else { "goal" };
            return Err(AdmissionError::missing_input(format!("catalog lists the {primary} workload's library; workload {}'s admitted storages are in its contract file workloads/{}/storages.json (as prepared), and storage_register returns each new storage's use_as", side.name, side.name)).to_string());
        }
        let run_job = |bench: &mut Workbench, config: &EngineRoleConfig, stage: Option<&StageRole>| {
            bench.job(AuthorRole::Engine, evidence_root, action, arguments, job_id, |bench, workspace, job, action, arguments| {
                EngineBench { bench, config, builds, stage }.engine_job(workspace, job, action, arguments)
            })
        };
        // Another workload's job: the session's bench viewing that workload, with its inputs and its crate.
        let (mut record, rules) = match other {
            Some(side) => (side.view.enter(bench, |bench| run_job(bench, &side.config, Some(&side.stage))), &side.config.inputs.rules),
            None => (run_job(bench, config, stage.as_ref()), &config.inputs.rules),
        };
        let record_value = record.as_mut().map_err(|e| e.to_string())?;
        if config.inputs.general.is_some() && matches!(action, "storage_check" | "storage_register") {
            schema_name_feedback(record_value, rules).map_err(|e| e.to_string())?;
        }
        record.map_err(|e| e.to_string())
    }
}

/// The other workload a job's `workload` argument names (`None`: the role's own, the primary, its default; module
/// documentation). Refused (`missing_input`): `workload` in a run of one workload, or a name that is not one of the run's
/// workloads.
pub(super) fn job_workload<'s>(stage: Option<&'s StageRole>, arguments: &Value) -> Result<Option<&'s super::stage::MemberSide>, AdmissionError> {
    let others: Vec<&str> = stage.map(|s| s.sides.iter().map(|k| k.name.as_str()).collect()).unwrap_or_default();
    let index = named_kept_workload(stage.map(|s| (s.workload.as_str(), others.as_slice())), arguments)?;
    Ok(index.and_then(|i| stage.and_then(|s| s.sides.get(i))))
}

/// [`job_workload`] over names: the index among `kept` (the other workloads) of the workload a job's `workload` argument
/// names, `None` for the role's own workload (named or absent). `stage`: the role's workload and the other workloads;
/// `None` in a run of one workload, where `workload` is refused.
pub(super) fn named_kept_workload(stage: Option<(&str, &[&str])>, arguments: &Value) -> Result<Option<usize>, AdmissionError> {
    let Some(named) = arguments.get("workload").filter(|w| !w.is_null()) else { return Ok(None) };
    let named = named.as_str().ok_or_else(|| AdmissionError::missing_input("workload is a workload's name"))?;
    let Some((own, kept)) = stage else { return Err(AdmissionError::missing_input("workload is an argument of a stage run's tools; this run has one workload")) };
    if named == own {
        return Ok(None);
    }
    kept.iter().position(|k| *k == named).map(Some).ok_or_else(|| {
        AdmissionError::missing_input(format!("workload {named} is not a workload of this run ({})", std::iter::once(own).chain(kept.iter().copied()).collect::<Vec<_>>().join(", ")))
    })
}

/// Feedback of a general-line storage tool (`storage_check`, `storage_register`): the schema-name rule's findings over
/// the frozen storage's own interface and builder files (`admission::engine::engine_storage_findings`), added to the
/// job record (`schema_name_feedback`) and its `result.json`. Feedback only: the submission's freeze and the admission
/// refuse them. A job that froze no storage is left as it is.
fn schema_name_feedback(record: &mut Value, rules: &EngineRuleSet) -> Result<(), AdmissionError> {
    let Some(storage) = record["paths"]["frozen"].as_str().map(PathBuf::from).filter(|p| p.ends_with("storage.json") && p.is_file()) else {
        return Ok(());
    };
    let frozen_dir = storage.parent().ok_or_else(|| AdmissionError::tool("a frozen storage record without its directory"))?;
    let frozen: crate::storage::freeze::FrozenStorage = read_json(&storage).map_err(AdmissionError::tool)?;
    let name = frozen.name()?;
    let src = frozen_dir.join("crate/src");
    let files = frozen
        .author_files
        .iter()
        .map(|file| Ok(gendb_verification::verus::FrameworkSource { path: file.clone(), text: fs::read_to_string(src.join(file)).map_err(AdmissionError::tool)? }))
        .collect::<Result<Vec<_>, AdmissionError>>()?;
    let findings = gendb_verification::admission::engine::engine_storage_findings(&files, &name, rules);
    record["schema_name_feedback"] = json!({"storage":name.as_str(),"findings":findings.iter().map(|f| json!({"file":f.file,"line":f.line,"rule":f.rule,"detail":f.detail})).collect::<Vec<_>>(),
        "meaning":"the general line's schema-name rule over this storage's own interface and builder files: a submission reading it is refused at freeze while any finding remains (feedback here; freeze and admission decide)"});
    if let Some(result) = record["result_record"].as_str() {
        write_json_atomic(Path::new(result), record).map_err(AdmissionError::tool)?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A general-line storage tool's record gains the schema-name findings of the frozen storage's own interface and
    /// builder files (`result.json` too); a record without a frozen storage is unchanged.
    #[test]
    fn storage_tools_report_schema_names_on_the_general_line() {
        use gendb_frontend::ast::{ColumnDef, PgType, TableDef};
        use gendb_verification::verus::engine_rules::{SchemaNames, TemplateConstants};
        let root = crate::controller::test_support::scratch_root("engine-storage-feedback");
        let schema = vec![TableDef { name: "region".into(), columns: vec![ColumnDef { name: "r_regionkey".into(), ty: PgType::Int8, nullable: false }], constraints: vec![] }];
        let declaration = gendb_verification::obligations::DeclaredSource::for_storage(&schema, &BTreeMap::from([(0, BTreeSet::from([0]))])).unwrap();
        let frozen_dir = root.join("job/frozen");
        let src = frozen_dir.join("crate/src");
        fs::create_dir_all(src.join("stores/keys/interface")).unwrap();
        fs::create_dir_all(src.join("builder")).unwrap();
        fs::write(src.join("stores/keys/interface/mod.rs"), "verus! { pub open spec fn r_regionkey_parts() -> nat { 1 } }").unwrap();
        fs::write(src.join("builder/mod.rs"), "verus! { pub fn build() {} }").unwrap();
        let frozen = crate::storage::freeze::FrozenStorage {
            manifest: crate::storage::manifest::StorageManifest { name: "keys".into(), ..crate::storage::manifest::StorageManifest::example() },
            declaration,
            compiler: Default::default(),
            modules: vec![],
            author_files: vec!["builder/mod.rs".into(), "stores/keys/interface/mod.rs".into()],
            framework_files: vec![],
            derivation: None,
        };
        write_json_atomic(&frozen_dir.join("storage.json"), &json!(frozen)).unwrap();
        let rules = EngineRuleSet::general_with_names(TemplateConstants::default(), SchemaNames::from_names(["region"], ["r_regionkey"]));
        let mut record = json!({"status":"completed","paths":{"frozen":frozen_dir.join("storage.json")},"result_record":root.join("job/result.json")});
        schema_name_feedback(&mut record, &rules).unwrap();
        let findings = record["schema_name_feedback"]["findings"].as_array().unwrap();
        assert_eq!(findings.len(), 1, "{record}");
        assert_eq!((findings[0]["file"].as_str(), findings[0]["rule"].as_str()), (Some("stores/keys/interface/mod.rs"), Some("schema_name")));
        assert_eq!(read_json::<Value>(&root.join("job/result.json")).unwrap()["schema_name_feedback"], record["schema_name_feedback"]);
        let mut without = json!({"status":"completed","paths":{"frozen":null}});
        schema_name_feedback(&mut without, &rules).unwrap();
        assert!(without.get("schema_name_feedback").is_none());
        fs::remove_dir_all(&root).unwrap();
    }

    /// The schema line seeds a round from a version folder whose code keeps the frozen crate's read-only modes: the
    /// author's copies (`engine/src/agent`, `new-storages`) are writable with the same bytes, while the version folder
    /// and the read-only copy of every earlier version under `versions/` stay read-only.
    #[test]
    fn a_version_seed_gives_the_author_writable_files() {
        use std::os::unix::fs::PermissionsExt;
        let root = crate::controller::test_support::scratch_root("engine-seed-modes");
        let version = root.join("run/versions/v001");
        let files = [
            ("code/agent/mod.rs", "engine/src/agent/mod.rs"),
            ("code/agent/helper.rs", "engine/src/agent/helper.rs"),
            ("code/storages/keys/crate/src/builder/mod.rs", "new-storages/keys/crate/src/builder/mod.rs"),
        ];
        for (file, _) in files {
            let path = version.join(file);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(&path, format!("// {file}\n")).unwrap();
            fs::set_permissions(&path, fs::Permissions::from_mode(0o444)).unwrap();
        }
        fs::write(version.join("seed-manifest.json"), "{}\n").unwrap();
        fs::write(version.join(NOTES_FILE), "# Notes\n").unwrap();
        let seed = RoundSeed {
            kind: rounds::SeedKind::Version,
            description: "v1 (round 1)".into(),
            version: Some("v1".into()),
            from: Some(version.clone()),
            notes: Some(version.join(NOTES_FILE)),
            versions: vec![("v1".into(), version.clone())],
        };
        let workspace = root.join("workspace");
        fs::create_dir_all(&workspace).unwrap();
        seed_workspace(&workspace, &seed, &[]).unwrap();
        let mode = |path: &Path| fs::metadata(path).unwrap().permissions().mode() & 0o777;
        for (file, copy) in files {
            assert_eq!(fs::read(workspace.join(copy)).unwrap(), fs::read(version.join(file)).unwrap(), "{copy}: same bytes");
            assert_ne!(mode(&workspace.join(copy)) & 0o200, 0, "{copy}: the author can write it");
            assert_eq!(mode(&version.join(file)), 0o444, "{file}: the version folder is unchanged");
        }
        let earlier = workspace.join(VERSIONS_DIRECTORY).join("v001/code/agent/mod.rs");
        assert_eq!(mode(&earlier) & 0o222, 0, "the read-only copy of the version stays read-only");
        fs::remove_dir_all(&root).unwrap();
    }

    /// Evidence stored in the library holds no floating point: every non-integer becomes its decimal text, integers
    /// and structure stay.
    #[test]
    fn evidence_is_float_free() {
        let value = json!({"margin":0.5,"rows":[{"ratio":1.25,"ns":7}],"name":"v1","stop":true});
        assert_eq!(float_free(&value), json!({"margin":"0.5","rows":[{"ratio":"1.25","ns":7}],"name":"v1","stop":true}));
    }
}
