//! The requests and input files of a run's work folder, written from a workload folder, its settings, the machine
//! ([`RunContext`]) and what the run's earlier steps recorded per scale ([`ScaleInputs`]: the capture, the data size
//! and the baselines).
//!
//! - templates mode: [`templates_request`], one request: the workload storage session first (`storage = "designed"`,
//!   `physical_only` within the data size) or the fixed flat storage (`"plain"`, `fixed_flat`), then the query sessions.
//!   Written without a capture and without baselines it is the preparation request (`gendb preflight` writes the
//!   capture for `designed`, `gendb prepare-flat-storage` the capture and the flat storages for `plain`).
//! - engine mode: [`flat_preparation_request`] per scale (`gendb prepare-flat-storage` into the run's library), then
//!   [`engine_request`], a general-line request whose scales come from the run's records; each `[[members]]` folder gets
//!   its own request ([`engine_request`] with the member's name, written to `requests/members/<name>.json`).
//! - [`write_inputs`]: `inputs/templates.json` (and the statements' SQL), `inputs/bindings-<scale>.json`,
//!   `inputs/data-size-<scale>.json` and, without the folder's own, an empty `inputs/variants.json`.
//!
//! GenDB fills in itself: the dataset and integrity constraints (from `schema.sql`), the library (`WORK/library`; a
//! member's `WORK/members/<name>/library`), the output home (`WORK/output`; none for a member), the host locks and the
//! author executable ([`RunContext::from_environment`]), the capture, the eligible flat storages (from the
//! `flat-storage.json` record of `gendb prepare-flat-storage`), objectives, targets and saved answers (from the bindings
//! and the baselines). Fixed: the provider-cost stop policy `estimated_usd`, no retry or call-time guard.
//!
//! A baselines folder holds `baselines.json`: `{"targets": "targets.json", "engines": [{"name": "duckdb",
//! "description": "..", "answers": "answers/duckdb/{query}/{binding}.json"}]}`, paths relative to it. `targets` (per
//! query, binding and worker count the engines' hot medians and `target_ms`) is optional: without it the run has saved
//! answers only. Each engine's answer files hold the rows at `/run/result`; a missing file means that engine has no
//! answer for that cell, and only an engine with an answer at every compared cell is required
//! (`validation.required_engines`).

use super::data::DataSize;
use super::queries::FolderQuery;
use super::settings::{CompareWith, Goal, Mode, Settings, StartFrom, Storage};
use super::{FolderError, WorkloadFolder, write_text};
use crate::controller::benchmark_inputs::apply_benchmark_inputs;
use crate::controller::hardware::Hardware;
use crate::controller::limits::{Limits, Money, SpendPolicy, UNSET_COUNT, UNSET_SECONDS};
use crate::controller::request::{
    DataAllowance, EngineRequest, EngineScale, EngineStorageSeed, EngineWorkloads, MemberRole, PauseCadence, QueryObjective, QueryRequest, REQUEST_FORMAT, Seed, SeedVersion,
    WorkloadMember, WorkloadRequest, WorkloadStorageRequest,
};
use crate::providers::AuthorModel;
use crate::query::host_locks::HostLocks;
use crate::storage::policy::{EligibleStorage, StoredDataPolicy};
use gendb_artifacts::ContentId;
use gendb_verification::admission::bindings::CONCRETE_BINDING;
use gendb_verification::admission::{BenchmarkBinding, SavedAnswerSource, ValidationPolicy};
use serde::Deserialize;
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// The environment variable naming GenDB's machine folder (default `~/.gendb`).
pub const GENDB_HOME_ENV: &str = "GENDB_HOME";
/// The pointer to the rows in an answer file.
const ROWS_POINTER: &str = "/run/result";

/// The machine: the run's work folder, the host's lock files and the author executable.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RunContext {
    pub work: PathBuf,
    pub host_locks: HostLocks,
    pub author_executable: PathBuf,
}

/// `$GENDB_HOME/config.toml`.
#[derive(Default, Deserialize)]
#[serde(deny_unknown_fields)]
struct MachineConfig {
    #[serde(default)]
    author: Option<PathBuf>,
    #[serde(default)]
    locks: Option<MachineLocks>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct MachineLocks {
    activity: PathBuf,
    build: PathBuf,
    race: PathBuf,
}

impl RunContext {
    /// The machine of `$GENDB_HOME` (default `~/.gendb`): `config.toml` `author = PATH` (else `claude`, found on `PATH`)
    /// and `[locks] activity, build, race` (else `$GENDB_HOME/locks/{activity,build,race}.lock`). Every GenDB run on one
    /// machine should use the same three lock files; give their real paths, not symbolic links (the timing gate is a
    /// file named after the activity lock's path).
    pub fn from_environment(work: &Path) -> Result<RunContext, FolderError> {
        let home = match std::env::var_os(GENDB_HOME_ENV) {
            Some(home) => PathBuf::from(home),
            None => PathBuf::from(std::env::var_os("HOME").ok_or_else(|| FolderError::new("machine_invalid", format!("neither {GENDB_HOME_ENV} nor HOME is set")))?).join(".gendb"),
        };
        let file = home.join("config.toml");
        let config: MachineConfig = if file.is_file() {
            let text = std::fs::read_to_string(&file).map_err(|e| FolderError::new("machine_invalid", format!("{}: {e}", file.display())))?;
            toml::from_str(&text).map_err(|e| FolderError::new("machine_invalid", format!("{}: {e}", file.display())))?
        } else {
            MachineConfig::default()
        };
        let host_locks = match config.locks {
            Some(MachineLocks { activity, build, race }) => HostLocks { activity_lock: activity, build_lock: build, race_lock: race },
            None => {
                let dir = home.join("locks");
                HostLocks { activity_lock: dir.join("activity.lock"), build_lock: dir.join("build.lock"), race_lock: dir.join("race.lock") }
            }
        };
        let work = std::path::absolute(work).map_err(|e| FolderError::new("machine_invalid", format!("{}: {e}", work.display())))?;
        Ok(RunContext { work, host_locks, author_executable: config.author.unwrap_or_else(|| PathBuf::from("claude")) })
    }

    /// The folders of the primary workload (`member` `None`) or of one member.
    pub fn paths(&self, member: Option<&str>) -> WorkloadPaths {
        match member {
            None => WorkloadPaths { library: self.work.join("library"), inputs: self.work.join("inputs"), output_home: Some(self.work.join("output")) },
            Some(name) => {
                let root = self.work.join("members").join(name);
                WorkloadPaths { library: root.join("library"), inputs: root.join("inputs"), output_home: None }
            }
        }
    }

    /// `WORK/requests/<name>.json`.
    pub fn request_file(&self, name: &str) -> PathBuf {
        self.work.join("requests").join(format!("{name}.json"))
    }

    /// `WORK/requests/members/<name>.json`: the request of member `name`.
    pub fn member_request_file(&self, name: &str) -> PathBuf {
        self.work.join("requests/members").join(format!("{name}.json"))
    }
}

/// Where one workload of a run keeps its library, input files and output.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WorkloadPaths {
    pub library: PathBuf,
    pub inputs: PathBuf,
    /// `WORK/output` for the primary; a member has none.
    pub output_home: Option<PathBuf>,
}

impl WorkloadPaths {
    pub fn templates(&self) -> PathBuf {
        self.inputs.join("templates.json")
    }

    pub fn bindings(&self, scale: &str) -> PathBuf {
        self.inputs.join(format!("bindings-{scale}.json"))
    }

    pub fn data_size(&self, scale: &str) -> PathBuf {
        self.inputs.join(format!("data-size-{scale}.json"))
    }

    /// The empty variants manifest of a folder without `variants/manifest.json`.
    pub fn empty_variants(&self) -> PathBuf {
        self.inputs.join("variants.json")
    }
}

/// What the run's steps recorded for one scale.
#[derive(Clone, Debug)]
pub struct ScaleInputs {
    pub name: String,
    /// Every table's source files (`WorkloadFolder::locations`).
    pub locations: BTreeMap<String, Vec<PathBuf>>,
    /// The prepared capture; `None` before the preparation step (the preparation request).
    pub capture: Option<PathBuf>,
    pub data_size: DataSize,
    /// The saved baselines; `None` with `compare_with = "none"` and before the baselines step.
    pub baselines: Option<Baselines>,
}

/// A baselines folder (module documentation), read.
#[derive(Clone, Debug, PartialEq)]
pub struct Baselines {
    /// `baselines.json`.
    pub file: PathBuf,
    /// The targets file and its content, when the baselines are timed.
    pub targets: Option<(PathBuf, Value)>,
    pub engines: Vec<BaselineEngine>,
}

/// One engine of a baselines folder.
#[derive(Clone, Debug, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BaselineEngine {
    /// The short name (`duckdb`) saved answers and `required_engines` use.
    pub name: String,
    /// The engine's version and settings.
    pub description: String,
    /// The answer file of a cell, with `{query}` and `{binding}` (a bindings-file id), relative to `baselines.json`
    /// until read.
    pub answers: String,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct BaselinesFile {
    #[serde(default)]
    targets: Option<PathBuf>,
    engines: Vec<BaselineEngine>,
}

impl Baselines {
    /// The baselines file `baselines.json` (or a folder holding it).
    pub fn read(path: &Path) -> Result<Baselines, FolderError> {
        let file = if path.is_dir() { path.join("baselines.json") } else { path.to_path_buf() };
        let invalid = |what: String| FolderError::new("baselines_invalid", format!("{}: {what}", file.display()));
        let text = std::fs::read_to_string(&file).map_err(|e| invalid(e.to_string()))?;
        let parsed: BaselinesFile = serde_json::from_str(&text).map_err(|e| invalid(e.to_string()))?;
        let base = file.parent().unwrap_or(Path::new("/")).to_path_buf();
        let targets = match parsed.targets {
            Some(targets) => {
                let targets = base.join(targets);
                let text = std::fs::read_to_string(&targets).map_err(|e| invalid(format!("{}: {e}", targets.display())))?;
                Some((targets.clone(), serde_json::from_str(&text).map_err(|e| invalid(format!("{}: {e}", targets.display())))?))
            }
            None => None,
        };
        if parsed.engines.is_empty() {
            return Err(invalid("engines lists at least one engine".into()));
        }
        let engines = parsed.engines.into_iter().map(|e| BaselineEngine { answers: base.join(&e.answers).display().to_string(), ..e }).collect();
        Ok(Baselines { file, targets, engines })
    }

    /// The answer file of `engine` for `query` at bindings-file binding `binding`.
    pub fn answer_file(&self, engine: &BaselineEngine, query: &str, binding: &str) -> PathBuf {
        PathBuf::from(engine.answers.replace("{query}", query).replace("{binding}", binding))
    }
}

/// The eligible flat storages a `gendb prepare-flat-storage` run recorded (`flat-storage.json`: `tables[].package`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlatStorages {
    pub record: PathBuf,
    pub packages: Vec<ContentId>,
}

impl FlatStorages {
    pub fn read(record: &Path) -> Result<FlatStorages, FolderError> {
        let invalid = |what: String| FolderError::new("flat_record_invalid", format!("{}: {what}", record.display()));
        let text = std::fs::read_to_string(record).map_err(|e| invalid(e.to_string()))?;
        let value: Value = serde_json::from_str(&text).map_err(|e| invalid(e.to_string()))?;
        let tables = value["tables"].as_array().ok_or_else(|| invalid("no tables list".into()))?;
        let packages = tables.iter().map(|t| serde_json::from_value(t["package"].clone()).map_err(|e| invalid(format!("package: {e}")))).collect::<Result<Vec<ContentId>, _>>()?;
        Ok(FlatStorages { record: record.to_path_buf(), packages })
    }

    /// The `physical_only` policy admitting exactly these storages.
    fn policy(&self) -> StoredDataPolicy {
        let review = format!("generated flat storage: every column once (gendb prepare-flat-storage, record {})", self.record.display());
        StoredDataPolicy::PhysicalOnly { eligible_storages: self.packages.iter().map(|&package| EligibleStorage { package, review: review.clone() }).collect() }
    }
}

/// A session's limits: `max_iterations` submissions and a provider-cost stop at `max_cost_usd` (`None`: unset).
fn session_limits(max_iterations: u32, max_cost_usd: Option<&str>) -> Result<Limits, FolderError> {
    let max_cost_usd = match max_cost_usd {
        Some(text) => Money::parse(text).map_err(|e| FolderError::new("settings_invalid", format!("dollars {text:?}: {e}")))?,
        None => Money::UNSET,
    };
    Ok(Limits { max_iterations, max_cost_usd, spend_policy: SpendPolicy::EstimatedUsd, max_retries_per_iteration: UNSET_COUNT, max_author_tool_turns: 0, author_timeout_seconds: UNSET_SECONDS })
}

/// The `model` setting.
fn author_model(settings: &Settings) -> Result<AuthorModel, FolderError> {
    match &settings.model {
        None => Ok(AuthorModel::default()),
        Some(id) => serde_json::from_value(json!(id)).map_err(|_| FolderError::new("settings_invalid", format!("model {id:?}: a supported model id (claude-opus-5-5, claude-sonnet-5-5)"))),
    }
}

/// The fields every request of the folder has: the dataset at `locations`, no queries, the worker counts, scheduling,
/// the machine, `library` and the declared constraints.
fn base_request(folder: &WorkloadFolder, ctx: &RunContext, locations: &BTreeMap<String, Vec<PathBuf>>, library: &Path) -> Result<WorkloadRequest, FolderError> {
    let settings = &folder.settings;
    let preparations = settings.parallel_preparations();
    Ok(WorkloadRequest {
        format_version: REQUEST_FORMAT,
        dataset: folder.schema.dataset(locations),
        queries: vec![],
        hardware: Hardware { threads: settings.threads() },
        max_concurrent_queries: 1,
        max_concurrent_preparations: (preparations != 1).then_some(preparations),
        author_executable: ctx.author_executable.clone(),
        author_model: author_model(settings)?,
        library: library.to_path_buf(),
        host_locks: ctx.host_locks.clone(),
        prepared_workload: None,
        data_allowance: None,
        output_home: None,
        workload_storage: None,
        part_access: None,
        storage_policy: StoredDataPolicy::Unrestricted,
        integrity_constraints: folder.schema.constraints.clone(),
        validation: ValidationPolicy::FormalProofs { numeric_relative_tolerance: settings.numeric_tolerance(), required_engines: vec![], saved_answers: vec![] },
        engine: None,
    })
}

/// One query session per query file, without an objective.
fn query_requests(folder: &WorkloadFolder) -> Result<Vec<QueryRequest>, FolderError> {
    let settings = &folder.settings;
    let budget = settings.session_budget_usd.as_ref().map(|d| d.text());
    let limits = session_limits(settings.max_submissions(), budget.as_deref())?;
    Ok(folder
        .queries
        .iter()
        .map(|q| QueryRequest {
            name: Some(q.name.clone()),
            sql: q.sql.clone(),
            limits: limits.clone(),
            parameters: q.parameters.clone(),
            test_bindings: vec![],
            arguments: vec![],
            objective: QueryObjective::Correctness,
            preflight_from: None,
            reselect_from: None,
            continue_from: None,
        })
        .collect())
}

/// The visible bindings `visible` lists for `query`: `(binding_id, arguments)`.
fn listed_bindings(visible: &Value, query: &str) -> Vec<(String, Vec<String>)> {
    visible["queries"][query]
        .as_array()
        .into_iter()
        .flatten()
        .map(|b| (b["binding_id"].as_str().unwrap_or_default().to_string(), b["arguments"].as_array().into_iter().flatten().filter_map(|a| a.as_str().map(str::to_string)).collect()))
        .collect()
}

/// The saved answers of `baselines` at `cells` (`(query, request binding name, bindings-file binding id)`) whose files
/// exist, and the engines with an answer at every cell. An engine without any answer file is refused (a wrong path
/// pattern would otherwise silently compare nothing).
fn saved_answers(baselines: &Baselines, cells: &[(String, String, String)]) -> Result<(Vec<SavedAnswerSource>, Vec<String>), FolderError> {
    let (mut answers, mut complete) = (vec![], vec![]);
    let mut found: BTreeMap<&str, usize> = BTreeMap::new();
    for (query, binding, id) in cells {
        for engine in &baselines.engines {
            let path = baselines.answer_file(engine, query, id);
            if path.is_file() {
                *found.entry(&engine.name).or_default() += 1;
                answers.push(SavedAnswerSource { query: query.clone(), binding: binding.clone(), engine: engine.name.clone(), description: engine.description.clone(), path, rows_pointer: ROWS_POINTER.into() });
            }
        }
    }
    for engine in &baselines.engines {
        match found.get(engine.name.as_str()).copied().unwrap_or(0) {
            0 if !cells.is_empty() => {
                return Err(FolderError::new("baselines_invalid", format!("{}: engine {} has no answer file ({})", baselines.file.display(), engine.name, engine.answers)));
            }
            n if n == cells.len() => complete.push(engine.name.clone()),
            _ => {}
        }
    }
    Ok((answers, complete))
}

/// The templates-mode request at `scale` (module documentation). Without `scale.capture` and `scale.baselines` it is
/// the preparation request.
pub fn templates_request(folder: &WorkloadFolder, ctx: &RunContext, scale: &ScaleInputs) -> Result<WorkloadRequest, FolderError> {
    let settings = &folder.settings;
    if settings.mode() != Mode::Templates {
        return Err(FolderError::new("settings_invalid", "templates_request is for mode = \"templates\""));
    }
    let paths = ctx.paths(None);
    let mut request = base_request(folder, ctx, &scale.locations, &paths.library)?;
    request.queries = query_requests(folder)?;
    request.max_concurrent_queries = settings.parallel_queries();
    request.prepared_workload = settings.capture.clone().or_else(|| scale.capture.clone());
    request.output_home = paths.output_home.clone();
    match settings.storage() {
        Storage::Designed => {
            request.storage_policy = StoredDataPolicy::PhysicalOnly { eligible_storages: vec![] };
            request.data_allowance = Some(DataAllowance { live_bytes: scale.data_size.original_data_bytes });
            request.workload_storage = Some(WorkloadStorageRequest { limits: session_limits(settings.max_submissions(), None)?, stop_before_queries: false });
        }
        Storage::Plain => request.storage_policy = StoredDataPolicy::FixedFlat {},
    }
    let visible = folder.visible_bindings(&scale.name)?;
    let names: Vec<String> = folder.queries.iter().map(|q| q.name.clone()).collect();
    let mut cells = vec![];
    match settings.goal() {
        Goal::Fast => {
            if let Some(missing) = folder.queries.iter().find(|q| q.is_template() && listed_bindings(&visible, &q.name).is_empty()) {
                return Err(FolderError::new(
                    "bindings_missing",
                    format!("{}: goal \"fast\" measures a template at its bindings: list them in bindings.json, or set goal = \"correct\"", missing.name),
                ));
            }
            match scale.baselines.as_ref().and_then(|b| b.targets.as_ref()) {
                Some((file, targets)) => apply_benchmark_inputs(&mut request, &names, &visible, targets, &file.display().to_string(), settings.speedup()).map_err(|e| FolderError::new("baselines_invalid", e))?,
                None => {
                    for (query, folder_query) in request.queries.iter_mut().zip(&folder.queries) {
                        let bindings = if folder_query.is_template() {
                            listed_bindings(&visible, &folder_query.name).into_iter().map(|(name, arguments)| BenchmarkBinding { name, arguments }).collect()
                        } else {
                            vec![]
                        };
                        query.objective = QueryObjective::ExecutionTime { bindings, targets: vec![], early_stop: None };
                    }
                }
            }
            for q in &folder.queries {
                for (id, _) in listed_bindings(&visible, &q.name) {
                    let binding = if q.is_template() { id.clone() } else { CONCRETE_BINDING.to_string() };
                    cells.push((q.name.clone(), binding, id));
                }
            }
        }
        Goal::Correct => {
            for (query, folder_query) in request.queries.iter_mut().zip(&folder.queries) {
                let listed = listed_bindings(&visible, &folder_query.name);
                if folder_query.is_template() {
                    query.test_bindings = listed.iter().map(|(_, arguments)| arguments.clone()).collect();
                }
                // The first admission binding is the one run on the full data: the first test binding (`request_0`), or a
                // concrete statement's one binding.
                if let Some((id, _)) = listed.first() {
                    let binding = if folder_query.is_template() { "request_0".to_string() } else { CONCRETE_BINDING.to_string() };
                    cells.push((folder_query.name.clone(), binding, id.clone()));
                }
            }
        }
    }
    if let Some(baselines) = &scale.baselines {
        let (answers, complete) = saved_answers(baselines, &cells)?;
        let every_query_compared = folder.queries.iter().all(|q| cells.iter().any(|(name, _, _)| *name == q.name));
        request.validation = ValidationPolicy::FormalProofs {
            numeric_relative_tolerance: settings.numeric_tolerance(),
            required_engines: if every_query_compared { complete } else { vec![] },
            saved_answers: answers,
        };
    }
    Ok(request)
}

/// The `gendb prepare-flat-storage` request of engine mode at `scale`: the dataset at that scale, one query per query
/// file (no objective), `fixed_flat`, into `library`; without an output home or capture.
pub fn flat_preparation_request(folder: &WorkloadFolder, ctx: &RunContext, scale: &ScaleInputs, library: &Path) -> Result<WorkloadRequest, FolderError> {
    let mut request = base_request(folder, ctx, &scale.locations, library)?;
    request.queries = query_requests(folder)?;
    request.storage_policy = StoredDataPolicy::FixedFlat {};
    if let Some(baselines) = &scale.baselines {
        let (_, complete) = saved_answers(baselines, &engine_cells(folder, &folder.visible_bindings(&scale.name)?))?;
        request.validation = ValidationPolicy::FormalProofs { numeric_relative_tolerance: folder.settings.numeric_tolerance(), required_engines: complete, saved_answers: vec![] };
    }
    Ok(request)
}

/// Engine mode's compared cells at one scale: every query at every visible binding, named by its binding id.
fn engine_cells(folder: &WorkloadFolder, visible: &Value) -> Vec<(String, String, String)> {
    folder.queries.iter().flat_map(|q| listed_bindings(visible, &q.name).into_iter().map(move |(id, _)| (q.name.clone(), id.clone(), id))).collect()
}

/// A seed named by a `start_from` setting.
fn seed(start: StartFrom) -> Seed {
    match start {
        StartFrom::Version { run, version } => Seed::Run { version: SeedVersion { run, version }, workload: None },
        StartFrom::Folder(source) => Seed::Source { source },
    }
}

/// The `engine.workloads.members[]` entry of a `[[members]]` folder named `name` (its request at
/// [`RunContext::member_request_file`]).
pub fn member_entry(ctx: &RunContext, name: &str, role: MemberRole, start_from: Option<&str>) -> WorkloadMember {
    WorkloadMember { name: name.to_string(), role, request: ctx.member_request_file(name), seed: start_from.map(|s| seed(StartFrom::parse(s))) }
}

/// The engine-mode request (a general-line request) over `scales` (the ladder, each with its capture), its library
/// seeded with `flat`. `member`: the member's name when this is a `[[members]]` folder's request (its own library, no
/// output home); `members`: the primary's members ([`member_entry`]).
pub fn engine_request(folder: &WorkloadFolder, ctx: &RunContext, scales: &[ScaleInputs], flat: &FlatStorages, member: Option<&str>, members: Vec<WorkloadMember>) -> Result<WorkloadRequest, FolderError> {
    let settings = &folder.settings;
    if settings.mode() != Mode::Engine {
        return Err(FolderError::new("settings_invalid", "engine_request is for mode = \"engine\""));
    }
    let first = scales.first().ok_or_else(|| FolderError::new("scale_invalid", "engine mode needs at least one scale"))?;
    if folder.schema.constraints.is_none() {
        return Err(FolderError::new("schema_keys_missing", "engine mode: the engine assumes the declared keys; declare them in schema.sql"));
    }
    if settings.compare_with() == CompareWith::None {
        return Err(FolderError::new("settings_invalid", "engine mode compares every answer with the baselines' saved answers: compare_with = \"none\" is for templates mode"));
    }
    let budget = settings.budget_usd.as_ref().map(|d| d.text()).ok_or_else(|| FolderError::new("settings_invalid", "engine mode needs budget_usd: the budget of every engine-agent call together"))?;
    let paths = ctx.paths(member);
    let mut request = base_request(folder, ctx, &first.locations, &paths.library)?;
    request.storage_policy = flat.policy();
    request.output_home = paths.output_home.clone();
    let mut engine_scales = vec![];
    let mut required: Option<Vec<String>> = None;
    for scale in scales {
        let visible = folder.visible_bindings(&scale.name)?;
        if let Some(missing) = folder.queries.iter().find(|q| !listed_bindings(&visible, &q.name).iter().any(|(id, _)| *id == settings.timing_binding())) {
            return Err(FolderError::new("bindings_missing", format!("{} at {}: engine mode times every query at the binding {} (timing_binding): list it in the bindings", missing.name, scale.name, settings.timing_binding())));
        }
        let baselines = scale.baselines.as_ref().ok_or_else(|| FolderError::new("baselines_missing", format!("{}: engine mode compares every answer with the baselines: the baselines step comes first", scale.name)))?;
        let (answers, complete) = saved_answers(baselines, &engine_cells(folder, &visible))?;
        required = Some(match required {
            None => complete,
            Some(earlier) => earlier.into_iter().filter(|e| complete.contains(e)).collect(),
        });
        engine_scales.push(EngineScale {
            name: scale.name.clone(),
            locations: scale.locations.clone(),
            prepared_workload: scale.capture.clone().ok_or_else(|| FolderError::new("capture_missing", format!("{}: the flat preparation step writes the capture first", scale.name)))?,
            bindings: paths.bindings(&scale.name),
            targets: scale.baselines.as_ref().and_then(|b| b.targets.as_ref()).map(|(file, _)| file.clone()).unwrap_or_default(),
            saved_answers: answers,
            original_data_bytes: scale.data_size.original_data_bytes,
            original_data_record: paths.data_size(&scale.name),
        });
    }
    request.validation = ValidationPolicy::FormalProofs { numeric_relative_tolerance: settings.numeric_tolerance(), required_engines: required.unwrap_or_default(), saved_answers: vec![] };
    let start = settings.start();
    let needs_workloads = !members.is_empty() || settings.one_engine() || matches!(start, Some(StartFrom::Folder(_)));
    let (seed_version, workloads) = match (member, needs_workloads, start) {
        (Some(_), _, _) => (None, None),
        (None, true, start) => (None, Some(EngineWorkloads { name: settings.name_or(&folder.root), seed: start.map(seed), members, require_one_engine: settings.one_engine() })),
        (None, false, Some(StartFrom::Version { run, version })) => (Some(SeedVersion { run, version }), None),
        (None, false, _) => (None, None),
    };
    request.engine = Some(EngineRequest {
        line: Some("general".into()),
        templates: paths.templates(),
        bindings: None,
        timing_binding: settings.timing_binding(),
        targets: None,
        variants: folder.variants_manifest().unwrap_or_else(|| paths.empty_variants()),
        storage_seed: EngineStorageSeed { source_library: paths.library.clone(), packages: flat.packages.clone() },
        reuse_libraries: settings.reuse.clone().unwrap_or_default(),
        pause_after_round: false,
        limits: Limits { max_iterations: UNSET_COUNT, ..session_limits(1, Some(&budget))? },
        scales: engine_scales,
        branches: Some(settings.branches()),
        pause_after_session: PauseCadence::Never,
        call_limit_seconds: Some(settings.call_limit_seconds()),
        anon_memory_limit_bytes: Some(settings.memory_limit_bytes()?),
        timed_calls: settings.timed_calls,
        emphasis: settings.emphasis,
        stage: None,
        seed_version,
        workloads,
    });
    Ok(request)
}

/// The training set's `templates.json` (each query's SQL file and parameters) as GenDB writes it under `inputs/`.
fn templates_index(queries: &[FolderQuery]) -> Value {
    let templates: serde_json::Map<String, Value> =
        queries.iter().map(|q| (q.name.clone(), json!({"sql": format!("queries/{}.sql", q.name), "parameters": q.parameters}))).collect();
    json!({"format": "gendb.workload-folder.templates.v1", "templates": templates})
}

/// Write the input files of one workload of a run (module documentation) under `paths.inputs`: the statements
/// (`queries/<name>.sql`, the query files without their header lines) and `templates.json`, per scale its bindings and
/// data size, and an empty variants manifest when the folder has none.
pub fn write_inputs(folder: &WorkloadFolder, paths: &WorkloadPaths, scales: &[ScaleInputs]) -> Result<(), FolderError> {
    for query in &folder.queries {
        write_text(&paths.inputs.join("queries").join(format!("{}.sql", query.name)), &query.sql)?;
    }
    let pretty = |value: &Value| serde_json::to_string_pretty(value).map(|t| t + "\n").map_err(|e| FolderError::new("folder_invalid", e.to_string()));
    write_text(&paths.templates(), &pretty(&templates_index(&folder.queries))?)?;
    for scale in scales {
        write_text(&paths.bindings(&scale.name), &pretty(&folder.visible_bindings(&scale.name)?)?)?;
        write_text(&paths.data_size(&scale.name), &pretty(&json!(scale.data_size))?)?;
    }
    if folder.variants_manifest().is_none() {
        write_text(&paths.empty_variants(), &pretty(&json!({"variants": []}))?)?;
    }
    Ok(())
}

/// `request` with every query served at each of its visible bindings (`queries[].arguments`; a concrete statement at its
/// one binding): the `gendb serve` request of a run.
pub fn serve_request(mut request: WorkloadRequest, visible: &Value) -> WorkloadRequest {
    for query in &mut request.queries {
        let name = query.name.clone().unwrap_or_default();
        if query.is_template() {
            query.arguments = listed_bindings(visible, &name).into_iter().map(|(_, arguments)| arguments).collect();
        }
    }
    request
}
