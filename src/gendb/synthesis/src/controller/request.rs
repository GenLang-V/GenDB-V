//! The user's workload request (`request.json`, format 2): the dataset, the statements, the user's iteration and money
//! controls per query and (optionally) for the workload storage author, the worker counts, and where the run's
//! executables, library, prepared data and host locks are.
//! The same request drives synthesis (`gendb synthesize`) and serving without synthesis (`gendb serve`); fields that
//! only one route uses are named as such (`part_access`: serving only).
//!
//! Format 1 was the `integrated-synthesis` request of the earlier GenDB version. Its verified-mode fields keep their JSON names here; the fields
//! of the native path, the shared data-design stage, baseline engines and prior-run context are not part of format 2,
//! and a format 1 request is refused with the list of what differs (only the earlier GenDB version runs it).
//!
//! `author_model` selects the model of every author session of the run (`providers::AuthorModel`): absent means Opus 5.5,
//! the default; the request keeps its JSON identity then.
//!
//! `storage_policy` selects which prepared data admitted storages may hold (`storage::policy`): absent means
//! `unrestricted` (the historical behaviour); `physical_only` keeps the physical organization of each table's own
//! rows and excludes materialized query computation and cross-table row locators. The user's exclusions of storage
//! packages under `physical_only` are library records (`storage::exclusion`), honored by every request over the
//! library without a request field. `fixed_flat` reads only the fixed flat storages GenDB prepares once
//! (`storage::flat`, `gendb prepare-flat-storage`); such a request takes no `workload_storage` and no `data_allowance`.
//!
//! A query may name a closed query session of an earlier run (`reselect_from`) to recover one of its evaluated
//! candidates without an author (`controller::reselect`), or (`continue_from`) to start its author session from the
//! package that session admitted, as the incumbent its submissions must beat (`controller::run`, incumbent).
//!
//! `integrity_constraints` declares PRIMARY KEY / UNIQUE / FOREIGN KEY / CHECK constraints the user asserts about the
//! full source tables (`admission::integrity_constraints`): `{"trust": "user_declared", "declarations": [{"table",
//! "sql"}]}`, each `sql` one clause after `ALTER TABLE <table> ADD`. A CHECK must be named (`CONSTRAINT <name> CHECK
//! (...)`) and stay in the raise-free, collation-independent subset; keys precede the foreign keys that reference them;
//! the order is part of the identity (the `ALTER TABLE` lines of `benchmarks/tpc-h/schema.sql` are the TPC-H list).
//! They are the user's assumption, never checked against the data: query crates then use the entry v5 (`bound_db`
//! assumes them on the whole database), a storage may opt in (`uses_declared_constraints`, storage entry v2) and then
//! applies only to runs with exactly this list, existing unconstrained storages still compose, only tiny cases the
//! verified evaluator certifies are run, and a package that assumes them is served only to requests declaring exactly
//! them. Absent means none declared, and the request keeps its JSON identity. [`WorkloadRequest::validate`] applies the
//! structural refusals before any preparation, author call or serving; the translation's refusals (unsupported clause,
//! CHECK outside the subset) follow at statement preparation.
//!
//! Each query selects its objective ([`QueryObjective`]): correctness (default: the first exact verified candidate is
//! admitted and the session stops) or verified execution time (every submission is measured until the user's guards
//! and the fastest exact verified candidate is admitted), optionally with user-supplied runtime targets and an early
//! stop once one exact verified candidate beats every target by the user's factor (`EarlyStop`). Execution time is
//! measured at benchmark bindings × configured worker counts: a concrete statement's one binding, or the user's named
//! benchmark bindings of a template (`objective.bindings`), which are samples, never the proof domain.
//!
//! `engine` selects the engine target instead ([`EngineRequest`], `crate::engine`): one
//! verified engine for every well-typed query on the dataset's schema, built against a training set of templates. Such
//! a request has no `queries[]` and no `workload_storage`, uses the `physical_only` storage policy, declares its
//! integrity constraints, and validates with `formal_proofs` (the saved answers name templates). It runs with `gendb
//! engine synthesize`. Two lines share the section ([`EngineLine`]):
//! - absent `line`: the schema engine: rounds of one session each, one scale, a `data_allowance`,
//!   the training set's `bindings` and `targets` and the top-level `prepared_workload` and saved answers;
//! - `line: "general"`: the general engine started from
//!   version 0 (the verified interpreter over the flat storage), optimized by up to three branches in long sessions,
//!   timed under a per-call limit and a memory limit, climbing the scale ladder `scales` in list order. Everything that
//!   depends on the scale is in its scale ([`EngineScale`]: source locations, capture, bindings, baselines, saved
//!   answers and the original data size, the budget of a version with a storage change), so the
//!   top level names none of it. An optional `emphasis` ([`EngineEmphasis`]) makes one direction
//!   the prompt's main one from the first version; absent, the prompt has no main-direction section. A relaunch of a
//!   general-line run may raise its budget `limits.max_cost_usd`, never lower it (`lifecycle::record_request`).
//!
//! A general-line request may be a **stage run** ([`EngineStage`], `engine.stage`):
//! the same engine made fast on a goal workload (the request's own dataset, templates and scales) while it keeps serving
//! other workloads, each a complete general-line request of its own (`kept_workloads[].request`, read with
//! [`WorkloadRequest::kept_workloads`]), from an accepted version of another general-line run (`seed_version`). Absent,
//! the request serializes as before; present, it is part of the run's identity.
//!
//! A general-line request of one workload may be a **continued run** (`engine.seed_version`: the
//! engine evolves over time): its root is an accepted version of another general-line run instead of version 0, and it
//! starts at the last scale of its ladder ([`EngineRequest::start_scale`]); its training set may add templates to the
//! seed run's. Absent, the request serializes as before; present, it is part of the run's identity.
//!
//! A general-line request may name **several workloads** of one engine (`engine.workloads`, [`EngineWorkloads`]):
//! the request itself is the primary workload (named by
//! `engine.workloads.name`, always counted), and every member is a complete general-line request file of its own with a
//! role ([`MemberRole`]: `counted` decides through the summed score, `check` is verified and its answers checked on
//! every submission without timing, `kept` is verified and timed, never deciding). A member names a seed of its own
//! side of the root ([`Seed`]: an accepted version of another run, `{run, version, workload?}`, or an exported engine
//! folder, `{source}`); the primary's seed is also the code of the first workspace. The field excludes `engine.stage` and
//! `engine.seed_version`; absent, the request serializes as before; present, it is part of the run's identity. A check
//! member's scales may omit `targets` (it is never timed). [`WorkloadRequest::workload_set`] reads every form (one
//! workload, `engine.stage`, `engine.workloads`) as one [`WorkloadSet`]. `engine.workloads.require_one_engine`
//! ([`EngineWorkloads::require_one_engine`]) accepts only versions that are one engine; a relaunch may set it.

use super::hardware::Hardware;
use super::limits::{Limits, UNSET_COUNT};
use super::records;
use crate::prompts::{EarlyStop, RuntimeTarget};
use crate::providers::AuthorModel;
use crate::query::host_locks::HostLocks;
use crate::storage::policy::StoredDataPolicy;
use gendb_frontend::params::{BindingRequest, ParamRequest};
use gendb_verification::admission::{BenchmarkBinding, IntegrityConstraints, ValidationPolicy};
use gendb_verification::admission::bindings::CONCRETE_BINDING;
use gendb_verification::admission::validation::SavedAnswerSource;
use gendb_verification::verus::engine_rules::EngineLine;
use gendb_storage::import::DatasetSpec;
use gendb_storage::io::PartAccess;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::{Path, PathBuf};

/// `format_version` of this request.
pub const REQUEST_FORMAT: u32 = 2;

/// Fields of a format 1 request that format 2 does not have, and what replaced each.
const V7_ONLY_FIELDS: [(&str, &str); 13] = [
    ("authoring", "the verified (Verus) path is the only path; the field is gone"),
    ("worker", "the worker is the gendb executable itself (`gendb worker`)"),
    ("synthesis", "the command selects the route: `gendb synthesize` or `gendb serve`"),
    ("shared_design_limits", "the native shared data-design stage is not part of the verified path"),
    ("data_design_policy", "native shared data-design stage"),
    ("retain_prior_shared_design", "native shared data-design stage"),
    ("resources", "only a live stored-bytes allowance applies to admitted storage assets: `data_allowance.live_bytes`"),
    ("module_resources", "native modular path"),
    ("allow_whole_query", "native path"),
    ("native_validation", "native compiler validation policy"),
    ("baselines", "DuckDB/Umbra baseline engines are not run by the active path (earlier version only); select queries[].objective {\"kind\":\"execution_time\"}, optionally with user-supplied targets"),
    ("prior_run_context", "prior-run context is not supported by this controller (earlier version only)"),
    ("supplemental_native_evidence", "native timing history (earlier version only)"),
];

/// One workload request.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WorkloadRequest {
    /// [`REQUEST_FORMAT`].
    pub format_version: u32,
    /// Declared source tables (relative locations resolve against the request file).
    pub dataset: DatasetSpec,
    pub queries: Vec<QueryRequest>,
    pub hardware: Hardware,
    /// Query author sessions running at the same time (synthesis), started in request order (`controller::schedule`).
    /// A scheduling control only, it never changes a result, so a resumed run may give another value
    /// (`lifecycle::record_request`): its open sessions resume this many at a time, the others waiting with their
    /// records unchanged.
    pub max_concurrent_queries: usize,
    /// Statement preparations running at the same time before any author call (synthesis): each is one statement's
    /// preflight (Verus statement check, evaluator builds, tiny cases) and its prepared-data references. Absent: one at
    /// a time. A scheduling control only, it never changes a result, so a resumed run may give another value
    /// (`lifecycle::record_request`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_concurrent_preparations: Option<usize>,
    /// The Claude Code executable of the authors (synthesis). A bare name resolves through `PATH`.
    pub author_executable: PathBuf,
    /// The model of every author session of this run, workload storage and query authors alike (synthesis): a
    /// supported model id (`AuthorModel`), launched at the transport's fixed effort. Absent: Opus 5.5.
    #[serde(default, skip_serializing_if = "AuthorModel::is_default")]
    pub author_model: AuthorModel,
    /// The object store of admitted packages (created on first use by synthesis; must exist for serving).
    pub library: PathBuf,
    /// Host lock files that keep timed measurements free of concurrent builds and author tools.
    #[serde(rename = "barriers")]
    pub host_locks: HostLocks,
    /// A prepared root to reuse or extend instead of importing the demanded columns again (required for serving).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub prepared_workload: Option<PathBuf>,
    /// The user's storage budget (synthesis): `live_bytes` bounds all serving storage together (`storage::budget`);
    /// absent: no budget.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub data_allowance: Option<DataAllowance>,
    /// The readable output home (`output`): after the workload storage session and after each query
    /// session closes, GenDB writes its folders there (`output::write_workload`, `output::write_query`; a query's
    /// folder is its `name`, else `qNN` by request position). Absent: no output home is written.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub output_home: Option<PathBuf>,
    /// The workload storage phase (synthesis): one storage author session, run before the query sessions, designs
    /// and proves storages shared by the workload. Absent: no workload phase; query authors choose admitted storages
    /// or create their own.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub workload_storage: Option<WorkloadStorageRequest>,
    /// Kernel advice for mapping stored parts while serving (serving): `{"read_advice": "normal"|"random",
    /// "drop_cached_pages": bool}`. Absent: normal readahead and no page drop. Advice only (no global cache flush, no
    /// proof of a cold cache); every served cell records the setting it ran with.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub part_access: Option<PartAccess>,
    /// Which prepared data admitted storages may hold (synthesis and serving): `{"kind": "unrestricted"}` (absent) or
    /// `{"kind": "physical_only", "eligible_storages": [{"package", "review"}]}` (`storage::policy`); the library's
    /// recorded exclusions apply under `physical_only` in addition (`storage::exclusion`).
    #[serde(default, skip_serializing_if = "StoredDataPolicy::is_unrestricted")]
    pub storage_policy: StoredDataPolicy,
    /// The user's declared integrity constraints (synthesis, preflight and serving): `{"trust": "user_declared",
    /// "declarations": [{"table", "sql"}]}`, each `sql` one table-constraint clause of `ALTER TABLE <table> ADD`, in
    /// order (keys before the foreign keys that reference them). They are assumptions about the full source tables,
    /// never checked against the data. The `ALTER TABLE` lines of `benchmarks/tpc-h/schema.sql` are the TPC-H list.
    /// Absent: none declared.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub integrity_constraints: Option<IntegrityConstraints>,
    /// The validation policy (synthesis): which checks besides the Verus proof of every submitted crate establish a
    /// candidate (`admission::validation`). `{"kind": "formal_proofs", "numeric_relative_tolerance", "saved_answers"}`:
    /// no tiny cases, evaluator builds or reference engine; benchmark-binding results compared with saved answers of
    /// other engines. Absent: `tests_and_references` (the historical behaviour), and the request keeps its JSON
    /// identity. A resumed run may move once from the default to `formal_proofs` (`lifecycle::record_request`).
    #[serde(default, skip_serializing_if = "ValidationPolicy::is_default")]
    pub validation: ValidationPolicy,
    /// The schema-engine target ([`EngineRequest`]); absent: a workload run, and the request keeps its JSON identity.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub engine: Option<EngineRequest>,
}

/// The engine section of a request: the training set, its
/// bindings and the saved baselines the engine's totals are compared with, the frozen variants, the storages the engine
/// library was seeded with, and the user's controls. Relative paths resolve against the request file. Everything else
/// an engine run reads is a top-level field: `dataset`, `hardware.threads` (the worker counts of every matrix),
/// `library` (the seeded engine library), `storage_policy` (`physical_only`), `integrity_constraints` and `validation`
/// (`formal_proofs`); for the schema line also `prepared_workload` (the capture the seeded storages were built over),
/// `data_allowance` and the saved answers per template and visible binding, which the general line gives per scale.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EngineRequest {
    /// Which engine line (`gendb_verification::verus::engine_rules::EngineLine::of_request`): absent is the schema
    /// engine (and the request keeps its JSON identity), `"general"` the general line; any other value is refused.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub line: Option<String>,
    /// `templates.json` of the training set (`fixtures/tpch/templates/templates.json`): each template's SQL file
    /// (relative to that file) and its parameters.
    pub templates: PathBuf,
    /// The visible bindings (`output/tpch-sf100/bindings/visible.json`): per template, its named argument lists
    /// (`queries.<template>[] {binding_id, arguments}`). Schema line only (required there); the general line gives
    /// them per scale.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub bindings: Option<PathBuf>,
    /// The binding of the official matrix and the totals (`v0`). The other visible bindings are timed for a version
    /// whose official totals meet the stop (reported, never a stop condition).
    pub timing_binding: String,
    /// The saved DuckDB/Umbra baselines (`output/tpch-sf100/baselines/targets.json`): per template, binding and worker
    /// count, both engines' hot medians and their answer agreement. Never rerun. Schema line only (required there);
    /// the general line gives them per scale.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub targets: Option<PathBuf>,
    /// The frozen meaning-preserving variants (`fixtures/tpch/engine-variants/manifest.json`).
    pub variants: PathBuf,
    /// The storages the engine library (`library`) was seeded with.
    pub storage_seed: EngineStorageSeed,
    /// Read-only libraries whose admitted author code (query programs with their general modules, and storage code) the
    /// engine author may reuse: indexed into the author's search index and copied
    /// under `admitted-code/` like the engine library's own, filtered by the run's storage policy. They are only read:
    /// never written, never counted in the engine library's storage budget and never served.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub reuse_libraries: Vec<PathBuf>,
    /// Stop after every round for review: the round finishes (submission, admission,
    /// official timing, version records), the run summary records the pause (`status` `paused`, reason
    /// `paused_for_review`) and the controller exits; relaunching the same command resumes at the next round. A review
    /// cadence, not a cap: it bounds neither rounds nor cost, and it is not part of the run's identity
    /// (`lifecycle::record_request`), so a relaunch may switch it. Schema line only.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub pause_after_round: bool,
    /// The user's controls, read for the whole run. Schema line: `max_iterations` guards the number of rounds (one
    /// round is one fresh author session ending with one submission), `max_cost_usd` the provider-reported cost of all
    /// rounds together, `max_retries_per_iteration` the calls of one round after its first, `author_timeout_seconds`
    /// one call. General line: `max_cost_usd` is the budget of every engine-agent call of every branch together
    /// (required; the run stops only on it or on the user), so `max_iterations` is `unset`;
    /// `max_retries_per_iteration` and `author_timeout_seconds` apply to each call as before.
    pub limits: Limits,
    /// General line: the scale ladder, climbed in list order.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub scales: Vec<EngineScale>,
    /// General line: the number of branches searching at once (1 to [`MAX_BRANCHES`]). Branch
    /// `b1` starts first; the others start once `b1` has one evaluated submission. One branch is one
    /// line of versions, each built on the best version so far: the prompt and the facts then say
    /// nothing of branches, directions of other branches, merges or rebases. A scheduling control: not part of the
    /// run's identity, so a relaunch may change it (`lifecycle::record_request`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub branches: Option<u32>,
    /// General line: the review cadence ([`PauseCadence`]). A scheduling control like
    /// `pause_after_round`: not part of the run's identity, so a relaunch may switch it.
    #[serde(default, skip_serializing_if = "PauseCadence::is_never")]
    pub pause_after_session: PauseCadence,
    /// General line: the time limit of one engine call in seconds (60 in the general-engine runs). A cell is finished only
    /// when every one of its calls ends within it; it is enforced in the worker child.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub call_limit_seconds: Option<u64>,
    /// General line: the framework safety limit of one worker child's anonymous resident memory in bytes
    /// (144 GiB in the general-engine runs, the memory of the saved Umbra baseline), the same for every version and scale.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub anon_memory_limit_bytes: Option<u64>,
    /// General line: the prompt's main direction from the first version ([`EngineEmphasis`]).
    /// Absent: the general prompt has no main-direction section, and the request keeps its JSON identity. Part of the run's
    /// identity: a relaunch keeps it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub emphasis: Option<EngineEmphasis>,
    /// General line: a stage run ([`EngineStage`]): this request's workload is the goal, and the engine keeps serving
    /// the kept workloads. Absent: a run of one workload, and the request keeps its JSON identity. Part of the run's
    /// identity.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stage: Option<EngineStage>,
    /// General line, one workload: a **continued run** (continual evolution): the run's root `v000`
    /// is this accepted version of another general-line run instead of version 0: its code and its storage uses (which
    /// this run's `library` must hold admitted), frozen under this run's rules, verified whole, timed alone and admitted
    /// (`engine::branches::RootSource::seeded`). The run starts at the last scale of its ladder, where the seed was built;
    /// its first scale checks the variants. The training set may grow beyond the seed run's: the prompt names the
    /// seed's templates and the new ones. Absent: version 0, and the request keeps its JSON identity. Part of the run's
    /// identity. A stage run names its seed in `engine.stage` instead.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub seed_version: Option<SeedVersion>,
    /// General line: the workloads of one engine ([`EngineWorkloads`]): this request is the primary
    /// workload and every member a general-line request of its own with its role and its side's seed. Absent: a run of
    /// one workload (or a stage run), and the request keeps its JSON identity. Part of the run's identity. Excludes
    /// `stage` and `seed_version`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub workloads: Option<EngineWorkloads>,
}

/// The workloads of one general-line engine (`engine.workloads`): the request's own workload is
/// the primary (`name`, always counted; its `seed` is its side of the root and the code of the first workspace), every
/// member a complete general-line request file of its own (its dataset, constraints, templates, variants, scales, storage
/// seed and library, distinct from every other workload's; its `limits` and `emphasis` unused, no `output_home`) with its
/// role and, optionally, the seed of its side. The fields every workload shares must be equal, as in a stage run:
/// `hardware.threads`, `barriers`, `author_executable` and `engine.{call_limit_seconds, anon_memory_limit_bytes,
/// branches}`. There is no guard per workload: the summed score decides.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EngineWorkloads {
    /// The primary workload's name ([`EngineStage::NAME_RULE`], not [`RESERVED_WORKLOAD_NAME`]): its module directory
    /// `workloads/<name>/`, its plans `plans/<name>/` and its key in records.
    pub name: String,
    /// The primary seed: the primary's side of the root and the code of the first workspace. Absent: the primary's side
    /// is version 0.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub seed: Option<Seed>,
    /// The other workloads, in order (possibly none: a run of the primary alone, for example a new schema seeded from an
    /// exported engine).
    pub members: Vec<WorkloadMember>,
    /// Only a version that is one engine can be accepted (`version.json` `general.one_engine`: every workload served by
    /// the default module over storage families or plain flat storages, no workload module of its own, no inherited
    /// workload-specific storage). A submission that is not one engine is refused before any build or timing
    /// (`not_one_engine`); while the head is not one engine, the first one-engine submission is accepted when it is
    /// correct, even with a worse combined score (`one_engine_transition`), and from then on the combined score decides
    /// as before (`engine::stage::one_engine`). Absent (false): the combined score alone decides, and the request keeps
    /// its JSON identity. Part of the run's identity, except that a relaunch may set it, never unset it
    /// (`lifecycle::record_request`).
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub require_one_engine: bool,
}

/// One member of `engine.workloads`: its name, role, general-line request file (relative paths resolve against the run
/// request file) and the seed of its side of the root.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WorkloadMember {
    pub name: String,
    pub role: MemberRole,
    pub request: PathBuf,
    /// The seed of its side of the root. Absent: the primary seed's code out of the box on this workload, else version
    /// 0 over its plain storage (the stage root's rule).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub seed: Option<Seed>,
}

/// What one workload of a run decides.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MemberRole {
    /// In the acceptance and the score: the run's score is the sum of every counted workload's (the primary always is).
    Counted,
    /// Verified, every template answered and checked against the saved answers on every submission (gating), never
    /// timed in the score, no storage budget rule; `targets` optional.
    Check,
    /// Verified and timed against the parent's side for every accepted version, shown, never deciding (the stage run's
    /// kept workload).
    Kept,
}

impl MemberRole {
    /// The role's name in requests and records.
    pub fn name(self) -> &'static str {
        match self {
            MemberRole::Counted => "counted",
            MemberRole::Check => "check",
            MemberRole::Kept => "kept",
        }
    }
}

/// The workload name a member may not take: the shared default workload module's directory `workloads/default/`
/// (`engine::submission::DEFAULT_WORKLOAD`).
pub const RESERVED_WORKLOAD_NAME: &str = "default";

/// The seed of one side of a run's root: an accepted version of another general-line run, or an engine
/// folder written by `gendb engine export`. JSON: `{"run", "version", "workload"?}` or `{"source"}`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "SeedFields", into = "SeedFields")]
pub enum Seed {
    /// `<run>/engine/versions/<version>`; `workload` picks the module and storage uses of one workload of a version of
    /// several workloads (required there, refused for a version of one workload).
    Run { version: SeedVersion, workload: Option<String> },
    /// An exported engine folder (`gendb engine export`): its shared engine, default module, families and plans.
    Source { source: PathBuf },
}

/// The JSON form of a [`Seed`].
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct SeedFields {
    #[serde(default, skip_serializing_if = "Option::is_none")]
    run: Option<PathBuf>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    version: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    workload: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    source: Option<PathBuf>,
}

impl TryFrom<SeedFields> for Seed {
    type Error = String;

    fn try_from(fields: SeedFields) -> Result<Self, String> {
        match fields {
            SeedFields { run: Some(run), version: Some(version), workload, source: None } => Ok(Seed::Run { version: SeedVersion { run, version }, workload }),
            SeedFields { run: None, version: None, workload: None, source: Some(source) } => Ok(Seed::Source { source }),
            _ => Err("a seed is {\"run\", \"version\", \"workload\"?} (an accepted version of another general-line run) or {\"source\"} (an exported engine folder)".into()),
        }
    }
}

impl From<Seed> for SeedFields {
    fn from(seed: Seed) -> Self {
        match seed {
            Seed::Run { version, workload } => SeedFields { run: Some(version.run), version: Some(version.version), workload, source: None },
            Seed::Source { source } => SeedFields { run: None, version: None, workload: None, source: Some(source) },
        }
    }
}

impl Seed {
    /// The seed's own rules (no file is read): a version id of letters and digits and a workload name of the name rule,
    /// or a source folder named.
    fn validate(&self, field: &str) -> Result<(), String> {
        match self {
            Seed::Run { version, workload } => {
                version.validate(field)?;
                match workload {
                    Some(name) if !workload_name_is_portable(name) => Err(format!("{field}.workload {name:?}: {}", EngineStage::NAME_RULE)),
                    _ => Ok(()),
                }
            }
            Seed::Source { source } if source.as_os_str().is_empty() => Err(format!("{field}.source names an exported engine folder")),
            Seed::Source { .. } => Ok(()),
        }
    }

    /// Make the seed's paths absolute with `absolute`.
    fn resolve(&mut self, absolute: &impl Fn(&mut PathBuf)) {
        match self {
            Seed::Run { version, .. } => absolute(&mut version.run),
            Seed::Source { source } => absolute(source),
        }
    }
}

/// Whether `name` follows [`EngineStage::NAME_RULE`].
fn workload_name_is_portable(name: &str) -> bool {
    (1..=64).contains(&name.len()) && name.bytes().all(|b| b.is_ascii_lowercase() || b.is_ascii_digit() || b == b'_')
}

impl EngineWorkloads {
    /// Every workload's name, the primary first.
    pub fn names(&self) -> Vec<&str> {
        std::iter::once(self.name.as_str()).chain(self.members.iter().map(|m| m.name.as_str())).collect()
    }

    /// The section's own rules (no file is read): names that follow [`EngineStage::NAME_RULE`], all unique and none
    /// [`RESERVED_WORKLOAD_NAME`]; every seed's rules; a member request named.
    fn validate(&self) -> Result<(), String> {
        let mut names = BTreeSet::new();
        for name in self.names() {
            if !workload_name_is_portable(name) {
                return Err(format!("engine.workloads: {name:?}: {}", EngineStage::NAME_RULE));
            }
            if name == RESERVED_WORKLOAD_NAME {
                return Err(format!("engine.workloads: the workload name {name:?} is the shared default module's directory workloads/{name}/; choose another name"));
            }
            if !names.insert(name) {
                return Err(format!("engine.workloads: the workload name {name:?} is given twice (the primary's and every member's names are unique)"));
            }
        }
        if let Some(seed) = &self.seed {
            seed.validate("engine.workloads.seed")?;
        }
        for member in &self.members {
            if member.request.as_os_str().is_empty() {
                return Err(format!("engine.workloads.members[{}].request names the workload's general-line request file", member.name));
            }
            if let Some(seed) = &member.seed {
                seed.validate(&format!("engine.workloads.members[{}].seed", member.name))?;
            }
        }
        Ok(())
    }
}

/// Which request form a [`WorkloadSet`] was read from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum WorkloadForm {
    /// A run of one workload (neither `engine.stage` nor `engine.workloads`; possibly a continued run).
    One,
    /// `engine.stage`.
    Stage,
    /// `engine.workloads`.
    Workloads,
}

/// The name of the one member of a run of one workload ([`WorkloadForm::One`]). Such a run's crates and records name no
/// workload, so the name appears in no record of it.
pub const ONE_WORKLOAD_NAME: &str = "main";

/// The workloads of one general-line run, whichever form the request names them in
/// (`engine.stage` = the goal counted and every kept workload kept; `engine.seed_version` = one member with a seed;
/// neither = one member, version 0; `engine.workloads` as given).
#[derive(Clone, Debug)]
pub struct WorkloadSet {
    pub form: WorkloadForm,
    /// The primary seed: the code of the first workspace, and the out-of-the-box candidate of every member without a seed
    /// of its own (`None`: version 0).
    pub seed: Option<Seed>,
    /// Every member, the primary (the run's own request) first.
    pub members: Vec<SetMember>,
}

/// One member of a [`WorkloadSet`].
#[derive(Clone, Debug)]
pub struct SetMember {
    pub name: String,
    pub role: MemberRole,
    /// Its request file (absolute); `None` for the primary, which is the run's own request.
    pub path: Option<PathBuf>,
    pub request: WorkloadRequest,
    /// The seed of its side of the root; `None`: the primary seed's code out of the box, else version 0.
    pub seed: Option<Seed>,
}

impl WorkloadSet {
    /// The member `name`.
    pub fn member(&self, name: &str) -> Option<&SetMember> {
        self.members.iter().find(|m| m.name == name)
    }

    /// Every member's name, the primary first.
    pub fn names(&self) -> Vec<String> {
        self.members.iter().map(|m| m.name.clone()).collect()
    }
}

/// A stage run of the general line: one engine for several workloads, one crate
/// per workload (`gendb_verification::obligations::engine_crate_files_with` with `FlatAccess::Uniform`), its root the
/// accepted version `seed_version` of another general-line run. The goal workload is the request itself (its dataset,
/// constraints, templates, variants, scales, library and limits); its score decides every submission. Each kept
/// workload is a complete general-line request file of its own ([`WorkloadRequest::kept_workloads`]): its dataset,
/// constraints, templates, variants, scales, storage seed and library (distinct from every other workload's); it runs at
/// its last scale (its first scale checks variants); its `limits` and `emphasis` are not used (the run's are the goal
/// request's) and it has no `output_home`. The fields every workload shares must be equal: `hardware.threads`,
/// `barriers`, `author_executable` and `engine.{call_limit_seconds, anon_memory_limit_bytes, branches}`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EngineStage {
    /// The goal workload's name ([`EngineStage::NAME_RULE`]): its module directory `workloads/<name>/` and its key in
    /// records.
    pub workload: String,
    /// The accepted version the run starts from.
    pub seed_version: SeedVersion,
    /// The workloads the engine keeps serving (verified, checked and timed for every accepted version; never deciding).
    pub kept_workloads: Vec<KeptWorkload>,
}

/// An accepted version of another general-line run: `<run>/engine/versions/<version>` (its `node.json` accepted, its
/// `code/agent/**` and `manifest.json`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SeedVersion {
    /// The run directory (relative paths resolve against the request file).
    pub run: PathBuf,
    /// The version's id (`v016`).
    pub version: String,
}

impl SeedVersion {
    /// The version's folder, `<run>/engine/versions/<version>`.
    pub fn directory(&self) -> PathBuf {
        self.run.join("engine").join("versions").join(&self.version)
    }

    /// The version id's rule (no file is read): letters and digits only, so the folder stays under the run's versions.
    fn validate(&self, field: &str) -> Result<(), String> {
        let version = &self.version;
        if version.is_empty() || !version.bytes().all(|b| b.is_ascii_alphanumeric()) {
            return Err(format!("{field}.version {version:?} names an accepted version of the seed run (`v016`)"));
        }
        Ok(())
    }
}

/// One kept workload of a stage run: its name ([`EngineStage::NAME_RULE`]) and its general-line request file (relative
/// paths resolve against the stage request file).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct KeptWorkload {
    pub name: String,
    pub request: PathBuf,
}

/// One kept workload of a stage run, read and checked ([`WorkloadRequest::kept_workloads`]).
#[derive(Clone, Debug)]
pub struct KeptWorkloadRequest {
    pub name: String,
    /// Its request file (absolute).
    pub path: PathBuf,
    pub request: WorkloadRequest,
}

impl EngineStage {
    /// What a workload name is: lowercase ASCII letters, digits and `_`, 1 to 64 of them.
    pub const NAME_RULE: &'static str = "a workload name is 1 to 64 lowercase ASCII letters, digits and `_`";

    /// Every workload's name, the goal first.
    pub fn workload_names(&self) -> Vec<&str> {
        std::iter::once(self.workload.as_str()).chain(self.kept_workloads.iter().map(|k| k.name.as_str())).collect()
    }

    /// The seed version's folder, `<run>/engine/versions/<version>`.
    pub fn seed_version_directory(&self) -> PathBuf {
        self.seed_version.directory()
    }

    /// The section's own rules (no file is read): names that follow [`EngineStage::NAME_RULE`], all unique; a version id
    /// of letters and digits; a kept request named.
    fn validate(&self) -> Result<(), String> {
        let mut names = BTreeSet::new();
        for name in self.workload_names() {
            if !workload_name_is_portable(name) {
                return Err(format!("engine.stage: {name:?}: {}", Self::NAME_RULE));
            }
            if !names.insert(name) {
                return Err(format!("engine.stage: the workload name {name:?} is given twice (the goal's and every kept workload's names are unique)"));
            }
        }
        self.seed_version.validate("engine.stage.seed_version")?;
        if let Some(kept) = self.kept_workloads.iter().find(|k| k.request.as_os_str().is_empty()) {
            return Err(format!("engine.stage.kept_workloads[{}].request names the workload's general-line request file", kept.name));
        }
        Ok(())
    }
}

/// The main direction a general-line run's prompt sets from the first version (for example a run with
/// data and query co-optimization from day 0, compared with a run's query-level path). The goal, the rules, the
/// storage policy, the budget rule and the loop stay the same; the prompt adds one section that says where to put the
/// work (`prompts::engine_general_sections::emphasis_section`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum EngineEmphasis {
    /// `co_optimization`: the storage layout, the access layer for encoded columns and the operators designed together,
    /// with storage changes within the budget rule from the start.
    CoOptimization,
}

impl EngineEmphasis {
    /// The value's name in the request and in a session's prompt context (`general.emphasis`).
    pub fn name(self) -> &'static str {
        match self {
            EngineEmphasis::CoOptimization => "co_optimization",
        }
    }
}

/// The most branches of a general-line run (up to three).
pub const MAX_BRANCHES: u32 = 3;

/// When a general-line run pauses for review. A pause lets every running session finish, starts no
/// new one, writes the run summary (`status` `paused`) and exits; relaunching the same command resumes from the
/// records. A review cadence, never a cap.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PauseCadence {
    /// No pause (absent).
    #[default]
    Never,
    /// After the first session of each branch.
    FirstSessionOfEachBranch,
    /// After every session.
    EverySession,
}

impl PauseCadence {
    pub fn is_never(&self) -> bool {
        *self == PauseCadence::Never
    }
}

/// One scale of the general line's ladder: everything that differs between scales. The
/// schema (the dataset's tables and fields), the templates, the timing binding and the variants are the same at every
/// scale.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EngineScale {
    /// The scale's name (`sf1`): ASCII letters, digits, `_` and `-`, unique in the ladder.
    pub name: String,
    /// The source files of every dataset table at this scale (`table -> locations`; every table, no other).
    pub locations: BTreeMap<String, Vec<PathBuf>>,
    /// The capture of this scale (the prepared root its flat storage assets were published from).
    pub prepared_workload: PathBuf,
    /// The visible bindings at this scale (`queries.<template>[] {binding_id, arguments}`; only parameters the
    /// benchmark ties to the scale differ).
    pub bindings: PathBuf,
    /// The saved DuckDB/Umbra baselines at this scale (`targets.json`; measured once per scale, never rerun). Required,
    /// except in the request of a check member of `engine.workloads` (never timed), where it may be absent (empty, and
    /// not serialized then).
    #[serde(default, skip_serializing_if = "path_is_empty")]
    pub targets: PathBuf,
    /// The saved answers of other engines at this scale (each names a training template and a visible binding).
    pub saved_answers: Vec<SavedAnswerSource>,
    /// The original data size at this scale in bytes (the raw generator text, the same definition as the template runs'
    /// `data_allowance.live_bytes`): the storage budget of a version with any storage change at this scale; a version
    /// reading only the plain storage is allowed as is (`engine::role::GeneralInputs::budget_rule`).
    pub original_data_bytes: u64,
    /// The record that states `original_data_bytes` (the data generation record).
    pub original_data_record: PathBuf,
}

impl EngineRequest {
    /// The request's engine line (an unknown `engine.line` is refused by name).
    pub fn engine_line(&self) -> Result<EngineLine, String> {
        EngineLine::of_request(self.line.as_deref())
    }

    /// Whether this is a general-line request (the general line's engine rules apply: no whole-statement evaluator
    /// rule, plus the schema-name scan; version 0 is the verified interpreter over the flat storage).
    pub fn is_general(&self) -> bool {
        self.engine_line() == Ok(EngineLine::General)
    }

    /// Whether only a version that is one engine can be accepted ([`EngineWorkloads::require_one_engine`]).
    pub fn requires_one_engine(&self) -> bool {
        self.workloads.as_ref().is_some_and(|w| w.require_one_engine)
    }

    /// The scale named `name` and its position in the ladder.
    pub fn scale(&self, name: &str) -> Option<(usize, &EngineScale)> {
        self.scales.iter().enumerate().find(|(_, s)| s.name == name)
    }

    /// The general line's rules (module and field documentation), on the engine section and the top-level fields. With
    /// `targets_optional` (the request of a check member) a scale may omit `targets`.
    fn validate_general(&self, request: &WorkloadRequest, targets_optional: bool) -> Result<(), String> {
        if self.bindings.is_some() || self.targets.is_some() {
            return Err("a general-line request gives bindings and targets per scale (engine.scales[]), not in the engine section".into());
        }
        if self.pause_after_round {
            return Err("a general-line request pauses with engine.pause_after_session, not pause_after_round".into());
        }
        if request.prepared_workload.is_some() || request.data_allowance.is_some() {
            return Err("a general-line request gives the capture and the original data size per scale (engine.scales[].prepared_workload, original_data_bytes) and no data_allowance (its storage budget is each scale's original data size, for a version with a storage change), not at the top level".into());
        }
        if matches!(&request.validation, ValidationPolicy::FormalProofs { saved_answers, .. } if !saved_answers.is_empty()) {
            return Err("a general-line request gives the saved answers per scale (engine.scales[].saved_answers); validation.saved_answers is empty".into());
        }
        match self.branches {
            Some(branches) if (1..=MAX_BRANCHES).contains(&branches) => {}
            other => return Err(format!("engine.branches is 1 to {MAX_BRANCHES} for the general line, not {other:?}")),
        }
        if !self.call_limit_seconds.is_some_and(|s| s > 0) {
            return Err("engine.call_limit_seconds (the time limit of one engine call, 60) is required and positive for the general line".into());
        }
        if !self.anon_memory_limit_bytes.is_some_and(|b| b > 0) {
            return Err("engine.anon_memory_limit_bytes (the worker child's memory limit, 144 GiB) is required and positive for the general line".into());
        }
        if self.limits.max_cost_usd.is_unset() {
            return Err("engine.limits.max_cost_usd is the general line's budget (all branches' calls together) and is required".into());
        }
        if self.limits.max_iterations != UNSET_COUNT {
            return Err("engine.limits.max_iterations is unset for the general line: the run stops only on the budget or the user".into());
        }
        if self.scales.is_empty() {
            return Err("engine.scales lists the scale ladder of the general line (at least one scale)".into());
        }
        let tables: BTreeSet<&str> = request.dataset.tables.iter().map(|t| t.name.as_str()).collect();
        let mut names = BTreeSet::new();
        for scale in &self.scales {
            let at = format!("engine.scales[{}]", scale.name);
            if scale.name.is_empty() || !scale.name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-') || !names.insert(scale.name.as_str()) {
                return Err(format!("{at}: a scale name is a unique name of ASCII letters, digits, `_` and `-`"));
            }
            if scale.locations.keys().map(String::as_str).collect::<BTreeSet<_>>() != tables {
                return Err(format!("{at}.locations names every dataset table and no other ({tables:?})"));
            }
            if scale.locations.values().any(Vec::is_empty) {
                return Err(format!("{at}.locations: every table has at least one source file"));
            }
            if scale.original_data_bytes == 0 {
                return Err(format!("{at}.original_data_bytes (the raw data size, the budget for changed storage) must be positive"));
            }
            if !targets_optional && path_is_empty(&scale.targets) {
                return Err(format!("{at}.targets names the saved baselines of the scale (only a check member's request may omit them)"));
            }
            let mut seen = BTreeSet::new();
            if let Some(twice) = scale.saved_answers.iter().find(|a| !seen.insert((&a.query, &a.binding, &a.engine))) {
                return Err(format!("{at}.saved_answers: ({}, {}, {}) is given twice", twice.query, twice.binding, twice.engine));
            }
        }
        let first = &self.scales[0];
        if let Some(table) = request.dataset.tables.iter().find(|t| first.locations.get(&t.name) != Some(&t.locations)) {
            return Err(format!("dataset.tables[{}].locations are the first scale's ({}) locations", table.name, first.name));
        }
        if let Some(stage) = &self.stage {
            stage.validate()?;
        }
        if let Some(seed) = &self.seed_version {
            if self.stage.is_some() {
                return Err("engine.seed_version continues a run of one workload; a stage run names its seed in engine.stage.seed_version".into());
            }
            seed.validate("engine.seed_version")?;
        }
        if let Some(workloads) = &self.workloads {
            if self.stage.is_some() || self.seed_version.is_some() {
                return Err("engine.workloads names every workload and the seed of each side; it excludes engine.stage and engine.seed_version".into());
            }
            workloads.validate()?;
        }
        Ok(())
    }

    /// The scale a run of this request starts at (its ladder index): a continued run (`seed_version`) at the last scale,
    /// where its seed was built, and a run of several workloads (`workloads`; like a stage run it has no ladder: every
    /// workload stays at the last scale of its request); every other run at the first.
    pub fn start_scale(&self) -> usize {
        if self.seed_version.is_some() || self.workloads.is_some() { self.scales.len().saturating_sub(1) } else { 0 }
    }

    /// The schema line refuses every general-line field, so a general-line field never silently changes it.
    fn validate_schema_line(&self, request: &WorkloadRequest) -> Result<(), String> {
        let general = [
            ("scales", !self.scales.is_empty()),
            ("branches", self.branches.is_some()),
            ("pause_after_session", !self.pause_after_session.is_never()),
            ("call_limit_seconds", self.call_limit_seconds.is_some()),
            ("anon_memory_limit_bytes", self.anon_memory_limit_bytes.is_some()),
            ("emphasis", self.emphasis.is_some()),
            ("stage", self.stage.is_some()),
            ("seed_version", self.seed_version.is_some()),
            ("workloads", self.workloads.is_some()),
        ];
        if let Some((field, _)) = general.iter().find(|(_, present)| *present) {
            return Err(format!("engine.{field} is a general-line field (engine.line \"general\")"));
        }
        if self.bindings.is_none() || self.targets.is_none() {
            return Err("engine.bindings and engine.targets name the training set's visible bindings and saved baselines".into());
        }
        if request.data_allowance.is_none() {
            return Err("an engine run needs data_allowance.live_bytes: the storage budget its storages share".into());
        }
        if request.prepared_workload.is_none() {
            return Err("an engine run names prepared_workload: the capture its seeded storages' assets were built over".into());
        }
        Ok(())
    }
}

impl WorkloadRequest {
    /// The request one scale of a general-line run is prepared and timed with: the dataset with that scale's
    /// locations, its capture, and its saved answers under the request's validation policy. The engine section is kept;
    /// the per-scale fields are what every route of the scale reads.
    pub fn at_scale(&self, scale: &EngineScale) -> WorkloadRequest {
        let mut request = self.clone();
        for table in &mut request.dataset.tables {
            if let Some(locations) = scale.locations.get(&table.name) {
                table.locations = locations.clone();
            }
        }
        request.prepared_workload = Some(scale.prepared_workload.clone());
        if let ValidationPolicy::FormalProofs { saved_answers, .. } = &mut request.validation {
            *saved_answers = scale.saved_answers.clone();
        }
        request
    }
}

/// The storages an engine library starts from: seeded by hard links from another library,
/// without its query packages.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EngineStorageSeed {
    /// The library the storages were seeded from (recorded; the engine run reads only `library`).
    pub source_library: PathBuf,
    /// The seeded storage packages; each must be admitted in the request's `library` before the run starts.
    pub packages: Vec<gendb_artifacts::ContentId>,
}

impl EngineRequest {
    /// The engine section's own rules, and the top-level fields an engine run requires or excludes (both lines, then
    /// the line's own: [`EngineRequest::validate_general`], [`EngineRequest::validate_schema_line`]). `targets_optional`:
    /// the request of a check member, whose scales may omit `targets`.
    fn validate(&self, request: &WorkloadRequest, targets_optional: bool) -> Result<(), String> {
        if !request.queries.is_empty() {
            return Err("an engine run has no queries[]: its statements are the training templates (engine.templates)".into());
        }
        if request.workload_storage.is_some() {
            return Err("an engine run has no workload_storage phase: the engine library is seeded with admitted storages (engine.storage_seed)".into());
        }
        if request.storage_policy.kind() != crate::storage::policy::PHYSICAL_ONLY {
            return Err(format!("an engine run uses storage_policy physical_only (revision 2), not {}", request.storage_policy.kind()));
        }
        if request.integrity_constraints.is_none() {
            return Err("an engine run declares integrity_constraints: the engine entry states bound_db with them (engine_requires_declared_constraints)".into());
        }
        if !matches!(request.validation, ValidationPolicy::FormalProofs { .. }) {
            return Err("an engine run validates with formal_proofs: its cells are compared with the saved answers of the training templates".into());
        }
        match self.engine_line()? {
            EngineLine::General => self.validate_general(request, targets_optional)?,
            EngineLine::SchemaEngine => self.validate_schema_line(request)?,
        }
        if self.timing_binding.trim().is_empty() {
            return Err("engine.timing_binding names a visible binding (v0)".into());
        }
        if self.storage_seed.packages.is_empty() {
            return Err("engine.storage_seed.packages lists the seeded storage packages".into());
        }
        if self.reuse_libraries.contains(&request.library) {
            return Err("engine.reuse_libraries names other libraries, read only for reuse; the engine library is `library`".into());
        }
        self.limits.validate().map_err(|e| format!("engine.limits: {e}"))
    }
}

/// The user's controls of the workload storage author session.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WorkloadStorageRequest {
    pub limits: Limits,
    /// Run only the workload storage phase: once its session closes, the run's summary is published closed with every
    /// ready query `not_started`, and no query author is called. The admitted storages stay in the library for later
    /// requests. Absent or false: the query sessions follow as usual.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub stop_before_queries: bool,
}

impl WorkloadRequest {
    /// Whether this run stops after the workload storage phase (`workload_storage.stop_before_queries`).
    pub fn stops_before_queries(&self) -> bool {
        self.workload_storage.as_ref().is_some_and(|storage| storage.stop_before_queries)
    }
}

/// One statement of the workload.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct QueryRequest {
    /// A readable name of the statement (for TPC-H `q01`..`q22`): its folder in the output home
    /// (`output::write_query`) and its key in named binding files (`gendb evaluate`). Not part of any key.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    pub sql: String,
    /// The user's controls of this query's author session (synthesis).
    pub limits: Limits,
    /// Typed statement parameters `$n`, each fixed or free with an inclusive domain; absent: a concrete statement.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub parameters: Vec<ParamRequest>,
    /// Admission bindings of the free parameters (argument texts in slot order, each inside the declared domain); the
    /// framework adds the domain's minimum, maximum and interior bindings (synthesis).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub test_bindings: Vec<Vec<String>>,
    /// Argument bindings to serve (serving); absent: the one binding of a concrete statement.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub arguments: Vec<Vec<String>>,
    /// What the author session optimizes (synthesis); absent: correctness.
    #[serde(default, skip_serializing_if = "QueryObjective::is_correctness")]
    pub objective: QueryObjective,
    /// A completed preflight of the same statement to load instead of rerunning it (synthesis): the statement evidence
    /// directory `<run>/queries/query-NNNN/verus-preflight` of an earlier `gendb preflight` or `synthesize` run. It is
    /// used only when its evidence identity (statement, bindings, source versions, framework build, prover) is the
    /// current one; otherwise the query is refused before any author call (`admission::preflight::reuse`). Runtime
    /// targets and early stop may differ. Absent: a fresh preflight.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub preflight_from: Option<PathBuf>,
    /// A closed query session of an earlier synthesis run to recover a candidate from instead of calling an author
    /// (synthesis): `<run>/queries/query-NNNN`. The session selects the best of its eligible candidates that the
    /// storage policy and the library's exclusions still admit, evaluates a copy afresh, qualifies and serves it
    /// (`controller::reselect`); no author is invoked and no submission is counted. The source run's request must
    /// name the same statement, parameters, admission bindings, objective, worker counts, data allowance and storage
    /// policy kind, else the query is refused before its preflight (`reselect_source_invalid`). Absent: the author
    /// session.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reselect_from: Option<PathBuf>,
    /// A closed query session of an earlier synthesis run whose admitted (qualified) candidate this query's author
    /// session continues from (synthesis): `<run>/queries/query-NNNN`. Before the first author call the role writes
    /// that candidate's manifest and author files into the workspace (its storage uses pinned to the admitted packages
    /// it reads, which must be admitted in this run's library), it is frozen with the current framework and evaluated
    /// afresh as the session's incumbent (iteration 0). The incumbent competes in the search stop, selection and
    /// qualification like a submission but is never one: it stays selected, and is the package admitted into this
    /// run's library, unless a submission is exact, verified and has a lower score_ns. The source run's request must
    /// name the same SQL, parameters and admission bindings, with the same storage policy kind, and the source session
    /// the same statement key; otherwise the query is refused before its preflight (`continue_source_invalid`). Only
    /// with the execution_time objective; not with `reselect_from`. Absent: the author starts from an empty workspace.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub continue_from: Option<PathBuf>,
}

impl QueryRequest {
    /// Some parameter is free: the statement is a template.
    pub fn is_template(&self) -> bool {
        self.parameters.iter().any(|p| matches!(p.binding, BindingRequest::Free { .. }))
    }
}

/// The objective of one query's author session. JSON: `{"kind": "correctness"}` or
/// `{"kind": "execution_time", "bindings": [{"name", "arguments"}], "targets": [{"binding", "workers", "median_ns",
/// "provenance", "timing_scope", "system"}], "early_stop": {"min_speedup"}}` (`bindings` only for a template, where it
/// is required; `binding` of a target only for a template; a target's `system`, the measured system it names, optional;
/// `targets` and `early_stop` optional).
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum QueryObjective {
    /// The first exact verified candidate is qualified and the session stops. Timings are descriptive.
    #[default]
    Correctness,
    /// Every exact verified submission is measured (hot median per benchmark binding and worker count) until the
    /// user's submission or cost guard; the fastest (score over the whole matrix) is qualified, served and measured
    /// again at the same bindings and worker counts.
    ExecutionTime {
        /// The user's named benchmark bindings of a template (argument texts in slot order, inside the declared
        /// domain): where candidates are measured and scored. Required for a template, absent for a concrete
        /// statement (its one binding `statement`). Distinct from `test_bindings` and from the declared (proof) domain.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        bindings: Vec<BenchmarkBinding>,
        /// User-supplied search guidance with provenance, at most one per benchmark binding and configured worker
        /// count; empty: optimize the measured runtime without an external target. Never a same-window comparison.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        targets: Vec<RuntimeTarget>,
        /// The user's early stop (`EarlyStop`): the submission guard becomes a maximum once the selected exact verified
        /// candidate is `min_speedup` times faster than the target at every benchmark binding and configured worker
        /// count. Absent: every submission up to the guards is requested.
        #[serde(default, skip_serializing_if = "Option::is_none")]
        early_stop: Option<EarlyStop>,
    },
}

impl QueryObjective {
    pub fn is_correctness(&self) -> bool {
        *self == QueryObjective::Correctness
    }

    pub fn is_execution_time(&self) -> bool {
        matches!(self, QueryObjective::ExecutionTime { .. })
    }

    /// The user's runtime targets (empty for correctness).
    pub fn runtime_targets(&self) -> &[RuntimeTarget] {
        match self {
            QueryObjective::Correctness => &[],
            QueryObjective::ExecutionTime { targets, .. } => targets,
        }
    }

    /// The user's benchmark bindings (empty for correctness and for a concrete statement).
    pub fn benchmark_bindings(&self) -> &[BenchmarkBinding] {
        match self {
            QueryObjective::Correctness => &[],
            QueryObjective::ExecutionTime { bindings, .. } => bindings,
        }
    }

    /// The user's early stop (never set for correctness).
    pub fn early_stop(&self) -> Option<EarlyStop> {
        match self {
            QueryObjective::Correctness => None,
            QueryObjective::ExecutionTime { early_stop, .. } => *early_stop,
        }
    }

    /// An execution-time search needs a user guard to end (a submission or provider-cost guard). A template needs
    /// named benchmark bindings (one argument text per free parameter), a concrete statement none. Each target names a
    /// benchmark binding (a template's by name; a concrete statement's is implicit) and a configured worker count, at
    /// most once per cell, with a positive median, its provenance and its timing scope. An early stop needs a positive
    /// factor and a target at every benchmark binding × configured worker count. Argument values and domains are
    /// checked with the statement (`admission::prepare_statement`).
    fn validate(&self, query: &QueryRequest, hardware: &Hardware) -> Result<(), String> {
        let QueryObjective::ExecutionTime { bindings, targets, early_stop } = self else { return Ok(()) };
        let limits = &query.limits;
        if limits.max_iterations == UNSET_COUNT && limits.max_cost_usd.is_unset() {
            return Err("the execution_time objective measures every submission until the user's guards: set max_iterations or max_cost_usd".into());
        }
        let names: Vec<&str> = if query.is_template() {
            let free = query.parameters.iter().filter(|p| matches!(p.binding, BindingRequest::Free { .. })).count();
            if bindings.is_empty() {
                return Err("execution_time on a template needs objective.bindings: the user's named benchmark bindings (argument texts of the free parameters in slot order); they are measured, never the proof domain".into());
            }
            let mut names = BTreeSet::new();
            for binding in bindings {
                if let Some(refusal) = BenchmarkBinding::name_refusal(&binding.name) {
                    return Err(refusal);
                }
                if !names.insert(binding.name.as_str()) {
                    return Err(format!("benchmark binding name {} is repeated", binding.name));
                }
                if binding.arguments.len() != free {
                    return Err(format!("benchmark binding {} has {} arguments for {free} free parameters", binding.name, binding.arguments.len()));
                }
            }
            bindings.iter().map(|b| b.name.as_str()).collect()
        } else {
            if !bindings.is_empty() {
                return Err(format!("objective.bindings is for templates: a concrete statement has the one binding `{CONCRETE_BINDING}`"));
            }
            vec![CONCRETE_BINDING]
        };
        let mut cells = BTreeSet::new();
        for target in targets {
            let binding = match (&target.binding, query.is_template()) {
                (Some(name), _) if names.contains(&name.as_str()) => name.as_str(),
                (None, false) => CONCRETE_BINDING,
                (None, true) => return Err(format!("runtime target at {} workers must name its benchmark binding (one of {names:?})", target.workers)),
                (Some(name), _) => return Err(format!("runtime target binding {name:?} is not a benchmark binding {names:?}")),
            };
            if !hardware.threads.contains(&target.workers) || !cells.insert((binding, target.workers)) {
                return Err(format!("runtime target ({binding}, {} workers) must be a distinct cell of a configured worker count {:?}", target.workers, hardware.threads));
            }
            if target.median_ns == 0 || target.provenance.trim().is_empty() || target.timing_scope.trim().is_empty() {
                return Err(format!("runtime target ({binding}, {} workers) needs a positive median_ns, its provenance and its timing_scope", target.workers));
            }
            if target.system.as_ref().is_some_and(|system| system.trim().is_empty()) {
                return Err(format!("runtime target ({binding}, {} workers): system, when given, names the measured system", target.workers));
            }
        }
        if let Some(stop) = early_stop {
            if stop.min_speedup == 0 {
                return Err("early_stop.min_speedup must be at least 1".into());
            }
            let uncovered: Vec<(&str, usize)> =
                names.iter().flat_map(|&b| hardware.threads.iter().map(move |&w| (b, w))).filter(|cell| !cells.contains(cell)).collect();
            if !uncovered.is_empty() {
                return Err(format!("early_stop needs a runtime target at every benchmark binding and configured worker count; none at {uncovered:?}"));
            }
        }
        Ok(())
    }
}

/// The user's data allowance.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DataAllowance {
    /// The storage budget: the largest total serving bytes, in bytes, of all usable admitted storages together
    /// (`synthesis::storage::budget`; the original input is not counted).
    pub live_bytes: u64,
}

/// Why a request cannot be used.
#[derive(Debug)]
pub enum RequestError {
    /// The request file cannot be read or decoded.
    Record(records::RecordError),
    /// A format 1 request (the earlier GenDB version): the fields that differ, each with what replaced it.
    FormatOne { v7_fields: Vec<String> },
    /// Any other invalid field or combination.
    Invalid(String),
}

impl fmt::Display for RequestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RequestError::Record(error) => write!(f, "{error}"),
            RequestError::FormatOne { v7_fields } => write!(
                f,
                "format_version 1 is the integrated-synthesis request of the earlier GenDB version (not part of this repository); format {REQUEST_FORMAT} differs in: {}",
                v7_fields.join("; ")
            ),
            RequestError::Invalid(detail) => f.write_str(detail),
        }
    }
}

impl std::error::Error for RequestError {}

impl From<records::RecordError> for RequestError {
    fn from(error: records::RecordError) -> Self {
        RequestError::Record(error)
    }
}

impl WorkloadRequest {
    /// Read `path` and make every path in it absolute: relative dataset locations, library, prepared root and lock
    /// files resolve against the request's directory; the author executable does too unless it is a bare name
    /// (`PATH`). The parents of the lock files are created.
    pub fn read(path: &Path) -> Result<WorkloadRequest, RequestError> {
        let path = path.canonicalize().map_err(|e| records::RecordError::new(path, e))?;
        let value: Value = records::read_json(&path)?;
        if value["format_version"] != REQUEST_FORMAT {
            return Err(format_refusal(&value));
        }
        let mut request: WorkloadRequest =
            serde_json::from_value(value).map_err(|e| RequestError::Invalid(format!("{}: {e}", path.display())))?;
        let base = path.parent().unwrap_or(Path::new("/"));
        let absolute = |p: &mut PathBuf| {
            if p.is_relative() {
                *p = base.join(&*p);
            }
        };
        for table in &mut request.dataset.tables {
            table.locations.iter_mut().for_each(absolute);
        }
        absolute(&mut request.library);
        request.prepared_workload.iter_mut().for_each(absolute);
        for query in &mut request.queries {
            query.preflight_from.iter_mut().for_each(absolute);
            query.reselect_from.iter_mut().for_each(absolute);
            query.continue_from.iter_mut().for_each(absolute);
        }
        if let Some(engine) = &mut request.engine {
            for file in [&mut engine.templates, &mut engine.variants, &mut engine.storage_seed.source_library] {
                absolute(file);
            }
            engine.bindings.iter_mut().chain(engine.targets.iter_mut()).for_each(absolute);
            engine.reuse_libraries.iter_mut().for_each(absolute);
            for scale in &mut engine.scales {
                for file in [&mut scale.prepared_workload, &mut scale.bindings, &mut scale.original_data_record] {
                    absolute(file);
                }
                // Absent targets (a check member's request) stay absent.
                if !path_is_empty(&scale.targets) {
                    absolute(&mut scale.targets);
                }
                scale.locations.values_mut().flatten().for_each(absolute);
            }
            if let Some(stage) = &mut engine.stage {
                absolute(&mut stage.seed_version.run);
                stage.kept_workloads.iter_mut().for_each(|k| absolute(&mut k.request));
            }
            if let Some(seed) = &mut engine.seed_version {
                absolute(&mut seed.run);
            }
            if let Some(workloads) = &mut engine.workloads {
                workloads.seed.iter_mut().for_each(|s| s.resolve(&absolute));
                for member in &mut workloads.members {
                    absolute(&mut member.request);
                    member.seed.iter_mut().for_each(|s| s.resolve(&absolute));
                }
            }
        }
        if request.author_executable.components().count() > 1 {
            absolute(&mut request.author_executable);
        }
        let locks = &mut request.host_locks;
        for lock in [&mut locks.activity_lock, &mut locks.build_lock, &mut locks.race_lock] {
            absolute(lock);
            if let Some(parent) = lock.parent() {
                records::create_dir(parent)?;
            }
        }
        Ok(request)
    }

    /// Checks shared by both routes: format, statements present, worker counts, host locks, and each query's
    /// controls (their values matter only to synthesis, but an invalid control is refused either way).
    pub fn validate(&self) -> Result<(), RequestError> {
        self.validate_with(false)
    }

    /// [`WorkloadRequest::validate`] of the request of a member of `engine.workloads` with role `role`: a check member's
    /// scales may omit `targets`; every other rule is the same.
    pub fn validate_member(&self, role: MemberRole) -> Result<(), RequestError> {
        self.validate_with(role == MemberRole::Check)
    }

    /// [`WorkloadRequest::validate`], where `targets_optional` lets an engine request's scales omit `targets`.
    fn validate_with(&self, targets_optional: bool) -> Result<(), RequestError> {
        if self.format_version != REQUEST_FORMAT {
            return Err(RequestError::Invalid(format!("format_version {} (expected {REQUEST_FORMAT})", self.format_version)));
        }
        if self.max_concurrent_preparations == Some(0) {
            return Err(RequestError::Invalid("max_concurrent_preparations must be positive when given".into()));
        }
        if let Some(engine) = &self.engine {
            engine.validate(self, targets_optional).map_err(|e| RequestError::Invalid(format!("engine: {e}")))?;
        } else if self.queries.is_empty() {
            return Err(RequestError::Invalid("the request has no queries".into()));
        }
        self.hardware.validate().map_err(RequestError::Invalid)?;
        self.host_locks.validate().map_err(|e| RequestError::Invalid(format!("barriers: {e}")))?;
        for (index, query) in self.queries.iter().enumerate() {
            query.limits.validate().map_err(|e| RequestError::Invalid(format!("queries[{index}].limits: {e}")))?;
            query.objective.validate(query, &self.hardware).map_err(|e| RequestError::Invalid(format!("queries[{index}].objective: {e}")))?;
            if query.continue_from.is_some() && query.reselect_from.is_some() {
                return Err(RequestError::Invalid(format!("queries[{index}]: continue_from and reselect_from exclude each other (an author session continues; a reselection calls no author)")));
            }
            if query.continue_from.is_some() && !query.objective.is_execution_time() {
                return Err(RequestError::Invalid(format!("queries[{index}].continue_from: needs the execution_time objective (the incumbent and the submissions compete on score_ns)")));
            }
        }
        if let Some(storage) = &self.workload_storage {
            storage.limits.validate().map_err(|e| RequestError::Invalid(format!("workload_storage.limits: {e}")))?;
        }
        self.storage_policy.validate().map_err(|e| RequestError::Invalid(format!("storage_policy: {e}")))?;
        if self.storage_policy.is_fixed_flat() && (self.workload_storage.is_some() || self.data_allowance.is_some()) {
            return Err(RequestError::Invalid(
                "storage_policy fixed_flat: the storages are the fixed flat storages GenDB prepares (gendb prepare-flat-storage), so the request takes no workload_storage and no data_allowance".into(),
            ));
        }
        if self.data_allowance.as_ref().is_some_and(|allowance| allowance.live_bytes == 0) {
            return Err(RequestError::Invalid("data_allowance.live_bytes must be positive".into()));
        }
        if let Some(constraints) = &self.integrity_constraints {
            constraints.validate(&self.dataset).map_err(|e| RequestError::Invalid(format!("integrity_constraints: {e}")))?;
        }
        self.validation.validate().map_err(|e| RequestError::Invalid(format!("validation: {e}")))?;
        // An engine run's saved answers name training templates, checked against `engine.templates` when they are read.
        if let ValidationPolicy::FormalProofs { saved_answers, .. } = &self.validation
            && self.engine.is_none()
            && let Some(unknown) = saved_answers.iter().find(|a| !self.queries.iter().any(|q| q.name.as_deref() == Some(a.query.as_str())))
        {
            return Err(RequestError::Invalid(format!("validation.saved_answers: query {:?} is not the name of a request query", unknown.query)));
        }
        Ok(())
    }

    /// The request's SQL texts in order.
    pub fn statements(&self) -> Vec<&str> {
        self.queries.iter().map(|query| query.sql.as_str()).collect()
    }

    /// The engine section of an engine run; a workload run is refused by name.
    pub fn engine(&self) -> Result<&EngineRequest, RequestError> {
        self.engine.as_ref().ok_or_else(|| RequestError::Invalid("this request has no engine section: run it with gendb synthesize".into()))
    }

    /// The kept workloads of a stage run ([`EngineStage`]), each request file read ([`WorkloadRequest::read`]) and
    /// validated, in the stage's order; empty for a request without `engine.stage`. Refused by name: a kept request that
    /// is not a general-line request, is itself a stage run, has an output home, uses the library of another workload,
    /// or differs from this (the goal) request in a field every workload shares (`hardware.threads`, `barriers`,
    /// `author_executable`, `engine.call_limit_seconds`, `engine.anon_memory_limit_bytes`, `engine.branches`).
    pub fn kept_workloads(&self) -> Result<Vec<KeptWorkloadRequest>, RequestError> {
        let Some(stage) = self.engine.as_ref().and_then(|e| e.stage.as_ref()) else { return Ok(vec![]) };
        let mut libraries = vec![self.library.clone()];
        let mut kept = vec![];
        for workload in &stage.kept_workloads {
            let at = format!("engine.stage.kept_workloads[{}] ({})", workload.name, workload.request.display());
            let request = self.read_member_request(&at, &workload.request, MemberRole::Kept, RunForm::Stage, &mut libraries)?;
            kept.push(KeptWorkloadRequest { name: workload.name.clone(), path: workload.request.clone(), request });
        }
        Ok(kept)
    }

    /// Every workload of this general-line run as one [`WorkloadSet`], the primary first:
    /// - `engine.workloads`: the primary (this request, counted, its side's seed the primary seed) and every member,
    ///   its request read and checked as [`WorkloadRequest::kept_workloads`] checks a kept workload's (and, for a member
    ///   of `engine.workloads`, refused when it names `engine.workloads` or `engine.seed_version` itself);
    /// - `engine.stage`: the goal (counted, no seed of its own: the stage seed out of the box, else version 0) and every
    ///   kept workload (kept, its side the stage seed), the primary seed the stage seed;
    /// - neither: one member [`ONE_WORKLOAD_NAME`], counted, its side and the primary seed `engine.seed_version` (a
    ///   continued run) or none (version 0).
    ///
    /// Refused: a request without an engine section, and every refusal of a member's request.
    pub fn workload_set(&self) -> Result<WorkloadSet, RequestError> {
        let engine = self.engine()?;
        let primary = |name: &str, seed: Option<Seed>| SetMember { name: name.to_string(), role: MemberRole::Counted, path: None, request: self.clone(), seed };
        if let Some(workloads) = &engine.workloads {
            let mut libraries = vec![self.library.clone()];
            let mut members = vec![primary(&workloads.name, workloads.seed.clone())];
            for member in &workloads.members {
                let at = format!("engine.workloads.members[{}] ({})", member.name, member.request.display());
                let request = self.read_member_request(&at, &member.request, member.role, RunForm::Workloads, &mut libraries)?;
                members.push(SetMember { name: member.name.clone(), role: member.role, path: Some(member.request.clone()), request, seed: member.seed.clone() });
            }
            return Ok(WorkloadSet { form: WorkloadForm::Workloads, seed: workloads.seed.clone(), members });
        }
        if let Some(stage) = &engine.stage {
            let seed = Seed::Run { version: stage.seed_version.clone(), workload: None };
            let mut members = vec![primary(&stage.workload, None)];
            for kept in self.kept_workloads()? {
                members.push(SetMember { name: kept.name, role: MemberRole::Kept, path: Some(kept.path), request: kept.request, seed: Some(seed.clone()) });
            }
            return Ok(WorkloadSet { form: WorkloadForm::Stage, seed: Some(seed), members });
        }
        let seed = engine.seed_version.clone().map(|version| Seed::Run { version, workload: None });
        Ok(WorkloadSet { form: WorkloadForm::One, seed: seed.clone(), members: vec![primary(ONE_WORKLOAD_NAME, seed)] })
    }

    /// Read and check the request file `path` of another workload of this run (`at` names it in refusals) with role
    /// `role`, in a run of form `form`: a general-line request, not itself a run of several workloads, without an output
    /// home, with a library of its own (not one of `libraries`, to which it is added) and the fields every workload
    /// shares equal to this request's (`hardware.threads`, `barriers`, `author_executable`, `engine.call_limit_seconds`,
    /// `engine.anon_memory_limit_bytes`, `engine.branches`).
    fn read_member_request(&self, at: &str, path: &Path, role: MemberRole, form: RunForm, libraries: &mut Vec<PathBuf>) -> Result<WorkloadRequest, RequestError> {
        let at = |detail: String| RequestError::Invalid(format!("{at}: {detail}"));
        let (what, run) = match form {
            RunForm::Stage => ("a kept workload", "stage run"),
            RunForm::Workloads => ("a member", "run"),
        };
        let goal = self.engine()?;
        let request = WorkloadRequest::read(path).map_err(|e| at(e.to_string()))?;
        request.validate_member(role).map_err(|e| at(e.to_string()))?;
        let engine = request.engine().map_err(|e| at(e.to_string()))?;
        if !engine.is_general() {
            return Err(at(format!("{what}'s request is a general-line request (engine.line \"general\")")));
        }
        if engine.stage.is_some() {
            return Err(at(format!("{what}'s request is not itself a stage run (no engine.stage)")));
        }
        if form == RunForm::Workloads && engine.workloads.is_some() {
            return Err(at("a member's request is not itself a run of several workloads (no engine.workloads)".into()));
        }
        if form == RunForm::Workloads && engine.seed_version.is_some() {
            return Err(at("a member's request names no engine.seed_version: the seed of its side is its members entry's seed".into()));
        }
        if request.output_home.is_some() {
            return Err(at(format!("{what} has no output_home of its own: the {run}'s output home shows every workload")));
        }
        if libraries.iter().any(|l| same_file(l, &request.library)) {
            return Err(at(format!("its library {} is another workload's: every workload has its own library", request.library.display())));
        }
        let (locks, goal_locks) = (&request.host_locks, &self.host_locks);
        let same_locks = same_file(&locks.activity_lock, &goal_locks.activity_lock)
            && same_file(&locks.build_lock, &goal_locks.build_lock)
            && same_file(&locks.race_lock, &goal_locks.race_lock);
        let shared = [
            ("hardware.threads", request.hardware.threads != self.hardware.threads),
            ("barriers", !same_locks),
            ("author_executable", request.author_executable != self.author_executable),
            ("engine.call_limit_seconds", engine.call_limit_seconds != goal.call_limit_seconds),
            ("engine.anon_memory_limit_bytes", engine.anon_memory_limit_bytes != goal.anon_memory_limit_bytes),
            ("engine.branches", engine.branches != goal.branches),
        ];
        if let Some((field, _)) = shared.iter().find(|(_, differs)| *differs) {
            return Err(at(format!("{field} differs from the {run} request's: every workload of a {run} shares it")));
        }
        libraries.push(request.library.clone());
        Ok(request)
    }
}

/// The run form a member request is read for ([`WorkloadRequest::read_member_request`]).
#[derive(Clone, Copy, PartialEq, Eq)]
enum RunForm {
    Stage,
    Workloads,
}

/// Whether a path is empty (an absent optional path field).
fn path_is_empty(path: &PathBuf) -> bool {
    path.as_os_str().is_empty()
}

/// Whether two absolute paths name the same file: equal once resolved (`canonicalize`, when both exist), else equal
/// once `.` and `..` components are removed lexically (a lock file not created yet).
fn same_file(a: &Path, b: &Path) -> bool {
    let lexical = |p: &Path| {
        let mut out = PathBuf::new();
        for component in p.components() {
            match component {
                std::path::Component::CurDir => {}
                std::path::Component::ParentDir => {
                    out.pop();
                }
                other => out.push(other),
            }
        }
        out
    };
    match (a.canonicalize(), b.canonicalize()) {
        (Ok(x), Ok(y)) => x == y,
        _ => lexical(a) == lexical(b),
    }
}

/// The refusal of a request whose `format_version` is not [`REQUEST_FORMAT`]: a format 1 request names its format-1-only fields.
fn format_refusal(value: &Value) -> RequestError {
    if value["format_version"] != 1 {
        return RequestError::Invalid(format!("unsupported request format_version {} (expected {REQUEST_FORMAT})", value["format_version"]));
    }
    let v7_fields = V7_ONLY_FIELDS
        .iter()
        .filter(|(field, _)| value.get(field).is_some())
        .map(|(field, replaced)| format!("{field}: {replaced}"))
        .chain(value.pointer("/hardware/memory_limit_bytes").map(|_| "hardware.memory_limit_bytes: a native representation-output bound; not used".to_string()))
        .collect();
    RequestError::FormatOne { v7_fields }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::controller::limits::tests::limits;
    use crate::controller::limits::Money;
    use serde_json::json;

    fn query(objective: Value) -> Result<QueryRequest, serde_json::Error> {
        serde_json::from_value(json!({"sql":"q","limits":json!(limits()),"objective":objective}))
    }

    #[test]
    fn objective_defaults_to_correctness_and_execution_time_is_typed_and_validated() {
        let hardware = Hardware { threads: vec![1, 4] };
        let omitted: QueryRequest = serde_json::from_value(json!({"sql":"q","limits":json!(limits())})).unwrap();
        assert!(omitted.objective.is_correctness());
        assert!(json!(omitted).get("objective").is_none(), "a correctness request serializes as before");

        let open = query(json!({"kind":"execution_time"})).unwrap();
        assert!(open.objective.is_execution_time() && open.objective.runtime_targets().is_empty());
        assert!(open.objective.validate(&open, &hardware).is_ok());

        let target = json!({"workers":4,"median_ns":1000,"provenance":"DuckDB 1.x, host h, SF1","timing_scope":"hot query call"});
        let targeted = query(json!({"kind":"execution_time","targets":[target]})).unwrap();
        assert_eq!(targeted.objective.runtime_targets()[0].median_ns, 1000);
        assert!(targeted.objective.validate(&targeted, &hardware).is_ok());

        let unguarded = Limits { max_iterations: UNSET_COUNT, max_cost_usd: Money::UNSET, ..limits() };
        let unguarded = QueryRequest { limits: unguarded, ..open.clone() };
        assert!(open.objective.validate(&unguarded, &hardware).is_err(), "an execution-time search needs a user guard");
        let unconfigured = query(json!({"kind":"execution_time","targets":[{"workers":8,"median_ns":1,"provenance":"p","timing_scope":"s"}]})).unwrap();
        assert!(unconfigured.objective.validate(&unconfigured, &hardware).is_err());
        let unsourced = query(json!({"kind":"execution_time","targets":[{"workers":1,"median_ns":1,"provenance":" ","timing_scope":"s"}]})).unwrap();
        assert!(unsourced.objective.validate(&unsourced, &hardware).is_err());
        assert!(query(json!({"kind":"execution_time","engines":["duckdb"]})).is_err(), "unknown objective fields are refused");
        assert!(query(json!({"kind":"verified_speedup"})).is_err());
    }

    #[test]
    fn early_stop_is_optional_and_needs_a_target_at_every_configured_worker_count() {
        let hardware = Hardware { threads: vec![1, 4] };
        let target = |workers: usize| json!({"workers":workers,"median_ns":1000,"provenance":"DuckDB 1.x, host h, SF1","timing_scope":"hot query call"});
        let legacy = query(json!({"kind":"execution_time","targets":[target(1), target(4)]})).unwrap();
        assert_eq!(legacy.objective.early_stop(), None);
        assert!(json!(legacy.objective).get("early_stop").is_none(), "a request without early_stop keeps its identity");
        let covered = query(json!({"kind":"execution_time","targets":[target(1), target(4)],"early_stop":{"min_speedup":5}})).unwrap();
        assert_eq!(covered.objective.early_stop(), Some(EarlyStop { min_speedup: 5 }));
        assert!(covered.objective.validate(&covered, &hardware).is_ok());
        let partial = query(json!({"kind":"execution_time","targets":[target(1)],"early_stop":{"min_speedup":5}})).unwrap();
        assert!(partial.objective.validate(&partial, &hardware).unwrap_err().contains("(\"statement\", 4)"), "a missing target never establishes the stop");
        let zero = query(json!({"kind":"execution_time","targets":[target(1), target(4)],"early_stop":{"min_speedup":0}})).unwrap();
        assert!(zero.objective.validate(&zero, &hardware).is_err());
    }

    /// A template's execution time is measured at the user's named benchmark bindings; targets carry the binding;
    /// the early stop needs the whole binding × worker matrix; a concrete statement keeps its implicit binding and
    /// its request JSON.
    #[test]
    fn template_execution_time_needs_named_bindings_and_a_full_target_matrix() {
        let hardware = Hardware { threads: vec![1, 4] };
        let template = |objective: Value| -> QueryRequest {
            serde_json::from_value(json!({"sql":"q","limits":json!(limits()),"objective":objective,
                "parameters":[{"index":1,"type":"integer","binding":{"free":{}}},{"index":2,"type":"date","binding":{"fixed":"1994-01-01"}}]})).unwrap()
        };
        let target = |binding: &str, workers: usize| json!({"binding":binding,"workers":workers,"median_ns":1000,"provenance":"DuckDB, host h, SF100","timing_scope":"hot query call"});
        let bindings = json!([{"name":"qgen","arguments":["15"]},{"name":"wide","arguments":["49"]}]);
        let full: Vec<Value> = ["qgen", "wide"].iter().flat_map(|b| [target(b, 1), target(b, 4)]).collect();
        let valid = template(json!({"kind":"execution_time","bindings":bindings,"targets":full,"early_stop":{"min_speedup":5}}));
        assert!(valid.is_template() && valid.objective.validate(&valid, &hardware).is_ok());
        assert_eq!(valid.objective.benchmark_bindings()[1].arguments, ["49"]);
        let invalid = |objective: Value| {
            let q = template(objective);
            q.objective.validate(&q, &hardware).unwrap_err()
        };
        assert!(invalid(json!({"kind":"execution_time"})).contains("needs objective.bindings"), "no framework default binding is measured");
        assert!(invalid(json!({"kind":"execution_time","bindings":[{"name":"a","arguments":[]}]})).contains("0 arguments for 1 free"));
        assert!(invalid(json!({"kind":"execution_time","bindings":[{"name":"a","arguments":["1"]},{"name":"a","arguments":["2"]}]})).contains("repeated"));
        assert!(invalid(json!({"kind":"execution_time","bindings":[{"name":"minimum","arguments":["1"]}]})).contains("framework binding name"));
        assert!(invalid(json!({"kind":"execution_time","bindings":bindings,"targets":[{"workers":1,"median_ns":1,"provenance":"p","timing_scope":"s"}]})).contains("must name its benchmark binding"));
        assert!(invalid(json!({"kind":"execution_time","bindings":bindings,"targets":[target("other", 1)]})).contains("not a benchmark binding"));
        assert!(invalid(json!({"kind":"execution_time","bindings":bindings,"targets":[target("qgen", 1), target("qgen", 1)]})).contains("distinct cell"));
        let partial: Vec<Value> = full[..3].to_vec();
        assert!(invalid(json!({"kind":"execution_time","bindings":bindings,"targets":partial,"early_stop":{"min_speedup":5}})).contains("(\"wide\", 4)"), "every matrix cell needs a target");
        let concrete = query(json!({"kind":"execution_time","bindings":[{"name":"a","arguments":[]}]})).unwrap();
        assert!(concrete.objective.validate(&concrete, &hardware).unwrap_err().contains("for templates"));
        let named = query(json!({"kind":"execution_time","targets":[target("statement", 1), target("statement", 4)],"early_stop":{"min_speedup":5}})).unwrap();
        assert!(named.objective.validate(&named, &hardware).is_ok(), "a concrete statement's target may name its one binding");
        let saved = json!({"kind":"execution_time","targets":[{"workers":1,"median_ns":7,"provenance":"p","timing_scope":"s"}],"early_stop":{"min_speedup":5}});
        assert_eq!(json!(query(saved.clone()).unwrap().objective), saved, "a saved concrete objective keeps its JSON identity");
    }

    /// Absent `author_model` is Opus 5.5 and keeps an existing request's JSON; a supported model id selects that
    /// model; anything else (aliases, other models) is refused when the request is decoded, naming the supported ids.
    #[test]
    fn author_model_defaults_to_opus_and_accepts_only_supported_model_ids() {
        let request = |model: Option<&str>| {
            let mut value = json!({"format_version":2,"dataset":{"tables":[]},"queries":[{"sql":"q","limits":json!(limits())}],
                "hardware":{"threads":[1]},"max_concurrent_queries":1,"author_executable":"claude","library":"library",
                "barriers":{"activity_lock":"/l/a","build_lock":"/l/b","race_lock":"/l/r"}});
            if let Some(model) = model {
                value["author_model"] = json!(model);
            }
            serde_json::from_value::<WorkloadRequest>(value)
        };
        let default = request(None).unwrap();
        assert_eq!((default.author_model, default.author_model.id()), (AuthorModel::Opus55, "claude-opus-5-5"));
        assert!(json!(default).get("author_model").is_none(), "an existing request keeps its identity");
        let sonnet = request(Some("claude-sonnet-5-5")).unwrap();
        assert_eq!(sonnet.author_model.id(), "claude-sonnet-5-5");
        assert_eq!(json!(sonnet)["author_model"], "claude-sonnet-5-5");
        assert_eq!(request(Some("claude-opus-5-5")).unwrap().author_model, AuthorModel::Opus55);
        for invalid in ["sonnet", "claude-sonnet-5", "claude-haiku-4-5", ""] {
            let error = request(Some(invalid)).unwrap_err().to_string();
            assert!(error.contains("expected `claude-opus-5-5` or `claude-sonnet-5-5`"), "{invalid}: {error}");
        }
    }

    #[test]
    fn stop_before_queries_is_optional_and_serializes_only_when_set() {
        let storage: WorkloadStorageRequest = serde_json::from_value(json!({"limits":json!(limits())})).unwrap();
        assert!(!storage.stop_before_queries && json!(storage).get("stop_before_queries").is_none(), "an existing request keeps its identity");
        let only: WorkloadStorageRequest = serde_json::from_value(json!({"limits":json!(limits()),"stop_before_queries":true})).unwrap();
        assert!(only.stop_before_queries);
    }

    #[test]
    fn reselect_from_is_optional_and_absolute_after_reading() {
        let omitted: QueryRequest = serde_json::from_value(json!({"sql":"q","limits":json!(limits())})).unwrap();
        assert!(omitted.reselect_from.is_none() && json!(omitted).get("reselect_from").is_none(), "an existing request keeps its identity");
        let root = crate::controller::test_support::scratch_root("request-reselect");
        records::create_dir(&root).unwrap();
        let path = root.join("request.json");
        records::write_new_json(&path, &json!({"format_version":2,"dataset":{"tables":[]},
            "queries":[{"sql":"q","limits":json!(limits()),"reselect_from":"earlier/queries/query-0000"}],
            "hardware":{"threads":[1]},"max_concurrent_queries":1,"author_executable":"claude","library":"library",
            "barriers":{"activity_lock":"l/a","build_lock":"l/b","race_lock":"l/r"}})).unwrap();
        let read = WorkloadRequest::read(&path).unwrap();
        assert_eq!(read.queries[0].reselect_from.as_deref(), Some(root.canonicalize().unwrap().join("earlier/queries/query-0000").as_path()));
    }

    /// `continue_from` is optional (an existing request keeps its identity), made absolute when read, needs the
    /// execution_time objective and excludes `reselect_from`.
    #[test]
    fn continue_from_is_optional_absolute_and_needs_an_execution_time_author_session() {
        let omitted: QueryRequest = serde_json::from_value(json!({"sql":"q","limits":json!(limits())})).unwrap();
        assert!(omitted.continue_from.is_none() && json!(omitted).get("continue_from").is_none(), "an existing request keeps its identity");
        let root = crate::controller::test_support::scratch_root("request-continue");
        records::create_dir(&root).unwrap();
        let write = |name: &str, query: Value| {
            let path = root.join(name);
            records::write_new_json(&path, &json!({"format_version":2,"dataset":{"tables":[]},"queries":[query],
                "hardware":{"threads":[1]},"max_concurrent_queries":1,"author_executable":"claude","library":"library",
                "barriers":{"activity_lock":"l/a","build_lock":"l/b","race_lock":"l/r"}})).unwrap();
            WorkloadRequest::read(&path).unwrap()
        };
        let timed = json!({"kind":"execution_time"});
        let read = write("continue.json", json!({"sql":"q","limits":json!(limits()),"objective":timed,"continue_from":"earlier/queries/query-0000"}));
        assert_eq!(read.queries[0].continue_from.as_deref(), Some(root.canonicalize().unwrap().join("earlier/queries/query-0000").as_path()));
        read.validate().unwrap();
        let correctness = write("correctness.json", json!({"sql":"q","limits":json!(limits()),"continue_from":"earlier/queries/query-0000"}));
        assert!(correctness.validate().unwrap_err().to_string().contains("needs the execution_time objective"));
        let both = write("both.json", json!({"sql":"q","limits":json!(limits()),"objective":timed,"continue_from":"a/queries/query-0000","reselect_from":"a/queries/query-0000"}));
        assert!(both.validate().unwrap_err().to_string().contains("continue_from and reselect_from exclude each other"));
        std::fs::remove_dir_all(root).unwrap();
    }

    /// Absent `integrity_constraints` keeps a request's JSON; a declaration list is decoded and structurally validated
    /// (named refusals), and a valid list is accepted.
    #[test]
    fn integrity_constraints_are_optional_and_validated() {
        let request = |constraints: Option<Value>| {
            let mut value = json!({"format_version":2,
                "dataset":{"tables":[{"name":"t","fields":[{"name":"a","ty":"I64","nullable":false}],"locations":[],"format":"Parquet"}]},
                "queries":[{"sql":"q","limits":json!(limits())}],"hardware":{"threads":[1]},"max_concurrent_queries":1,
                "author_executable":"claude","library":"library","barriers":{"activity_lock":"/l/a","build_lock":"/l/b","race_lock":"/l/r"}});
            if let Some(constraints) = constraints {
                value["integrity_constraints"] = constraints;
            }
            serde_json::from_value::<WorkloadRequest>(value)
        };
        let omitted = request(None).unwrap();
        assert!(omitted.integrity_constraints.is_none() && json!(omitted).get("integrity_constraints").is_none(), "an existing request keeps its identity");
        assert!(omitted.validate().is_ok());
        let declared = json!({"trust":"user_declared","declarations":[{"table":"t","sql":"PRIMARY KEY (a)"}]});
        let valid = request(Some(declared.clone())).unwrap();
        assert_eq!(json!(valid)["integrity_constraints"], declared);
        assert!(valid.validate().is_ok());
        let invalid = |constraints: Value| request(Some(constraints)).unwrap().validate().unwrap_err().to_string();
        assert!(invalid(json!({"trust":"checked","declarations":declared["declarations"]})).contains("integrity_constraints_trust_unsupported"));
        assert!(invalid(json!({"trust":"user_declared","declarations":[]})).contains("integrity_constraints_invalid"));
        assert!(invalid(json!({"trust":"user_declared","declarations":[{"table":"u","sql":"PRIMARY KEY (a)"}]})).contains("not a dataset table"));
        assert!(request(Some(json!({"trust":"user_declared","declarations":[],"checked":true}))).is_err(), "unknown fields are refused");
        // The canonical TPC-H list is a request field value as it stands.
        let canonical: Value = serde_json::from_str(&std::fs::read_to_string(
            Path::new(env!("CARGO_MANIFEST_DIR")).join("../fixtures/tpch/integrity-constraints.json")).unwrap()).unwrap();
        let canonical: IntegrityConstraints = serde_json::from_value(canonical).unwrap();
        assert_eq!((canonical.trust.as_str(), canonical.declarations.len()), ("user_declared", 15));
    }

    /// An engine request has no queries, uses physical_only with a budget, declares its constraints, validates with
    /// formal_proofs and names its capture; each rule is refused by name, and an absent section keeps the JSON identity.
    #[test]
    fn engine_requests_follow_the_engine_rules() {
        let engine = json!({"templates":"t/templates.json","bindings":"b.json","timing_binding":"v0","targets":"targets.json","variants":"v/manifest.json",
            "storage_seed":{"source_library":"lib","packages":["07".repeat(32)]},"limits":json!(limits())});
        let base = json!({"format_version":2,
            "dataset":{"tables":[{"name":"t","fields":[{"name":"a","ty":"I64","nullable":false}],"locations":[],"format":"Parquet"}]},
            "queries":[],"hardware":{"threads":[1,32,64]},"max_concurrent_queries":1,"author_executable":"claude","library":"library",
            "barriers":{"activity_lock":"/l/a","build_lock":"/l/b","race_lock":"/l/r"},"prepared_workload":"capture",
            "data_allowance":{"live_bytes":1000},"storage_policy":{"kind":"physical_only","eligible_storages":[]},
            "integrity_constraints":{"trust":"user_declared","declarations":[{"table":"t","sql":"PRIMARY KEY (a)"}]},
            "validation":{"kind":"formal_proofs","numeric_relative_tolerance":"1e-9","saved_answers":[{"query":"Q01","binding":"v0","engine":"duckdb","description":"d","path":"a.json","rows_pointer":""}]},
            "engine":engine});
        let request = |edit: &dyn Fn(&mut Value)| {
            let mut value = base.clone();
            edit(&mut value);
            serde_json::from_value::<WorkloadRequest>(value).unwrap().validate()
        };
        assert!(request(&|_| {}).is_ok(), "{:?}", request(&|_| {}).err().map(|e| e.to_string()));
        let refused = |edit: &dyn Fn(&mut Value), words: &str| {
            let error = request(edit).unwrap_err().to_string();
            assert!(error.contains(words), "{words}: {error}");
        };
        refused(&|v| v["queries"] = json!([{"sql":"q","limits":json!(limits())}]), "no queries[]");
        refused(&|v| v["storage_policy"] = json!({"kind":"unrestricted"}), "physical_only");
        refused(&|v| { v.as_object_mut().unwrap().remove("data_allowance"); }, "data_allowance");
        refused(&|v| { v.as_object_mut().unwrap().remove("integrity_constraints"); }, "integrity_constraints");
        refused(&|v| { v.as_object_mut().unwrap().remove("validation"); }, "formal_proofs");
        refused(&|v| v["engine"]["storage_seed"]["packages"] = json!([]), "storage_seed");
        refused(&|v| v["engine"]["reuse_libraries"] = json!(["library"]), "reuse_libraries");
        let reuse = |v: &mut Value| {
            v["engine"]["reuse_libraries"] = json!(["single-copy"]);
            v["engine"]["pause_after_round"] = json!(true);
        };
        assert!(request(&reuse).is_ok());
        let plain: WorkloadRequest = serde_json::from_value(base.clone()).unwrap();
        let engine_fields = json!(plain)["engine"].as_object().unwrap().keys().cloned().collect::<Vec<_>>();
        assert!(!engine_fields.iter().any(|f| f == "reuse_libraries" || f == "pause_after_round"), "absent options keep the request's JSON identity: {engine_fields:?}");
        let without = serde_json::from_value::<WorkloadRequest>(json!({"format_version":2,"dataset":{"tables":[]},"queries":[{"sql":"q","limits":json!(limits())}],
            "hardware":{"threads":[1]},"max_concurrent_queries":1,"author_executable":"claude","library":"library","barriers":{"activity_lock":"/l/a","build_lock":"/l/b","race_lock":"/l/r"}})).unwrap();
        assert!(json!(without).get("engine").is_none() && without.engine().is_err(), "a workload request keeps its identity and is no engine run");
    }

    /// The general line: its fields are validated with a named refusal each, the schema line refuses
    /// them, absent fields keep a request's JSON identity (the emphasis included), the review cadence is not
    /// part of the run's identity, a relaunch may raise the budget but not lower it, and a scale's view
    /// carries its locations, capture and saved answers.
    #[test]
    fn general_line_requests_follow_their_rules() {
        let scale = |name: &str, bytes: u64| {
            json!({"name":name,"locations":{"t":[format!("{name}/t.parquet")]},"prepared_workload":format!("{name}/capture"),
                "bindings":format!("{name}/visible.json"),"targets":format!("{name}/targets.json"),
                "saved_answers":[{"query":"Q01","binding":"v0","engine":"duckdb","description":"d","path":format!("{name}/a.json"),"rows_pointer":""}],
                "original_data_bytes":bytes,"original_data_record":format!("{name}/generation.json")})
        };
        let budget = json!({"max_iterations":"unset","max_cost_usd":"1000","spend_policy":"estimated_usd","max_retries_per_iteration":2,"author_timeout_seconds":"unset"});
        let base = json!({"format_version":2,
            "dataset":{"tables":[{"name":"t","fields":[{"name":"a","ty":"I64","nullable":false}],"locations":["sf1/t.parquet"],"format":"Parquet"}]},
            "queries":[],"hardware":{"threads":[1,32,64]},"max_concurrent_queries":1,"author_executable":"claude","library":"library",
            "barriers":{"activity_lock":"/l/a","build_lock":"/l/b","race_lock":"/l/r"},"storage_policy":{"kind":"physical_only","eligible_storages":[]},
            "integrity_constraints":{"trust":"user_declared","declarations":[{"table":"t","sql":"PRIMARY KEY (a)"}]},
            "validation":{"kind":"formal_proofs","numeric_relative_tolerance":"1e-9"},
            "engine":{"line":"general","templates":"t/templates.json","timing_binding":"v0","variants":"v/manifest.json",
                "storage_seed":{"source_library":"lib","packages":["07".repeat(32)]},"limits":budget,
                "scales":[scale("sf1", 100), scale("sf10", 1000)],"branches":3,"pause_after_session":"first_session_of_each_branch",
                "call_limit_seconds":60,"anon_memory_limit_bytes":154_618_822_656u64}});
        let parse = |edit: &dyn Fn(&mut Value)| {
            let mut value = base.clone();
            edit(&mut value);
            serde_json::from_value::<WorkloadRequest>(value)
        };
        let valid = parse(&|_| {}).unwrap();
        assert!(valid.validate().is_ok(), "{:?}", valid.validate().err().map(|e| e.to_string()));
        let engine = valid.engine().unwrap();
        assert!(engine.is_general() && engine.scale("sf10").map(|(i, _)| i) == Some(1) && engine.pause_after_session == PauseCadence::FirstSessionOfEachBranch);
        let refused = |edit: &dyn Fn(&mut Value), words: &str| {
            let error = parse(edit).unwrap().validate().unwrap_err().to_string();
            assert!(error.contains(words), "{words}: {error}");
        };
        refused(&|v| v["engine"]["line"] = json!("fast"), "not a known engine line");
        refused(&|v| v["engine"]["bindings"] = json!("b.json"), "per scale");
        refused(&|v| v["engine"]["pause_after_round"] = json!(true), "pause_after_session");
        refused(&|v| v["prepared_workload"] = json!("capture"), "per scale");
        refused(&|v| v["data_allowance"] = json!({"live_bytes":1}), "per scale");
        refused(&|v| v["validation"]["saved_answers"] = base["engine"]["scales"][0]["saved_answers"].clone(), "per scale");
        for branches in [json!(0), json!(4), Value::Null] {
            refused(&|v| v["engine"]["branches"] = branches.clone(), "1 to 3");
        }
        refused(&|v| { v["engine"].as_object_mut().unwrap().remove("call_limit_seconds"); }, "call_limit_seconds");
        refused(&|v| v["engine"]["anon_memory_limit_bytes"] = json!(0), "anon_memory_limit_bytes");
        refused(&|v| v["engine"]["limits"]["max_cost_usd"] = json!("unset"), "budget");
        refused(&|v| v["engine"]["limits"]["max_iterations"] = json!(5), "unset for the general line");
        refused(&|v| v["engine"]["scales"] = json!([]), "scale ladder");
        refused(&|v| v["engine"]["scales"] = json!([scale("sf1", 100), scale("sf1", 100)]), "unique name");
        refused(&|v| v["engine"]["scales"][1]["locations"] = json!({"u":["x"]}), "every dataset table");
        refused(&|v| v["engine"]["scales"][1]["original_data_bytes"] = json!(0), "must be positive");
        refused(&|v| v["dataset"]["tables"][0]["locations"] = json!(["sf10/t.parquet"]), "first scale");
        assert!(parse(&|v| v["engine"]["pause_after_session"] = json!("sometimes")).is_err(), "an unknown cadence is refused when decoded");
        // The emphasis: optional, one known value, absent from the JSON when not set.
        let emphasized = parse(&|v| v["engine"]["emphasis"] = json!("co_optimization")).unwrap();
        assert!(emphasized.validate().is_ok() && emphasized.engine().unwrap().emphasis == Some(EngineEmphasis::CoOptimization));
        assert_eq!(json!(emphasized)["engine"]["emphasis"], "co_optimization");
        assert!(engine.emphasis.is_none() && json!(valid)["engine"].get("emphasis").is_none(), "absent, the request keeps its JSON identity");
        assert!(parse(&|v| v["engine"]["emphasis"] = json!("speed")).is_err(), "an unknown emphasis is refused when decoded");
        // The schema line refuses every general-line field and keeps its JSON identity without them.
        let schema_line = |edit: &dyn Fn(&mut Value)| {
            let mut value = base.clone();
            let engine = value["engine"].as_object_mut().unwrap();
            for field in ["line", "scales", "branches", "pause_after_session", "call_limit_seconds", "anon_memory_limit_bytes", "emphasis"] {
                engine.remove(field);
            }
            value["engine"]["bindings"] = json!("b.json");
            value["engine"]["targets"] = json!("targets.json");
            value["engine"]["limits"]["max_iterations"] = json!(3);
            value["prepared_workload"] = json!("capture");
            value["data_allowance"] = json!({"live_bytes":100});
            edit(&mut value);
            serde_json::from_value::<WorkloadRequest>(value).unwrap()
        };
        assert!(schema_line(&|_| {}).validate().is_ok());
        let fields: Vec<String> = json!(schema_line(&|_| {}))["engine"].as_object().unwrap().keys().cloned().collect();
        assert!(!fields.iter().any(|f| ["line", "scales", "branches", "pause_after_session", "call_limit_seconds", "anon_memory_limit_bytes", "emphasis"].contains(&f.as_str())), "{fields:?}");
        for (field, value) in [("branches", json!(1)), ("call_limit_seconds", json!(60)), ("pause_after_session", json!("every_session")), ("emphasis", json!("co_optimization")),
            ("stage", json!({"workload":"w","seed_version":{"run":"r","version":"v1"},"kept_workloads":[]})), ("seed_version", json!({"run":"r","version":"v1"})),
            ("workloads", json!({"name":"w","members":[]}))] {
            let error = schema_line(&|v| v["engine"][field] = value.clone()).validate().unwrap_err().to_string();
            assert!(error.contains("general-line field"), "{field}: {error}");
        }
        // A continued run: `seed_version` is optional, absent from the JSON when not set, starts the
        // run at the last scale, and is not combined with a stage run.
        let seeded = parse(&|v| v["engine"]["seed_version"] = json!({"run":"run2","version":"v016"})).unwrap();
        assert!(seeded.validate().is_ok());
        let seed = seeded.engine().unwrap().seed_version.clone().unwrap();
        assert_eq!(json!(seeded)["engine"]["seed_version"]["version"], "v016");
        assert_eq!(seed.directory(), Path::new("run2/engine/versions/v016"));
        assert_eq!((seeded.engine().unwrap().start_scale(), engine.start_scale()), (engine.scales.len() - 1, 0), "a continued run starts at the last scale");
        assert!(json!(valid)["engine"].get("seed_version").is_none(), "absent, the request keeps its JSON identity");
        assert!(parse(&|v| v["engine"]["seed_version"] = json!({"run":"run2","version":"../v016"})).unwrap().validate().unwrap_err().to_string().contains("engine.seed_version.version"));
        let both = parse(&|v| {
            v["engine"]["seed_version"] = json!({"run":"run2","version":"v016"});
            v["engine"]["stage"] = json!({"workload":"w","seed_version":{"run":"r","version":"v1"},"kept_workloads":[]});
        });
        assert!(both.unwrap().validate().unwrap_err().to_string().contains("a stage run names its seed"));
        assert!(schema_line(&|v| { v["engine"].as_object_mut().unwrap().remove("targets"); }).validate().unwrap_err().to_string().contains("engine.targets"));
        // A scale's view: its locations, capture and saved answers.
        let at = valid.at_scale(&engine.scales[1]);
        assert_eq!(at.dataset.tables[0].locations, [PathBuf::from("sf10/t.parquet")]);
        assert_eq!(at.prepared_workload.as_deref(), Some(Path::new("sf10/capture")));
        assert!(matches!(&at.validation, ValidationPolicy::FormalProofs { saved_answers, .. } if saved_answers[0].path == Path::new("sf10/a.json")));
        // The review cadence and the number of branches are scheduling controls: a relaunch may switch them (one line,
        // three branches with a pause after each first session become one with no pause). Every
        // other field stays part of the run's identity.
        let root = crate::controller::test_support::scratch_root("request-general-identity");
        records::create_dir(&root).unwrap();
        let record = |request: &WorkloadRequest| crate::controller::workload_run::lifecycle::record_request(&root, &json!(request));
        let recorded = record(&valid).unwrap();
        let switched = parse(&|v| { v["engine"].as_object_mut().unwrap().remove("pause_after_session"); }).unwrap();
        assert!(!recorded && record(&switched).unwrap());
        let one_line = parse(&|v| {
            v["engine"]["branches"] = json!(1);
            v["engine"]["pause_after_session"] = json!("never");
        })
        .unwrap();
        assert!(one_line.validate().is_ok() && json!(one_line)["engine"].get("pause_after_session").is_none(), "the cadence never is absent");
        assert!(record(&one_line).unwrap(), "a relaunch may change the branch count and the cadence");
        assert!(record(&parse(&|v| v["engine"]["branches"] = json!(2)).unwrap()).unwrap());
        for (edit, what) in [
            (&(|v: &mut Value| v["engine"]["limits"]["max_cost_usd"] = json!("999")) as &dyn Fn(&mut Value), "a lower budget"),
            (&|v: &mut Value| v["engine"]["emphasis"] = json!("co_optimization"), "the emphasis"),
            (&|v: &mut Value| v["engine"]["call_limit_seconds"] = json!(30), "the call limit"),
            (&|v: &mut Value| v["engine"]["timing_binding"] = json!("v1"), "the timing binding"),
            (&|v: &mut Value| v["engine"]["scales"][1]["original_data_bytes"] = json!(999), "a scale"),
            (&|v: &mut Value| v["engine"]["reuse_libraries"] = json!(["other"]), "the reuse libraries"),
            (&|v: &mut Value| v["author_executable"] = json!("other-claude"), "the author executable"),
        ] {
            let changed = parse(&|v| {
                v["engine"]["branches"] = json!(1);
                edit(v);
            })
            .unwrap();
            assert!(record(&changed).is_err(), "{what} is part of the identity");
        }
        // A relaunch may raise the budget, never lower it: request.json stays, each raise is a new record,
        // and the newest raise is the run's budget from then on.
        let lifecycle_records = |name: &str| records::read_json::<Value>(&root.join(name)).unwrap();
        let budget = |dollars: &str| parse(&|v| v["engine"]["limits"]["max_cost_usd"] = json!(dollars)).unwrap();
        let recorded_request = std::fs::read(root.join("request.json")).unwrap();
        assert!(record(&budget("1500")).unwrap(), "a raise is accepted");
        let raise = lifecycle_records(crate::controller::workload_run::lifecycle::BUDGET_RAISE);
        assert_eq!((raise["from"].as_str(), raise["to"].as_str()), (Some("1000"), Some("1500")), "{raise}");
        assert!(record(&budget("1500")).unwrap() && !root.join("budget-raise-1.json").exists(), "the same budget again records nothing");
        let lowered = record(&budget("1000")).unwrap_err().to_string();
        assert!(lowered.contains("never lower it") && lowered.contains("budget-raise.json") && lowered.contains("1500"), "{lowered}");
        assert!(record(&budget("2000.5")).unwrap());
        assert_eq!(lifecycle_records("budget-raise-1.json")["to"], "2000.5");
        assert!(record(&budget("1500")).is_err(), "below the newest raise");
        let raised_and_changed = parse(&|v| {
            v["engine"]["limits"]["max_cost_usd"] = json!("3000");
            v["engine"]["call_limit_seconds"] = json!(30);
        })
        .unwrap();
        assert!(record(&raised_and_changed).is_err() && !root.join("budget-raise-2.json").exists(), "a raise admits no other change");
        let mut unset = json!(budget("2000.5"));
        unset["engine"]["limits"]["max_cost_usd"] = json!("unset");
        assert!(crate::controller::workload_run::lifecycle::record_request(&root, &unset).is_err(), "an unset budget is no raise");
        assert_eq!(std::fs::read(root.join("request.json")).unwrap(), recorded_request, "request.json stays as written");
        std::fs::remove_dir_all(&root).unwrap();
        // On the schema line nothing changes: a branch count there is refused by validation, and the comparison keeps
        // every engine field but the two review cadences.
        let schema_root = crate::controller::test_support::scratch_root("request-schema-identity");
        records::create_dir(&schema_root).unwrap();
        let schema_request = json!(schema_line(&|_| {}));
        assert!(!crate::controller::workload_run::lifecycle::record_request(&schema_root, &schema_request).unwrap());
        let mut with_branches = schema_request.clone();
        with_branches["engine"]["branches"] = json!(1);
        assert!(crate::controller::workload_run::lifecycle::record_request(&schema_root, &with_branches).is_err(), "the schema line compares engine.branches like any field");
        let mut raised = schema_request.clone();
        raised["engine"]["limits"]["max_cost_usd"] = json!("2000");
        assert!(crate::controller::workload_run::lifecycle::record_request(&schema_root, &raised).is_err(), "the schema line compares its budget like any field");
        std::fs::remove_dir_all(&schema_root).unwrap();
    }

    /// A general-line request whose library is `library`, at worker counts `threads`, with its lock files under `locks`
    /// (relative paths: they resolve against the request file when read).
    fn general_request(library: &str, threads: Value, locks: &str) -> Value {
        let scale = json!({"name":"sf1","locations":{"t":["sf1/t.parquet"]},"prepared_workload":"sf1/capture","bindings":"sf1/visible.json","targets":"sf1/targets.json",
            "saved_answers":[],"original_data_bytes":100,"original_data_record":"sf1/generation.json"});
        let budget = json!({"max_iterations":"unset","max_cost_usd":"1000","spend_policy":"estimated_usd","max_retries_per_iteration":2,"author_timeout_seconds":"unset"});
        json!({"format_version":2,
            "dataset":{"tables":[{"name":"t","fields":[{"name":"a","ty":"I64","nullable":false}],"locations":["sf1/t.parquet"],"format":"Parquet"}]},
            "queries":[],"hardware":{"threads":threads},"max_concurrent_queries":1,"author_executable":"claude","library":library,
            "barriers":{"activity_lock":format!("{locks}/a"),"build_lock":format!("{locks}/b"),"race_lock":format!("{locks}/r")},"storage_policy":{"kind":"physical_only","eligible_storages":[]},
            "integrity_constraints":{"trust":"user_declared","declarations":[{"table":"t","sql":"PRIMARY KEY (a)"}]},
            "validation":{"kind":"formal_proofs","numeric_relative_tolerance":"1e-9"},
            "engine":{"line":"general","templates":"t/templates.json","timing_binding":"v0","variants":"v/manifest.json",
                "storage_seed":{"source_library":"lib","packages":["07".repeat(32)]},"limits":budget,"scales":[scale],"branches":1,
                "call_limit_seconds":60,"anon_memory_limit_bytes":154_618_822_656u64}})
    }

    /// A stage run: `engine.stage` is optional (absent, the request keeps its JSON identity) and part
    /// of the identity when present; its names follow the name rule and are unique; its paths resolve against the
    /// request file; each kept workload's request is read and validated, and refused when it is not a plain general-line
    /// request with its own library or differs in a shared field (threads, barriers, branches, ...).
    #[test]
    fn stage_requests_follow_their_rules() {
        let root = crate::controller::test_support::scratch_root("request-stage");
        records::create_dir(&root).unwrap();
        let stage = json!({"workload":"sec","seed_version":{"run":"run2","version":"v016"},"kept_workloads":[{"name":"tpch","request":"kept/tpch.json"}]});
        let write = |name: &str, value: &Value| {
            let path = root.join(name);
            records::create_dir(path.parent().unwrap()).unwrap();
            std::fs::write(&path, serde_json::to_vec_pretty(value).unwrap()).unwrap();
            path
        };
        // Shared fields compare as written: both requests name the lock files by the same absolute paths.
        let locks = root.join("l").display().to_string();
        let mut goal = general_request("library-sec", json!([1, 32, 64]), &locks);
        let plain: WorkloadRequest = serde_json::from_value(goal.clone()).unwrap();
        assert!(json!(plain)["engine"].get("stage").is_none() && plain.kept_workloads().unwrap().is_empty(), "absent, the request keeps its JSON identity");
        goal["engine"]["stage"] = stage.clone();
        let kept = general_request("../library-tpch", json!([1, 32, 64]), &locks);
        write("kept/tpch.json", &kept);
        let request = WorkloadRequest::read(&write("stage.json", &goal)).unwrap();
        request.validate().unwrap();
        let section = request.engine().unwrap().stage.clone().unwrap();
        let base = root.canonicalize().unwrap();
        assert_eq!(section.workload_names(), ["sec", "tpch"]);
        assert_eq!(section.seed_version_directory(), base.join("run2/engine/versions/v016"));
        assert_eq!(json!(request)["engine"]["stage"]["kept_workloads"][0]["request"], json!(base.join("kept/tpch.json")));
        let read = request.kept_workloads().unwrap();
        assert_eq!((read[0].name.as_str(), read[0].request.library.clone()), ("tpch", base.join("kept/../library-tpch")));
        assert!(same_file(&base.join("kept/../l/a"), &base.join("l/a")) && !same_file(&base.join("kept/l/a"), &base.join("l/a")), "paths compare once resolved");

        // The section's own rules.
        let invalid = |edit: &dyn Fn(&mut Value)| {
            let mut value = goal.clone();
            edit(&mut value);
            serde_json::from_value::<WorkloadRequest>(value).unwrap().validate().unwrap_err().to_string()
        };
        assert!(invalid(&|v| v["engine"]["stage"]["kept_workloads"][0]["name"] = json!("sec")).contains("given twice"));
        assert!(invalid(&|v| v["engine"]["stage"]["workload"] = json!("SEC")).contains(EngineStage::NAME_RULE));
        assert!(invalid(&|v| v["engine"]["stage"]["kept_workloads"][0]["name"] = json!("tpc-h")).contains(EngineStage::NAME_RULE));
        assert!(invalid(&|v| v["engine"]["stage"]["seed_version"]["version"] = json!("../v016")).contains("seed_version.version"));
        assert!(serde_json::from_value::<WorkloadRequest>({ let mut v = goal.clone(); v["engine"]["stage"]["guard"] = json!(0.1); v }).is_err(), "no other field (no guard)");

        // The kept workloads' requests.
        let refused = |name: &str, edit: &dyn Fn(&mut Value), words: &str| {
            let mut value = kept.clone();
            edit(&mut value);
            write(&format!("kept/{name}.json"), &value);
            let mut stage_value = goal.clone();
            stage_value["engine"]["stage"]["kept_workloads"][0]["request"] = json!(format!("kept/{name}.json"));
            let request = WorkloadRequest::read(&write(&format!("stage-{name}.json"), &stage_value)).unwrap();
            request.validate().unwrap();
            let error = request.kept_workloads().unwrap_err().to_string();
            assert!(error.contains(words) && error.contains("kept_workloads[tpch]"), "{name}: {words}: {error}");
        };
        refused("threads", &|v| v["hardware"]["threads"] = json!([1, 64]), "hardware.threads differs");
        refused("barriers", &|v| v["barriers"]["race_lock"] = json!(format!("{locks}/other")), "barriers differs");
        refused("branches", &|v| v["engine"]["branches"] = json!(2), "engine.branches differs");
        refused("call-limit", &|v| v["engine"]["call_limit_seconds"] = json!(30), "engine.call_limit_seconds differs");
        refused("library", &|v| v["library"] = json!("../library-sec"), "another workload's");
        refused("output", &|v| v["output_home"] = json!("out"), "no output_home");
        refused("nested", &|v| v["engine"]["stage"] = stage.clone(), "not itself a stage run");
        refused("invalid", &|v| v["engine"]["branches"] = json!(9), "1 to 3");
        std::fs::remove_dir_all(&root).unwrap();
    }

    /// A run of several workloads: `engine.workloads` is optional (absent, the
    /// request keeps its JSON identity) and part of the identity when present; its paths resolve against the request
    /// file; names follow the name rule, are unique and not `default`; a seed is `{run, version, workload?}` or
    /// `{source}`; it excludes `engine.stage` and `engine.seed_version`; each member's request is read and refused as a
    /// kept workload's is, and also when it is itself a run of several workloads or names a seed version; a check
    /// member's scales may omit `targets`, nobody else's; the workload set lists the primary first with every role and
    /// seed; the run starts at its last scale.
    #[test]
    fn workloads_requests_follow_their_rules() {
        let root = crate::controller::test_support::scratch_root("request-workloads");
        records::create_dir(&root).unwrap();
        let write = |name: &str, value: &Value| {
            let path = root.join(name);
            records::create_dir(path.parent().unwrap()).unwrap();
            std::fs::write(&path, serde_json::to_vec_pretty(value).unwrap()).unwrap();
            path
        };
        let locks = root.join("l").display().to_string();
        let mut run = general_request("library-tpch", json!([1, 32, 64]), &locks);
        let plain: WorkloadRequest = serde_json::from_value(run.clone()).unwrap();
        assert!(json!(plain)["engine"].get("workloads").is_none(), "absent, the request keeps its JSON identity");
        let workloads = json!({"name":"tpch","seed":{"run":"ce/run","version":"v004"},"members":[
            {"name":"sec","role":"counted","request":"members/sec.json","seed":{"run":"s2/run","version":"v001","workload":"sec"}},
            {"name":"anyschema","role":"check","request":"members/anyschema.json"},
            {"name":"old","role":"kept","request":"members/old.json","seed":{"source":"exported/engine"}}]});
        run["engine"]["workloads"] = workloads.clone();
        run["engine"]["scales"] = json!([run["engine"]["scales"][0].clone(), {"name":"sf10","locations":{"t":["sf10/t.parquet"]},"prepared_workload":"sf10/capture",
            "bindings":"sf10/visible.json","targets":"sf10/targets.json","saved_answers":[],"original_data_bytes":1000,"original_data_record":"sf10/generation.json"}]);
        let member = general_request("../library-sec", json!([1, 32, 64]), &locks);
        write("members/sec.json", &member);
        write("members/old.json", &general_request("../library-old", json!([1, 32, 64]), &locks));
        let mut check = general_request("../library-anyschema", json!([1, 32, 64]), &locks);
        check["engine"]["scales"][0].as_object_mut().unwrap().remove("targets");
        write("members/anyschema.json", &check);
        let request = WorkloadRequest::read(&write("run.json", &run)).unwrap();
        request.validate().unwrap();
        let base = root.canonicalize().unwrap();
        let engine = request.engine().unwrap();
        assert_eq!(engine.start_scale(), 1, "no ladder: the last scale");
        let section = engine.workloads.clone().unwrap();
        assert_eq!(section.names(), ["tpch", "sec", "anyschema", "old"]);
        assert_eq!(section.seed, Some(Seed::Run { version: SeedVersion { run: base.join("ce/run"), version: "v004".into() }, workload: None }));
        assert_eq!(section.members[2].seed, Some(Seed::Source { source: base.join("exported/engine") }));
        assert_eq!(json!(request)["engine"]["workloads"]["members"][0]["seed"], json!({"run":base.join("s2/run"),"version":"v001","workload":"sec"}), "a seed keeps its JSON form");
        let set = request.workload_set().unwrap();
        assert_eq!(set.form, WorkloadForm::Workloads);
        assert_eq!(set.names(), ["tpch", "sec", "anyschema", "old"]);
        assert_eq!(set.members.iter().map(|m| m.role).collect::<Vec<_>>(), [MemberRole::Counted, MemberRole::Counted, MemberRole::Check, MemberRole::Kept]);
        assert!(set.members[0].path.is_none() && set.members[0].seed == section.seed && set.seed == section.seed);
        assert_eq!(set.member("sec").unwrap().seed, Some(Seed::Run { version: SeedVersion { run: base.join("s2/run"), version: "v001".into() }, workload: Some("sec".into()) }));
        assert!(set.member("anyschema").unwrap().request.engine().unwrap().scales[0].targets.as_os_str().is_empty(), "a check member's targets may be absent");
        assert!(json!(set.member("anyschema").unwrap().request)["engine"]["scales"][0].get("targets").is_none(), "and stay absent");
        // The one-engine rule: absent, false and not serialized; set, it reads back and serializes.
        assert!(!engine.requires_one_engine() && json!(request)["engine"]["workloads"].get("require_one_engine").is_none(), "absent: the JSON identity is kept");
        let mut one = run.clone();
        one["engine"]["workloads"]["require_one_engine"] = json!(true);
        let one = WorkloadRequest::read(&write("run-one.json", &one)).unwrap();
        one.validate().unwrap();
        assert!(one.engine().unwrap().requires_one_engine() && json!(one)["engine"]["workloads"]["require_one_engine"] == true);

        // The section's own rules.
        let invalid = |edit: &dyn Fn(&mut Value)| {
            let mut value = run.clone();
            edit(&mut value);
            serde_json::from_value::<WorkloadRequest>(value).unwrap().validate().unwrap_err().to_string()
        };
        assert!(invalid(&|v| v["engine"]["workloads"]["members"][1]["name"] = json!("sec")).contains("given twice"));
        assert!(invalid(&|v| v["engine"]["workloads"]["members"][1]["name"] = json!("default")).contains("default module"));
        assert!(invalid(&|v| v["engine"]["workloads"]["name"] = json!("TPC-H")).contains(EngineStage::NAME_RULE));
        assert!(invalid(&|v| v["engine"]["workloads"]["seed"]["version"] = json!("../v004")).contains("engine.workloads.seed.version"));
        assert!(invalid(&|v| v["engine"]["workloads"]["members"][0]["seed"]["workload"] = json!("SEC")).contains("seed.workload"));
        assert!(invalid(&|v| v["engine"]["seed_version"] = json!({"run":"r","version":"v1"})).contains("excludes engine.stage and engine.seed_version"));
        assert!(invalid(&|v| { v["engine"]["scales"][0].as_object_mut().unwrap().remove("targets"); }).contains("targets names the saved baselines"));
        let decoded = |seed: Value| serde_json::from_value::<WorkloadRequest>({ let mut v = run.clone(); v["engine"]["workloads"]["seed"] = seed; v }).map(drop).unwrap_err().to_string();
        assert!(decoded(json!({"run":"r","version":"v1","source":"s"})).contains("a seed is"));
        assert!(decoded(json!({"version":"v1"})).contains("a seed is"));
        assert!(serde_json::from_value::<WorkloadRequest>({ let mut v = run.clone(); v["engine"]["workloads"]["guard"] = json!(0.1); v }).is_err(), "no other field (no guard)");
        assert!(serde_json::from_value::<WorkloadRequest>({ let mut v = run.clone(); v["engine"]["workloads"]["members"][0]["role"] = json!("goal"); v }).is_err(), "roles are counted, check, kept");

        // The members' requests.
        let refused = |name: &str, role: &str, edit: &dyn Fn(&mut Value), words: &str| {
            let mut value = member.clone();
            edit(&mut value);
            write(&format!("members/{name}.json"), &value);
            let mut run_value = run.clone();
            run_value["engine"]["workloads"]["members"][0]["request"] = json!(format!("members/{name}.json"));
            run_value["engine"]["workloads"]["members"][0]["role"] = json!(role);
            let request = WorkloadRequest::read(&write(&format!("run-{name}.json"), &run_value)).unwrap();
            request.validate().unwrap();
            let error = request.workload_set().unwrap_err().to_string();
            assert!(error.contains(words) && error.contains("workloads.members[sec]"), "{name}: {words}: {error}");
        };
        refused("threads", "counted", &|v| v["hardware"]["threads"] = json!([1, 64]), "hardware.threads differs");
        refused("branches", "counted", &|v| v["engine"]["branches"] = json!(2), "engine.branches differs");
        refused("library", "counted", &|v| v["library"] = json!("../library-tpch"), "another workload's");
        refused("output", "kept", &|v| v["output_home"] = json!("out"), "no output_home");
        refused("nested", "counted", &|v| v["engine"]["workloads"] = json!({"name":"x","members":[]}), "not itself a run of several workloads");
        refused("seeded", "counted", &|v| v["engine"]["seed_version"] = json!({"run":"r","version":"v1"}), "names no engine.seed_version");
        refused("untargeted", "counted", &|v| { v["engine"]["scales"][0].as_object_mut().unwrap().remove("targets"); }, "targets names the saved baselines");
        std::fs::remove_dir_all(&root).unwrap();
    }

    /// The workload set of every request form: a run of one workload is one counted member `main`
    /// (seeded by `engine.seed_version` when it is a continued run), a stage run the goal (no seed of its own) and its
    /// kept workloads (seeded by the stage seed), the primary seed the stage seed.
    #[test]
    fn every_request_form_has_a_workload_set() {
        let root = crate::controller::test_support::scratch_root("request-workload-set");
        records::create_dir(&root).unwrap();
        let locks = root.join("l").display().to_string();
        let one: WorkloadRequest = serde_json::from_value(general_request("library", json!([1, 32, 64]), &locks)).unwrap();
        let set = one.workload_set().unwrap();
        assert_eq!((set.form, set.names(), set.seed.is_none(), set.members[0].role), (WorkloadForm::One, vec![ONE_WORKLOAD_NAME.to_string()], true, MemberRole::Counted));
        let mut continued = general_request("library", json!([1, 32, 64]), &locks);
        continued["engine"]["seed_version"] = json!({"run":"run2","version":"v016"});
        let continued: WorkloadRequest = serde_json::from_value(continued).unwrap();
        let seed = Seed::Run { version: SeedVersion { run: "run2".into(), version: "v016".into() }, workload: None };
        let set = continued.workload_set().unwrap();
        assert_eq!((set.seed.clone(), set.members[0].seed.clone()), (Some(seed.clone()), Some(seed)));
        let kept = general_request("../library-tpch", json!([1, 32, 64]), &locks);
        std::fs::create_dir_all(root.join("kept")).unwrap();
        std::fs::write(root.join("kept/tpch.json"), serde_json::to_vec_pretty(&kept).unwrap()).unwrap();
        let mut stage = general_request("library-sec", json!([1, 32, 64]), &locks);
        stage["engine"]["stage"] = json!({"workload":"sec","seed_version":{"run":"run2","version":"v016"},"kept_workloads":[{"name":"tpch","request":"kept/tpch.json"}]});
        std::fs::write(root.join("stage.json"), serde_json::to_vec_pretty(&stage).unwrap()).unwrap();
        let stage = WorkloadRequest::read(&root.join("stage.json")).unwrap();
        let set = stage.workload_set().unwrap();
        let stage_seed = Seed::Run { version: SeedVersion { run: root.canonicalize().unwrap().join("run2"), version: "v016".into() }, workload: None };
        assert_eq!((set.form, set.names()), (WorkloadForm::Stage, vec!["sec".to_string(), "tpch".to_string()]));
        assert_eq!((set.members[0].seed.clone(), set.members[1].seed.clone(), set.members[1].role), (None, Some(stage_seed.clone()), MemberRole::Kept));
        assert_eq!(set.seed, Some(stage_seed));
        std::fs::remove_dir_all(&root).unwrap();
    }

    /// A general-line request file (`GENDB_GENERAL_REQUEST`, read only; a live run's request) parses with
    /// this build, keeps every field it has and adds none (no `engine.stage`), and re-serializes byte for byte as the
    /// run recorded it (`GENDB_RECORDED_REQUEST`, the run's `request.json`), up to the budget raises the run recorded
    /// separately (`limits.max_cost_usd` is compared with the recorded request's).
    #[test]
    #[ignore = "reads the general-line request named by GENDB_GENERAL_REQUEST and the recorded request named by GENDB_RECORDED_REQUEST"]
    fn general_request_reserializes_byte_for_byte() {
        let path = PathBuf::from(std::env::var("GENDB_GENERAL_REQUEST").expect("GENDB_GENERAL_REQUEST"));
        let request = WorkloadRequest::read(&path).unwrap();
        request.validate().unwrap();
        assert!(request.engine().unwrap().stage.is_none());
        let original: Value = serde_json::from_slice(&std::fs::read(&path).unwrap()).unwrap();
        let mut reserialized = serde_json::to_value(&request).unwrap();
        assert_eq!(reserialized, original, "every field of the request is kept, nothing added");
        let recorded = std::fs::read(std::env::var("GENDB_RECORDED_REQUEST").expect("GENDB_RECORDED_REQUEST")).unwrap();
        let recorded_value: Value = serde_json::from_slice(&recorded).unwrap();
        reserialized["engine"]["limits"]["max_cost_usd"] = recorded_value["engine"]["limits"]["max_cost_usd"].clone();
        assert_eq!(serde_json::to_vec_pretty(&reserialized).unwrap(), recorded, "the run's recorded request.json, byte for byte");
        println!("{}: {} bytes re-serialized equal to the recorded request (budget {} recorded, {} requested)", path.display(), recorded.len(),
            recorded_value["engine"]["limits"]["max_cost_usd"], original["engine"]["limits"]["max_cost_usd"]);
    }

    /// The general-line requests of earlier runs (read only) parse with this build, keep every field
    /// they have and add none (no `engine.workloads`), re-serialize byte for byte as each run recorded its `request.json`
    /// (up to the budget raises each run recorded separately), and read as one workload set of their form (a stage
    /// run's kept requests included). `GENDB_RECORDED_REQUESTS` lists `<request file>=<recorded request.json>` pairs
    /// separated by `;` (for example a general-line run's, a continued run's and a stage run's).
    #[test]
    #[ignore = "reads the requests and recorded requests named by GENDB_RECORDED_REQUESTS"]
    fn recorded_requests_reserialize_byte_for_byte() {
        let pairs = std::env::var("GENDB_RECORDED_REQUESTS").expect("GENDB_RECORDED_REQUESTS");
        for pair in pairs.split(';').filter(|p| !p.trim().is_empty()) {
            let (path, recorded_path) = pair.split_once('=').expect("<request>=<recorded request.json>");
            let request = WorkloadRequest::read(Path::new(path)).unwrap();
            request.validate().unwrap();
            let engine = request.engine().unwrap();
            assert!(engine.workloads.is_none(), "{path}: no engine.workloads");
            let original: Value = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
            let mut reserialized = serde_json::to_value(&request).unwrap();
            assert_eq!(reserialized, original, "{path}: every field of the request is kept, nothing added");
            let recorded = std::fs::read(recorded_path).unwrap();
            let recorded_value: Value = serde_json::from_slice(&recorded).unwrap();
            reserialized["engine"]["limits"]["max_cost_usd"] = recorded_value["engine"]["limits"]["max_cost_usd"].clone();
            assert_eq!(serde_json::to_vec_pretty(&reserialized).unwrap(), recorded, "{path}: the run's recorded request.json, byte for byte");
            let set = request.workload_set().unwrap();
            let expected = if engine.stage.is_some() { WorkloadForm::Stage } else { WorkloadForm::One };
            assert_eq!(set.form, expected, "{path}");
            for member in set.members.iter().filter_map(|m| m.path.as_ref().map(|p| (p, &m.request))) {
                let kept: Value = serde_json::from_slice(&std::fs::read(member.0).unwrap()).unwrap();
                assert_eq!(serde_json::to_value(member.1).unwrap(), kept, "{}: the kept request keeps every field", member.0.display());
            }
            println!("{path}: {} bytes re-serialized equal to {recorded_path} (budget {} recorded, {} requested); workload set {:?} {:?}", recorded.len(),
                recorded_value["engine"]["limits"]["max_cost_usd"], original["engine"]["limits"]["max_cost_usd"], set.form, set.names());
        }
    }

    /// On a copy of a paused schema-engine run's request (read only; the paths come from
    /// `GENDB_PAUSED_REQUEST` and `GENDB_PAUSED_RECORDED_REQUEST`, a copy of the run's recorded `request.json`): it
    /// parses and validates, keeps every field it has, and re-serializes byte for byte as the run recorded it, so a
    /// relaunch presents the same request (`lifecycle::record_request`).
    #[test]
    #[ignore = "reads a copy of a paused run's request named by GENDB_PAUSED_REQUEST and GENDB_PAUSED_RECORDED_REQUEST"]
    fn paused_engine_request_reserializes_byte_identically() {
        let request_path = PathBuf::from(std::env::var("GENDB_PAUSED_REQUEST").expect("GENDB_PAUSED_REQUEST"));
        let recorded_path = PathBuf::from(std::env::var("GENDB_PAUSED_RECORDED_REQUEST").expect("GENDB_PAUSED_RECORDED_REQUEST"));
        let request = WorkloadRequest::read(&request_path).unwrap();
        request.validate().unwrap();
        let engine = request.engine().unwrap();
        assert!(!engine.is_general() && engine.line.is_none() && engine.scales.is_empty());
        // Every field of the request file is kept and nothing is added; the only difference is a field the format
        // omits when empty (`storage_policy.eligible_storages: []`), as when the run first recorded it.
        let mut original: Value = serde_json::from_slice(&std::fs::read(&request_path).unwrap()).unwrap();
        if original.pointer("/storage_policy/eligible_storages") == Some(&json!([])) {
            original["storage_policy"].as_object_mut().unwrap().remove("eligible_storages");
        }
        let reserialized = serde_json::to_value(&request).unwrap();
        assert_eq!(reserialized, original, "every field of the request is kept, nothing added");
        let bytes = serde_json::to_vec_pretty(&reserialized).unwrap();
        assert_eq!(bytes, std::fs::read(&recorded_path).unwrap(), "the run's recorded request.json, byte for byte");
    }

    /// A relaunch of a live general-line run with a changed request: the request at
    /// `GENDB_RELAUNCH_REQUEST` validates, and GenDB accepts it against a copy of the run's recorded `request.json`
    /// (`GENDB_RECORDED_REQUEST`, read only; the comparison runs in a scratch copy), exactly as `gendb engine
    /// synthesize` does when it is relaunched (`lifecycle::record_request`).
    #[test]
    #[ignore = "reads the relaunch request and a copy of the run's recorded request named by GENDB_RELAUNCH_REQUEST and GENDB_RECORDED_REQUEST"]
    fn a_relaunch_request_matches_the_recorded_request() {
        let request = WorkloadRequest::read(Path::new(&std::env::var("GENDB_RELAUNCH_REQUEST").expect("GENDB_RELAUNCH_REQUEST"))).unwrap();
        request.validate().unwrap();
        let engine = request.engine().unwrap();
        assert!(engine.is_general() && engine.branches == Some(1) && engine.pause_after_session.is_never());
        let root = crate::controller::test_support::scratch_root("relaunch-request");
        records::create_dir(&root).unwrap();
        std::fs::copy(std::env::var("GENDB_RECORDED_REQUEST").expect("GENDB_RECORDED_REQUEST"), root.join("request.json")).unwrap();
        let existed = crate::controller::workload_run::lifecycle::record_request(&root, &serde_json::to_value(&request).unwrap()).unwrap();
        assert!(existed, "the run's recorded request accepts the relaunch request");
        println!("relaunch request accepted: line general, branches {:?}, pause_after_session {:?}, budget {}", engine.branches, engine.pause_after_session, engine.limits.max_cost_usd.decimal());
        std::fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn storage_policy_is_optional_and_physical_only_is_explicit() {
        let policy = |value: Value| serde_json::from_value::<StoredDataPolicy>(value);
        assert!(StoredDataPolicy::default().is_unrestricted());
        let physical = policy(json!({"kind":"physical_only","eligible_storages":[{"package":"07".repeat(32),"review":"builder and readers reviewed"}]})).unwrap();
        assert_eq!(physical.kind(), "physical_only");
        assert!(physical.validate().is_ok());
        assert!(policy(json!({"kind":"no_precomputation"})).is_err());
    }
}
