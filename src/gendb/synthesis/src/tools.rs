//! The authors' local tools (`gendb_local` MCP server), one tool set for both roles:
//!
//! - storage tools over a `verus-storage.json`: `storage_check`, `storage_verify`, `storage_compile`, `storage_build`,
//!   `storage_register`;
//! - query tools over a `verus-query.json`: `check`, `verify`, `compile`, `trial`, `profile`;
//! - for the schema-engine author ([`AuthorRole::Engine`]) the same five names are the engine tools over a
//!   `verus-engine.json` (`engine::role`): `trial` and `profile` run training templates (`templates`, `binding`) or the
//!   author's own statements (`sql`) instead of one statement's bindings. In a run of several workloads
//!   (`engine::stage`: a stage run, or `engine.workloads`) every tool also takes `workload` (default: the goal, the
//!   primary workload): which workload's crate, data, library and saved answers the job uses
//!   ([`LocalToolContext::workloads`]; a check workload's too, whose trials compare answers and have no baselines).
//!
//! A workload storage author uses the query tools for diagnostic query crates of any workload statement (named by
//! `statement`); a query author uses the storage tools to create and register storages in its own session. Both run
//! the same code on their retained owner thread (`tools::bench`).
//!
//! Protocol, end to end:
//! 1. The provider starts `gendb <mcp words> <workspace>/local-tool.json <call>/local-jobs` per author call
//!    (`providers::LocalToolServer`); [`mcp::serve`] answers JSON-RPC on stdio and does no compute.
//! 2. `tools/call` arguments are parsed as [`LocalJobArguments`] (unknown fields refused on the client, recorded as
//!    `refused-NNNN.json`) and forwarded over the session socket to the retained role
//!    (`controller::session::forward_job`).
//! 3. The role runs the job on its owner thread, writing `<call>/local-jobs/<NNNN>-<job_name>/{request.json, frozen/,
//!    verus/, ..., result.json}` and returning the full job record; the client returns its compact form
//!    ([`compact_job_record`]).
//!
//! Trial and profile build the query crate with the whole-crate verify-and-compile run by default; with
//! `verification: "not_run"` they build it with `rust_verify --no-verify` and label the result `diagnostic_unverified`
//! (same freeze, storages, assets, binding, workers, reference and tiny cases; storages stay verified whole).
//!
//! Every job is a diagnostic: never a submission, never an official measurement (a storage registered by
//! `storage_register` is an admitted library record, not a measurement). Jobs of one session run one at a time on the
//! role's owner thread; Verus runs and asset builds hold the shared host activity lease only for their own duration,
//! so the author's own Bash commands are never refused.
//!
//! One more tool, [`WAIT_TOOL`], runs no job: the thin client answers it from the job calls it received and the call's
//! job records ([`mcp`]), so an author (or a sub-agent) waits for a job's answer without a Bash command, which would
//! hold the shared activity lease that a timed job needs alone to start.

pub mod bench;
pub mod mcp;

use crate::controller::session::LocalSessionEndpoint;
use crate::query::evaluation::DEFAULT_TRIAL_HOT_CALLS;
use gendb_verification::admission::AdmissionError;
use gendb_verification::admission::execution::CHILD_TIMEOUT_SECONDS;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::path::PathBuf;

/// MCP server name; the provider exposes tools as `mcp__gendb_local__<tool>`.
pub const SERVER_NAME: &str = "gendb_local";
/// Format of `local-tool.json` (3: storage and query tools of both roles; 2 was the v3 query tools only).
pub const CONTEXT_FORMAT: u32 = 3;
/// File name of the tool context in the author workspace.
pub const CONTEXT_FILE: &str = "local-tool.json";
/// What a trial/profile child timeout covers (tool schema and `tools.json`).
pub const CHILD_TIMEOUT_MEANING: &str = "The bound runs from the child's start: it covers the warm call (whose first touches may fault storage pages in from the device) and every hot call of the child, not the compile or the wait for the host timing lease, which come before it. Reaching it returns a censored execution_failure with no result or timing; it does not by itself show that hot calls are slow";

/// The tool that waits for a local job of the author call (answered by the thin client, `mcp`; it runs no job).
pub const WAIT_TOOL: &str = "wait";
/// The longest one `wait` call waits, in seconds, and its default: below Claude Code's 1800 s silence limit for a stdio
/// MCP call, so a wait answers in time even if the client asked for no progress notifications.
pub const MAX_WAIT_SECONDS: u64 = 1500;
/// What `wait` does (its MCP description and its `tools.json` entry).
pub const WAIT_SUMMARY: &str = "Wait for a local job of this author call, named by its job_name (the latest job of that name), holding no host lock: returns the job's answer, as its own tool call returns it, as soon as the job ends; or, after wait_seconds, its status: queued (behind earlier jobs of this call, which run one at a time; jobs_ahead) or running (a trial or profile includes its wait for the host timing lease). A job keeps running when its own tool call returned early (for example after a client timeout); wait still reports it. Use it instead of sleeping or polling in Bash: a Bash call holds the host's shared activity lock until it ends, and a timed job needs that lock alone to start";

/// The arguments of one `wait` call.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WaitArguments {
    /// The `job_name` of a job of this author call; the latest job of that name is meant.
    pub job_name: String,
    /// The most this call waits, `0..=MAX_WAIT_SECONDS` (0: the status at once); absent: [`MAX_WAIT_SECONDS`].
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub wait_seconds: Option<u64>,
}

impl WaitArguments {
    /// The checked wait bound; every violation is `missing_input` (fix the request).
    pub fn bound(&self) -> Result<std::time::Duration, AdmissionError> {
        validate_job_name(&self.job_name)?;
        match self.wait_seconds.unwrap_or(MAX_WAIT_SECONDS) {
            seconds @ 0..=MAX_WAIT_SECONDS => Ok(std::time::Duration::from_secs(seconds)),
            _ => Err(AdmissionError::missing_input(format!("wait_seconds is in 0..={MAX_WAIT_SECONDS}"))),
        }
    }
}

/// One local tool.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ToolAction {
    /// Freeze a storage snapshot: manifest, author file set, source rules, framework files; statement coverage; no Verus.
    StorageCheck,
    /// `storage_check` + one whole-crate verification of the storage crate (or a module-scoped diagnostic run).
    StorageVerify,
    /// `storage_check` + the one whole-crate verify-and-compile run of the storage crate.
    StorageCompile,
    /// `storage_compile` (cached) + the checked build recorded and its asset built once over the current capture by the
    /// stored library (cached) + builds over the workload's tiny inputs when the validation policy runs them; sizes and
    /// build time.
    StorageBuild,
    /// `storage_build` (cached) + admission of the storage package (no second build); the asset is reopened from the
    /// library.
    StorageRegister,
    /// Freeze a query snapshot over its declared storage uses: manifest, coverage, composition, source rules; no Verus.
    Check,
    /// `check` + one whole-crate verification (or a module-scoped diagnostic run).
    Verify,
    /// `check` + the one whole-crate verify-and-compile run used for submissions.
    Compile,
    /// `compile` (cached) + query over the storage assets (the benchmark matrix by default): 1 warm + `hot_calls` hot
    /// calls per cell (default 1), tiny cases when the validation policy runs them.
    Trial,
    /// `trial` with 1 warm + 1 measured call and per-call CPU/dispatch detail.
    Profile,
    /// Re-read the library now: the admitted storage catalog (newly admitted versions included) and the storage budget.
    Catalog,
}

impl ToolAction {
    pub const ALL: [ToolAction; 11] = [
        ToolAction::StorageCheck,
        ToolAction::StorageVerify,
        ToolAction::StorageCompile,
        ToolAction::StorageBuild,
        ToolAction::StorageRegister,
        ToolAction::Check,
        ToolAction::Verify,
        ToolAction::Compile,
        ToolAction::Trial,
        ToolAction::Profile,
        ToolAction::Catalog,
    ];

    pub fn name(self) -> &'static str {
        match self {
            ToolAction::StorageCheck => "storage_check",
            ToolAction::StorageVerify => "storage_verify",
            ToolAction::StorageCompile => "storage_compile",
            ToolAction::StorageBuild => "storage_build",
            ToolAction::StorageRegister => "storage_register",
            ToolAction::Check => "check",
            ToolAction::Verify => "verify",
            ToolAction::Compile => "compile",
            ToolAction::Trial => "trial",
            ToolAction::Profile => "profile",
            ToolAction::Catalog => "catalog",
        }
    }

    pub fn parse(name: &str) -> Result<ToolAction, AdmissionError> {
        Self::ALL.into_iter().find(|a| a.name() == name).ok_or_else(|| {
            AdmissionError::missing_input(format!("unsupported local job action {name}; the tools are {:?}", Self::ALL.map(ToolAction::name)))
        })
    }

    /// Storage tools take a `storage` manifest; query tools a `candidate` manifest.
    pub fn is_storage(self) -> bool {
        matches!(self, ToolAction::StorageCheck | ToolAction::StorageVerify | ToolAction::StorageCompile | ToolAction::StorageBuild | ToolAction::StorageRegister)
    }

    /// Trial and profile run a compiled query library on data at one worker count.
    pub fn is_timed(self) -> bool {
        matches!(self, ToolAction::Trial | ToolAction::Profile)
    }

    /// The actions that run query children with an author-bounded timeout (asset builds run under the framework's
    /// own bound: an asset is built once and reused).
    fn takes_timeout(self) -> bool {
        self.is_timed()
    }

    /// Trial, profile and storage_build take `verification` (`not_run`: an unverified diagnostic build).
    pub fn takes_verification(self) -> bool {
        self.is_timed() || self == ToolAction::StorageBuild
    }

    fn takes_modules(self) -> bool {
        matches!(self, ToolAction::Verify | ToolAction::StorageVerify)
    }
}

/// The MCP tool names the provider must offer (`context.local_tools.required_tools`).
pub fn required_tools() -> Vec<String> {
    required_tools_of(false)
}

/// The tools an author session is offered: every tool, or under `storage_policy` `fixed_flat` (`fixed_flat`) every tool
/// but the storage tools (no storage is designed, built or registered by an author there).
pub fn offered_actions(fixed_flat: bool) -> Vec<ToolAction> {
    ToolAction::ALL.into_iter().filter(|a| !(fixed_flat && a.is_storage())).collect()
}

/// The MCP tool names of [`offered_actions`], then [`WAIT_TOOL`] (offered to every role).
pub fn required_tools_of(fixed_flat: bool) -> Vec<String> {
    offered_actions(fixed_flat).iter().map(|a| a.name()).chain([WAIT_TOOL]).map(|name| format!("mcp__{SERVER_NAME}__{name}")).collect()
}

/// Which role's session a tool context serves.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum AuthorRole {
    /// The workload storage author: query tools name any workload statement (diagnostic query crates).
    WorkloadStorage,
    /// A query author: query tools run the session's one statement.
    Query,
    /// The schema-engine author: the query tool names run the engine crate (`engine::role`) over the training templates
    /// or ad hoc statements.
    Engine,
}

/// How trial and profile build the query crate they run. The default is the whole-crate verify-and-compile run;
/// `NotRun` compiles the same frozen crate with `rust_verify --no-verify` (every other step unchanged) and labels the
/// result `diagnostic_unverified`: never a submission, proof, official measurement or early-stop input.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TrialVerification {
    #[default]
    WholeCrate,
    NotRun,
}

impl TrialVerification {
    pub const ALL: [TrialVerification; 2] = [TrialVerification::WholeCrate, TrialVerification::NotRun];

    pub fn name(self) -> &'static str {
        match self {
            TrialVerification::WholeCrate => "whole_crate",
            TrialVerification::NotRun => "not_run",
        }
    }
}

/// A statement the query tools can run.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ToolStatement {
    /// The `statement` argument value.
    pub index: usize,
    pub statement_key: String,
    pub sql: String,
    /// The statement's request name (an engine role's training template, its `templates` argument value).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
}

/// `local-tool.json`: what the MCP thin client needs to list the tools and reach the retained role.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LocalToolContext {
    pub format_version: u32,
    pub role: AuthorRole,
    /// The canonical author workspace (manifest paths are resolved inside it).
    pub author_workspace: PathBuf,
    pub session_service: LocalSessionEndpoint,
    /// The configured worker counts (trial/profile `workers`).
    pub worker_counts: Vec<usize>,
    /// The statements the query tools run (one for a query author).
    pub statements: Vec<ToolStatement>,
    /// The author contract index, named in tool descriptions.
    pub author_contract: PathBuf,
    /// `storage_policy` `fixed_flat`: the storage tools are not listed (and the role refuses them). Absent: false.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub fixed_flat: bool,
    /// The engine role's visible binding names (its `binding` argument; the first is the timing binding). Absent: none.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub engine_bindings: Vec<String>,
    /// A run of several workloads' workloads, the goal (primary) first (the tools' `workload` argument; `templates` and
    /// `binding` are the named workload's). Absent: a run with one workload, whose tools take no `workload`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub workloads: Vec<ToolWorkload>,
}

/// One workload of a stage run as its tools offer it: its name, training templates and visible bindings (the timing
/// binding first); in a run of several workloads also its role (`counted`, `check` or `kept`).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ToolWorkload {
    pub name: String,
    pub templates: Vec<String>,
    pub bindings: Vec<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub role: Option<String>,
}

/// The arguments of one tool call.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LocalJobArguments {
    /// Query tools: `verus-query.json` inside the workspace (relative or absolute).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub candidate: Option<PathBuf>,
    /// Storage tools: `verus-storage.json` inside the workspace (relative or absolute).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub storage: Option<PathBuf>,
    /// 1..64 portable identifier bytes; names the job directory.
    pub job_name: String,
    /// Query tools of the workload role: the statement index (`ToolStatement::index`); default the only statement.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub statement: Option<usize>,
    /// Trial/profile only: one of the configured worker counts.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub workers: Option<usize>,
    /// Verify/storage_verify only: crate module paths of a module-scoped diagnostic run.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub modules: Vec<String>,
    /// Trial/profile only: bound (seconds) of each query child process of the job ([`CHILD_TIMEOUT_MEANING`]).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub timeout_seconds: Option<u64>,
    /// Trial only: hot calls per cell after the warm call; absent = `DEFAULT_TRIAL_HOT_CALLS` (1).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub hot_calls: Option<u32>,
    /// Trial/profile only: argument texts of the free statement parameters (slot order), one of the admission
    /// bindings; default the first.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub arguments: Option<Vec<String>>,
    /// Trial/profile only: how the query crate is built; absent = [`TrialVerification::WholeCrate`].
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub verification: Option<TrialVerification>,
    /// Engine trial/profile only: the training templates to run (names); absent: every template (trial).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub templates: Vec<String>,
    /// Engine trial/profile only: the visible binding the templates run at; absent: the timing binding.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub binding: Option<String>,
    /// Engine trial/profile only: the author's own SQL statements over the schema, `;`-free, one per entry, instead of
    /// templates (no saved answers: only status and rows are reported).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub sql: Vec<String>,
    /// A run of several workloads' tools only: the workload whose crate, data, library and saved answers the job uses;
    /// absent: the goal (primary) workload. The engine role checks the name (`engine::role::job_workload`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub workload: Option<String>,
}

impl LocalJobArguments {
    /// The build mode of this job (the default whole-crate run unless the author asked for `not_run`).
    pub fn verification(&self) -> TrialVerification {
        self.verification.unwrap_or_default()
    }

    /// Whether an engine-tool argument (`templates`, `binding`, `sql`) is given.
    pub fn engine_arguments_given(&self) -> bool {
        !self.templates.is_empty() || self.binding.is_some() || !self.sql.is_empty()
    }
}

impl LocalJobArguments {
    /// Which arguments the action accepts; every violation is `missing_input` (fix the request).
    pub fn check(&self, action: ToolAction) -> Result<(), AdmissionError> {
        validate_job_name(&self.job_name)?;
        let refuse = |detail: &str| Err(AdmissionError::missing_input(detail));
        if action == ToolAction::Catalog {
            let only_name = LocalJobArguments { job_name: self.job_name.clone(), candidate: None, storage: None, statement: None, workers: None,
                modules: vec![], timeout_seconds: None, hot_calls: None, arguments: None, verification: None, templates: vec![], binding: None, sql: vec![],
                workload: self.workload.clone() };
            return if *self == only_name { Ok(()) } else { refuse("catalog takes only job_name (and workload in a stage run)") };
        }
        if action.is_storage() {
            if self.storage.is_none() || self.candidate.is_some() || self.statement.is_some() {
                return refuse("storage tools take a storage manifest (storage), not candidate or statement");
            }
        } else if self.candidate.is_none() || self.storage.is_some() {
            return refuse("query tools take a query manifest (candidate), not storage");
        }
        let timed = action.is_timed();
        // A trial without workers times every configured worker count; a profile times one cell.
        if (action == ToolAction::Profile && self.workers.is_none()) || (!timed && self.workers.is_some()) {
            return refuse("workers is required for profile and optional for trial (absent: every configured worker count)");
        }
        if !self.modules.is_empty() && !action.takes_modules() {
            return refuse("modules is a verify/storage_verify argument");
        }
        if self.arguments.is_some() && !timed {
            return refuse("arguments is a trial/profile argument");
        }
        if self.engine_arguments_given() && !timed {
            return refuse("templates, binding and sql are trial/profile arguments of the engine tools");
        }
        if self.verification.is_some() && !action.takes_verification() {
            return refuse("verification is a trial/profile/storage_build argument");
        }
        if self.hot_calls.is_some_and(|n| action != ToolAction::Trial || n == 0) {
            return refuse("hot_calls is a trial argument of at least 1");
        }
        if self.timeout_seconds.is_some_and(|t| !action.takes_timeout() || t == 0 || t > CHILD_TIMEOUT_SECONDS) {
            return Err(AdmissionError::missing_input(format!("timeout_seconds is a trial/profile argument in 1..={CHILD_TIMEOUT_SECONDS}")));
        }
        Ok(())
    }
}

fn validate_job_name(name: &str) -> Result<(), AdmissionError> {
    let portable = name.bytes().enumerate().all(|(i, b)| b.is_ascii_alphanumeric() || (i > 0 && matches!(b, b'.' | b'_' | b'-')));
    if name.is_empty() || name.len() > 64 || !portable {
        return Err(AdmissionError::missing_input("job_name must be 1..64 portable identifier bytes"));
    }
    Ok(())
}

/// JSON input schema of one tool.
fn input_schema(action: ToolAction, context: &LocalToolContext) -> Value {
    let mut required = vec![json!("job_name")];
    let mut properties = json!({"job_name":{"type":"string","pattern":"^[A-Za-z0-9][A-Za-z0-9._-]{0,63}$"}});
    let staged = context.role == AuthorRole::Engine && !context.workloads.is_empty();
    if staged {
        properties["workload"] = workload_property(context);
    }
    if action == ToolAction::Catalog {
        return json!({"type":"object","additionalProperties":false,"required":required,"properties":properties});
    }
    let manifest = if action.is_storage() { "storage" } else { "candidate" };
    required.insert(0, json!(manifest));
    properties[manifest] = json!({"type":"string","minLength":1});
    let engine = context.role == AuthorRole::Engine;
    if engine && !action.is_storage() {
        properties[manifest]["description"] = json!("your verus-engine.json inside the workspace");
    }
    let timed = action.is_timed();
    if action == ToolAction::Profile {
        required.push(json!("workers"));
    }
    if timed {
        properties["workers"] = json!({"type":"integer","enum":context.worker_counts,
            "description":"profile: required, the one worker count. trial: optional; absent times every configured worker count"});
        if engine {
            // A stage run: every workload's templates and bindings (each job's are its workload's).
            let (names, bindings): (Vec<&str>, Vec<&str>) = if staged {
                (union(context.workloads.iter().flat_map(|w| w.templates.iter().map(String::as_str))), union(context.workloads.iter().flat_map(|w| w.bindings.iter().map(String::as_str))))
            } else {
                (context.statements.iter().filter_map(|s| s.name.as_deref()).collect(), context.engine_bindings.iter().map(String::as_str).collect())
            };
            let of_workload = if staged { " (of the job's workload)" } else { "" };
            properties["templates"] = json!({"type":"array","items":{"type":"string","enum":names},
                "description":format!("optional: the training templates to run{of_workload}. trial: absent runs every template (the training matrix); profile: exactly one template or one sql statement")});
            properties["binding"] = json!({"type":"string","enum":bindings,
                "description":format!("optional: the visible binding the templates run at{of_workload}; absent: the timing binding (the first)")});
            properties["sql"] = json!({"type":"array","items":{"type":"string","minLength":1},
                "description":"optional, instead of templates: your own SQL statements over the schema (no parameters), each translated by the frontend and encoded like the templates; no saved answer exists, so only the status, rows and times are reported"});
        } else {
            properties["arguments"] = json!({"type":"array","items":{"type":"string"},
                "description":"optional: argument texts of the free parameters in slot order, equal to one admission binding (contract parameters.json; the user's benchmark bindings come first). trial: absent times every benchmark binding; profile: absent uses the first admission binding"});
        }
        properties["verification"] = json!({"type":"string","enum":TrialVerification::ALL.map(TrialVerification::name),
            "description":"optional, default whole_crate (the verify-and-compile run submissions use). not_run: compile this frozen query crate AND its workspace storages with rust_verify --no-verify (no proof obligation checked; their diagnostic storage builds are reused; admitted storages are used as admitted; freeze, source rules, binding, workers, result comparisons and tiny cases as the validation policy runs them unchanged); the result is labelled diagnostic_unverified / verification_not_run and is never a submission, proof or official measurement"});
    }
    if action == ToolAction::StorageBuild {
        properties["verification"] = json!({"type":"string","enum":TrialVerification::ALL.map(TrialVerification::name),
            "description":"optional, default whole_crate. not_run: an UNVERIFIED diagnostic build: compile the storage crate with rust_verify --no-verify and build its parts once over the current data, apart from every admitted and trial asset (one per storage name in this session; a newer one replaces it); reports stored bytes per part and build time; labelled diagnostic_unverified, never registrable, admissible or submittable, and not counted in the storage budget. Trials with verification not_run read it"});
    }
    if action.takes_modules() {
        properties["modules"] = json!({"type":"array","items":{"type":"string","pattern":"^[A-Za-z_][A-Za-z0-9_]*(::[A-Za-z_][A-Za-z0-9_]*)*$"},
            "description":"optional: verify only these crate modules and their descendants (diagnostic; not valid evidence)"});
    }
    if action == ToolAction::Trial {
        properties["hot_calls"] = json!({"type":"integer","minimum":1,
            "description":format!("optional: hot calls per cell after the warm call; default {DEFAULT_TRIAL_HOT_CALLS} (fast feedback, no spread estimate); ask for more when you need the spread or less noise")});
    }
    if action.takes_timeout() {
        properties["timeout_seconds"] = json!({"type":"integer","minimum":1,"maximum":CHILD_TIMEOUT_SECONDS,
            "description":format!("optional bound of each child process of this job; default {CHILD_TIMEOUT_SECONDS}. {CHILD_TIMEOUT_MEANING}")});
    }
    if !action.is_storage() && context.role == AuthorRole::WorkloadStorage {
        required.push(json!("statement"));
        properties["statement"] = json!({"type":"integer","enum":context.statements.iter().map(|s| s.index).collect::<Vec<_>>(),
            "description":"the workload statement this diagnostic query crate implements (contract workload.json)"});
    }
    json!({"type":"object","additionalProperties":false,"required":required,"properties":properties})
}

/// The `workload` argument of a run of several workloads' tools (every tool; default the goal or primary, the first
/// workload).
fn workload_property(context: &LocalToolContext) -> Value {
    let names: Vec<&str> = context.workloads.iter().map(|w| w.name.as_str()).collect();
    let first = names.first().copied().unwrap_or("-");
    // A run of several workloads names each workload's role; a stage run's description stays as it was.
    let description = if context.workloads.iter().any(|w| w.role.is_some()) {
        let roles: Vec<String> = context.workloads.iter().map(|w| format!("{} ({})", w.name, w.role.as_deref().unwrap_or("-"))).collect();
        format!("optional: the workload whose crate (src/agent/** with its own module workloads/<name>/** or the default module workloads/default/**, and its family instances), data, library and saved answers this job uses: {}; absent: the primary workload {first} (catalog lists the primary's library only; a check workload has no baselines, so its trials report answers and times only)", roles.join(", "))
    } else {
        format!("optional: the workload whose crate (src/agent/** with workloads/<name>/**), data, library and saved answers this job uses; absent: the goal workload {first} (catalog lists the goal's library only)")
    };
    json!({"type":"string","enum":names,"description":description})
}

/// The distinct values of `values`, in first-seen order.
fn union<'a>(values: impl Iterator<Item = &'a str>) -> Vec<&'a str> {
    let mut seen = vec![];
    for value in values {
        if !seen.contains(&value) {
            seen.push(value);
        }
    }
    seen
}

/// The MCP `tools/list` entries.
pub fn tool_list(context: &LocalToolContext) -> Value {
    let contract = context.author_contract.display();
    let description = |action: ToolAction| -> String {
        if context.role == AuthorRole::Engine
            && let Some(text) = engine_tool_description(action)
        {
            return text.to_string();
        }
        match action {
            ToolAction::StorageCheck => format!("Every storage tool result carries storage_budget_now (the budget as it stands, a snapshot, not a reservation). Freeze a snapshot of a storage crate from a verus-storage.json: manifest schema, author file set, source rules over stores/<name>/interface and builder, framework-file comparison; reports which workload statements it covers; no Verus. Refusals carry failure_class; contract: {contract}"),
            ToolAction::StorageVerify => "storage_check + one Verus verification (--no-cheating) of the whole storage crate; diagnostics verbatim. Optional modules verifies only those modules (diagnostic only).".into(),
            ToolAction::StorageCompile => "storage_check + the single whole-crate verify-and-compile run of the storage crate; returns the build identity (argv, verified count, library).".into(),
            ToolAction::StorageBuild => "storage_compile (cached for identical sources) + the checked build recorded in the library and its asset built ONCE over the current prepared data by that stored library (cached; later uses and admission reuse it) + builds over the workload's tiny inputs when the run's validation policy runs them (validation.json); returns parts, stored bytes, canonical bytes of the stored columns, build wall time and whether the capture had to be extended by new columns. verification \"not_run\": an unverified diagnostic build instead (no Verus proof, no library record, never admissible).".into(),
            ToolAction::StorageRegister => "storage_build (cached) + admission of the storage package as a new version of its name (no second build); the asset is reopened from the library; queries can then name it by package id. Registering an admitted package returns its admission.".into(),
            ToolAction::Check => "Freeze a snapshot of a query crate from a verus-query.json over its declared storage uses (admitted package ids or workspace storage manifests): coverage of the statement's demand (storage_does_not_cover_demand), storage composition, source rules, framework files; writes the use-specific framework files into your workspace crate (read-only) so direct rust_verify works; no Verus.".into(),
            ToolAction::Verify => "check + one Verus verification (--no-cheating) of the whole query crate; diagnostics verbatim. Optional modules (e.g. [\"agent\"]) verifies only those modules (diagnostic only).".into(),
            ToolAction::Compile => "check + the single Verus verify-and-compile invocation used for submissions; returns the build identity (argv, verified count, library).".into(),
            ToolAction::Trial => "compile (cached for identical crate content) + the storage assets (admitted asset for the current data, built once if missing; workspace storages via storage_build) + the query over the whole matrix by default (every benchmark binding x configured worker count; workers/arguments narrow it) under the host timing lease: per cell 1 warm + hot_calls hot calls (default 1: one sample, no spread estimate) compared with the SQL's prepared-data reference or, under the validation policy formal_proofs, with the saved answers of other engines where given (validation.json), reported with the user's target, the early-stop bar, median, min, max and met (summary.matrix); plus the generated tiny cases when the validation policy runs them (skipped when identical crate content over the same assets passed them); per storage use aggregate read requests/elements/bytes versus stored bytes and the child's device read bytes; diagnostic only. verification \"not_run\" builds the query crate with --no-verify instead (unproved code; result labelled diagnostic_unverified).".into(),
            ToolAction::Profile => "trial with 1 warm + 1 measured call, per-call dispatch ranges, wall, process user/system CPU and calling-thread CPU; diagnostic only; verification \"not_run\" as for trial.".into(),
            ToolAction::Catalog => format!("Re-read the library now (cheap: records and file sizes, no data read): rewrites your contract's storages.json (every admitted storage version, including those other sessions admitted since your session was prepared; interface copies of new versions under admitted-storages/) and storage-budget.json, and returns the budget (used, left) and the storage list. {}", crate::tools::bench::SHARED_FACTS_MEANING),
        }
    };
    let mut tools: Vec<Value> = offered_actions(context.fixed_flat).iter().map(|a| json!({"name":a.name(),"description":description(*a),"inputSchema":input_schema(*a, context)})).collect();
    tools.push(json!({"name":WAIT_TOOL,"description":format!("{WAIT_SUMMARY}."),
        "inputSchema":{"type":"object","additionalProperties":false,"required":["job_name"],"properties":{
            "job_name":{"type":"string","pattern":"^[A-Za-z0-9][A-Za-z0-9._-]{0,63}$","description":"the job_name of a local job of this author call (the latest job of that name)"},
            "wait_seconds":{"type":"integer","minimum":0,"maximum":MAX_WAIT_SECONDS,
                "description":format!("optional: the most this call waits before it answers the job's status; default and maximum {MAX_WAIT_SECONDS}; 0 answers at once")}}}}));
    json!(tools)
}

/// What the engine tools do (the engine role's `check`, `verify`, `compile`, `trial`, `profile`); `None`: the shared
/// description of a storage tool or `catalog`.
fn engine_tool_description(action: ToolAction) -> Option<&'static str> {
    Some(match action {
        ToolAction::Check => "Freeze a snapshot of the engine crate from a verus-engine.json over its storage uses: manifest, coverage of every column of every table, storage composition, source rules (central scan, no static items, engine rules: template constants, AST fragments and the whole-statement evaluator), framework files; writes the framework files into your workspace crate (read-only) so direct rust_verify works; no Verus.",
        ToolAction::Verify => "check + one Verus verification (--no-cheating) of the whole engine crate; diagnostics verbatim. Optional modules (e.g. [\"agent::plan\"]) verifies only those modules (diagnostic only).",
        ToolAction::Compile => "check + the single Verus verify-and-compile invocation used for submissions; returns the build identity (argv, verified count, library).",
        ToolAction::Trial => "compile (cached for identical crate content; verification \"not_run\" builds it with --no-verify instead, labelled diagnostic_unverified) + the storage assets + the engine called in one fresh child per cell under the host timing lease: by default every training template at the timing binding x every configured worker count (templates, binding, workers narrow it), 1 warm + hot_calls hot calls per cell (default 1), each template answer compared with its saved answers; per cell the median, the faster baseline's time and the ratio, and the totals per worker count when every template ran. With sql: your own statements instead (status, rows and times only). Diagnostic only, never the official measurement.",
        ToolAction::Profile => "one cell (workers, and one template or one sql statement) with 1 warm + 1 measured call: per-call dispatch ranges, wall, process user/system CPU and calling-thread CPU; verification \"not_run\" as for trial.",
        _ => return None,
    })
}

/// Compact MCP answer of a job record: the full record stays in `result_record`.
pub fn compact_job_record(record: &Value) -> Value {
    let mut compact = json!({"format_version":record["format_version"],"job_id":record["job_id"],"action":record["action"],
        "status":record["status"],"failure_class":record["failure_class"],"error":record["error"],"elapsed_ns":record["elapsed_ns"],
        "result_record":record["result_record"],"paths":record["paths"],"diagnostic_only":true,"official_measurement":false});
    if let Some(label) = record.get("verification") {
        compact["verification"] = label.clone();
        compact["diagnostic_unverified"] = record["diagnostic_unverified"].clone();
    }
    let r = &record["result"];
    if record["status"] == "completed" {
        compact["summary"] = json!({"status":r["status"],"verification":r.pointer("/build/record/verification").or(r.get("verification")),
            "workers":r["workers"],"matrix":r.get("matrix"),"crate_version":r.get("crate_version"),"reused":r.get("reused"),"real_data":r.pointer("/real_data/cells"),
            "boundary_cases":r.pointer("/boundary/cases").and_then(Value::as_array).map(Vec::len),
            "storage":r.get("storage"),"coverage":r.get("coverage"),"registration":r.get("registration"),
            "build_reused":r.pointer("/build/reused"),
            "asset":r.get("asset").map(|a| json!({"asset":a["asset"],"built_now":a["built_now"],"storage_bytes":a["storage_bytes"],
                "canonical_column_bytes":a["canonical_column_bytes"],"build_wall_ns":a["build_wall_ns"]})),
            "capture_extension":r.get("capture_extension"),"storage_budget":r.get("storage_budget"),"catalog":r.get("catalog"),
            "storage_budget_now":r.get("storage_budget_now")});
    }
    compact
}

#[cfg(test)]
mod tests {
    use super::*;
    use gendb_verification::admission::FailureClass;

    fn arguments(value: Value) -> LocalJobArguments {
        serde_json::from_value(value).unwrap()
    }

    #[test]
    fn arguments_are_checked_per_action() {
        let trial = arguments(json!({"candidate":"q.json","job_name":"t1","workers":8,"arguments":["1"],"timeout_seconds":60}));
        assert!(trial.check(ToolAction::Trial).is_ok());
        assert!(arguments(json!({"candidate":"q.json","job_name":"m"})).check(ToolAction::Trial).is_ok(), "a trial without workers times the matrix");
        assert!(arguments(json!({"candidate":"q.json","job_name":"p"})).check(ToolAction::Profile).is_err(), "a profile needs its worker count");
        assert_eq!(trial.check(ToolAction::Compile).unwrap_err().class, FailureClass::MissingInput);
        assert_eq!(trial.verification(), TrialVerification::WholeCrate, "absent means the verified default");
        assert!(serde_json::to_value(&trial).unwrap().get("verification").is_none(), "a default request is serialized unchanged");
        let unverified = arguments(json!({"candidate":"q.json","job_name":"u","workers":8,"verification":"not_run"}));
        assert!(unverified.check(ToolAction::Profile).is_ok() && unverified.verification() == TrialVerification::NotRun);
        assert!(arguments(json!({"candidate":"q.json","job_name":"c","verification":"not_run"})).check(ToolAction::Compile).unwrap_err().message.contains("verification"));
        assert!(serde_json::from_value::<LocalJobArguments>(json!({"candidate":"q.json","job_name":"x","workers":8,"verification":"skip"})).is_err(), "typed values only");
        let verify = arguments(json!({"candidate":"q.json","job_name":"v","modules":["agent"]}));
        assert!(verify.check(ToolAction::Verify).is_ok());
        assert!(verify.check(ToolAction::Check).unwrap_err().message.contains("modules"));
        let build = arguments(json!({"storage":"s.json","job_name":"b"}));
        assert!(build.check(ToolAction::StorageBuild).is_ok() && build.check(ToolAction::StorageRegister).is_ok());
        assert!(arguments(json!({"storage":"s.json","job_name":"b","timeout_seconds":60})).check(ToolAction::StorageBuild).is_err(), "an asset build runs under the framework bound");
        assert!(arguments(json!({"candidate":"q.json","job_name":"h","hot_calls":5})).check(ToolAction::Trial).is_ok());
        assert!(arguments(json!({"candidate":"q.json","job_name":"h","hot_calls":0})).check(ToolAction::Trial).unwrap_err().message.contains("hot_calls"));
        assert!(arguments(json!({"candidate":"q.json","job_name":"h","workers":8,"hot_calls":5})).check(ToolAction::Profile).is_err(), "a profile has one measured call");
        assert!(build.check(ToolAction::Check).unwrap_err().message.contains("query manifest"));
        assert!(arguments(json!({"storage":"s.json","job_name":"s","statement":0})).check(ToolAction::StorageCheck).is_err());
        assert!(arguments(json!({"job_name":"-bad","candidate":"q"})).check(ToolAction::Check).unwrap_err().message.contains("portable"));
        assert!(serde_json::from_value::<LocalJobArguments>(json!({"job_name":"x","join_build_sides":[]})).is_err(), "native arguments are unknown");
        assert_eq!(ToolAction::parse("describe_physical").unwrap_err().class, FailureClass::MissingInput);
        assert_eq!(required_tools().len(), 12);
        assert_eq!(required_tools().last().map(String::as_str), Some("mcp__gendb_local__wait"), "every role is offered wait");
        assert!(arguments(json!({"job_name":"c"})).check(ToolAction::Catalog).is_ok());
        assert!(arguments(json!({"job_name":"c","candidate":"q.json"})).check(ToolAction::Catalog).is_err(), "catalog takes only job_name");
        assert!(required_tools().contains(&"mcp__gendb_local__storage_register".to_string()));
        let flat = required_tools_of(true);
        assert_eq!(flat.len(), 7, "fixed_flat offers the query tools, catalog and wait only");
        assert!(flat.iter().all(|t| !t.contains("storage_")) && flat.contains(&"mcp__gendb_local__catalog".to_string()) && flat.contains(&"mcp__gendb_local__wait".to_string()));
        let wait = |value: Value| serde_json::from_value::<WaitArguments>(value);
        assert_eq!(wait(json!({"job_name":"t1"})).unwrap().bound().unwrap().as_secs(), MAX_WAIT_SECONDS, "absent: the longest wait");
        assert_eq!(wait(json!({"job_name":"t1","wait_seconds":0})).unwrap().bound().unwrap().as_secs(), 0, "0 answers at once");
        assert!(wait(json!({"job_name":"t1","wait_seconds":MAX_WAIT_SECONDS + 1})).unwrap().bound().unwrap_err().message.contains("wait_seconds"));
        assert!(wait(json!({"job_name":"-t"})).unwrap().bound().unwrap_err().message.contains("portable"));
        assert!(wait(json!({"job_name":"t1","candidate":"q.json"})).is_err(), "wait takes job_name and wait_seconds only");
    }
}
