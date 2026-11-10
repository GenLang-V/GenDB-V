//! The engine author's workspace inputs: the generated contract bundle `contract/engine/**`,
//! the engine toolkit index, the crate map and the readable training-set and versions files. Every fact is generated
//! from the enforcing code (fixed entries, claims, obligations, registry, refusal rules, toolchain argv, failure classes,
//! tool schemas), the training templates and their saved baselines, the library's records and the prepared capture's
//! metadata; nothing is specific to a query.
//!
//! Workspace layout (paths the prompt and the tools name):
//! - `engine/src/**`: the engine crate (`verus-engine.json` `crate_dir`); the author owns `src/agent/**`, the framework
//!   files are written read-only for the manifest's storage uses (and again by the `check` tool);
//! - `verus-engine.json` (the manifest, seeded with the crate), `verus-engine-example.json`, `verus-storage-example.json`;
//! - `NOTES.md` (carried between rounds), `ENGINE_MAP.md` ([`engine_map`], generated each round);
//! - `versions/vNNN/`: read-only copies of every earlier version's sources and notes; `new-storages/`: storages the
//!   author builds from admitted ones;
//! - `reference/src/**`: the SQLSpec library and the engine toolkit, read-only, for reading before the crate exists;
//! - `admitted-storages/<name>@<id>/`, `admitted-code/`, `search-index.{json,txt}`: the admitted catalogs (the search
//!   index and `admitted-code/` also hold the admitted code of the request's read-only reuse libraries);
//! - `contract/engine/index.json`: the map of every input; `{task,final-claim,obligations,templates,storages,
//!   storage-budget,stored-data,data,registry,parallel,performance,rules,toolchain,tools,failure-classes,validation,
//!   accounting,integrity-constraints}.json`, `templates.md`, `toolkit.md`, `versions.md`,
//!   `fixed/{engine_entry,engine_codec,storage_entry,storage_entry_v2,storage_entry_derived,stored}.rs`,
//!   `proof-library/**`; `verus-tmp/`, `local-tool.json`.
//!
//! The general engine line (`EngineContractInputs::general`) writes the same bundle with its own task, index, rules,
//! failure classes, performance, tools and versions files, the budget rule (`budget-rule.json`), the storage-authoring
//! reference (`storage-authoring.md`) and a search index that also covers every version and verified attempt of the
//! run ([`general`]); the schema line's files are unchanged. A stage run of the general line
//! ([`write_stage_engine_contract`]) writes the goal workload's bundle with the stage's changes and every
//! workload's own files ([`stage`]); a run of several workloads ([`write_workloads_engine_contract`]) writes the
//! primary workload's bundle with that run's changes, every workload's files and `workloads.json` ([`workloads`]); every
//! other run writes its bundle as before.

use super::brief::common::{self, FixedFiles, quoted_item, write};
use super::brief::search_index::{EngineRecords, ReuseLibrary, write_engine_search_index, write_search_index};
use crate::controller::layout::NOTES_FILE;
use crate::controller::limits::Limits;
use crate::controller::author::{CANDIDATE_MANIFEST_RULE, CandidateSubmission};
use crate::engine::submission::{EngineManifest, MANIFEST_FILE};
use crate::engine::totals::STOP_RULE;
use crate::query::QuerySession;
use crate::query::compile::crate_options;
use crate::query::candidate::CompilerChoice;
use crate::query::source_items::{module_doc, public_items};
use crate::storage::catalog::write_read_only;
use crate::storage::manifest::StorageManifest;
use crate::storage::policy::StoredDataPolicy;
use crate::tools::{self, AuthorRole, ToolAction};
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_registry::{ConstraintMode, CrateKind, STORED_PARTS_SOURCE, definitions_for};
use gendb_runtime::abi::ENGINE_CODEC_SOURCE;
use gendb_storage::import::PreparedSource;
use gendb_verification::admission::AdmissionError;
use gendb_verification::admission::execution::CHILD_TIMEOUT_SECONDS;
use gendb_verification::obligations::{
    ENGINE_CLAIM_V1, ENGINE_ENTRY_IDENTITY, ENGINE_ENTRY_SOURCE, QUERY_ENTRY_V5, STORAGE_ENTRY_DERIVED, STORAGE_ENTRY_V1, STORAGE_ENTRY_V2, engine_toolkit_files,
    query_statement_check_files,
};
use gendb_verification::verus::engine_rules::{ALLOWED_EXEC_HELPERS, ENGINE_RULES, EVALUATOR_ROUTES, WHOLE_STATEMENT_EVALUATOR_RULE};
use gendb_verification::verus::{FrameworkSource, FrozenCrate, VerusMode, VerusToolchain, verus_args};
use serde_json::{Value, json};
use std::fs;
use std::path::Path;
use std::sync::Arc;

mod general;
pub(crate) mod stage;
pub(crate) mod workloads;

pub use general::{BUDGET_RULE_FILE, BUDGET_RULE_TEXT, GeneralContract, PLAIN_COLUMNS_CONTRACT_FILE};
pub use stage::{STAGE_FILE, StageContract, WorkloadContract, WorkloadRole};
pub use workloads::{MemberContract, WORKLOADS_FILE, WorkloadsContract};

/// The contract bundle directory, relative to the workspace.
pub const CONTRACT_DIRECTORY: &str = "contract/engine";
/// `scope` of the prepared context.
pub const SCOPE: &str = "verus_schema_engine";
/// `scope` of a general-line session's context and contract index.
pub const GENERAL_SCOPE: &str = "verus_general_engine";
/// The crate map in the workspace.
pub const ENGINE_MAP_FILE: &str = "ENGINE_MAP.md";
/// Read-only copies of earlier versions in the workspace.
pub const VERSIONS_DIRECTORY: &str = "versions";

/// Items of the fixed engine entry its claim consists of (quoted verbatim in `final-claim.json`).
const ENGINE_CLAIM_ITEMS: [&str; 12] = [
    "supported", "capacity_domain", "bound_db", "outcome_ok", "answer_meets", "stores_ready", "workers_ok", "served", "engine_meets", "abi_engine_query",
    "theorem_engine_end_to_end", "corollary_inside_capacity",
];

/// What the engine contract is generated from.
pub struct EngineContractInputs<'a> {
    /// The prepared training templates, in training order (name, session).
    pub sessions: &'a [(String, Arc<QuerySession>)],
    /// `engine::facts::training_facts`.
    pub training: &'a Value,
    /// Every accepted version's summary (`engine::rounds`), oldest first.
    pub versions: &'a [Value],
    /// The user's engine controls.
    pub limits: &'a Limits,
    pub store: &'a ObjectStore,
    pub capture: &'a PreparedSource,
    pub hardware: &'a Value,
    pub observed_hardware: &'a Value,
    pub free_bytes: Option<u64>,
    pub data_allowance: Option<u64>,
    pub storage_policy: &'a StoredDataPolicy,
    /// The seeded storages `(name, package)`, for the manifest example.
    pub seeded: &'a [(String, ContentId)],
    /// The request's read-only reuse libraries (`engine.reuse_libraries`): their admitted code joins the search index.
    pub reuse_libraries: &'a [ReuseLibrary<'a>],
    /// The general line's inputs (`None`: the schema line, whose bundle is unchanged).
    pub general: Option<GeneralContract<'a>>,
}

/// Generate the engine contract bundle and the readable files in `root` (the canonical workspace); returns the
/// context's contract facts: `files`, `storage_budget`, `integrity_constraints`, `performance`, `local_tools`.
pub fn write_engine_contract(root: &Path, inputs: &EngineContractInputs) -> Result<Value, AdmissionError> {
    write_contract(root, inputs, None)
}

/// The engine contract of a stage run: the goal workload's bundle from `inputs` (a general line's)
/// with the stage's changes, every workload's files under `contract/engine/workloads/<name>/` and `stage.json`
/// ([`stage`]); the context's contract facts also name `files.workloads` (by workload, then by file) and `files.stage`.
pub fn write_stage_engine_contract(root: &Path, inputs: &EngineContractInputs, stage: &StageContract) -> Result<Value, AdmissionError> {
    if inputs.general.is_none() {
        return Err(AdmissionError::tool("a stage run's contract is a general line's"));
    }
    write_contract(root, inputs, Some(Several::Stage(stage)))
}

/// The engine contract of a run of several workloads: the primary workload's bundle from `inputs` (a
/// general line's) with that run's changes, every workload's files under `contract/engine/workloads/<name>/` and
/// `workloads.json` ([`workloads`]); the context's contract facts also name `files.workloads` (by workload, then by
/// file) and `files.workloads_record`.
pub fn write_workloads_engine_contract(root: &Path, inputs: &EngineContractInputs, set: &WorkloadsContract) -> Result<Value, AdmissionError> {
    if inputs.general.is_none() {
        return Err(AdmissionError::tool("a run of several workloads' contract is a general line's"));
    }
    write_contract(root, inputs, Some(Several::Set(set)))
}

/// The two kinds of run of the general line with several workloads, whose contract changes the primary's bundle.
#[derive(Clone, Copy)]
enum Several<'a> {
    /// A stage run (`engine.stage`).
    Stage(&'a StageContract),
    /// A run of several workloads (`engine.workloads`).
    Set(&'a WorkloadsContract),
}

/// [`write_engine_contract`], with a stage run's or a run of several workloads' changes when `several` is given
/// (general line only).
fn write_contract(root: &Path, inputs: &EngineContractInputs, several: Option<Several>) -> Result<Value, AdmissionError> {
    let (stage, set) = match several {
        Some(Several::Stage(stage)) => (Some(stage), None),
        Some(Several::Set(set)) => (None, Some(set)),
        None => (None, None),
    };
    let contract = root.join(CONTRACT_DIRECTORY);
    fs::create_dir_all(&contract).map_err(AdmissionError::tool)?;
    fs::create_dir_all(root.join("new-storages")).map_err(AdmissionError::tool)?;
    let (_, first) = inputs.sessions.first().ok_or_else(|| AdmissionError::tool("an engine run needs at least one prepared template"))?;
    let statement = first.statement();
    let schema = &statement.instance.doc.tables;
    // A schema with a nullable column: the contract says how NULL rows are held and read (else unchanged).
    let nullable = common::has_nullable_column(schema);
    let c = |name: &str| contract.join(name);
    // The SQLSpec library and the toolkit, read-only, for reading before the crate's framework files exist.
    let reference = root.join("reference/src");
    let check_files = query_statement_check_files(&statement.instance, &statement.identity()).map_err(AdmissionError::tool)?;
    let library: Vec<FrameworkSource> =
        check_files.into_iter().filter(|f| !matches!(f.path.as_str(), "lib.rs" | "gendb_entry.rs" | "query.rs" | "gendb_params.rs")).chain(engine_toolkit_files()).collect();
    for f in &library {
        write_read_only(&reference.join(&f.path), &f.text)?;
    }
    let fixed = write_fixed_files(&contract, nullable)?;
    write(&c("final-claim.json"), &final_claim(&contract.join("fixed/engine_entry.rs")))?;
    write(&c("obligations.json"), &json!({"format_version":1,"engine":engine_obligations(&contract.join("fixed/engine_entry.rs")),"storage":common::storage_obligations(&fixed),
        "note":"the engine crate is proved against the engine entry; a storage you add is proved against the derived storage entry (built_from)"}))?;
    write(&c("integrity-constraints.json"), &common::integrity_constraints(statement, &fixed, &library, &reference))?;
    let general_line = inputs.general.as_ref();
    write(&c("templates.json"), inputs.training)?;
    write_text(&c("templates.md"), &templates_markdown(inputs.training))?;
    write_text(&c("toolkit.md"), &toolkit_index(&engine_toolkit_files(), &root.join("engine/src")))?;
    write_text(&c("versions.md"), &match general_line {
        Some(g) => general::versions_markdown(g, inputs.training),
        None => versions_markdown(inputs.versions, inputs.training),
    })?;
    let demands: Vec<(String, gendb_verification::obligations::DeclaredSource)> =
        inputs.sessions.iter().map(|(_, s)| Ok((s.statement().key_v4_id.clone(), s.demand()?))).collect::<Result<_, AdmissionError>>()?;
    write(&c("storages.json"), &common::storages_catalog(inputs.store, inputs.capture, schema, root, &demands, inputs.storage_policy)?)?;
    let budget = common::storage_budget(inputs.store, inputs.capture, schema, inputs.storage_policy, inputs.data_allowance, &c("storage-budget.json"))?;
    write(&c("stored-data.json"), &common::stored_data(&fixed.stored, inputs.storage_policy, true, nullable))?;
    let mut data = data_facts(inputs, schema);
    if let Some(g) = general_line {
        general::add_data_facts(&mut data, g);
        write(&c(BUDGET_RULE_FILE), &general::budget_rule(g))?;
        write_text(&c(PLAIN_COLUMNS_CONTRACT_FILE), gendb_verification::obligations::PLAIN_COLUMNS)?;
        // Every stage crate carries the nullable items, so their reference is always written there; a
        // run of several workloads adds the section on storage families.
        let authoring = general::storage_authoring(nullable || several.is_some());
        let authoring = if set.is_some() { authoring + workloads::FAMILY_AUTHORING } else { authoring };
        write_text(&c(super::engine_general_sections::STORAGE_AUTHORING_FILE), &authoring)?;
    }
    write(&c("data.json"), &data)?;
    let mut registry_file = general_line.map_or_else(registry, |_| general::registry(registry()));
    if set.is_some() {
        workloads::amend_registry(&mut registry_file);
    }
    write(&c("registry.json"), &registry_file)?;
    common::write_proof_library(&contract, &reference, &library)?;
    let workers = &first.worker_counts;
    write(&c("parallel.json"), &common::parallel(workers))?;
    let mut performance_file = general_line.map_or_else(|| performance(inputs.training, workers), |g| general::performance(inputs.training, workers, g));
    let mut rules_file = general_line.map_or_else(rules, general::rules);
    let mut failure_classes_file = general_line.map_or_else(failure_classes, general::failure_classes);
    let mut tools = general_line.map_or_else(|| tools_file(inputs.training, workers), |g| general::tools_file(inputs.training, workers, g));
    if let Some(stage) = stage {
        stage::amend_performance(&mut performance_file, stage);
        stage::amend_rules(&mut rules_file);
        stage::amend_failure_classes(&mut failure_classes_file);
        stage::amend_tools(&mut tools, stage);
    }
    if let Some(set) = set {
        workloads::amend_performance(&mut performance_file, set);
        workloads::amend_rules(&mut rules_file);
        workloads::amend_failure_classes(&mut failure_classes_file);
        workloads::amend_tools(&mut tools, set);
    }
    write(&c("performance.json"), &performance_file)?;
    write(&c("rules.json"), &rules_file)?;
    write(&c("toolchain.json"), &toolchain(root)?)?;
    write(&c("failure-classes.json"), &failure_classes_file)?;
    let sessions: Vec<&QuerySession> = inputs.sessions.iter().map(|(_, s)| s.as_ref()).collect();
    write(&c("validation.json"), &common::validation(AuthorRole::Engine, &sessions))?;
    write(&c("tools.json"), &tools)?;
    write(&c("accounting.json"), &common::accounting(inputs.limits))?;
    let example = root.join("verus-engine-example.json");
    write(&example, &json!(EngineManifest::example(inputs.seeded)))?;
    write(&root.join("verus-storage-example.json"), &json!(StorageManifest::example()))?;
    let mut task_file = general_line.map_or_else(|| task(root, &example), |g| general::task(root, &example, g));
    if nullable {
        task_file["storage_manifest"]["schema"] = common::manifest_schema(true, true);
        if general_line.is_some() {
            general::add_nullable_access(&mut task_file["generated_access"]);
        }
    }
    let shape = general_line.map(|g| super::engine_general_sections::Shape::of_branches(g.inputs.branches.len()));
    if let (Some(stage), Some(shape)) = (stage, shape) {
        stage::amend_task(&mut task_file, root, &contract, stage, shape);
    }
    if let (Some(set), Some(shape)) = (set, shape) {
        workloads::amend_task(&mut task_file, root, &contract, set, shape);
    }
    write(&c("task.json"), &task_file)?;
    let search_index = match general_line {
        Some(g) => write_engine_search_index(inputs.store, inputs.reuse_libraries, &EngineRecords { engine_dir: g.engine_dir }, root, inputs.storage_policy)?,
        None => write_search_index(inputs.store, inputs.reuse_libraries, root, inputs.storage_policy)?,
    };
    let mut index_file = general_line.map_or_else(|| index(root, &contract), |g| general::index(root, &contract, g));
    if nullable && general_line.is_some() {
        general::add_nullable_access(&mut index_file["generated_access"]);
    }
    if let (Some(stage), Some(shape)) = (stage, shape) {
        stage::amend_index(&mut index_file, &contract, stage, shape);
    }
    if let (Some(set), Some(shape)) = (set, shape) {
        workloads::amend_index(&mut index_file, &contract, set, shape);
    }
    write(&c("index.json"), &index_file)?;
    let workloads_files = stage.map(|stage| stage::write_workload_files(&contract, stage)).transpose()?;
    let member_files = set.map(|set| workloads::write_member_files(&contract, set)).transpose()?;
    let mut constraints = common::constraints_fact(statement, &c("integrity-constraints.json"));
    constraints["in_words"] = json!("the engine entry states bound_db with these declarations: the engine is proved for every database that satisfies them; a storage may opt in (uses_declared_constraints, storage entry v2) and then applies only to runs with exactly these declarations; the declarations are never checked against the data");
    let mut facts = json!({"files":{"workspace":root,"author_contract":c("index.json"),"engine_manifest":root.join(MANIFEST_FILE),"engine_crate":root.join("engine"),
            "engine_map":root.join(ENGINE_MAP_FILE),"notes":root.join(NOTES_FILE),"versions":root.join(VERSIONS_DIRECTORY),"templates":c("templates.md"),
            "toolkit":c("toolkit.md"),"versions_detail":c("versions.md"),"data":c("data.json"),"toolchain":c("toolchain.json"),"search_index":search_index,
            "new_storages":root.join("new-storages"),"submission_example":example,"full_context":root.parent().map(|p| p.join("context.json"))},
        "storage_budget":budget,"integrity_constraints":constraints,
        "performance":{"free_bytes_at_prepare":inputs.free_bytes,"file":c("performance.json"),"worker_counts":workers,
            "evaluation_timing":"official cells: 1 warm + 3 hot calls in one fresh child per (template, worker count), the median hot call; planning inside the call is timed, SQL translation and encoding are not"},
        "local_tools":{"transport":"typed stdio MCP sibling","server":tools::SERVER_NAME,"mcp_context":root.join(tools::CONTEXT_FILE),
            "required_tools":tools::required_tools(),"actions":ToolAction::ALL.iter().map(|a| a.name()).collect::<Vec<_>>()},
        "output":format!("Return CandidateSubmission whose candidate_manifest is your {MANIFEST_FILE} inside this workspace; files.author_contract maps every input")});
    if let Some(g) = general_line {
        facts["files"]["budget_rule"] = json!(c(BUDGET_RULE_FILE));
        facts["files"]["plain_columns"] = json!(c(PLAIN_COLUMNS_CONTRACT_FILE));
        // The main author may run sub-agents, at most 5 at a time; the
        // transport reads this key (`ClaudeCode::configure_context`).
        facts["author_subagents"] = json!({"max_concurrent":5});
        facts["performance"]["evaluation_timing"] = json!(format!("each submission is timed interleaved with its parent under the development plan: per cell (template at the timing binding, worker count) both in fresh children back to back, 1 warm + {} each (engine.timed_calls), the median hot call the cell's time, under the call limits; planning inside the call is timed, SQL translation and encoding are not. The full protocol (the version timed alone, 1 warm + 3 hot calls per cell, every visible binding, the variants timed and a profile) runs only in the final evaluation, for the final numbers", crate::engine::protocol::hot_calls_text(g.inputs.timed_calls)));
    }
    if let Some(workloads) = workloads_files {
        facts["files"]["workloads"] = workloads;
        facts["files"]["stage"] = json!(c(STAGE_FILE));
    }
    if let Some(workloads) = member_files {
        facts["files"]["workloads"] = workloads;
        facts["files"]["workloads_record"] = json!(c(WORKLOADS_FILE));
    }
    Ok(facts)
}

fn write_text(path: &Path, text: &str) -> Result<(), AdmissionError> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(AdmissionError::tool)?;
    }
    fs::write(path, text).map_err(AdmissionError::tool)
}

/// The fixed texts under `<contract>/fixed/`: the engine entry and its AST codec, the storage entries (v1, the
/// opt-in v2 and the derived entry) and the stored-parts read API.
fn write_fixed_files(contract: &Path, nullable: bool) -> Result<FixedFiles, AdmissionError> {
    let fixed = contract.join("fixed");
    write_read_only(&fixed.join("engine_entry.rs"), ENGINE_ENTRY_SOURCE)?;
    write_read_only(&fixed.join("engine_codec.rs"), ENGINE_CODEC_SOURCE)?;
    let files = FixedFiles {
        // Engine runs declare integrity constraints; the query entry field selects the constrained storage obligations.
        query: QUERY_ENTRY_V5,
        query_entry: fixed.join("engine_entry.rs"),
        storage_entry: fixed.join("storage_entry.rs"),
        storage_entry_v2: Some(fixed.join("storage_entry_v2.rs")),
        storage_entry_derived: fixed.join("storage_entry_derived.rs"),
        stored: fixed.join("stored.rs"),
        nullable,
    };
    write_read_only(&files.storage_entry, STORAGE_ENTRY_V1.source)?;
    write_read_only(files.storage_entry_v2.as_ref().expect("set above"), STORAGE_ENTRY_V2.source)?;
    write_read_only(&files.storage_entry_derived, STORAGE_ENTRY_DERIVED.source)?;
    write_read_only(&files.stored, STORED_PARTS_SOURCE)?;
    Ok(files)
}

/// `final-claim.json`: the engine claim record and its items quoted from the fixed entry.
fn final_claim(entry: &Path) -> Value {
    json!({"format_version":1,"fixed_entry":entry,"identity":ENGINE_ENTRY_IDENTITY,"claim":ENGINE_CLAIM_V1,
        "claim_items":ENGINE_CLAIM_ITEMS.iter().map(|n| quoted_item(ENGINE_ENTRY_SOURCE, n)).collect::<Vec<_>>(),
        "statuses":{"Refused":"the worker count is outside 1..=64 (decided by the entry)","Malformed":"the AST bytes do not decode (decode_spec is None)",
            "ParamRefused":"the decoded query is not supported (not wf_ordered over the schema)","Ok / SqlError / Capacity":"your engine's answer, judged by answer_meets"},
        "in_words":"for every supported query and every database bound to the stored parts of the engine's storage uses under the declared integrity constraints, and under the trusted assumptions (claim.trusted_assumptions), every call terminates (proved_properties) with an outcome the SQL meaning allows: allowed rows (ordered_ok: any tie order, any tie choice at a LIMIT boundary), the exact SQL error, or Capacity only outside capacity_domain. The fixed claim also permits WorkerFailed, which the trusted assumption worker_failure excludes; a process abort (allocation failure, stack exhaustion, failed thread creation, an unwind on the calling thread) ends a call with no outcome, excluded only by the trusted assumption calling_thread_progress"})
}

/// The engine obligations (`obligations.json` `engine`): the author items and what the entry provides.
fn engine_obligations(entry: &Path) -> Value {
    json!({"format_version":1,"fixed_entry":entry,"identity":ENGINE_ENTRY_IDENTITY,"author_items":ENGINE_CLAIM_V1.author_obligations,
        "theorems":ENGINE_CLAIM_V1.theorems,"trusted_assumptions":ENGINE_CLAIM_V1.trusted_assumptions,"proved_properties":ENGINE_CLAIM_V1.proved_properties,
        "domains":ENGINE_CLAIM_V1.domains})
}

/// The registry index of an engine run: the engine crate's definitions (declared constraints) and the storage crates'.
pub(super) fn registry() -> Value {
    let kinds = |kind: CrateKind, mode: ConstraintMode| -> Vec<Value> { definitions_for(kind, mode).map(registry_row).collect() };
    json!({"format_version":1,"engine_crate":kinds(CrateKind::Engine, ConstraintMode::Declared),
        "storage_crate":kinds(CrateKind::Storage, ConstraintMode::Unconstrained),"storage_crate_uses_declared_constraints":kinds(CrateKind::Storage, ConstraintMode::Declared),
        "placeholder":"<storage> in a crate path stands for a storage's name",
        "authority":"each definition's file is the authority; this index only says which file holds which items and where assembled crates carry it (gendb_registry)"})
}

/// One registry definition as `registry.json` lists it.
pub(super) fn registry_row(d: &gendb_registry::Definition) -> Value {
    json!({"name":d.name,"crate_path":d.crate_path,"presence":d.presence,"role":d.role,"origin":d.origin,"items":d.items,"summary":d.summary})
}

/// The data facts (as the workload storage author reads them: the schema, storability, sizes and the source data facts
/// computed at import), the host and the storage budget.
fn data_facts(inputs: &EngineContractInputs, schema: &[gendb_frontend::ast::TableDef]) -> Value {
    let mut facts = common::data_facts(inputs.capture, schema);
    facts["source_facts"] = common::source_data_facts(inputs.capture);
    facts["unavailable"] = json!({"source_facts":"value ranges, estimated distinct counts, sortedness, key density and text byte lengths of every captured column are in source_facts (computed once at import)",
        "use":"facts of this data only: the engine is proved for every bound database, so a fast path that relies on one must be guarded by a flag a storage builder checks (ENGINE_STORAGE in the prompt)",
        "how_to_measure":"trial/profile over the storages, storage_build over a candidate storage; never hash or fingerprint whole datasets, never write into the source or capture directories"});
    facts["hardware"] = json!({"configured":inputs.hardware,"observed":inputs.observed_hardware});
    facts["free_bytes_at_prepare"] = json!(inputs.free_bytes);
    facts["data_allowance_bytes"] = json!(inputs.data_allowance);
    facts
}

/// `performance.json`: the timing protocol of the official matrix, the variants and the totals, and the execution
/// environment (`common::measurement_protocol`).
fn performance(training: &Value, workers: &[usize]) -> Value {
    let protocol = common::measurement_protocol(workers);
    json!({"format_version":1,
        "official_matrix":format!("every training template at the timing binding {} x every configured worker count {workers:?}: one fresh worker child per cell holding the host's exclusive timing lease, 1 warm call then 3 hot calls; the cell's time is the median hot call", training["timing_binding"]),
        "timed_call":"wall time of one engine call (abi_engine_query) over the mapped storage parts, the engine's planning included; SQL translation, binding substitution, AST encoding and the echo are untimed and recorded separately",
        "totals":"per worker count, the sum of the template medians; compared with the saved DuckDB and Umbra totals of the same templates, binding and worker count (templates.json baseline_totals; never rerun)",
        "stop_rule":STOP_RULE,
        "variant_matrix":"every timed variant at the timing binding and 64 workers, 1 warm + 1 hot call; its ratio to the template's official median is a report, never a bound",
        "other_bindings":format!("for a version whose official totals meet the stop, every template at the other visible bindings {} with the official protocol; reported, never a stop condition", training["other_bindings"]),
        "baselines":"saved runs of DuckDB and Umbra (templates.json baselines per template, binding and worker count, with their answer agreement); they are not same-window comparisons",
        "execution_environment":protocol["execution_environment"],"profiling":protocol["profiling"],"compiler_controls":protocol["compiler_controls"],
        "host":"data.json hardware (configured worker counts and the observed host)"})
}

/// `rules.json`: the central source rules and the engine's own rules.
fn rules() -> Value {
    let mut rules = common::rules();
    rules["engine_rules"] = json!({"rules":ENGINE_RULES,"static_items":crate::engine::submission::ENGINE_STATIC_ITEM_RULE,
        "scope":"every agent/ file of the engine crate, at freeze (the check tool and every submission) and again at admission: no template constant of the training templates' SQL texts, no table of AST fragments with fixed table or column indices, no reference to the whole-statement evaluator or to a function that can reach it (whole_query_evaluator), and no static item (no state between calls)"});
    rules["whole_query_evaluator"] = json!({"rule":WHOLE_STATEMENT_EVALUATOR_RULE,
        "refused_functions":EVALUATOR_ROUTES,
        "allowed_helpers":ALLOWED_EXEC_HELPERS,
        "in_words":"the engine is your own planner, operators and general expression path, not the verified reference interpreter. Refused in agent/ code: the modules crate::exec::relational::eval and ::entry (any path or relational::{..} group naming them), a glob import of crate::exec::relational itself (globs of its other submodules, such as domain, stay allowed), aliases of relational (`relational as`), and every function in refused_functions as an identifier, whatever path, alias or glob it comes through (each can call the evaluator with a query, condition or expression you pass it); a function of your own with one of these names must be renamed. Allowed: every other executable helper (allowed_helpers lists them by module, each checked not to reach the evaluator)",
        "enforced":"refused at freeze and again at admission (engine rule whole_statement_evaluator); lexical, backed by the trajectory audit"});
    rules
}

/// `toolchain.json`: the shared toolchain file (`common::toolchain_file`) and the exact commands for the engine crate.
fn toolchain(root: &Path) -> Result<Value, AdmissionError> {
    let crate_dir = root.join("engine");
    let mut file = common::toolchain_file(root, &crate_dir)?;
    let toolchain = VerusToolchain::from_env().map_err(AdmissionError::tool)?;
    let tmp = root.join("verus-tmp");
    let environment = file["environment"].as_str().unwrap_or_default().to_string();
    let command = |mode: VerusMode, out: &Path| -> Result<String, AdmissionError> {
        let krate = FrozenCrate::from_recorded_author_files(crate_dir.clone(), vec![], vec!["lib.rs".into()]);
        let argv = verus_args(&krate, &crate_options(CrateKind::Engine, &CompilerChoice::default()), mode, out).map_err(AdmissionError::tool)?;
        Ok(format!("env -i {environment} {} {}", common::shell_word(&toolchain.rust_verify.display().to_string()), argv.iter().map(|a| common::shell_word(a)).collect::<Vec<_>>().join(" ")))
    };
    file["engine_crate"] = json!({"verify":command(VerusMode::Verify, &tmp)?,"compile":command(VerusMode::VerifyAndCompile, &tmp.join("FRESH_OUTPUT_DIRECTORY"))?,
        "framework_files":"written into the crate for the manifest's storage uses when the round is prepared and again by the check tool",
        "direct_verus":"direct-verus.sh query <engine crate dir> runs the same rust_verify on the engine crate (crate name gendb_query instead of gendb_engine: verification is the same; build libraries with the compile tool)"});
    file["query_crate"] = json!("not used in an engine run: see engine_crate");
    Ok(file)
}

/// `failure-classes.json` with the engine's named refusals.
fn failure_classes() -> Value {
    let mut file = common::failure_classes();
    let named = file["named_reasons"].as_object_mut().expect("named reasons");
    named.insert("engine_storage_coverage_incomplete".into(), json!("refusal: the engine's storage uses together do not store every column of every table; add a use"));
    named.insert("engine_requires_declared_constraints".into(), json!("refusal: the engine claim is stated under the run's declared integrity constraints"));
    named.insert("template_constant".into(), json!("refusal (engine rules): an agent/ file contains a text or date constant of a training template's SQL text"));
    named.insert("ast_fragment_table".into(), json!("refusal (engine rules): an agent/ file holds an AST node with a fixed table or column index"));
    named.insert("whole_statement_evaluator".into(), json!("refusal (engine rules): an agent/ file references the whole-statement evaluator crate::exec::relational::{eval, entry}, globs exec::relational itself or aliases it, or names a function that can reach the evaluator (rules.json whole_query_evaluator.refused_functions)"));
    named.insert("saved_answer_disagreement".into(), json!("execution failure: a template's (or variant's) answer agrees with no saved answer of another engine"));
    file
}

/// `tools.json` of the engine role.
fn tools_file(training: &Value, workers: &[usize]) -> Value {
    let templates: Vec<&Value> = training["templates"].as_array().into_iter().flatten().map(|t| &t["name"]).collect();
    json!({"format_version":1,"server":format!("{} (typed MCP)", tools::SERVER_NAME),"role":AuthorRole::Engine,
        "tools":{"check":"freeze the engine crate from a verus-engine.json: manifest, storage uses, complete coverage, composition, source rules (central scan, static items, engine rules), framework files written into your crate; no Verus",
            "verify":"check + one whole-crate Verus verification (or the named modules, diagnostic only)",
            "compile":"check + the whole-crate verify-and-compile run submissions use",
            "trial":"compile (or verification not_run) + the engine over the training matrix (templates x workers at one binding) or your sql statements, one fresh child per cell under the timing lease",
            "profile":"one cell, 1 warm + 1 measured call, with dispatch and CPU detail",
            "storage_check":"as for every role: a storage crate snapshot (storages you add are built_from admitted ones)","storage_verify":"storage_check + Verus","storage_compile":"storage_check + verify-and-compile",
            "storage_build":"storage_compile + its asset built once (verification not_run: an unverified diagnostic build)","storage_register":"storage_build + admission as a new version",
            "catalog":"re-read the library: storages.json and storage-budget.json","wait":tools::WAIT_SUMMARY},
        "arguments":{"candidate":"engine tools: your verus-engine.json inside the workspace","storage":"storage tools: a verus-storage.json inside the workspace","job_name":"1..64 portable identifier",
            "wait_seconds":format!("wait only, optional, 0..={}: the most the call waits (default the maximum)", tools::MAX_WAIT_SECONDS),
            "templates":{"meaning":"trial/profile: training template names; trial default every template, profile exactly one (or one sql)","values":templates},
            "binding":{"meaning":"trial/profile: the visible binding the templates run at; default the timing binding","values":training["templates"][0]["bindings"].as_array().map(|b| b.iter().map(|x| x["name"].clone()).collect::<Vec<_>>())},
            "sql":"trial/profile: your own SQL statements over the schema (no parameters), instead of templates; each is translated and encoded like the templates; no saved answer (status, rows and times only)",
            "workers":format!("profile: required, one of {workers:?}; trial: optional (absent: every configured worker count)"),"modules":"verify/storage_verify only; crate module paths",
            "hot_calls":"trial only, optional, at least 1 (default 1); official evaluations always run 1 warm + 3 hot",
            "timeout_seconds":format!("trial/profile only, optional, 1..={CHILD_TIMEOUT_SECONDS}: bound of each child of the job. {}", tools::CHILD_TIMEOUT_MEANING),
            "verification":"trial/profile/storage_build only, optional: whole_crate (default) or not_run (rust_verify --no-verify; every result labelled diagnostic_unverified, never a submission or official measurement)"},
        "result_fields":{"trial":"cells[] per (statement, binding, workers): status (saved_answers_agree / saved_answers_agree_partly / not_compared for sql), warm_wall_ns, hot_wall_ns, median_hot_wall_ns, rows, echo_equal, baseline {umbra_ns, duckdb_ns, faster_ns}, ratio_to_faster; totals per worker count when every template ran (with the baselines' totals); storage[] per use; build {reused, record}",
            "profile":"trial's fields for one cell with one measured call, plus dispatch {spawned, joined, ranges}, process user/system CPU and calling_thread_share_permille",
            "authority":"each job's result.json (result_record) holds the full record"},
        "diagnostics":"every job is a diagnostic: never a submission, never the official measurement; jobs run one at a time in the session's framework service. storage_register admits a storage version into the library",
        "child_timeout_seconds":CHILD_TIMEOUT_SECONDS,"direct_use":"you may also run rust_verify yourself (toolchain.json engine_crate)"})
}

fn task(root: &Path, example: &Path) -> Value {
    json!({"format_version":1,
        "task":"Write one verified engine for the schema: crate::agent::engine answers every supported query (wf_ordered over the schema) over the stored data, proved against the fixed engine entry; submit its verus-engine.json",
        "you_own":root.join("engine/src/agent"),"required_items":ENGINE_CLAIM_V1.author_obligations,
        "you_choose":"the planner, physical plans and operators, data representations, parallelism, compiler controls, which admitted storages the engine reads and any storage you add built from them; every specification, lemma and proof",
        "manifest":{"file":root.join(MANIFEST_FILE),"schema":EngineManifest::schema(),"example":example,"rule":CANDIDATE_MANIFEST_RULE},
        "storage_manifest":{"schema":common::manifest_schema(true, false),"example":root.join("verus-storage-example.json"),"where":root.join("new-storages"),
            "rule":"a storage you add sets built_from (admitted sources, optionally extends one of them) and declares data_policy per part"},
        "fixed":"the engine entry, the AST codec, the toolkit and every framework file are regenerated at freeze; edited workspace copies are never used",
        "readability":"versions are published and read by people and later rounds: name modules after what they do; a //! header per module (its first sentence is the module's line in ENGINE_MAP.md); state units and invariants; explain proof steps that are not obvious"})
}

fn index(root: &Path, contract: &Path) -> Value {
    let c = |name: &str| contract.join(name);
    json!({"format_version":1,"scope":SCOPE,
        "task":"Write one verified engine for every supported query on the schema (contract task.json); its totals over the training templates are its performance feedback",
        "read_order":["task","final_claim","obligations","templates","versions","engine_map","toolkit","storages","stored_data","data","validation","performance","rules","tools","integrity_constraints","proof_library"],
        "inputs":{"task":c("task.json"),"final_claim":c("final-claim.json"),"obligations":c("obligations.json"),"templates":c("templates.md"),"templates_data":c("templates.json"),
            "versions":c("versions.md"),"engine_map":root.join(ENGINE_MAP_FILE),"toolkit":c("toolkit.md"),"storages":c("storages.json"),"storage_budget":c("storage-budget.json"),
            "stored_data":c("stored-data.json"),"data":c("data.json"),"registry":c("registry.json"),"fixed":c("fixed"),"proof_library":c("proof-library/index.json"),
            "proof_patterns":c("proof-library/patterns.json"),"parallelism":c("parallel.json"),"performance":c("performance.json"),"validation":c("validation.json"),
            "source_rules":c("rules.json"),"toolchain":c("toolchain.json"),"tools":c("tools.json"),"failure_classes":c("failure-classes.json"),"accounting":c("accounting.json"),
            "integrity_constraints":c("integrity-constraints.json"),"reference_sources":root.join("reference/src"),"engine_crate":root.join("engine"),
            "earlier_versions":root.join(VERSIONS_DIRECTORY),"new_storages":root.join("new-storages")},
        "commands":{"tools":format!("mcp__{}__{{{}}} (tools.json)", tools::SERVER_NAME, ToolAction::ALL.map(ToolAction::name).join(",")),
            "api_lookup":common::api_lookup(contract),
            "direct_verify":"toolchain.json engine_crate.verify (module-scoped diagnostic runs through the foreground helper toolchain.json direct_verus)"},
        "output":{"submission":CandidateSubmission::schema(),"manifest":EngineManifest::schema(),"rule":CANDIDATE_MANIFEST_RULE},
        "framework_source":"read your crate's framework files, reference/src and contract fixed/** freely: they are the authority (look items up with commands.api_lookup and toolkit.md first, then read the regions you need). Host and controller source is not needed and is not an input",
        "input_boundary":"your task inputs are this workspace, the files mapped above and the prepared data they name; the pinned toolchain (including vstd sources), standard system tools and hardware diagnostics are available. Other GenDB runs, scratch directories, tests, fixtures and repository source are not inputs: do not read, list or search them (every tool call is recorded and audited)"})
}

/// `templates.md`: per training template its SQL, parameters, visible bindings and the saved baseline medians at
/// every binding and worker count.
pub fn templates_markdown(training: &Value) -> String {
    let ms = |ns: &Value| ns.as_f64().map_or("-".to_string(), |ns| format!("{:.3}", ns / 1e6));
    let mut out = format!(
        "# Training templates\n\nThe training set of this engine run: every template with its SQL, parameters, visible bindings (`{}` is the timing binding) and the saved DuckDB and Umbra hot medians in ms. Generated by GenDB from `templates.json` (same directory).\n",
        training["timing_binding"].as_str().unwrap_or("-")
    );
    for t in training["templates"].as_array().into_iter().flatten() {
        out.push_str(&format!("\n## {}\n\nReads: {}.\n\n```sql\n{}\n```\n", t["name"].as_str().unwrap_or("-"),
            t["tables"].as_array().into_iter().flatten().filter_map(Value::as_str).collect::<Vec<_>>().join(", "), t["sql"].as_str().unwrap_or_default().trim_end()));
        let parameters: Vec<String> = t["parameters"].as_array().into_iter().flatten()
            .map(|p| format!("`${}` {} ({})", p["index"], p["name"].as_str().unwrap_or("-"), p["type"].as_str().unwrap_or("-"))).collect();
        if !parameters.is_empty() {
            out.push_str(&format!("\nParameters: {}.\n", parameters.join("; ")));
        }
        out.push_str("\n| Binding | Arguments | Workers | Umbra ms | DuckDB ms | Agreement |\n|---|---|---:|---:|---:|---|\n");
        for b in t["bindings"].as_array().into_iter().flatten() {
            let arguments: Vec<&str> = b["arguments"].as_array().into_iter().flatten().filter_map(Value::as_str).collect();
            for cell in t["baselines"].as_array().into_iter().flatten().filter(|c| c["binding"] == b["name"]) {
                out.push_str(&format!("| {} | {} | {} | {} | {} | {} |\n", b["name"].as_str().unwrap_or("-"), arguments.join(", "), cell["workers"], ms(&cell["umbra_ns"]), ms(&cell["duckdb_ns"]),
                    cell["agreement"].as_str().unwrap_or("-")));
            }
        }
    }
    out
}

/// `versions.md`: every accepted version's totals and per-template official medians.
pub fn versions_markdown(versions: &[Value], training: &Value) -> String {
    let ms = |ns: &Value| ns.as_f64().map_or("-".to_string(), |ns| format!("{:.3}", ns / 1e6));
    let mut out = String::from("# Versions\n\nEvery accepted version of this engine run, oldest first: its official totals and per-template hot medians (ms) at the timing binding. Generated by GenDB from each version's record.\n");
    if versions.is_empty() {
        out.push_str("\nNo version yet.\n");
        return out;
    }
    let names: Vec<&str> = training["templates"].as_array().into_iter().flatten().filter_map(|t| t["name"].as_str()).collect();
    for v in versions {
        let workers: Vec<u64> = v["totals"]["workers"].as_array().into_iter().flatten().filter_map(|w| w["workers"].as_u64()).collect();
        out.push_str(&format!("\n## {} (round {})\n\nFolder: `{}`.\n\n| Template |", v["version"].as_str().unwrap_or("-"), v["round"], v["directory"].as_str().unwrap_or("-")));
        for w in &workers {
            out.push_str(&format!(" {w} workers |"));
        }
        out.push_str(&format!("\n|---|{}\n", "---:|".repeat(workers.len())));
        for name in &names {
            out.push_str(&format!("| {name} |"));
            for w in &workers {
                let cell = v["totals"]["templates"].as_array().into_iter().flatten().find(|r| r["template"] == *name && r["workers"].as_u64() == Some(*w));
                out.push_str(&format!(" {} |", cell.map_or("-".to_string(), |r| ms(&r["engine"]["median_ns"]))));
            }
            out.push('\n');
        }
        out.push_str("| **Total** |");
        for w in v["totals"]["workers"].as_array().into_iter().flatten() {
            out.push_str(&format!(" {} |", ms(&w["engine_ns"])));
        }
        out.push('\n');
    }
    out
}

/// One module's section of a Markdown index: its path, header and public items with their signature lines.
fn module_section(path: &str, file: &Path, text: &str) -> String {
    let doc = module_doc(text);
    let mut out = format!("\n## `{path}`\n\nFile: `{}`.\n\n{}\n", file.display(), if doc.is_empty() { "(no module header)".to_string() } else { doc });
    let items = public_items(path, text, false);
    let listed: Vec<String> = items["items"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|item| item["kind"] != "re-export")
        .map(|item| {
            let line = item["text"].as_str().or(item["signature"].as_str()).unwrap_or_default().replace('\n', " ");
            let doc = item["doc"].as_str().map(|d| format!(" — {d}")).unwrap_or_default();
            format!("- line {}: `{}`{doc}", item["line"], line)
        })
        .collect();
    if !listed.is_empty() {
        out.push('\n');
        out.push_str(&listed.join("\n"));
        out.push('\n');
    }
    out
}

/// `toolkit.md`: the engine toolkit index, generated from each toolkit file's module header and public items (as the
/// files stand in this build), with the file under the engine crate's `src/`.
pub fn toolkit_index(toolkit: &[FrameworkSource], crate_src: &Path) -> String {
    let mut out = String::from(
        "# Engine toolkit index\n\nThe engine-only proof toolkit every engine crate carries as `crate::engine_link` (framework files, read-only, generic: no query, table or column is named). Generated by GenDB from each module's `//!` header and public items; the files are the authority.\n",
    );
    for file in toolkit {
        out.push_str(&module_section(&file.path, &crate_src.join(&file.path), &file.text));
    }
    out
}

/// `ENGINE_MAP.md`: the map of the engine crate's author modules (`src/agent/**` under `crate_src`), generated from each
/// module's `//!` header and public items, so a fresh round can orient itself in a large crate. `about` names the
/// version and round it describes.
pub fn engine_map(crate_src: &Path, about: &str) -> Result<String, AdmissionError> {
    let agent = crate_src.join("agent");
    let mut files = vec![];
    collect_rust_files(&agent, &mut files)?;
    files.sort();
    let lines: usize = files.iter().map(|f| fs::read_to_string(f).map(|t| t.lines().count()).unwrap_or(0)).sum();
    let mut out = format!(
        "# Engine map\n\nGenerated by GenDB when this round was prepared, from the engine crate's author modules ({about}): {} files, {lines} lines under `{}`. Each module's `//!` header and its public items. Framework modules (`spec`, `exec`, `bridge`, `link`, `engine_link`, `stores`, `gendb_entry`) are indexed in the contract (`toolkit.md`, `proof-library/`).\n",
        files.len(),
        agent.display()
    );
    for file in &files {
        let text = fs::read_to_string(file).map_err(AdmissionError::tool)?;
        let path = file.strip_prefix(crate_src).unwrap_or(file).display().to_string();
        out.push_str(&module_section(&path, file, &text));
    }
    Ok(out)
}

fn collect_rust_files(dir: &Path, found: &mut Vec<std::path::PathBuf>) -> Result<(), AdmissionError> {
    if !dir.is_dir() {
        return Ok(());
    }
    for entry in fs::read_dir(dir).map_err(AdmissionError::tool)? {
        let path = entry.map_err(AdmissionError::tool)?.path();
        if path.is_dir() {
            collect_rust_files(&path, found)?;
        } else if path.extension().is_some_and(|e| e == "rs") {
            found.push(path);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The toolkit index lists every toolkit module with its header, and the crate map every agent module with its
    /// items, from the files as they stand.
    #[test]
    fn indexes_follow_module_headers_and_items() {
        let toolkit = engine_toolkit_files();
        let index = toolkit_index(&toolkit, Path::new("/crate/src"));
        for file in &toolkit {
            assert!(index.contains(&format!("## `{}`", file.path)), "{}", file.path);
        }
        assert!(index.contains("File: `/crate/src/engine_link/mod.rs`"));
        let scratch = crate::controller::test_support::scratch_root("engine-map");
        fs::create_dir_all(scratch.join("src/agent/plan")).unwrap();
        fs::write(scratch.join("src/agent/mod.rs"), "//! The engine entry: plans and runs a query.\nverus! {\n/// Answers one query.\npub fn engine(q: u8) -> u8 { q }\n}\n").unwrap();
        fs::write(scratch.join("src/agent/plan/join.rs"), "//! Hash join.\npub fn build() {}\n").unwrap();
        let map = engine_map(&scratch.join("src"), "v3, round 4").unwrap();
        assert!(map.contains("(v3, round 4): 2 files, 7 lines"), "{map}");
        assert!(map.contains("## `agent/mod.rs`") && map.contains("The engine entry: plans and runs a query.") && map.contains("`pub fn engine(q: u8) -> u8 { q }` — Answers one query."), "{map}");
        assert!(map.contains("## `agent/plan/join.rs`") && map.contains("Hash join."));
        fs::remove_dir_all(&scratch).ok();
    }

    /// The general line's contract files over the scripted run: the general manifest schema and task, the line's rules
    /// without the evaluator rule, its failure classes, the timing, score, limits and profile in `performance.json`, the
    /// tools under the limits, the budget rule, and `versions.md` with the versions' totals and the attempts.
    #[test]
    fn the_general_contract_states_the_lines_rules_timing_and_budget() {
        use gendb_verification::verus::engine_rules::{EngineRuleSet, SchemaNames, TemplateConstants};
        let root = crate::controller::test_support::scratch_root("general-contract");
        let run = crate::prompts::engine_facts::general::tests::scripted_run(&root.join("run"));
        let training = crate::prompts::engine_facts::general::tests::training();
        let rules_set = EngineRuleSet::general_with_names(TemplateConstants::from_texts(&[("Q01".into(), "SELECT 'MAIL' FROM t".into())]).unwrap(),
            SchemaNames::from_names(["lineitem"], ["l_shipdate"]));
        let scale: crate::controller::request::EngineScale = serde_json::from_value(serde_json::json!({"name":"sf1","locations":{},"prepared_workload":"/p","bindings":"/b",
            "targets":"/t","saved_answers":[],"original_data_bytes":1_100_693_130u64,"original_data_record":"/g.json"})).unwrap();
        let plain_storages = std::collections::BTreeSet::from([gendb_artifacts::ContentId::from_bytes([7; 32])]);
        let inputs = crate::engine::role::GeneralInputs { scale, plain_storages, plain_storage_bytes: 1_586_435_879, scale_index: 0, scales: 3, next_scale: Some("sf10".into()), call_limits: gendb_runtime::worker::CallLimits::GENERAL_ENGINE, timed_calls: 3,
            branches: vec!["b1".into(), "b2".into(), "b3".into()], budget_usd: crate::controller::limits::Money::parse("1000").unwrap(), emphasis: None, seed: None };
        let g = GeneralContract { engine_dir: &run.engine_dir, rules: &rules_set, inputs: &inputs };
        let contract = Path::new("/w/contract/engine");
        let task = general::task(Path::new("/w"), Path::new("/w/verus-engine-example.json"), &g);
        assert!(task["manifest"]["schema"]["properties"]["next_session"].is_object() && task["generated_access"]["engine_crate"]["module"] == "crate::flat_tables");
        let index = general::index(Path::new("/w"), contract, &g);
        assert_eq!((index["scope"].as_str(), index["inputs"]["tree"].as_str()), (Some("verus_general_engine"), run.engine_dir.join("TREE.md").to_str()));
        assert!(index["output"]["manifest"]["properties"]["direction"].is_object());
        let rules = general::rules(&g);
        assert!(rules["whole_query_evaluator"].is_null() && rules["interpreter"]["allowed"] == true);
        let ids: Vec<&str> = rules["engine_rules"]["rules"].as_array().unwrap().iter().filter_map(|r| r["id"].as_str()).collect();
        assert_eq!(ids, ["template_constant", "ast_fragment_table", "schema_name"]);
        assert!(rules["engine_rules"]["rules"].as_array().unwrap().iter().all(|r| !r["reason"].as_str().unwrap().contains("design ")), "no design reference in the rule texts");
        assert!(rules["engine_rules"]["rules"][2]["reason"].as_str().unwrap().starts_with("generality: main-line engine code works for any schema"));
        assert_eq!(rules["engine_rules"]["rule_set"]["line"], "general");
        let classes = general::failure_classes(&g);
        assert!(classes["named_reasons"]["whole_statement_evaluator"].is_null() && classes["named_reasons"]["schema_name"].is_string() && classes["named_reasons"]["over_time_limit"].is_string());
        let performance = general::performance(&training, &[1, 32, 64], &g);
        assert!(performance["stop_rule"].is_null() && performance["official_matrix"].is_null());
        assert_eq!(performance["submission_timing"]["rule"], crate::engine::race::RACE_RULE);
        assert_eq!(performance["score"]["rule"], crate::engine::score::SCORE_RULE);
        assert_eq!((performance["call_limits"]["call_limit_seconds"].as_u64(), performance["call_limits"]["anon_memory_limit_bytes"].as_u64()), (Some(60), Some(154_618_822_656)));
        assert_eq!(performance["sampling_profile"]["method"], crate::engine::profile::PROFILE_METHOD);
        assert!(general::tools_file(&training, &[1, 32, 64], &g)["tools"]["profile"].as_str().unwrap().contains("sampled self time"));
        let sql = general::tools_file(&training, &[1, 32, 64], &g)["arguments"]["sql"].as_str().unwrap().to_string();
        assert!(sql.contains("stored up to at most 100 rows and 1048576 bytes of row text") && sql.contains("the rest is not stored"), "{sql}");
        // The general line's registry lists the definitions generated when the storages call for them (the flat access);
        // the schema line's registry is the same as before.
        let schema_registry = registry();
        let general_registry = general::registry(registry());
        let paths = |key: &str| -> Vec<String> { general_registry[key].as_array().unwrap().iter().map(|d| d["crate_path"].as_str().unwrap().to_string()).collect() };
        assert_eq!(paths("engine_crate_when_its_storages_call_for_it"), ["flat_tables.rs", "flat_tables/plain.rs"]);
        assert_eq!(paths("storage_crate_built_from_admitted_storages"),
            ["sources_flat.rs", "sources_flat/plain.rs", "stores/<storage>/interface/plain.rs", "gendb_entry/sources.rs", "gendb_entry/derivation.rs"]);
        assert_eq!(general_registry["plain_columns_file"], PLAIN_COLUMNS_CONTRACT_FILE);
        assert_eq!(general_registry["engine_crate_when_its_storages_call_for_it"][0]["presence"], serde_json::json!({"optional":"engine"}));
        assert!(general_registry["engine_crate"] == schema_registry["engine_crate"] && schema_registry.get("engine_crate_when_its_storages_call_for_it").is_none());
        // The budget is the original data size at the scale, as in the template runs; the plain
        // storage is allowed as is and reported beside it.
        let budget = general::budget_rule(&g);
        assert_eq!((budget["budget_bytes"].as_u64(), budget["plain_storage"]["bytes"].as_u64()), (Some(1_100_693_130), Some(1_586_435_879)));
        assert_eq!((budget["plain_storage"]["times_original"].as_str(), budget["plain_storage"]["storages"][0].as_str()), (Some("1.44"), Some("07".repeat(32).as_str())));
        let rule = budget["rule"].as_str().unwrap();
        assert!(rule.contains("reads only the plain storage is allowed as is") && rule.contains("at most the original data size of the scale") && budget["last_scale"].is_null(), "{budget}");
        let mut data = serde_json::json!({});
        general::add_data_facts(&mut data, &g);
        assert_eq!((data["storage_budget"]["budget_bytes"].as_u64(), data["storage_budget"]["plain_storage_bytes"].as_u64()), (Some(1_100_693_130), Some(1_586_435_879)));
        assert!(!general::performance(&training, &[1, 32, 64], &g)["scale_ladder"]["rule"].as_str().unwrap().contains("budget"), "the ladder has no budget condition");
        let versions = general::versions_markdown(&g, &training);
        assert!(versions.contains("## Scale sf1") && versions.contains("| Umbra | baseline | - | 340.000 | 22.800 | 28.400 |"), "{versions}");
        assert!(versions.contains("v001](") && versions.contains("10050.000 (29.559)") && versions.contains("| b1-a002 | b1 | v001 | - | refusal: schema_name"), "{versions}");
        assert!(task["manifest"]["schema"]["properties"]["base"].is_object() && performance["main_line"].as_str().unwrap().contains("over all branches"), "several branches keep base and the main line");
        // One line (one branch): no rebase in the manifest schema, the direction is one short line, and the main line is
        // the line of versions, each built on the head.
        let one = crate::engine::role::GeneralInputs { branches: vec!["b1".into()], ..inputs.clone() };
        let one_line = GeneralContract { engine_dir: &run.engine_dir, rules: &rules_set, inputs: &one };
        let task = general::task(Path::new("/w"), Path::new("/w/verus-engine-example.json"), &one_line);
        let properties = &task["manifest"]["schema"]["properties"];
        assert!(properties["base"].is_null() && properties["direction"]["description"].as_str().unwrap().starts_with("optional: one short line"), "{properties}");
        assert!(general::index(Path::new("/w"), contract, &one_line)["output"]["manifest"]["properties"]["base"].is_null());
        let performance = general::performance(&training, &[1, 32, 64], &one_line);
        assert!(performance["main_line"].as_str().unwrap().starts_with("one line of versions: each version builds on the best version"), "{}", performance["main_line"]);
        assert!(!performance["scale_ladder"]["rule"].as_str().unwrap().contains("main-line"));
        assert!(general::failure_classes(&one_line)["named_reasons"]["not_better_than_parent"].as_str().unwrap().ends_with("the head stays"));
        std::fs::remove_dir_all(&root).ok();
    }

    /// Writes a stage run's contract files (one line, the fixture's workloads) under
    /// `GENDB_GENERAL_RENDER_DIR/stage-contract/` for review: `stage.json`, every workload's files, and the task, index,
    /// rules, failure classes, performance and tools files with the stage's parts.
    #[test]
    #[ignore = "writes the stage contract under GENDB_GENERAL_RENDER_DIR for review"]
    fn write_stage_contract_render() {
        use gendb_verification::verus::engine_rules::{EngineRuleSet, SchemaNames, TemplateConstants};
        let out = std::path::PathBuf::from(std::env::var("GENDB_GENERAL_RENDER_DIR").expect("GENDB_GENERAL_RENDER_DIR")).join("stage-contract");
        std::fs::remove_dir_all(&out).ok();
        let stage_contract = stage::tests::fixture_stage(&out.join("fixture"));
        let contract = out.join("w").join(CONTRACT_DIRECTORY);
        let files = stage::write_workload_files(&contract, &stage_contract).unwrap();
        let run = crate::prompts::engine_facts::general::tests::scripted_run(&out.join("fixture/scripted"));
        let training = &stage_contract.workloads[0].training;
        let rules_set = EngineRuleSet::general_with_names(TemplateConstants::from_texts(&[]).unwrap(), SchemaNames::from_names(["t"], ["c_one"]));
        let scale: crate::controller::request::EngineScale = serde_json::from_value(serde_json::json!({"name":"sf3","locations":{},"prepared_workload":"/p","bindings":"/b",
            "targets":"/t","saved_answers":[],"original_data_bytes":5_439_582_957u64,"original_data_record":"/export.report.json"})).unwrap();
        let inputs = crate::engine::role::GeneralInputs { scale, plain_storages: Default::default(), plain_storage_bytes: 7_746_659_210, scale_index: 0, scales: 1, next_scale: None,
            call_limits: gendb_runtime::worker::CallLimits::GENERAL_ENGINE, timed_calls: 3, branches: vec!["b1".into()], budget_usd: crate::controller::limits::Money::parse("1000").unwrap(), emphasis: None, seed: None };
        let g = GeneralContract { engine_dir: &run.engine_dir, rules: &rules_set, inputs: &inputs };
        let root = out.join("w");
        let shape = super::super::engine_general_sections::Shape::OneLine;
        let mut task = general::task(&root, &root.join("verus-engine-example.json"), &g);
        stage::amend_task(&mut task, &root, &contract, &stage_contract, shape);
        let mut index = general::index(&root, &contract, &g);
        stage::amend_index(&mut index, &contract, &stage_contract, shape);
        let mut rules = general::rules(&g);
        stage::amend_rules(&mut rules);
        let mut classes = general::failure_classes(&g);
        stage::amend_failure_classes(&mut classes);
        let mut performance = general::performance(training, &[1, 32, 64], &g);
        stage::amend_performance(&mut performance, &stage_contract);
        let mut tools = general::tools_file(training, &[1, 32, 64], &g);
        stage::amend_tools(&mut tools, &stage_contract);
        for (name, value) in [("task.json", task), ("index.json", index), ("rules.json", rules), ("failure-classes.json", classes), ("performance.json", performance), ("tools.json", tools)] {
            write(&contract.join(name), &value).unwrap();
        }
        println!("stage contract: {}; files.workloads: {}", contract.display(), serde_json::to_string_pretty(&files).unwrap());
    }

    /// Writes a run of several workloads' contract files (one line, the workloads fixture's workloads) under
    /// `GENDB_GENERAL_RENDER_DIR/workloads-contract/` for review: `workloads.json`, every workload's files, and the task,
    /// index, rules, failure classes, performance and tools files with the run's parts, and `storage-authoring.md`.
    #[test]
    #[ignore = "writes the contract of a run of several workloads under GENDB_GENERAL_RENDER_DIR for review"]
    fn write_workloads_contract_render() {
        use gendb_verification::verus::engine_rules::{EngineRuleSet, SchemaNames, TemplateConstants};
        let out = std::path::PathBuf::from(std::env::var("GENDB_GENERAL_RENDER_DIR").expect("GENDB_GENERAL_RENDER_DIR")).join("workloads-contract");
        std::fs::remove_dir_all(&out).ok();
        let set = workloads::tests::fixture_workloads(&out.join("fixture"));
        let contract = out.join("w").join(CONTRACT_DIRECTORY);
        let files = workloads::write_member_files(&contract, &set).unwrap();
        let run = crate::prompts::engine_facts::general::tests::scripted_run(&out.join("fixture/scripted"));
        let training = &set.members[0].inputs.training;
        let rules_set = EngineRuleSet::general_with_names(TemplateConstants::from_texts(&[]).unwrap(), SchemaNames::from_names(["t"], ["c_one"]));
        let scale: crate::controller::request::EngineScale = serde_json::from_value(serde_json::json!({"name":"sf100","locations":{},"prepared_workload":"/p","bindings":"/b",
            "targets":"/t","saved_answers":[],"original_data_bytes":114_641_618_862u64,"original_data_record":"/generation.json"})).unwrap();
        let inputs = crate::engine::role::GeneralInputs { scale, plain_storages: Default::default(), plain_storage_bytes: 158_618_806_633, scale_index: 1, scales: 2, next_scale: None,
            call_limits: gendb_runtime::worker::CallLimits::GENERAL_ENGINE, timed_calls: 3, branches: vec!["b1".into()], budget_usd: crate::controller::limits::Money::parse("1000").unwrap(), emphasis: None, seed: None };
        let g = GeneralContract { engine_dir: &run.engine_dir, rules: &rules_set, inputs: &inputs };
        let root = out.join("w");
        let shape = super::super::engine_general_sections::Shape::OneLine;
        let mut task = general::task(&root, &root.join("verus-engine-example.json"), &g);
        workloads::amend_task(&mut task, &root, &contract, &set, shape);
        let mut index = general::index(&root, &contract, &g);
        workloads::amend_index(&mut index, &contract, &set, shape);
        let mut rules = general::rules(&g);
        workloads::amend_rules(&mut rules);
        let mut classes = general::failure_classes(&g);
        workloads::amend_failure_classes(&mut classes);
        let mut performance = general::performance(training, &[1, 32, 64], &g);
        workloads::amend_performance(&mut performance, &set);
        let mut tools = general::tools_file(training, &[1, 32, 64], &g);
        workloads::amend_tools(&mut tools, &set);
        let mut registry_file = general::registry(registry());
        workloads::amend_registry(&mut registry_file);
        for (name, value) in [("task.json", task), ("index.json", index), ("rules.json", rules), ("failure-classes.json", classes), ("performance.json", performance), ("tools.json", tools),
            ("registry.json", registry_file)] {
            write(&contract.join(name), &value).unwrap();
        }
        write_text(&contract.join(super::super::engine_general_sections::STORAGE_AUTHORING_FILE), &(general::storage_authoring(true) + workloads::FAMILY_AUTHORING)).unwrap();
        println!("workloads contract: {}; files.workloads: {}", contract.display(), serde_json::to_string_pretty(&files).unwrap());
    }

    #[test]
    fn templates_and_versions_render_as_markdown_tables() {
        let training = serde_json::json!({"timing_binding":"v0","templates":[{"name":"Q01","tables":["lineitem"],"sql":"SELECT 1","parameters":[{"index":1,"name":"delta","type":"date"}],
            "bindings":[{"name":"v0","arguments":["1998-09-02"]}],"baselines":[{"binding":"v0","workers":1,"umbra_ns":1_500_000,"duckdb_ns":2_000_000,"agreement":"exact-order"}]}]});
        let md = templates_markdown(&training);
        assert!(md.contains("## Q01") && md.contains("```sql\nSELECT 1\n```") && md.contains("| v0 | 1998-09-02 | 1 | 1.500 | 2.000 | exact-order |"), "{md}");
        let versions = [serde_json::json!({"version":"v1","round":2,"directory":"/v1","totals":{"workers":[{"workers":1,"engine_ns":3_000_000}],
            "templates":[{"template":"Q01","workers":1,"engine":{"median_ns":3_000_000}}]}})];
        let md = versions_markdown(&versions, &training);
        assert!(md.contains("## v1 (round 2)") && md.contains("| Q01 | 3.000 |") && md.contains("| **Total** | 3.000 |"), "{md}");
    }
}
