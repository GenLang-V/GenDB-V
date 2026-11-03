//! The contract files of a run of several workloads (one engine, general for any
//! schema, data and query of SQLSpec, tuned for the counted workloads). The primary workload's contract is the general
//! line's (`prompts::engine_contract::general`), written over the primary's inputs; a run of several workloads
//! ([`WorkloadsContract`], `prompts::engine_contract::write_workloads_engine_contract`) changes it as follows, on the
//! general and stage generators, so every shared fact stays one text:
//!
//! - `workloads.json` ([`workloads_record`]): every workload with its role (`counted`, `check`, `kept`), whether it is
//!   the primary, its scale, library and files; the root's sides; one engine as one crate per workload; storage
//!   families, the default module and plans; the user's transition; the evaluation's order; the combined score; the
//!   rules; the tools' `workload` argument;
//! - `workloads/<name>/` per workload (`stage::write_one_workload`): its templates, data, constraints, budget rule,
//!   bindings, baselines (a check workload has none) and, for every workload but the primary, its storages catalog;
//! - `task.json` and `index.json`: the task, ownership of the default module, the workloads' modules, the families and
//!   the plans, the manifest schema of a run of several workloads (`EngineManifest::members_schema`), the family
//!   manifest's schema (`storage::family::FamilyManifest::schema`), the generated access of every crate, the fixed files
//!   per crate and per family instance, and the run's files;
//! - `rules.json`, `failure-classes.json`, `performance.json` and `tools.json`: the rules of such a run
//!   (`MEMBER_ENGINE_RULES`: the stage rules and R3-R5, with R6 the check workloads in words), the
//!   workloads' outcomes in an evaluation (the workloads fixture `members[].status`), the evaluation's order and the combined
//!   score, no ladder, and the `workload` argument;
//! - `storage-authoring.md` gains the section on storage families ([`FAMILY_AUTHORING`]) and `registry.json` the
//!   whole-schema files of a family's instance ([`amend_registry`]).
//!
//! What a workload contributes is plain data ([`MemberContract`], with the stage's [`WorkloadContract`] for its inputs),
//! so the texts are tested from the workloads fixture; [`MemberContract::prepare`] reads it from a workload's prepared inputs,
//! its capture and its library.

use super::super::brief::common::write;
use super::general::{GeneralContract, rule_texts};
use super::stage::{UNIFORM_ACCESS, WORKLOADS_DIRECTORY, WorkloadContract, WorkloadRole, files_of, write_one_workload};
use crate::controller::request::MemberRole;
use crate::engine::role::EngineInputs;
use crate::engine::submission::EngineManifest;
use crate::prompts::engine_general_sections::Shape;
use crate::storage::family::{DEFAULT_PLAN_FILE, FAMILY_MANIFEST_FILE, FamilyManifest};
use crate::storage::policy::StoredDataPolicy;
use gendb_artifacts::ObjectStore;
use gendb_storage::import::PreparedSource;
use gendb_verification::admission::AdmissionError;
use gendb_verification::verus::engine_rules::{
    DEFAULT_MODULE_DIRECTORY, MEMBER_ENGINE_RULES, PLAN_FILE_PATTERN, SCHEMA_COLUMN_MENTION, SCHEMA_TABLE_MENTION,
};
use serde_json::{Value, json};
use std::path::Path;

/// The run's file in the contract directory.
pub const WORKLOADS_FILE: &str = "workloads.json";

/// One workload of a run of several workloads as its contract files need it: its role, whether it is the primary, and
/// its inputs as a stage workload's (`inputs.role` is `Goal` for the primary, whose storages catalog is the contract's
/// own, and `Kept` for every other workload, which gets its own catalog; the role that decides is `role`).
#[derive(Clone, Debug)]
pub struct MemberContract {
    pub role: MemberRole,
    pub primary: bool,
    pub inputs: WorkloadContract,
}

impl MemberContract {
    /// The contract data of the workload `name` (`WorkloadContract::prepare`, as a stage workload's: the primary as the
    /// goal, every other workload as a kept one, so it gets its own storages catalog).
    #[allow(clippy::too_many_arguments)]
    pub fn prepare(root: &Path, name: &str, role: MemberRole, primary: bool, inputs: &EngineInputs, capture: &PreparedSource, store: &ObjectStore, policy: &StoredDataPolicy,
        library: &Path, first_scale: &str) -> Result<Self, AdmissionError> {
        let side = if primary { WorkloadRole::Goal } else { WorkloadRole::Kept };
        Ok(MemberContract { role, primary, inputs: WorkloadContract::prepare(root, name, side, inputs, capture, store, policy, library, first_scale)? })
    }

    fn name(&self) -> &str {
        &self.inputs.name
    }
}

/// What a run of several workloads adds to the general line's contract inputs.
#[derive(Clone, Debug)]
pub struct WorkloadsContract {
    /// The primary workload's name (`engine.workloads.name`).
    pub primary: String,
    /// Each workload's seed as the request gives it (`{run, version, workload?}`, `{source}`, or null without one), by
    /// name.
    pub seeds: Value,
    /// Every workload, the primary first.
    pub members: Vec<MemberContract>,
}

impl WorkloadsContract {
    fn names(&self, role: MemberRole) -> Vec<&str> {
        self.members.iter().filter(|m| m.role == role).map(MemberContract::name).collect()
    }
}

/// Every workload's files (`files.workloads`: by workload, then by file).
pub fn members_files(contract: &Path, set: &WorkloadsContract) -> Value {
    Value::Object(set.members.iter().map(|m| (m.name().to_string(), files_of(contract, &m.inputs))).collect())
}

/// Write every workload's files under `<contract>/workloads/<name>/` and `workloads.json` (module documentation); returns
/// `files.workloads`.
pub fn write_member_files(contract: &Path, set: &WorkloadsContract) -> Result<Value, AdmissionError> {
    for member in &set.members {
        write_one_workload(contract, &member.inputs)?;
    }
    write(&contract.join(WORKLOADS_FILE), &workloads_record(contract, set))?;
    Ok(members_files(contract, set))
}

/// One engine as one crate per workload, as the contract states it.
const ONE_ENGINE: &str = "src/agent/** is the engine, shared by every workload. At freeze GenDB composes one crate per workload: src/agent/**, that workload's module copied in as src/agent/workload/** (its own workloads/<name>/** where workload_module_scope allows one, else the shared default module workloads/default/**), and the instances of the storage families it reads, every framework file generated for that workload's schema, storages and declared constraints; each crate is verified whole against gendb-verus-engine-entry-v1. Shared code reaches the module as crate::agent::workload::..., so every module offers the items the shared code calls; rustc checks each crate; src/agent/workload must not exist in the workspace. One engine means the same src/agent/** and workloads/default/** bytes in every crate and the same family sources in every instance: a recorded digest (version.json general.shared_digest), not a theorem";
/// Storage families, the default module and plans, as the contract states them.
const FAMILIES: &str = "a storage you add is a storage family (storage_family_required): one shared builder and interface under storages/<family>/ (verus-family.json, <crate_dir>/src/builder/**, <crate_dir>/src/stores/<family>/interface/**, default_plan.rs), whose store is crate::stores::<family> in every instance. GenDB composes it into each workload that names it in its storage_uses ({name, family}) as one storage over that workload's whole schema: every table and column, built from that workload's plain flat storages, the part template of verus-family.json expanded in table and column order, builder/plan.rs from the workload's plan or the family's default plan, and two generated files checked by Verus in the instance (schema_exec.rs, crate::schema_exec: each column's type and nullability at run time; whole_schema.rs, crate::whole_schema: lemma_<family>, the store's relations are every table of the schema). The instance is then an ordinary storage: verified whole, built in the workload's library, checked against the policy, one copy and the budget, admitted. The detail: storage-authoring.md, section Storage families";
const DEFAULT_MODULE: &str = "workloads/default/** is shared code, scanned like src/agent/** with workload_module_statement: it opens the family stores (before the first family, the plain flat storages) by table id, for any schema; every workload without a module of its own uses it";
const PLANS: &str = "a workload tunes a family only through its plan plans/<workload>/<family>.rs (else the family's default_plan.rs): data only (plan_is_data), checked by the family's builder at run time (an inapplicable entry is ignored, never unsound), never read by the engine, which learns the layout from the stored parts. A new schema needs no code, only an optional plan";
/// The user's transition, as the contract states it.
const TRANSITION: &str = "by the end, every workload is served by the default module over storage families. The start version is not general: its workload-specific storages and the own modules that open them are allowed only as inherited and are to be replaced early: put a workload on a family, rebuild its storages with the family's builder at its scale, then delete its own module (workload_module_scope then requires it). Every version on the way stays verified and correct on every workload; version.json general.one_engine records whether a version is one engine";
/// The order of a submission's evaluation.
const EVALUATION: [&str; 9] = [
    "freeze every workload's crate (manifest, each workload's storage uses and family instances, coverage, the source rules over every crate, composition); a refusal is an attempt",
    "Verus on every workload's whole crate, --no-cheating, 0 errors (gating)",
    "every workload's storages in its library: new storages and family instances built, the storage policy, single copy and the budget (gating; a check workload is exempt from the budget)",
    "every check workload: every template at every visible binding at the smallest and the largest configured worker count, one call each, every answer against the saved answers, before any timing (gating; a wrong answer is also flagged for the operator)",
    "every counted workload: the interleaved timing against the parent's side of that workload at its scale (performance.json submission_timing), every answer checked",
    "the combined decision (performance.json workloads.score): not better, an attempt with every workload's timing recorded; the kept workloads are not timed (members[].status not_run)",
    "every kept workload: the interleaved timing against the parent's side of that workload at its scale (recorded and shown, never deciding; a wrong answer refuses and is flagged)",
    "every workload's variants at its first scale, one call each at 64 workers, for their answers (gating)",
    "admission of every workload's crate in its library with the same lineage (version id, parents), selected in every library; one version folder with every workload's records (version.json workloads, combined_score, general)",
];
/// The combined score, as the contract states it.
const SCORE: &str = "per counted workload, its score (performance.json score.rule) at its scale from its same-window timing against the parent's side: F_w its finished cells, G_w its normalized time; the combined F is the sum of F_w and the combined G the sum of G_w over the counted workloads, in exact billionths. Better means a larger combined F, or the same F and a smaller combined G. There is no guard per workload: a loss on one workload that a larger gain on another outweighs is accepted, and every workload's score, totals and ratios are recorded (version.json workloads) and shown (CURRENT FACTS, TREE.md, FINDINGS.md). The user asks that the engine not lose its performance on any workload";

/// `workloads.json` (module documentation).
pub fn workloads_record(contract: &Path, set: &WorkloadsContract) -> Value {
    let workloads: Vec<Value> = set.members.iter().map(|m| json!({"name":m.name(),"role":m.role.name(),"primary":m.primary,"scale":m.inputs.scale,"first_scale":m.inputs.first_scale,
        "library":m.inputs.library,"seed":set.seeds[m.name()],"files":files_of(contract, &m.inputs)})).collect();
    json!({"format_version":1,"primary":set.primary,"workloads":workloads,
        "roles":{"counted":"in the acceptance and the combined score","check":"verified whole and every template answered at every visible binding by every submission, before any timing (gating); never timed, not in the score, no budget rule","kept":"verified and timed against the parent's side of that workload for every accepted version and shown, never deciding"},
        "root":"the root v000 has one side per workload: a workload with a seed gets that seed's code, module and storages, verified whole and timed alone (a check workload: answered) when the run was prepared; a workload without one gets the primary seed's code where it verifies there, else GenDB's version 0. The workspace starts from the primary's side with its notebook; every other side's code, module, storage author files, notebook and manifest are read-only under root-sides/<name>/, the sides' common ancestor's code under root-sides/ancestor/ when GenDB found one",
        "one_engine":ONE_ENGINE,"families":FAMILIES,"default_module":DEFAULT_MODULE,"plans":PLANS,"transition":TRANSITION,"evaluation":EVALUATION,"score":SCORE,
        "rules":workloads_rules(),
        "tools":"every engine and storage tool takes workload (default: the primary): which crate, data, library and saved answers a job uses",
        "meaning":"a run of several workloads of the general line (engine.workloads): one engine for every workload, each with its own crate, library, storage budget and saved answers"})
}

/// The rules of a run of several workloads in words, as `rules.json` and `workloads.json` state them.
fn workloads_rules() -> Value {
    json!({"names":"the schema-name rule covers the table and column names of every workload's schema, the check workloads' included; template constants are those of every workload's templates",
        "one_word_column_names":"a column name of one word (no _) is refused only inside a string, byte string or char literal (as a whole word); as an identifier or an identifier segment it is reported, not refused",
        "workload_module_statement":"gating: files under agent/workload/ (the default module or a workload's own module in its crate) name no statement type or AST path (EOrderedQuery, EQuery, EPred, EExpr, exec::ast, spec::ast and the like)",
        "storage_family_required":"gating: every storage a submission adds is a family use; a workspace storage of one workload is refused; uses of admitted packages (inherited storages, admitted family instances, plain flat storages) stay allowed",
        "plan_is_data":"gating: a plan and a default plan are data only (rules.json engine_rules)",
        "workload_module_scope":"gating: an own module workloads/<name>/ only beside an inherited storage that is neither a family instance nor a plain flat storage",
        "check_workloads":"gating: every check workload's crate verifies whole and every template at every visible binding agrees with the saved answers",
        "workload_directory":"src/agent/workload in the workspace is refused: GenDB composes it per crate",
        "default_module_directory":DEFAULT_MODULE_DIRECTORY,"plan_file":PLAN_FILE_PATTERN})
}

/// The generated files of a family instance, as `task.json` and `index.json` state them.
const FAMILY_ACCESS: &str = "every family instance's storage crate carries, besides the derived storage entry's files, the crate-root modules schema_exec.rs (crate::schema_exec, schema_exec(): every table's columns with their types and nullability, the text engine crates carry as gendb_entry/schema_exec.rs) and whole_schema.rs (crate::whole_schema: TABLE_COUNT, stored_type, lemma_schema_shape for the schema's table count, column counts and stored types, and lemma_<family>(db): the instance's stored relations are every table of the workload's schema, table for table), both generated per workload and checked by Verus (registry.json family_instance_whole_schema_files); the engine crate of a workload reading a family instance carries whole_schema.rs too. Its crate::sources_flat (the flat sources by table and column id) always carries the nullable items, whatever the schema, as an engine crate's crate::flat_tables does (generated_access.stage): nullable_column(t, c) is false for every column of a schema without nullable columns. So a builder over crate::sources_flat and an opener over the store are written by table id, for any table count, and one builder text compiles in every instance";

/// `task.json` of a run of several workloads: the general task file with the run's task, ownership, manifest schema,
/// family manifest schema, generated access, fixed files per crate and family instance, and the run's files.
pub fn amend_task(task: &mut Value, root: &Path, contract: &Path, set: &WorkloadsContract, shape: Shape) {
    let names = |role: MemberRole| -> String {
        let names = set.names(role);
        if names.is_empty() { "none".to_string() } else { names.join(", ") }
    };
    task["task"] = json!(format!(
        "Build one verified engine for every workload of this run: faster than the best of DuckDB and Umbra on the training templates of every counted workload ({}) at every worker count; first finish every template within the call limit at its scale, then reduce the total time; the combined score over the counted workloads decides every submission. Every submission verifies and agrees with the saved answers on every workload, the check workloads ({}) included; kept workloads ({}) are timed and shown, never deciding. crate::agent::engine answers every supported query (wf_ordered over each workload's schema) over that workload's stored data, proved against the fixed engine entry in every workload's crate; new storage is a storage family, a workload's tuning is a plan; submit your verus-engine.json once it holds several verified improvements",
        names(MemberRole::Counted),
        names(MemberRole::Check),
        names(MemberRole::Kept)
    ));
    let crate_dir = root.join(crate::engine::submission::CRATE_DIRECTORY);
    task["you_own"] = json!([crate_dir.join("src/agent"), crate_dir.join(WORKLOADS_DIRECTORY), crate_dir.join(crate::engine::submission::PLANS_DIRECTORY), root.join("storages")]);
    task["manifest"]["schema"] = members_manifest_schema(shape);
    task["family_manifest"] = json!({"file":FAMILY_MANIFEST_FILE,"default_plan":DEFAULT_PLAN_FILE,"convention":"storages/<family>/verus-family.json, named in the engine manifest's families[]","schema":FamilyManifest::schema()});
    task["generated_access"]["stage"] = json!(UNIFORM_ACCESS);
    task["generated_access"]["family_instances"] = json!(FAMILY_ACCESS);
    super::general::add_nullable_access(&mut task["generated_access"]);
    task["fixed_files"]["per_workload"] = json!("each workload's crate has these framework files, generated for its own schema, storages and declared constraints; src/agent/** and its module (workloads/<name>/** or workloads/default/**, copied in as src/agent/workload/**) are yours");
    task["fixed_files"]["per_family_instance"] = json!("each family instance's storage crate has the derived storage entry's framework files and the two generated files of generated_access.family_instances; its builder/plan.rs is GenDB's slot (the workload's plan or the family's default plan); the family's builder and interface are yours");
    task["workloads"] = json!({"file":contract.join(WORKLOADS_FILE),"one_engine":ONE_ENGINE,"families":FAMILIES,"default_module":DEFAULT_MODULE,"plans":PLANS,"transition":TRANSITION});
}

/// The manifest's schema in a run of several workloads as the author reads it: `EngineManifest::members_schema`
///, on one line without `base`, as the general line's.
fn members_manifest_schema(shape: Shape) -> Value {
    let mut schema = EngineManifest::members_schema();
    GeneralContract::one_line_schema(&mut schema, shape);
    schema
}

/// `index.json` of a run of several workloads: the run's files in the inputs and the read order, the manifest schema
/// and the generated access.
pub fn amend_index(index: &mut Value, contract: &Path, set: &WorkloadsContract, shape: Shape) {
    index["task"] = json!("Build one verified engine faster than the best of DuckDB and Umbra on every counted workload's training templates at every worker count, every workload verified and correct, the check workloads included (contract task.json, workloads.json); every submission is judged by the combined score of one interleaved timing per counted workload against the parent's side of it");
    if let Some(order) = index["read_order"].as_array_mut() {
        order.insert(1, json!("workloads"));
    }
    index["inputs"]["workloads_record"] = json!(contract.join(WORKLOADS_FILE));
    index["inputs"]["workloads"] = members_files(contract, set);
    index["output"]["manifest"] = members_manifest_schema(shape);
    index["generated_access"]["stage"] = json!(UNIFORM_ACCESS);
    index["generated_access"]["family_instances"] = json!(FAMILY_ACCESS);
    super::general::add_nullable_access(&mut index["generated_access"]);
}

/// `rules.json` of a run of several workloads: its rule set (`MEMBER_ENGINE_RULES`), its reports, and its rules in
/// words.
pub fn amend_rules(rules: &mut Value) {
    let engine_rules = &mut rules["engine_rules"];
    engine_rules["line"] = json!("general, several workloads");
    engine_rules["rules"] = json!(rule_texts(MEMBER_ENGINE_RULES));
    engine_rules["scope"] = json!("at freeze (the check tool and every submission) and again at admission, in every workload's crate: template constants of every workload, AST fragments and the schema-name rule over every agent/ file and every family's builder and interface, the workload-module rule over agent/workload/ (the default module or a workload's own module), the plan rule over every plan and default plan, the family rule over every workload's storage uses, the module-scope rule per workload; no static item (no state between calls)");
    engine_rules["reported"] = json!([
        {"id":SCHEMA_TABLE_MENTION,"meaning":"a table name of a workload's schema as a word or segment of an identifier outside literals and storage paths: reported with the evaluation, never refused"},
        {"id":SCHEMA_COLUMN_MENTION,"meaning":"a one-word column name of a workload's schema as an identifier or a segment of one: reported with the evaluation, never refused"},
        {"id":"workload_module_report","meaning":"each workload's own module lines, item kinds, loops and the storages it names, its inherited storages and its plans' size, with every freeze and admission (version.json workloads.<name>.general)"}]);
    engine_rules["workloads"] = workloads_rules();
}

/// `failure-classes.json` of a run of several workloads: its refusals and reports, and the workloads' outcomes as the
/// evaluation records them (`members[].status`, the workloads fixture).
pub fn amend_failure_classes(classes: &mut Value) {
    let named = &mut classes["named_reasons"];
    named["workload_module_statement"] = json!("refusal (engine rules): a file under agent/workload/ names a statement type, an AST path or the AST codec (rules.json engine_rules)");
    named["storage_family_required"] = json!("refusal (engine rules): a submission adds a storage that is not a family use");
    named["plan_is_data"] = json!("refusal (engine rules): a plan or a default plan holds code, not data");
    named["workload_module_scope"] = json!("refusal (engine rules): a workload has a module of its own while it reads only family instances and plain flat storages");
    named[SCHEMA_COLUMN_MENTION] = json!("report only: a one-word column name of a workload's schema in an identifier; never refused");
    classes["member_outcomes"] = json!({"not_run":"not evaluated: an earlier step refused the submission, or (a kept workload) the combined score was not better",
        "refused":"this workload's step refused the submission; step names it (freeze, verus, storages, answers, timing, variants) and reason its first line; a wrong answer is also flagged for the operator",
        "checked":"a check workload: verified whole and every template answered at every visible binding with the saved answers",
        "timed":"verified, its storages checked and timed against the parent's side of that workload (race: its race.json); a counted workload's score is part of the combined decision, a kept workload's is recorded and shown",
        "where":"the evaluation record's members[] (name, role, status, step, reason, race, check) and combined (parent, candidate, better), shown in the evaluation of the submission"});
}

/// `performance.json` of a run of several workloads: the evaluation's order and the combined score; no ladder.
pub fn amend_performance(performance: &mut Value, set: &WorkloadsContract) {
    performance["workloads"] = json!({"evaluation":EVALUATION,"score":SCORE,
        "workloads":set.members.iter().map(|m| json!({"name":m.name(),"role":m.role.name(),"primary":m.primary,"scale":m.inputs.scale,"first_scale":m.inputs.first_scale})).collect::<Vec<_>>()});
    performance["scale_ladder"]["rule"] = json!("off in a run of several workloads: each workload stays at its scale (workloads.json); no scale move");
}

/// `registry.json` of a run of several workloads: the general line's index plus the whole-schema files of a storage
/// family's instance (`gendb_registry::WHOLE_SCHEMA_DEFINITIONS`: `whole_schema.rs` in the instance's storage crate and in
/// the engine crates that read it, `schema_exec.rs` in the storage crate).
pub fn amend_registry(registry: &mut Value) {
    let rows: Vec<Value> = gendb_registry::DEFINITIONS.iter().filter(|d| gendb_registry::WHOLE_SCHEMA_DEFINITIONS.contains(&d.name)).map(super::registry_row).collect();
    registry["family_instance_whole_schema_files"] = json!(rows);
    registry["family_instance_whole_schema_meaning"] = json!("generated only for a storage that stores every column of every table in table and column order (a storage family's instance) and for the engine crates that read one, and checked by Verus with the crate (no trust); in no storage closure");
}

/// `tools.json` of a run of several workloads: the tools' `workload` argument.
pub fn amend_tools(tools: &mut Value, set: &WorkloadsContract) {
    tools["arguments"]["workload"] = json!({"meaning":"every engine and storage tool, optional (default: the primary workload): which workload's crate (src/agent/** with its module and family instances), data, library and saved answers the job uses; templates, binding and sql are that workload's","values":set.members.iter().map(|m| m.name().to_string()).collect::<Vec<_>>()});
}

/// The section `storage-authoring.md` gains in a run of several workloads: how to write a storage
/// family, how GenDB composes it, the plan and the default module.
pub const FAMILY_AUTHORING: &str = r#"
## Storage families (a run of several workloads)

In a run of several workloads every storage you add is a **storage family**: written once, composed by GenDB into every workload that uses it (`storage_family_required`).

- **Files.** `storages/<family>/verus-family.json` (its schema: `task.json` `family_manifest`), the builder `<crate_dir>/src/builder/**` and the interface `<crate_dir>/src/stores/<family>/interface/**` inside the family's directory, and `default_plan.rs` beside the manifest. The engine manifest names the family in `families[]` (`{name, source}`) and each workload that reads it in its `storage_uses` (`{"name": <family>, "family": <family>}`).
- **One text in every instance.** The builder and the interface name their store `crate::stores::<family>`; the instance's storage name is the family's name, so the same text compiles in every workload's instance and engine crate.
- **The part template.** `verus-family.json` declares the parts of every table, the parts of every column by its type class (int4, int8, numeric, date, text-like) and the extra parts of a nullable column, each with a label pattern (`{table}`, `{column}`) and a kind. GenDB expands it over the workload's schema in table and column order into the instance's `verus-storage.json` (`parts`, `data_policy`), with `tables` = every table and column (a whole-schema storage) and `built_from` = the workload's plain flat storages. Contents may vary with the data and the plan; the slots may not: an unused slot is an empty part.
- **Generated files.** Each instance's crate carries `schema_exec.rs` (`crate::schema_exec`: each column's type and nullability at run time) and `whole_schema.rs` (`crate::whole_schema`: `TABLE_COUNT`, `stored_type`, `lemma_schema_shape` for the schema's table count, column counts and stored types, and `lemma_<family>(db)`, the instance's relations are every table of the schema, table for table), both generated for the workload's schema and checked by Verus; the engine crate of a workload that reads the instance carries `whole_schema.rs` too. Write the builder over `crate::sources_flat` and the generated schema, by table id and column id, never by name (the schema-name rule covers the family's files).
- **Plans.** `builder/plan.rs` of an instance is the workload's plan `plans/<workload>/<family>.rs`, else `default_plan.rs`: one `pub fn plan()` whose body is data (`plan_is_data`). The builder checks the plan against the schema and the data at run time and ignores an inapplicable entry; the engine never reads the plan (it learns the layout from the stored parts).
- **Opening.** The default module `workloads/default/` opens the family's store as the engine's tables, by table id, for any schema; a workload reading only family and plain flat storages has no module of its own (`workload_module_scope`).
- **Then an ordinary storage.** Each instance is verified whole, built in its workload's library at that workload's scale, checked against the storage policy, one copy and the budget, and admitted; the sections above hold for it.
"#;

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::prompts::engine_facts::general::tests::workloads_run::fixture_at;
    use std::fs;
    use std::path::PathBuf;

    /// The fixture's workloads (the workloads fixture) as contract data, with stand-in data, constraints, budget and storages
    /// records and scale files under `root` (no capture or library is read; a check workload has no baselines).
    pub(crate) fn fixture_workloads(root: &Path) -> WorkloadsContract {
        let fixture = fixture_at(&root.join("run"));
        let members = fixture["context"]["workloads"].as_array().unwrap().iter().map(|w| {
            let name = w["name"].as_str().unwrap();
            let inputs = root.join("inputs").join(name);
            fs::create_dir_all(&inputs).unwrap();
            fs::write(inputs.join("visible.json"), "{\"queries\":{}}\n").unwrap();
            let role = match w["role"].as_str().unwrap() {
                "check" => MemberRole::Check,
                "kept" => MemberRole::Kept,
                _ => MemberRole::Counted,
            };
            let baselines = if role == MemberRole::Check { PathBuf::new() } else { inputs.join("targets.json") };
            if role != MemberRole::Check {
                fs::write(&baselines, "{}\n").unwrap();
            }
            let primary = w["primary"] == true;
            let workload = WorkloadContract { name: name.into(), role: if primary { WorkloadRole::Goal } else { WorkloadRole::Kept }, scale: w["scale"].as_str().unwrap().into(),
                first_scale: w["first_scale"].as_str().unwrap().into(), library: PathBuf::from(w["library"].as_str().unwrap()), training: w["training"].clone(),
                data: json!({"tables":[],"storage_budget":{"budget_bytes":w["budget"]["budget_bytes"]}}), integrity_constraints: json!({"declarations":[]}),
                budget_rule: json!({"budget_bytes":w["budget"]["budget_bytes"]}), storages: (!primary).then(|| json!({"storages":[]})), bindings: inputs.join("visible.json"), baselines };
            MemberContract { role, primary, inputs: workload }
        }).collect();
        let seeds = json!({"tpch":fixture["context"]["workloads"][0]["side_origin"]["seed"],"sec":fixture["context"]["workloads"][1]["side_origin"]["seed"],"anyschema":null});
        WorkloadsContract { primary: "tpch".into(), seeds, members }
    }

    /// A run of several workloads' contract: every workload's files (a check workload without
    /// baselines) and `workloads.json` with the roles, the root, the composition, families, the default module, plans,
    /// the transition, the evaluation's order, the combined score and the rules; the task with the default module,
    /// families and plans owned, the members manifest schema, the family manifest's schema and the generated access; the
    /// index, rules (the member rule set), failure classes (the members' outcomes), performance and tools.
    #[test]
    fn a_workloads_contract_names_every_workload_its_role_its_files_and_the_rules() {
        let root = crate::controller::test_support::scratch_root("workloads-contract");
        let set = fixture_workloads(&root);
        let contract = root.join("w/contract/engine");
        let files = write_member_files(&contract, &set).unwrap();
        for (workload, file) in [("tpch", "templates.md"), ("sec", "storages.json"), ("sec", "baselines.json"), ("anyschema", "templates.json"), ("anyschema", "storages.json")] {
            assert!(contract.join("workloads").join(workload).join(file).is_file(), "{workload}/{file}");
        }
        assert!(!contract.join("workloads/anyschema/baselines.json").exists() && files["anyschema"]["baselines"].is_null() && files["tpch"]["storages"].is_null(), "{files}");
        let record: Value = serde_json::from_str(&fs::read_to_string(contract.join(WORKLOADS_FILE)).unwrap()).unwrap();
        assert_eq!((record["primary"].as_str(), record["workloads"][2]["role"].as_str(), record["workloads"][0]["primary"].as_bool()), (Some("tpch"), Some("check"), Some(true)));
        assert_eq!(record["workloads"][1]["seed"]["workload"], "sec");
        assert_eq!(record["evaluation"].as_array().map(Vec::len), Some(9));
        for key in ["one_engine", "families", "default_module", "plans", "transition", "score", "root"] {
            assert!(record[key].is_string(), "{key}");
        }
        assert!(record["score"].as_str().unwrap().contains("There is no guard per workload") && record["rules"]["plan_file"] == PLAN_FILE_PATTERN);
        let mut task = json!({"manifest":{},"generated_access":{"engine_crate":{}},"fixed_files":{}});
        amend_task(&mut task, Path::new("/w"), &contract, &set, Shape::OneLine);
        assert!(task["task"].as_str().unwrap().contains("counted workload (tpch, sec)") && task["task"].as_str().unwrap().contains("check workloads (anyschema)"), "{}", task["task"]);
        assert_eq!(task["you_own"], json!(["/w/engine/src/agent", "/w/engine/workloads", "/w/engine/plans", "/w/storages"]));
        let schema = &task["manifest"]["schema"]["properties"];
        assert!(schema["families"].is_object() && schema["default_modules"].is_object() && schema["base"].is_null(), "{schema}");
        assert!(task["family_manifest"]["schema"].is_object() && task["generated_access"]["family_instances"].as_str().unwrap().contains("whole_schema.rs"));
        assert!(task["generated_access"]["family_instances"].as_str().unwrap().contains("crate::sources_flat (the flat sources by table and column id) always carries the nullable items"));
        let mut index = json!({"read_order":["task","final_claim"],"inputs":{},"output":{},"generated_access":{}});
        amend_index(&mut index, &contract, &set, Shape::OneLine);
        assert_eq!(index["read_order"], json!(["task", "workloads", "final_claim"]));
        assert!(index["inputs"]["workloads"]["anyschema"]["data"].is_string() && index["inputs"]["workloads_record"] == json!(contract.join(WORKLOADS_FILE)));
        let (mut rules, mut classes, mut performance, mut tools) = (json!({"engine_rules":{}}), json!({"named_reasons":{}}), json!({"scale_ladder":{"rule":"move"}}), json!({"arguments":{}}));
        amend_rules(&mut rules);
        amend_failure_classes(&mut classes);
        amend_performance(&mut performance, &set);
        amend_tools(&mut tools, &set);
        let ids: Vec<&str> = rules["engine_rules"]["rules"].as_array().unwrap().iter().filter_map(|r| r["id"].as_str()).collect();
        assert_eq!(ids, ["template_constant", "ast_fragment_table", "schema_name", "workload_module_statement", "storage_family_required", "plan_is_data", "workload_module_scope"]);
        assert!(classes["member_outcomes"]["checked"].is_string() && classes["named_reasons"]["plan_is_data"].is_string());
        assert!(performance["workloads"]["evaluation"][3].as_str().unwrap().starts_with("every check workload") && performance["scale_ladder"]["rule"].as_str().unwrap().starts_with("off in a run of several workloads"));
        assert_eq!(tools["arguments"]["workload"]["values"], json!(["tpch", "sec", "anyschema"]));
        assert!(FAMILY_AUTHORING.contains("`storage_family_required`") && FAMILY_AUTHORING.contains("`plan_is_data`") && FAMILY_AUTHORING.contains("`workload_module_scope`"));
        let mut registry = json!({});
        amend_registry(&mut registry);
        let names: Vec<&str> = registry["family_instance_whole_schema_files"].as_array().unwrap().iter().filter_map(|r| r["name"].as_str()).collect();
        assert_eq!(names, ["whole_schema", "storage_schema_exec", "engine_whole_schema"]);
        let plain = super::super::general::registry(json!({}));
        assert!(!plain.to_string().contains("whole_schema"), "the general line's registry without them: {plain}");
        fs::remove_dir_all(&root).ok();
    }
}
