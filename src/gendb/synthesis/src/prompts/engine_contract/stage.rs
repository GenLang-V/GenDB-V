//! The contract files of a stage run: one engine for a goal workload, whose
//! score decides every submission, and kept workloads, which are verified, timed against the parent and shown. The
//! goal's contract is the general line's (`prompts::engine_contract::general`), written over the goal's inputs; a stage
//! run ([`StageContract`], `prompts::engine_contract::write_stage_engine_contract`) changes it as follows, built on the
//! general generators so every shared fact stays one text:
//!
//! - `stage.json` ([`stage_record`]): the workloads with their roles, scales, libraries and files, one engine as one
//!   crate per workload, general code with a plan per workload, the evaluation's
//!   order, the score and the stage's rules;
//! - `workloads/<name>/` per workload ([`write_workload_files`]): `templates.md` and `templates.json` (its SQL,
//!   parameters, visible bindings and saved baselines), `data.json` (its schema, sizes and source facts, its budget),
//!   `integrity-constraints.json`, `budget-rule.json`, `bindings.json` and `baselines.json` (copies of its scale's
//!   files), and for a kept workload `storages.json` (its library's admitted storages; their interfaces under
//!   `admitted-storages/` beside the goal's);
//! - `task.json` and `index.json`: the stage task, ownership of `workloads/<name>/**`, the stage manifest schema
//!   (`EngineManifest::stage_schema`), the generated access every stage crate carries (always `crate::flat_tables` and
//!   the nullable items), the fixed files per crate, and the stage's files;
//! - `rules.json`, `failure-classes.json`, `performance.json` and `tools.json`: the stage rules (one-word column names
//!   refused only inside literals; `workload_module_statement`), the kept workloads' outcomes, the evaluation's order
//!   and score, no ladder, and the tools' `workload` argument.
//!
//! What a workload contributes is plain data ([`WorkloadContract`]), so the texts are tested from a fixture;
//! [`WorkloadContract::prepare`] reads it from a workload's prepared inputs, its capture and its library.

use super::super::brief::common::{self, write};
use super::general::{GeneralContract, budget_rule_of};
use super::write_text;
use crate::engine::role::EngineInputs;
use crate::engine::submission::EngineManifest;
use crate::prompts::engine_general_sections::Shape;
use crate::storage::policy::StoredDataPolicy;
use gendb_artifacts::ObjectStore;
use gendb_storage::import::PreparedSource;
use gendb_verification::admission::AdmissionError;
use gendb_verification::verus::engine_rules::{SCHEMA_COLUMN_MENTION, SCHEMA_TABLE_MENTION, STAGE_ENGINE_RULES};
use serde_json::{Value, json};
use std::fs;
use std::path::{Path, PathBuf};

/// The stage file in the contract directory.
pub const STAGE_FILE: &str = "stage.json";
/// The directory of the per-workload files in the contract directory (`workloads/<name>/`).
pub const WORKLOADS_DIRECTORY: &str = "workloads";

/// A workload's role in a stage run.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WorkloadRole {
    /// Its score decides every submission.
    Goal,
    /// Verified, timed against the parent and shown for every accepted version; never deciding.
    Kept,
}

impl WorkloadRole {
    /// The role as records and the stage view name it (`goal`, `kept`).
    pub fn name(self) -> &'static str {
        match self {
            WorkloadRole::Goal => "goal",
            WorkloadRole::Kept => "kept",
        }
    }
}

/// One workload of a stage run as its contract files need it: plain data, read by [`WorkloadContract::prepare`].
#[derive(Clone, Debug)]
pub struct WorkloadContract {
    /// Its name (`engine.stage`): its module directory `workloads/<name>/` and its key in records.
    pub name: String,
    pub role: WorkloadRole,
    /// The scale where it is timed, and the first scale of its ladder, where its variants are checked.
    pub scale: String,
    pub first_scale: String,
    /// Its own library.
    pub library: PathBuf,
    /// Its training facts at `scale` (`engine::facts::training_facts`).
    pub training: Value,
    /// Its data facts at `scale` (`data.json`: the schema, storability, sizes and the source facts of its capture).
    pub data: Value,
    /// Its declared integrity constraints (`Statement::integrity_constraints_json`).
    pub integrity_constraints: Value,
    /// Its budget rule at `scale` (`budget-rule.json`).
    pub budget_rule: Value,
    /// A kept workload's admitted storages (`storages.json`); `None` for the goal, whose catalog is the contract's own.
    pub storages: Option<Value>,
    /// Its scale's visible bindings and saved baselines (the request's `bindings` and `targets` files), copied; an empty
    /// `baselines` path: none (a check workload of a run of several workloads, never timed), and no `baselines.json`.
    pub bindings: PathBuf,
    pub baselines: PathBuf,
}

impl WorkloadContract {
    /// The contract data of the workload `name` from its prepared inputs at its scale (`inputs.general` set), its capture
    /// there and its library's store: its schema, constraints and data facts from the capture's metadata (nothing is
    /// scanned), its budget rule, and for a kept workload its admitted storages, their interfaces copied under
    /// `<root>/admitted-storages/` (as the goal's are).
    #[allow(clippy::too_many_arguments)]
    pub fn prepare(root: &Path, name: &str, role: WorkloadRole, inputs: &EngineInputs, capture: &PreparedSource, store: &ObjectStore, policy: &StoredDataPolicy, library: &Path,
        first_scale: &str) -> Result<Self, AdmissionError> {
        let general = inputs.general.as_ref().ok_or_else(|| AdmissionError::tool(format!("workload {name}: a stage run's inputs are general-line inputs")))?;
        let (_, first) = inputs.sessions.first().ok_or_else(|| AdmissionError::tool(format!("workload {name}: no prepared template")))?;
        let statement = first.statement();
        let schema = &statement.instance.doc.tables;
        let mut data = common::data_facts(capture, schema);
        data["source_facts"] = common::source_data_facts(capture);
        data["storage_budget"] = json!({"budget_bytes":general.scale.original_data_bytes,"plain_storage_bytes":general.plain_storage_bytes,"scale":general.scale.name,"rule":"budget-rule.json beside this file"});
        let storages = match role {
            WorkloadRole::Goal => None,
            WorkloadRole::Kept => {
                let demands: Vec<(String, gendb_verification::obligations::DeclaredSource)> =
                    inputs.sessions.iter().map(|(_, s)| Ok((s.statement().key_v4_id.clone(), s.demand()?))).collect::<Result<_, AdmissionError>>()?;
                Some(common::storages_catalog(store, capture, schema, root, &demands, policy)?)
            }
        };
        Ok(WorkloadContract {
            name: name.to_string(),
            role,
            scale: general.scale.name.clone(),
            first_scale: first_scale.to_string(),
            library: library.to_path_buf(),
            training: inputs.training_facts.clone(),
            data,
            integrity_constraints: statement.integrity_constraints_json(),
            budget_rule: budget_rule_of(general, "head"),
            storages,
            bindings: general.scale.bindings.clone(),
            baselines: general.scale.targets.clone(),
        })
    }
}

/// What a stage run adds to the general line's contract inputs.
#[derive(Clone, Debug)]
pub struct StageContract {
    /// The goal workload's name.
    pub goal: String,
    /// The accepted version of another general-line run the stage run starts from: `{run, version}`.
    pub seed: Value,
    /// Every workload, the goal first.
    pub workloads: Vec<WorkloadContract>,
}

impl StageContract {
    fn kept(&self) -> impl Iterator<Item = &WorkloadContract> {
        self.workloads.iter().filter(|w| w.role == WorkloadRole::Kept)
    }
}

/// The files of workload `name` under `<contract>/workloads/<name>/`, by key (as `files.workloads.<name>` names them);
/// `storages` for a workload with its own catalog (a kept workload). The stage tests' view; the contract writes
/// [`files_of`].
#[cfg(test)]
pub(crate) fn workload_files(contract: &Path, name: &str, storages: bool) -> Value {
    member_files(contract, name, storages, true)
}

/// [`workload_files`], with `baselines.json` only when the workload has saved baselines (`baselines`; a check workload of
/// a run of several workloads has none).
pub(crate) fn member_files(contract: &Path, name: &str, storages: bool, baselines: bool) -> Value {
    let dir = contract.join(WORKLOADS_DIRECTORY).join(name);
    let mut files = json!({"templates":dir.join("templates.md"),"templates_data":dir.join("templates.json"),"data":dir.join("data.json"),
        "integrity_constraints":dir.join("integrity-constraints.json"),"budget_rule":dir.join("budget-rule.json"),"bindings":dir.join("bindings.json")});
    if baselines {
        files["baselines"] = json!(dir.join("baselines.json"));
    }
    if storages {
        files["storages"] = json!(dir.join("storages.json"));
    }
    files
}

/// [`member_files`] of `workload`.
pub(crate) fn files_of(contract: &Path, workload: &WorkloadContract) -> Value {
    member_files(contract, &workload.name, workload.storages.is_some(), !workload.baselines.as_os_str().is_empty())
}

/// Every workload's files (`files.workloads`: by workload, then by file).
pub fn workloads_files(contract: &Path, stage: &StageContract) -> Value {
    Value::Object(stage.workloads.iter().map(|w| (w.name.clone(), files_of(contract, w))).collect())
}

/// Write every workload's files under `<contract>/workloads/<name>/` and `stage.json` (module documentation); returns
/// `files.workloads`.
pub fn write_workload_files(contract: &Path, stage: &StageContract) -> Result<Value, AdmissionError> {
    for workload in &stage.workloads {
        write_one_workload(contract, workload)?;
    }
    write(&contract.join(STAGE_FILE), &stage_record(contract, stage))?;
    Ok(workloads_files(contract, stage))
}

/// Write one workload's files under `<contract>/workloads/<name>/` ([`files_of`]): its templates, data, constraints,
/// budget rule, the copies of its bindings and baselines (when it has them) and its storages catalog (when it has one).
pub(crate) fn write_one_workload(contract: &Path, workload: &WorkloadContract) -> Result<(), AdmissionError> {
    let files = files_of(contract, workload);
    let dir = contract.join(WORKLOADS_DIRECTORY).join(&workload.name);
    fs::create_dir_all(&dir).map_err(|e| AdmissionError::tool(format!("{}: {e}", dir.display())))?;
    let at = |key: &str| PathBuf::from(files[key].as_str().expect("a workload file"));
    write(&at("templates_data"), &workload.training)?;
    write_text(&at("templates"), &super::templates_markdown(&workload.training))?;
    write(&at("data"), &workload.data)?;
    write(&at("integrity_constraints"), &workload.integrity_constraints)?;
    write(&at("budget_rule"), &workload.budget_rule)?;
    for (key, source) in [("bindings", &workload.bindings), ("baselines", &workload.baselines)] {
        if files[key].is_string() {
            fs::copy(source, at(key)).map_err(|e| AdmissionError::tool(format!("workload {}: copy {}: {e}", workload.name, source.display())))?;
        }
    }
    if let Some(storages) = &workload.storages {
        write(&at("storages"), storages)?;
    }
    Ok(())
}

/// One engine as one crate per workload, as the contract states it.
const ONE_ENGINE: &str = "src/agent/** is the engine, shared by every workload; workloads/<name>/** is each workload's module. At freeze GenDB composes one crate per workload: src/agent/** with workloads/<name>/** copied in as src/agent/workload/** (src/agent/workload must not exist in the workspace), and every framework file generated for that workload's schema, storages and declared constraints; each crate is verified whole against gendb-verus-engine-entry-v1. Shared code reaches the module as crate::agent::workload::..., so every module offers the items the shared code calls; rustc checks each crate. Without any workloads/<name>/ directory, src/agent/** alone is every workload's crate. One engine means the same src/agent/** bytes in every crate: a recorded digest, not a theorem";
/// General code with a plan per workload, as the contract states it.
const GENERAL_CODE: &str = "query processing and the code that builds and reads storages (layouts, encodings, compression, indexes, metadata) are general: written for any supported schema and data, parameterized by tables, columns and types, never for one benchmark's tables; the workloads are the cases that test it. A workload module holds only its plan (data: which tables and columns get which layout, encoding or index) and the opening of its storages as the engine's tables, with the proofs that needs; a new workload needs a new plan, not new code. Storage code the start version wrote for one workload's tables is to be replaced in this stage by general code and a plan; its storages are then built once by the general builders, and that workload must keep verifying and answering correctly";
/// The order of a stage submission's evaluation.
const EVALUATION: [&str; 7] = [
    "freeze every workload's crate (manifest, each workload's storage uses, coverage, the source rules over every crate, composition); a refusal is an attempt",
    "Verus on the goal workload's whole crate, --no-cheating, 0 errors (gating)",
    "the goal's storages: new storages built, the storage policy, single copy and the budget in the goal's library (gating)",
    "the interleaved timing against the parent's goal side at the goal's scale (performance.json submission_timing); every answer checked against the saved answers",
    "the score decision on the goal's score (performance.json score): not better, an attempt, and no kept workload is verified or timed (the evaluation's kept_workloads say not_run)",
    "for every kept workload, in its library: whole-crate Verus (gating), its storages, policy and budget (gating), an interleaved timing against the parent's side of that workload at its scale (recorded and shown, never deciding: slower or unfinished cells do not refuse the submission, a wrong answer does and is flagged), its variants at its first scale for their answers (gating)",
    "admission of every workload's crate in its library with the same lineage (version id, parents), selected in every library; one version folder with every workload's records (version.json workloads)",
];

/// `stage.json` (module documentation).
pub fn stage_record(contract: &Path, stage: &StageContract) -> Value {
    let workloads: Vec<Value> = stage.workloads.iter().map(|w| json!({"name":w.name,"role":w.role.name(),"scale":w.scale,"first_scale":w.first_scale,"library":w.library,
        "files":files_of(contract, w)})).collect();
    json!({"format_version":1,"goal":stage.goal,"seed":stage.seed,"workloads":workloads,"one_engine":ONE_ENGINE,"general_code":GENERAL_CODE,"evaluation":EVALUATION,
        "score":"the goal workload's score (performance.json score.rule, at the goal's scale) decides every submission; each kept workload's score, totals and ratios to the parent, from the same-window timing, are recorded (version.json workloads) and shown (CURRENT FACTS, TREE.md, FINDINGS.md), never deciding: there is no guard",
        "rules":stage_rules(),
        "tools":"every engine and storage tool takes workload (default: the goal): which crate, data, library and saved answers a job uses",
        "meaning":"a stage run of the general line: one engine for several workloads, each with its own crate, library, storage budget and saved answers"})
}

/// The stage's source rules, as `rules.json` and `stage.json` state them.
fn stage_rules() -> Value {
    json!({"names":"the schema-name rule covers the table and column names of every workload's schema; template constants are those of every workload's templates",
        "one_word_column_names":"a column name of one word (no _) is refused only inside a string, byte string or char literal (as a whole word); as an identifier or an identifier segment it is reported, not refused. Every TPC-H column name has two segments, so its rule is unchanged",
        "workload_module_statement":"gating: files under agent/workload/ (a workload's module in its crate) name no statement type or AST path (EOrderedQuery, EQuery, EPred, EExpr, exec::ast, spec::ast and the like): a workload module opens its workload's storages as the engine's tables and proves what that needs; query processing stays in the shared engine",
        "workload_directory":"src/agent/workload in the workspace is refused: GenDB composes it per crate from workloads/<name>/"})
}

/// The generated access of a stage crate: every crate carries `crate::flat_tables` and the
/// nullable items, also over a schema without a flat use or a nullable column.
pub(crate) const UNIFORM_ACCESS: &str = "in a stage run every engine crate carries crate::flat_tables, also without a flat storage use (flat_table(t) false where no flat storage holds t), and always the nullable items: nullable_column(t, c) (an open spec function, false for every column of a schema without nullable columns), lemma_nullable_column, nullable_column_slice (its precondition unsatisfiable when nothing is nullable) and column_slice for !nullable_column(t, c), so shared code compiles and verifies in every workload's crate; it reads nullability at run time from schema_exec() and links it with lemma_nullable_column";

/// `task.json` of a stage run: the general task file with the stage task, ownership, manifest schema, generated access,
/// fixed files per crate and the stage's files.
pub fn amend_task(task: &mut Value, root: &Path, contract: &Path, stage: &StageContract, shape: Shape) {
    task["task"] = json!(format!(
        "Make the same verified engine fast on the goal workload {}: faster on its training templates at every worker count than the best of DuckDB and Umbra; first finish every template within the call limit at its scale, then reduce the total time; its score decides every submission. The engine keeps serving {}: every submission verifies and agrees with the saved answers on every workload, and each kept workload is timed against the parent for every accepted version and shown, never deciding. crate::agent::engine answers every supported query (wf_ordered over each workload's schema) over that workload's stored data, proved against the fixed engine entry in every workload's crate; submit your verus-engine.json once it holds several verified improvements",
        stage.goal,
        stage.kept().map(|w| w.name.as_str()).collect::<Vec<_>>().join(", ")
    ));
    task["you_own"] = json!([root.join("engine/src/agent"), root.join("engine").join(WORKLOADS_DIRECTORY)]);
    task["manifest"]["schema"] = stage_manifest_schema(shape);
    task["generated_access"]["stage"] = json!(UNIFORM_ACCESS);
    super::general::add_nullable_access(&mut task["generated_access"]);
    task["fixed_files"]["per_workload"] = json!("each workload's crate has these framework files, generated for its own schema, storages and declared constraints; src/agent/** and workloads/<name>/** (copied in as src/agent/workload/**) are yours");
    task["stage"] = json!({"file":contract.join(STAGE_FILE),"one_engine":ONE_ENGINE,"general_code":GENERAL_CODE});
}

/// The manifest's schema in a stage run as the author reads it: `EngineManifest::stage_schema`, on one
/// line without `base`, as the general line's.
fn stage_manifest_schema(shape: Shape) -> Value {
    let mut schema = EngineManifest::stage_schema();
    GeneralContract::one_line_schema(&mut schema, shape);
    schema
}

/// `index.json` of a stage run: the stage's files in the inputs and the read order, the stage manifest schema and the
/// generated access.
pub fn amend_index(index: &mut Value, contract: &Path, stage: &StageContract, shape: Shape) {
    index["task"] = json!("Make the same verified engine faster than the best of DuckDB and Umbra on the goal workload's training templates at every worker count, keeping every workload verified and correct (contract task.json, stage.json); every submission is judged on the goal workload against its parent in one interleaved timing");
    if let Some(order) = index["read_order"].as_array_mut() {
        order.insert(1, json!("stage"));
    }
    index["inputs"]["stage"] = json!(contract.join(STAGE_FILE));
    index["inputs"]["workloads"] = workloads_files(contract, stage);
    index["output"]["manifest"] = stage_manifest_schema(shape);
    index["generated_access"]["stage"] = json!(UNIFORM_ACCESS);
    super::general::add_nullable_access(&mut index["generated_access"]);
}

/// `rules.json` of a stage run: the stage's rule set (`STAGE_ENGINE_RULES`), its reports, and the stage's rules in
/// words.
pub fn amend_rules(rules: &mut Value) {
    let engine_rules = &mut rules["engine_rules"];
    engine_rules["line"] = json!("general, stage run");
    engine_rules["rules"] = json!(super::general::rule_texts(STAGE_ENGINE_RULES));
    engine_rules["scope"] = json!("at freeze (the check tool and every submission) and again at admission, in every workload's crate: template constants of every workload, AST fragments and the schema-name rule over every agent/ file, the workload-module rule over agent/workload/ (a workload's module); the schema-name rule also over the own interface and builder files of every storage a crate reads that is not a generated flat storage; no static item (no state between calls)");
    engine_rules["reported"] = json!([
        {"id":SCHEMA_TABLE_MENTION,"meaning":"a table name of a workload's schema as a word or segment of an identifier outside literals and storage paths: reported with the evaluation, never refused"},
        {"id":SCHEMA_COLUMN_MENTION,"meaning":"a one-word column name of a workload's schema as an identifier or a segment of one: reported with the evaluation, never refused"},
        {"id":"workload_module_report","meaning":"each workload module's lines, item kinds, loops and the storages it names, with every freeze and admission: its size and shape for review"}]);
    engine_rules["stage"] = stage_rules();
}

/// `failure-classes.json` of a stage run: the stage's refusal and report, and the kept workloads' outcomes as the
/// evaluation records them (`kept_workloads[].status`, the stage fixture).
pub fn amend_failure_classes(classes: &mut Value) {
    let named = &mut classes["named_reasons"];
    named["workload_module_statement"] = json!("refusal (engine rules, stage run): a file under agent/workload/ names a statement type, an AST path or the AST codec (rules.json engine_rules)");
    named[SCHEMA_COLUMN_MENTION] = json!("report only: a one-word column name of a workload's schema in an identifier; never refused");
    classes["kept_workload_outcomes"] = json!({"not_run":"the goal's score was not better (an attempt), or the goal's side was refused: no kept workload was verified or timed",
        "refused":"the goal's score was better, but a kept workload's whole-crate Verus, storages, policy, budget, an answer or a variant's answer refused the submission; reason names it (a wrong answer is also flagged for the operator)",
        "timed":"verified, its storages checked and timed against the parent's side of that workload (race: its race.json); recorded and shown, never deciding",
        "where":"the evaluation record's kept_workloads[] (name, status, reason, race), shown in the evaluation of the submission"});
}

/// `performance.json` of a stage run: the evaluation's order and the score per workload; no ladder.
pub fn amend_performance(performance: &mut Value, stage: &StageContract) {
    performance["stage"] = json!({"evaluation":EVALUATION,
        "score":"the goal workload's score decides (score.rule); each kept workload's score and its totals and ratios to the parent per worker count, from the same-window timing, are recorded and shown, never deciding",
        "workloads":stage.workloads.iter().map(|w| json!({"name":w.name,"role":w.role.name(),"scale":w.scale,"first_scale":w.first_scale})).collect::<Vec<_>>()});
    performance["scale_ladder"]["rule"] = json!("off in a stage run: each workload stays at its scale (stage.workloads); no scale move");
}

/// `tools.json` of a stage run: the tools' `workload` argument.
pub fn amend_tools(tools: &mut Value, stage: &StageContract) {
    tools["arguments"]["workload"] = json!({"meaning":"every engine and storage tool, optional (default: the goal workload): which workload's crate (src/agent/** with its module), data, library and saved answers the job uses; templates, binding and sql are that workload's","values":stage.workloads.iter().map(|w| w.name.clone()).collect::<Vec<_>>()});
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::prompts::engine_facts::general::tests::stage_run::fixture_at;

    /// The fixture's workloads (the stage fixture) as stage contract data, with stand-in data, constraints, budget and
    /// storages records and scale files under `root` (no capture or library is read).
    pub(crate) fn fixture_stage(root: &Path) -> StageContract {
        let fixture = fixture_at(&root.join("run"));
        let stage = &fixture["context"]["stage"];
        let workloads = stage["workloads"].as_array().unwrap().iter().map(|w| {
            let name = w["name"].as_str().unwrap();
            let inputs = root.join("inputs").join(name);
            fs::create_dir_all(&inputs).unwrap();
            fs::write(inputs.join("visible.json"), "{\"queries\":{}}\n").unwrap();
            fs::write(inputs.join("targets.json"), "{}\n").unwrap();
            let kept = w["role"] == "kept";
            WorkloadContract { name: name.into(), role: if kept { WorkloadRole::Kept } else { WorkloadRole::Goal }, scale: w["scale"].as_str().unwrap().into(),
                first_scale: w["first_scale"].as_str().unwrap().into(), library: PathBuf::from(w["library"].as_str().unwrap()), training: w["training"].clone(),
                data: json!({"tables":[],"storage_budget":{"budget_bytes":w["storage"]["budget_bytes"]}}), integrity_constraints: json!({"declarations":[]}),
                budget_rule: json!({"budget_bytes":w["storage"]["budget_bytes"]}), storages: kept.then(|| json!({"storages":[]})), bindings: inputs.join("visible.json"),
                baselines: inputs.join("targets.json") }
        }).collect();
        StageContract { goal: stage["goal"].as_str().unwrap().into(), seed: json!({"run":stage["seed"]["run"],"version":stage["seed"]["version"]}), workloads }
    }

    /// A stage run's contract: every workload's files and `stage.json` with the
    /// composition, the general-code direction, the evaluation's order, the score and the rules; the task with the
    /// workload modules owned, the stage manifest schema and the uniform generated access; the index, rules, failure
    /// classes, performance and tools with the stage's parts.
    #[test]
    fn a_stage_contract_names_every_workload_its_files_its_rules_and_the_evaluations_order() {
        let root = crate::controller::test_support::scratch_root("stage-contract");
        let stage = fixture_stage(&root);
        let contract = root.join("w/contract/engine");
        let files = write_workload_files(&contract, &stage).unwrap();
        for (workload, file) in [("sec", "templates.md"), ("sec", "templates.json"), ("sec", "bindings.json"), ("tpch", "baselines.json"), ("tpch", "storages.json"), ("tpch", "budget-rule.json")] {
            assert!(contract.join("workloads").join(workload).join(file).is_file(), "{workload}/{file}");
        }
        assert!(files["sec"]["storages"].is_null() && files["tpch"]["storages"].is_string() && files["tpch"]["templates"] == json!(contract.join("workloads/tpch/templates.md")));
        let templates = fs::read_to_string(contract.join("workloads/sec/templates.md")).unwrap();
        assert!(templates.contains("## Q24\n\nReads: num, pre.") && templates.contains("| v0 |  | 1 | 447.843 | 476.574 | exact-order |"), "{templates}");
        let record: Value = serde_json::from_str(&fs::read_to_string(contract.join(STAGE_FILE)).unwrap()).unwrap();
        assert_eq!((record["goal"].as_str(), record["workloads"][1]["role"].as_str(), record["workloads"][1]["first_scale"].as_str()), (Some("sec"), Some("kept"), Some("sf1")));
        assert_eq!(record["evaluation"].as_array().map(Vec::len), Some(7));
        assert!(record["general_code"].as_str().unwrap().contains("a new workload needs a new plan, not new code") && record["one_engine"].as_str().unwrap().contains("src/agent/workload must not exist in the workspace"));
        assert!(record["rules"]["workload_module_statement"].as_str().unwrap().starts_with("gating: files under agent/workload/") && record["score"].as_str().unwrap().contains("there is no guard"));
        let mut task = json!({"manifest":{},"generated_access":{"engine_crate":{}},"fixed_files":{}});
        amend_task(&mut task, Path::new("/w"), &contract, &stage, Shape::OneLine);
        assert!(task["task"].as_str().unwrap().starts_with("Make the same verified engine fast on the goal workload sec") && task["task"].as_str().unwrap().contains("keeps serving tpch"));
        assert_eq!(task["you_own"], json!(["/w/engine/src/agent", "/w/engine/workloads"]));
        let schema = &task["manifest"]["schema"]["properties"];
        assert!(schema["workloads"]["items"]["properties"]["storage_uses"].is_object() && schema["base"].is_null() && schema["storage_uses"]["maxItems"] == 0, "{schema}");
        assert!(task["generated_access"]["stage"].as_str().unwrap().starts_with("in a stage run every engine crate carries crate::flat_tables") && task["generated_access"]["nullable_columns"].is_object());
        let mut index = json!({"read_order":["task","final_claim"],"inputs":{},"output":{},"generated_access":{}});
        amend_index(&mut index, &contract, &stage, Shape::OneLine);
        assert_eq!(index["read_order"], json!(["task", "stage", "final_claim"]));
        assert!(index["inputs"]["workloads"]["tpch"]["data"].is_string() && index["inputs"]["stage"] == json!(contract.join(STAGE_FILE)));
        let (mut rules, mut classes, mut performance, mut tools) = (json!({"engine_rules":{}}), json!({"named_reasons":{}}), json!({"scale_ladder":{"rule":"move"}}), json!({"arguments":{}}));
        amend_rules(&mut rules);
        amend_failure_classes(&mut classes);
        amend_performance(&mut performance, &stage);
        amend_tools(&mut tools, &stage);
        assert!(rules["engine_rules"]["stage"]["one_word_column_names"].as_str().unwrap().starts_with("a column name of one word (no _) is refused only inside"));
        assert!(classes["named_reasons"]["workload_module_statement"].is_string() && classes["kept_workload_outcomes"]["not_run"].is_string());
        let ids: Vec<&str> = rules["engine_rules"]["rules"].as_array().unwrap().iter().filter_map(|r| r["id"].as_str()).collect();
        assert_eq!(ids, ["template_constant", "ast_fragment_table", "schema_name", "workload_module_statement"]);
        assert!(performance["stage"]["evaluation"][4].as_str().unwrap().contains("no kept workload is verified or timed") && performance["scale_ladder"]["rule"].as_str().unwrap().starts_with("off in a stage run"));
        assert_eq!(tools["arguments"]["workload"]["values"], json!(["sec", "tpch"]));
        fs::remove_dir_all(&root).ok();
    }
}
