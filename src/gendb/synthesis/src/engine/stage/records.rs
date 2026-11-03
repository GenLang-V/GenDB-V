//! The records of a stage version (the stage fixture, the fixture's `version.workloads`): what its folder
//! holds beside a one-workload version's records.
//!
//! - The code ([`write_stage_code`]): `code/agent/**` is the shared engine (the goal crate's `src/agent/**` without the
//!   composed `workload/`), `code/workloads/<name>/**` each workload's module as its crate held it (absent without
//!   modules), `code/storages/` every crate's workspace storages, and `code-view/` the reading view of all of them. A
//!   session seeded from the version gets `engine/src/agent/**` and `engine/workloads/**` back.
//! - The seed manifest ([`stage_seed_manifest`]): the stage form, each workload's entry naming its crate's admitted
//!   storage uses.
//! - Per workload, `workloads/<name>/workload.json` ([`WorkloadRecord`]: its role, scale, recorded score, cells, serving
//!   bytes, storage uses, module lines, its race against the parent's side) and, for a kept workload, its own records
//!   beside it (`race.json` or the root's `score.json`, `cells/<scale>.json`, `admission.json`, its variant answers);
//!   the goal's records stay at the folder's top as before. [`write_workload`] writes them and returns the workload's
//!   `version.json` `workloads.<name>` entry; [`EngineBench::write_stage_workloads`] does it for every workload of a
//!   version accepted in a session (`engine::acceptance`), the stage root's folder for its sides (`stage::root`).
//!
//! A version of a run of several workloads (`engine.workloads`; the workloads fixture, the fixture's `version` and
//! `version_root`) keeps the same layout with:
//! - the code [`write_members_code`]: `code/agent/**`, `code/workloads/<name>/**` (own modules) and
//!   `code/workloads/default/**`, `code/families/<family>/**` and `code/plans/<name>/<family>.rs`
//!   (`engine::submission::members::write_member_code`), each workload's frozen family instances under
//!   `code/instances/<name>/`, and the reading view of every `.rs` file of the code;
//! - the seed manifest: the stage form with the families named under `code/` ([`members_seed_manifest`]);
//! - per workload ([`write_member`]): `workload.json` with its role, whether it is the primary, its score when timed
//!   (none for a check workload), its check (`check.json`: the answers of every template at every visible binding), its
//!   `general` record (own module lines, inherited and family storages, plan lines; from the crate's
//!   `engine::submission::members::MemberRecord`), and its `version.json` `workloads.<name>` entry;
//! - `version.json` `combined_score` ([`combined_record`]: the sums over the counted workloads) and `general`
//!   ([`general_record`]: whether the version is one engine, the own modules, the inherited storages and the digest of
//!   the shared sources).

use super::super::role::{EngineBench, copy_tree};
use super::super::score::{CellResult, CombinedScore};
use super::super::submission::members::MemberRecord;
use super::super::submission::{CRATE_DIRECTORY, EngineManifest, FrozenEngine, WORKLOAD_MODULE, WorkloadModules};
use super::super::tree::{RecordedScore, TreeNode, WORKLOAD_RECORD_FILE, WORKLOADS_DIRECTORY, node_directory};
use crate::controller::records::read_json;
use crate::controller::request::MemberRole;
use crate::prompts::engine_contract::WorkloadRole;
use crate::query::candidate::StorageUseDeclaration;
use gendb_artifacts::verus::VerusStorageUseV1;
use gendb_verification::admission::AdmissionError;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::fs;
use std::path::{Path, PathBuf};

/// A stage version's record on one workload (`versions/vNNN/workloads/<name>/workload.json`). The tree reads its role
/// and score (`engine::tree::WorkloadScore`); the stage view reads the rest.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct WorkloadRecord {
    pub format_version: u32,
    pub version: String,
    pub workload: String,
    /// `goal` or `kept`; in a run of several workloads `counted`, `check` or `kept`.
    pub role: String,
    pub scale: String,
    /// Its recorded score at `scale` (its `record` is the timing record in the version folder); `None` for a check
    /// workload (never timed).
    #[serde(default)]
    pub score: Option<RecordedScore>,
    /// Its cells at `scale` (`engine::score::CellResult`), a file of the version folder; `None` for a check workload.
    #[serde(default)]
    pub cells: Option<PathBuf>,
    /// Its serving storage's bytes when known, and its storage uses (admitted packages of its library).
    pub serving_bytes: Option<u64>,
    pub uses: Vec<VerusStorageUseV1>,
    /// Lines of its workload module (`workloads/<name>/**`; 0 without one).
    pub module_lines: u64,
    /// Its race report against the parent's side of the workload; `None` when it was timed alone (the root) or not timed.
    pub race: Option<PathBuf>,
    pub parent: Option<String>,
    /// A run of several workloads: the primary workload.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub primary: bool,
    /// A run of several workloads, a check workload: its answers (`calls`, `agreed`, `record`: its `check.json`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub check: Option<Value>,
    /// A run of several workloads: what of the version is specific to the workload (the workloads fixture `general`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub general: Option<Value>,
}

/// The records of version `version` on `workload`: `versions/<version>/workloads/<workload>`.
pub fn workload_directory(engine_dir: &Path, version: &str, workload: &str) -> PathBuf {
    node_directory(engine_dir, version, true).join(WORKLOADS_DIRECTORY).join(workload)
}

/// The record of version `version` on `workload`, when it has one.
pub fn read_workload_record(engine_dir: &Path, version: &str, workload: &str) -> Option<WorkloadRecord> {
    read_json(&workload_directory(engine_dir, version, workload).join(WORKLOAD_RECORD_FILE)).ok()
}

/// The cells version `version` recorded on `workload` at `scale` (for a race's skips): its record's cells file.
pub fn workload_cells(engine_dir: &Path, version: &str, workload: &str, scale: &str) -> Option<Vec<CellResult>> {
    let record = read_workload_record(engine_dir, version, workload).filter(|r| r.scale == scale)?;
    read_json(record.cells.as_ref()?).ok()
}

/// The storage facts of one workload's part of a version (the stage fixture's `storage`).
pub struct StorageFacts {
    pub serving_bytes: Option<u64>,
    pub budget_bytes: u64,
    pub plain_storage_bytes: u64,
    /// The budget rule's decision (`storage::engine_library::BudgetRule::decide`).
    pub decision: Value,
}

/// One workload's part of a stage version, as its folder and `version.json` record it ([`write_workload`]).
pub struct WorkloadPart<'a> {
    pub name: &'a str,
    pub role: WorkloadRole,
    pub scale: &'a str,
    /// Its timing at `scale`: the cells, the score, and the record it was read from: a race report against the parent
    /// (`raced`) or, for the root, the score record of its timing alone.
    pub cells: &'a [CellResult],
    pub score: &'a RecordedScore,
    pub timing: &'a Path,
    pub raced: bool,
    pub parent: Option<&'a str>,
    /// Other records of its evaluation copied beside its own (variant answers, the official matrix).
    pub copies: Vec<PathBuf>,
    /// Its admission record in its library (`library_version`, `package`, `uses`, ...).
    pub admission: &'a Value,
    pub library: &'a Path,
    pub storage: StorageFacts,
    /// Its whole-crate Verus run (`verification` with `errors` and `verified`, `wall_ns`).
    pub build: &'a Value,
    pub module_lines: u64,
}

/// Write one workload's records of version `version` into the folder being staged at `staging` (renamed to `target`
/// once complete; every recorded path names `target`), and return its `version.json` `workloads.<name>` entry. With
/// `at_top` (the goal of a version accepted in a session) its timing, cells and admission are the folder's own top-level
/// records, already written; otherwise they are written under `workloads/<name>/`.
pub fn write_workload(staging: &Path, target: &Path, version: &str, part: &WorkloadPart<'_>, at_top: bool) -> Result<Value, AdmissionError> {
    let relative = if at_top { PathBuf::new() } else { PathBuf::from(WORKLOADS_DIRECTORY).join(part.name) };
    let timing_name = if part.raced { "race.json" } else { "score.json" };
    let cells_file = PathBuf::from("cells").join(format!("{}.json", part.scale));
    if !at_top {
        let dir = staging.join(&relative);
        write_value(&dir.join(&cells_file), &json!(part.cells))?;
        copy_file(part.timing, &dir.join(timing_name))?;
        write_value(&dir.join("admission.json"), part.admission)?;
        for file in part.copies.iter().filter(|f| f.is_file()) {
            if let Some(name) = file.file_name() {
                copy_file(file, &dir.join(name))?;
            }
        }
    }
    let timing = target.join(&relative).join(timing_name);
    let score = RecordedScore { record: timing.clone(), ..part.score.clone() };
    let uses: Vec<VerusStorageUseV1> = serde_json::from_value(part.admission["uses"].clone()).unwrap_or_default();
    let record = WorkloadRecord {
        format_version: 1,
        version: version.to_string(),
        workload: part.name.to_string(),
        role: part.role.name().to_string(),
        scale: part.scale.to_string(),
        score: Some(score.clone()),
        cells: Some(target.join(&relative).join(&cells_file)),
        serving_bytes: part.storage.serving_bytes,
        uses,
        module_lines: part.module_lines,
        race: part.raced.then(|| timing.clone()),
        parent: part.parent.map(String::from),
        primary: false,
        check: None,
        general: None,
    };
    write_value(&staging.join(WORKLOADS_DIRECTORY).join(part.name).join(WORKLOAD_RECORD_FILE), &json!(record))?;
    let verification = &part.build["verification"];
    Ok(json!({"role":part.role.name(),"scale":part.scale,"score":score,
        "times":{part.scale:{"race":record.race}},
        "storage":{"serving_bytes":part.storage.serving_bytes,"budget_bytes":part.storage.budget_bytes,"plain_storage_bytes":part.storage.plain_storage_bytes,"decision":part.storage.decision},
        "proof":{"errors":verification["errors"],"verified":verification["verified"],"wall_ns":part.build["wall_ns"]},
        "admission":{"library":part.library,"package":part.admission["package"]},
        "module_lines":part.module_lines}))
}

impl EngineBench<'_> {
    /// Every workload's records of an accepted stage version into its folder being staged at `staging` (renamed to
    /// `target`), and its `version.json` `workloads` (`write_workload`): the goal's from the version's own
    /// records at the folder's top (`record`: the evaluation's record with the admission; `engine`: the goal's frozen
    /// crate), every kept workload's from `record.workloads.<name>` under `workloads/<name>/`.
    pub(in crate::engine) fn write_stage_workloads(&self, staging: &Path, target: &Path, node: &TreeNode, record: &Value, engine: &FrozenEngine) -> Result<Value, AdmissionError> {
        let stage = self.stage.ok_or_else(|| AdmissionError::tool("a stage version's records outside a stage run"))?;
        let general = self.inputs().general.clone().ok_or_else(|| AdmissionError::tool("a stage version without general inputs"))?;
        let module_lines = |report: &Value| report["lines"].as_u64().unwrap_or(0);
        let cells = |value: &Value| serde_json::from_value::<Vec<CellResult>>(value.clone()).map_err(AdmissionError::tool);
        let score = node.score.clone().ok_or_else(|| AdmissionError::tool("an accepted version without a score"))?;
        let goal_cells = cells(&record["candidate_cells"])?;
        let race = target.join("race.json");
        let goal = WorkloadPart {
            name: &stage.workload,
            role: WorkloadRole::Goal,
            scale: &general.scale.name,
            cells: &goal_cells,
            score: &score,
            timing: &race,
            raced: true,
            parent: record["parent"].as_str(),
            copies: vec![],
            admission: &record["admission"],
            library: &self.bench.config.library,
            storage: StorageFacts {
                serving_bytes: record["storage_policy_at_evaluation"]["serving_bytes"].as_u64(),
                budget_bytes: general.scale.original_data_bytes,
                plain_storage_bytes: general.plain_storage_bytes,
                decision: record["storage_policy_at_evaluation"]["budget_decision"].clone(),
            },
            build: &record["build"],
            module_lines: engine.workload.as_ref().map_or(0, |w| module_lines(&w.module_report)),
        };
        let mut workloads = serde_json::Map::new();
        workloads.insert(stage.workload.clone(), write_workload(staging, target, &node.id, &goal, true)?);
        for side in &stage.sides {
            let kept = &record["workloads"][side.name.as_str()];
            let general = side.config.inputs.general.clone().ok_or_else(|| AdmissionError::tool(format!("workload {}: no general inputs", side.name)))?;
            let kept_cells = cells(&kept["candidate_cells"])?;
            let kept_score: RecordedScore = serde_json::from_value(kept["score"].clone()).map_err(AdmissionError::tool)?;
            let race = PathBuf::from(kept["race"].as_str().ok_or_else(|| AdmissionError::tool(format!("workload {}: no race record", side.name)))?);
            let part = WorkloadPart {
                name: &side.name,
                role: WorkloadRole::Kept,
                scale: &general.scale.name,
                cells: &kept_cells,
                score: &kept_score,
                timing: &race,
                raced: true,
                parent: kept["parent"].as_str(),
                copies: kept["finished_checks"]["variants"]["file"].as_str().map(PathBuf::from).into_iter().collect(),
                admission: &kept["admission"],
                library: &side.view.library,
                storage: StorageFacts {
                    serving_bytes: kept["storage_policy_at_evaluation"]["serving_bytes"].as_u64(),
                    budget_bytes: general.scale.original_data_bytes,
                    plain_storage_bytes: general.plain_storage_bytes,
                    decision: kept["storage_policy_at_evaluation"]["budget_decision"].clone(),
                },
                build: &kept["build"],
                module_lines: module_lines(&kept["module_report"]),
            };
            workloads.insert(side.name.clone(), write_workload(staging, target, &node.id, &part, false)?);
        }
        Ok(Value::Object(workloads))
    }
}

/// One timed workload's timing in a version of a run of several workloads ([`MemberPart`]): its cells, its score, and the
/// record it was read from (a race report against the parent's side when `raced`, else the root's score record of its
/// timing alone).
pub struct MemberTiming<'a> {
    pub cells: &'a [CellResult],
    pub score: &'a RecordedScore,
    pub timing: &'a Path,
    pub raced: bool,
    pub parent: Option<&'a str>,
}

/// One workload's part of a version of a run of several workloads, as its folder and `version.json` record it
/// ([`write_member`]).
pub struct MemberPart<'a> {
    pub name: &'a str,
    pub role: MemberRole,
    /// The primary workload: its timing, cells and admission are the folder's own top-level records.
    pub primary: bool,
    pub scale: &'a str,
    /// Its timing (a counted or kept workload); `None` for a check workload.
    pub timing: Option<MemberTiming<'a>>,
    /// A check workload's answers: its check record (`calls`, `agreed`, `file`: the check file of its evaluation).
    pub check: Option<&'a Value>,
    /// Other records of its evaluation copied beside its own (variant answers, the official matrix).
    pub copies: Vec<PathBuf>,
    pub admission: &'a Value,
    pub library: &'a Path,
    /// Its storage facts (`budget_bytes` is not shown for a check workload, which is exempt).
    pub storage: StorageFacts,
    pub build: &'a Value,
    /// Its crate's record (`engine::submission::members::MemberRecord`; `None` when its freeze recorded none).
    pub member: Option<&'a MemberRecord>,
    /// The root's record of the side (`v000` only; `Null` for every other version).
    pub origin: Value,
}

/// What of a version is specific to one workload (the workloads fixture `general`): its own module's lines, its inherited and
/// family storages and its plans' lines, from its crate's record.
pub fn member_general(member: Option<&MemberRecord>) -> Value {
    match member {
        Some(m) => json!({"own_module_lines":m.own_module_lines,"inherited_storages":m.inherited_storages,"family_storages":m.family_storages,"plan_lines":m.plan_lines}),
        None => json!({"own_module_lines":0,"inherited_storages":[],"family_storages":[],"plan_lines":0}),
    }
}

/// The check file of a check workload's version records (`workloads/<name>/check.json`).
pub const CHECK_FILE: &str = "check.json";
/// Each workload's frozen storages in a version's code of a run of several workloads (`code/instances/<workload>/`).
pub const INSTANCES_DIRECTORY: &str = "instances";

/// Write one workload's records of version `version` of a run of several workloads into the folder being staged at
/// `staging` (renamed to `target` once complete; every recorded path names `target`), and return its `version.json`
/// `workloads.<name>` entry (the workloads fixture). The primary's timing, cells and admission are the folder's own top-level
/// records, already written; every other workload's go under `workloads/<name>/` (a check workload's `check.json`, no
/// timing). `workload.json` is written under `workloads/<name>/` for every workload.
pub fn write_member(staging: &Path, target: &Path, version: &str, part: &MemberPart<'_>) -> Result<Value, AdmissionError> {
    let relative = if part.primary { PathBuf::new() } else { PathBuf::from(WORKLOADS_DIRECTORY).join(part.name) };
    let own = PathBuf::from(WORKLOADS_DIRECTORY).join(part.name);
    let dir = staging.join(&relative);
    let cells_file = PathBuf::from("cells").join(format!("{}.json", part.scale));
    let timing_name = |t: &MemberTiming<'_>| if t.raced { "race.json" } else { "score.json" };
    if !part.primary {
        if let Some(t) = &part.timing {
            write_value(&dir.join(&cells_file), &json!(t.cells))?;
            copy_file(t.timing, &dir.join(timing_name(t)))?;
        }
        write_value(&dir.join("admission.json"), part.admission)?;
        for file in part.copies.iter().filter(|f| f.is_file()) {
            if let Some(name) = file.file_name() {
                copy_file(file, &dir.join(name))?;
            }
        }
    }
    // A check workload's answers, always beside its own record (the primary is counted, never a check workload).
    let check = match part.check {
        Some(check) => {
            if let Some(file) = check["file"].as_str().map(Path::new).filter(|f| f.is_file()) {
                copy_file(file, &staging.join(&own).join(CHECK_FILE))?;
            }
            Some(json!({"calls":check["calls"],"agreed":check["agreed"],"record":target.join(&own).join(CHECK_FILE)}))
        }
        None => None,
    };
    let score = part.timing.as_ref().map(|t| RecordedScore { record: target.join(&relative).join(timing_name(t)), ..t.score.clone() });
    let race = part.timing.as_ref().filter(|t| t.raced).map(|t| target.join(&relative).join(timing_name(t)));
    let uses: Vec<VerusStorageUseV1> = serde_json::from_value(part.admission["uses"].clone()).unwrap_or_default();
    let general = member_general(part.member);
    let record = WorkloadRecord {
        format_version: 1,
        version: version.to_string(),
        workload: part.name.to_string(),
        role: part.role.name().to_string(),
        scale: part.scale.to_string(),
        score: score.clone(),
        cells: part.timing.as_ref().map(|_| target.join(&relative).join(&cells_file)),
        serving_bytes: part.storage.serving_bytes,
        uses,
        module_lines: part.member.map_or(0, |m| m.own_module_lines),
        race: race.clone(),
        parent: part.timing.as_ref().and_then(|t| t.parent).map(String::from),
        primary: part.primary,
        check: check.clone(),
        general: Some(general.clone()),
    };
    write_value(&staging.join(&own).join(WORKLOAD_RECORD_FILE), &json!(record))?;
    let verification = &part.build["verification"];
    let exempt = part.role == MemberRole::Check;
    let decision = if exempt { json!("exempt: a check workload's storage is not held to the budget") } else { part.storage.decision.clone() };
    Ok(json!({"role":part.role.name(),"primary":part.primary,"scale":part.scale,"score":score,
        "times":{part.scale:{"race":race,"check":check.as_ref().map(|c| c["record"].clone())}},
        "storage":{"serving_bytes":part.storage.serving_bytes,"budget_bytes":if exempt { Value::Null } else { json!(part.storage.budget_bytes) },
            "plain_storage_bytes":part.storage.plain_storage_bytes,"decision":decision},
        "proof":{"errors":verification["errors"],"verified":verification["verified"],"wall_ns":part.build["wall_ns"]},
        "admission":{"library":part.library,"package":part.admission["package"]},
        "general":general,"check":check,"origin":part.origin}))
}

/// `version.json` `combined_score` of a version of a run of several workloads (the workloads fixture): the sums over its counted
/// workloads' scores in `workloads` (its `version.json` `workloads` entries, in run order). `Null` without a counted
/// workload with a score.
pub fn combined_record(workloads: &serde_json::Map<String, Value>, order: &[String]) -> Value {
    let mut counted = vec![];
    for name in order {
        let entry = &workloads[name.as_str()];
        if entry["role"] == MemberRole::Counted.name()
            && let Ok(score) = serde_json::from_value::<RecordedScore>(entry["score"].clone())
        {
            counted.push((name.as_str(), score.score, score.cells));
        }
    }
    if counted.is_empty() {
        return Value::Null;
    }
    CombinedScore::of(&counted).map_or(Value::Null, |c| json!(c))
}

/// `version.json` `general` of a version of a run of several workloads (the workloads fixture): whether it is one
/// engine (no workload with a module of its own or an inherited storage: the condition for naming a publication
/// version), the workloads with an own module, every inherited storage by workload, and the digest of the shared
/// sources (the primary's crate's). When the crates were frozen from `one_workspace` (every version but the root, whose
/// sides are different engines) they have the same digest; a difference is recorded (`shared_digests_differ`), a
/// framework defect for the operator to look at.
pub fn general_record(members: &[(&str, Option<&MemberRecord>)], one_workspace: bool) -> Value {
    let own: Vec<&str> = members.iter().filter(|(_, m)| m.is_some_and(|m| m.own_module_lines > 0)).map(|(n, _)| *n).collect();
    let mut own_sorted = own.clone();
    own_sorted.sort();
    let inherited: Vec<Value> = members.iter().filter_map(|(n, m)| m.filter(|m| !m.inherited_storages.is_empty()).map(|m| json!({"workload":n,"storages":m.inherited_storages}))).collect();
    let digests: Vec<&str> = members.iter().filter_map(|(_, m)| m.map(|m| m.shared_sources_digest.as_str())).collect();
    let mut general = json!({"one_engine":own.is_empty() && inherited.is_empty(),"own_modules":own_sorted,"inherited_storages":inherited,
        "shared_digest":digests.first().copied()});
    // The crates of one submission are frozen from one workspace: a differing digest would be a framework defect.
    if one_workspace && digests.iter().any(|d| Some(*d) != digests.first().copied()) {
        general["shared_digests_differ"] = json!(members.iter().map(|(n, m)| json!({"workload":n,"digest":m.map(|m| &m.shared_sources_digest)})).collect::<Vec<_>>());
    }
    general
}

/// The code of a version of a run of several workloads (module documentation) into `staging` from its crates
/// `(workload, frozen directory)`, the primary's first (`engine::submission::members::write_member_code`), every crate's
/// frozen storages (its family instances, which have the same name in every workload) kept per workload under
/// `code/instances/<workload>/` (a record: a session's workspace is seeded from the families, not from them), and the
/// reading view of every `.rs` file of the shared engine, the modules, the families and the plans.
pub fn write_members_code(staging: &Path, crates: &[(&str, &Path)]) -> Result<(), AdmissionError> {
    let code = staging.join("code");
    super::super::submission::members::write_member_code(&code, crates)?;
    for (workload, frozen) in crates {
        if frozen.join("storages").is_dir() {
            copy_tree(&frozen.join("storages"), &code.join(INSTANCES_DIRECTORY).join(workload), false)?;
        }
    }
    for root in ["agent", WORKLOADS_DIRECTORY, super::super::submission::members::VERSION_FAMILIES_DIRECTORY, super::super::submission::PLANS_DIRECTORY] {
        for file in rust_files(&code.join(root)) {
            let relative = file.strip_prefix(&code).map_err(AdmissionError::tool)?;
            let view = staging.join("code-view").join(format!("{}.md", relative.display()));
            let text = fs::read_to_string(&file).map_err(AdmissionError::tool)?;
            write_text(&view, &crate::output::code_view(&text))?;
        }
    }
    Ok(())
}

/// The seed manifest of a version of a run of several workloads: the stage form ([`stage_seed_manifest`]: each
/// workload's admitted storage uses and its own module files) with every family's source named as the version's code
/// holds it (`code/families/<family>/verus-family.json`; a session's seeding names them at their workspace paths).
pub fn members_seed_manifest(manifest: &EngineManifest, uses: &[(String, Vec<VerusStorageUseV1>)]) -> EngineManifest {
    stage_seed_manifest(manifest, uses).with_version_family_sources()
}

impl EngineBench<'_> {
    /// Every workload's records of an accepted version of a run of several workloads into its folder being staged at
    /// `staging` (renamed to `target`), and its `version.json` `workloads`, `combined_score` and `general` (the
    /// workloads fixture; [`write_member`]): the primary's from the version's own records at the folder's top (`record`: the
    /// evaluation's record with the admission; `engine`: the primary's frozen crate), every other workload's from
    /// `record.workloads.<name>` under `workloads/<name>/`. Returns `(workloads, combined_score, general)`.
    pub(in crate::engine) fn write_member_workloads(&self, staging: &Path, target: &Path, node: &TreeNode, record: &Value, engine: &FrozenEngine) -> Result<(Value, Value, Value), AdmissionError> {
        let stage = self.stage.ok_or_else(|| AdmissionError::tool("a version of several workloads' records outside such a run"))?;
        let general = self.inputs().general.clone().ok_or_else(|| AdmissionError::tool("a version of several workloads without general inputs"))?;
        let cells = |value: &Value| serde_json::from_value::<Vec<CellResult>>(value.clone()).map_err(AdmissionError::tool);
        let score = node.score.clone().ok_or_else(|| AdmissionError::tool("an accepted version without a score"))?;
        let primary_cells = cells(&record["candidate_cells"])?;
        let race = target.join("race.json");
        let primary_member = engine.workload.as_ref().and_then(|w| w.member.clone());
        let storage = |policy: &Value, general: &super::super::role::GeneralInputs| StorageFacts {
            serving_bytes: policy["serving_bytes"].as_u64(),
            budget_bytes: general.scale.original_data_bytes,
            plain_storage_bytes: general.plain_storage_bytes,
            decision: policy["budget_decision"].clone(),
        };
        let primary = MemberPart {
            name: &stage.workload,
            role: stage.role,
            primary: true,
            scale: &general.scale.name,
            timing: Some(MemberTiming { cells: &primary_cells, score: &score, timing: &race, raced: true, parent: record["parent"].as_str() }),
            check: None,
            copies: vec![],
            admission: &record["admission"],
            library: &self.bench.config.library,
            storage: storage(&record["storage_policy_at_evaluation"], &general),
            build: &record["build"],
            member: primary_member.as_ref(),
            origin: Value::Null,
        };
        let mut workloads = serde_json::Map::new();
        workloads.insert(stage.workload.clone(), write_member(staging, target, &node.id, &primary)?);
        let mut members: Vec<(String, Option<MemberRecord>)> = vec![(stage.workload.clone(), primary_member.clone())];
        for side in &stage.sides {
            let other = &record["workloads"][side.name.as_str()];
            let general = side.config.inputs.general.clone().ok_or_else(|| AdmissionError::tool(format!("workload {}: no general inputs", side.name)))?;
            let member: Option<MemberRecord> = serde_json::from_value(other["member"].clone()).ok();
            let other_cells = if other["candidate_cells"].is_array() { cells(&other["candidate_cells"])? } else { vec![] };
            let other_score: Option<RecordedScore> = serde_json::from_value(other["score"].clone()).ok();
            let other_race = other["race"].as_str().map(PathBuf::from);
            let timing = match (&other_score, &other_race) {
                (Some(score), Some(race)) => Some(MemberTiming { cells: &other_cells, score, timing: race, raced: true, parent: other["parent"].as_str() }),
                _ => None,
            };
            let part = MemberPart {
                name: &side.name,
                role: side.role,
                primary: false,
                scale: &general.scale.name,
                timing,
                check: other["check"].is_object().then_some(&other["check"]),
                copies: other["finished_checks"]["variants"]["file"].as_str().map(PathBuf::from).into_iter().collect(),
                admission: &other["admission"],
                library: &side.view.library,
                storage: storage(&other["storage_policy_at_evaluation"], &general),
                build: &other["build"],
                member: member.as_ref(),
                origin: Value::Null,
            };
            workloads.insert(side.name.clone(), write_member(staging, target, &node.id, &part)?);
            members.push((side.name.clone(), member));
        }
        let order: Vec<String> = members.iter().map(|(n, _)| n.clone()).collect();
        let combined = combined_record(&workloads, &order);
        let general = general_record(&members.iter().map(|(n, m)| (n.as_str(), m.as_ref())).collect::<Vec<_>>(), true);
        Ok((Value::Object(workloads), combined, general))
    }
}

/// The code of a stage version (module documentation) into `staging` from its crates `(workload, frozen directory)`,
/// the goal's first: the shared engine from the goal's crate, each workload's module from its own crate, every crate's
/// workspace storages and the reading view.
pub fn write_stage_code(staging: &Path, crates: &[(&str, &Path)]) -> Result<(), AdmissionError> {
    let code = staging.join("code");
    let Some((_, goal)) = crates.first() else { return Err(AdmissionError::tool("a stage version without its goal crate")) };
    copy_tree(&goal.join("crate/src/agent"), &code.join("agent"), false)?;
    let composed = code.join("agent").join(WORKLOAD_MODULE);
    if composed.exists() {
        fs::remove_dir_all(&composed).map_err(|e| AdmissionError::tool(format!("{}: {e}", composed.display())))?;
    }
    // The kept crates' storages first, so a storage name both use keeps the goal's sources.
    for (workload, frozen) in crates.iter().rev() {
        let module = frozen.join("crate/src/agent").join(WORKLOAD_MODULE);
        if module.is_dir() {
            copy_tree(&module, &code.join(WORKLOADS_DIRECTORY).join(workload), false)?;
        }
        if frozen.join("storages").is_dir() {
            copy_tree(&frozen.join("storages"), &code.join("storages"), false)?;
        }
    }
    for root in ["agent", WORKLOADS_DIRECTORY] {
        for file in rust_files(&code.join(root)) {
            let relative = file.strip_prefix(&code).map_err(AdmissionError::tool)?;
            let view = staging.join("code-view").join(format!("{}.md", relative.display()));
            let text = fs::read_to_string(&file).map_err(AdmissionError::tool)?;
            write_text(&view, &crate::output::code_view(&text))?;
        }
    }
    Ok(())
}

/// The stage-form seed manifest of a version: `manifest`'s modules, compiler and notes, no storage use of its own, and
/// one entry per workload of `uses` (in that order) with its crate's admitted storage uses and the modules `manifest`
/// declares for it (none when it names the workload not).
pub fn stage_seed_manifest(manifest: &EngineManifest, uses: &[(String, Vec<VerusStorageUseV1>)]) -> EngineManifest {
    let workloads = uses
        .iter()
        .map(|(name, uses)| WorkloadModules {
            name: name.clone(),
            storage_uses: uses.iter().map(|u| StorageUseDeclaration::admitted(&u.name, u.package)).collect(),
            modules: manifest.workloads.iter().find(|w| w.name == *name).map(|w| w.modules.clone()).unwrap_or_default(),
        })
        .collect();
    EngineManifest { crate_dir: CRATE_DIRECTORY.into(), storage_uses: vec![], workloads, ..manifest.for_seed() }
}

/// Every `.rs` file under `dir`, sorted (none when it does not exist).
fn rust_files(dir: &Path) -> Vec<PathBuf> {
    let mut found = vec![];
    for entry in fs::read_dir(dir).into_iter().flatten().flatten() {
        let path = entry.path();
        if path.is_dir() {
            found.extend(rust_files(&path));
        } else if path.extension().is_some_and(|x| x == "rs") {
            found.push(path);
        }
    }
    found.sort();
    found
}

pub(super) fn write_value(path: &Path, value: &Value) -> Result<(), AdmissionError> {
    write_text(path, &format!("{}\n", serde_json::to_string_pretty(value).map_err(AdmissionError::tool)?))
}

pub(super) fn write_text(path: &Path, text: &str) -> Result<(), AdmissionError> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(AdmissionError::tool)?;
    }
    fs::write(path, text).map_err(|e| AdmissionError::tool(format!("{}: {e}", path.display())))
}

pub(super) fn copy_file(from: &Path, to: &Path) -> Result<(), AdmissionError> {
    if let Some(parent) = to.parent() {
        fs::create_dir_all(parent).map_err(AdmissionError::tool)?;
    }
    fs::copy(from, to).map(drop).map_err(|e| AdmissionError::tool(format!("copy {} to {}: {e}", from.display(), to.display())))
}
