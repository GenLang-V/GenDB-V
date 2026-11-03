//! `gendb engine prepare` of a run of several workloads (no author, $0; idempotent and resumable like version 0's): the
//! root `v000` with one side per workload, each admitted in its own library as its first engine version (lineage
//! `framework_generated`: no author, no parent in this run). Each side writes its admission's intent before the
//! admission and its admission after it (`engine/seed/<name>/admitting.json`, `admitted.json`), so a resumed preparation
//! admits every side once per library. Then the folder `versions/v000`, the selection in every library and the main
//! line. [`seed_root`] is the order of these steps over [`RootWork`] (real: [`FrameworkRoot`]; tests: a canned one).
//!
//! **A stage run** (`engine.stage`):
//! 1. **Out of the box** (`engine/seed/out-of-the-box/`, [`OutOfTheBox`]): the seed version's `agent/**` and module list
//!    (`engine::submission::write_root_from_version`), with the goal's plain storage uses, frozen for the goal under the
//!    stage rules; when frozen, its whole crate verified; when verified, its storages and budget checked, timed alone at
//!    the goal's scale and its finished templates checked (version 0's plan, `engine::protocol::VERSION_ZERO`). Every
//!    outcome is recorded (`record.json`, `OUT_OF_THE_BOX.md`): the refusal, the first compile or Verus errors, or the
//!    score. Only the first blocking layer is seen.
//! 2. **The sides**, node kind `stage_seed`, one per workload under `engine/seed/<name>/`: every kept workload's side is
//!    the seed's code over the seed's storage uses in its library (verified, its storages checked, timed alone at its
//!    scale, its variants checked at its first scale; no profile: the seed run's profiles exist); the goal's side is the
//!    seed's code when it was admissible out of the box (the root is then one engine), else version 0 over the goal's
//!    flat storage (generated, verified, timed alone, checked and profiled as today's version 0).
//! 3. The folder (the seed's code and notebook for the first session, a stage-form manifest with every workload's uses
//!    and no module, the seed run's `TREE.md` and `FINDINGS.md` under `stage1/`, every side's records).
//!
//! **A run of several workloads** (`engine.workloads`; the workloads fixture `version_root`), node kind
//! `workload_seed`:
//! 1. **The sides**, one per workload under `engine/seed/<name>/`: a workload with a seed of its own (the primary's is
//!    the primary seed) gets that seed's code, module, families and plans over that seed's storage uses, which its
//!    library holds (`engine::submission::members::write_side_root` from a version folder, `write_source_root` from an
//!    exported engine folder); a workload without one gets the primary seed's code **out of the box**
//!    (`engine/seed/<name>/out-of-the-box/`, over its plain storage or the seed's storage families, without the seed's
//!    own modules), when that is admissible, else version 0 over its plain flat storage. Each side is frozen for its
//!    workload alone (`MemberCrate { workloads: [name] }`) under the run's rule set, verified whole, its storages checked
//!    (a check workload is exempt from the budget), then a counted or kept workload's side timed alone at its scale and
//!    its finished templates checked (version 0's plan for the primary, the development plan otherwise), a check
//!    workload's side answered at every visible binding (`engine::stage::members`) and its variants checked.
//! 2. The folder: the primary side's code (its shared engine, module, families and plans; `code/`) and its seed's
//!    notebook for the first session, a seed manifest with every workload's uses, every side's records
//!    (`workloads/<name>/`: `workload.json`, `SIDE.md`, `OUT_OF_THE_BOX.md` when tried, its timing or check), every other
//!    side's code, module, storage author files, notebook and manifest under `root-sides/<name>/` (read-only in every
//!    session's workspace) and the code of the seeds' common ancestor under `root-sides/ancestor/` when GenDB finds one
//!    (following each seed version's parents, then its run's root's seed, across runs); `version.json` with every
//!    workload's entry and its side's `origin`, the combined score and the one-engine record.
//!
//! Trust: none in proofs. The sides are verified whole by Verus; the choice of each side, the copies and the records are
//! host code used for records.

use super::records::{MemberPart, MemberTiming, StorageFacts, WorkloadPart, copy_file, members_seed_manifest, stage_seed_manifest, write_member, write_members_code, write_text, write_value, write_workload};
use super::StageRun;
use crate::engine::acceptance::{AdmissionIntent, CheckedEngine, ENGINE_FINISHED_CHECKS_KIND, Runnable, fresh_directory, main_line_lock, select_version};
use crate::engine::branches::{VERSION_ZERO_TIMING_KIND, framework_role};
use crate::engine::protocol::{DEVELOPMENT, EvaluationPlan, VERSION_ZERO};
use crate::engine::role::{EngineAuthorRole, EngineBench, copy_tree, float_free, storage_inputs, write_matrix};
use crate::engine::score::CellResult;
use crate::engine::submission::members::{MemberRecord, write_side_root, write_source_root};
use crate::engine::submission::{
    CRATE_DIRECTORY, EngineBuild, EngineFreeze, EngineManifest, FrozenEngine, MANIFEST_FILE, PLANS_DIRECTORY, VERSION_ZERO_NOTES, WORKLOADS_DIRECTORY, WorkloadModules, write_root_from_version,
    write_root_version,
};
use crate::engine::tree::{self, MainLineChange, NodeKind, ROOT_VERSION, RecordedScore, TreeNode, VersionTree, append_main_line};
use crate::controller::author::CandidateSubmission;
use crate::controller::layout::NOTES_FILE;
use crate::controller::records::{now_unix_ms, read_json, write_json_atomic};
use crate::controller::request::{MemberRole, Seed, SeedVersion, WorkloadForm};
use crate::prompts::engine_contract::WorkloadRole;
use crate::query::candidate::StorageUseDeclaration;
use crate::tools::TrialVerification;
use gendb_artifacts::verus::{VERUS_ENGINE_LINEAGE_KIND, VerusEngineLineageV1, engine_selections, engine_versions};
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_verification::admission::{AdmissionError, FailureClass};
use gendb_verification::obligations::interpreter_engine;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

/// The root's records under the engine directory (`engine/seed/`).
pub const SEED_DIRECTORY: &str = "seed";
/// The out-of-the-box record's directory under it (a stage run's), or under a workload's side directory (a run of
/// several workloads').
pub const OUT_OF_THE_BOX_DIRECTORY: &str = "out-of-the-box";
/// The out-of-the-box record as authors and the operator read it.
pub const OUT_OF_THE_BOX_FILE: &str = "OUT_OF_THE_BOX.md";
/// The out-of-the-box record.
const OUT_OF_THE_BOX_RECORD: &str = "record.json";
/// A root side's admission (`engine/seed/<name>/admitted.json`; its intent is `admitting.json` beside it).
const SIDE_ADMITTED_FILE: &str = "admitted.json";
/// The seed run's version tree and findings in the root folder and the first workspace (read-only history; a stage
/// run's).
pub const STAGE_ONE_DIRECTORY: &str = "stage1";
/// Every side but the primary's in the root folder and every session's workspace (read-only; a run of several
/// workloads').
pub const ROOT_SIDES_DIRECTORY: &str = "root-sides";
/// The seeds' common ancestor's code under [`ROOT_SIDES_DIRECTORY`].
pub const ANCESTOR_DIRECTORY: &str = "ancestor";
/// A side's record in the root folder (`workloads/<name>/SIDE.md`; a run of several workloads').
pub const SIDE_FILE: &str = "SIDE.md";
/// The reason of the stage root's selection in every library and of its main-line change. Its admission's lineage is
/// `framework_generated` in every library (no author and no parent in this run; the library knows no other root kind),
/// and the tree's node kind `stage_seed` says what it was made from.
const STAGE_SEED_REASON: &str = "stage_seed";
/// The reason of the root's selection and main-line change in a run of several workloads (node kind `workload_seed`).
const WORKLOAD_SEED_REASON: &str = "workload_seed";

/// How far a seed's code got on a workload out of the box.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum OutOfTheBoxStatus {
    /// Refused at freeze (the manifest or the source rules).
    Refused,
    /// rustc stopped it (the crate does not assemble).
    NotAssembled,
    /// Verus stopped it (a proof obligation or a Verus refusal).
    NotVerified,
    /// Verified whole; then storages, timing (or answers) and checks.
    Verified,
}

/// The out-of-the-box record (`record.json` of its directory); the stage fixture shows [`OutOfTheBox::view`], the workloads fixture
/// [`OutOfTheBox::side_view`].
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct OutOfTheBox {
    pub status: OutOfTheBoxStatus,
    /// The step that stopped it (`freeze`, `compile`, `verus`, `storages`, `timing`, `checks`, `answers`), or `timing`
    /// (`answers` for a check workload) when it was timed (answered) and its finished templates checked.
    pub step: String,
    /// The first lines of the blocking errors (none when it passed).
    pub first_errors: Vec<String>,
    /// Its recorded score at the workload's scale when timed.
    pub score: Option<RecordedScore>,
    /// `OUT_OF_THE_BOX.md`.
    pub record: PathBuf,
    /// Its attempt directory (workspace, frozen crate, evaluation).
    pub directory: PathBuf,
    /// Verified, timed (or answered) and checked: its admission's intent is the workload's side of the root.
    pub admissible: bool,
    pub at_unix_ms: u64,
}

impl OutOfTheBox {
    /// A seed stopped at `step` by `error` (its first error lines kept).
    fn stopped(status: OutOfTheBoxStatus, step: &str, error: &AdmissionError, directory: &Path) -> Self {
        Self { status, step: step.into(), first_errors: first_errors(&error.message), score: None, record: PathBuf::new(), directory: directory.to_path_buf(), admissible: false, at_unix_ms: now_unix_ms() }
    }

    /// The stage view's `seed.out_of_the_box` (the stage fixture): status, step, first errors, score and record.
    pub fn view(&self) -> Value {
        json!({"status":self.status,"step":self.step,"first_errors":self.first_errors,"score":self.score,"record":self.record})
    }

    /// A side's `origin.out_of_the_box` (the workloads fixture): status, step, first errors and `record` (the copy in the root
    /// folder).
    pub fn side_view(&self, record: &Path) -> Value {
        json!({"status":self.status,"step":self.step,"first_errors":self.first_errors,"record":record})
    }

    /// The stage run's record read back from `engine_dir` (`None` before the preparation made it).
    pub fn read(engine_dir: &Path) -> Option<Self> {
        Self::read_at(&out_of_the_box_directory(engine_dir))
    }

    /// The record in the out-of-the-box directory `dir`, if any.
    pub fn read_at(dir: &Path) -> Option<Self> {
        read_json(&dir.join(OUT_OF_THE_BOX_RECORD)).ok()
    }

    /// The outcome in words.
    fn outcome(&self) -> String {
        match self.status {
            OutOfTheBoxStatus::Refused => "refused at freeze (the manifest or the source rules)".to_string(),
            OutOfTheBoxStatus::NotAssembled => "not assembled: rustc stopped it".to_string(),
            OutOfTheBoxStatus::NotVerified => "assembled, not verified: Verus stopped it".to_string(),
            OutOfTheBoxStatus::Verified if self.admissible && self.step == "answers" => "verified whole, then every template answered and its variants checked".to_string(),
            OutOfTheBoxStatus::Verified if self.admissible => "verified whole, then timed alone and its finished templates checked".to_string(),
            OutOfTheBoxStatus::Verified => format!("verified whole, then stopped at {}", self.step),
        }
    }

    /// The score and the first errors as markdown.
    fn details(&self) -> String {
        let mut out = String::new();
        if let Some(score) = &self.score {
            out.push_str(&format!("\nScore at {}: {} of {} cells finished, normalized time {}{}.\n", score.scale, score.score.finished, score.cells, score.score.normalized_time,
                if score.beats_both { ", beats both baselines" } else { "" }));
        }
        if !self.first_errors.is_empty() {
            out.push_str(&format!("\n## First errors\n\n```text\n{}\n```\n", self.first_errors.join("\n")));
        }
        out
    }

    /// `OUT_OF_THE_BOX.md` of a stage run.
    fn markdown(&self, goal: &str, seed: &SeedVersion) -> String {
        let mut out = format!(
            "# Out of the box: the seed on `{goal}`\n\nGenDB froze the seed {} (`{}`) for the goal workload `{goal}` over its plain storage under this stage run's rules (no author): {} (step `{}`). Only the first blocking layer is seen.\n",
            seed.version,
            seed.run.display(),
            self.outcome(),
            self.step
        );
        out.push_str(&self.details());
        out.push_str(&format!(
            "\n{}\n\nRecords: `{}` (workspace `author/`, frozen crate `frozen/`, evaluation `evaluation/`).\n",
            if self.admissible { format!("This frozen crate is the root's side on `{goal}`: the root is one engine.") } else { format!("The root's side on `{goal}` is version 0 over its flat storage.") },
            self.directory.display()
        ));
        out
    }

    /// `OUT_OF_THE_BOX.md` of a workload of a run of several workloads.
    fn member_markdown(&self, workload: &str, seed: &Seed) -> String {
        let mut out = format!(
            "# Out of the box: the primary seed on `{workload}`\n\nGenDB froze the primary seed {} for the workload `{workload}` (its shared engine, default module and storage families, without the seed's own workload modules, over this workload's plain storage or the seed's families) under this run's rules (no author): {} (step `{}`). Only the first blocking layer is seen.\n",
            seed_text(seed),
            self.outcome(),
            self.step
        );
        out.push_str(&self.details());
        out.push_str(&format!(
            "\n{}\n\nRecords: `{}` (workspace `author/`, frozen crate `frozen/`, evaluation `evaluation/`).\n",
            if self.admissible { format!("This frozen crate is the root's side on `{workload}`.") } else { format!("The root's side on `{workload}` is version 0 over its plain storage.") },
            self.directory.display()
        ));
        out
    }
}

/// A seed in words: `v004 of the run `<run>`` (`(its workload `sec`)`), or `the exported engine `<folder>``.
fn seed_text(seed: &Seed) -> String {
    match seed {
        Seed::Run { version, workload } => format!("{} of the run `{}`{}", version.version, version.run.display(), workload.as_ref().map_or(String::new(), |w| format!(" (its workload `{w}`)"))),
        Seed::Source { source } => format!("the exported engine `{}`", source.display()),
    }
}

/// A seed as a side's origin records it (the workloads fixture `side_origin.seed`): `run`, `version`, `workload` and `source`,
/// each null when it does not apply; `Null` without a seed.
pub fn seed_record(seed: Option<&Seed>) -> Value {
    match seed {
        Some(Seed::Run { version, workload }) => json!({"run":version.run,"version":version.version,"workload":workload,"source":null}),
        Some(Seed::Source { source }) => json!({"run":null,"version":null,"workload":null,"source":source}),
        None => Value::Null,
    }
}

/// The first blocking lines of an error message: each `error` line with the location line after it, at most eight; else
/// its first four lines.
pub fn first_errors(message: &str) -> Vec<String> {
    let lines: Vec<&str> = message.lines().map(str::trim_end).filter(|l| !l.trim().is_empty()).collect();
    let mut found = vec![];
    for (index, line) in lines.iter().enumerate() {
        if line.trim_start().starts_with("error") && found.len() < 8 {
            found.push(line.to_string());
            if let Some(location) = lines.get(index + 1).filter(|l| l.trim_start().starts_with("-->")) {
                found.push(location.to_string());
            }
        }
    }
    found.truncate(8);
    if found.is_empty() { lines.iter().take(4).map(|l| l.to_string()).collect() } else { found }
}

/// Where a crate that froze was stopped by its whole-crate Verus run: rustc's errors (`error[E…]`) leave it not
/// assembled (step `compile`), any other failure not verified (step `verus`).
pub fn blocked_at_build(error: &AdmissionError) -> (OutOfTheBoxStatus, &'static str) {
    if error.class != FailureClass::ProofFailure && error.message.contains("error[E") { (OutOfTheBoxStatus::NotAssembled, "compile") } else { (OutOfTheBoxStatus::NotVerified, "verus") }
}

/// `engine/seed/out-of-the-box` (a stage run's).
pub fn out_of_the_box_directory(engine_dir: &Path) -> PathBuf {
    engine_dir.join(SEED_DIRECTORY).join(OUT_OF_THE_BOX_DIRECTORY)
}

/// `engine/seed/<name>/out-of-the-box` (a workload of a run of several workloads).
pub fn member_out_of_the_box_directory(engine_dir: &Path, name: &str) -> PathBuf {
    engine_dir.join(SEED_DIRECTORY).join(name).join(OUT_OF_THE_BOX_DIRECTORY)
}

/// What a root side is made from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SideSource {
    /// A seed's code over that seed's storage uses: a stage run's seed (for the goal over its plain uses, when admissible
    /// out of the box), or a workload's own seed in a run of several workloads.
    Seed,
    /// Version 0, the verified interpreter over the workload's flat storage.
    VersionZero,
    /// A run of several workloads: the primary seed's code, admissible out of the box on a workload without a seed.
    OutOfTheBox,
}

impl SideSource {
    /// The side's `origin.kind` (the workloads fixture).
    pub fn kind(self) -> &'static str {
        match self {
            SideSource::Seed => "seed",
            SideSource::VersionZero => "version_0",
            SideSource::OutOfTheBox => "out_of_the_box",
        }
    }
}

/// What a root side's admission intent keeps (`AdmissionIntent::keep`).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SideKeep {
    pub source: SideSource,
    pub frozen: PathBuf,
    /// Its recorded score when timed alone (`None` for a check workload's side, which is answered, never timed).
    #[serde(default)]
    pub score: Option<RecordedScore>,
    pub cells: Vec<CellResult>,
    pub checks: Value,
    pub storage_policy: Value,
    /// A check workload's side: its answers (`calls`, `agreed`, `file`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub check: Option<Value>,
}

/// A root side admitted (`engine/seed/<name>/admitted.json`): what the folder records of it. `profile` is filled after
/// the admission (`Null` until then; the goal's or primary's side made from version 0 only).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct SideAdmission {
    pub workload: String,
    pub keep: SideKeep,
    pub admission: Value,
    pub evaluation: PathBuf,
    pub build: Value,
    #[serde(default)]
    pub profile: Value,
}

/// What the root needs from the framework (real: [`FrameworkRoot`]; tests: a canned implementation).
pub(in crate::engine) trait RootWork {
    /// The (primary) seed's code frozen and evaluated for `workload` out of the box in the fresh attempt directory `dir`:
    /// its record (without the path of its markdown) and, when admissible, the intent of its admission as the
    /// workload's side.
    fn out_of_the_box(&mut self, workload: &str, dir: &Path) -> Result<(OutOfTheBox, Option<AdmissionIntent>), AdmissionError>;
    /// Workload `workload`'s side made from `source` and evaluated in the fresh attempt directory `dir`: the intent of
    /// its admission (its `keep` a [`SideKeep`]). Any refusal is the framework's: the root cannot be seeded.
    fn evaluate_side(&mut self, workload: &str, source: SideSource, dir: &Path) -> Result<AdmissionIntent, AdmissionError>;
    /// Admit `workload`'s side from its intent in its library, once (adopted when the library holds it): the admission
    /// record with `library_version`.
    fn admit_side(&mut self, workload: &str, intent: &AdmissionIntent) -> Result<Value, AdmissionError>;
    /// The profile of the goal's (primary's) side (never gating).
    fn profile_side(&mut self, workload: &str, side: &SideAdmission) -> Value;
    /// Select `v000` in every library (a library that already selected it keeps that selection); the primary library's
    /// selection record.
    fn select_root(&mut self) -> Result<ContentId, AdmissionError>;
}

/// One workload as the root's folder records it.
#[derive(Clone, Debug)]
pub struct SideFacts {
    pub name: String,
    /// Its role in a stage run's records (`Goal` for the primary).
    pub role: WorkloadRole,
    /// Its role in a run of several workloads (a stage run's goal is counted, its kept workloads kept).
    pub member: MemberRole,
    pub primary: bool,
    /// The seed of its side (a run of several workloads; the primary's is the primary seed).
    pub seed: Option<Seed>,
    pub scale: String,
    pub library: PathBuf,
    pub budget_bytes: u64,
    pub plain_storage_bytes: u64,
}

/// What the root is seeded from and for.
pub struct RootPlan<'a> {
    pub engine_dir: &'a Path,
    pub form: WorkloadForm,
    /// The primary seed (a stage run's seed version).
    pub seed: Option<Seed>,
    /// Every workload, the primary first.
    pub workloads: Vec<SideFacts>,
    /// The run's branch slots (the tree views).
    pub branches: &'a [String],
}

impl RootPlan<'_> {
    fn primary(&self) -> &SideFacts {
        &self.workloads[0]
    }

    /// A stage run's seed version.
    fn stage_seed(&self) -> Result<&SeedVersion, AdmissionError> {
        match &self.seed {
            Some(Seed::Run { version, .. }) => Ok(version),
            _ => Err(AdmissionError::tool("a stage root without its seed version")),
        }
    }
}

/// The root of a run of several workloads (module documentation), over `work`. Idempotent: a root with a main-line head
/// is returned as it is. Returns the preparation's record of it.
pub(in crate::engine) fn seed_root(work: &mut impl RootWork, plan: &RootPlan<'_>) -> Result<Value, AdmissionError> {
    let engine_dir = plan.engine_dir;
    let tree = VersionTree::read(engine_dir).map_err(AdmissionError::tool)?;
    if let (Some(v0), Some(_)) = (tree.version(ROOT_VERSION), tree.main_line_head()) {
        let out_of_the_box = match plan.form {
            WorkloadForm::Workloads => json!(plan.workloads.iter().filter_map(|w| OutOfTheBox::read_at(&member_out_of_the_box_directory(engine_dir, &w.name)).map(|o| (w.name.clone(), o.view()))).collect::<BTreeMap<_, _>>()),
            _ => json!(OutOfTheBox::read(engine_dir).map(|o| o.view())),
        };
        return Ok(json!({"status":"present","version":v0.id,"directory":v0.directory(engine_dir),"out_of_the_box":out_of_the_box}));
    }
    match plan.form {
        WorkloadForm::Workloads => seed_members_root(work, plan),
        _ => seed_stage_root_sides(work, plan),
    }
}


/// Workload `facts`' side, admitted once in its library: its record when it was admitted (`engine/seed/<name>/
/// admitted.json`), else the intent of its admission (recorded in `admitting.json`, else made now by `make_intent` in
/// its side directory and written) admitted as its library's first version, then recorded.
fn admit_side_once<W: RootWork>(work: &mut W, engine_dir: &Path, facts: &SideFacts, make_intent: impl FnOnce(&mut W, &Path) -> Result<AdmissionIntent, AdmissionError>) -> Result<SideAdmission, AdmissionError> {
    let dir = engine_dir.join(SEED_DIRECTORY).join(&facts.name);
    fs::create_dir_all(&dir).map_err(AdmissionError::tool)?;
    let admitted_file = dir.join(SIDE_ADMITTED_FILE);
    if admitted_file.is_file() {
        return read_json(&admitted_file).map_err(AdmissionError::tool);
    }
    let intent_file = dir.join(crate::engine::acceptance::ADMITTING_FILE);
    let intent = match AdmissionIntent::read(&intent_file)? {
        Some(intent) => intent,
        None => {
            let intent = make_intent(work, &dir)?;
            intent.write(&intent_file)?;
            intent
        }
    };
    let mut admission = work.admit_side(&facts.name, &intent)?;
    if admission["library_version"] != 1 {
        return Err(AdmissionError::tool(format!(
            "workload {}: the root was admitted as library version {}, not 1: every library of a run of several workloads starts without engine versions",
            facts.name, admission["library_version"]
        )));
    }
    admission["evaluation"] = json!(intent.evaluation);
    let keep: SideKeep = serde_json::from_value(intent.keep.clone()).map_err(AdmissionError::tool)?;
    let side = SideAdmission { workload: facts.name.clone(), keep, admission, evaluation: intent.evaluation.clone(), build: intent.build.clone(), profile: Value::Null };
    write_json_atomic(&admitted_file, &side).map_err(AdmissionError::tool)?;
    Ok(side)
}

/// The primary's side made from version 0 is profiled once, like today's version 0 (never gating), before the folder.
fn profile_once(work: &mut impl RootWork, engine_dir: &Path, facts: &SideFacts, side: &mut SideAdmission) -> Result<(), AdmissionError> {
    if facts.primary && side.keep.source == SideSource::VersionZero && side.profile.is_null() && !root_folder(engine_dir).join(tree::NODE_FILE).is_file() {
        side.profile = work.profile_side(&facts.name, side);
        write_json_atomic(&engine_dir.join(SEED_DIRECTORY).join(&facts.name).join(SIDE_ADMITTED_FILE), side).map_err(AdmissionError::tool)?;
    }
    Ok(())
}

/// The root's selection in every library and its main-line change (`reason`), once, then the tree views.
fn select_and_record(work: &mut impl RootWork, plan: &RootPlan<'_>, node: &TreeNode, reason: &str) -> Result<(), AdmissionError> {
    let engine_dir = plan.engine_dir;
    {
        let _lock = main_line_lock(engine_dir)?;
        if VersionTree::read(engine_dir).map_err(AdmissionError::tool)?.main_line_head().is_none() {
            let selection = work.select_root()?;
            append_main_line(engine_dir, &MainLineChange { version: ROOT_VERSION.into(), previous: None, reason: reason.into(), scale: node.scale.clone(), race: None, adopted: None,
                selection, at_unix_ms: now_unix_ms() })
            .map_err(AdmissionError::tool)?;
        }
    }
    VersionTree::read(engine_dir).and_then(|t| t.write_views(engine_dir, plan.branches)).map_err(AdmissionError::tool)
}

// ------------------------------------------------------------------------------------------------ a stage run's root

/// [`seed_root`] of a stage run (module documentation, "A stage run").
fn seed_stage_root_sides(work: &mut impl RootWork, plan: &RootPlan<'_>) -> Result<Value, AdmissionError> {
    let engine_dir = plan.engine_dir;
    let seed = plan.stage_seed()?;
    let goal = plan.primary().name.clone();
    // 1. Out of the box.
    let oob_dir = out_of_the_box_directory(engine_dir);
    let oob = match OutOfTheBox::read(engine_dir) {
        Some(oob) => oob,
        None => {
            let attempt = fresh_directory(&oob_dir, "attempt")?;
            let (mut oob, intent) = work.out_of_the_box(&goal, &attempt)?;
            oob.record = oob_dir.join(OUT_OF_THE_BOX_FILE);
            if let Some(intent) = intent.filter(|_| oob.admissible) {
                intent.write(&oob_dir.join(crate::engine::acceptance::ADMITTING_FILE))?;
            }
            write_text(&oob.record, &oob.markdown(&goal, seed))?;
            write_json_atomic(&oob_dir.join(OUT_OF_THE_BOX_RECORD), &oob).map_err(AdmissionError::tool)?;
            oob
        }
    };
    // 2. Every workload's side, the goal first, each admitted once in its library.
    let mut sides = vec![];
    for facts in &plan.workloads {
        let mut side = admit_side_once(work, engine_dir, facts, |work, dir| {
            if facts.name == goal && oob.admissible {
                return AdmissionIntent::read(&oob_dir.join(crate::engine::acceptance::ADMITTING_FILE))?
                    .ok_or_else(|| AdmissionError::tool("the admissible out-of-the-box seed has no admission intent"));
            }
            let source = if facts.name == goal { SideSource::VersionZero } else { SideSource::Seed };
            work.evaluate_side(&facts.name, source, &fresh_directory(dir, "attempt")?)
        })?;
        profile_once(work, engine_dir, facts, &mut side)?;
        sides.push(side);
    }
    // 3. The folder, then the selection in every library and the main line.
    let node = write_root_folder(plan, seed, &oob, &sides)?;
    select_and_record(work, plan, &node, STAGE_SEED_REASON)?;
    Ok(json!({"status":"admitted","version":ROOT_VERSION,"directory":node.directory(engine_dir),"kind":node.kind,"out_of_the_box":oob.view(),
        "sides":sides.iter().map(|s| json!({"workload":s.workload,"source":s.keep.source,"score":s.keep.score,"library_version":s.admission["library_version"],"profile":s.profile["status"]})).collect::<Vec<_>>(),
        "one_engine":sides.iter().all(|s| s.keep.source == SideSource::Seed),"cost_usd":"0",
        "cost":"framework work: the stage root is seeded without an author; its evaluations are framework compute, not author cost"}))
}

/// `versions/v000`.
fn root_folder(engine_dir: &Path) -> PathBuf {
    tree::node_directory(engine_dir, ROOT_VERSION, true)
}

/// The stage root's folder (module documentation), written once (staged, `node.json` last). Returns its node.
fn write_root_folder(plan: &RootPlan<'_>, seed: &SeedVersion, oob: &OutOfTheBox, sides: &[SideAdmission]) -> Result<TreeNode, AdmissionError> {
    let engine_dir = plan.engine_dir;
    let goal_facts = plan.primary();
    let goal = sides.iter().find(|s| s.workload == goal_facts.name).ok_or_else(|| AdmissionError::tool("the root has no goal side"))?;
    let goal_score = goal.keep.score.clone().ok_or_else(|| AdmissionError::tool("the stage root's goal side has no score"))?;
    let one_engine = sides.iter().all(|s| s.keep.source == SideSource::Seed);
    let direction = if one_engine {
        format!("stage root: the seed {} on every workload (it verified on {} out of the box)", seed.version, goal_facts.name)
    } else {
        format!("stage root: the seed {} on every kept workload; version 0 on {} (the seed {} out of the box)", seed.version, goal_facts.name,
            match oob.status { OutOfTheBoxStatus::Refused => "was refused at freeze", OutOfTheBoxStatus::NotAssembled => "did not assemble", OutOfTheBoxStatus::NotVerified => "did not verify", OutOfTheBoxStatus::Verified => "was verified but not admissible" })
    };
    let node = TreeNode {
        format_version: 1,
        id: ROOT_VERSION.into(),
        accepted: true,
        kind: NodeKind::StageSeed,
        branch: tree::MAIN.into(),
        parents: vec![],
        scale: goal_facts.scale.clone(),
        score: Some(goal_score.clone()),
        reason: None,
        session: None,
        iteration: None,
        direction: Some(direction.clone()),
        rationale: Some(format!("seeded from {} of {}", seed.version, seed.run.display())),
        created_unix_ms: now_unix_ms(),
    };
    let target = root_folder(engine_dir);
    if target.join(tree::NODE_FILE).is_file() {
        return read_json(&target.join(tree::NODE_FILE)).map_err(AdmissionError::tool);
    }
    let staging = target.with_file_name(format!(".staging-{}-{}", node.id, now_unix_ms()));
    fs::create_dir_all(&staging).map_err(AdmissionError::tool)?;
    // The seed's code, its notebook and its run's history: what the first session continues from.
    let seed_dir = seed.directory();
    copy_tree(&seed_dir.join("code/agent"), &staging.join("code/agent"), false)?;
    write_code_view(&staging, &staging.join("code/agent"))?;
    let seed_manifest_file = ["seed-manifest.json", "manifest.json"].into_iter().map(|f| seed_dir.join(f)).find(|p| p.is_file()).ok_or_else(|| AdmissionError::tool("the seed version has no manifest"))?;
    let seed_manifest: EngineManifest = read_json(&seed_manifest_file).map_err(AdmissionError::tool)?;
    if seed_dir.join("manifest.json").is_file() {
        copy_file(&seed_dir.join("manifest.json"), &staging.join("manifest.json"))?;
    }
    let uses: Vec<(String, Vec<gendb_artifacts::verus::VerusStorageUseV1>)> =
        sides.iter().map(|s| (s.workload.clone(), serde_json::from_value(s.admission["uses"].clone()).unwrap_or_default())).collect();
    write_value(&staging.join("seed-manifest.json"), &json!(stage_seed_manifest(&seed_manifest, &uses)))?;
    if seed_dir.join(NOTES_FILE).is_file() {
        copy_file(&seed_dir.join(NOTES_FILE), &staging.join(NOTES_FILE))?;
    }
    for file in ["TREE.md", tree::FINDINGS_MARKDOWN] {
        let from = seed.run.join("engine").join(file);
        if from.is_file() {
            copy_file(&from, &staging.join(STAGE_ONE_DIRECTORY).join(file))?;
        }
    }
    // Every side's records: the goal's at the top (as version 0's), each kept one under workloads/<name>/.
    let mut workloads = serde_json::Map::new();
    for (facts, side) in plan.workloads.iter().map(|f| (f, sides.iter().find(|s| s.workload == f.name))) {
        let side = side.ok_or_else(|| AdmissionError::tool(format!("the root has no side for workload {}", facts.name)))?;
        let at_top = facts.role == WorkloadRole::Goal;
        let score_file = side.evaluation.join("score.json");
        if at_top {
            write_top_records(&staging, &facts.scale, side)?;
        }
        if side.keep.source == SideSource::VersionZero {
            copy_tree(&side.keep.frozen.join("crate/src/agent"), &staging.join(tree::WORKLOADS_DIRECTORY).join(&facts.name).join("code/agent"), false)?;
        }
        let score = side.keep.score.clone().ok_or_else(|| AdmissionError::tool(format!("the stage root's side on {} has no score", facts.name)))?;
        let part = WorkloadPart {
            name: &facts.name,
            role: facts.role,
            scale: &facts.scale,
            cells: &side.keep.cells,
            score: &score,
            timing: &score_file,
            raced: false,
            parent: None,
            copies: ["official-matrix.json", "variant-answers.json", "variant-matrix.json"].iter().map(|n| side.evaluation.join(n)).collect(),
            admission: &side.admission,
            library: &facts.library,
            storage: side_storage(facts, side),
            build: &side.build,
            module_lines: 0,
        };
        workloads.insert(facts.name.clone(), write_workload(&staging, &target, ROOT_VERSION, &part, at_top)?);
    }
    let mut times = serde_json::Map::new();
    times.insert(node.scale.clone(), json!({"score":node.score,"timing":"timed alone (no parent)","evaluation":goal.evaluation}));
    let version = json!({"format_version":1,"version":node.id,"accepted":true,"directory":target,"node":node,"parents":[],"branch":tree::MAIN,"kind":node.kind,
        "origin":{"seed":{"run":seed.run,"version":seed.version},"out_of_the_box":oob.view(),"goal_side":goal.keep.source,"one_engine":one_engine,"author":"none (seeded by GenDB)"},
        "goal":{"scale":node.scale,"workload":goal_facts.name},
        "storage":{"uses":goal.admission["uses"],"budget_rule":"the root's goal side reads the goal's plain storage (allowed as is) or the seed's storages, within its budget"},
        "times":times,"cost":{"known_provider_reported_cost_usd":"0","scope":"no author: framework work"},
        "finished_checks":goal.keep.checks,"admission":goal.admission,"profile":goal.profile,"workloads":Value::Object(workloads)});
    write_value(&staging.join("version.json"), &version)?;
    let readme = format!(
        "# Engine version {} (stage root)\n\n{direction}. The first session continues from the seed's code (`code/agent`), its notebook (`NOTES.md`) and a stage-form manifest naming every workload's storage uses (`seed-manifest.json`); the seed run's version tree and findings are under `{STAGE_ONE_DIRECTORY}/`. Out of the box: `{}`.\n{}",
        node.id,
        oob.record.display(),
        crate::output::engine::general::workloads_readme(&version).unwrap_or_default()
    );
    write_text(&staging.join("README.md"), &readme)?;
    write_value(&staging.join(tree::NODE_FILE), &json!(node))?;
    fs::rename(&staging, &target).map_err(|e| AdmissionError::tool(format!("{}: {e}", target.display())))?;
    Ok(node)
}

/// The primary side's records at the top of the root folder being staged (as version 0's): its cells at its scale, its
/// admission, and its evaluation's score, official matrix and profile.
fn write_top_records(staging: &Path, scale: &str, side: &SideAdmission) -> Result<(), AdmissionError> {
    write_value(&staging.join("cells").join(format!("{scale}.json")), &json!(side.keep.cells))?;
    write_value(&staging.join("admission.json"), &side.admission)?;
    for name in ["score.json", "official-matrix.json", crate::engine::profile::PROFILE_FILE] {
        if side.evaluation.join(name).is_file() {
            copy_file(&side.evaluation.join(name), &staging.join(name))?;
        }
    }
    if side.evaluation.join(crate::engine::profile::PROFILE_DIRECTORY).is_dir() {
        copy_tree(&side.evaluation.join(crate::engine::profile::PROFILE_DIRECTORY), &staging.join(crate::engine::profile::PROFILE_DIRECTORY), false)?;
    }
    Ok(())
}

/// A side's storage facts (its serving bytes and budget decision from its storage policy).
fn side_storage(facts: &SideFacts, side: &SideAdmission) -> StorageFacts {
    StorageFacts { serving_bytes: side.keep.storage_policy["serving_bytes"].as_u64(), budget_bytes: facts.budget_bytes, plain_storage_bytes: facts.plain_storage_bytes,
        decision: side.keep.storage_policy["budget_decision"].clone() }
}

/// The reading view of every file under `dir` (a folder's `code/...`), at `code-view/<path below code>.md` of
/// `staging`.
fn write_code_view(staging: &Path, dir: &Path) -> Result<(), AdmissionError> {
    for file in walk(dir) {
        let relative = file.strip_prefix(staging.join("code")).map_err(AdmissionError::tool)?.to_path_buf();
        write_text(&staging.join("code-view").join(format!("{}.md", relative.display())), &crate::output::code_view(&fs::read_to_string(&file).map_err(AdmissionError::tool)?))?;
    }
    Ok(())
}

/// Every file under `dir`, sorted.
fn walk(dir: &Path) -> Vec<PathBuf> {
    let mut found = vec![];
    for entry in fs::read_dir(dir).into_iter().flatten().flatten() {
        let path = entry.path();
        if path.is_dir() {
            found.extend(walk(&path));
        } else {
            found.push(path);
        }
    }
    found.sort();
    found
}

// ------------------------------------------------------------------------------------------------ a run of several workloads' root

/// [`seed_root`] of a run of several workloads (module documentation, "A run of several workloads").
fn seed_members_root(work: &mut impl RootWork, plan: &RootPlan<'_>) -> Result<Value, AdmissionError> {
    let engine_dir = plan.engine_dir;
    let mut sides = vec![];
    let mut tried: BTreeMap<String, OutOfTheBox> = BTreeMap::new();
    for facts in &plan.workloads {
        let oob_dir = member_out_of_the_box_directory(engine_dir, &facts.name);
        let mut side = admit_side_once(work, engine_dir, facts, |work, dir| {
            // A workload with a seed of its own: that seed's side.
            if facts.seed.is_some() {
                return work.evaluate_side(&facts.name, SideSource::Seed, &fresh_directory(dir, "attempt")?);
            }
            // Else the primary seed's code out of the box (recorded once), when admissible; else version 0.
            if let Some(seed) = &plan.seed {
                let oob = match OutOfTheBox::read_at(&oob_dir) {
                    Some(oob) => oob,
                    None => {
                        let attempt = fresh_directory(&oob_dir, "attempt")?;
                        let (mut oob, intent) = work.out_of_the_box(&facts.name, &attempt)?;
                        oob.record = oob_dir.join(OUT_OF_THE_BOX_FILE);
                        if let Some(intent) = intent.filter(|_| oob.admissible) {
                            intent.write(&oob_dir.join(crate::engine::acceptance::ADMITTING_FILE))?;
                        }
                        write_text(&oob.record, &oob.member_markdown(&facts.name, seed))?;
                        write_json_atomic(&oob_dir.join(OUT_OF_THE_BOX_RECORD), &oob).map_err(AdmissionError::tool)?;
                        oob
                    }
                };
                if oob.admissible {
                    return AdmissionIntent::read(&oob_dir.join(crate::engine::acceptance::ADMITTING_FILE))?
                        .ok_or_else(|| AdmissionError::tool(format!("the admissible out-of-the-box seed on {} has no admission intent", facts.name)));
                }
            }
            work.evaluate_side(&facts.name, SideSource::VersionZero, &fresh_directory(dir, "attempt")?)
        })?;
        if let Some(oob) = OutOfTheBox::read_at(&oob_dir) {
            tried.insert(facts.name.clone(), oob);
        }
        profile_once(work, engine_dir, facts, &mut side)?;
        sides.push(side);
    }
    let node = write_members_root_folder(plan, &sides, &tried)?;
    select_and_record(work, plan, &node, WORKLOAD_SEED_REASON)?;
    let version: Value = read_json(&node.directory(engine_dir).join("version.json")).map_err(AdmissionError::tool)?;
    Ok(json!({"status":"admitted","version":ROOT_VERSION,"directory":node.directory(engine_dir),"kind":node.kind,
        "sides":sides.iter().map(|s| json!({"workload":s.workload,"source":s.keep.source,"score":s.keep.score,"check":s.keep.check,"library_version":s.admission["library_version"],"profile":s.profile["status"]})).collect::<Vec<_>>(),
        "out_of_the_box":tried.iter().map(|(name, o)| (name.clone(), o.view())).collect::<BTreeMap<_, _>>(),
        "combined_score":version["combined_score"],"general":version["general"],"cost_usd":"0",
        "cost":"framework work: the root is seeded without an author; its evaluations are framework compute, not author cost"}))
}

/// The crate record of a side (`candidate.json` `workload.member` of its frozen crate), when its freeze recorded one.
fn side_member(side: &SideAdmission) -> Option<MemberRecord> {
    read_json::<FrozenEngine>(&side.keep.frozen.join("candidate.json")).ok().and_then(|e| e.workload.and_then(|w| w.member))
}

/// The notebook of a seed: a version folder's `NOTES.md`, or an exported engine folder's.
fn seed_notes(seed: Option<&Seed>) -> Option<PathBuf> {
    let file = match seed? {
        Seed::Run { version, .. } => version.directory().join(NOTES_FILE),
        Seed::Source { source } => source.join(NOTES_FILE),
    };
    file.is_file().then_some(file)
}

/// The root folder of a run of several workloads (module documentation), written once (staged, `node.json` last).
/// Returns its node.
fn write_members_root_folder(plan: &RootPlan<'_>, sides: &[SideAdmission], tried: &BTreeMap<String, OutOfTheBox>) -> Result<TreeNode, AdmissionError> {
    let engine_dir = plan.engine_dir;
    let target = root_folder(engine_dir);
    if target.join(tree::NODE_FILE).is_file() {
        return read_json(&target.join(tree::NODE_FILE)).map_err(AdmissionError::tool);
    }
    let side_of = |name: &str| sides.iter().find(|s| s.workload == name).ok_or_else(|| AdmissionError::tool(format!("the root has no side for workload {name}")));
    let primary_facts = plan.primary();
    let primary = side_of(&primary_facts.name)?;
    let primary_score = primary.keep.score.clone().ok_or_else(|| AdmissionError::tool(format!("the root's primary side on {} has no score (the primary workload is counted)", primary_facts.name)))?;
    let origin_text = |facts: &SideFacts, side: &SideAdmission| match side.keep.source {
        SideSource::Seed => format!("{}: the seed {}", facts.name, facts.seed.as_ref().map_or_else(|| "-".to_string(), seed_text)),
        SideSource::OutOfTheBox => format!("{}: the primary seed out of the box", facts.name),
        SideSource::VersionZero => format!("{}: version 0", facts.name),
    };
    let direction = format!("root of a run of several workloads: one side per workload ({})",
        plan.workloads.iter().filter_map(|f| side_of(&f.name).ok().map(|s| origin_text(f, s))).collect::<Vec<_>>().join("; "));
    let node = TreeNode {
        format_version: 1,
        id: ROOT_VERSION.into(),
        accepted: true,
        kind: NodeKind::WorkloadSeed,
        branch: tree::MAIN.into(),
        parents: vec![],
        scale: primary_facts.scale.clone(),
        score: Some(primary_score),
        reason: None,
        session: None,
        iteration: None,
        direction: Some(direction.clone()),
        rationale: Some(format!("seeded per workload; the primary {} from {}", primary_facts.name, plan.seed.as_ref().map_or_else(|| "version 0".to_string(), seed_text))),
        created_unix_ms: now_unix_ms(),
    };
    let staging = target.with_file_name(format!(".staging-{}-{}", node.id, now_unix_ms()));
    fs::create_dir_all(&staging).map_err(AdmissionError::tool)?;
    // The primary side's code, manifest and notebook: what the first session continues from.
    write_members_code(&staging, &[(primary_facts.name.as_str(), primary.keep.frozen.as_path())])?;
    let primary_manifest: EngineManifest = read_json(&primary.keep.frozen.join("manifest.json")).map_err(AdmissionError::tool)?;
    copy_file(&primary.keep.frozen.join("manifest.json"), &staging.join("manifest.json"))?;
    let uses: Vec<(String, Vec<gendb_artifacts::verus::VerusStorageUseV1>)> =
        plan.workloads.iter().map(|f| Ok((f.name.clone(), serde_json::from_value(side_of(&f.name)?.admission["uses"].clone()).unwrap_or_default()))).collect::<Result<_, AdmissionError>>()?;
    write_value(&staging.join("seed-manifest.json"), &json!(members_seed_manifest(&primary_manifest, &uses)))?;
    if let Some(notes) = seed_notes(primary_facts.seed.as_ref()) {
        copy_file(&notes, &staging.join(NOTES_FILE))?;
    }
    write_top_records(&staging, &primary_facts.scale, primary)?;
    // Every side's records under workloads/<name>/ with its origin, and every other side's code under root-sides/<name>/.
    let mut workloads = serde_json::Map::new();
    let mut members: Vec<(String, Option<MemberRecord>)> = vec![];
    for facts in &plan.workloads {
        let side = side_of(&facts.name)?;
        let own = staging.join(tree::WORKLOADS_DIRECTORY).join(&facts.name);
        let own_target = target.join(tree::WORKLOADS_DIRECTORY).join(&facts.name);
        let oob = tried.get(&facts.name);
        let oob_record = own_target.join(OUT_OF_THE_BOX_FILE);
        if let Some(oob) = oob {
            copy_file(&oob.record, &own.join(OUT_OF_THE_BOX_FILE))?;
        }
        let side_record = own_target.join(SIDE_FILE);
        let origin = json!({"kind":side.keep.source.kind(),"seed":if side.keep.source == SideSource::Seed { seed_record(facts.seed.as_ref()) } else { Value::Null },
            "out_of_the_box":oob.map_or(Value::Null, |o| o.side_view(&oob_record)),"record":side_record});
        write_text(&own.join(SIDE_FILE), &side_markdown(facts, side, oob))?;
        let member = side_member(side);
        let timing_file = side.evaluation.join("score.json");
        let timing = side.keep.score.as_ref().map(|score| MemberTiming { cells: &side.keep.cells, score, timing: &timing_file, raced: false, parent: None });
        let part = MemberPart {
            name: &facts.name,
            role: facts.member,
            primary: facts.primary,
            scale: &facts.scale,
            timing,
            check: side.keep.check.as_ref(),
            copies: ["official-matrix.json", "variant-answers.json", "variant-matrix.json"].iter().map(|n| side.evaluation.join(n)).collect(),
            admission: &side.admission,
            library: &facts.library,
            storage: side_storage(facts, side),
            build: &side.build,
            member: member.as_ref(),
            origin,
        };
        workloads.insert(facts.name.clone(), write_member(&staging, &target, ROOT_VERSION, &part)?);
        if !facts.primary {
            write_side_copy(&staging.join(ROOT_SIDES_DIRECTORY).join(&facts.name), facts, side)?;
        }
        members.push((facts.name.clone(), member));
    }
    let ancestor = write_common_ancestor(&staging.join(ROOT_SIDES_DIRECTORY).join(ANCESTOR_DIRECTORY), plan, sides)?;
    let order: Vec<String> = plan.workloads.iter().map(|f| f.name.clone()).collect();
    let combined = super::records::combined_record(&workloads, &order);
    // The sides are different engines (each from its own seed), so their shared sources differ by design.
    let general = super::records::general_record(&members.iter().map(|(n, m)| (n.as_str(), m.as_ref())).collect::<Vec<_>>(), false);
    let mut times = serde_json::Map::new();
    times.insert(node.scale.clone(), json!({"score":node.score,"timing":"timed alone (no parent)","evaluation":primary.evaluation}));
    let version = json!({"format_version":1,"version":node.id,"accepted":true,"directory":target,"node":node,"parents":[],"branch":tree::MAIN,"kind":node.kind,
        "origin":{"seed":seed_record(plan.seed.as_ref()),"sides":sides.iter().map(|s| (s.workload.clone(), json!(s.keep.source.kind()))).collect::<BTreeMap<_, _>>(),
            "ancestor":ancestor,"author":"none (seeded by GenDB)"},
        "goal":{"scale":node.scale,"workload":primary_facts.name},
        "storage":{"uses":primary.admission["uses"],"budget_rule":"each side reads its workload's plain storage (allowed as is) or its seed's storages within its budget (a check workload is exempt)"},
        "times":times,"cost":{"known_provider_reported_cost_usd":"0","scope":"no author: framework work"},
        "finished_checks":primary.keep.checks,"admission":primary.admission,"profile":primary.profile,
        "workloads":Value::Object(workloads),"combined_score":combined,"general":general});
    write_value(&staging.join("version.json"), &version)?;
    let readme = format!(
        "# Engine version {} (root of a run of several workloads)\n\n{direction}. The first session continues from the primary side's code (`code/`), its seed's notebook (`NOTES.md`) and a manifest naming every workload's storage uses (`seed-manifest.json`); every other side's code, module, storage author files, notebook and manifest are under `{ROOT_SIDES_DIRECTORY}/<workload>/`{}. Each side's record: `workloads/<workload>/{SIDE_FILE}`.\n{}",
        node.id,
        if ancestor.is_null() { String::new() } else { format!(", the seeds' common ancestor's code under `{ROOT_SIDES_DIRECTORY}/{ANCESTOR_DIRECTORY}/`") },
        crate::output::engine::general::workloads_readme(&version).unwrap_or_default()
    );
    write_text(&staging.join("README.md"), &readme)?;
    write_value(&staging.join(tree::NODE_FILE), &json!(node))?;
    fs::rename(&staging, &target).map_err(|e| AdmissionError::tool(format!("{}: {e}", target.display())))?;
    Ok(node)
}

/// `SIDE.md` of a workload's side: where it came from and how it was measured.
fn side_markdown(facts: &SideFacts, side: &SideAdmission, oob: Option<&OutOfTheBox>) -> String {
    let from = match side.keep.source {
        SideSource::Seed => format!("the seed {}: its code, module, families and plans over its storage uses (which the workload's library holds)", facts.seed.as_ref().map_or_else(|| "-".to_string(), seed_text)),
        SideSource::OutOfTheBox => "the primary seed's code, admissible here out of the box (`OUT_OF_THE_BOX.md`)".to_string(),
        SideSource::VersionZero => "GenDB's version 0: the verified interpreter over the workload's plain flat storage".to_string(),
    };
    let measured = match (&side.keep.score, &side.keep.check) {
        (Some(score), _) => format!("timed alone at {}: {} of {} cells finished, normalized time {}", score.scale, score.score.finished, score.cells, score.score.normalized_time),
        (None, Some(check)) => format!("answered at {}: {} of {} calls agreed with the saved answers", facts.scale, check["agreed"], check["calls"]),
        _ => "not measured".to_string(),
    };
    let tried = match (oob, side.keep.source) {
        (Some(oob), SideSource::VersionZero) => format!("\n\nThe primary seed's code out of the box here: {} (step `{}`; `OUT_OF_THE_BOX.md`).", oob.outcome(), oob.step),
        _ => String::new(),
    };
    format!("# The side of `{}` ({}{})\n\nMade from {from}; frozen for this workload alone under the run's rules and verified whole, then {measured}.{tried}\n\nEvaluation: `{}`. Admission: library version {} of `{}`.\n",
        facts.name, facts.member.name(), if facts.primary { ", primary" } else { "" }, side.evaluation.display(), side.admission["library_version"], facts.library.display())
}

/// Another side's copy for the sessions' workspaces (`root-sides/<name>/`, read-only there): its code (shared engine,
/// module, families, plans), its manifest, its seed's notebook and its seed version's storage author files
/// (`code/storages/**`), when it has them.
fn write_side_copy(dir: &Path, facts: &SideFacts, side: &SideAdmission) -> Result<(), AdmissionError> {
    crate::engine::submission::members::write_member_code(&dir.join("code"), &[(facts.name.as_str(), side.keep.frozen.as_path())])?;
    copy_file(&side.keep.frozen.join("manifest.json"), &dir.join("manifest.json"))?;
    let seed = (side.keep.source == SideSource::Seed).then_some(facts.seed.as_ref()).flatten();
    if let Some(notes) = seed_notes(seed) {
        copy_file(&notes, &dir.join(NOTES_FILE))?;
    }
    if let Some(Seed::Run { version, .. }) = seed {
        let storages = version.directory().join("code/storages");
        if storages.is_dir() {
            copy_tree(&storages, &dir.join("storages"), false)?;
        }
    }
    Ok(())
}

/// The versions a seed version descends from, nearest first (itself first): its parents within its run (`node.json`),
/// and from its run's root the root's own seed (`version.json` `origin.seed`), across runs.
pub fn ancestry(seed: &SeedVersion) -> Vec<SeedVersion> {
    let mut found: Vec<SeedVersion> = vec![];
    let mut seen: BTreeSet<(PathBuf, String)> = BTreeSet::new();
    let mut queue: std::collections::VecDeque<SeedVersion> = [seed.clone()].into();
    while let Some(next) = queue.pop_front() {
        let key = (next.run.canonicalize().unwrap_or_else(|_| next.run.clone()), next.version.clone());
        if !seen.insert(key) {
            continue;
        }
        let dir = next.directory();
        let Ok(node) = read_json::<TreeNode>(&dir.join(tree::NODE_FILE)) else { continue };
        for parent in &node.parents {
            queue.push_back(SeedVersion { run: next.run.clone(), version: parent.clone() });
        }
        if node.parents.is_empty() {
            let version: Value = read_json(&dir.join("version.json")).unwrap_or(Value::Null);
            if let (Some(run), Some(id)) = (version["origin"]["seed"]["run"].as_str(), version["origin"]["seed"]["version"].as_str()) {
                queue.push_back(SeedVersion { run: PathBuf::from(run), version: id.to_string() });
            }
        }
        found.push(next);
    }
    found
}

/// The seeds' common ancestor (module documentation) of the sides made from a version seed: the nearest version of the
/// primary's (else the first seeded side's) [`ancestry`] that every other seeded side descends from; `None` with fewer
/// than two such sides or no common version.
pub fn common_ancestor(seeds: &[SeedVersion]) -> Option<SeedVersion> {
    let [first, rest @ ..] = seeds else { return None };
    if rest.is_empty() {
        return None;
    }
    let key = |s: &SeedVersion| (s.run.canonicalize().unwrap_or_else(|_| s.run.clone()), s.version.clone());
    let others: Vec<BTreeSet<(PathBuf, String)>> = rest.iter().map(|s| ancestry(s).iter().map(key).collect()).collect();
    ancestry(first).into_iter().find(|candidate| others.iter().all(|set| set.contains(&key(candidate))))
}

/// The code of the seeds' common ancestor under `dir` (`code/agent/**` and its workload modules, and `ANCESTOR.md`),
/// when GenDB finds one; returns its record (`run`, `version`, `directory`), or `Null`.
fn write_common_ancestor(dir: &Path, plan: &RootPlan<'_>, sides: &[SideAdmission]) -> Result<Value, AdmissionError> {
    let seeds: Vec<SeedVersion> = plan
        .workloads
        .iter()
        .filter(|f| sides.iter().any(|s| s.workload == f.name && s.keep.source == SideSource::Seed))
        .filter_map(|f| match &f.seed {
            Some(Seed::Run { version, .. }) => Some(version.clone()),
            _ => None,
        })
        .collect();
    let Some(ancestor) = common_ancestor(&seeds) else { return Ok(Value::Null) };
    let code = ancestor.directory().join("code");
    for part in ["agent", WORKLOADS_DIRECTORY] {
        if code.join(part).is_dir() {
            copy_tree(&code.join(part), &dir.join("code").join(part), false)?;
        }
    }
    write_text(&dir.join("ANCESTOR.md"), &format!("# The seeds' common ancestor\n\nVersion {} of the run `{}`: the nearest version every seeded side descends from (its parents, then its run's root's seed). Its code is under `code/`; other records of that run are not inputs.\n",
        ancestor.version, ancestor.run.display()))?;
    Ok(json!({"run":ancestor.run,"version":ancestor.version,"directory":dir}))
}

// ------------------------------------------------------------------------------------------------ the framework's root work

/// The root's work done by the framework over the prepared run (module documentation).
pub(in crate::engine) struct FrameworkRoot<'r> {
    pub run: &'r StageRun,
    pub engine_dir: &'r Path,
}

/// What a root side's evaluation produced after its build: timed alone (a counted or kept workload: its score, cells
/// and timing record) or answered (a check workload: its answers), its checks and its storage policy.
struct Evaluated {
    score: Option<RecordedScore>,
    cells: Vec<CellResult>,
    checks: Value,
    storage_policy: Value,
    timing: Option<Value>,
    check: Option<Value>,
}

impl FrameworkRoot<'_> {
    /// A framework role over workload `workload` with its bench's workspace at `<dir>/author`: its request, inputs,
    /// first scale and its side's crate (`StageRun::side_role`).
    fn role(&self, workload: &str, dir: &Path) -> Result<EngineAuthorRole, AdmissionError> {
        let w = self.run.workload(workload).ok_or_else(|| AdmissionError::tool(format!("{workload} is not a workload of this run")))?;
        Ok(framework_role(&w.request, &w.prepared, self.engine_dir, dir)?.with_stage(self.run.side_role(workload)))
    }

    /// The stage-form manifest's workloads of a stage root workspace: the goal's plain storage uses, every kept
    /// workload's the seed's storage uses (the seed was built for them).
    fn stage_root_workloads(&self) -> Result<Vec<WorkloadModules>, AdmissionError> {
        let seed_dir = self.run.seed_directory()?;
        let manifest_file = ["seed-manifest.json", "manifest.json"].into_iter().map(|f| seed_dir.join(f)).find(|p| p.is_file())
            .ok_or_else(|| AdmissionError::missing_input(format!("seed version {}: no manifest", seed_dir.display())))?;
        let seed: EngineManifest = read_json(&manifest_file).map_err(AdmissionError::tool)?;
        let plain = |w: &super::StageWorkload| -> Vec<StorageUseDeclaration> {
            w.prepared.inputs.seeded.iter().map(|(name, package)| StorageUseDeclaration::admitted(name, *package)).collect()
        };
        Ok(self
            .run
            .workloads()
            .map(|w| WorkloadModules { name: w.name.clone(), storage_uses: if w.primary { plain(w) } else { seed.storage_uses.clone() }, modules: vec![] })
            .collect())
    }

    /// The workspace of `workload`'s side from `seed` in a run of several workloads (`engine::submission::members`): a
    /// version folder's side (`write_side_root`, the seed's `workload` among a version of several), or an exported
    /// engine's (`write_source_root`, over the workload's plain flat storages when the engine has no family).
    fn write_member_side(&self, workspace: &Path, workload: &str, seed: &Seed) -> Result<(), AdmissionError> {
        let w = self.run.workload(workload).ok_or_else(|| AdmissionError::tool(format!("{workload} is not a workload of this run")))?;
        match seed {
            Seed::Run { version, workload: seed_workload } => write_side_root(workspace, &version.directory(), seed_workload.as_deref(), workload)?,
            Seed::Source { source } => write_source_root(workspace, source, workload, &w.flat_storages)?,
        };
        Ok(())
    }

    /// The workspace of the primary seed's code out of the box on `workload` (a run of several workloads; module
    /// documentation): its shared engine, default module and families, without the seed's own workload module and
    /// plans, over the workload's plain flat storages, or one family use per family of the seed when it has families.
    fn write_out_of_the_box(&self, workspace: &Path, workload: &str, seed: &Seed) -> Result<(), AdmissionError> {
        let w = self.run.workload(workload).ok_or_else(|| AdmissionError::tool(format!("{workload} is not a workload of this run")))?;
        self.write_member_side(workspace, workload, seed)?;
        if matches!(seed, Seed::Source { .. }) {
            return Ok(());
        }
        let crate_dir = workspace.join(CRATE_DIRECTORY);
        for own in [crate_dir.join(WORKLOADS_DIRECTORY).join(workload), crate_dir.join(PLANS_DIRECTORY).join(workload)] {
            if own.exists() {
                fs::remove_dir_all(&own).map_err(|e| AdmissionError::tool(format!("{}: {e}", own.display())))?;
            }
        }
        let manifest_file = workspace.join(MANIFEST_FILE);
        let mut manifest: EngineManifest = read_json(&manifest_file).map_err(AdmissionError::tool)?;
        let storage_uses: Vec<StorageUseDeclaration> = if manifest.families.is_empty() {
            w.flat_storages.iter().map(|(name, package)| StorageUseDeclaration::admitted(name, *package)).collect()
        } else {
            manifest.families.iter().map(|f| StorageUseDeclaration { name: f.name.clone(), admitted: None, workspace: None, family: Some(f.name.clone()) }).collect()
        };
        manifest.workloads = vec![WorkloadModules { name: workload.to_string(), storage_uses, modules: vec![] }];
        fs::write(&manifest_file, format!("{}\n", serde_json::to_string_pretty(&manifest).map_err(AdmissionError::tool)?)).map_err(AdmissionError::tool)
    }

    /// Storages and budget, then the timing alone and the finished checks under `plan` (a counted or kept workload), or
    /// the answers at every visible binding and the variants (a check workload), of a frozen root crate:
    /// `Err((step, error))` names the step that stopped it.
    #[allow(clippy::too_many_arguments)]
    fn evaluate_built(bench: &mut EngineBench<'_>, workload: &str, role: MemberRole, engine: &FrozenEngine, frozen_dir: &Path, evaluation: &Path, build: &EngineBuild, plan: &EvaluationPlan, label: &str) -> Result<Evaluated, (&'static str, AdmissionError)> {
        let general = bench.inputs().general.clone().ok_or(("storages", AdmissionError::tool("a root side without general inputs")))?;
        let rule = bench.budget_rule().map_err(|e| ("storages", e))?;
        let storages = bench.storages(engine, frozen_dir, evaluation, TrialVerification::WholeCrate).map_err(|e| ("storages", e))?;
        let storage_policy = bench.check_storage_policy(engine, frozen_dir, &storages, &rule).map_err(|e| ("storages", e))?;
        let run = Runnable { label: label.to_string(), library: build.library.clone(), inputs: storage_inputs(&storages) };
        let subject = CheckedEngine { library: &build.library, inputs: &run.inputs, frozen: Some((&engine.storage_uses, frozen_dir)) };
        if role == MemberRole::Check {
            let failed = |failure: crate::engine::acceptance::Failure| match failure {
                crate::engine::acceptance::Failure::Candidate { reason, .. } => AdmissionError::refusal(reason),
                crate::engine::acceptance::Failure::Framework(error) => error,
            };
            let check = bench.check_answers_here(workload, &build.library, &storages, evaluation).map_err(|f| ("answers", failed(f)))?;
            let variants = bench.variant_answers(&subject, &BTreeSet::new(), evaluation).map_err(|f| ("checks", failed(f)))?;
            let checks = json!({"plan":DEVELOPMENT.record(),"answers":check,"variants":variants});
            return Ok(Evaluated { score: None, cells: vec![], checks, storage_policy, timing: None, check: Some(check) });
        }
        let (matrix, scored) = bench.time_alone(&run, plan.cell_calls, &evaluation.join("timing")).map_err(|e| ("timing", e))?;
        let matrix_file = evaluation.join("official-matrix.json");
        write_matrix(&matrix, &matrix_file).map_err(|e| ("timing", e))?;
        write_json_atomic(&evaluation.join("score.json"), &json!(scored)).map_err(|e| ("timing", AdmissionError::tool(e)))?;
        let score = RecordedScore::of(&general.scale.name, &scored, &evaluation.join("score.json"));
        let checks = bench.finished_checks(plan, &subject, &scored, evaluation).map_err(|reason| ("checks", AdmissionError::refusal(reason)))?;
        let cells = scored.cells.iter().map(|c| CellResult { template: c.template.clone(), workers: c.workers, status: c.status }).collect();
        let timing = json!({"score":scored.score,"cells_total":scored.cells_total,"beats_both":scored.beats_both,"file":matrix_file,"plan":plan.name});
        Ok(Evaluated { score: Some(score), cells, checks, storage_policy, timing: Some(timing), check: None })
    }

    /// The intent of a root side's admission from its evaluation: lineage `framework_generated` on the main branch (no
    /// parent), its finished checks and its timing alone (named by `generator`; none for a check workload, whose answers
    /// are among its checks) as evidence.
    fn intent(source: SideSource, frozen: &Path, evaluation: &Path, build: &EngineBuild, evaluated: Evaluated, generator: String) -> AdmissionIntent {
        let lineage = VerusEngineLineageV1 { branch: tree::MAIN.into(), kind: "framework_generated".into(), parents: vec![] };
        let mut evidence = vec![(VERUS_ENGINE_LINEAGE_KIND.to_string(), json!(lineage)), (ENGINE_FINISHED_CHECKS_KIND.to_string(), float_free(&evaluated.checks))];
        if let Some(mut timing) = evaluated.timing {
            timing["generator"] = json!(generator);
            evidence.push((VERSION_ZERO_TIMING_KIND.to_string(), float_free(&timing)));
        }
        let keep = SideKeep { source, frozen: frozen.to_path_buf(), score: evaluated.score, cells: evaluated.cells, checks: evaluated.checks, storage_policy: evaluated.storage_policy,
            check: evaluated.check };
        AdmissionIntent { evaluation: evaluation.to_path_buf(), build: build.record.clone(), evidence, keep: json!(keep), written_unix_ms: now_unix_ms() }
    }

    /// The (primary) seed's generator label in records.
    fn seed_label(&self) -> String {
        match (&self.run.form, &self.run.seed) {
            (WorkloadForm::Workloads, Some(seed)) => format!("seed {}", seed_text(seed)),
            (_, Some(Seed::Run { version, .. })) => format!("stage seed {} of {}", version.version, version.run.display()),
            _ => "no seed".to_string(),
        }
    }

    /// The plan a side of `w` is timed under: version 0's for the primary (the goal), the development plan otherwise.
    fn plan_of(w: &super::StageWorkload) -> &'static EvaluationPlan {
        if w.primary { &VERSION_ZERO } else { &DEVELOPMENT }
    }
}

impl RootWork for FrameworkRoot<'_> {
    fn out_of_the_box(&mut self, workload: &str, dir: &Path) -> Result<(OutOfTheBox, Option<AdmissionIntent>), AdmissionError> {
        let w = self.run.workload(workload).ok_or_else(|| AdmissionError::tool(format!("{workload} is not a workload of this run")))?;
        let label = self.seed_label();
        let mut role = self.role(workload, dir)?;
        let mut bench = role.view();
        let workspace = bench.bench.workspace()?.to_path_buf();
        match (self.run.form, &self.run.seed) {
            (WorkloadForm::Workloads, Some(seed)) => self.write_out_of_the_box(&workspace, workload, seed)?,
            (WorkloadForm::Workloads, None) => return Err(AdmissionError::tool("out of the box without a primary seed")),
            _ => {
                write_root_from_version(&workspace, &self.run.seed_directory()?, self.stage_root_workloads()?)?;
            }
        }
        let frozen_dir = dir.join("frozen");
        let submission = CandidateSubmission { candidate_manifest: MANIFEST_FILE.into(), rationale: label.clone(), data_access_analysis: "the seed's storage access, out of the box".into() };
        let engine = match bench.freeze_submission(&workspace, &frozen_dir, &submission) {
            Ok(frozen) => frozen.engine,
            Err(error) if error.class == FailureClass::ToolFailure => return Err(error),
            Err(error) => return Ok((OutOfTheBox::stopped(OutOfTheBoxStatus::Refused, "freeze", &error, dir), None)),
        };
        let evaluation = dir.join("evaluation");
        fs::create_dir_all(&evaluation).map_err(AdmissionError::tool)?;
        let locks = bench.bench.config.locks.clone();
        let build = match bench.builds.compile(&locks, &engine, &frozen_dir, &evaluation.join("verus-build"), true) {
            Ok(build) => build,
            Err(error) if error.class == FailureClass::ToolFailure => return Err(error),
            Err(error) => {
                let (status, step) = blocked_at_build(&error);
                return Ok((OutOfTheBox::stopped(status, step, &error, dir), None));
            }
        };
        // A stage run's goal: version 0's plan (as before); a run of several workloads' workload: its side's plan.
        let plan = if self.run.form == WorkloadForm::Workloads { Self::plan_of(w) } else { &VERSION_ZERO };
        match Self::evaluate_built(&mut bench, workload, w.role, &engine, &frozen_dir, &evaluation, &build, plan, &label) {
            Ok(evaluated) => {
                let score = evaluated.score.clone();
                let step = if evaluated.check.is_some() { "answers" } else { "timing" };
                let source = if self.run.form == WorkloadForm::Workloads { SideSource::OutOfTheBox } else { SideSource::Seed };
                let intent = Self::intent(source, &frozen_dir, &evaluation, &build, evaluated, label);
                let oob = OutOfTheBox { status: OutOfTheBoxStatus::Verified, step: step.into(), first_errors: vec![], score, record: PathBuf::new(), directory: dir.to_path_buf(),
                    admissible: true, at_unix_ms: now_unix_ms() };
                Ok((oob, Some(intent)))
            }
            Err((_, error)) if error.class == FailureClass::ToolFailure => Err(error),
            Err((step, error)) => Ok((OutOfTheBox::stopped(OutOfTheBoxStatus::Verified, step, &error, dir), None)),
        }
    }

    fn evaluate_side(&mut self, workload: &str, source: SideSource, dir: &Path) -> Result<AdmissionIntent, AdmissionError> {
        let w = self.run.workload(workload).ok_or_else(|| AdmissionError::tool(format!("{workload} is not a workload of this run")))?;
        let label = match (source, &w.seed) {
            (SideSource::VersionZero, _) => gendb_verification::obligations::INTERPRETER_ENGINE_GENERATOR.to_string(),
            (_, Some(seed)) if self.run.form == WorkloadForm::Workloads => format!("seed {}", seed_text(seed)),
            _ => self.seed_label(),
        };
        let plan = if self.run.form == WorkloadForm::Workloads { Self::plan_of(w) } else if w.primary { &VERSION_ZERO } else { &DEVELOPMENT };
        let stopped = |what: &str, error: AdmissionError| AdmissionError::tool(format!("the root's side on {workload} ({source:?}) {what}: {error}"));
        let mut role = self.role(workload, dir)?;
        let mut bench = role.view();
        let store = bench.bench.store()?;
        let existing = engine_versions(&store).map_err(AdmissionError::tool)?;
        if !existing.is_empty() {
            return Err(AdmissionError::refusal(format!("the library {} of workload {workload} already holds {} engine versions; a run of several workloads' libraries start without engine versions", w.request.library.display(), existing.len())));
        }
        let workspace = bench.bench.workspace()?.to_path_buf();
        match (source, self.run.form) {
            (SideSource::Seed, WorkloadForm::Workloads) => {
                let seed = w.seed.as_ref().ok_or_else(|| AdmissionError::tool(format!("workload {workload} has no seed of its own")))?;
                self.write_member_side(&workspace, workload, seed)?;
            }
            (SideSource::Seed, _) => {
                write_root_from_version(&workspace, &self.run.seed_directory()?, self.stage_root_workloads()?)?;
            }
            (SideSource::VersionZero, form) => {
                let substitutes = std::collections::BTreeMap::new();
                let context = EngineFreeze { workspace: &workspace, schema: bench.schema(), library: &w.request.library, substitutes: &substitutes, policy: &w.request.storage_policy, rules: &w.prepared.inputs.rules };
                // A run of several workloads' version 0 reads the workload's plain flat storages; a stage run's its seeded storages.
                let uses = if form == WorkloadForm::Workloads { &w.flat_storages } else { &w.prepared.inputs.seeded };
                write_root_version(&context, uses, &dir.join("uses"), interpreter_engine, VERSION_ZERO_NOTES)?;
                let manifest: EngineManifest = read_json(&workspace.join(MANIFEST_FILE)).map_err(AdmissionError::tool)?;
                let workloads = match form {
                    WorkloadForm::Workloads => vec![WorkloadModules { name: workload.to_string(), storage_uses: manifest.storage_uses.clone(), modules: vec![] }],
                    _ => self.stage_root_workloads()?,
                };
                write_value(&workspace.join(MANIFEST_FILE), &json!(EngineManifest::stage_form(&manifest, workloads)))?;
            }
            (SideSource::OutOfTheBox, _) => return Err(AdmissionError::tool("an out-of-the-box side is made by out_of_the_box")),
        }
        let frozen_dir = dir.join("frozen");
        let submission = CandidateSubmission { candidate_manifest: MANIFEST_FILE.into(), rationale: label.clone(), data_access_analysis: "the root's side".into() };
        let engine = bench.freeze_submission(&workspace, &frozen_dir, &submission).map_err(|e| stopped("was refused at freeze", e))?.engine;
        let evaluation = dir.join("evaluation");
        fs::create_dir_all(&evaluation).map_err(AdmissionError::tool)?;
        let locks = bench.bench.config.locks.clone();
        let build = bench.builds.compile(&locks, &engine, &frozen_dir, &evaluation.join("verus-build"), true).map_err(|e| stopped("did not verify", e))?;
        let evaluated = Self::evaluate_built(&mut bench, workload, w.role, &engine, &frozen_dir, &evaluation, &build, plan, &label).map_err(|(step, e)| stopped(&format!("failed at {step}"), e))?;
        Ok(Self::intent(source, &frozen_dir, &evaluation, &build, evaluated, label))
    }

    fn admit_side(&mut self, workload: &str, intent: &AdmissionIntent) -> Result<Value, AdmissionError> {
        let keep: SideKeep = serde_json::from_value(intent.keep.clone()).map_err(AdmissionError::tool)?;
        let engine: FrozenEngine = read_json(&keep.frozen.join("candidate.json")).map_err(AdmissionError::tool)?;
        // The bench of the attempt that froze it (its workspace's session root names the registrations).
        let attempt = keep.frozen.parent().ok_or_else(|| AdmissionError::tool("a root side's frozen crate without its attempt directory"))?;
        let mut role = self.role(workload, attempt)?;
        role.view().admit_from_intent(&keep.frozen, &engine, intent)
    }

    fn profile_side(&mut self, workload: &str, side: &SideAdmission) -> Value {
        let outcome = (|| -> Result<Value, AdmissionError> {
            let w = self.run.workload(workload).ok_or_else(|| AdmissionError::tool(format!("{workload} is not a workload of this run")))?;
            let inputs = &w.prepared.inputs;
            let limit = inputs.general.as_ref().map_or(u64::MAX, |g| g.call_limits.call_limit_ns);
            let scored = crate::engine::score::score(&inputs.baselines, &inputs.training.timing_binding, &inputs.workers, limit, &side.keep.cells).map_err(|e| AdmissionError::tool(e.to_string()))?;
            let attempt = side.keep.frozen.parent().ok_or_else(|| AdmissionError::tool("a root side's frozen crate without its attempt directory"))?;
            let mut role = self.role(workload, attempt)?;
            let mut bench = role.view();
            let run = bench.admitted_runnable(ROOT_VERSION, &side.evaluation.join("profile-storages"))?;
            Ok(bench.profile_runnable(ROOT_VERSION, &run.library, &run.inputs, &scored, &side.evaluation))
        })();
        outcome.unwrap_or_else(|error| json!({"status":"failed","error":error.to_string(),"meaning":"profiles are diagnostics: never gating"}))
    }

    fn select_root(&mut self) -> Result<ContentId, AdmissionError> {
        let reason = if self.run.form == WorkloadForm::Workloads { WORKLOAD_SEED_REASON } else { STAGE_SEED_REASON };
        let mut primary_selection = None;
        for w in self.run.workloads() {
            let store = ObjectStore::open_existing(&w.request.library).map_err(|e| AdmissionError::tool(format!("{}: {e}", w.request.library.display())))?;
            let selection = match engine_selections(&store).map_err(AdmissionError::tool)?.first() {
                Some((id, _)) => *id,
                None => select_version(&store, ROOT_VERSION, reason, None)?,
            };
            primary_selection.get_or_insert(selection);
        }
        primary_selection.ok_or_else(|| AdmissionError::tool("a run of several workloads without workloads"))
    }
}

/// The root of the run `run` (module documentation) by the framework ([`FrameworkRoot`]); a failure stops the
/// preparation resumably.
pub fn seed_stage_root(run: &StageRun, engine_dir: &Path, branches: &[String]) -> Result<Value, crate::controller::workload_run::WorkloadError> {
    let plan = root_plan(run, engine_dir, branches);
    seed_root(&mut FrameworkRoot { run, engine_dir }, &plan).map_err(crate::engine::branches::framework_error)
}

/// The plan of the root of `run` (module documentation): every workload's role, seed, scale, library and budget.
pub fn root_plan<'a>(run: &StageRun, engine_dir: &'a Path, branches: &'a [String]) -> RootPlan<'a> {
    let workloads = run
        .workloads()
        .map(|w| {
            let general = w.prepared.inputs.general.as_ref();
            SideFacts {
                name: w.name.clone(),
                role: w.contract_role(),
                member: w.role,
                primary: w.primary,
                seed: if w.primary { run.seed.clone() } else { w.seed.clone() },
                scale: w.scale(),
                library: w.request.library.clone(),
                budget_bytes: general.map_or(0, |g| g.scale.original_data_bytes),
                plain_storage_bytes: general.map_or(0, |g| g.plain_storage_bytes),
            }
        })
        .collect();
    RootPlan { engine_dir, form: run.form, seed: run.seed.clone(), workloads, branches }
}
