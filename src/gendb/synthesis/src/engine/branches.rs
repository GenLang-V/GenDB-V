//! The general line's run: version 0,
//! the branch slots and their sessions, merges into the main line, the review cadence, the scale ladder, the budget
//! and the stop. `gendb engine prepare REQUEST RUN_DIR` runs the preparation alone ([`prepare_general_run`]); `gendb
//! engine synthesize` runs everything ([`run_general_engine`]).
//!
//! - **Preparation** (idempotent, once per controller process): the inputs of the current scale
//!   (`engine::rounds::prepare_engine_scale`), then version 0 ([`seed_version_zero`]): GenDB writes the interpreter
//!   engine over the flat storage of every table (`engine::submission::write_version_zero`), freezes it under the
//!   general line's rules, verifies and compiles the whole crate, times it alone at the first scale under the call and
//!   memory limits (1 warm + 1 hot call per cell like every development timing; unfinished cells are recorded, not
//!   refused), checks the finished templates and profiles it (`engine::protocol::VERSION_ZERO`), admits it as `v000` on
//!   branch `main` (lineage `framework_generated`, no author, $0) and selects it as the main-line head. A continued run
//!   (`engine.seed_version`) seeds its root the same way from an accepted version of another run
//!   (its code and storage uses, [`RootSource::seeded`]) at the last scale of its ladder ([`LadderState::start`]).
//! - **Branch slots** `b1`..`bN` (`engine.branches`). Each slot runs one session at a time on its own thread; the
//!   driver starts the next one when it ends. Slot `b1` starts first; the others once `b1` has one evaluated submission
//!   (staggered start). A slot's next session ([`plan_slot`]): its open session (a relaunch resumes it),
//!   else a merge session when the branch's head has gains the main line has not taken and its last session was not a
//!   merge (one merge session, then the branch continues), else a branch session from its head.
//! - **Review cadence** (`engine.pause_after_session`, [`pauses_after`]): once a session that should pause ends, no new
//!   session starts; when the running ones have ended the run summary says `paused` and the controller exits. A
//!   relaunch continues from the records.
//! - **Scale ladder** ([`ladder_decision`], [`ladder_check`]): when the main-line head finishes every cell at the
//!   current scale, the move is due (no storage condition: every accepted version met the budget rule of its scale). Every session then ends at its next evaluation (`engine::sessions::session_end`,
//!   reason `scale_move`, closed like a fresh session: its notebook and records carry over), and no new session starts
//!   ([`starts_now`]); an open session still resumes after a relaunch, so the run never waits on a session that cannot
//!   run. Once none runs or is open, the inputs of the next scale are prepared, the main-line head and every other
//!   branch head are timed interleaved there under the development plan (the winner is the main-line head), and
//!   `scale.json` records the move. Sessions then continue at the new scale; the first scale's inputs stay prepared
//!   (`engine::role::FirstScale`) for the variants of their submissions (`engine::protocol`). A flat storage without an asset for the new capture stops the run with
//!   the command that prepares it (`gendb prepare-flat-storage`).
//! - **Storage assets** (`engine::asset_upkeep`): the run library's superseded derived storage assets are released
//!   after a scale move and at a launch with no open session (and after an admission on one line), every head's kept.
//! - **Stop**: the budget (`engine.limits.max_cost_usd`, the provider-reported spend of every session together, checked
//!   before every call by each session's policy) or the user (TERM; the run stays resumable). "Beats both at a scale"
//!   is a milestone in the summary, never a stop. A framework error or unresolved accounting stops
//!   the run resumably.
//!
//! - **Runs of several workloads** (`engine.stage`; `engine.workloads`; `engine::stage`): every
//!   workload is prepared at the last scale of its request (`engine::stage::StageRun`), the root is seeded per workload
//!   (`engine::stage::root`: a stage run's out-of-the-box record and `v000`; a run of several workloads' one side per
//!   workload) instead of version 0, the ladder is off (every workload stays at its scale), every session's role
//!   reaches the other workloads (`engine::role::EngineAuthorRole::with_stage`), the storage assets are released in
//!   every workload's library, and the run summary names every workload (`stage`, or `workloads` with the head's
//!   combined score).
//!
//! With an output home (`output_home`), its readable engine folders (`output::engine::general`) are written after the
//! preparation and after every session.
//!
//! Records under `<run>/engine/`: `seed-v0/` (version 0's freeze and evaluation), `branches/<b>/sessions/session-NNNN/`
//! (`engine::sessions`), `versions/`, `attempts/`, `tree.json`, `TREE.md`, `main-line.jsonl`, `findings.jsonl`,
//! `FINDINGS.md`, `flags.jsonl` (`engine::tree`), `asset-releases.jsonl` (`engine::asset_upkeep`), `scale.json`,
//! `scales/<scale>/` (statements, preparation) and `scale-moves/<scale>/` (the timings of a move).

use super::acceptance::{ADMITTING_FILE, AdmissionIntent, CheckedEngine, Runnable, main_line_lock, record_cells, select_version};
use super::protocol::{DEVELOPMENT, VERSION_ZERO};
use super::score::CellResult;
use super::role::{EngineAuthorRole, EngineRoleConfig, EngineRoleMode, FirstScale, GeneralInputs, SessionConfig, storage_inputs};
use super::rounds::{PAUSED, PAUSED_FOR_REVIEW, PreparedEngine, engine_directory, prepare_engine_scale};
use super::stage::StageRun;
use super::sessions::{DueScaleMove, RunSpend, SessionKind, SessionRecord, SessionView, branch_sessions, session_directory, SESSION_FILE};
use super::submission::{CRATE_DIRECTORY, EngineManifest, FrozenEngine, MANIFEST_FILE, RootAgentGenerator, write_root_version};
use super::tree::{self, MainLineChange, NodeKind, RecordedScore, TreeNode, VersionTree, ROOT_VERSION, append_main_line, record_scale_score};
use crate::controller::author::{AuthorTransport, CandidateSubmission};
use crate::controller::layout::NOTES_FILE;
use crate::controller::limits::{Limits, Money, UNSET_COUNT};
use crate::controller::records::{self, RecordError, now_unix_ms, read_json, write_json_atomic};
use crate::controller::request::{EngineRequest, PauseCadence, SeedVersion, WorkloadForm, WorkloadRequest};
use crate::controller::run::RunRequest;
use crate::controller::schedule::{ScheduledSession, run_sessions};
use crate::controller::session::RetainedRole;
use crate::controller::workload_run::WorkloadError;
use crate::controller::workload_run::authors::HostLeasedAuthor;
use crate::controller::workload_run::lifecycle::{Route, publish_summary, record_request, record_route};
use crate::controller::workload_run::sessions::socket_directory;
use crate::controller::PromptInput;
use crate::prompts::engine_general_sections::Shape;
use crate::storage::asset_release::AssetUpkeep;
use crate::storage::engine_library::library_bytes;
use crate::tools::bench::{BenchConfig, Workbench};
use crate::tools::TrialVerification;
use gendb_artifacts::verus::{VERUS_ENGINE_LINEAGE_KIND, VerusEngineLineageV1, engine_versions};
use gendb_artifacts::ObjectStore;
use gendb_frontend::parser::SqlParser;
use gendb_verification::admission::AdmissionError;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::mpsc;

/// The ladder's state in the engine directory.
pub const LADDER_FILE: &str = "scale.json";

/// Why a stage run never moves (its ladder decision).
pub const STAGE_LADDER_OFF: &str = "off in a stage run: every workload stays at the last scale of its request";

/// The branch slots of a run with `count` branches: `b1`, `b2`, ...
pub fn branch_names(count: u32) -> Vec<String> {
    (1..=count).map(|i| format!("b{i}")).collect()
}

// ------------------------------------------------------------------------------------------------ pure rules

/// What a slot runs next.
#[derive(Clone, Debug, PartialEq)]
pub enum SlotPlan {
    /// Its open session (a relaunch resumes it from its records).
    Resume(PathBuf),
    /// A new session.
    Start { number: u32, kind: SessionKind, seed: String, merge_from: Option<String>, previous: Option<PathBuf> },
}

/// The next session of slot `branch` (module documentation): its open session, else a merge session when one is due
/// and its last session was not a merge, else a branch session from its head.
pub fn plan_slot(tree: &VersionTree, sessions: &[SessionView], branch: &str) -> Result<SlotPlan, String> {
    if let Some(open) = sessions.iter().find(|s| s.open) {
        return Ok(SlotPlan::Resume(open.directory.clone()));
    }
    let last = sessions.last();
    let number = last.map_or(1, |s| s.record.number + 1);
    let previous = last.map(|s| s.directory.clone());
    let after_merge = last.is_some_and(|s| s.record.kind == SessionKind::Merge);
    if let Some((head, main)) = tree.merge_due(branch).filter(|_| !after_merge) {
        return Ok(SlotPlan::Start { number, kind: SessionKind::Merge, seed: main, merge_from: Some(head), previous });
    }
    let head = tree.branch_head(branch).ok_or_else(|| "the tree has no version 0: run gendb engine prepare first".to_string())?;
    Ok(SlotPlan::Start { number, kind: SessionKind::Branch, seed: head.to_string(), merge_from: None, previous })
}

/// Staggered start: the first slot starts at once, every other once the first slot's sessions have
/// evaluated a submission.
pub fn may_start(branch: &str, first_slot_evaluated: u32) -> bool {
    branch == "b1" || first_slot_evaluated > 0
}

/// Whether a slot runs `plan` now (module documentation, scale ladder): while the ladder's move is due
/// (`move_due`), only an open session resumes (it ends at its next evaluation); a new session waits for the move.
pub fn starts_now(plan: &SlotPlan, move_due: bool) -> bool {
    !move_due || matches!(plan, SlotPlan::Resume(_))
}

/// Whether the run pauses for review after `session` ended.
pub fn pauses_after(cadence: PauseCadence, session: &SessionRecord) -> bool {
    match cadence {
        PauseCadence::Never => false,
        PauseCadence::FirstSessionOfEachBranch => session.number == 1,
        PauseCadence::EverySession => true,
    }
}

/// The ladder's decision at the current scale.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LadderDecision {
    /// Stay, and why.
    Stay(String),
    /// Move to scale `next`.
    Move { next: usize },
}

/// The ladder rule: move from scale `current` of `scales` when the main-line
/// head's score there has every cell finished. No storage condition: the head, like every accepted version, is within
/// the budget of its scale.
pub fn ladder_decision(current: usize, scales: usize, head_score: Option<&RecordedScore>) -> LadderDecision {
    if current + 1 >= scales {
        return LadderDecision::Stay("the last scale of the ladder".into());
    }
    match head_score {
        None => return LadderDecision::Stay("the main-line head has no score at this scale yet".into()),
        Some(score) if !score.all_finished() => {
            return LadderDecision::Stay(format!("the main-line head finished {} of {} cells", score.score.finished, score.cells));
        }
        Some(_) => {}
    }
    LadderDecision::Move { next: current + 1 }
}

/// The ladder's decision at `general`'s scale over `tree` ([`ladder_decision`]): the main-line head's recorded score
/// there. Asked by the driver before it starts sessions and by every session evaluation (`engine::acceptance`), which
/// ends its session when the move is due.
pub fn ladder_check(general: &GeneralInputs, tree: &VersionTree) -> LadderDecision {
    let head = tree.main_line_head().unwrap_or(ROOT_VERSION);
    ladder_decision(general.scale_index, general.scales, tree.score_at(head, &general.scale.name).as_ref())
}

/// The session end a ladder decision asks for (`engine::sessions::session_end`): a due move at `general`'s scale, named
/// as the session's texts name the deciding head.
pub fn due_scale_move<'a>(general: &'a GeneralInputs, decision: &LadderDecision) -> Option<DueScaleMove<'a>> {
    match decision {
        LadderDecision::Move { .. } => Some(DueScaleMove {
            head: Shape::of_branches(general.branches.len()).head(),
            from: &general.scale.name,
            to: general.next_scale.as_deref().unwrap_or("the next scale"),
        }),
        LadderDecision::Stay(_) => None,
    }
}

/// `scale.json`: the current scale and every move.
#[derive(Clone, Debug, Default, PartialEq, Serialize, Deserialize)]
pub struct LadderState {
    pub format_version: u32,
    pub current: usize,
    pub moves: Vec<Value>,
}

impl LadderState {
    pub fn read(engine_dir: &Path) -> Result<Self, RecordError> {
        let path = engine_dir.join(LADDER_FILE);
        if path.is_file() { records::read_json(&path) } else { Ok(Self { format_version: 1, current: 0, moves: vec![] }) }
    }

    /// The ladder of a run about to be prepared or run: its record, else the start scale of its request
    /// (`EngineRequest::start_scale`). A continued run starts at the last scale (no move, no timing), which is written to
    /// `scale.json` at once, so every reader of the run's ladder (facts, final evaluation, summaries) sees it.
    pub fn start(engine_dir: &Path, engine: &EngineRequest) -> Result<Self, RecordError> {
        let path = engine_dir.join(LADDER_FILE);
        if path.is_file() {
            return records::read_json(&path);
        }
        let state = Self { format_version: 1, current: engine.start_scale(), moves: vec![] };
        if state.current > 0 {
            records::create_dir(engine_dir)?;
            write_json_atomic(&path, &state)?;
        }
        Ok(state)
    }
}

// ------------------------------------------------------------------------------------------------ framework work

/// A framework step's failure as the run reports it (a resumable controller error naming the step).
pub(super) fn framework_error(error: AdmissionError) -> WorkloadError {
    WorkloadError::Controller(crate::controller::ControllerError::Role { stage: "engine framework work", detail: error.to_string() })
}

/// A role without an author for framework work at one scale (version 0, a scale move, a final evaluation): its bench is
/// opened on `directory/author`.
pub(super) fn framework_role(request: &WorkloadRequest, prepared: &PreparedEngine, engine_dir: &Path, directory: &Path) -> Result<EngineAuthorRole, AdmissionError> {
    let bench = session_bench(request, prepared)?;
    let mut role = EngineAuthorRole::new(bench, EngineRoleConfig { engine_dir: engine_dir.to_path_buf(), inputs: prepared.inputs.clone(), mode: EngineRoleMode::Framework });
    role.view().bench.open_workspace(&directory.join("author"))?;
    Ok(role)
}

/// The session bench of the general line at `prepared`'s scale: no bench-level storage allowance (the budget rule
/// is applied per candidate at evaluation and admission, `GeneralInputs::budget_rule`), and the
/// shared host's upkeep of storage assets (`storage::asset_release`: the free-space floor of every asset build).
pub(super) fn session_bench(request: &WorkloadRequest, prepared: &PreparedEngine) -> Result<Workbench, AdmissionError> {
    Ok(Workbench::new(
        BenchConfig {
            library: request.library.clone(),
            locks: request.host_locks.clone(),
            parser: SqlParser::from_environment().map_err(|e| AdmissionError::tool(format!("SQL frontend: {e}")))?,
            live_bytes_allowance: None,
            storage_policy: request.storage_policy.clone(),
            asset_upkeep: Some(AssetUpkeep::GENERAL_LINE),
        },
        prepared.data.capture.clone(),
        prepared.inputs.sessions.iter().map(|(_, s)| s.clone()).collect(),
    ))
}

/// The notebook of version 0 (`NOTES.md` of `v000`, carried into the first session of every branch).
const VERSION_ZERO_NOTES_MD: &str = "# Notes\n\n## Direction\n\nVersion 0, generated by GenDB: the verified SQLSpec interpreter over the flat storage of every table (no author).\n\n## Design\n\n`agent/mod.rs` materializes every table from its flat storage (`crate::flat_tables::materialize_database`), runs `exec_ordered` and maps its outcome; its proof is the interpreter's theorem plus the uniqueness of the bound database. It names no table or column.\n\n## Tried\n\nNothing yet. Its timing at the first scale is in `version.json` and `cells/`.\n\n## Ideas\n\nKnown costs of the interpreter (the prompt's Fallback section): every call materializes every table; FROM lists and inner joins are materialized products; AND/OR evaluate both sides; every subquery runs again per outer row; GROUP BY and the top-level sort are quadratic; one thread.\n\n## Proof notes\n\nThe interpreter's ensures (`rel_outcome_ok` with `denote_top`) and `lemma_denote_top_ok` give `answer_meets`.\n";

/// What a run's root version (`v000`) is made of. Production seeds one of two: version 0, GenDB's interpreter engine
/// ([`RootSource::interpreter`]), or, for a continued run (`engine.seed_version`), an accepted
/// version of another general-line run ([`RootSource::seeded`]). A third source exists only in test builds (the general
/// line's trial seeds a labeled slowed copy of version 0 as the parent its submissions are raced against,
/// `engine::general_trial`); no request field or command can name one.
pub struct RootSource {
    /// The generator identity recorded as the root's origin.
    generator: String,
    /// What writes the root's workspace.
    from: RootFrom,
    /// The manifest's notes, the node's direction, the notebook (`NOTES.md`), the README's heading and description.
    manifest_notes: String,
    direction: String,
    notes_md: String,
    heading: String,
    description: String,
}

/// What writes a root's workspace.
enum RootFrom {
    /// Its `agent/` files generated from the schema and the flat uses, over the flat uses.
    Generated(RootAgentGenerator),
    /// An accepted version of another general-line run: its code and its own storage uses
    /// (`engine::submission::write_root_from_seed_version`).
    Version(SeedVersion),
}

impl RootSource {
    /// Version 0: the verified interpreter over the flat storage of every table (`gendb-interpreter-engine-v0`).
    pub fn interpreter() -> Self {
        Self {
            generator: gendb_verification::obligations::INTERPRETER_ENGINE_GENERATOR.into(),
            from: RootFrom::Generated(gendb_verification::obligations::interpreter_engine),
            manifest_notes: super::submission::VERSION_ZERO_NOTES.into(),
            direction: "version 0: the verified interpreter over the flat storage (framework generated)".into(),
            notes_md: VERSION_ZERO_NOTES_MD.into(),
            heading: "version 0".into(),
            description: "Generated by GenDB: the verified interpreter over the flat storage of every table.".into(),
        }
    }

    /// A continued run's root (`engine.seed_version`): the seed version's code over its own storage uses (which the run's
    /// library holds admitted), frozen under this run's rules, verified whole, timed alone and admitted like version 0;
    /// its notebook continues. Refused (missing input) when the folder is not an accepted version
    /// (`engine::submission::write_root_from_seed_version` checks its code and manifest when it writes the workspace).
    pub fn seeded(seed: &SeedVersion) -> Result<Self, AdmissionError> {
        let directory = seed.directory();
        let node: Value = read_json(&directory.join(tree::NODE_FILE)).map_err(|e| AdmissionError::missing_input(format!("engine.seed_version {}: {e}", directory.display())))?;
        if node["accepted"] != true {
            return Err(AdmissionError::missing_input(format!("engine.seed_version {}: not an accepted version", directory.display())));
        }
        let notes_md = fs::read_to_string(directory.join(NOTES_FILE)).unwrap_or_else(|_| format!("# Notes\n\nThe seed version {} of `{}` kept no notebook.\n", seed.version, seed.run.display()));
        let from = format!("version {} of the run `{}`", seed.version, seed.run.display());
        Ok(Self {
            generator: format!("seed: {from}"),
            from: RootFrom::Version(seed.clone()),
            manifest_notes: format!("the seed {from}: its code and its storage uses, verified whole and timed alone in this run (no author)"),
            direction: format!("continued run: the seed {from} (its code and storages)"),
            notes_md,
            heading: format!("continued from {}", seed.version),
            description: format!("Made by GenDB from the seed {from}: its code and its storage uses, frozen under this run's rules, verified whole and timed alone here (no author)."),
        })
    }

    /// The root of `engine`: the seed version of a continued run, else version 0.
    pub fn of(engine: &EngineRequest) -> Result<Self, AdmissionError> {
        match &engine.seed_version {
            Some(seed) => Self::seeded(seed),
            None => Ok(Self::interpreter()),
        }
    }

    /// The seed version of a continued run's root (`None`: a generated root).
    fn seed(&self) -> Option<&SeedVersion> {
        match &self.from {
            RootFrom::Version(seed) => Some(seed),
            RootFrom::Generated(_) => None,
        }
    }

    /// The root's origin as its records state it: the generator, and a continued run's seed version.
    fn origin(&self) -> Value {
        match self.seed() {
            None => json!({"generator":self.generator,"author":"none (generated by GenDB)"}),
            Some(seed) => json!({"generator":self.generator,"seed":{"run":seed.run,"version":seed.version},"author":"none (made by GenDB from the seed version)"}),
        }
    }

    /// A test fixture's root (test builds only), named by `generator` in every record it leaves.
    #[cfg(test)]
    pub(super) fn fixture(generator: &'static str, agent: RootAgentGenerator, manifest_notes: &'static str, notes_md: &'static str, description: &'static str) -> Self {
        Self { generator: generator.into(), from: RootFrom::Generated(agent), manifest_notes: manifest_notes.into(), direction: manifest_notes.into(), notes_md: notes_md.into(),
            heading: "version 0".into(), description: description.into() }
    }
}

/// What version 0's admission recorded (`seed-v0/admitted.json`), so a resumed preparation finishes its records
/// without admitting it twice. `profile` is filled after the admission (`Null` until then).
#[derive(Clone, Debug, Serialize, Deserialize)]
struct VersionZeroAdmission {
    admission: Value,
    frozen: PathBuf,
    score: RecordedScore,
    cells: Vec<CellResult>,
    checks: Value,
    #[serde(default)]
    profile: Value,
}

/// What version 0's admission intent keeps (`seed-v0/admitting.json`, `engine::acceptance::AdmissionIntent`).
#[derive(Clone, Debug, Serialize, Deserialize)]
struct RootKeep {
    frozen: PathBuf,
    score: RecordedScore,
    cells: Vec<CellResult>,
    checks: Value,
}

/// The run's root (module documentation): version 0 generated, or a continued run's seed version
/// ([`RootSource::of`]), frozen, verified, timed alone at the run's start scale, admitted as `v000` and selected as the
/// main-line head. Idempotent: an existing `v000` with a main-line head is returned as it is.
pub fn seed_version_zero(request: &WorkloadRequest, prepared: &PreparedEngine, engine_dir: &Path) -> Result<Value, WorkloadError> {
    let source = RootSource::of(request.engine()?).map_err(framework_error)?;
    seed_root_version(request, prepared, engine_dir, &source)
}

/// [`seed_version_zero`] with the root's source. Resumable at every step: the
/// evaluation's intent (`seed-v0/admitting.json`) is written before the library admission and the admission
/// (`seed-v0/admitted.json`) after it, before the profile and the folder; a resumed preparation adopts the library's
/// admission of the same frozen root or admits from the intent (`engine::acceptance::EngineBench::admit_from_intent`),
/// never twice.
pub(super) fn seed_root_version(request: &WorkloadRequest, prepared: &PreparedEngine, engine_dir: &Path, source: &RootSource) -> Result<Value, WorkloadError> {
    let tree = VersionTree::read(engine_dir)?;
    if let (Some(v0), Some(_)) = (tree.version(ROOT_VERSION), tree.main_line_head()) {
        return Ok(json!({"status":"present","version":v0.id,"directory":v0.directory(engine_dir)}));
    }
    let engine = request.engine()?;
    let general = prepared.inputs.general.clone().ok_or_else(|| WorkloadError::invalid("engine: version 0 is prepared at a scale of the general line"))?;
    let dir = engine_dir.join("seed-v0");
    records::create_dir(&dir)?;
    let recorded = dir.join("admitted.json");
    let mut admitted: VersionZeroAdmission = if recorded.is_file() {
        // Admitted before an interruption: finish the records from what was recorded.
        read_json(&recorded)?
    } else {
        let admitted = admit_root(request, prepared, engine_dir, &dir, source).map_err(framework_error)?;
        write_json_atomic(&recorded, &admitted)?;
        admitted
    };
    if admitted.admission["library_version"] != 1 {
        return Err(WorkloadError::invalid(format!("engine: version 0 was admitted as library version {}, not 1", admitted.admission["library_version"])));
    }
    let node = TreeNode {
        format_version: 1,
        id: ROOT_VERSION.into(),
        accepted: true,
        kind: NodeKind::FrameworkGenerated,
        branch: tree::MAIN.into(),
        parents: vec![],
        scale: general.scale.name.clone(),
        score: Some(admitted.score.clone()),
        reason: None,
        session: None,
        iteration: None,
        direction: Some(source.direction.clone()),
        rationale: Some(source.manifest_notes.clone()),
        created_unix_ms: now_unix_ms(),
    };
    // 8. The profile (never gating), once, after the admission is recorded.
    if admitted.profile.is_null() && !node.directory(engine_dir).join(tree::NODE_FILE).is_file() {
        admitted.profile = profile_root(request, prepared, engine_dir, &dir, &admitted);
        write_json_atomic(&recorded, &admitted)?;
    }
    write_version_zero_folder(engine_dir, &node, &admitted, source).map_err(framework_error)?;
    let store = ObjectStore::open_existing(&request.library).map_err(|e| framework_error(AdmissionError::tool(format!("{}: {e}", request.library.display()))))?;
    let _lock = main_line_lock(engine_dir).map_err(framework_error)?;
    if VersionTree::read(engine_dir)?.main_line_head().is_none() {
        let selected = gendb_artifacts::verus::engine_selections(&store).map_err(|e| framework_error(AdmissionError::tool(e)))?;
        // Selected before an interruption: the library's selection stream already names it.
        let selection = match selected.last() {
            Some((id, _)) => *id,
            None => select_version(&store, ROOT_VERSION, "version_0", None).map_err(framework_error)?,
        };
        append_main_line(engine_dir, &MainLineChange { version: ROOT_VERSION.into(), previous: None, reason: "version_0".into(), scale: general.scale.name.clone(), race: None, adopted: None, selection, at_unix_ms: now_unix_ms() })?;
    }
    let branches = branch_names(engine.branches.unwrap_or(1));
    VersionTree::read(engine_dir)?.write_views(engine_dir, &branches)?;
    Ok(json!({"status":"admitted","version":ROOT_VERSION,"directory":node.directory(engine_dir),"score":admitted.score,"admission":admitted.admission,
        "profile":admitted.profile,"origin":source.origin(),"cost_usd":"0",
        "cost":match source.seed() {
            None => "framework work: version 0 was built during framework development, not by an author; its admission evaluation is framework compute, not author cost",
            Some(_) => "framework work: the seed version's cost is its own run's; its admission evaluation here is framework compute, not author cost",
        }}))
}

/// Generate, freeze, verify, time and check the root under `dir`, record the intent, and admit it once
/// (`seed_root_version`). A recorded intent (an interruption after the evaluation) skips straight to the admission.
fn admit_root(request: &WorkloadRequest, prepared: &PreparedEngine, engine_dir: &Path, dir: &Path, source: &RootSource) -> Result<VersionZeroAdmission, AdmissionError> {
    let mut role = framework_role(request, prepared, engine_dir, dir)?;
    let intent_file = dir.join(ADMITTING_FILE);
    let intent = match AdmissionIntent::read(&intent_file)? {
        Some(intent) => intent,
        None => {
            let intent = evaluate_root(&mut role, request, prepared, dir, source)?;
            intent.write(&intent_file)?;
            intent
        }
    };
    let keep: RootKeep = serde_json::from_value(intent.keep.clone()).map_err(AdmissionError::tool)?;
    let engine: FrozenEngine = read_json(&keep.frozen.join("candidate.json")).map_err(AdmissionError::tool)?;
    let mut admission = role.view().admit_from_intent(&keep.frozen, &engine, &intent)?;
    admission["evaluation"] = json!(intent.evaluation);
    Ok(VersionZeroAdmission { admission, frozen: keep.frozen, score: keep.score, cells: keep.cells, checks: keep.checks, profile: Value::Null })
}

/// Steps 1-6 of the root (no parent): written into the workspace (version 0 generated over the plain storage, or a
/// continued run's seed version copied with its own storage uses), frozen under the general line's rules, verified and
/// compiled whole, its storages checked (under the budget rule like every version), timed alone at the run's start scale
/// with every failing cell recorded, its finished templates checked. Returns the intent of its admission.
fn evaluate_root(role: &mut EngineAuthorRole, request: &WorkloadRequest, prepared: &PreparedEngine, dir: &Path, source: &RootSource) -> Result<AdmissionIntent, AdmissionError> {
    let general = prepared.inputs.general.clone().ok_or_else(|| AdmissionError::tool("general inputs"))?;
    let mut bench = role.view();
    let store = bench.bench.store()?;
    let existing = engine_versions(&store).map_err(AdmissionError::tool)?;
    if !existing.is_empty() {
        return Err(AdmissionError::refusal(format!("the library {} already holds {} engine versions but this run has no version 0; a general-line run starts from an engine library without engine versions", request.library.display(), existing.len())));
    }
    let workspace = bench.bench.workspace()?.to_path_buf();
    let substitutes = std::collections::BTreeMap::new();
    let context = super::submission::EngineFreeze {
        workspace: &workspace,
        schema: bench.schema(),
        library: &request.library,
        substitutes: &substitutes,
        policy: &request.storage_policy,
        rules: &prepared.inputs.rules,
    };
    let submission = match &source.from {
        RootFrom::Generated(agent) => {
            write_root_version(&context, &prepared.inputs.seeded, &dir.join("uses"), *agent, &source.manifest_notes)?;
            CandidateSubmission { candidate_manifest: MANIFEST_FILE.into(), rationale: "version 0, generated by GenDB".into(), data_access_analysis: "every table read whole from its flat storage".into() }
        }
        RootFrom::Version(seed) => {
            super::submission::write_root_from_seed_version(&workspace, &seed.directory())?;
            CandidateSubmission { candidate_manifest: MANIFEST_FILE.into(), rationale: source.manifest_notes.clone(), data_access_analysis: "the seed version's own storage access".into() }
        }
    };
    fs::write(workspace.join(NOTES_FILE), &source.notes_md).map_err(AdmissionError::tool)?;
    let frozen_dir = (0..).map(|n| dir.join(format!("frozen-{n}"))).find(|d| !d.exists()).expect("an unbounded range");
    let engine = bench.freeze_submission(&workspace, &frozen_dir, &submission)?.engine;
    // A fresh evaluation directory per attempt (`evaluation`, then `evaluation-1`, ...): an attempt stopped before its
    // intent was written (for example by the user's TERM during the Verus run) is evaluated again from the start.
    let evaluation = super::acceptance::fresh_directory(dir, "evaluation")?;
    let locks = request.host_locks.clone();
    let build = bench.builds.compile(&locks, &engine, &frozen_dir, &evaluation.join("verus-build"), true)?;
    let storages = bench.storages(&engine, &frozen_dir, &evaluation, TrialVerification::WholeCrate)?;
    bench.check_storage_policy(&engine, &frozen_dir, &storages, &general.budget_rule())?;
    let run = Runnable { label: format!("v000 ({})", source.heading), library: build.library.clone(), inputs: storage_inputs(&storages) };
    let (matrix, scored) = bench.time_alone(&run, VERSION_ZERO.cell_calls, &evaluation.join("timing"))?;
    let timing_file = evaluation.join("official-matrix.json");
    super::role::write_matrix(&matrix, &timing_file)?;
    write_json_atomic(&evaluation.join("score.json"), &json!(scored)).map_err(AdmissionError::tool)?;
    let score = RecordedScore::of(&general.scale.name, &scored, &evaluation.join("score.json"));
    let subject = CheckedEngine { library: &build.library, inputs: &run.inputs, frozen: None };
    let checks = bench.finished_checks(&VERSION_ZERO, &subject, &scored, &evaluation).map_err(|reason| AdmissionError::tool(format!("the root's finished checks ({}): {reason}", source.heading)))?;
    let lineage = VerusEngineLineageV1 { branch: tree::MAIN.into(), kind: "framework_generated".into(), parents: vec![] };
    let timing = json!({"score":scored.score,"cells_total":scored.cells_total,"beats_both":scored.beats_both,"file":timing_file,"generator":source.generator});
    let evidence = vec![(VERUS_ENGINE_LINEAGE_KIND.to_string(), json!(lineage)), (super::acceptance::ENGINE_FINISHED_CHECKS_KIND.to_string(), super::role::float_free(&checks)),
        (VERSION_ZERO_TIMING_KIND.to_string(), super::role::float_free(&timing))];
    let cells: Vec<CellResult> = scored.cells.iter().map(|c| CellResult { template: c.template.clone(), workers: c.workers, status: c.status }).collect();
    let keep = RootKeep { frozen: frozen_dir, score, cells, checks };
    Ok(AdmissionIntent { evaluation, build: build.record, evidence, keep: json!(keep), written_unix_ms: now_unix_ms() })
}

/// The root's profile (never gating) over its admitted library and assets, at the worker count of each
/// template's largest gap in its recorded cells; written under its evaluation directory.
fn profile_root(request: &WorkloadRequest, prepared: &PreparedEngine, engine_dir: &Path, dir: &Path, admitted: &VersionZeroAdmission) -> Value {
    let inputs = &prepared.inputs;
    let limit = inputs.general.as_ref().map_or(u64::MAX, |g| g.call_limits.call_limit_ns);
    let evaluation = PathBuf::from(admitted.admission["evaluation"].as_str().unwrap_or_default());
    let outcome = framework_role(request, prepared, engine_dir, dir).and_then(|mut role| {
        let mut bench = role.view();
        let scored = super::score::score(&inputs.baselines, &inputs.training.timing_binding, &inputs.workers, limit, &admitted.cells).map_err(|e| AdmissionError::tool(e.to_string()))?;
        let run = bench.admitted_runnable(ROOT_VERSION, &evaluation.join("profile-storages"))?;
        Ok(bench.profile_runnable(ROOT_VERSION, &run.library, &run.inputs, &scored, &evaluation))
    });
    outcome.unwrap_or_else(|error| json!({"status":"failed","error":error.to_string(),"meaning":"profiles are diagnostics: never gating"}))
}

/// Record kind of version 0's official timing (admission evidence; it has no parent to race).
pub const VERSION_ZERO_TIMING_KIND: &str = "gendb.verus.engine-timing.v1";

/// Version 0's folder: code, reading view, manifests, the root's notebook, cells, admission, `version.json` and the
/// node (last).
fn write_version_zero_folder(engine_dir: &Path, node: &TreeNode, admitted: &VersionZeroAdmission, source: &RootSource) -> Result<(), AdmissionError> {
    let target = node.directory(engine_dir);
    if target.join(tree::NODE_FILE).is_file() {
        return Ok(());
    }
    let frozen_dir = &admitted.frozen;
    let staging = target.with_file_name(format!(".staging-{}-{}", node.id, now_unix_ms()));
    fs::create_dir_all(&staging).map_err(AdmissionError::tool)?;
    let engine: FrozenEngine = read_json(&frozen_dir.join("candidate.json")).map_err(AdmissionError::tool)?;
    super::role::copy_tree(&frozen_dir.join("crate/src/agent"), &staging.join("code/agent"), false)?;
    for file in engine.author_files.iter().filter(|f| f.starts_with("agent/") && f.ends_with(".rs")) {
        let text = fs::read_to_string(frozen_dir.join("crate/src").join(file)).map_err(AdmissionError::tool)?;
        let view = staging.join("code-view").join(format!("{file}.md"));
        fs::create_dir_all(view.parent().unwrap_or(&staging)).map_err(AdmissionError::tool)?;
        fs::write(&view, crate::output::code_view(&text)).map_err(AdmissionError::tool)?;
    }
    let manifest: EngineManifest = read_json(&frozen_dir.join("manifest.json")).map_err(AdmissionError::tool)?;
    let uses: Vec<gendb_artifacts::verus::VerusStorageUseV1> = serde_json::from_value(admitted.admission["uses"].clone()).map_err(AdmissionError::tool)?;
    let seed = EngineManifest {
        crate_dir: CRATE_DIRECTORY.into(),
        storage_uses: uses.iter().map(|u| crate::query::candidate::StorageUseDeclaration::admitted(&u.name, u.package)).collect(),
        ..manifest.for_seed()
    };
    let write = |name: &str, value: &Value| write_json_atomic(&staging.join(name), value).map_err(AdmissionError::tool);
    write("manifest.json", &json!(manifest))?;
    write("seed-manifest.json", &json!(seed))?;
    fs::write(staging.join(NOTES_FILE), &source.notes_md).map_err(AdmissionError::tool)?;
    fs::create_dir_all(staging.join("cells")).map_err(AdmissionError::tool)?;
    write(&format!("cells/{}.json", node.scale), &json!(admitted.cells))?;
    write("admission.json", &admitted.admission)?;
    if let Some(evaluation) = admitted.admission["evaluation"].as_str().map(PathBuf::from) {
        for name in ["official-matrix.json", "score.json", super::profile::PROFILE_FILE] {
            if evaluation.join(name).is_file() {
                fs::copy(evaluation.join(name), staging.join(name)).map_err(AdmissionError::tool)?;
            }
        }
        if evaluation.join(super::profile::PROFILE_DIRECTORY).is_dir() {
            super::role::copy_tree(&evaluation.join(super::profile::PROFILE_DIRECTORY), &staging.join(super::profile::PROFILE_DIRECTORY), false)?;
        }
    }
    let mut times = serde_json::Map::new();
    times.insert(node.scale.clone(), json!({"score":node.score,"timing":"timed alone (no parent)","evaluation":admitted.admission["evaluation"]}));
    write("version.json", &json!({"format_version":1,"version":node.id,"accepted":true,"node":node,"parents":[],"branch":tree::MAIN,"kind":node.kind,
        "origin":source.origin(),
        "goal":{"scale":node.scale},"storage":{"uses":uses,"budget_rule":match source.seed() {
            None => "version 0 reads only the plain storage, allowed as is at every scale",
            Some(_) => "the seed version's storages, checked under this scale's budget rule like every version",
        }},
        "times":times,"cost":{"known_provider_reported_cost_usd":"0","scope":"no author: framework work"},
        "finished_checks":admitted.checks,"admission":admitted.admission,"profile":admitted.profile}))?;
    let score = &admitted.score;
    fs::write(staging.join("README.md"), format!("# Engine version {} ({})\n\n{} Score at {}: {} of {} cells finished, normalized time {}.\n",
        node.id, source.heading, source.description, node.scale, score.score.finished, score.cells, score.score.normalized_time)).map_err(AdmissionError::tool)?;
    write(tree::NODE_FILE, &json!(node))?;
    fs::rename(&staging, &target).map_err(|e| AdmissionError::tool(format!("{}: {e}", target.display())))
}

// ------------------------------------------------------------------------------------------------ the run

/// `gendb engine prepare REQUEST RUN_DIR`: the run directory's route and request, the inputs of the
/// current scale and version 0, without any author. Returns the preparation record (`engine/prepare.json`).
pub async fn prepare_general_run(request: &WorkloadRequest, run_dir: &Path, framework_executable: &Path) -> Result<Value, WorkloadError> {
    let (root, engine) = open_run(request, run_dir)?;
    let parser = SqlParser::from_environment().map_err(WorkloadError::Frontend)?;
    let engine_dir = engine_directory(&root);
    // A run of several workloads (a stage run, or engine.workloads): every workload at its last scale, and its root
    // with one side per workload instead of version 0 (`engine::stage::root`).
    if several_workloads(engine) {
        let run = StageRun::prepare(request, &root, &parser, framework_executable).await?;
        let branches = branch_names(engine.branches.unwrap_or(1));
        let run_root = super::stage::root::seed_stage_root(&run, &engine_dir, &branches)?;
        crate::output::engine::general::write_general_output(request, &root, &engine_dir);
        let workloads: Vec<Value> = run.workloads().map(|w| json!({"name":w.name,"role":run.role_name(w),"scale":w.scale(),"first_scale":w.first_scale_name(),"library":w.request.library,
            "library_bytes":library_bytes(&w.request.library).ok()})).collect();
        let record = match run.form {
            WorkloadForm::Workloads => json!({"format_version":1,"run":root,"scale":run.primary.scale(),"workloads":{"primary":run.primary.name,"workloads":workloads,"seed":run.seed},
                "root":run_root,"library_bytes":library_bytes(&request.library).map_err(framework_error)?,"prepared_unix_ms":now_unix_ms(),
                "next":"gendb engine synthesize REQUEST RUN_DIR starts the branch session from the root v000 (one side per workload)"}),
            _ => json!({"format_version":1,"run":root,"scale":run.primary.scale(),"stage":{"goal":run.primary.name,"workloads":workloads,"seed":run.stage_seed().map_err(framework_error)?},"root":run_root,
                "out_of_the_box":engine_dir.join(super::stage::root::SEED_DIRECTORY).join(super::stage::root::OUT_OF_THE_BOX_DIRECTORY).join(super::stage::root::OUT_OF_THE_BOX_FILE),
                "library_bytes":library_bytes(&request.library).map_err(framework_error)?,"prepared_unix_ms":now_unix_ms(),
                "next":"gendb engine synthesize REQUEST RUN_DIR starts the branch sessions from the stage root v000"}),
        };
        write_json_atomic(&engine_dir.join("prepare.json"), &record)?;
        return Ok(record);
    }
    let ladder = LadderState::start(&engine_dir, engine)?;
    let prepared = prepare_engine_scale(request, ladder.current, &root, &parser, framework_executable).await?;
    let version_zero = seed_version_zero(request, &prepared, &engine_dir)?;
    crate::output::engine::general::write_general_output(request, &root, &engine_dir);
    let record = json!({"format_version":1,"run":root,"scale":request.engine()?.scales[ladder.current].name,"version_zero":version_zero,
        "library_bytes":library_bytes(&request.library).map_err(framework_error)?,"prepared_unix_ms":now_unix_ms(),
        "next":"gendb engine synthesize REQUEST RUN_DIR starts the branch sessions from the root v000"});
    write_json_atomic(&engine_dir.join("prepare.json"), &record)?;
    Ok(record)
}

/// Validate a general-line request and record the run directory's route and request; `(run root, engine section)`.
pub(super) fn open_run<'r>(request: &'r WorkloadRequest, run_dir: &Path) -> Result<(PathBuf, &'r EngineRequest), WorkloadError> {
    request.validate()?;
    let engine = request.engine()?;
    if !engine.is_general() {
        return Err(WorkloadError::invalid("engine: this is a schema-engine request (no engine.line); gendb engine prepare is for the general line"));
    }
    records::create_dir(run_dir)?;
    let root = run_dir.canonicalize().map_err(|e| RecordError::new(run_dir, e))?;
    record_route(&root, Route::Engine)?;
    record_request(&root, &serde_json::to_value(request).map_err(|e| WorkloadError::invalid(e.to_string()))?)?;
    Ok((root, engine))
}

/// How the driver runs sessions: the prompt of every call, and whether only one render call per session is made.
#[derive(Clone, Copy)]
pub struct GeneralRunOptions {
    pub prompt: fn(&PromptInput) -> String,
    /// Render-only: every session ends after its first submission, only `b1` starts, and the run pauses after it.
    pub render_only: bool,
}

/// The general line's run (module documentation) with `authors(label, inspection_dir)` as each session's author.
pub async fn run_general_engine<A, F>(request: &WorkloadRequest, run_dir: &Path, mut authors: F, framework_executable: &Path, options: GeneralRunOptions) -> Result<Value, WorkloadError>
where
    A: AuthorTransport + Send + 'static,
    F: FnMut(&str, &Path) -> Result<A, String>,
{
    let (root, engine) = open_run(request, run_dir)?;
    let parser = SqlParser::from_environment().map_err(WorkloadError::Frontend)?;
    let engine_dir = engine_directory(&root);
    let mut ladder = LadderState::start(&engine_dir, engine)?;
    let branches = branch_names(if options.render_only { 1 } else { engine.branches.unwrap_or(1) });
    // A run of several workloads (`engine::stage`): every workload at its last scale, its root, and no ladder; the
    // primary's inputs are the sessions' own.
    let stage = match several_workloads(engine) {
        true => Some(StageRun::prepare(request, &root, &parser, framework_executable).await?),
        false => None,
    };
    let mut prepared = match &stage {
        Some(run) => {
            super::stage::root::seed_stage_root(run, &engine_dir, &branch_names(engine.branches.unwrap_or(1)))?;
            super::stage::share_prepared(&run.primary.prepared)
        }
        None => {
            let prepared = prepare_engine_scale(request, ladder.current, &root, &parser, framework_executable).await?;
            seed_version_zero(request, &prepared, &engine_dir)?;
            prepared
        }
    };
    // The first scale, where sessions at a later scale check their submissions' variants (`engine::protocol`): prepared
    // once per controller process, from the run's records under `engine/scales/<first>/` (a render evaluates nothing).
    // A stage run's goal brings its own.
    let mut first_scale = match (&stage, ladder.current) {
        (Some(run), _) => run.primary.first_scale.clone().filter(|_| !options.render_only),
        (None, 0) => None,
        _ if options.render_only => None,
        _ => Some(FirstScale::of(&prepare_engine_scale(request, 0, &root, &parser, framework_executable).await?)),
    };
    let sockets = socket_directory()?;
    // Once per launch, the run library's superseded derived storage assets (`engine::asset_upkeep`): only when no
    // session is open, since an open one may resume an admission that reads them.
    if !options.render_only {
        let open = branches.iter().map(|b| branch_sessions(&engine_dir, b)).collect::<Result<Vec<_>, _>>()?.into_iter().flatten().any(|s| s.open);
        if open {
            super::asset_upkeep::record_skipped(&engine_dir, "controller start", "a session is open (its next admission, or the next scale move, releases them)");
        } else {
            match &stage {
                None => {
                    super::asset_upkeep::release_pass(&request.library, &engine_dir, "controller start");
                }
                Some(run) => {
                    for workload in run.workloads() {
                        super::asset_upkeep::release_workload_pass(&workload.request.library, &engine_dir, "controller start", &workload.name);
                    }
                }
            }
        }
    }
    let spend = RunSpend::new(&engine_dir, engine.limits.max_cost_usd);
    let (sender, receiver) = mpsc::channel::<(String, PathBuf, Result<Value, String>)>();
    let mut running: BTreeSet<String> = BTreeSet::new();
    let mut threads = vec![];
    let mut pause_after: Vec<PathBuf> = vec![];
    let mut stop: Option<(&'static str, String)> = None;
    let mut ladder_note;
    // A framework failure of the driver itself stops the run resumably once the running sessions have ended; it never
    // abandons a running session.
    let fail = |stop: &mut Option<(&'static str, String)>, error: WorkloadError| {
        stop.get_or_insert(("resumable", format!("framework_error: {error}")));
    };
    let (status, reason) = loop {
        let state = (|| -> Result<(VersionTree, bool, LadderDecision), WorkloadError> {
            let tree = VersionTree::read(&engine_dir)?;
            let budget_used = spend.now()?.spent >= engine.limits.max_cost_usd;
            let decision = if stage.is_some() { LadderDecision::Stay(STAGE_LADDER_OFF.into()) } else { driver_ladder_check(&prepared, &tree).map_err(framework_error)? };
            Ok((tree, budget_used, decision))
        })();
        let (tree, budget_used, decision) = match state {
            Ok(state) => state,
            Err(error) => {
                fail(&mut stop, error);
                (VersionTree::default(), false, LadderDecision::Stay("the records could not be read".into()))
            }
        };
        ladder_note = json!({"current":engine.scales[ladder.current].name,"decision":format!("{decision:?}")});
        let pausing = !pause_after.is_empty() || stop.is_some();
        // While the move is due, only open sessions run (`starts_now`); each ends at its next evaluation.
        let moving = matches!(decision, LadderDecision::Move { .. }) && !pausing && !budget_used;
        if running.is_empty() {
            if let Some((status, reason)) = stop.take() {
                break (status, reason);
            }
            if budget_used {
                break ("stopped", "budget_limit".to_string());
            }
            if pausing {
                break (PAUSED, PAUSED_FOR_REVIEW.to_string());
            }
            if let LadderDecision::Move { next } = decision {
                let moved = async {
                    let open = branches.iter().map(|b| branch_sessions(&engine_dir, b)).collect::<Result<Vec<_>, _>>()?.into_iter().flatten().any(|s| s.open);
                    if open {
                        // An open session (after a relaunch) resumes below and ends at its next evaluation; the move
                        // waits for it.
                        return Ok(None);
                    }
                    let next_prepared = prepare_engine_scale(request, next, &root, &parser, framework_executable).await?;
                    let record = move_scale(request, &next_prepared, &engine_dir, &branches, &tree).map_err(framework_error)?;
                    Ok::<_, WorkloadError>(Some((next_prepared, record)))
                }
                .await;
                match moved {
                    Ok(Some((next_prepared, record))) => {
                        // Leaving the first scale: its inputs stay for the variants of later submissions.
                        if ladder.current == 0 {
                            first_scale = Some(FirstScale::of(&prepared));
                        }
                        ladder.current = next;
                        ladder.moves.push(record);
                        ladder.format_version = 1;
                        if let Err(error) = write_json_atomic(&engine_dir.join(LADDER_FILE), &ladder) {
                            fail(&mut stop, error.into());
                        }
                        prepared = next_prepared;
                        continue;
                    }
                    Ok(None) => {}
                    Err(error) => {
                        fail(&mut stop, error);
                        continue;
                    }
                }
            }
        }
        if !(pausing || budget_used) {
            let started = (|| -> Result<(), WorkloadError> {
                let first_slot_evaluated: u32 = branch_sessions(&engine_dir, &branches[0])?.iter().map(|s| s.evaluated).sum();
                for branch in &branches {
                    if running.contains(branch) || !may_start(branch, first_slot_evaluated) {
                        continue;
                    }
                    let sessions = branch_sessions(&engine_dir, branch)?;
                    let plan = plan_slot(&tree, &sessions, branch).map_err(WorkloadError::invalid)?;
                    if !starts_now(&plan, moving) {
                        continue;
                    }
                    let session = build_session(request, engine, &prepared, stage.as_ref(), first_scale.as_ref(), &engine_dir, branch, plan, &spend, options, &mut authors, &sockets)?;
                    let (branch_name, directory, sender) = (branch.clone(), session.directory.clone(), sender.clone());
                    threads.push(std::thread::spawn(move || {
                        let result = run_sessions(vec![session], &directory, 1).map(|mut r| r.pop().unwrap_or(Value::Null)).map_err(|e| e.to_string());
                        let _ = sender.send((branch_name, directory, result));
                    }));
                    running.insert(branch.clone());
                }
                Ok(())
            })();
            if let Err(error) = started {
                fail(&mut stop, error);
            }
        }
        if running.is_empty() {
            match stop.take() {
                Some((status, reason)) => break (status, reason),
                None => break ("stopped", "no_session_can_start".to_string()),
            }
        }
        let Ok((branch, directory, result)) = receiver.recv() else {
            break ("resumable", "framework_error: a session thread ended without a result".to_string());
        };
        running.remove(&branch);
        let summary = result.unwrap_or_else(|error| json!({"status":"framework_error","error":error}));
        if summary["status"] == "framework_error" {
            stop.get_or_insert(("resumable", format!("framework_error in {}: {}", directory.display(), summary["error"])));
        } else if summary["status"] == "accounting_unresolved" {
            stop.get_or_insert(("resumable", format!("accounting_unresolved in {}", directory.display())));
        } else if summary["calls"] == 0 && summary["reason"] != "budget_limit" {
            // A session that closed before any author call (for example a readiness refusal) would only be started
            // again the same way: stop for review instead of looping.
            stop.get_or_insert(("resumable", format!("session_without_call in {}: {}", directory.display(), summary["reason"])));
        }
        let after = (|| -> Result<bool, WorkloadError> {
            let record: SessionRecord = read_json(&directory.join(SESSION_FILE))?;
            VersionTree::read(&engine_dir)?.write_views(&engine_dir, &branches)?;
            Ok(options.render_only || pauses_after(engine.pause_after_session, &record))
        })();
        match after {
            Ok(true) => pause_after.push(directory),
            Ok(false) => {}
            Err(error) => fail(&mut stop, error),
        }
        crate::output::engine::general::write_general_output(request, &root, &engine_dir);
    };
    for thread in threads {
        let _ = thread.join();
    }
    let mut summary = general_summary(request, &root, &engine_dir, &branches, &spend, status, &reason, &pause_after, &ladder_note)?;
    if let Some(run) = &stage {
        let key = if run.form == WorkloadForm::Workloads { "workloads" } else { "stage" };
        summary[key] = super::stage::run_summary(run, &engine_dir);
    }
    publish_summary(&root, &summary)?;
    Ok(summary)
}

/// Whether the request names several workloads (`engine.stage` or `engine.workloads`; `engine::stage`).
pub(super) fn several_workloads(engine: &EngineRequest) -> bool {
    engine.stage.is_some() || engine.workloads.is_some()
}

/// The ladder's decision now ([`ladder_check`]) at the scale of `prepared` (the ladder's current scale).
fn driver_ladder_check(prepared: &PreparedEngine, tree: &VersionTree) -> Result<LadderDecision, AdmissionError> {
    let general = prepared.inputs.general.as_ref().ok_or_else(|| AdmissionError::tool("the ladder's check without general inputs"))?;
    Ok(ladder_check(general, tree))
}

/// A move to the scale of `next` (module documentation): the main-line head timed against every other branch head
/// there (the winner is the main-line head), or alone; every timed version's score and cells are recorded at the new
/// scale. Returns the move's record.
fn move_scale(request: &WorkloadRequest, next: &PreparedEngine, engine_dir: &Path, branches: &[String], tree: &VersionTree) -> Result<Value, AdmissionError> {
    let general = next.inputs.general.clone().ok_or_else(|| AdmissionError::tool("a scale move without general inputs"))?;
    let scale = general.scale.name.clone();
    let dir = engine_dir.join("scale-moves").join(&scale);
    fs::create_dir_all(&dir).map_err(AdmissionError::tool)?;
    let mut role = framework_role(request, next, engine_dir, &dir)?;
    let mut bench = role.view();
    let mut head = tree.main_line_head().unwrap_or(ROOT_VERSION).to_string();
    let rivals: BTreeSet<String> = branches.iter().filter_map(|b| tree.branch_head(b)).map(String::from).filter(|v| *v != head).collect();
    let mut timings = vec![];
    if rivals.is_empty() {
        let run = bench.admitted_runnable(&head, &dir.join(format!("{head}-storages")))?;
        let (matrix, scored) = bench.time_alone(&run, DEVELOPMENT.cell_calls, &dir.join(format!("{head}-timing")))?;
        let file = dir.join(format!("{head}-score.json"));
        write_json_atomic(&file, &json!(scored)).map_err(AdmissionError::tool)?;
        super::role::write_matrix(&matrix, &dir.join(format!("{head}-matrix.json")))?;
        record_scale_score(engine_dir, &head, &RecordedScore::of(&scale, &scored, &file), "scale_move").map_err(AdmissionError::tool)?;
        record_cells(engine_dir, &head, &scale, &scored)?;
        timings.push(json!({"version":head,"alone":true,"score":scored.score,"file":file}));
    }
    for rival in rivals {
        let parent = bench.admitted_runnable(&head, &dir.join(format!("{head}-storages")))?;
        let candidate = bench.admitted_runnable(&rival, &dir.join(format!("{rival}-storages")))?;
        let work = dir.join(format!("race-{head}-{rival}"));
        let report = bench.race_runnables(&parent, &candidate, None, DEVELOPMENT.cell_calls, &work).map_err(|e| AdmissionError::tool(format!("the scale move's timing of {head} and {rival}: {e}")))?;
        let file = dir.join(format!("race-{head}-{rival}.json"));
        write_json_atomic(&file, &json!(report)).map_err(AdmissionError::tool)?;
        for (version, scored) in [(&head, &report.parent_score), (&rival, &report.candidate_score)] {
            record_scale_score(engine_dir, version, &RecordedScore::of(&scale, scored, &file), "scale_move").map_err(AdmissionError::tool)?;
            record_cells(engine_dir, version, &scale, scored)?;
        }
        timings.push(json!({"parent":head,"candidate":rival,"candidate_better":report.candidate_better,"file":file}));
        if report.candidate_better {
            let _lock = main_line_lock(engine_dir)?;
            bench.select(&rival, &head, "scale_move", &scale, Some(&file), None)?;
            head = rival;
        }
    }
    // Every head now has its assets at the new scale: the superseded derived assets are released (`engine::asset_upkeep`).
    let released = super::asset_upkeep::release_pass(&request.library, engine_dir, &format!("scale move to {scale}"));
    Ok(json!({"to":scale,"at_unix_ms":now_unix_ms(),"main_line_head":head,"timings":timings,"directory":dir,"asset_release":released}))
}

/// Build the scheduled session of `plan` for slot `branch`: a new session's record is written before it starts; an
/// open one is resumed with its recorded request.
#[allow(clippy::too_many_arguments)]
fn build_session<A, F>(
    request: &WorkloadRequest,
    engine: &EngineRequest,
    prepared: &PreparedEngine,
    stage: Option<&StageRun>,
    first_scale: Option<&FirstScale>,
    engine_dir: &Path,
    branch: &str,
    plan: SlotPlan,
    spend: &RunSpend,
    options: GeneralRunOptions,
    authors: &mut F,
    sockets: &Path,
) -> Result<ScheduledSession<HostLeasedAuthor<A>, RetainedRole<EngineAuthorRole>>, WorkloadError>
where
    A: AuthorTransport + Send,
    F: FnMut(&str, &Path) -> Result<A, String>,
{
    let general = prepared.inputs.general.as_ref().ok_or_else(|| WorkloadError::invalid("engine: general inputs"))?;
    let (directory, record) = match plan {
        SlotPlan::Resume(directory) => {
            let record: SessionRecord = read_json(&directory.join(SESSION_FILE))?;
            (directory, record)
        }
        SlotPlan::Start { number, kind, seed, merge_from, previous } => {
            let directory = session_directory(engine_dir, branch, number);
            let task = json!({"role":"general_engine","branch":branch,"session":number,"kind":kind,"seed":seed,"merge_from":merge_from,"scale":general.scale.name,
                "threads":request.hardware.threads,"training_set":prepared.inputs.training.identity,"timing_binding":engine.timing_binding});
            let limits = session_limits(&engine.limits, spend.left()?, options.render_only);
            let record = SessionRecord { format_version: 1, branch: branch.into(), number, kind, seed, merge_from, scale: general.scale.name.clone(), previous,
                request: RunRequest { format_version: 1, task, limits, continue_from: None }, started_unix_ms: now_unix_ms() };
            records::create_dir(&directory)?;
            records::write_new_json(&directory.join(SESSION_FILE), &record)?;
            (directory, record)
        }
    };
    let label = format!("{}-session-{:04}", record.branch, record.number);
    let inspection = engine_dir.parent().unwrap_or(engine_dir).join("author-inspection").join(&label);
    let author = authors(&label, &inspection).map_err(|detail| WorkloadError::Controller(crate::controller::ControllerError::Author { stage: "session author", detail }))?;
    let author = HostLeasedAuthor::new(author, request.host_locks.clone());
    let bench = session_bench(request, prepared).map_err(framework_error)?;
    let config = EngineRoleConfig {
        engine_dir: engine_dir.to_path_buf(),
        inputs: prepared.inputs.clone(),
        mode: EngineRoleMode::Session(SessionConfig { record: record.clone(), directory: directory.clone(), spend: spend.clone(), prompt: options.prompt, first_scale: first_scale.cloned() }),
    };
    let mut role = EngineAuthorRole::new(bench, config);
    if let Some(run) = stage {
        role = role.with_stage(run.session_role(engine_dir));
    }
    let role = RetainedRole::start(role, &directory, sockets)?;
    Ok(ScheduledSession { directory, request: record.request, author, role, reselect_from: None, on_close: None })
}

/// A session's controls: no submission guard (the session ends by its own rules), the budget left over every
/// session, and the user's retries and call timeout. A render-only session makes one submission.
pub fn session_limits(engine: &Limits, left: Money, render_only: bool) -> Limits {
    Limits { max_iterations: if render_only { 1 } else { UNSET_COUNT }, max_cost_usd: left, ..engine.clone() }
}

/// The run summary of the general line: status and reason, the scale ladder, the main-line head and its milestone, each
/// branch, the versions and attempts, the spend, the library's bytes, and the pause.
#[allow(clippy::too_many_arguments)]
fn general_summary(request: &WorkloadRequest, root: &Path, engine_dir: &Path, branches: &[String], spend: &RunSpend, status: &str, reason: &str, paused_after: &[PathBuf], ladder: &Value) -> Result<Value, WorkloadError> {
    let tree = VersionTree::read(engine_dir)?;
    let state = LadderState::read(engine_dir)?;
    let engine = request.engine()?;
    let scale = &engine.scales[state.current].name;
    let head = tree.main_line_head();
    let head_score = head.and_then(|h| tree.score_at(h, scale));
    let now = spend.now()?;
    let mut rows = vec![];
    for branch in branches {
        let sessions = branch_sessions(engine_dir, branch)?;
        rows.push(json!({"branch":branch,"head":tree.branch_head(branch),"direction":super::acceptance::branch_direction(&tree, branch),
            "sessions":sessions.len(),"open_sessions":sessions.iter().filter(|s| s.open).count(),"evaluated":sessions.iter().map(|s| s.evaluated).sum::<u32>(),
            "versions":tree.of_branch(branch).filter(|n| n.accepted).count(),"attempts":tree.of_branch(branch).filter(|n| !n.accepted).count()}));
    }
    Ok(json!({"format_version":1,"line":"general","status":status,"reason":reason,"run":root,
        "scale":{"current":scale,"index":state.current,"ladder":engine.scales.iter().map(|s| &s.name).collect::<Vec<_>>(),"moves":state.moves,"last_check":ladder},
        "main_line_head":head,"main_line_score":head_score,
        "milestone":{"beats_both_at_current_scale":head_score.as_ref().is_some_and(|s| s.beats_both),"meaning":"every cell finished and every total below both baselines' totals at this scale: a milestone and a report, never a stop"},
        "branches":rows,"versions":tree.versions().map(|n| &n.id).collect::<Vec<_>>(),"attempts":tree.attempts().count(),
        "spend":{"known_provider_reported_cost_usd":now.spent,"reserved_usd":now.reserved,"complete":now.complete,"budget_usd":spend.budget,
            "scope":"provider-reported cost of every engine-agent call of every session, counted once per provider session from the session ledgers; framework work (version 0, timings, builds) is not included"},
        "library_bytes":library_bytes(&request.library).map_err(framework_error)?,
        "pause":if status == PAUSED { json!({"after_sessions":paused_after,"resume":"relaunch the same command (same request and run directory): open sessions resume and the slots continue from the records; engine.pause_after_session is not part of the run's identity, so the relaunch may switch it","meaning":"a review cadence, not a cap"}) } else { Value::Null },
        "records":{"tree":engine_dir.join("TREE.md"),"findings":engine_dir.join(tree::FINDINGS_MARKDOWN),"flags":engine_dir.join(tree::FLAGS_FILE),"ladder":engine_dir.join(LADDER_FILE)},
        "scope":"one verified general engine optimized from version 0 by branches in long sessions; every version and attempt is kept under engine/versions and engine/attempts"}))
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::score::{NormalizedTime, Score};
    use super::super::tree::NodeKind;
    use gendb_artifacts::ContentId;
    use gendb_artifacts::verus::VerusStorageUseV1;

    fn recorded(finished: usize, cells: usize) -> RecordedScore {
        RecordedScore { scale: "sf1".into(), score: Score { finished, normalized_time: NormalizedTime::from_billionths(1) }, cells, beats_both: false, record: PathBuf::new() }
    }

    fn node(id: &str, branch: &str, parents: &[&str], kind: NodeKind) -> TreeNode {
        TreeNode { format_version: 1, id: id.into(), accepted: true, kind, branch: branch.into(), parents: parents.iter().map(|p| p.to_string()).collect(), scale: "sf1".into(),
            score: Some(recorded(6, 6)), reason: None, session: None, iteration: None, direction: None, rationale: None, created_unix_ms: 1 }
    }

    fn session(number: u32, kind: SessionKind, open: bool) -> SessionView {
        let request = RunRequest { format_version: 1, task: json!({}), limits: crate::controller::limits::tests::limits(), continue_from: None };
        SessionView {
            record: SessionRecord { format_version: 1, branch: "b1".into(), number, kind, seed: "v000".into(), merge_from: None, scale: "sf1".into(), previous: None, request, started_unix_ms: 1 },
            directory: PathBuf::from(format!("/e/branches/b1/sessions/session-{number:04}")),
            open,
            summary: Value::Null,
            evaluated: 1,
        }
    }

    fn change(version: &str) -> MainLineChange {
        MainLineChange { version: version.into(), previous: None, reason: "r".into(), scale: "sf1".into(), race: None, adopted: None, selection: gendb_artifacts::ContentId::from_bytes([1; 32]), at_unix_ms: 1 }
    }

    /// Done-check 3 (merge-session seeding): a slot resumes its open session; a branch with gains the main line has not
    /// taken runs one merge session seeded from the main-line head (the branch head it merges named), then continues
    /// from its own head; staggered start and the review cadence follow the request.
    #[test]
    fn slots_resume_merge_once_then_continue() {
        let mut tree = VersionTree {
            nodes: vec![node("v000", "main", &[], NodeKind::FrameworkGenerated), node("v001", "b1", &["v000"], NodeKind::Branch), node("v002", "b2", &["v000"], NodeKind::Branch)],
            scale_scores: Default::default(),
            main_line: vec![change("v000"), change("v002")],
            workload_scores: Default::default(),
        };
        // No session yet: b1 starts its first branch session from its head... but its head v001 has gains: a merge is
        // due only after a session ended, and the first session of a fresh slot is planned the same way.
        let fresh = plan_slot(&tree, &[], "b3").unwrap();
        assert_eq!(fresh, SlotPlan::Start { number: 1, kind: SessionKind::Branch, seed: "v000".into(), merge_from: None, previous: None });
        assert_eq!(plan_slot(&tree, &[session(1, SessionKind::Branch, true)], "b1").unwrap(), SlotPlan::Resume(PathBuf::from("/e/branches/b1/sessions/session-0001")));
        let merge = plan_slot(&tree, &[session(1, SessionKind::Branch, false)], "b1").unwrap();
        assert_eq!(merge, SlotPlan::Start { number: 2, kind: SessionKind::Merge, seed: "v002".into(), merge_from: Some("v001".into()),
            previous: Some(PathBuf::from("/e/branches/b1/sessions/session-0001")) });
        let after_merge = plan_slot(&tree, &[session(1, SessionKind::Branch, false), session(2, SessionKind::Merge, false)], "b1").unwrap();
        assert!(matches!(after_merge, SlotPlan::Start { number: 3, kind: SessionKind::Branch, ref seed, .. } if seed == "v001"), "one merge session, then the branch continues: {after_merge:?}");
        // Once a merge took b1's gains, no merge is due.
        tree.nodes.push(node("v003", "main", &["v002", "v001"], NodeKind::Merge));
        tree.main_line.push(change("v003"));
        assert!(matches!(plan_slot(&tree, &[session(1, SessionKind::Branch, false)], "b1").unwrap(), SlotPlan::Start { kind: SessionKind::Branch, .. }));
        // Staggered start and cadence.
        assert!(may_start("b1", 0) && !may_start("b2", 0) && may_start("b3", 1));
        let first = session(1, SessionKind::Branch, false).record;
        let second = session(2, SessionKind::Branch, false).record;
        assert!(pauses_after(PauseCadence::FirstSessionOfEachBranch, &first) && !pauses_after(PauseCadence::FirstSessionOfEachBranch, &second));
        assert!(pauses_after(PauseCadence::EverySession, &second) && !pauses_after(PauseCadence::Never, &first));
        assert_eq!(branch_names(3), ["b1", "b2", "b3"]);
    }

    /// The ladder moves when the main-line head finishes every cell, the move to the last scale included (no storage
    /// condition); the last scale is never left.
    #[test]
    fn the_ladder_moves_on_all_finished_at_every_scale() {
        assert!(matches!(ladder_decision(0, 3, None), LadderDecision::Stay(_)));
        assert!(matches!(ladder_decision(0, 3, Some(&recorded(5, 6))), LadderDecision::Stay(ref r) if r.contains("5 of 6")));
        assert_eq!(ladder_decision(0, 3, Some(&recorded(6, 6))), LadderDecision::Move { next: 1 });
        assert!(matches!(ladder_decision(1, 3, Some(&recorded(5, 6))), LadderDecision::Stay(ref r) if r.contains("5 of 6")));
        assert_eq!(ladder_decision(1, 3, Some(&recorded(6, 6))), LadderDecision::Move { next: 2 }, "the move to the last scale has no budget condition");
        assert!(matches!(ladder_decision(2, 3, Some(&recorded(6, 6))), LadderDecision::Stay(ref r) if r.contains("last scale")));
        let limits = session_limits(&crate::controller::limits::tests::limits(), Money::parse("7").unwrap(), false);
        assert_eq!((limits.max_iterations, limits.max_cost_usd), (UNSET_COUNT, Money::parse("7").unwrap()));
        assert_eq!(session_limits(&limits, Money(1), true).max_iterations, 1);
    }

    /// The general inputs of scale `index` of the ladder `sf1`, `sf10`, `sf100` with `branches` slots: the request's
    /// original data size is 1,000 bytes times the scale's factor, the plain storage's 1,400 bytes times it, and the
    /// plain storages are the packages `1` and `2`.
    fn general(index: usize, branches: u32) -> GeneralInputs {
        let names = ["sf1", "sf10", "sf100"];
        let factor = 10u64.pow(index as u32);
        let scale = serde_json::from_value(json!({"name":names[index],"locations":{},"prepared_workload":"/p","bindings":"/b","targets":"/t","saved_answers":[],
            "original_data_bytes":1_000 * factor,"original_data_record":"/g.json"})).unwrap();
        GeneralInputs { scale, plain_storages: BTreeSet::from([package(1), package(2)]), plain_storage_bytes: 1_400 * factor, scale_index: index, scales: 3,
            next_scale: names.get(index + 1).map(|n| n.to_string()), call_limits: gendb_runtime::worker::CallLimits::GENERAL_ENGINE, branches: branch_names(branches),
            budget_usd: Money::parse("1000").unwrap(), emphasis: None, seed: None }
    }

    fn package(byte: u8) -> ContentId {
        ContentId::from_bytes([byte; 32])
    }

    /// The budget rule at a lower scale and at the last scale: a version reading only the plain
    /// storages is allowed above the original data size; a version with changed storage (a use that is not plain, or a
    /// new storage) is accepted within the scale's original data size and at it, and refused over it.
    #[test]
    fn plain_storage_is_allowed_as_is_and_changed_storage_is_bounded_by_the_original_data_size_at_every_scale() {
        let uses = |packages: &[u8]| -> Vec<VerusStorageUseV1> { packages.iter().map(|b| VerusStorageUseV1 { name: format!("s{b}"), package: package(*b) }).collect() };
        for (index, original) in [(0, 1_000u64), (2, 100_000)] {
            let rule = general(index, 1).budget_rule();
            let scale = ["sf1", "sf10", "sf100"][index];
            assert_eq!(rule, crate::storage::engine_library::BudgetRule::OriginalDataSize { original_data_bytes: original, scale: scale.into(), plain_storages: BTreeSet::from([package(1), package(2)]) });
            let plain_size = 1_400 * 10u64.pow(index as u32);
            assert!(rule.decide(&uses(&[1, 2]), 0, plain_size).unwrap().starts_with(&format!("plain storage only at {scale}")), "plain only over the original size: accepted at {scale}");
            assert!(rule.decide(&uses(&[1, 3]), 0, original - 1).is_ok() && rule.decide(&uses(&[1, 3]), 0, original).is_ok(), "changed storage within and at the original size at {scale}");
            assert!(rule.decide(&uses(&[1, 3]), 0, original + 1).unwrap_err().contains(&format!("exceed the original data size at {scale}, {original} bytes, by 1 bytes")), "changed storage over at {scale}");
            assert!(rule.decide(&uses(&[1, 2]), 1, original + 1).is_err(), "a new storage is a storage change at {scale}");
        }
    }

    /// Rule 1 of the scale move: an evaluation over a tree whose main-line head finishes every cell at the
    /// session's scale finds the move due and names it for the session end (`sessions::session_end`), the move to the
    /// last scale included.
    #[test]
    fn an_evaluation_finds_the_move_due_when_the_head_finishes_every_cell() {
        let mut tree = VersionTree { nodes: vec![node("v000", "main", &[], NodeKind::FrameworkGenerated)], scale_scores: Default::default(), main_line: vec![change("v000")], workload_scores: Default::default() };
        tree.nodes[0].score = Some(recorded(5, 6));
        let stay = ladder_check(&general(0, 1), &tree);
        assert!(matches!(stay, LadderDecision::Stay(ref r) if r.contains("5 of 6")) && due_scale_move(&general(0, 1), &stay).is_none(), "{stay:?}");
        tree.nodes[0].score = Some(recorded(6, 6));
        let one_line = general(0, 1);
        let moving = ladder_check(&one_line, &tree);
        assert_eq!(moving, LadderDecision::Move { next: 1 });
        assert_eq!(due_scale_move(&one_line, &moving), Some(DueScaleMove { head: "head", from: "sf1", to: "sf10" }));
        assert_eq!(due_scale_move(&general(0, 3), &moving).map(|m| m.head), Some("main-line head"), "several branches name the main-line head");
        // At sf10 the move to the last scale follows the same rule.
        assert!(matches!(ladder_check(&general(1, 1), &tree), LadderDecision::Stay(ref r) if r.contains("no score at this scale")));
        let mut sf10 = recorded(6, 6);
        sf10.scale = "sf10".into();
        tree.scale_scores.insert(("v000".into(), "sf10".into()), sf10);
        let moving = ladder_check(&general(1, 1), &tree);
        assert_eq!(due_scale_move(&general(1, 1), &moving), Some(DueScaleMove { head: "head", from: "sf10", to: "sf100" }));
    }

    /// Rule 2 of the scale move: while the move is due, a slot's open session resumes (after a relaunch it
    /// is the session the move waits for) and only a new session waits; without a due move every plan runs.
    #[test]
    fn a_due_move_lets_an_open_session_resume_and_holds_new_ones() {
        let tree = VersionTree { nodes: vec![node("v000", "main", &[], NodeKind::FrameworkGenerated)], scale_scores: Default::default(), main_line: vec![change("v000")], workload_scores: Default::default() };
        let open = plan_slot(&tree, &[session(1, SessionKind::Branch, false), session(2, SessionKind::Branch, true)], "b1").unwrap();
        assert!(matches!(open, SlotPlan::Resume(_)) && starts_now(&open, true), "the open session resumes while the move is due: {open:?}");
        let next = plan_slot(&tree, &[session(1, SessionKind::Branch, false)], "b1").unwrap();
        assert!(matches!(next, SlotPlan::Start { number: 2, .. }) && !starts_now(&next, true), "a new session waits for the move: {next:?}");
        assert!(starts_now(&next, false) && starts_now(&open, false));
    }
}
