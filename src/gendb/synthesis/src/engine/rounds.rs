//! The engine run: rounds and versions. `gendb engine synthesize REQUEST
//! RUN_DIR` runs it ([`synthesize_engine`]); `gendb engine render-inputs REQUEST OUT_DIR` renders the first call's inputs
//! of one round without a provider ([`render_engine_inputs`]).
//!
//! A general-line request (`engine.line: "general"`) runs through `engine::branches` instead: the same commands, plus
//! `gendb engine prepare REQUEST RUN_DIR` (version 0 without an author) and `gendb engine final-evaluation REQUEST RUN_DIR
//! VERSION [SCALE]` (the full protocol of one version, `engine::final_evaluation`); its inputs are prepared per scale
//! ([`prepare_engine_scale`]) by the same preparation as a round's ([`prepare_engine`]). A run of several workloads'
//! inputs (`engine.stage` or `engine.workloads`, [`prepare_stage_inputs`]) are every workload's, each at its last scale
//! (and its first, for its variants), with one rule set over every workload. `gendb engine export RUN_DIR VERSION OUT`
//! (`engine::export`) writes one version's engine source; `gendb engine check-request REQUEST` ([`check_request`])
//! checks every workload of a general-line request at every scale without running anything. Everything below describes
//! the schema line.
//!
//! Phases ([`run_engine`]):
//! 1. request: read and validated (the engine section's rules, `controller::request`), the run directory's route
//!    (`engine`) and immutable request;
//! 2. inputs, once per controller process ([`prepare_engine`]): the training set (templates, visible bindings, frozen
//!    variants) and the saved baselines; the seeded storages must be admitted in the engine library; the templates
//!    through the ordinary data preparation and preflight (`facts::preparation_request`, root `<run>/preparation`);
//!    their encoded statements (`facts::EncodedStatements`, reused across restarts) and the training facts;
//! 3. rounds, until a stop: each round is one author session (`controller::run`, scheduled by
//!    `controller::schedule`) with the engine role (`engine::role`). Its seed ([`next_seed`]) is the latest version,
//!    else the previous round's workspace, else an empty engine crate, with every earlier version copied read-only and
//!    the notes carried. Its request (`round.json`, written before the session starts) gives the round one submission
//!    and the cost left under the user's guard. An accepted submission becomes the next version ([`write_version`];
//!    the round's receipts are added when it closes); a round without one is recorded as an attempt and its workspace
//!    stays where it is;
//! 4. the stop: the latest version's official totals meet the stop rule (`target_met`), the user's rounds guard
//!    (`round_limit`) or cost guard (`budget_limit`). A framework error or unresolved accounting of a round stops the run
//!    resumably (`resumable`): a restart continues that round from its records, never replaying a paid call. An eligible
//!    submission whose admission failed in the framework stops the run for review (`qualification_framework_failure`).
//!    With `engine.pause_after_round` the run also pauses after every closed round that did not meet a stop (`paused`,
//!    reason `paused_for_review`, the summary's `pause` record): a review cadence, not a cap; relaunching the same
//!    command starts the next round;
//! 5. the run summary (`<run>/summary[-N].json`, `summary-latest.json`) after every round and, with an output home,
//!    the readable engine folders (`output::engine`).
//!
//! Records under `<run>/engine/`: `statements.json`; `rounds/round-NNNN/` (`round.json`, `seed.json`, the session's
//! ledger, calls, iterations, resolution and summary, and its workspace `author/`); `versions/vNNN/` (every version,
//! complete: `version.json`, `README.md`, `code/` and `code-view/`, `manifest.json`, `seed-manifest.json`, `NOTES.md`,
//! `admission.json`, `evaluation.json`, `timing.json`, `totals.json`, the official, qualification and variant cells, `variants.md`,
//! the other bindings' matrices when measured, and `receipts.json`). The state is always read from these records
//! ([`EngineState::read`]).
//!
//! Long runs: an engine run lasts many hours. Launch it detached with a wrapper
//! (`setsid <launcher> REQUEST RUN_DIR GENDB` writing `RUN_DIR.{pid,start,log,exit,end}`). Nothing
//! here bounds the run's time: only the user's rounds and cost guards and each call's own `author_timeout_seconds`
//! apply. Provider-reported costs are authoritative and counted once per session, from each round's summary.
//!
//! Relaunching with a newer `gendb` build (framework fixes between rounds) is supported: every controller process
//! prepares its inputs again (statements, preflight checks reused only while their evidence identity is current, the
//! encoded statements, the training facts) and each round renders its contract with the running build. Earlier rounds
//! and versions are records and are not rebuilt; the next submission is frozen and admitted against the new framework.
//! Two conditions: the request must serialize to the same `request.json` (a new request field must be skipped when
//! absent), and the framework files a storage crate carries (SQLSpec, `gendb_abi.rs`, the storage entries and their
//! generated files) must stay byte-identical, or every seeded storage becomes stale and its re-verification rebuilds its
//! asset.

use super::branches::{GeneralRunOptions, prepare_general_run, run_general_engine};
use super::facts::{CheckSources, EncodedStatements, EngineChecks, TrainingSet, preparation_request, training_facts};
use super::role::{EngineAuthorRole, EngineInputs, EngineRoleConfig, EngineRoleMode, FirstScale, GeneralInputs, RoundConfig, copy_tree};
use super::submission::{EngineManifest, FrozenEngine};
use super::totals::Baselines;
use crate::controller::author::AuthorTransport;
use crate::controller::crash_dumps;
use crate::controller::hardware::observe_host;
use crate::controller::layout::{NOTES_FILE, RunLayout};
use crate::controller::limits::{Limits, Money, UNSET_COUNT};
use crate::controller::records::{self, RecordError};
use crate::controller::request::{MemberRole, Seed, WorkloadForm, WorkloadRequest, WorkloadSet};
use crate::controller::run::RunRequest;
use crate::controller::schedule::{ScheduledSession, run_sessions};
use crate::controller::session::RetainedRole;
use crate::controller::workload_run::WorkloadError;
use crate::controller::workload_run::authors::{HostLeasedAuthor, LOCAL_TOOL_SERVER_WORDS};
use crate::controller::workload_run::lifecycle::{Route, publish_summary, record_request, record_route};
use crate::controller::workload_run::preparation::{PreparedData, PreparedQuery, prepare_workload};
use crate::controller::workload_run::render::RenderAuthor;
use crate::controller::workload_run::sessions::socket_directory;
use crate::providers::claude_code::declared_usage_scope;
use crate::providers::{ClaudeCode, LocalToolServer};
use crate::query::QuerySession;
use crate::storage::catalog;
use crate::storage::engine_library::plain_storage_bytes;
use crate::tools::bench::{BenchConfig, Workbench};
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_frontend::parser::SqlParser;
use gendb_verification::admission::{AdmissionError, ValidationPolicy};
use gendb_runtime::worker::CallLimits;
use gendb_storage::versions::CurrentCapture;
use gendb_verification::verus::engine_rules::{EngineRuleSet, StageWorkload, TemplateConstants};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::Arc;

/// The engine directory of a run.
pub fn engine_directory(run: &Path) -> PathBuf {
    run.join("engine")
}

/// The session directory of round `round`.
pub fn round_directory(engine_dir: &Path, round: u32) -> PathBuf {
    engine_dir.join("rounds").join(format!("round-{round:04}"))
}

/// The folder of version `number` (`v001`).
pub fn version_directory(engine_dir: &Path, number: u32) -> PathBuf {
    engine_dir.join("versions").join(format!("v{number:03}"))
}

/// The readable name of version `number` (`v1`).
pub fn version_name(number: u32) -> String {
    format!("v{number}")
}

/// Where a round's workspace comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SeedKind {
    /// No version and no earlier round: an empty engine crate over the seeded storages.
    Empty,
    /// The latest version's sources, manifest and notes.
    Version,
    /// No version yet: the previous round's workspace (its author files and notes).
    PreviousRound,
}

/// The seed of one round's workspace (`engine::role::seed_workspace`), recorded in `round.json`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RoundSeed {
    pub kind: SeedKind,
    /// What the author reads (`v2 (round 3)`, `round 1's workspace (no version yet)`, `an empty engine crate`).
    pub description: String,
    /// The seeding version's name, when the seed is a version.
    pub version: Option<String>,
    /// The version folder or the previous round's workspace.
    pub from: Option<PathBuf>,
    /// The `NOTES.md` carried into the round.
    pub notes: Option<PathBuf>,
    /// Every earlier version `(name, folder)`, copied read-only into the workspace.
    pub versions: Vec<(String, PathBuf)>,
}

/// `round.json`: one round's identity, written before its session starts and read back by a restart.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct RoundRecord {
    pub format_version: u32,
    pub round: u32,
    pub seed: RoundSeed,
    /// The version an accepted submission of this round becomes.
    pub next_version: u32,
    /// The session's request (its ledger identity).
    pub request: RunRequest,
    pub started_unix_ms: u64,
}

/// The engine run's state, read from its records.
pub struct EngineState {
    /// Every version's `version.json`, oldest first.
    pub versions: Vec<Value>,
    /// Every round's view (`round_view`), in order.
    pub rounds: Vec<Value>,
}

impl EngineState {
    /// Read the versions and rounds under `engine_dir`.
    pub fn read(engine_dir: &Path) -> Result<Self, RecordError> {
        let mut versions = vec![];
        for dir in sorted_children(&engine_dir.join("versions"), "v") {
            let path = dir.join("version.json");
            if path.is_file() {
                versions.push(records::read_json(&path)?);
            }
        }
        let mut rounds = vec![];
        for dir in sorted_children(&engine_dir.join("rounds"), "round-") {
            if dir.join("round.json").is_file() {
                rounds.push(round_view(&dir)?);
            }
        }
        Ok(Self { versions, rounds })
    }

    /// The latest version's record.
    pub fn latest_version(&self) -> Option<&Value> {
        self.versions.last()
    }

    /// The round whose session has not closed (a restart resumes it).
    pub fn open_round(&self) -> Option<&Value> {
        self.rounds.iter().find(|r| r["outcome"] == "open")
    }

    /// The provider-reported cost of every round, known so far, and whether every round's cost is complete.
    pub fn spent(&self) -> (Money, bool) {
        let mut total = Money::default();
        let mut complete = true;
        for round in &self.rounds {
            match round["known_reported_cost_usd"].as_str().and_then(|t| Money::parse(t).ok()).map(|known| total.checked_sum(known)) {
                Some(Ok(sum)) => total = sum,
                _ => complete = false,
            }
            complete &= round["cost_complete"] == true;
        }
        (total, complete)
    }

    /// What authors read about earlier versions and rounds (`context.engine.versions` and `.rounds`): the closed rounds
    /// only.
    pub fn author_view(&self) -> Value {
        json!({"versions":self.versions,"rounds":self.rounds.iter().filter(|r| r["outcome"] != "open").collect::<Vec<_>>()})
    }
}

/// The subdirectories of `dir` whose names start with `prefix`, sorted by name.
fn sorted_children(dir: &Path, prefix: &str) -> Vec<PathBuf> {
    let mut found: Vec<PathBuf> = fs::read_dir(dir)
        .into_iter()
        .flatten()
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.is_dir() && p.file_name().and_then(|n| n.to_str()).is_some_and(|n| n.starts_with(prefix)))
        .collect();
    found.sort();
    found
}

/// One round as the facts and the summary show it: its seed, whether it is open, accepted a version or was an attempt,
/// its submission's status and error, its workspace, records and provider-reported cost.
fn round_view(dir: &Path) -> Result<Value, RecordError> {
    let record: RoundRecord = records::read_json(&dir.join("round.json"))?;
    let layout = RunLayout::new(dir);
    let summary: Value = if layout.summary().is_file() { records::read_json(&layout.summary())? } else { Value::Null };
    // A session is open until its summary exists with complete accounting (`controller::run`: `accounting_unresolved`
    // summaries stay resumable); every other summary closed it.
    let closed = summary.is_object() && summary["status"] != "accounting_unresolved";
    let resolution: Value = if layout.resolution().is_file() { records::read_json(&layout.resolution())? } else { Value::Null };
    let iteration = resolution["iteration"].as_u64().map(|i| i as u32);
    let evaluation: Value = iteration
        .map(|i| layout.evaluation(i))
        .filter(|p| p.is_file())
        .map(|p| records::read_json(&p))
        .transpose()?
        .unwrap_or(Value::Null);
    let outcome = match (closed, resolution["status"].as_str()) {
        (false, _) => "open",
        (true, Some("version_accepted")) => "version",
        (true, _) => "attempt",
    };
    let status = match outcome {
        "version" => json!("version_accepted"),
        _ if !evaluation["status"].is_null() => evaluation["status"].clone(),
        _ => json!(format!("no evaluated submission ({})", summary["reason"].as_str().unwrap_or("open"))),
    };
    Ok(json!({"round":record.round,"directory":dir,"seed":record.seed.description,"outcome":outcome,
        "version":resolution["version"].as_u64().map(|n| version_name(n as u32)),"status":status,"reason":summary["reason"],
        "failure_class":evaluation["failure_class"],"error":evaluation["error"],"qualification_error":resolution["qualification_error"],
        "evaluation_record":iteration.map(|i| layout.evaluation(i)),"workspace":layout.workspace(),
        "reported_cost_usd":summary["reported_cost_usd"],"known_reported_cost_usd":summary["known_reported_cost_usd"],"cost_complete":summary["cost_complete"],
        "calls":summary["calls"],"tokens":summary.pointer("/accounting/tokens"),"author_elapsed_ms":summary["author_elapsed_ms"]}))
}

/// The seed of round `round` (module documentation): the latest version, else the previous round's workspace, else an
/// empty engine crate; with every earlier version.
pub fn next_seed(state: &EngineState, engine_dir: &Path, round: u32) -> RoundSeed {
    let versions: Vec<(String, PathBuf)> = state
        .versions
        .iter()
        .filter_map(|v| Some((v["version"].as_str()?.to_string(), PathBuf::from(v["directory"].as_str()?))))
        .collect();
    if let Some(latest) = state.latest_version() {
        let directory = PathBuf::from(latest["directory"].as_str().unwrap_or_default());
        let name = latest["version"].as_str().unwrap_or("-").to_string();
        return RoundSeed {
            kind: SeedKind::Version,
            description: format!("{name} (round {})", latest["round"]),
            version: Some(name),
            notes: Some(directory.join(NOTES_FILE)),
            from: Some(directory),
            versions,
        };
    }
    if round > 1 {
        let workspace = RunLayout::new(&round_directory(engine_dir, round - 1)).workspace();
        return RoundSeed {
            kind: SeedKind::PreviousRound,
            description: format!("round {}'s workspace (no version yet)", round - 1),
            version: None,
            notes: Some(workspace.join(NOTES_FILE)),
            from: Some(workspace),
            versions,
        };
    }
    RoundSeed { kind: SeedKind::Empty, description: "an empty engine crate".into(), version: None, from: None, notes: None, versions }
}

/// The controls of one round's session: one submission, the provider cost left under the user's guard (`spent` so far),
/// and the user's retries and per-call timeout.
pub fn round_limits(engine: &Limits, spent: Money) -> Limits {
    let left = engine.max_cost_usd.remaining_after(spent);
    Limits { max_iterations: 1, max_cost_usd: if left.0 == 0 { Money(1) } else { left }, ..engine.clone() }
}

/// Why no further round starts (`None`: another round may start).
fn stop_reason(state: &EngineState, engine: &Limits) -> Option<&'static str> {
    if state.latest_version().is_some_and(|v| v["totals"]["stop"]["stop"] == true) {
        return Some("target_met");
    }
    if engine.max_iterations != UNSET_COUNT && state.rounds.len() as u64 >= u64::from(engine.max_iterations) {
        return Some("round_limit");
    }
    let (spent, _) = state.spent();
    if !engine.max_cost_usd.is_unset() && spent >= engine.max_cost_usd {
        return Some("budget_limit");
    }
    None
}

// ------------------------------------------------------------------------------------------------ versions

/// What [`write_version`] records.
pub struct VersionWrite<'a> {
    pub engine_dir: &'a Path,
    pub version: u32,
    pub round: u32,
    pub frozen_dir: &'a Path,
    pub engine: &'a FrozenEngine,
    /// The storage uses as admitted packages, in `Stores` order.
    pub uses: &'a [(String, ContentId)],
    /// The gating evaluation (build, storage, qualification, variant matrix).
    pub evaluation: &'a Value,
    /// The admission's library record (`admission::engine::EngineAdmission::record`).
    pub admission: &'a Value,
    /// The official timing of the admitted version (`engine::role`: matrix, totals, stop, variant ratios, other
    /// bindings, or the timing's failure).
    pub timing: &'a Value,
    pub training: &'a Value,
}

/// Write the complete folder of an accepted version (`versions/vNNN/`, module documentation), built beside it and
/// renamed into place; returns it. A folder of the same round's version is kept (a resumed qualification); a version
/// number taken by another round is a framework error.
pub fn write_version(w: &VersionWrite<'_>) -> Result<PathBuf, AdmissionError> {
    let target = version_directory(w.engine_dir, w.version);
    if target.join("version.json").is_file() {
        let existing: Value = records::read_json(&target.join("version.json")).map_err(AdmissionError::tool)?;
        if existing["round"] == w.round {
            return Ok(target);
        }
        return Err(AdmissionError::tool(format!("{} already holds round {}'s version", target.display(), existing["round"])));
    }
    let parent = target.parent().ok_or_else(|| AdmissionError::tool("version folder without parent"))?;
    fs::create_dir_all(parent).map_err(AdmissionError::tool)?;
    let staging = parent.join(format!(".staging-v{:03}-{}", w.version, records::now_unix_ms()));
    fs::create_dir(&staging).map_err(AdmissionError::tool)?;
    let crate_src = w.frozen_dir.join("crate/src");
    copy_tree(&crate_src.join("agent"), &staging.join("code/agent"), false)?;
    if w.frozen_dir.join("storages").is_dir() {
        copy_tree(&w.frozen_dir.join("storages"), &staging.join("code/storages"), false)?;
    }
    for file in w.engine.author_files.iter().filter(|f| f.starts_with("agent/") && f.ends_with(".rs")) {
        let text = fs::read_to_string(crate_src.join(file)).map_err(AdmissionError::tool)?;
        write_text(&staging.join("code-view").join(format!("{file}.md")), &crate::output::code_view(&text))?;
    }
    let manifest: EngineManifest = records::read_json(&w.frozen_dir.join("manifest.json")).map_err(AdmissionError::tool)?;
    write_json(&staging.join("manifest.json"), &json!(manifest))?;
    let seed_manifest = EngineManifest {
        crate_dir: super::submission::CRATE_DIRECTORY.into(),
        storage_uses: w.uses.iter().map(|(name, package)| crate::query::candidate::StorageUseDeclaration::admitted(name, *package)).collect(),
        ..manifest
    };
    write_json(&staging.join("seed-manifest.json"), &json!(seed_manifest))?;
    let notes = w.frozen_dir.parent().map(|iteration| iteration.join(NOTES_FILE)).filter(|p| p.is_file());
    if let Some(notes) = &notes {
        fs::copy(notes, staging.join(NOTES_FILE)).map_err(AdmissionError::tool)?;
    }
    let (e, t) = (w.evaluation, w.timing);
    write_json(&staging.join("evaluation.json"), e)?;
    write_json(&staging.join("timing.json"), t)?;
    write_json(&staging.join("admission.json"), &json!({"admission":w.admission,"build":e["build"],"verus":e["verus"],"qualification":e["qualification"],
        "storage":e["storage"],"frozen":w.engine}))?;
    write_json(&staging.join("totals.json"), &t["totals"])?;
    for (record, key, name) in [(e, "/variants/matrix/file", "variant-matrix.json"), (e, "/qualification/file", "qualification-cells.json"),
        (t, "/official/file", "official-matrix.json"), (t, "/variants/ratios/file", "variant-ratios.json")]
    {
        if let Some(source) = record.pointer(key).and_then(Value::as_str).map(Path::new).filter(|p| p.is_file()) {
            fs::copy(source, staging.join(name)).map_err(AdmissionError::tool)?;
        }
    }
    for other in t["other_bindings"].as_array().into_iter().flatten() {
        if let Some(source) = other.pointer("/matrix/file").and_then(Value::as_str).map(Path::new).filter(|p| p.is_file()) {
            fs::copy(source, staging.join(format!("binding-{}-matrix.json", other["binding"].as_str().unwrap_or("-")))).map_err(AdmissionError::tool)?;
        }
    }
    let name = version_name(w.version);
    write_text(&staging.join("variants.md"), &variants_markdown(&name, e, t))?;
    let record = json!({"format_version":1,"version":name,"number":w.version,"round":w.round,"directory":target,"created_unix_ms":records::now_unix_ms(),
        "crate_version":e["crate_version"],"entry_identity":w.engine.entry_identity,"toolkit_digest":w.engine.toolkit_digest,
        "frozen_crate":w.frozen_dir.join("crate"),"uses":w.uses.iter().map(|(n, p)| json!({"name":n,"package":p})).collect::<Vec<_>>(),
        "timing":{"status":t["status"],"failed_cells":t["failed_cells"],"class":t["class"],"error":t["error"],"timing_ns":t["timing_ns"]},
        "totals":t["totals"],"stop":t["stop"],
        "variants":{"summary":t["variants"]["ratios"]["summary"],"report":target.join("variants.md"),"timed":e["variants"]["timed"],"not_timed":e["variants"]["not_timed"]},
        "other_bindings":t["other_bindings"].as_array().into_iter().flatten().map(|o| json!({"binding":o["binding"],"totals":o["totals"]})).collect::<Vec<_>>(),
        "admission":w.admission,"evaluation_record":e["record"],"notes":notes.as_ref().map(|_| target.join(NOTES_FILE))});
    write_json(&staging.join("version.json"), &record)?;
    write_text(&staging.join("README.md"), &version_readme(&record, w.training))?;
    fs::rename(&staging, &target).map_err(AdmissionError::tool)?;
    Ok(target)
}

fn write_text(path: &Path, text: &str) -> Result<(), AdmissionError> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(AdmissionError::tool)?;
    }
    fs::write(path, text).map_err(AdmissionError::tool)
}

fn write_json(path: &Path, value: &Value) -> Result<(), AdmissionError> {
    write_text(path, &format!("{}\n", serde_json::to_string_pretty(value).map_err(AdmissionError::tool)?))
}

fn ms(ns: &Value) -> String {
    ns.as_f64().map_or("-".to_string(), |ns| format!("{:.3}", ns / 1e6))
}

/// `variants.md` of a version: every timed variant's hot call (the gating evaluation) against its template's official
/// median (the timing).
fn variants_markdown(name: &str, evaluation: &Value, timing: &Value) -> String {
    let mut out = format!("# Variants of {name}\n\nEvery timed variant at {} workers (1 warm + 1 hot call; each returned its template's saved answers before admission) against its template's official median: a report, never a bound. {} variants were not timed (AST bytes equal to their template's or another variant's).\n\n| Variant | Template | Kind | Variant ms | Template ms | Ratio |\n|---|---|---|---:|---:|---:|\n",
        evaluation["variants"]["workers"], evaluation["variants"]["not_timed"]);
    let rows = timing["variants"]["ratios"]["file"].as_str().and_then(|f| fs::read_to_string(f).ok()).and_then(|t| serde_json::from_str::<Value>(&t).ok());
    for row in rows.as_ref().and_then(|r| r["rows"].as_array()).into_iter().flatten() {
        out.push_str(&format!("| {} | {} | {} | {} | {} | {:.2} |\n", row["variant"]["id"].as_str().unwrap_or("-"), row["template"].as_str().unwrap_or("-"),
            row["variant"]["kind"].as_str().unwrap_or("-"), ms(&row["variant_hot_ns"]), ms(&row["template_median_ns"]), row["ratio"].as_f64().unwrap_or(0.0)));
    }
    let unmatched: Vec<&str> = rows.as_ref().and_then(|r| r["without_template"].as_array()).into_iter().flatten().filter_map(Value::as_str).collect();
    if !unmatched.is_empty() {
        out.push_str(&format!("\nNot compared (the official matrix has no median at that worker count): {}.\n", unmatched.join("; ")));
    }
    out
}

/// `README.md` of a version: its totals against the baselines, the stop, the per-template medians, variants and other
/// bindings, and where every record is.
fn version_readme(record: &Value, training: &Value) -> String {
    let name = record["version"].as_str().unwrap_or("-");
    let mut out = format!("# Engine version {name}\n\nAccepted in round {}; crate {}. Every file of this folder is GenDB's record; `code/` holds the author's sources (code and proofs), `code-view/` their reading view, `NOTES.md` the author's notes at submission.\n\n## Totals ({})\n\n| Workers | Engine ms | Umbra ms | DuckDB ms | Margin | Below both |\n|---:|---:|---:|---:|---:|---|\n",
        record["round"], record["crate_version"].as_str().unwrap_or("-"), record["totals"]["binding"].as_str().unwrap_or("-"));
    for w in record["totals"]["workers"].as_array().into_iter().flatten() {
        out.push_str(&format!("| {} | {} | {} | {} | {} | {} |\n", w["workers"], ms(&w["engine_ns"]), ms(&w["umbra_ns"]), ms(&w["duckdb_ns"]),
            w["margin"].as_f64().map_or("-".to_string(), |m| format!("{m:.3}x")), if w["below_both"] == true { "yes" } else { "no" }));
    }
    if record["timing"]["status"] != "timed" {
        out.push_str(&format!("\nOfficial timing: {} ({} failed cells{}); a worker count with a failed cell has no total.\n", record["timing"]["status"].as_str().unwrap_or("-"),
            record["timing"]["failed_cells"].as_u64().unwrap_or(0), record["timing"]["error"].as_str().map_or(String::new(), |e| format!("; {e}"))));
    }
    out.push_str(&format!("\nStop: {}.\n", if record["stop"]["stop"] == true { "met".to_string() } else {
        format!("not met ({})", record["stop"]["reasons"].as_array().into_iter().flatten().filter_map(Value::as_str).collect::<Vec<_>>().join("; ")) }));
    for other in record["other_bindings"].as_array().into_iter().flatten() {
        let totals: Vec<String> = other["totals"]["workers"].as_array().into_iter().flatten().map(|w| format!("{} workers {} ms", w["workers"], ms(&w["engine_ns"]))).collect();
        out.push_str(&format!("\nBinding {}: {} (reported, never a stop condition).\n", other["binding"].as_str().unwrap_or("-"), totals.join(", ")));
    }
    let versions = [record.clone()];
    let per_template = crate::prompts::engine_contract::versions_markdown(&versions, training);
    out.push_str(&format!("\n## Per template\n{}", per_template.split_once("\n## ").map_or(String::new(), |(_, rest)| format!("\n## {rest}"))));
    out.push_str("\nRecords: `version.json`, `evaluation.json` (the gating evaluation), `admission.json`, `timing.json` (the official timing after admission), `totals.json`, `official-matrix.json`, `qualification-cells.json`, `variant-matrix.json`, `variant-ratios.json`, `variants.md`, `receipts.json` (the round's provider-reported cost and time, added when the round closed).\n");
    out
}

/// Add the round's receipts (provider-reported cost, tokens, calls, author time, the ledger) to its version's folder.
fn record_version_receipts(version_dir: &Path, round: &Value) -> Result<(), RecordError> {
    let path = version_dir.join("receipts.json");
    let receipts = json!({"format_version":1,"round":round["round"],"reported_cost_usd":round["reported_cost_usd"],"known_reported_cost_usd":round["known_reported_cost_usd"],
        "cost_complete":round["cost_complete"],"calls":round["calls"],"tokens":round["tokens"],"author_elapsed_ms":round["author_elapsed_ms"],
        "ledger":RunLayout::new(Path::new(round["directory"].as_str().unwrap_or_default())).ledger(),
        "authority":"provider-reported, counted once from the round session's summary; every call's raw receipt is in the round's calls/"});
    records::write_json_atomic(&path, &receipts)
}

// ------------------------------------------------------------------------------------------------ the run

/// The engine run's inputs and the session bench's shared state, prepared once per controller process.
pub struct PreparedEngine {
    pub inputs: Arc<EngineInputs>,
    pub data: PreparedData,
}

/// Phase 2 (module documentation): the training set, the baselines, the engine library's seed, the templates'
/// preparation and preflight, their encoded statements and the training facts. The schema line's inputs: the engine
/// section's bindings and baselines, preparation under `<run>/preparation`, statements under `<run>/engine`.
pub async fn prepare_engine(request: &WorkloadRequest, root: &Path, parser: &SqlParser, framework_executable: &Path) -> Result<PreparedEngine, WorkloadError> {
    let engine = request.engine()?;
    let invalid = |e: &str| WorkloadError::invalid(format!("engine: {e}"));
    let bindings = engine.bindings.as_ref().ok_or_else(|| invalid("the schema line names engine.bindings"))?;
    let targets = engine.targets.as_ref().ok_or_else(|| invalid("the schema line names engine.targets"))?;
    let sources = InputSources { request, bindings, targets, preparation: root.join("preparation"), statements: engine_directory(root), general: None };
    prepare_inputs(&sources, parser, framework_executable).await
}

/// The general line's inputs at scale `index` of the ladder (`engine.scales`): the request at that scale
/// (`WorkloadRequest::at_scale`: its locations, capture and saved answers), its bindings and baselines, preparation
/// under `<run>/engine/scales/<scale>/preparation` and statements under `<run>/engine/scales/<scale>`, with the
/// general inputs (the scale, the call limits, the branches and the budget).
pub async fn prepare_engine_scale(request: &WorkloadRequest, index: usize, root: &Path, parser: &SqlParser, framework_executable: &Path) -> Result<PreparedEngine, WorkloadError> {
    prepare_scale_in(request, index, &engine_directory(root), parser, framework_executable).await
}

/// [`prepare_engine_scale`] with its records under `records` instead of `<run>/engine` (`<records>/scales/<scale>/`).
pub(super) async fn prepare_scale_in(request: &WorkloadRequest, index: usize, records: &Path, parser: &SqlParser, framework_executable: &Path) -> Result<PreparedEngine, WorkloadError> {
    let engine = request.engine()?;
    let scale = engine.scales.get(index).ok_or_else(|| WorkloadError::invalid(format!("engine: the ladder has no scale {index}")))?;
    let view = request.at_scale(scale);
    let call_limits = CallLimits {
        call_limit_ns: engine.call_limit_seconds.unwrap_or(0).saturating_mul(1_000_000_000),
        anon_memory_limit_bytes: engine.anon_memory_limit_bytes.unwrap_or(0),
    };
    let general = GeneralInputs {
        scale: scale.clone(),
        scale_index: index,
        scales: engine.scales.len(),
        next_scale: engine.scales.get(index + 1).map(|s| s.name.clone()),
        call_limits,
        branches: super::branches::branch_names(engine.branches.unwrap_or(1)),
        budget_usd: engine.limits.max_cost_usd,
        emphasis: engine.emphasis,
        seed: engine.seed_version.as_ref().map(super::role::SeedFacts::read).transpose().map_err(|e| WorkloadError::invalid(format!("engine: {e}")))?,
        // The plain storages are the seeded storages, version 0's uses.
        plain_storages: engine.storage_seed.packages.iter().copied().collect(),
        // Measured from the run library over this scale's capture once it is prepared (`prepare_inputs`).
        plain_storage_bytes: 0,
    };
    let scale_dir = records.join("scales").join(&scale.name);
    let sources = InputSources { request: &view, bindings: &scale.bindings, targets: &scale.targets, preparation: scale_dir.join("preparation"), statements: scale_dir, general: Some(general) };
    prepare_inputs(&sources, parser, framework_executable).await
}

/// The directory of kept workload `name`'s records in a stage run (`<run>/engine/kept/<name>`).
pub fn kept_workload_directory(root: &Path, name: &str) -> PathBuf {
    engine_directory(root).join("kept").join(name)
}

/// The directory of the records of workload `name` (not the primary) of a run of several workloads: a stage run's
/// `<run>/engine/kept/<name>` ([`kept_workload_directory`]), a run of several workloads' `<run>/engine/workloads/<name>`.
pub fn member_directory(root: &Path, form: WorkloadForm, name: &str) -> PathBuf {
    match form {
        WorkloadForm::Workloads => engine_directory(root).join(super::tree::WORKLOADS_DIRECTORY).join(name),
        _ => kept_workload_directory(root, name),
    }
}

/// The inputs of a run of several workloads ([`prepare_stage_inputs`]).
pub struct StageInputs {
    /// Every workload, the primary (the request's own) first.
    pub workloads: Vec<StageWorkloadInputs>,
    /// The run's rule set (`EngineRuleSet::for_stage` of a stage run, `EngineRuleSet::for_members` of a run of several
    /// workloads, over every workload, the primary first), which every workload's inputs carry as their `rules`: every
    /// crate of the run is frozen and admitted under it.
    pub rules: EngineRuleSet,
}

/// One workload of a run of several workloads, prepared.
pub struct StageWorkloadInputs {
    pub name: String,
    pub role: MemberRole,
    pub primary: bool,
    /// Its request: the run's request itself for the primary, the workload's request file for every other.
    pub request: WorkloadRequest,
    /// Its inputs at its last scale (each workload stays there: no ladder).
    pub prepared: PreparedEngine,
    /// Its first scale's inputs, where its submissions' variants are checked, when that is not its last scale.
    pub first_scale: Option<FirstScale>,
    /// The seed of its side of the root (a run of several workloads only).
    pub seed: Option<Seed>,
    /// A run of several workloads: its plain flat storages in table order (`submission::members::plain_flat_storages`).
    pub flat_storages: Vec<(String, ContentId)>,
}

/// The inputs of the run of several workloads `set` (the request's `WorkloadRequest::workload_set`): the primary at its
/// last scale under `<run>/engine/scales/<scale>/` (as a one-workload run's), every other workload at its last scale under
/// its own directory ([`member_directory`]), every workload also at its first scale when that is another one; then the
/// run's rule set over every workload's schema and template constants, set as every workload's `rules`; in a run of
/// several workloads also each workload's plain flat storages. Each preparation is the general line's
/// (`prepare_engine_scale`), so its records are reused on a relaunch. A check workload has no baselines (its scales name
/// no `targets`). A request of one workload is refused.
pub async fn prepare_stage_inputs(request: &WorkloadRequest, set: &WorkloadSet, root: &Path, parser: &SqlParser, framework_executable: &Path) -> Result<StageInputs, WorkloadError> {
    if set.form == WorkloadForm::One {
        return Err(WorkloadError::invalid("engine: a run of several workloads' inputs need engine.stage or engine.workloads"));
    }
    // Every workload at its last scale, and at its first when that is another one.
    let mut prepared = vec![];
    for (index, member) in set.members.iter().enumerate() {
        let records = if index == 0 { engine_directory(root) } else { member_directory(root, set.form, &member.name) };
        let workload_request = if index == 0 { request.clone() } else { member.request.clone() };
        let scales = workload_request.engine()?.scales.len();
        let last = prepare_scale_in(&workload_request, scales - 1, &records, parser, framework_executable).await?;
        let first = if scales > 1 { Some(prepare_scale_in(&workload_request, 0, &records, parser, framework_executable).await?) } else { None };
        prepared.push((member, workload_request, last, first));
    }
    // One rule set over every workload, carried by every workload's inputs.
    let schemas: Vec<Vec<gendb_frontend::ast::TableDef>> =
        prepared.iter().map(|(_, _, last, _)| last.inputs.sessions.first().map(|(_, s)| s.statement().instance.doc.tables.clone()).unwrap_or_default()).collect();
    let rule_workloads: Vec<StageWorkload> =
        prepared.iter().zip(&schemas).map(|((member, _, last, _), schema)| StageWorkload { name: &member.name, schema, constants: last.inputs.rules.constants() }).collect();
    let rules = match set.form {
        WorkloadForm::Workloads => EngineRuleSet::for_members(&rule_workloads),
        _ => EngineRuleSet::for_stage(&rule_workloads),
    };
    let mut workloads = vec![];
    for (index, ((member, workload_request, mut last, first), schema)) in prepared.into_iter().zip(&schemas).enumerate() {
        set_rules(&mut last, &rules)?;
        let first_scale = match first {
            Some(mut first) => {
                set_rules(&mut first, &rules)?;
                Some(FirstScale::of(&first))
            }
            None => None,
        };
        let flat_storages = match set.form {
            WorkloadForm::Workloads => super::submission::members::plain_flat_storages(&workload_request.library, schema, &last.inputs.seeded)
                .map_err(|e| WorkloadError::invalid(format!("engine.workloads: workload {}: {e}", member.name)))?,
            _ => vec![],
        };
        let seed = if set.form == WorkloadForm::Workloads { member.seed.clone() } else { None };
        workloads.push(StageWorkloadInputs { name: member.name.clone(), role: member.role, primary: index == 0, request: workload_request, prepared: last, first_scale, seed, flat_storages });
    }
    Ok(StageInputs { workloads, rules })
}

// ------------------------------------------------------------------------------------------------ check-request

/// `gendb engine check-request REQUEST` (the stage fixture): every workload of a general-line request (one
/// workload, a stage run or `engine.workloads`) checked at every scale as the run will read it, without preparing data,
/// running an engine or timing anything. Per workload and scale: the training set with the scale's bindings; the
/// baselines with a cell for every template at the timing binding and every worker count at every scale the run times
/// (a check workload names none; a run of several workloads times every workload at its last scale, a run of one
/// workload from its start scale on, `EngineRequest::start_scale`); every saved answer naming a training template and
/// visible binding, its file present; a saved answer of every required engine for every template at every visible
/// binding; the capture, the original data record and every source file present; the library open, every seeded storage
/// admitted in it with a stored asset for the scale's capture. Every seed: a version folder accepted with its code and
/// a manifest (the workload named among a version of several), or an exported folder with its manifest and agent. The
/// report lists every problem found (`ok` when none); only an unreadable or invalid request is an error. Small records
/// only: capture records and stamps are opened, no data is read.
pub fn check_request(path: &Path) -> Result<Value, WorkloadError> {
    let request = WorkloadRequest::read(path)?;
    request.validate()?;
    let engine = request.engine()?;
    if !engine.is_general() {
        return Err(WorkloadError::invalid("engine: check-request is for general-line requests (engine.line \"general\")"));
    }
    let set = request.workload_set()?;
    let several = set.form != WorkloadForm::One;
    let mut problems: Vec<String> = vec![];
    let mut workloads = vec![];
    for member in &set.members {
        let mut found: Vec<String> = vec![];
        let scales = check_member_scales(&member.request, member.role, several, &mut found);
        if let Some(seed) = &member.seed {
            check_seed(seed, &mut found);
        }
        problems.extend(found.iter().map(|p| format!("workload {}: {p}", member.name)));
        workloads.push(json!({"name":member.name,"role":member.role.name(),"request":member.path.as_ref().map_or_else(|| path.to_path_buf(), |p| p.clone()),"library":member.request.library,
            "seed":member.seed,"scales":scales,"problems":found}));
    }
    Ok(json!({"format_version":1,"request":path,"form":set.form,"ok":problems.is_empty(),"problems":problems,"workloads":workloads,
        "meaning":"every workload of the request at every scale as the run reads it (inputs, saved answers, libraries, stored assets, seeds); no data is prepared, no engine runs and nothing is timed"}))
}

/// [`check_request`]'s checks of one workload's request at every scale (`role`: its role; `several`: a run of several
/// workloads, which times it at its last scale): one record per scale; every problem is added to `found`.
fn check_member_scales(request: &WorkloadRequest, role: MemberRole, several: bool, found: &mut Vec<String>) -> Vec<Value> {
    let Ok(engine) = request.engine() else {
        found.push("no engine section".into());
        return vec![];
    };
    let required: Vec<String> = match &request.validation {
        ValidationPolicy::FormalProofs { required_engines, .. } => required_engines.clone(),
        ValidationPolicy::TestsAndReferences => vec![],
    };
    let timed_from = if several { engine.scales.len().saturating_sub(1) } else { engine.start_scale() };
    let store = match ObjectStore::open_existing(&request.library) {
        Ok(store) => Some(store),
        Err(e) => {
            found.push(format!("library {}: {e}", request.library.display()));
            None
        }
    };
    let mut seeded = vec![];
    if let Some(store) = &store {
        for id in &engine.storage_seed.packages {
            match catalog::admitted_storage(store, *id) {
                Ok((package, _)) => seeded.push((package.name.clone(), *id, package)),
                Err(e) => found.push(format!("seeded storage {id} is not admitted in {}: {e}", request.library.display())),
            }
        }
        if let Ok(versions) = gendb_artifacts::verus::engine_versions(store)
            && !versions.is_empty()
        {
            found.push(format!("library {} already holds {} engine versions; a run's library starts without engine versions", request.library.display(), versions.len()));
        }
    }
    let mut records = vec![];
    for (index, scale) in engine.scales.iter().enumerate() {
        let at = |what: String| format!("{}: {what}", scale.name);
        let mut record = json!({"name":scale.name,"timed":role != MemberRole::Check && index >= timed_from,"original_data_bytes":scale.original_data_bytes});
        let training = match TrainingSet::read(&engine.templates, &scale.bindings, &engine.variants, &engine.timing_binding) {
            Ok(training) => training,
            Err(e) => {
                found.push(at(format!("the training set: {e}")));
                records.push(record);
                continue;
            }
        };
        record["templates"] = json!(training.templates.len());
        record["saved_answers"] = json!(scale.saved_answers.len());
        if role != MemberRole::Check || !scale.targets.as_os_str().is_empty() {
            match Baselines::read(&scale.targets) {
                Ok(baselines) => {
                    record["baseline_cells"] = json!(baselines.cell_count());
                    if role != MemberRole::Check && index >= timed_from {
                        for template in &training.templates {
                            for &workers in &request.hardware.threads {
                                if baselines.cell(&template.name, &engine.timing_binding, workers).is_none() {
                                    found.push(at(format!("no baseline of {} at {workers} workers", template.name)));
                                }
                            }
                        }
                    }
                }
                Err(e) => found.push(at(format!("the baselines: {e}"))),
            }
        }
        for answer in &scale.saved_answers {
            match training.template(&answer.query) {
                None => found.push(at(format!("a saved answer of {} names no training template", answer.query))),
                Some(template) if template.arguments(&answer.binding).is_none() => found.push(at(format!("a saved answer of {} names no visible binding {}", answer.query, answer.binding))),
                Some(_) if !answer.path.is_file() => found.push(at(format!("the saved answer {} is missing", answer.path.display()))),
                Some(_) => {}
            }
        }
        for template in &training.templates {
            for (binding, _) in &template.bindings {
                for engine_name in &required {
                    if !scale.saved_answers.iter().any(|a| a.query == template.name && a.binding == *binding && a.engine == *engine_name) {
                        found.push(at(format!("no saved answer of {engine_name} for {} at {binding}", template.name)));
                    }
                }
            }
        }
        if !scale.prepared_workload.is_dir() {
            found.push(at(format!("the capture {} is missing", scale.prepared_workload.display())));
        }
        if !scale.original_data_record.is_file() {
            found.push(at(format!("the original data record {} is missing", scale.original_data_record.display())));
        }
        if let Some(missing) = scale.locations.values().flatten().find(|l| !l.is_file()) {
            found.push(at(format!("the source file {} is missing", missing.display())));
        }
        // Every seeded storage has a stored asset for this scale's capture (`gendb prepare-flat-storage`).
        if let (Some(store), true) = (&store, scale.prepared_workload.is_dir()) {
            let view = request.at_scale(scale);
            let assets = gendb_storage::import::PreparedSource::open(&scale.prepared_workload, &view.dataset)
                .map_err(|e| e.to_string())
                .and_then(|source| CurrentCapture::of(&source).map_err(|e| e.to_string()))
                .and_then(|capture| gendb_storage::versions::resolve_storage_assets(store, seeded.iter().map(|(name, id, package)| (name.as_str(), *id, package)), &capture).map_err(|e| e.to_string()));
            match assets {
                Ok(assets) => record["stored_assets"] = json!({"storages":assets.len(),"stored_bytes":assets.iter().map(|a| a.asset.storage_bytes).sum::<u64>()}),
                Err(e) => found.push(at(format!("the seeded storages' assets for the capture: {e}"))),
            }
        }
        records.push(record);
    }
    records
}

/// [`check_request`]'s checks of one seed; every problem is added to `found`.
pub(super) fn check_seed(seed: &Seed, found: &mut Vec<String>) {
    match seed {
        Seed::Run { version, workload } => {
            let dir = version.directory();
            let node: Option<Value> = records::read_json(&dir.join("node.json")).ok();
            if node.as_ref().is_none_or(|n| n["accepted"] != true) {
                found.push(format!("seed {}: not an accepted version folder", dir.display()));
            }
            if !dir.join("code/agent/mod.rs").is_file() {
                found.push(format!("seed {}: no code/agent/mod.rs", dir.display()));
            }
            match ["seed-manifest.json", "manifest.json"].into_iter().map(|f| dir.join(f)).find(|p| p.is_file()).map(|f| records::read_json::<EngineManifest>(&f)) {
                None => found.push(format!("seed {}: no manifest", dir.display())),
                Some(Err(e)) => found.push(format!("seed {}: its manifest: {e}", dir.display())),
                Some(Ok(manifest)) => match (manifest.workloads.is_empty(), workload) {
                    (true, Some(w)) => found.push(format!("seed {}: a version of one workload has no workload {w}", dir.display())),
                    (false, None) => found.push(format!("seed {}: a version of several workloads: the seed names its workload", dir.display())),
                    (false, Some(w)) if !manifest.workloads.iter().any(|e| e.name == *w) => found.push(format!("seed {}: no workload {w}", dir.display())),
                    _ => {}
                },
            }
        }
        Seed::Source { source } => {
            if !source.join(super::submission::members::EXPORT_MANIFEST_FILE).is_file() || !source.join("agent/mod.rs").is_file() {
                found.push(format!("seed {}: not an exported engine folder (manifest.json and agent/mod.rs)", source.display()));
            }
        }
    }
}

/// Set the rule set of freshly prepared inputs (not shared yet).
fn set_rules(prepared: &mut PreparedEngine, rules: &EngineRuleSet) -> Result<(), WorkloadError> {
    let inputs = Arc::get_mut(&mut prepared.inputs).ok_or_else(|| WorkloadError::invalid("engine: a stage workload's inputs are shared before their rule set is set"))?;
    inputs.rules = rules.clone();
    Ok(())
}

/// Where one preparation of the engine inputs reads and writes.
struct InputSources<'a> {
    request: &'a WorkloadRequest,
    bindings: &'a Path,
    targets: &'a Path,
    /// The data preparation's root.
    preparation: PathBuf,
    /// Where the encoded statements and the variants' statement records go.
    statements: PathBuf,
    general: Option<GeneralInputs>,
}

async fn prepare_inputs(sources: &InputSources<'_>, parser: &SqlParser, framework_executable: &Path) -> Result<PreparedEngine, WorkloadError> {
    let request = sources.request;
    let engine = request.engine()?;
    let invalid = |e: String| WorkloadError::invalid(format!("engine: {e}"));
    let training = TrainingSet::read(&engine.templates, sources.bindings, &engine.variants, &engine.timing_binding).map_err(invalid)?;
    if let ValidationPolicy::FormalProofs { saved_answers, .. } = &request.validation
        && let Some(unknown) = saved_answers.iter().find(|a| training.template(&a.query).is_none())
    {
        return Err(invalid(format!("validation.saved_answers: {} is not a training template", unknown.query)));
    }
    // A check workload of a run of several workloads names no targets: it is never timed, so it has no baselines.
    let baselines = if sources.targets.as_os_str().is_empty() { Baselines::default() } else { Baselines::read(sources.targets).map_err(|e| invalid(e.to_string()))? };
    let constants = TemplateConstants::from_templates_json(&engine.templates).map_err(invalid)?;
    let store = ObjectStore::open_existing(&request.library).map_err(|e| invalid(format!("the engine library {}: {e}; seed it first", request.library.display())))?;
    for reuse in &engine.reuse_libraries {
        super::role::open_reuse_library(reuse).map_err(|e| invalid(e.to_string()))?;
    }
    let mut seeded = vec![];
    for package in &engine.storage_seed.packages {
        let (record, _) = catalog::admitted_storage(&store, *package)
            .map_err(|e| invalid(format!("engine_library_not_seeded: seeded storage {package} is not admitted in {} ({e})", request.library.display())))?;
        seeded.push((record.name.clone(), *package));
    }
    let preparation = &sources.preparation;
    records::create_dir(preparation)?;
    let prepared = prepare_workload(&preparation_request(request, &engine.limits, &training), preparation, parser, framework_executable).await?;
    let data = prepared.data.ok_or_else(|| invalid("every training template was refused before data preparation".into()))?;
    let mut sessions: Vec<(String, Arc<QuerySession>)> = vec![];
    for (template, query) in training.templates.iter().zip(prepared.queries) {
        match query {
            PreparedQuery::Ready(session) => sessions.push((template.name.clone(), session)),
            PreparedQuery::Refused(record) => return Err(invalid(format!("training template {} was refused at preparation: {}", template.name, record["error"]))),
        }
    }
    let check_sources = CheckSources { parser, dataset: &request.dataset, constraints: request.integrity_constraints.as_ref(), validation: &request.validation };
    let checks = EngineChecks::prepare(&training, &sessions, &check_sources, &sources.statements).map_err(|e| invalid(e.to_string()))?;
    let statements = EncodedStatements::prepare(&training, &checks, &sources.statements).map_err(|e| invalid(e.to_string()))?;
    let workers = request.hardware.threads.clone();
    let facts = training_facts(&training, &sessions, &baselines, &workers, &statements).map_err(|e| invalid(e.to_string()))?;
    let numeric_relative_tolerance = match &request.validation {
        ValidationPolicy::FormalProofs { numeric_relative_tolerance, .. } => numeric_relative_tolerance.clone(),
        ValidationPolicy::TestsAndReferences => "0".into(),
    };
    let line = engine.engine_line().map_err(invalid)?;
    let schema = sessions.first().map(|(_, s)| s.statement().instance.doc.tables.clone()).unwrap_or_default();
    // The plain storage's size at this scale, reported beside the general line's budget: the
    // seeded storages version 0 reads, measured from the run library over this scale's capture.
    let general = match &sources.general {
        Some(general) => {
            let capture = CurrentCapture::of(&data.capture.current()).map_err(|e| invalid(e.to_string()))?;
            let plain_storage_bytes = plain_storage_bytes(&store, &capture, &schema, &request.storage_policy, &seeded).map_err(|e| invalid(e.to_string()))?;
            Some(GeneralInputs { plain_storage_bytes, ..general.clone() })
        }
        None => None,
    };
    let inputs = EngineInputs {
        training,
        sessions,
        checks,
        statements,
        training_facts: facts,
        baselines,
        rules: EngineRuleSet::for_line(line, constants, &schema),
        workers,
        engine_limits: engine.limits.clone(),
        hardware: json!(request.hardware),
        observed_hardware: observe_host(),
        seeded,
        reuse_libraries: engine.reuse_libraries.clone(),
        part_access: request.part_access.unwrap_or_default(),
        dataset: request.dataset.clone(),
        constraints: request.integrity_constraints.clone(),
        numeric_relative_tolerance,
        general,
    };
    Ok(PreparedEngine { inputs: Arc::new(inputs), data })
}

/// Run the engine request (module documentation) in `run_dir` with `authors(round, inspection_dir)` as each round's
/// author. Returns the run summary (also published under `run_dir`).
pub async fn run_engine<A, F>(request: &WorkloadRequest, run_dir: &Path, mut authors: F, framework_executable: &Path) -> Result<Value, WorkloadError>
where
    A: AuthorTransport + Send,
    F: FnMut(u32, &Path) -> Result<A, String>,
{
    request.validate()?;
    let engine = request.engine()?.clone();
    records::create_dir(run_dir)?;
    let root = run_dir.canonicalize().map_err(|e| RecordError::new(run_dir, e))?;
    record_route(&root, Route::Engine)?;
    record_request(&root, &serde_json::to_value(request).map_err(|e| WorkloadError::invalid(e.to_string()))?)?;
    let parser = SqlParser::from_environment().map_err(WorkloadError::Frontend)?;
    let prepared = prepare_engine(request, &root, &parser, framework_executable).await?;
    let engine_dir = engine_directory(&root);
    let sockets = socket_directory()?;
    let (status, reason) = loop {
        let state = EngineState::read(&engine_dir)?;
        let record = match state.open_round() {
            Some(open) => records::read_json::<RoundRecord>(&Path::new(open["directory"].as_str().unwrap_or_default()).join("round.json"))?,
            None => {
                if let Some(reason) = stop_reason(&state, &engine.limits) {
                    break ("stopped", reason);
                }
                let round = state.rounds.len() as u32 + 1;
                let seed = next_seed(&state, &engine_dir, round);
                let (spent, _) = state.spent();
                let task = json!({"role":"schema_engine","round":round,"seed":seed.description,"threads":request.hardware.threads,
                    "training_set":prepared.inputs.training.identity,"timing_binding":engine.timing_binding});
                let record = RoundRecord {
                    format_version: 1,
                    round,
                    next_version: state.versions.len() as u32 + 1,
                    seed,
                    request: RunRequest { format_version: 1, task, limits: round_limits(&engine.limits, spent), continue_from: None },
                    started_unix_ms: records::now_unix_ms(),
                };
                let dir = round_directory(&engine_dir, round);
                records::create_dir(&dir)?;
                records::write_new_json(&dir.join("round.json"), &record)?;
                record
            }
        };
        let outcome = run_round(request, &root, &prepared, &state, &record, &mut authors, &sockets)?;
        let state = EngineState::read(&engine_dir)?;
        let round = state.rounds.iter().find(|r| r["round"] == record.round).cloned().unwrap_or(Value::Null);
        if round["outcome"] == "version"
            && let Some(version) = state.versions.iter().find(|v| v["round"] == record.round)
        {
            record_version_receipts(Path::new(version["directory"].as_str().unwrap_or_default()), &round)?;
        }
        write_output(request, &root, &engine_dir);
        if outcome["status"] == "framework_error" {
            break ("resumable", "framework_error");
        }
        if round["outcome"] == "open" {
            break ("resumable", "accounting_unresolved");
        }
        // An eligible submission whose admission failed in the framework is not the author's attempt: stop for review
        // before another round is paid for (the round's evaluation stays recorded; a relaunch starts the next round).
        if round["qualification_error"].as_str().is_some_and(|e| e.starts_with("tool_failure")) {
            break ("stopped", "qualification_framework_failure");
        }
        // Review cadence (`engine.pause_after_round`): the round is closed with every record written; a relaunch starts
        // the next one. A stop that holds now is reported as the stop instead.
        if engine.pause_after_round && stop_reason(&state, &engine.limits).is_none() {
            break (PAUSED, PAUSED_FOR_REVIEW);
        }
    };
    let mut summary = run_summary(&root, &engine_dir, &prepared, status, reason)?;
    if status == PAUSED {
        summary["pause"] = pause_record(&engine_dir)?;
    }
    publish_summary(&root, &summary)?;
    Ok(summary)
}

/// `status` of a run summary written at a pause for review.
pub const PAUSED: &str = "paused";
/// `reason` of a run summary written at a pause for review.
pub const PAUSED_FOR_REVIEW: &str = "paused_for_review";

/// What a pause for review records in the run summary: the round it followed, that round's outcome and version, the
/// round to come, and how the run resumes.
fn pause_record(engine_dir: &Path) -> Result<Value, WorkloadError> {
    let state = EngineState::read(engine_dir)?;
    let last = state.rounds.last().cloned().unwrap_or(Value::Null);
    Ok(json!({"paused_after_round":last["round"],"round_directory":last["directory"],"outcome":last["outcome"],"version":last["version"],
        "status_of_round":last["status"],"next_round":state.rounds.len() + 1,"latest_version":state.latest_version().map(|v| &v["version"]),
        "resume":"relaunch the same command (same request and run directory): the run continues with the next round from these records; nothing is replayed. engine.pause_after_round is not part of the run's identity, so the relaunch may switch it",
        "meaning":"a review cadence (engine.pause_after_round), not a cap: no limit on rounds or cost follows from it"}))
}

/// One round's session: the engine role over the session bench, retained on its owner thread, and the round's author
/// leased by the host locks; scheduled as one session (`controller::schedule`, which records a framework error in the
/// round directory). Returns the session's summary or its framework error record.
fn run_round<A, F>(request: &WorkloadRequest, root: &Path, prepared: &PreparedEngine, state: &EngineState, record: &RoundRecord, authors: &mut F, sockets: &Path) -> Result<Value, WorkloadError>
where
    A: AuthorTransport + Send,
    F: FnMut(u32, &Path) -> Result<A, String>,
{
    let engine_dir = engine_directory(root);
    let directory = round_directory(&engine_dir, record.round);
    let author = authors(record.round, &root.join("author-inspection").join(format!("round-{:04}", record.round)))
        .map_err(|detail| WorkloadError::Controller(crate::controller::ControllerError::Author { stage: "round author", detail }))?;
    let author = HostLeasedAuthor::new(author, request.host_locks.clone());
    let bench = Workbench::new(
        BenchConfig {
            library: request.library.clone(),
            locks: request.host_locks.clone(),
            parser: SqlParser::from_environment().map_err(WorkloadError::Frontend)?,
            live_bytes_allowance: request.data_allowance.as_ref().map(|a| a.live_bytes),
            storage_policy: request.storage_policy.clone(),
            asset_upkeep: None,
        },
        prepared.data.capture.clone(),
        prepared.inputs.sessions.iter().map(|(_, s)| s.clone()).collect(),
    );
    let config = EngineRoleConfig {
        engine_dir: engine_dir.clone(),
        inputs: prepared.inputs.clone(),
        mode: EngineRoleMode::Round(RoundConfig { round: record.round, seed: record.seed.clone(), next_version: record.next_version, history: state.author_view() }),
    };
    let role = RetainedRole::start(EngineAuthorRole::new(bench, config), &directory, sockets)?;
    let session = ScheduledSession { directory: directory.clone(), request: record.request.clone(), author, role, reselect_from: None, on_close: None };
    let mut results = run_sessions(vec![session], &directory, 1)?;
    Ok(results.pop().unwrap_or(Value::Null))
}

/// The engine folders of the output home, when the request names one; a failure is recorded, never fatal.
fn write_output(request: &WorkloadRequest, root: &Path, engine_dir: &Path) {
    let Some(home) = &request.output_home else { return };
    if let Err(error) = crate::output::engine::write_engine(home, engine_dir) {
        let record = root.join(format!("output-error-{}.json", records::now_unix_ms()));
        let _ = records::write_json_atomic(&record, &json!({"output_home":home,"error":error.to_string()}));
    }
}

/// The run summary: status and reason, the latest version and its stop decision, every version and round, and the
/// authors' provider-reported cost per round and in total.
fn run_summary(root: &Path, engine_dir: &Path, prepared: &PreparedEngine, status: &str, reason: &str) -> Result<Value, WorkloadError> {
    let state = EngineState::read(engine_dir)?;
    let (spent, complete) = state.spent();
    let latest = state.latest_version();
    Ok(json!({"format_version":1,"status":status,"reason":reason,"run":root,
        "latest_version":latest.map(|v| &v["version"]),"stop":latest.map(|v| &v["stop"]),
        "versions":state.versions.iter().map(|v| json!({"version":v["version"],"round":v["round"],"directory":v["directory"],
            "totals_ns":v["totals"]["workers"].as_array().into_iter().flatten().map(|w| json!({"workers":w["workers"],"engine_ns":w["engine_ns"],"margin":w["margin"]})).collect::<Vec<_>>()})).collect::<Vec<_>>(),
        "rounds":state.rounds,
        "author_accounting":{"known_reported_cost_usd_total":spent,"cost_complete":complete,
            "scope":"provider-reported author cost of every round session, counted once from each round's summary; framework work and the controller are not included; raw receipts in each round's calls/ are authoritative"},
        "statements":{"training_set":prepared.inputs.statements.record["training_set"],"ast_format":prepared.inputs.statements.record["ast_format"]},"statements_record":engine_dir.join(super::facts::STATEMENTS_FILE),
        "preparation":{"preparation_ns":prepared.data.preparation_ns as u64,"record":prepared.data.record,"source_version":prepared.data.source.source_snapshot()},
        "scope":"one verified engine for the schema, built in rounds against the training templates; every version is kept under engine/versions"}))
}

// ------------------------------------------------------------------------------------------------ routes

/// `gendb engine synthesize REQUEST RUN_DIR`: the engine run with one inspected Claude Code author per round (evidence
/// under `<run>/author-inspection/round-NNNN`; a version without a declared usage scope is refused).
pub async fn synthesize_engine(request_path: &Path, run_dir: &Path, framework_executable: &Path) -> Result<Value, WorkloadError> {
    let _ = crash_dumps::contain();
    let request = WorkloadRequest::read(request_path)?;
    let author = |evidence: &Path| claude_code_author(&request, framework_executable, evidence);
    if request.engine()?.is_general() {
        let options = GeneralRunOptions { prompt: GENERAL_LINE_PROMPT, render_only: false };
        return run_general_engine(&request, run_dir, |_session: &str, evidence: &Path| author(evidence), framework_executable, options).await;
    }
    run_engine(&request, run_dir, |_round: u32, evidence: &Path| author(evidence), framework_executable).await
}

/// The author of `gendb engine synthesize`: Claude Code (`request.author_executable`, `request.author_model`) inspected
/// into `evidence`, with the local tool server `framework_executable author-tools mcp`. A version without a declared
/// usage scope for its reported cost and tokens is refused.
pub fn claude_code_author(request: &WorkloadRequest, framework_executable: &Path, evidence: &Path) -> Result<ClaudeCode, String> {
    let tool_server = LocalToolServer { program: framework_executable.to_path_buf(), arguments: LOCAL_TOOL_SERVER_WORDS.iter().map(|w| w.to_string()).collect() };
    let author = ClaudeCode::inspect(request.author_executable.clone(), request.author_model, evidence, tool_server).map_err(|e| e.to_string())?;
    let version = author.capability().version;
    if declared_usage_scope(&version).is_none() {
        return Err(format!("Claude Code {version} has no declared usage scope for its reported cost and tokens; configure an inspected version"));
    }
    Ok(author)
}

/// The prompt of every call of a general-line session (`prompts::engine_policy::general_author_prompt`): the full
/// prompt on a session's first call, the evaluation and the changed facts on a call that continues the session.
pub const GENERAL_LINE_PROMPT: fn(&crate::controller::PromptInput) -> String = crate::prompts::engine_policy::general_author_prompt;

/// `gendb engine render-inputs REQUEST OUT_DIR`: the inputs of the first call of the run's next round, rendered without a
/// provider: the request runs one round in `OUT_DIR/run` with a render-only author that saves the call's prompt,
/// context, contract and tool context under `OUT_DIR/rendered` and submits no manifest (the round is recorded as an
/// attempt; nothing is admitted). The run pauses after that round (`pause_after_round`), so the rendered inputs show the
/// user's guards as the request sets them. The output home is not written.
pub async fn render_engine_inputs(request_path: &Path, out: &Path, prepared_run: Option<&Path>, framework_executable: &Path) -> Result<Value, WorkloadError> {
    let _ = crash_dumps::contain();
    if out.exists() {
        return Err(WorkloadError::invalid(format!("{} exists; render-inputs writes a new directory", out.display())));
    }
    let mut request = WorkloadRequest::read(request_path)?;
    request.output_home = None;
    let general = request.engine()?.is_general();
    if let Some(engine) = &mut request.engine {
        engine.pause_after_round = !general;
    }
    let rendered = out.join("rendered");
    let summary = if general {
        // The general line renders the first call of b1's next session over a copy of a prepared run's version 0 and
        // main line: nothing is admitted or selected in the library (the render's one submission names no manifest).
        let prepared = prepared_run.ok_or_else(|| WorkloadError::invalid("render-inputs of a general-line request needs the prepared run directory (gendb engine prepare REQUEST RUN_DIR) as its third argument"))?;
        let from = engine_directory(prepared);
        let to = engine_directory(&out.join("run"));
        if !from.join("versions").join(super::tree::ROOT_VERSION).join(super::tree::NODE_FILE).is_file() {
            return Err(WorkloadError::invalid(format!("{} has no version 0; run gendb engine prepare first", prepared.display())));
        }
        copy_tree(&from.join("versions").join(super::tree::ROOT_VERSION), &to.join("versions").join(super::tree::ROOT_VERSION), false)
            .map_err(|e| WorkloadError::invalid(format!("copying version 0 for the render: {e}")))?;
        for file in [super::tree::MAIN_LINE_FILE, super::branches::LADDER_FILE] {
            if from.join(file).is_file() {
                fs::copy(from.join(file), to.join(file)).map_err(|e| RecordError::new(&to.join(file), e))?;
            }
        }
        // A stage run's out-of-the-box record, which its stage view shows (`engine::stage::root`).
        let out_of_the_box = Path::new(super::stage::root::SEED_DIRECTORY).join(super::stage::root::OUT_OF_THE_BOX_DIRECTORY);
        for file in ["record.json", super::stage::root::OUT_OF_THE_BOX_FILE] {
            let source = from.join(&out_of_the_box).join(file);
            if source.is_file() {
                records::create_dir(&to.join(&out_of_the_box))?;
                fs::copy(&source, to.join(&out_of_the_box).join(file)).map_err(|e| RecordError::new(&to.join(&out_of_the_box).join(file), e))?;
            }
        }
        let authors = |_session: &str, _evidence: &Path| -> Result<RenderAuthor, String> { Ok(RenderAuthor { out: rendered.clone() }) };
        run_general_engine(&request, &out.join("run"), authors, framework_executable, GeneralRunOptions { prompt: GENERAL_LINE_PROMPT, render_only: true }).await?
    } else {
        records::create_dir(out)?;
        let authors = |_round: u32, _evidence: &Path| -> Result<RenderAuthor, String> { Ok(RenderAuthor { out: rendered.clone() }) };
        run_engine(&request, &out.join("run"), authors, framework_executable).await?
    };
    let mut files = vec![];
    for entry in walk(&rendered) {
        let text = fs::read_to_string(&entry).unwrap_or_default();
        files.push(json!({"file":entry.strip_prefix(&rendered).unwrap_or(&entry),"lines":text.lines().count(),"bytes":fs::metadata(&entry).map(|m| m.len()).unwrap_or(0)}));
    }
    let record = json!({"format_version":1,"rendered":rendered,"prompt":rendered.join("prompt.md"),"rendered_call":rendered.join("prompt.md").is_file(),"files":files,
        "run":out.join("run"),"summary":summary,"scope":"the first call's inputs of one engine round through the public controller with a render-only author: no provider, no admission"});
    records::write_new_json(&out.join("render.json"), &record)?;
    Ok(record)
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

/// Usage of `gendb engine`.
pub const ENGINE_USAGE: &str = "usage: gendb engine synthesize REQUEST.json RUN_DIR | gendb engine prepare REQUEST.json RUN_DIR (general line: version 0, no author) | gendb engine render-inputs REQUEST.json OUT_DIR [PREPARED_RUN_DIR (general line)] | gendb engine final-evaluation REQUEST.json RUN_DIR VERSION [SCALE [WORKLOAD]] (general line: the full protocol of one version, for reporting; SCALE `-` is the default scale; WORKLOAD names a workload of a run of several workloads, default the goal or primary) | gendb engine re-evaluate REQUEST.json RUN_DIR ATTEMPT (general line, controller stopped: an attempt judged not better, its recorded race's suspicious pairs timed again) | gendb engine operator-note RUN_DIR BRANCH TEXT (general line: a note shown once at the top of the branch's next author call) | gendb engine operator-resume RUN_DIR BRANCH [TEXT] (general line, controller stopped: end the branch's recorded provider wait, so the relaunched controller calls at once) | gendb engine export RUN_DIR VERSION OUT (general line: the engine source of one accepted version, a folder a later run seeds from) | gendb engine check-request REQUEST.json (general line: every workload at every scale as the run reads it; no data, engine or timing)";

/// `gendb engine operator-note RUN_DIR BRANCH TEXT` (`engine::operator_note`): appends the note and prints it as JSON.
/// Exit 0, 2 for a usage error, 3 when the note cannot be written (printed on stderr).
fn operator_note_command(words: &[Option<&str>]) -> ExitCode {
    let [Some(run_dir), Some(branch), Some(text)] = words else {
        eprintln!("{ENGINE_USAGE}");
        return ExitCode::from(2);
    };
    let written = Path::new(run_dir)
        .canonicalize()
        .map_err(|e| format!("{run_dir}: {e}"))
        .and_then(|root| super::operator_note::write_note(&engine_directory(&root), branch, text, "operator").map_err(|e| e.to_string()));
    match written {
        Ok(note) => {
            println!("{}", serde_json::to_string_pretty(&note).expect("JSON values serialize"));
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("gendb engine operator-note: {error}");
            ExitCode::from(3)
        }
    }
}

/// `gendb engine operator-resume RUN_DIR BRANCH [TEXT]` (`engine::operator_resume`): with the run's controller stopped,
/// records the end of the branch's provider wait and prints the record as JSON. Exit 0, 2 for a usage error, 3 when it
/// is refused or cannot be written (printed on stderr).
fn operator_resume_command(words: &[Option<&str>]) -> ExitCode {
    let (run_dir, branch, reason) = match words {
        [Some(run_dir), Some(branch)] => (run_dir, branch, None),
        [Some(run_dir), Some(branch), Some(reason)] => (run_dir, branch, Some(*reason)),
        _ => {
            eprintln!("{ENGINE_USAGE}");
            return ExitCode::from(2);
        }
    };
    match super::operator_resume::operator_resume(Path::new(run_dir), branch, reason) {
        Ok(record) => {
            println!("{}", serde_json::to_string_pretty(&record).expect("JSON values serialize"));
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("gendb engine operator-resume: {error}");
            ExitCode::from(3)
        }
    }
}

/// `gendb engine export RUN_DIR VERSION OUT` (`engine::export`): writes the exported engine folder and prints its record
/// as JSON. Exit 0, 2 for a usage error, 3 when it is refused or cannot be written (printed on stderr).
fn export_command(words: &[Option<&str>]) -> ExitCode {
    let [Some(run_dir), Some(version), Some(out)] = words else {
        eprintln!("{ENGINE_USAGE}");
        return ExitCode::from(2);
    };
    match super::export::export_version(Path::new(run_dir), version, Path::new(out)) {
        Ok(record) => {
            println!("{}", serde_json::to_string_pretty(&record).expect("JSON values serialize"));
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("gendb engine export: {error}");
            ExitCode::from(3)
        }
    }
}

/// `gendb engine check-request REQUEST` ([`check_request`]): prints the report as JSON. Exit 0 when nothing was found,
/// 1 when the report lists problems, 2 for a usage error, 3 when the request cannot be read (printed on stderr).
fn check_request_command(words: &[Option<&str>]) -> ExitCode {
    let [Some(request)] = words else {
        eprintln!("{ENGINE_USAGE}");
        return ExitCode::from(2);
    };
    match check_request(Path::new(request)) {
        Ok(report) => {
            println!("{}", serde_json::to_string_pretty(&report).expect("JSON values serialize"));
            if report["ok"] == true { ExitCode::SUCCESS } else { ExitCode::from(1) }
        }
        Err(error) => {
            eprintln!("gendb engine check-request: {error}");
            ExitCode::from(3)
        }
    }
}

/// `gendb engine ...` (the words after `engine`): prints the run summary or the render record as JSON. Exit 0 when the
/// controller returned a record (a stop, a resumable stop or a pause for review: the summary's `status` says which), 2
/// for a usage error, 3 when the run stopped with an error (printed on stderr).
pub fn command(arguments: &[OsString]) -> ExitCode {
    let words: Vec<Option<&str>> = arguments.iter().map(|a| a.to_str()).collect();
    if words.first() == Some(&Some("operator-note")) {
        return operator_note_command(&words[1..]);
    }
    if words.first() == Some(&Some("operator-resume")) {
        return operator_resume_command(&words[1..]);
    }
    if words.first() == Some(&Some("export")) {
        return export_command(&words[1..]);
    }
    if words.first() == Some(&Some("check-request")) {
        return check_request_command(&words[1..]);
    }
    let (Some(Some(sub)), [_, request, target, rest @ ..]) = (words.first().copied(), arguments) else {
        eprintln!("{ENGINE_USAGE}");
        return ExitCode::from(2);
    };
    let (prepared_run, final_version, final_scale, final_workload) = match (sub, rest) {
        ("final-evaluation", [version]) => (None, Some(version), None, None),
        ("final-evaluation", [version, scale]) => (None, Some(version), Some(scale), None),
        ("final-evaluation", [version, scale, workload]) => (None, Some(version), Some(scale), Some(workload)),
        // The attempt to re-evaluate travels as `final_version` (one name argument).
        ("re-evaluate", [attempt]) => (None, Some(attempt), None, None),
        ("final-evaluation" | "re-evaluate", _) => {
            eprintln!("{ENGINE_USAGE}");
            return ExitCode::from(2);
        }
        (_, []) => (None, None, None, None),
        ("render-inputs", [prepared]) => (Some(Path::new(prepared)), None, None, None),
        _ => {
            eprintln!("{ENGINE_USAGE}");
            return ExitCode::from(2);
        }
    };
    // A version, scale or workload name that is not UTF-8 is a usage error; a scale `-` is the default scale.
    fn text(word: Option<&OsString>) -> Result<Option<&str>, ()> {
        word.map(|w| w.to_str().ok_or(())).transpose()
    }
    let (Ok(final_version), Ok(final_scale), Ok(final_workload)) = (text(final_version), text(final_scale), text(final_workload)) else {
        eprintln!("{ENGINE_USAGE}");
        return ExitCode::from(2);
    };
    let final_scale = final_scale.filter(|scale| *scale != "-");
    let executable = match std::env::current_exe() {
        Ok(executable) => executable,
        Err(error) => {
            eprintln!("gendb engine: this executable: {error}");
            return ExitCode::from(3);
        }
    };
    // The user's stop of a controller (`gendb_runtime::process_stop`), before any thread starts: SIGTERM or SIGINT
    // stops every process tree this controller starts, waits, records `RUN_DIR/processes/stop-<id>.json` and ends it
    // with that signal; the run stays resumable.
    if matches!(sub, "synthesize" | "prepare")
        && let Err(error) = gendb_runtime::process_stop::install(Path::new(target))
    {
        eprintln!("gendb engine {sub}: the user's stop: {error}");
        return ExitCode::from(3);
    }
    let runtime = match tokio::runtime::Runtime::new() {
        Ok(runtime) => runtime,
        Err(error) => {
            eprintln!("gendb engine: async runtime: {error}");
            return ExitCode::from(3);
        }
    };
    let result = match sub {
        "synthesize" => runtime.block_on(synthesize_engine(Path::new(request), Path::new(target), &executable)),
        "render-inputs" => runtime.block_on(render_engine_inputs(Path::new(request), Path::new(target), prepared_run, &executable)),
        "prepare" => runtime.block_on(async {
            let request = WorkloadRequest::read(Path::new(request))?;
            prepare_general_run(&request, Path::new(target), &executable).await
        }),
        // The user's stop is not installed: the run directory's process records stay the run controller's
        // (`engine::final_evaluation`).
        "final-evaluation" => runtime.block_on(async {
            let request = WorkloadRequest::read(Path::new(request))?;
            let version = final_version.ok_or_else(|| WorkloadError::invalid(ENGINE_USAGE))?;
            super::final_evaluation::final_evaluation(&request, Path::new(target), version, final_scale, final_workload, &executable).await
        }),
        // Not installed either: the command refuses while the run's controller runs (`engine::re_evaluation`).
        "re-evaluate" => runtime.block_on(async {
            let request = WorkloadRequest::read(Path::new(request))?;
            let attempt = final_version.ok_or_else(|| WorkloadError::invalid(ENGINE_USAGE))?;
            super::re_evaluation::re_evaluate(&request, Path::new(target), attempt, &executable).await
        }),
        _ => {
            eprintln!("{ENGINE_USAGE}");
            return ExitCode::from(2);
        }
    };
    // A stopping controller ends from its stop thread, after its children (`gendb_runtime::process_stop`).
    gendb_runtime::process_stop::park_if_stopping();
    match result {
        Ok(record) => {
            println!("{}", serde_json::to_string_pretty(&record).expect("JSON values serialize"));
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("gendb engine {sub}: {error}");
            ExitCode::from(3)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::controller::limits::tests::limits;

    fn version(dir: &Path, number: u32, round: u32, stop: bool) -> Value {
        json!({"version":version_name(number),"number":number,"round":round,"directory":version_directory(dir, number),"totals":{"stop":{"stop":stop}}})
    }

    /// A general-line request file (path from `GENDB_GENERAL_REQUEST`) validates, and every scale's inputs read as the
    /// run reads them: the training set with the scale's bindings, its baselines with a cell for every template at the
    /// timing binding and every worker count at every scale the run times (from its start scale on,
    /// `EngineRequest::start_scale`: a continued run's earlier scales only check variants), its saved answers naming
    /// training templates and visible bindings, every visible binding of every template with a saved answer of every
    /// required engine (as each statement's preparation requires), and its files present. Reads small records only; no
    /// preparation, data or Verus.
    #[test]
    #[ignore = "reads the general-line request named by GENDB_GENERAL_REQUEST and the files it names"]
    fn general_request_file_reads_at_every_scale() {
        let path = PathBuf::from(std::env::var("GENDB_GENERAL_REQUEST").expect("GENDB_GENERAL_REQUEST"));
        let request = WorkloadRequest::read(&path).unwrap();
        request.validate().unwrap_or_else(|e| panic!("{e}"));
        let engine = request.engine().unwrap();
        assert!(engine.is_general());
        let required: Vec<String> = match &request.validation {
            ValidationPolicy::FormalProofs { required_engines, .. } => required_engines.clone(),
            ValidationPolicy::TestsAndReferences => vec![],
        };
        for (index, scale) in engine.scales.iter().enumerate() {
            let training = TrainingSet::read(&engine.templates, &scale.bindings, &engine.variants, &engine.timing_binding).unwrap_or_else(|e| panic!("{}: {e}", scale.name));
            let baselines = Baselines::read(&scale.targets).unwrap();
            if index >= engine.start_scale() {
                for template in &training.templates {
                    for &workers in &request.hardware.threads {
                        assert!(baselines.cell(&template.name, &engine.timing_binding, workers).is_some(), "{}: no baseline {} at {workers}", scale.name, template.name);
                    }
                }
            }
            for answer in &scale.saved_answers {
                let template = training.template(&answer.query).unwrap_or_else(|| panic!("{}: saved answer of {} names no training template", scale.name, answer.query));
                assert!(template.arguments(&answer.binding).is_some() && answer.path.is_file(), "{}: {} {} {}", scale.name, answer.query, answer.binding, answer.path.display());
            }
            for template in &training.templates {
                for (binding, _) in &template.bindings {
                    for engine_name in &required {
                        assert!(scale.saved_answers.iter().any(|a| a.query == template.name && a.binding == *binding && a.engine == *engine_name),
                            "{}: no saved answer of {engine_name} for {} at {binding}", scale.name, template.name);
                    }
                }
            }
            assert!(scale.prepared_workload.is_dir() && scale.original_data_record.is_file(), "{}", scale.name);
            assert!(scale.locations.values().flatten().all(|l| l.is_file()), "{}: a source file is missing", scale.name);
            let view = request.at_scale(scale);
            assert_eq!(view.prepared_workload.as_deref(), Some(scale.prepared_workload.as_path()));
            println!("{}: {} templates, {} saved answers, {} baseline cells, original data {} bytes", scale.name, training.templates.len(), scale.saved_answers.len(),
                baselines.cell_count(), scale.original_data_bytes);
        }
    }

    /// The preparation of a general-line request (path from `GENDB_GENERAL_REQUEST`) at one scale of its ladder
    /// (`GENDB_PREPARE_SCALE`, its name), as the run prepares it (`prepare_scale_in`), with its records under the scratch
    /// directory `GENDB_PREPARE_RECORDS` (never a run directory): every template translated, typed and preflighted under
    /// the request's validation (its saved answers read), every statement encoded with its echo, the training facts
    /// written. `GENDB_WORKER` is the gendb executable. Reuses the request's capture (no import when it covers the
    /// templates' columns); no engine runs and nothing is timed.
    #[test]
    #[ignore = "prepares the request named by GENDB_GENERAL_REQUEST at GENDB_PREPARE_SCALE under GENDB_PREPARE_RECORDS; GENDB_WORKER; TMPDIR a scratch directory"]
    fn general_request_prepares_at_scale() {
        let request = WorkloadRequest::read(Path::new(&std::env::var("GENDB_GENERAL_REQUEST").expect("GENDB_GENERAL_REQUEST"))).unwrap();
        request.validate().unwrap_or_else(|e| panic!("{e}"));
        let name = std::env::var("GENDB_PREPARE_SCALE").expect("GENDB_PREPARE_SCALE");
        let records = PathBuf::from(std::env::var("GENDB_PREPARE_RECORDS").expect("GENDB_PREPARE_RECORDS"));
        let worker = PathBuf::from(std::env::var("GENDB_WORKER").expect("GENDB_WORKER"));
        let index = request.engine().unwrap().scales.iter().position(|s| s.name == name).unwrap_or_else(|| panic!("{name} is not a scale of the ladder"));
        let parser = SqlParser::from_environment().unwrap();
        let prepared = tokio::runtime::Runtime::new().unwrap().block_on(prepare_scale_in(&request, index, &records, &parser, &worker)).unwrap_or_else(|e| panic!("{name}: {e}"));
        let inputs = &prepared.inputs;
        println!("{name}: {} templates prepared, {} official statements encoded, {} timed variants, {} template constants, plain storage {} bytes",
            inputs.sessions.len(), inputs.statements.official.len(), inputs.statements.variants.len(), inputs.rules.constants().constants().len(),
            inputs.general.as_ref().map_or(0, |g| g.plain_storage_bytes));
    }

    /// The library of a general-line request (path from `GENDB_GENERAL_REQUEST`) holds every seeded
    /// storage package admitted, with a stored asset for every scale's capture, so version 0's preparation and every
    /// scale move find the plain storage (otherwise `flat_storage_not_prepared`). Opens each capture (its record, receipt
    /// and file stamps; nothing decoded) and reads the library's records; no data is read.
    #[test]
    #[ignore = "reads the general-line request named by GENDB_GENERAL_REQUEST, its captures' records and its library"]
    fn general_request_library_has_every_scale_asset() {
        use gendb_storage::import::PreparedSource;
        let request = WorkloadRequest::read(Path::new(&std::env::var("GENDB_GENERAL_REQUEST").expect("GENDB_GENERAL_REQUEST"))).unwrap();
        request.validate().unwrap_or_else(|e| panic!("{e}"));
        let engine = request.engine().unwrap();
        let store = ObjectStore::open_existing(&request.library).unwrap();
        let seeded: Vec<(String, ContentId, gendb_artifacts::verus::VerusStoragePackageV1)> = engine
            .storage_seed
            .packages
            .iter()
            .map(|id| {
                let (package, _) = catalog::admitted_storage(&store, *id).unwrap_or_else(|e| panic!("{id} is not admitted in {}: {e}", request.library.display()));
                (package.name.clone(), *id, package)
            })
            .collect();
        for scale in &engine.scales {
            let view = request.at_scale(scale);
            let source = PreparedSource::open(&scale.prepared_workload, &view.dataset).unwrap_or_else(|e| panic!("{}: capture {}: {e}", scale.name, scale.prepared_workload.display()));
            let capture = CurrentCapture::of(&source).unwrap();
            let assets = gendb_storage::versions::resolve_storage_assets(&store, seeded.iter().map(|(name, id, package)| (name.as_str(), *id, package)), &capture)
                .unwrap_or_else(|e| panic!("{}: {e}", scale.name));
            let bytes: u64 = assets.iter().map(|a| a.asset.storage_bytes).sum();
            println!("{}: {} seeded storages with an asset for the capture, {bytes} stored bytes (original data {} bytes)", scale.name, assets.len(), scale.original_data_bytes);
        }
    }

    /// A relaunch of a recorded general-line run (`GENDB_GENERAL_RUN`, read only) with the request file
    /// `GENDB_GENERAL_REQUEST` is accepted by this build (a live run's relaunch with a new build): the run's
    /// request identity and budget records, copied into scratch, accept the request exactly as `open_run` checks it
    /// (a budget raise or a request change would add a record there, never in the run); and the run's engine records read: its version tree
    /// and main line, its scale ladder, every session's record and ledger, and each branch's next slot.
    #[test]
    #[ignore = "reads the general-line run named by GENDB_GENERAL_RUN and the request named by GENDB_GENERAL_REQUEST"]
    fn general_relaunch_is_accepted() {
        use super::super::branches::{LadderState, plan_slot};
        use super::super::sessions::branch_sessions;
        use super::super::tree::VersionTree;
        let run = PathBuf::from(std::env::var("GENDB_GENERAL_RUN").expect("GENDB_GENERAL_RUN"));
        let request = WorkloadRequest::read(Path::new(&std::env::var("GENDB_GENERAL_REQUEST").expect("GENDB_GENERAL_REQUEST"))).unwrap();
        request.validate().unwrap_or_else(|e| panic!("{e}"));
        let scratch = crate::controller::test_support::scratch_root("general-relaunch");
        records::create_dir(&scratch).unwrap();
        let recorded = |dir: &Path| -> Vec<String> {
            let mut names: Vec<String> = fs::read_dir(dir).unwrap().flatten().filter_map(|e| e.file_name().into_string().ok())
                .filter(|n| n == "request.json" || n == "route.json" || n.starts_with("budget-raise") || n.starts_with("request-change") || n == "validation-transition.json").collect();
            names.sort();
            names
        };
        for name in recorded(&run) {
            fs::copy(run.join(&name), scratch.join(&name)).unwrap();
        }
        record_route(&scratch, Route::Engine).unwrap();
        let existed = record_request(&scratch, &serde_json::to_value(&request).unwrap()).unwrap_or_else(|e| panic!("the relaunch is refused: {e}"));
        assert!(existed, "the run's request.json was copied");
        let new_records: Vec<String> = recorded(&scratch).into_iter().filter(|n| !run.join(n).exists()).collect();
        let engine_dir = engine_directory(&run);
        let tree = VersionTree::read(&engine_dir).unwrap();
        let ladder = LadderState::read(&engine_dir).unwrap();
        let engine = request.engine().unwrap();
        println!("request accepted; records a relaunch adds: {new_records:?}; versions {}; ladder at {}", tree.nodes.iter().filter(|n| n.accepted).count(), engine.scales[ladder.current].name);
        for branch in (1..=engine.branches.unwrap_or(1)).map(|b| format!("b{b}")) {
            let sessions = branch_sessions(&engine_dir, &branch).unwrap();
            for session in &sessions {
                let ledger: crate::controller::ledger::LedgerState = records::read_json(&RunLayout::new(&session.directory).ledger()).unwrap();
                println!("{branch} {}: open {}, {} calls, {} trials", session.directory.display(), session.open, ledger.calls.len(), ledger.trials.len());
            }
            println!("{branch} next slot: {:?}", plan_slot(&tree, &sessions, &branch).unwrap());
        }
        fs::remove_dir_all(&scratch).unwrap();
    }

    /// The seed is the latest version, else the previous round's workspace, else an empty crate; earlier versions are
    /// always carried read-only.
    #[test]
    fn seeds_follow_versions_then_rounds() {
        let dir = Path::new("/run/engine");
        let empty = EngineState { versions: vec![], rounds: vec![] };
        assert_eq!(next_seed(&empty, dir, 1).kind, SeedKind::Empty);
        let before_v1 = next_seed(&empty, dir, 3);
        assert_eq!((before_v1.kind, before_v1.from.as_deref()), (SeedKind::PreviousRound, Some(Path::new("/run/engine/rounds/round-0002/author"))));
        assert_eq!(before_v1.notes.as_deref(), Some(Path::new("/run/engine/rounds/round-0002/author/NOTES.md")));
        let state = EngineState { versions: vec![version(dir, 1, 1, false), version(dir, 2, 3, false)], rounds: vec![json!({}); 4] };
        let seed = next_seed(&state, dir, 5);
        assert_eq!((seed.kind, seed.version.as_deref(), seed.description.as_str()), (SeedKind::Version, Some("v2"), "v2 (round 3)"));
        assert_eq!(seed.from.as_deref(), Some(Path::new("/run/engine/versions/v002")));
        assert_eq!(seed.versions.iter().map(|(n, _)| n.as_str()).collect::<Vec<_>>(), ["v1", "v2"]);
    }

    /// Rounds stop at the target, the rounds guard or the cost guard; each round gets one submission and the cost left.
    #[test]
    fn stops_and_round_limits() {
        let dir = Path::new("/e");
        let guard = Limits { max_iterations: 3, max_cost_usd: Money::parse("10").unwrap(), ..limits() };
        let round = |cost: &str| json!({"outcome":"attempt","known_reported_cost_usd":cost,"cost_complete":true});
        assert_eq!(stop_reason(&EngineState { versions: vec![], rounds: vec![round("1")] }, &guard), None);
        assert_eq!(stop_reason(&EngineState { versions: vec![version(dir, 1, 1, true)], rounds: vec![round("1")] }, &guard), Some("target_met"));
        assert_eq!(stop_reason(&EngineState { versions: vec![], rounds: vec![round("1"); 3] }, &guard), Some("round_limit"));
        assert_eq!(stop_reason(&EngineState { versions: vec![], rounds: vec![round("6"), round("4")] }, &guard), Some("budget_limit"));
        let state = EngineState { versions: vec![], rounds: vec![round("2.5"), round("1.25")] };
        assert_eq!(state.spent(), (Money::parse("3.75").unwrap(), true));
        let next = round_limits(&guard, state.spent().0);
        assert_eq!((next.max_iterations, next.max_cost_usd.decimal()), (1, "6.25".to_string()));
        let unset = Limits { max_cost_usd: Money::UNSET, ..guard };
        assert!(round_limits(&unset, Money::parse("100").unwrap()).max_cost_usd.is_unset());
    }
}
