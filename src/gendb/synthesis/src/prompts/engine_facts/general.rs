//! The general engine line's data sections, rendered as Markdown from the session's prepared context
//! (`context.general`, `context.engine.training`, the refreshed `run_spend` and `library_bytes`), each evaluation's
//! record (its `next_call.context`, its race) and the run's records read when the prompt is rendered
//! ([`GeneralView::read`]): the version tree, the heads' recorded cells and profiles, the ladder and the session
//! ledgers. No raw JSON and no wide table is shown: one line per worker count, template, profiled cell or branch;
//! times in ms rounded to their size (`format::ms_rounded`), G with 3 decimals; facts only, the rules they relate to
//! stay in the instructions. Paths are named as the key paths name them (`<workspace>`, `<session>`, `<records>`, or
//! `files.<name>` in the texts a continued call shows too).
//!
//! - [`general_facts`], the head of CURRENT FACTS of a full prompt (a session's first call; a call that starts a fresh
//!   provider session inside a session leads with the session's latest evaluation): the scale, the ladder, the head's
//!   score and how long an evaluation takes at this scale ([`evaluation_time_fact`]); the totals per worker count of the
//!   main-line head and the branch head against both baselines; their per-template cells and the variants' counts; the
//!   branch head's profile ([`profile`]); the versions (or the branches with their heads and directions); the storage at
//!   this scale (the budget's numbers, the head's serving storage; the disk in one line: the library, the head's derived
//!   storage assets in it, the free space with the asset builds' floor, and what GenDB keeps); the run's budget with this
//!   session's share and submissions (the call's ledger view: the general line has no submission limit and one budget),
//!   and the provider session's context.
//! - [`branch_handoff`], HANDOFF: YOUR BRANCH SO FAR: the session's seed, the branch's previous session with its last
//!   evaluation's verdict and why it ended, a merge session's inputs, and the notebook carried into the session,
//!   verbatim.
//! - [`evaluation_section`] and [`changed_facts`], the body of a continued call (the provider session already holds
//!   the full prompt): the verdict on the latest submission with the evaluation's wall time per step and its
//!   interleaved timing per template and, for an accepted version with a recorded profile, its profile; then the facts
//!   that may have changed (the head's score, the totals, the versions, the storage, the budget and this session's
//!   context).
//! - [`resumed_facts`], the facts of a call that resumes its provider session after a stopped call: a continued call's,
//!   with the evaluation time at this scale and the provider session's context up to the stopped call.
//!
//! The evaluation time at the current scale (an evaluation at a large scale takes long) is the last evaluation of the branch's sessions timed at this scale, with its time per
//! step; before any, an estimate labelled as one, from what GenDB has recorded: the parent's recorded cells at this
//! scale (the interleaved timing runs each finished one again, 1 warm + the run's timed hot calls,
//! `general.timed_calls`) and the branch's last whole-crate Verus run.
//!
//! A run with one branch is one line of versions (`engine_general_sections::Shape::OneLine`): its
//! facts name the head (the best version so far) and the line's versions, and nothing of branches, other branches'
//! directions, merges or the main line.
//!
//! A stage run (one engine for several workloads; the context's stage view, the stage fixture) adds the facts of
//! [`stage`]: the workloads side by side, the out-of-the-box record and each kept workload's section in a full prompt;
//! the workloads' lines in a continued or resumed call; the kept workloads' outcome and races in an evaluation. The
//! sections above are the goal workload's (`engine.training`, `general.scale`). Without a stage view nothing changes.
//!
//! A run of several workloads (`engine.workloads`; the context's workloads view, the workloads fixture) adds the
//! facts of [`workloads`]: the Scale facts lead with the combined score, the workloads side by side follow the scale,
//! then the root's sides and each other workload's section in a full prompt; the workloads' lines in a continued or
//! resumed call; the combined decision and every workload's outcome and race in an evaluation. The sections above are
//! the primary workload's, their headings name it (`on `<name>``). Without a workloads view nothing changes.
//!
//! Reading only: nothing here decides, measures or writes. A record that cannot be read is named in the text instead.

use crate::controller::Trial;
use crate::prompts::engine_general_sections::{Shape, workloads_of};
use crate::controller::layout::RunLayout;
use crate::controller::ledger::LedgerState;
use crate::engine::branches::LadderState;
use crate::engine::profile::{PROFILE_DIRECTORY, PROFILE_FILE, StatementProfile};
use crate::engine::protocol::{DEFAULT_TIMED_CALLS, hot_calls_text};
use crate::engine::score::{CellResult, CellStatus};
use crate::engine::sessions::{SESSION_FILE, session_directory};
use crate::engine::tree::{self, VersionTree, node_directory};
use crate::prompts::data_sections::format::{decimal, dollars, fenced, ms_rounded, number, plain, size};
use crate::storage::asset_release::KEEP_RULE;
use gendb_runtime::worker::UnfinishedReason;
use gendb_verification::obligations::ENGINE_CRATE_NAME;
use serde_json::Value;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// The engine crate's functions listed per template in the profile facts (the version's `PROFILE.md` lists more).
const PROFILE_FUNCTIONS: usize = 3;

/// The run's records a general-line prompt is rendered from, read at the call.
#[derive(Debug, Default)]
pub struct GeneralView {
    /// `<run>/engine`.
    pub engine_dir: Option<PathBuf>,
    /// The version tree, or why it could not be read.
    pub tree: Option<VersionTree>,
    pub tree_error: Option<String>,
    pub ladder: Option<LadderState>,
    /// Recorded cells at the current scale, per version (the heads and the latest evaluated version).
    pub cells: BTreeMap<String, Vec<CellResult>>,
    /// `version.json` of the same versions.
    pub records: BTreeMap<String, Value>,
    /// The branch head's profile: `(version, report, per-statement records)`.
    pub profile: Option<(String, PathBuf, Vec<StatementProfile>)>,
    /// Entries of the findings log.
    pub findings: usize,
    /// The last evaluated submission of the branch's previous session (shown to a fresh session).
    pub previous_evaluation: Option<Value>,
    /// This session's ledger (the calls towards each submission).
    pub ledger: Option<LedgerState>,
    /// The last evaluation of the branch's sessions that was timed at the current scale.
    pub timed_here: Option<RecordedEvaluation>,
    /// The branch's last whole-crate Verus run in an evaluation, at any scale (Verus does not read the data).
    pub last_verus: Option<RecordedVerus>,
}

/// An evaluated submission read back from a session's ledger.
#[derive(Debug, Clone)]
pub struct RecordedEvaluation {
    /// The session's number in its branch, and the submission's in its session.
    pub session: u64,
    pub iteration: u32,
    /// The evaluation record (`Trial::evaluation`) and the controller's measure of its whole time.
    pub evaluation: Value,
    pub elapsed_ms: Option<u64>,
}

/// One whole-crate Verus run of an evaluation: its scale and wall time.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordedVerus {
    pub scale: String,
    pub elapsed_ms: u64,
}

/// `<run>/engine` of the session, the run's records (`context.general.files.versions` is `<run>/engine/versions`).
pub(crate) fn engine_dir(context: &Value) -> Option<PathBuf> {
    context["general"]["files"]["versions"].as_str().and_then(|p| Path::new(p).parent()).map(Path::to_path_buf)
}

/// The current scale's name.
/// The hot calls of every timed cell of the run's development timings (`general.timed_calls`, the request's
/// `engine.timed_calls`; 3 when absent).
pub(crate) fn timed_calls(context: &Value) -> u32 {
    context["general"]["timed_calls"].as_u64().and_then(|n| u32::try_from(n).ok()).unwrap_or(DEFAULT_TIMED_CALLS)
}

fn scale(context: &Value) -> String {
    plain(&context["general"]["scale"]["name"])
}

/// The branch this session works on.
fn branch(context: &Value) -> String {
    plain(&context["general"]["branch"]["name"])
}

/// The run's shape: one line when it has one branch slot (`context.general.branches`).
fn shape(context: &Value) -> Shape {
    Shape::of_context(context)
}

impl GeneralView {
    /// Read the records the facts of `context`'s session need; `evaluated` names a version the latest evaluation
    /// accepted (its cells and profile are read too).
    pub fn read(context: &Value, evaluated: Option<&str>) -> Self {
        let mut view = GeneralView { engine_dir: engine_dir(context), ..GeneralView::default() };
        let Some(dir) = view.engine_dir.clone() else {
            view.tree_error = Some("the context names no engine directory".into());
            return view;
        };
        match VersionTree::read(&dir) {
            Ok(tree) => view.tree = Some(tree),
            Err(error) => view.tree_error = Some(error.to_string()),
        }
        view.ladder = LadderState::read(&dir).ok();
        let scale = scale(context);
        let mut versions: Vec<String> = vec![];
        if let Some(tree) = &view.tree {
            versions.extend(tree.main_line_head().map(String::from));
            versions.extend(tree.branch_head(&branch(context)).map(String::from));
        }
        versions.extend(evaluated.map(String::from));
        for version in versions {
            let folder = node_directory(&dir, &version, true);
            if let Ok(text) = std::fs::read_to_string(folder.join("cells").join(format!("{scale}.json")))
                && let Ok(cells) = serde_json::from_str(&text)
            {
                view.cells.insert(version.clone(), cells);
            }
            if let Ok(text) = std::fs::read_to_string(folder.join("version.json"))
                && let Ok(record) = serde_json::from_str(&text)
            {
                view.records.insert(version, record);
            }
        }
        let profiled = evaluated.map(String::from).or_else(|| view.tree.as_ref().and_then(|t| t.branch_head(&branch(context)).map(String::from)));
        if let Some(version) = profiled {
            let folder = node_directory(&dir, &version, true);
            let mut profiles: Vec<StatementProfile> = std::fs::read_dir(folder.join(PROFILE_DIRECTORY))
                .into_iter()
                .flatten()
                .flatten()
                .filter_map(|e| std::fs::read_to_string(e.path()).ok().and_then(|t| serde_json::from_str(&t).ok()))
                .collect();
            if folder.join(PROFILE_FILE).is_file() || !profiles.is_empty() {
                profiles.sort_by(|a, b| (&a.template, a.workers).cmp(&(&b.template, b.workers)));
                view.profile = Some((version, folder.join(PROFILE_FILE), profiles));
            }
        }
        view.findings = tree::read_lines(&dir.join(tree::FINDINGS_FILE)).map_or(0, |l| l.len());
        let session_dir = context["general"]["seed_record"].as_str().and_then(|p| Path::new(p).parent()).map(Path::to_path_buf);
        view.ledger = session_dir.and_then(|d| read_ledger(&d));
        view.previous_evaluation = context["general"]["session"]["previous"].as_str().and_then(|p| read_ledger(Path::new(p))).and_then(|ledger| {
            ledger.trials.iter().rev().find(|t| !t.evaluation.is_null()).map(|t| serde_json::json!({"iteration":t.iteration,"evaluation":t.evaluation}))
        });
        (view.timed_here, view.last_verus) = branch_evaluations(&dir, &branch(context), &scale);
        view
    }

    fn head(&self, which: Head, context: &Value) -> Option<String> {
        let tree = self.tree.as_ref()?;
        match which {
            Head::MainLine => tree.main_line_head().map(String::from),
            Head::Branch => tree.branch_head(&branch(context)).map(String::from),
        }
    }
}

#[derive(Clone, Copy)]
enum Head {
    MainLine,
    Branch,
}

fn read_ledger(session_dir: &Path) -> Option<LedgerState> {
    let text = std::fs::read_to_string(RunLayout::new(session_dir).ledger()).ok()?;
    serde_json::from_str(&text).ok()
}

/// From the ledgers of `branch`'s sessions, newest first: the last evaluation timed at `scale` (its recorded score is at
/// that scale), and the last evaluation's whole-crate Verus step at any scale (with its session's scale). A session
/// whose records cannot be read is skipped.
fn branch_evaluations(engine_dir: &Path, branch: &str, scale: &str) -> (Option<RecordedEvaluation>, Option<RecordedVerus>) {
    let sessions_dir = session_directory(engine_dir, branch, 1).parent().map(Path::to_path_buf).unwrap_or_default();
    let mut sessions: Vec<PathBuf> = std::fs::read_dir(&sessions_dir).into_iter().flatten().flatten().map(|e| e.path()).filter(|p| p.join(SESSION_FILE).is_file()).collect();
    sessions.sort();
    let (mut timed, mut verus) = (None, None);
    for session in sessions.iter().rev() {
        let Some(record) = std::fs::read_to_string(session.join(SESSION_FILE)).ok().and_then(|t| serde_json::from_str::<Value>(&t).ok()) else { continue };
        let Some(ledger) = read_ledger(session) else { continue };
        for trial in ledger.trials.iter().rev() {
            let e = &trial.evaluation;
            if timed.is_none() && e["score"]["scale"] == scale {
                timed = Some(RecordedEvaluation { session: record["number"].as_u64().unwrap_or(0), iteration: trial.iteration, evaluation: e.clone(), elapsed_ms: trial.framework_elapsed_ms });
            }
            if verus.is_none()
                && let Some(ms) = e["steps"].as_array().into_iter().flatten().find(|s| s["step"] == "verus").and_then(|s| s["elapsed_ms"].as_u64())
            {
                verus = Some(RecordedVerus { scale: plain(&record["scale"]), elapsed_ms: ms });
            }
            if timed.is_some() && verus.is_some() {
                return (timed, verus);
            }
        }
    }
    (timed, verus)
}

// ------------------------------------------------------------------------------------------------ values

/// The configured worker counts.
fn workers(context: &Value) -> Vec<u64> {
    training_workers(&context["engine"]["training"])
}

/// The worker counts of training facts (`engine::facts::training_facts`).
fn training_workers(training: &Value) -> Vec<u64> {
    training["workers"].as_array().into_iter().flatten().filter_map(Value::as_u64).collect()
}

/// The call limit of every engine call, ns.
fn call_limit_ns(context: &Value) -> u64 {
    context["general"]["limits"]["call_limit_seconds"].as_u64().unwrap_or(0).saturating_mul(1_000_000_000)
}

/// A cell as the facts show it: the median in ms (rounded to its size), or why it did not finish.
fn cell_text(status: &CellStatus) -> String {
    match status {
        CellStatus::Finished { median_ns } => ms_rounded(&serde_json::json!(median_ns)),
        CellStatus::Unchecked { median_ns } => format!("{} unchecked", ms_rounded(&serde_json::json!(median_ns))),
        CellStatus::Unfinished { reason } => reason_text(*reason).to_string(),
    }
}

fn reason_text(reason: UnfinishedReason) -> &'static str {
    match reason {
        UnfinishedReason::OverTimeLimit => "time limit",
        UnfinishedReason::OverMemoryLimit => "memory limit",
        UnfinishedReason::ChildFailure => "child failed",
    }
}

/// `a / b / c` of one value per worker count.
fn per_workers(values: impl IntoIterator<Item = String>) -> String {
    values.into_iter().collect::<Vec<_>>().join(" / ")
}

/// `1 worker`, `32 workers`.
fn worker_count(w: u64) -> String {
    format!("{w} worker{}", if w == 1 { "" } else { "s" })
}

/// The faster baseline's median of `template` at the timing binding and `workers`, ns.
fn faster_baseline(template: &Value, binding: &str, workers: u64) -> Option<f64> {
    let cell = template["baselines"].as_array()?.iter().find(|c| c["binding"] == binding && c["workers"].as_u64() == Some(workers))?;
    match (number(&cell["umbra_ns"]), number(&cell["duckdb_ns"])) {
        (Some(u), Some(d)) => Some(u.min(d)),
        (one, other) => one.or(other),
    }
}

/// The saved totals of both baselines at the timing binding and `workers`: `(umbra, duckdb, target, target engine)`.
fn baseline_totals(context: &Value, workers: u64) -> Option<(Value, Value, Value, Value)> {
    baseline_totals_of(&context["engine"]["training"], workers)
}

/// [`baseline_totals`] of training facts.
fn baseline_totals_of(training: &Value, workers: u64) -> Option<(Value, Value, Value, Value)> {
    let binding = &training["timing_binding"];
    let row = training["baseline_totals"].as_array()?.iter().find(|t| &t["binding"] == binding && t["workers"].as_u64() == Some(workers))?;
    Some((row["umbra_ns"].clone(), row["duckdb_ns"].clone(), row["target_ns"].clone(), row["target_engine"].clone()))
}

/// The cell of `template` at `workers` among `cells`.
fn cell_of<'a>(cells: &'a [CellResult], template: &str, workers: u64) -> Option<&'a CellResult> {
    cells.iter().find(|c| c.template == template && c.workers as u64 == workers)
}

/// A version's total at `workers`: the sum of its cell times as the score counts them (a finished median capped at the
/// call limit, else the call limit; `None` without a cell of every template).
fn total_ns(context: &Value, cells: &[CellResult], workers: u64) -> Option<u64> {
    total_over(&context["engine"]["training"], cells, workers, call_limit_ns(context))
}

/// [`total_ns`] over the templates of training facts, with the call limit `limit_ns`.
fn total_over(training: &Value, cells: &[CellResult], workers: u64, limit_ns: u64) -> Option<u64> {
    training["templates"].as_array()?.iter().map(|t| cell_of(cells, t["name"].as_str()?, workers).map(|c| c.status.time_ns(limit_ns))).sum()
}

/// A recorded score as text: `F 12/66 finished, G 34.567` at its scale (G with 3 decimals; the record keeps 9).
fn score_text(tree: Option<&VersionTree>, version: &str, scale: &str) -> String {
    match tree.and_then(|t| t.score_at(version, scale)) {
        Some(s) => format!("F {}/{} finished, G {}{}", s.score.finished, s.cells, g_text(&s.score.normalized_time.to_string()), if s.beats_both { ", beats both baselines" } else { "" }),
        None => format!("no score recorded at {scale}"),
    }
}

/// A recorded G (normalized time, 9 decimals) with 3 decimals.
fn g_text(recorded: &str) -> String {
    decimal(&Value::String(recorded.to_string()), 3)
}

/// `path` relative to the directory the key paths name it in (`<workspace>`, `<session>`, `<records>`), else absolute:
/// for the texts only a full prompt shows (it has the key paths).
fn shown_path(context: &Value, path: &str) -> String {
    let workspace = context["files"]["workspace"].as_str().map(PathBuf::from);
    let session = workspace.as_ref().and_then(|w| w.parent()).map(Path::to_path_buf);
    let roots = [("<workspace>", workspace), ("<session>", session), ("<records>", engine_dir(context))];
    roots
        .iter()
        .find_map(|(name, root)| root.as_ref().and_then(|root| Path::new(path).strip_prefix(root).ok()).map(|rest| format!("{name}/{}", rest.display())))
        .unwrap_or_else(|| path.to_string())
}

/// `path` as the texts of a continued call can name it too (they have no key paths, and the provider session's first
/// prompt may come from an older build): under `files.versions_records` relative to it, beside it as a relative name,
/// else absolute.
fn records_path(context: &Value, path: &Path) -> String {
    let versions = context["files"]["versions_records"].as_str().map(PathBuf::from);
    if let Some(rest) = versions.as_ref().and_then(|v| path.strip_prefix(v).ok()) {
        return format!("`files.versions_records`/{}", rest.display());
    }
    match versions.as_ref().and_then(|v| v.parent()).and_then(|records| path.strip_prefix(records).ok()) {
        Some(rest) => format!("`{}` (beside `files.versions_records`)", rest.display()),
        None => format!("`{}`", path.display()),
    }
}

// ------------------------------------------------------------------------------------------------ CURRENT FACTS

/// The CURRENT FACTS head of a full prompt (module documentation): a session's first call, or a call that starts a
/// fresh provider session within the session, which also shows the session's `latest` evaluation.
pub fn general_facts(context: &Value, view: &GeneralView, latest: Option<&Trial>, ledger: &Value) -> Vec<String> {
    // The evaluation section of `latest` states its own time: the evaluation time is not repeated when it is that one.
    let time_shown = latest.is_some_and(|t| view.timed_here.as_ref().is_some_and(|here| here.session == session_number(context) && here.iteration == t.iteration));
    let evaluation = latest.map(|t| evaluation_section(context, view, t)).unwrap_or_default();
    // A run of several workloads: the combined score decides, so the workloads side by side follow the scale.
    if workloads_of(context).is_some() {
        return paragraphs([evaluation, scale_facts(context, view, !time_shown), workloads::overview(context), totals(context, view), per_template(context, view), profile(context, view, None),
            workloads::sides(context), workloads::member_sections(context), versions_or_branches(context, view), storage_facts(context, view, true),
            budget_and_session(context, view, latest, ledger, None)]);
    }
    let blocks = [evaluation, scale_facts(context, view, !time_shown), totals(context, view), per_template(context, view),
        profile(context, view, None), stage::workloads(context), stage::out_of_the_box(context), stage::kept_workloads(context), versions_or_branches(context, view),
        storage_facts(context, view, true), budget_and_session(context, view, latest, ledger, None)];
    paragraphs(blocks)
}

/// This session's number in its branch.
fn session_number(context: &Value) -> u64 {
    context["general"]["session"]["number"].as_u64().unwrap_or(0)
}

/// `ms` as minutes with one decimal: `2.2 min`.
fn minutes(ms: u64) -> String {
    format!("{:.1} min", ms as f64 / 60_000.0)
}

/// How long an evaluation takes at the current scale (module documentation), in one paragraph: the last evaluation timed
/// here with its time per step, or, before any, an estimate labelled as one.
fn evaluation_time_fact(context: &Value, view: &GeneralView) -> String {
    let name = scale(context);
    if let Some(here) = &view.timed_here {
        let which = if here.session == session_number(context) { format!("your submission {}", here.iteration) } else { format!("session {}, submission {}", here.session, here.iteration) };
        let took = evaluation_time(&here.evaluation, here.elapsed_ms).unwrap_or_else(|| "an unrecorded time".into());
        return format!("Evaluation time at {name}: the last evaluation timed here ({which}) took {took}.");
    }
    let verus = match &view.last_verus {
        Some(v) => format!("Verus on your whole crate (the last whole-crate run in an evaluation took {}, at {})", minutes(v.elapsed_ms), v.scale),
        None => "Verus on your whole crate (as long as your own whole-crate `verify`)".to_string(),
    };
    let cells_total = context["engine"]["training"]["templates"].as_array().map_or(0, Vec::len) * workers(context).len();
    let limit_s = context["general"]["limits"]["call_limit_seconds"].as_u64().unwrap_or(0);
    let parent = match shape(context) {
        Shape::OneLine => "the head",
        Shape::Branches => "your branch head",
    };
    let finished: Vec<u64> = view.head(Head::Branch, context).and_then(|h| view.cells.get(&h)).into_iter().flatten().filter_map(|c| match c.status {
        CellStatus::Finished { median_ns } | CellStatus::Unchecked { median_ns } => Some(median_ns),
        CellStatus::Unfinished { .. } => None,
    }).collect();
    // The parent's finished cells run again in the timing; its unfinished ones do not (`performance.json`). Each side of
    // a cell makes the development plan's calls (1 warm + the run's timed hot calls), each about the cell's recorded time.
    let hot = timed_calls(context);
    let calls = 1 + hot;
    let protocol = format!("1 warm + {}", hot_calls_text(hot));
    let (parent_side, yours) = match finished.iter().sum::<u64>() {
        0 => (String::new(), protocol.clone()),
        ns => (
            format!("{parent}'s {} run again, {protocol} each (about {calls} × {:.1} s = {}), and ", counted(finished.len(), "finished cell"), ns as f64 / 1e9, minutes(u64::from(calls) * ns / 1_000_000)),
            "the same way".to_string(),
        ),
    };
    let estimate = format!(
        "Evaluation time at {name}: no evaluation has been timed here yet. An estimate from GenDB's records, not a measurement: {verus}, then the interleaved timing: {parent_side}each of your {cells_total} cells runs {yours} (up to {calls} × {limit_s} s for a cell that does not finish); a storage you add is built at {name} before the timing."
    );
    // A run of several workloads: the evaluation also runs on every other workload.
    match workloads::evaluation_time_others(context) {
        Some(others) => format!("{estimate} {others}"),
        None => estimate,
    }
}

/// One evaluation's wall time in all and per step, as text: `42.3 min: Verus 12.1 min, storages 0.4 min, ...`
/// (`elapsed_ms`: the controller's measure of the whole evaluation; `None` when neither it nor the steps were
/// recorded). Steps are those `engine::acceptance` records (`evaluation.steps`); older records have none. A step under
/// 0.05 min is left out.
fn evaluation_time(evaluation: &Value, elapsed_ms: Option<u64>) -> Option<String> {
    let recorded: Vec<(&str, u64)> = evaluation["steps"].as_array().into_iter().flatten().filter_map(|s| Some((step_name(s["step"].as_str()?), s["elapsed_ms"].as_u64()?))).collect();
    let steps: Vec<String> = recorded.iter().filter(|(_, ms)| *ms >= 3_000).map(|(name, ms)| format!("{name} {}", minutes(*ms))).collect();
    let total = elapsed_ms.or_else(|| evaluation["framework_evaluation_ns"].as_u64().map(|ns| ns / 1_000_000));
    match (total, recorded.is_empty()) {
        (None, true) => None,
        // Recorded with no step: a submission refused at freeze.
        (Some(total), true) if evaluation["steps"].is_array() => Some(minutes(total)),
        (Some(total), true) => Some(format!("{} (no step times recorded)", minutes(total))),
        (total, false) if steps.is_empty() => Some(total.map_or("-".to_string(), minutes)),
        (total, false) => Some(format!("{}: {}", total.map_or("-".to_string(), minutes), steps.join(", "))),
    }
}

/// A recorded step's name as the facts show it.
fn step_name(step: &str) -> &str {
    match step {
        "verus" => "Verus",
        "verus_recorded" => "the recorded Verus run read back",
        "storages" => "storages",
        "interleaved_timing" => "interleaved timing",
        "variants" => "variants at the first scale",
        "admission" => "admission",
        "records" => "records",
        "main_line" => "main line",
        "profile" => "profile",
        other => other,
    }
}

/// The versions of the line (one line) or the branches and the version tree (several branches).
fn versions_or_branches(context: &Value, view: &GeneralView) -> Vec<String> {
    match shape(context) {
        Shape::OneLine => line_versions(context, view),
        Shape::Branches => branches(context, view),
    }
}

/// Blocks separated by one empty line (empty blocks left out).
fn paragraphs(blocks: impl IntoIterator<Item = Vec<String>>) -> Vec<String> {
    let mut lines: Vec<String> = vec![];
    for block in blocks.into_iter().filter(|b| !b.is_empty()) {
        if !lines.is_empty() {
            lines.push(String::new());
        }
        lines.extend(block);
    }
    lines
}

/// The scale, the ladder, what the next move needs, and the head's score; with `with_time`, how long an evaluation takes
/// at this scale ([`evaluation_time_fact`]).
fn scale_facts(context: &Value, view: &GeneralView, with_time: bool) -> Vec<String> {
    let general = &context["general"]["scale"];
    let name = scale(context);
    let (index, of) = (general["index"].as_u64().unwrap_or(0), general["of"].as_u64().unwrap_or(1));
    let head_name = shape(context).head();
    let moves: Vec<String> = view.ladder.iter().flat_map(|l| l.moves.iter()).map(|m| format!("to {} ({head_name} {})", plain(&m["to"]), plain(&m["main_line_head"]))).collect();
    let next = if index + 1 >= of { "This is the last scale.".to_string() } else { format!("The run moves to the next scale when the {head_name} finishes every cell here.") };
    let head = match (view.head(Head::MainLine, context), shape(context)) {
        (Some(head), Shape::OneLine) => format!("Head {head} (the best version so far): {}.", score_text(view.tree.as_ref(), &head, &name)),
        (Some(head), Shape::Branches) => format!("Main-line head {head}: {}.", score_text(view.tree.as_ref(), &head, &name)),
        (None, _) => format!("No {head_name} yet."),
    };
    // A run of several workloads: each workload stays at its scale, and the combined score is the head's.
    let sentence = workloads::scale_sentence(context)
        .unwrap_or_else(|| format!("Scale **{name}** ({} of {of} on the ladder; earlier moves: {}). {next} {head}", index + 1, if moves.is_empty() { "none".to_string() } else { moves.join(", ") }));
    let mut lines = vec!["## Scale".to_string(), String::new(), sentence];
    if with_time {
        lines.extend([String::new(), evaluation_time_fact(context, view)]);
    }
    lines
}

/// The heads whose times the facts show: the main-line head (one line: the head), and the branch head when it
/// differs.
fn heads(context: &Value, view: &GeneralView) -> Vec<(String, String)> {
    let mut heads = vec![];
    if let Some(main) = view.head(Head::MainLine, context) {
        let label = match shape(context) {
            Shape::OneLine => format!("{main} (head)"),
            Shape::Branches => format!("{main} (main line)"),
        };
        heads.push((main, label));
    }
    if let Some(head) = view.head(Head::Branch, context).filter(|h| heads.iter().all(|(v, _)| v != h)) {
        heads.push((head.clone(), format!("{head} ({} head)", branch(context))));
    }
    heads
}

/// The heads' totals: one line per worker count with both baselines' totals and the target, then each head's total,
/// finished cells and ratio to the target.
fn totals(context: &Value, view: &GeneralView) -> Vec<String> {
    let versions = heads(context, view);
    let name = scale(context);
    let binding = plain(&context["engine"]["training"]["timing_binding"]);
    let count = context["engine"]["training"]["templates"].as_array().map_or(0, Vec::len);
    let mut lines = vec![
        format!("## Score at {name}{} (binding {binding})", workloads::on_primary(context)),
        String::new(),
        format!("Totals in ms over the {count} templates (each cell's time, or the call limit when unfinished); ratio = total / the faster baseline's total (Goal)."),
        String::new(),
    ];
    for w in workers(context) {
        let (umbra, duckdb, target, engine) = baseline_totals(context, w).unwrap_or((Value::Null, Value::Null, Value::Null, Value::Null));
        let heads: Vec<String> = versions
            .iter()
            .map(|(version, label)| {
                let cells = view.cells.get(version).map(Vec::as_slice).unwrap_or_default();
                let total = total_ns(context, cells, w);
                let finished = cells.iter().filter(|c| c.workers as u64 == w && c.status.is_finished()).count();
                let ratio = total.zip(number(&target)).filter(|(_, t)| *t > 0.0).map_or("-".to_string(), |(e, t)| format!("{:.3}", e as f64 / t));
                let finished = if cells.is_empty() { "-".to_string() } else { format!("{finished}/{count}") };
                format!("{label} {}, {finished} finished, ratio {ratio}", total.map_or("-".to_string(), |t| ms_rounded(&serde_json::json!(t))))
            })
            .collect();
        let heads = if heads.is_empty() { String::new() } else { format!("; {}", heads.join("; ")) };
        // The target is the faster baseline: marked where it is one of the two, else named after them.
        let baselines = match engine.as_str() {
            Some("umbra") => format!("Umbra {} (the target), DuckDB {}", ms_rounded(&umbra), ms_rounded(&duckdb)),
            // Umbra did not time every template (a statement timed on DuckDB alone): its total does not exist.
            Some("duckdb") if umbra.is_null() => format!("DuckDB {} (the target; Umbra did not time every template)", ms_rounded(&duckdb)),
            Some("duckdb") => format!("Umbra {}, DuckDB {} (the target)", ms_rounded(&umbra), ms_rounded(&duckdb)),
            _ => format!("Umbra {}, DuckDB {}, target {} ({})", ms_rounded(&umbra), ms_rounded(&duckdb), ms_rounded(&target), plain(&engine)),
        };
        lines.push(format!("- {}: {baselines}{heads}.", worker_count(w)));
    }
    for (version, _) in &versions {
        if !view.cells.contains_key(version) {
            lines.push(String::new());
            lines.push(format!("{version} has no cells recorded at {name}."));
        }
    }
    lines
}

/// One line per template: the tables it reads, the faster baseline's medians and each head's cells; then the variants.
fn per_template(context: &Value, view: &GeneralView) -> Vec<String> {
    let training = &context["engine"]["training"];
    let binding = plain(&training["timing_binding"]);
    let counts = workers(context);
    let counts_text = per_workers(counts.iter().map(u64::to_string));
    let heads = heads(context, view);
    let labels: Vec<&str> = heads.iter().map(|(_, label)| label.as_str()).collect();
    let mut lines = vec![
        format!("## Per template at {}{}", scale(context), workloads::on_primary(context)),
        String::new(),
        format!(
            "Per template (the tables it reads): the faster baseline's saved hot median, then the recorded cell of {}, in ms at {counts_text} workers. `time limit`, `memory limit` and `child failed` did not finish (they count the call limit); `unchecked`: no saved answer to compare. SQL, parameters, every visible binding and both baselines: `files.templates`.",
            if labels.is_empty() { "no head yet".to_string() } else { labels.join(" and ") }
        ),
        String::new(),
    ];
    for t in training["templates"].as_array().into_iter().flatten() {
        let name = plain(&t["name"]);
        let tables: Vec<String> = t["tables"].as_array().into_iter().flatten().map(plain).collect();
        let mut line = format!(
            "- {name} ({}): {}",
            tables.join(", "),
            per_workers(counts.iter().map(|w| faster_baseline(t, &binding, *w).map_or("-".to_string(), |b| ms_rounded(&serde_json::json!(b)))))
        );
        for (version, _) in &heads {
            let cells = view.cells.get(version).map(Vec::as_slice).unwrap_or_default();
            line.push_str(&format!("; {version} {}", per_workers(counts.iter().map(|w| cell_of(cells, &name, *w).map_or("-".to_string(), |c| cell_text(&c.status))))));
        }
        lines.push(line);
    }
    if training["variants"]["kinds"].as_array().is_some_and(|k| !k.is_empty()) {
        lines.push(String::new());
        lines.push(format!("Variants (rule 6): {} frozen rewrites; {} have AST bytes of their own and are checked.", plain(&training["variants"]["frozen"]), plain(&training["variants"]["timed"])));
    }
    lines
}

/// The profile of `view.profile`'s version (or of `only`), one line per template: its outcome and the engine crate's
/// top functions by self time, with one share for libc and the allocator ([`ProfileParts`]). What the templates share
/// is said once: the worker count when it is the same for all, and the share of libc and the allocator with its range
/// when it leads in most templates; the templates where it does not lead show it on their line.
fn profile(context: &Value, view: &GeneralView, only: Option<&str>) -> Vec<String> {
    let Some((version, report, profiles)) = &view.profile else {
        return vec![];
    };
    if only.is_some_and(|o| o != version) {
        return vec![];
    }
    let mut lines = vec![format!("## Profile of {version}"), String::new()];
    if profiles.is_empty() {
        lines.push(format!("Report: {} (no per-template record).", records_path(context, report)));
        return lines;
    }
    let common_workers = profiles.first().map(|p| p.workers).filter(|w| profiles.iter().all(|p| p.workers == *w));
    let at = match common_workers {
        Some(w) => format!("at {}, the worker count of its largest gap to the faster baseline", worker_count(w as u64)),
        None => "at the worker count of its largest gap to the faster baseline".to_string(),
    };
    lines.push(format!(
        "Each template {at} (1 warm + 1 measured call), by sampled self time of the measured call: the engine crate's {PROFILE_FUNCTIONS} top functions, and libc and the allocator as one share (the system libraries, whose internal copy and allocation routines show no symbol, and the engine's allocation code: `__rustc::…`, `alloc::raw_vec::…`). Full report: {} (method, every call, every function; records in `{PROFILE_DIRECTORY}/` beside it).",
        records_path(context, report)
    ));
    let parts: Vec<ProfileParts> = profiles.iter().map(ProfileParts::of).collect();
    let led: Vec<usize> = (0..parts.len()).filter(|i| parts[*i].library_leads()).collect();
    let pattern = led.len() >= 2 && led.len() * 2 > parts.len();
    if pattern {
        let shares = led.iter().map(|i| parts[*i].library);
        let (low, high) = (shares.clone().min().unwrap_or(0), shares.max().unwrap_or(0));
        let others: Vec<&str> = (0..parts.len()).filter(|i| !led.contains(i)).map(|i| profiles[i].statement.as_str()).collect();
        let which = if others.is_empty() { "every template".to_string() } else { format!("{} of {} templates (all but {})", led.len(), parts.len(), others.join(", ")) };
        lines.push(String::new());
        lines.push(format!("libc and the allocator take the most samples in {which}: {}–{} of each.", share(low), share(high)));
    }
    lines.push(String::new());
    for (i, (p, part)) in profiles.iter().zip(&parts).enumerate() {
        let outcome = match &p.stopped {
            // A call stopped at the time limit ran for the call limit.
            Some(stop) if matches!(stop.reason, UnfinishedReason::OverTimeLimit) => reason_text(stop.reason).to_string(),
            Some(stop) => format!("{} after {}", reason_text(stop.reason), stop.elapsed_ns.map_or("-".to_string(), |ns| format!("{:.1} s", ns as f64 / 1e9))),
            None => p.calls.last().map_or("no call".to_string(), |c| format!("finished, {} ms", ms_rounded(&serde_json::json!(c.wall_ns)))),
        };
        let mut items: Vec<(String, u64)> = part.engine.iter().take(PROFILE_FUNCTIONS).map(|(f, s)| (format!("`{f}`"), *s)).collect();
        if part.library > 0 && !(pattern && led.contains(&i)) {
            items.push(("libc and allocator".to_string(), part.library));
        }
        items.extend(part.unsymbolized.iter().filter(|(_, s)| *s > 0).map(|(f, s)| (format!("`{f}`"), *s)));
        items.sort_by(|a, b| b.1.cmp(&a.1));
        let items: Vec<String> = items.iter().map(|(name, s)| format!("{name} {}", share(*s))).collect();
        let at = if common_workers.is_some() { String::new() } else { format!(" at {}", worker_count(p.workers as u64)) };
        lines.push(format!("- {}{at}: {outcome}; {}", p.statement, if items.is_empty() { "no samples".into() } else { items.join(", ") }));
    }
    lines
}

/// A share of a profiled call's samples, from permille: `61.8%`.
fn share(permille: u64) -> String {
    format!("{}.{}%", permille / 10, permille % 10)
}

/// One profiled call's samples as the profile facts show them, in permille of the call's samples: the engine crate's own
/// functions, one share for libc and the allocator, and the objects without any symbol table.
struct ProfileParts<'a> {
    /// The engine library's functions other than its allocation code, most samples first (standard-library code compiled
    /// into the engine, such as a `Vec` clone, included).
    engine: Vec<(&'a str, u64)>,
    /// Every sample in the system libraries ([`is_system_library`]) and in the engine's allocation code
    /// ([`is_allocation_code`]).
    library: u64,
    /// The groups of objects without a symbol table that are not system libraries (GenDB's worker executable,
    /// `[<file name>]`), by name.
    unsymbolized: Vec<(&'a str, u64)>,
}

impl<'a> ProfileParts<'a> {
    fn of(p: &'a StatementProfile) -> Self {
        let permille = |samples: u64| samples * 1000 / p.samples_taken.max(1);
        let (mut library, mut engine, mut unsymbolized) = (0, vec![], vec![]);
        for f in &p.functions {
            if is_system_library(&f.object) || is_allocation_code(&f.function) {
                library += f.self_samples;
            } else if f.function == format!("[{}]", f.object) {
                unsymbolized.push((f.function.as_str(), permille(f.self_samples)));
            } else {
                engine.push((f.function.as_str(), permille(f.self_samples)));
            }
        }
        ProfileParts { engine, library: permille(library), unsymbolized }
    }

    /// Whether libc and the allocator take more samples than any engine function and any other object.
    fn library_leads(&self) -> bool {
        self.library > 0 && self.engine.iter().chain(&self.unsymbolized).all(|(_, s)| self.library > *s)
    }
}

/// Whether `object` (a file name as a profile records it) is a system library: the C library and its kin (`libc.so.6`,
/// `libm.so.6`, `libgcc_s.so.1`), the loader (`ld-linux-x86-64.so.2`) or the kernel's vDSO. The engine library is not
/// one: built locally it is `libgendb_engine.so`; admitted, it is named by its content id.
fn is_system_library(object: &str) -> bool {
    object != format!("lib{ENGINE_CRATE_NAME}.so") && object.contains(".so") && ["lib", "ld-", "linux-vdso", "linux-gate"].iter().any(|prefix| object.starts_with(prefix))
}

/// Whether `function`, compiled into the engine library, is allocation code: Rust's allocator entry points
/// (`__rustc::__rdl_alloc`, `__rust_alloc`, ...) and the growth of vectors (`alloc::raw_vec::…`).
fn is_allocation_code(function: &str) -> bool {
    function.starts_with("__rustc::") || function.starts_with("__rdl_") || function.starts_with("__rg_") || (function.starts_with("__rust_") && function.contains("alloc"))
        || function.contains("alloc::raw_vec::") || function.starts_with("alloc::alloc::")
}

/// One line's versions: the counts, where the tree and the log are, and the last stated direction.
fn line_versions(context: &Value, view: &GeneralView) -> Vec<String> {
    let mut lines = vec!["## Versions".to_string(), String::new()];
    let Some(tree) = &view.tree else {
        lines.push(format!("The version tree could not be read: {}.", view.tree_error.as_deref().unwrap_or("unknown")));
        return lines;
    };
    let direction = context["general"]["branch"]["direction"].as_str().map(String::from).or_else(|| tree.versions().chain(tree.attempts()).filter(|n| n.direction.is_some() && n.id != tree::ROOT_VERSION).max_by_key(|n| n.created_unix_ms).and_then(|n| n.direction.clone()));
    lines.push(format!(
        "{} and {} so far (every node with its parent, score and reason: `files.tree`); {} in the findings log (`files.findings`). Last stated direction: {}.",
        counted(tree.versions().count(), "version"),
        counted(tree.attempts().count(), "attempt"),
        counted(view.findings, "entry"),
        direction.as_deref().map_or("none".to_string(), |d| d.lines().next().unwrap_or_default().to_string())
    ));
    lines
}

/// The branches: heads, versions, attempts and directions; the main-line head; where the tree and the log are.
fn branches(context: &Value, view: &GeneralView) -> Vec<String> {
    let mut lines = vec!["## Branches and the version tree".to_string(), String::new()];
    let Some(tree) = &view.tree else {
        lines.push(format!("The version tree could not be read: {}.", view.tree_error.as_deref().unwrap_or("unknown")));
        return lines;
    };
    let own = branch(context);
    let own_direction = context["general"]["branch"]["direction"].as_str().map(String::from).or_else(|| tree.of_branch(&own).filter(|n| n.direction.is_some()).max_by_key(|n| n.created_unix_ms).and_then(|n| n.direction.clone()));
    lines.push(format!(
        "Main-line head: {}. Your branch: {own}, head {}; direction: {}. In all {} and {} (`main` holds version 0 and merges; every node with its parents, kind, score and reason: `files.tree`); {} in the findings log (`files.findings`).",
        tree.main_line_head().unwrap_or("none"),
        tree.branch_head(&own).unwrap_or("none"),
        own_direction.as_deref().map_or("not stated yet (your branch's first submission states it in `direction`)".to_string(), |d| d.lines().next().unwrap_or_default().to_string()),
        counted(tree.versions().count(), "version"),
        counted(tree.attempts().count(), "attempt"),
        counted(view.findings, "entry")
    ));
    lines.push(String::new());
    for b in context["general"]["branches"].as_array().into_iter().flatten().filter_map(|b| b["branch"].as_str()) {
        let direction = tree.of_branch(b).filter(|n| n.direction.is_some()).max_by_key(|n| n.created_unix_ms).and_then(|n| n.direction.clone());
        lines.push(format!(
            "- {}: head {}, {}, {}; direction: {}",
            if b == own { format!("{b} (yours)") } else { b.to_string() },
            tree.branch_head(b).unwrap_or("-"),
            counted(tree.of_branch(b).filter(|n| n.accepted).count(), "version"),
            counted(tree.of_branch(b).filter(|n| !n.accepted).count(), "attempt"),
            direction.as_deref().map_or("not stated yet".to_string(), |d| d.lines().next().unwrap_or_default().to_string())
        ));
    }
    lines
}

/// The storage at the current scale (the rule is the instructions' Storage section): the budget for
/// a version with a storage change (the original data size) and the plain storage's size; the main-line head's serving
/// storage, and the room left when it uses changed storage; the branch head's serving storage; the disk
/// ([`disk_line`]). A continued call (`full` false) leaves out what cannot change within a session: the budget's
/// numbers (the scale stays).
fn storage_facts(context: &Value, view: &GeneralView, full: bool) -> Vec<String> {
    let general = &context["general"];
    let name = scale(context);
    let (budget, plain_bytes) = (&general["scale"]["original_data_bytes"], &general["scale"]["plain_storage_bytes"]);
    let mut lines = vec![format!("## Storage at {name}{}", workloads::on_primary(context)), String::new()];
    if full {
        lines.push(format!(
            "- Budget for a version with a storage change: the original data size, {} ({} bytes). The plain storage (allowed as is): {}, {} times the original.",
            size(budget),
            plain(budget),
            size(plain_bytes),
            times(plain_bytes, budget)
        ));
    }
    let serving = &context["storage_budget"]["used_bytes"];
    if let Some(main) = view.head(Head::MainLine, context) {
        let against = match (reads_only_plain(context), serving.as_u64(), budget.as_u64()) {
            (Some(true), _, _) => "plain storage only: allowed as is".to_string(),
            (Some(false), Some(s), Some(b)) if s > b => format!("with changed storage, above the budget by {} ({} bytes)", size(&serde_json::json!(s - b)), s - b),
            (Some(false), Some(s), Some(b)) => format!("with changed storage, room left {} ({} bytes)", size(&serde_json::json!(b - s)), b - s),
            _ => "not compared".to_string(),
        };
        let label = match shape(context) {
            Shape::OneLine => "Head",
            Shape::Branches => "Main-line head",
        };
        lines.push(format!("- {label} {main} serves {} ({} bytes), {against} (counted from the library before this call).", size(serving), plain(serving)));
    }
    if let Some(head) = view.head(Head::Branch, context).filter(|h| Some(h) != view.head(Head::MainLine, context).as_ref()) {
        let record = view.records.get(&head).map(|r| &r["storage"]).cloned().unwrap_or(Value::Null);
        lines.push(match record["serving_bytes"].is_null() {
            true => format!("- Your branch head {head}: serving storage not recorded."),
            false => format!("- Your branch head {head} serves {} ({} bytes); decision at its admission: {}.", size(&record["serving_bytes"]), plain(&record["serving_bytes"]), plain(&record["decision"])),
        });
    }
    lines.push(disk_line(context, full));
    lines
}

/// The disk in one line (`storage::asset_release`): the library's bytes and the head's derived storage
/// assets in it, the free space now with the floor every asset build leaves, and the rule of what GenDB keeps. The
/// refreshed `storage_assets` (else the prepared one) gives the head's bytes and the free space; without it, the free
/// space at preparation (full prompts only).
fn disk_line(context: &Value, full: bool) -> String {
    let general = &context["general"];
    let library = if context["library_bytes"].is_object() { &context["library_bytes"] } else { &general["library_bytes"] };
    let assets = if context["storage_assets"].is_object() { &context["storage_assets"] } else { &general["storage_assets"] };
    let mut held = if library.is_object() { format!("the run's library holds {}", size(&library["bytes"])) } else { String::new() };
    if let (Some(head), Some(assets_count)) = (assets["head"].as_str(), assets["head_derived_assets"].as_u64()) {
        let label = match shape(context) {
            Shape::OneLine => "the head",
            Shape::Branches => "the main-line head",
        };
        let part = match assets_count {
            0 => format!("{label} {head} reads no derived storage asset"),
            n => format!("{label} {head}'s derived storage assets take {} ({n} assets, every scale)", size(&assets["head_derived_bytes"])),
        };
        held = if held.is_empty() { part } else { format!("{held}, of which {part}") };
    }
    let free = &context["performance"]["free_bytes_at_prepare"];
    let room = match (assets["free_bytes"].is_number(), assets["floor_bytes"].as_u64()) {
        (true, Some(floor)) => Some(format!(
            "{} free now; an asset build needs its estimated size plus {} ({} GiB) free, else it is refused",
            size(&assets["free_bytes"]),
            size(&assets["floor_bytes"]),
            floor >> 30
        )),
        _ if full && !free.is_null() => Some(format!("{} were free when this session was prepared (not refreshed)", size(free))),
        _ => None,
    };
    let disk: Vec<String> = [Some(held).filter(|h| !h.is_empty()), room].into_iter().flatten().collect();
    let facts = if disk.is_empty() { String::new() } else { format!("{}. ", disk.join("; ")) };
    format!("- Disk: {facts}{KEEP_RULE}")
}

/// Whether the serving storage counted before this call (`context.storage_budget.used_by`) is plain storage only: every
/// counted storage one of the plain storages (`general.scale.plain_storages`); `None` when either list is missing.
fn reads_only_plain(context: &Value) -> Option<bool> {
    let plain_storages: Vec<&str> = context["general"]["scale"]["plain_storages"].as_array()?.iter().filter_map(Value::as_str).collect();
    let used_by = context["storage_budget"]["used_by"].as_array().filter(|u| !u.is_empty())?;
    Some(used_by.iter().all(|u| u["package"].as_str().is_some_and(|p| plain_storages.contains(&p))))
}

/// `bytes` as a multiple of `of`, two decimals (`-` when either is missing or `of` is 0).
fn times(bytes: &Value, of: &Value) -> String {
    match (bytes.as_u64(), of.as_u64()) {
        (Some(b), Some(o)) if o > 0 => format!("{:.2}", b as f64 / o as f64),
        _ => "-".into(),
    }
}

/// The run's budget and spend, this session's submissions and receipts, a merge session's kind, its provider context
/// (`provider_context`, else the latest evaluation's) and the calls towards the last submission. The rules (the run's
/// end, the session's end, the limits) are in the instructions.
fn budget_and_session(context: &Value, view: &GeneralView, latest: Option<&Trial>, ledger: &Value, provider_context: Option<&Value>) -> Vec<String> {
    let general = &context["general"];
    let spend = if context["run_spend"].is_object() { &context["run_spend"] } else { &general["spend"] };
    let session = &general["session"];
    let mut lines = vec!["## Budget and session".to_string(), String::new()];
    let this_session = match ledger["spent_usd"].is_null() {
        true => String::new(),
        false => format!(" ({} of it by this session's earlier calls{})", dollars(&ledger["spent_usd"]), if ledger["spent_complete"] == false { ", a receipt without a cost" } else { "" }),
    };
    // The run's reservations include this call's own stop guard (it has no receipt yet); only the other calls in flight
    // are worth stating.
    let others_in_flight = number(&spend["reserved_usd"]).unwrap_or(0.0) - number(&ledger["this_call"]["stop_guard_usd"]).unwrap_or(0.0);
    let one_line = shape(context) == Shape::OneLine;
    lines.push(format!(
        "- Run budget: {} of provider-reported cost for {}. Spent so far: {}{this_session}; left: {}{}.",
        dollars(&spend["budget_usd"]),
        if one_line { "every call of the run" } else { "every branch's calls together" },
        dollars(&spend["spent_usd"]),
        dollars(&spend["left_usd"]),
        if others_in_flight >= 0.01 { format!("; calls of other sessions in flight hold {} until their receipts settle", dollars(&serde_json::json!(others_in_flight))) } else { String::new() }
    ));
    let submissions = &ledger["submissions"];
    if submissions.is_object() {
        let uncounted: Vec<String> = submissions["not_counted_framework_failures"].as_array().into_iter().flatten().map(plain).collect();
        lines.push(format!(
            "- Submissions this session: {} (no limit){}. Every call's receipt: `ledger.json` in this session's directory.",
            plain(&submissions["used"]),
            if uncounted.is_empty() { String::new() } else { format!("; framework failures, not counted: {}", uncounted.join(", ")) }
        ));
    }
    if !one_line && session["kind"] == "merge" {
        lines.push(format!("- This session is a merge session taking the gains of {} into the main line.", plain(&session["merge_from"])));
    }
    let context_now = provider_context.or_else(|| latest.map(|t| &t.evaluation["next_call"]["context"])).filter(|c| c.is_object());
    lines.push(match context_now {
        Some(c) => format!(
            "- This provider session so far: {}; context {} tokens at the last turn, {} at the peak; {} automatic compactions.",
            counted(c["calls"].as_array().map_or(0, Vec::len), "call"),
            plain(&c["context_tokens"]),
            plain(&c["peak_context_tokens"]),
            plain(&c["compactions"])
        ),
        None => "- This provider session: the first call.".to_string(),
    });
    if let Some((calls, author_ms, cost)) = latest.and_then(|t| iteration_spend(view, t.iteration)) {
        lines.push(format!("- Towards your last submission: {}, {:.1} min of author time, {} provider-reported.", counted(calls, "call"), author_ms as f64 / 60_000.0, dollars(&serde_json::json!(cost))));
    }
    lines
}

/// `n` things: `1 call`, `2 calls`, `1 entry`, `2 entries`.
fn counted(n: usize, thing: &str) -> String {
    match (n, thing.strip_suffix('y')) {
        (1, _) => format!("{n} {thing}"),
        (_, Some(stem)) => format!("{n} {stem}ies"),
        _ => format!("{n} {thing}s"),
    }
}

/// The calls towards submission `iteration` in this session's ledger: `(calls, author ms, counted dollars)`.
fn iteration_spend(view: &GeneralView, iteration: u32) -> Option<(usize, u64, String)> {
    let ledger = view.ledger.as_ref()?;
    let mut cost = crate::controller::limits::Money::default();
    let (mut calls, mut elapsed) = (0, 0);
    for (call, counted) in ledger.calls.iter().zip(ledger.counted_usage()).filter(|(c, _)| c.iteration == iteration) {
        calls += 1;
        elapsed += call.receipt.as_ref().map_or(0, |r| r.elapsed_ms);
        if let Some(c) = counted.cost {
            cost = cost.checked_sum(c).ok()?;
        }
    }
    (calls > 0).then(|| (calls, elapsed, cost.decimal()))
}

// ------------------------------------------------------------------------------------------------ the handoff

/// HANDOFF: YOUR BRANCH SO FAR (module documentation; one line: HANDOFF: YOUR WORK SO FAR): shown on the first call
/// of every session.
pub fn branch_handoff(context: &Value, view: &GeneralView) -> Vec<String> {
    let general = &context["general"];
    let session = &general["session"];
    if shape(context) == Shape::OneLine {
        return line_handoff(context, view);
    }
    let mut lines = vec![
        "# HANDOFF: YOUR BRANCH SO FAR".to_string(),
        String::new(),
        format!(
            "Your workspace starts from {}: its code, manifest and storages, with read-only copies of the versions you work from in `files.versions`. GenDB's facts above are authoritative; the notebook is your branch's memory.",
            plain(&session["seed"])
        ),
        String::new(),
    ];
    lines.extend(previous_session(context, view, "The branch's previous session", "This is the branch's first session."));
    let merge = &general["seeded"]["merge"];
    if merge.is_object() {
        lines.push(format!(
            "- **Merge session.** You take the gains of the branch head {} into the main line: your workspace is the main-line head {}; the branch head's code is under `versions/{}/code`, their newest common ancestor's under `versions/{}/code`; the branch's notebook is `merge/branch-NOTES.md`; `merge/README.md` says the rest. A submission is judged against the main-line head; an accepted merge becomes the main-line head and ends this session.",
            plain(&merge["branch_head"]),
            plain(&merge["main_line_head"]),
            plain(&merge["branch_head"]),
            plain(&merge["merge_base"])
        ));
    }
    if general["branch"]["direction_required"] == true {
        lines.push("- Your branch has not stated a direction: your first submission states it (`direction`), different from the other branches' directions.".to_string());
    }
    lines.extend(carried_notebook(context));
    lines
}

/// HANDOFF: YOUR WORK SO FAR of one line: the seed (the head when the session started), the previous session and its
/// last evaluation, and the notebook carried into the session.
fn line_handoff(context: &Value, view: &GeneralView) -> Vec<String> {
    let session = &context["general"]["session"];
    let mut lines = vec![
        "# HANDOFF: YOUR WORK SO FAR".to_string(),
        String::new(),
        format!(
            "Your workspace starts from {}, the head when this session started: its code, manifest and storages, with read-only copies of the versions you work from in `files.versions`. GenDB's facts above are authoritative; the notebook is the line's memory.",
            plain(&session["seed"])
        ),
        String::new(),
    ];
    lines.extend(previous_session(context, view, "The previous session", "This is the first session."));
    lines.extend(carried_notebook(context));
    lines
}

/// Where the previous session is, its last evaluation's verdict, and why it ended; `first` when there was none. How
/// long an evaluation takes at this scale is in the Scale facts ([`evaluation_time_fact`]).
fn previous_session(context: &Value, view: &GeneralView, previous_label: &str, first: &str) -> Vec<String> {
    let Some(previous) = context["general"]["session"]["previous"].as_str() else {
        return vec![format!("- {first}")];
    };
    let mut lines = vec![format!("- {previous_label}: `{}` (its calls with their prompts and local jobs under `calls/`, its submissions under `iterations/`).", shown_path(context, previous))];
    lines.push(match &view.previous_evaluation {
        Some(last) => format!("- Its last evaluation (submission {}): {}.", plain(&last["iteration"]), verdict_line(&last["evaluation"])),
        None => "- It ended without an evaluated submission.".to_string(),
    });
    if let Some(end) = view.previous_evaluation.as_ref().and_then(|last| last["evaluation"]["next_call"]["session_end"].as_str()) {
        lines.push(format!("- Why it ended: {end}."));
    }
    lines
}

/// The notebook carried into the session, verbatim.
fn carried_notebook(context: &Value) -> Vec<String> {
    let seeded = &context["general"]["seeded"];
    let mut lines = vec![String::new(), "## Notebook carried into this session".to_string(), String::new()];
    match seeded["notes_text"].as_str() {
        Some(text) => {
            let from = seeded["notes_from"].as_str().map_or_else(|| plain(&seeded["notes_from"]), |p| shown_path(context, p));
            lines.push(format!("`NOTES.md` (`files.notes`) as this session started, from `{from}`:"));
            lines.push(String::new());
            lines.extend(fenced("markdown", text));
        }
        None => lines.push("(no NOTES.md was carried)".to_string()),
    }
    lines
}

/// One evaluation in one line: accepted as which version, or the attempt and why.
fn verdict_line(evaluation: &Value) -> String {
    match (evaluation["accepted"].as_bool(), evaluation["node"].as_str()) {
        (Some(true), Some(node)) => format!("accepted as {node} ({})", score_of(evaluation)),
        (Some(false), Some(node)) => format!("not accepted, recorded as attempt {node}: {}", first_line(&evaluation["error"])),
        _ => format!("{}: {}", plain(&evaluation["status"]), first_line(&evaluation["error"])),
    }
}

/// An evaluation's recorded score as text.
fn score_of(evaluation: &Value) -> String {
    let s = &evaluation["score"];
    if s.is_object() { format!("F {}/{} at {}, G {}", plain(&s["score"]["finished"]), plain(&s["cells"]), plain(&s["scale"]), decimal(&s["score"]["normalized_time"], 3)) } else { "no score".into() }
}

fn first_line(value: &Value) -> String {
    plain(value).lines().next().unwrap_or("-").to_string()
}

// ------------------------------------------------------------------------------------------------ a continued call

/// The verdict on the latest submission with its interleaved timing and (accepted) its profile.
pub fn evaluation_section(context: &Value, view: &GeneralView, trial: &Trial) -> Vec<String> {
    let e = &trial.evaluation;
    let one_line = shape(context) == Shape::OneLine;
    let mut lines = vec![format!("## Submission {}: {}", trial.iteration, verdict_line(e)), String::new()];
    let race = e["directory"].as_str().map(|d| Path::new(d).join("race.json")).and_then(|p| std::fs::read_to_string(&p).ok()).and_then(|t| serde_json::from_str::<Value>(&t).ok());
    let parents = (!e["parents"].is_null()).then(|| e["parents"].as_array().into_iter().flatten().map(plain).collect::<Vec<_>>().join(", "));
    let timing = race.as_ref().map(|race| {
        format!(
            "interleaved timing{} at {}: parent F {}, G {}; yours F {}, G {} (of {} cells)",
            workloads::on_primary(context),
            scale(context),
            plain(&race["parent_score"]["score"]["finished"]),
            decimal(&race["parent_score"]["score"]["normalized_time"], 3),
            plain(&race["candidate_score"]["score"]["finished"]),
            decimal(&race["candidate_score"]["score"]["normalized_time"], 3),
            plain(&race["candidate_score"]["cells_total"])
        )
    });
    match (parents, timing) {
        (Some(parents), timing) => {
            let parent = if one_line { format!("- Parent {parents}") } else { format!("- Parent {parents} (branch {})", plain(&e["branch"])) };
            lines.push(timing.map_or(format!("{parent}."), |t| format!("{parent}; {t}.")));
        }
        (None, Some(timing)) => lines.push(format!("- The {timing}.")),
        (None, None) => {}
    }
    // A run of several workloads: the combined decision and every workload's outcome.
    lines.extend(workloads::evaluation_lines(context, e));
    if e["accepted"] == false && !e["error"].is_null() {
        lines.push("- Why it was not accepted (the full text is under LATEST FEEDBACK):".to_string());
        lines.push(String::new());
        lines.extend(fenced("text", &plain(&e["error"]).lines().take(12).collect::<Vec<_>>().join("\n")));
        lines.push(String::new());
    }
    if e["flagged_for_root"] == true {
        lines.push("- Flagged for the operator review: an answer did not agree with the saved answers.".to_string());
    }
    if e["status"] != "version_accepted" && e["status"] != "attempt" {
        lines.push(format!("- Status `{}`: the framework could not judge this submission; it is not counted against you and is evaluated again.", plain(&e["status"])));
    }
    let main_line = &e["main_line"];
    if main_line.is_object() {
        lines.push(match (one_line, main_line["changed"] == true) {
            (true, true) => format!("- {} is now the head, the best version so far; your next submission builds on it.", plain(&main_line["head"])),
            (true, false) => format!("- The head is unchanged: {}.", plain(&main_line["head"])),
            (false, changed) => format!(
                "- Main line: {} ({}).",
                if changed { format!("{} is now the main-line head", plain(&main_line["head"])) } else { format!("unchanged, head {}", plain(&main_line["head"])) },
                plain(&main_line["reason"])
            ),
        });
    }
    if let Some(took) = evaluation_time(e, trial.framework_elapsed_ms) {
        lines.push(format!("- GenDB's evaluation took {took}."));
    }
    if let Some(directory) = e["directory"].as_str() {
        lines.push(format!(
            "- Records: {} ({}).",
            records_path(context, Path::new(directory)),
            if e["accepted"] == true { "version.json, race.json, cells/, variant-answers.json" } else { "attempt.json, race.json when timed" }
        ));
    }
    if let Some(race) = &race {
        lines.push(String::new());
        let mut table = race_table(context, race);
        // A run of several workloads: this table is the primary workload's.
        if let (Some(heading), primary) = (table.first_mut(), workloads::on_primary(context))
            && !primary.is_empty()
        {
            *heading = format!("{heading}{primary} at {}", scale(context));
        }
        lines.extend(table);
    }
    lines.extend(workloads::evaluation_tables(context, e));
    let kept = stage::kept_evaluation(context, e);
    if !kept.is_empty() {
        lines.push(String::new());
        lines.extend(kept);
    }
    if e["accepted"] == true {
        let profile = profile(context, view, e["node"].as_str());
        if !profile.is_empty() {
            lines.push(String::new());
            lines.extend(profile);
        }
    }
    lines
}

/// The interleaved timing per template: parent and candidate cells and their ratio at every worker count, one line each.
fn race_table(context: &Value, race: &Value) -> Vec<String> {
    let counts = workers(context);
    let counts_text = per_workers(counts.iter().map(u64::to_string));
    let pairs = race["pairs"].as_array().cloned().unwrap_or_default();
    let side = |pair: Option<&Value>, which: &str| -> String {
        let Some(pair) = pair else { return "-".into() };
        let status: Option<CellStatus> = serde_json::from_value(pair[which]["status"].clone()).ok();
        let text = status.as_ref().map_or("-".to_string(), cell_text);
        let text = if pair[which]["source"] == "parent_record" { format!("{text} (recorded)") } else { text };
        if pair["retimed"].is_object() { format!("{text} (re-timed)") } else { text }
    };
    let loads: Vec<f64> = pairs.iter().filter_map(|p| number(&p["load_average"]["one_minute"])).collect();
    let load = match (loads.iter().cloned().reduce(f64::min), loads.iter().cloned().reduce(f64::max)) {
        (Some(lo), Some(hi)) => format!(" The 1-minute load average before the pairs was between {lo:.2} and {hi:.2}."),
        _ => String::new(),
    };
    let retimed = pairs.iter().filter(|p| p["retimed"].is_object()).count();
    let retimed = match retimed {
        0 => String::new(),
        n => format!(" `(re-timed)`: {n} pair{} timed again once at the end, because a side was much slower than the parent's recorded time (the host is shared with other services); the re-timed result counts, and the first is kept in race.json.", if n == 1 { " was" } else { "s were" }),
    };
    // 2 calls: also races recorded under the earlier development cell (1 warm + 1 hot); more: 1 warm call and the run's
    // timed hot calls (`engine.timed_calls`, by default 3 as the final plan's), the median.
    let cell_time = match race["calls_per_cell"].as_u64() {
        Some(2) => "each side 1 warm + 1 hot call, the hot call's time the cell's time".to_string(),
        Some(calls) if calls > 2 => format!("each side 1 warm + {} hot calls, the median hot call the cell's time", calls - 1),
        _ => "the median hot call per cell".to_string(),
    };
    let mut lines = vec![
        "## Interleaved timing per template".to_string(),
        String::new(),
        format!(
            "Per template, ms at {counts_text} workers: parent {} → yours (yours / parent; below 1 is faster). One window, the two sides of a cell back to back ({cell_time}). `(recorded)`: not run again, the parent's record at this scale.{load}{retimed} Full record: `race.json` in the records above.",
            plain(&race["parent"])
        ),
        String::new(),
    ];
    for name in context["engine"]["training"]["templates"].as_array().into_iter().flatten().map(|t| plain(&t["name"])) {
        let pair = |w: u64| pairs.iter().find(|p| p["template"] == name.as_str() && p["workers"].as_u64() == Some(w));
        lines.push(format!(
            "- {name}: {} → {} ({})",
            per_workers(counts.iter().map(|w| side(pair(*w), "parent"))),
            per_workers(counts.iter().map(|w| side(pair(*w), "candidate"))),
            per_workers(counts.iter().map(|w| pair(*w).and_then(|p| number(&p["candidate_over_parent"])).map_or("-".to_string(), ratio_text)))
        ));
    }
    lines
}

/// A cell ratio (yours / parent) with 2 decimals, or 3 below 0.1 so a large gain still shows.
fn ratio_text(ratio: f64) -> String {
    if ratio < 0.1 { format!("{ratio:.3}") } else { format!("{ratio:.2}") }
}

/// The facts of a continued call that may have changed since the session's first prompt: the scale and the head's
/// score, the heads' totals, the versions (or the branches), the storage, and the budget with this session's context.
/// The evaluation time is not repeated: the evaluation section states the latest one's.
pub fn changed_facts(context: &Value, view: &GeneralView, latest: Option<&Trial>, ledger: &Value) -> Vec<String> {
    paragraphs([scale_facts(context, view, false), workloads::overview(context), totals(context, view), stage::workloads(context), versions_or_branches(context, view),
        storage_facts(context, view, false), budget_and_session(context, view, latest, ledger, None)])
}

/// The facts of a call that resumes its provider session after a stopped call: a continued call's, with the evaluation
/// time at this scale, and the provider session's context up to the stopped call (`provider_context`, as
/// `engine::sessions::ProviderContext` serializes it) in place of the latest evaluation's.
pub fn resumed_facts(context: &Value, view: &GeneralView, latest: Option<&Trial>, ledger: &Value, provider_context: &Value) -> Vec<String> {
    paragraphs([scale_facts(context, view, true), workloads::overview(context), totals(context, view), stage::workloads(context), versions_or_branches(context, view),
        storage_facts(context, view, false), budget_and_session(context, view, latest, ledger, Some(provider_context))])
}

pub(crate) mod stage;
pub(crate) mod workloads;

#[cfg(test)]
pub(crate) mod tests;
