//! `gendb engine re-evaluate REQUEST RUN_DIR ATTEMPT` (run by the operator, never automatically): the development
//! evaluation of a recorded attempt again, for an attempt whose interleaved timing was decided by load from other
//! services on the shared host (in one run the parent itself went over the call limit on four cells it had finished
//! in 10–50 s before; re-timing keeps the feedback to the authors right).
//!
//! What it reuses and what it runs ([`ReEvaluationPlan`]; `EngineBench::re_evaluate_attempt`):
//! - only an attempt that the score decision refused (`not better than its parent`, step 5 of `engine::acceptance`) at
//!   the run's current scale, on a branch (not a merge), whose parent is still the branch head or the main-line head;
//! - the frozen crate's whole-crate Verus run recorded at its first evaluation (`verus-build/run.json` and the library;
//!   `engine::submission::EngineBuilds::recorded`): no second Verus run;
//! - its recorded race (`race.json` of the first evaluation): the suspicious pairs of the re-timing rule
//!   (`engine::race::suspicion`) are timed again once, each after the quiet-moment gate and under one timing lease, the
//!   order alternating across them; every other pair is kept as recorded (each pair is interleaved on its own, so each
//!   stays a fair comparison); both scores are computed again over the result (`engine::race::retime_recorded`);
//! - the storages are resolved and checked again (cheap; the plain storage reads only existing assets), and when the
//!   attempt is now better the variants run as in every evaluation (an attempt refused at step 5 never ran them);
//! - now better: it is admitted as the next version exactly as an accepted submission is (the admission intent and the
//!   admission beside the frozen submission, the version folder, the main-line head, the findings entry, the verdict);
//!   its `version.json` names the re-evaluation (`re_evaluation`);
//! - still not better (or refused later): the attempt keeps its node, and its folder gets the new result
//!   (`re-evaluation.json`, and `re_evaluations` in `attempt.json`).
//!
//! Either way the branch's next author call is told, by an operator note written for the branch (`engine::operator_note`,
//! `by: re_evaluation`): what was re-timed, why, and the result. Records go under the frozen submission's
//! `re-evaluation[-N]/` (`race.json`, `race/retime/...`, the storages, the variants, [`RE_EVALUATION_FILE`]).
//!
//! **The controller must be stopped** (the simpler safe option): the command refuses while a controller launch of the
//! run is alive (`gendb_runtime::process_stop::live_launches`), and holds the attempt's session lock
//! (`<session>/controller.lock`, the controller's own run lock of that session) for its whole run, so a controller
//! started meanwhile cannot resume that session. The operator stops the run (SIGTERM), re-evaluates, then relaunches. Every
//! write a normal acceptance makes is made under the same library and main-line locks.

use super::acceptance::{NOT_BETTER_REASON, ReEvaluated, StepTimes, fresh_directory};
use super::branches::{LadderState, branch_names, framework_error, open_run, session_bench};
use super::operator_note::write_note;
use super::race::{RACE_RULE, RecordedRace};
use super::role::{EngineAuthorRole, EngineRoleConfig, EngineRoleMode, FirstScale, SessionConfig};
use super::rounds::{engine_directory, prepare_engine_scale};
use super::sessions::{RunSpend, SESSION_FILE, SessionRecord};
use super::tree::{NodeKind, TreeNode, VersionTree, node_directory};
use crate::controller::layout::RunLayout;
use crate::controller::records::{now_unix_ms, read_json, write_json_atomic};
use crate::controller::request::WorkloadRequest;
use crate::controller::workload_run::WorkloadError;
use crate::file_lock::FileLock;
use gendb_frontend::parser::SqlParser;
use serde_json::{Value, json};
use std::fs;
use std::path::{Path, PathBuf};

/// The record of one re-evaluation, in its directory and (the latest) in the attempt's folder.
pub const RE_EVALUATION_FILE: &str = "re-evaluation.json";

/// A recorded attempt that can be re-evaluated (module documentation), and where its records are.
#[derive(Clone, Debug, PartialEq)]
pub struct ReEvaluationPlan {
    /// The attempt's id (`b1-a003`), its node and its folder (`engine/attempts/<id>`).
    pub attempt: String,
    pub node: TreeNode,
    pub folder: PathBuf,
    /// The session and the frozen submission (`<session>/iterations/NNNN/frozen`).
    pub session: PathBuf,
    pub frozen_dir: PathBuf,
    /// The first evaluation's directory, its race and its Verus build directory.
    pub evaluation: PathBuf,
    pub race: PathBuf,
    pub build: PathBuf,
    /// The version the first evaluation timed it against.
    pub parent: String,
}

impl ReEvaluationPlan {
    /// The plan of re-evaluating `attempt` of the run in `engine_dir` at the run's current scale `scale`: refused (with
    /// the reason) unless it is an attempt of a branch session that the score decision refused at `scale`, with its
    /// first evaluation's race and Verus build on record and that race timed against its one parent.
    pub fn read(engine_dir: &Path, attempt: &str, scale: &str) -> Result<Self, String> {
        let folder = node_directory(engine_dir, attempt, false);
        let attempt_file = folder.join("attempt.json");
        let recorded: Value = read_json(&attempt_file).map_err(|e| format!("{attempt} is not a recorded attempt of this run: {e}"))?;
        let node: TreeNode = serde_json::from_value(recorded["node"].clone()).map_err(|e| format!("{}: {e}", attempt_file.display()))?;
        let reason = node.reason.clone().unwrap_or_default();
        if node.id != attempt || node.accepted {
            return Err(format!("{}: the record is not attempt {attempt}", attempt_file.display()));
        }
        if !reason.starts_with(NOT_BETTER_REASON) {
            return Err(format!("only an attempt that its interleaved timing judged not better can be re-evaluated; {attempt} was refused for another reason: {}", reason.lines().next().unwrap_or("-")));
        }
        if node.kind != NodeKind::Branch {
            return Err(format!("{attempt} is a merge attempt; a merge is judged in its own session (an accepted merge ends it), so it is not re-evaluated"));
        }
        if node.scale != scale {
            return Err(format!("{attempt} was timed at {}; the run is at {scale} now, where its race is not comparable", node.scale));
        }
        let [parent] = node.parents.as_slice() else { return Err(format!("{attempt} has {} parents; a branch attempt has one", node.parents.len())) };
        let session = node.session.clone().ok_or_else(|| format!("{attempt} names no session"))?;
        let evaluation = PathBuf::from(recorded["evaluation"].as_str().ok_or_else(|| format!("{}: no `evaluation`", attempt_file.display()))?);
        let frozen_dir = evaluation.parent().map(Path::to_path_buf).ok_or_else(|| format!("{}: not an evaluation directory", evaluation.display()))?;
        let (race, build) = (evaluation.join("race.json"), evaluation.join("verus-build"));
        for (what, path) in [("its race", &race), ("its Verus run", &build.join("run.json")), ("its frozen candidate", &frozen_dir.join("candidate.json")), ("its session", &session.join(SESSION_FILE))] {
            if !path.is_file() {
                return Err(format!("{attempt}: {what} is not on record ({})", path.display()));
            }
        }
        let timed_against = RecordedRace::read(&race)?.parent;
        if timed_against != *parent {
            return Err(format!("{}: the race timed {attempt} against {timed_against}, not its parent {parent}", race.display()));
        }
        Ok(Self { attempt: attempt.into(), parent: parent.clone(), node, folder, session, frozen_dir, evaluation, race, build })
    }

    /// The parent must still be a head the version would build on (the branch head, or the main-line head): a version
    /// admitted under a head that moved on would replace the newer versions' line.
    pub fn check_parent(&self, tree: &VersionTree) -> Result<(), String> {
        let (branch_head, main_line_head) = (tree.branch_head(&self.node.branch), tree.main_line_head());
        if branch_head == Some(self.parent.as_str()) || main_line_head == Some(self.parent.as_str()) {
            return Ok(());
        }
        Err(format!("{}'s parent {} is no longer a head (branch {} head {}, main-line head {}): it is not re-evaluated", self.attempt, self.parent, self.node.branch,
            branch_head.unwrap_or("-"), main_line_head.unwrap_or("-")))
    }

    /// What a version admitted by this re-evaluation records about it (`version.json` `re_evaluation`).
    pub fn record(&self, dir: &Path) -> Value {
        json!({"attempt":self.attempt,"attempt_folder":self.folder,"first_evaluation":self.evaluation,"first_race":self.race,"evaluation":dir,
            "meaning":"admitted by gendb engine re-evaluate: the attempt's recorded race with its suspicious pairs timed again (engine::race), its recorded Verus run reused"})
    }
}

/// The re-evaluation of `attempt` (module documentation). Returns its record.
pub async fn re_evaluate(request: &WorkloadRequest, run_dir: &Path, attempt: &str, framework_executable: &Path) -> Result<Value, WorkloadError> {
    let (root, engine) = open_run(request, run_dir)?;
    if let Some(launch) = gendb_runtime::process_stop::live_launches(&root).map_err(WorkloadError::invalid)?.last() {
        return Err(WorkloadError::invalid(format!(
            "the run's controller is running (pid {}, launch {}): stop it (SIGTERM to that pid), re-evaluate, then relaunch it",
            launch.pid, launch.id
        )));
    }
    let engine_dir = engine_directory(&root);
    let ladder = LadderState::read(&engine_dir)?;
    let scale = engine.scales[ladder.current].name.clone();
    let plan = ReEvaluationPlan::read(&engine_dir, attempt, &scale).map_err(WorkloadError::invalid)?;
    let _session = hold_session(&plan.session).map_err(WorkloadError::invalid)?;
    // A re-evaluation that admitted (or meant to admit) the attempt already is finished from its records, whatever
    // the heads are now.
    let admitted_before = ["admitting.json", "admitted.json"].iter().any(|f| plan.frozen_dir.join(f).is_file());
    if !admitted_before {
        plan.check_parent(&VersionTree::read(&engine_dir)?).map_err(WorkloadError::invalid)?;
    }
    let parser = SqlParser::from_environment().map_err(WorkloadError::Frontend)?;
    let prepared = prepare_engine_scale(request, ladder.current, &root, &parser, framework_executable).await?;
    let first_scale = match ladder.current {
        0 => None,
        _ => Some(FirstScale::of(&prepare_engine_scale(request, 0, &root, &parser, framework_executable).await?)),
    };
    let record: SessionRecord = read_json(&plan.session.join(SESSION_FILE))?;
    let config = EngineRoleConfig {
        engine_dir: engine_dir.clone(),
        inputs: prepared.inputs.clone(),
        mode: EngineRoleMode::Session(SessionConfig {
            record,
            directory: plan.session.clone(),
            spend: RunSpend::new(&engine_dir, engine.limits.max_cost_usd),
            prompt: crate::prompts::engine_policy::general_author_prompt,
            first_scale,
        }),
    };
    let mut role = EngineAuthorRole::new(session_bench(request, &prepared).map_err(framework_error)?, config);
    let started_unix_ms = now_unix_ms();
    let dir = fresh_directory(&plan.frozen_dir, "re-evaluation").map_err(framework_error)?;
    let mut steps = StepTimes::default();
    let outcome = {
        let mut view = role.view();
        view.bench.open_workspace(&RunLayout::new(&plan.session).workspace()).map_err(framework_error)?;
        view.re_evaluate_attempt(&dir, &plan, &mut steps).map_err(framework_error)?
    };
    let mut record = outcome_record(&plan, &dir, &outcome, &steps, started_unix_ms);
    VersionTree::read(&engine_dir)?.write_views(&engine_dir, &branch_names(engine.branches.unwrap_or(1)))?;
    // The branch's next call is told, once (a finished earlier re-evaluation told it already).
    if !matches!(outcome, ReEvaluated::Admitted { already: true, .. }) {
        let note = write_note(&engine_dir, &plan.node.branch, &note_text(&plan, &record), "re_evaluation")?;
        record["operator_note"] = json!(note);
    }
    write_json_atomic(&dir.join(RE_EVALUATION_FILE), &record)?;
    record_in_attempt(&plan, &record)?;
    crate::output::engine::general::write_general_output(request, &root, &engine_dir);
    Ok(record)
}

/// Hold the session's own run lock (`controller.lock`, which a controller holds while it runs the session) until
/// dropped; refused when held.
pub(super) fn hold_session(session: &Path) -> Result<FileLock, String> {
    let path = session.join("controller.lock");
    let file = fs::OpenOptions::new().read(true).write(true).create(true).truncate(false).open(&path).map_err(|e| format!("{}: {e}", path.display()))?;
    FileLock::acquire(file, libc::LOCK_EX | libc::LOCK_NB).map_err(|_| format!("{} is held: a controller runs this session; stop it first", path.display()))
}

/// The re-evaluation's record: what was reused, what was timed again and why, the steps, and the result.
fn outcome_record(plan: &ReEvaluationPlan, dir: &Path, outcome: &ReEvaluated, steps: &StepTimes, started_unix_ms: u64) -> Value {
    let race_file = dir.join("race.json");
    let race: Value = read_json(&race_file).unwrap_or(Value::Null);
    let retimed: Vec<Value> = race["pairs"].as_array().into_iter().flatten().filter(|p| p["retimed"].is_object())
        .map(|p| json!({"template":p["template"],"workers":p["workers"],"reason":p["retimed"]["reason"],
            "first":{"parent":p["retimed"]["first_pass"]["parent"]["status"],"candidate":p["retimed"]["first_pass"]["candidate"]["status"]},
            "now":{"parent":p["parent"]["status"],"candidate":p["candidate"]["status"]}}))
        .collect();
    let mut record = json!({"format_version":1,"attempt":plan.attempt,"branch":plan.node.branch,"iteration":plan.node.iteration,"parent":plan.parent,"scale":plan.node.scale,
        "directory":dir,"first_evaluation":plan.evaluation,"first_race":plan.race,"race":race.is_object().then_some(&race_file),
        "scores":race.is_object().then(|| json!({"parent":race["parent_score"]["score"],"candidate":race["candidate_score"]["score"],"candidate_better":race["candidate_better"]})),
        "retimed_pairs":retimed.len(),"retimed":retimed,"reused":{"verus":plan.build.join("run.json"),"race_pairs":race["reused"]},
        "steps":steps.record(),"started_unix_ms":started_unix_ms,"ended_unix_ms":now_unix_ms(),"rule":RACE_RULE});
    match outcome {
        ReEvaluated::Admitted { node, main_line, already } => {
            record["result"] = json!(if *already { "already_admitted" } else { "admitted" });
            record["version"] = json!(node.id);
            record["score"] = json!(node.score);
            record["main_line"] = main_line.clone();
        }
        ReEvaluated::NotAdmitted { reason, flagged, score } => {
            record["result"] = json!("not_admitted");
            record["reason"] = json!(reason);
            record["flagged_for_root"] = json!(flagged);
            record["score"] = json!(score);
        }
    }
    record
}

/// Keep the re-evaluation's record in the attempt's folder: `re-evaluation.json` (the latest) and a line under
/// `re_evaluations` in `attempt.json` (every one, in order).
fn record_in_attempt(plan: &ReEvaluationPlan, record: &Value) -> Result<(), WorkloadError> {
    write_json_atomic(&plan.folder.join(RE_EVALUATION_FILE), record)?;
    let attempt_file = plan.folder.join("attempt.json");
    let mut attempt: Value = read_json(&attempt_file)?;
    let entry = json!({"result":record["result"],"version":record["version"],"reason":record["reason"],"retimed_pairs":record["retimed_pairs"],
        "record":record["directory"].as_str().map(|d| Path::new(d).join(RE_EVALUATION_FILE)),"at_unix_ms":record["ended_unix_ms"]});
    match attempt["re_evaluations"].as_array_mut() {
        Some(entries) => entries.push(entry),
        None => attempt["re_evaluations"] = json!([entry]),
    }
    write_json_atomic(&attempt_file, &attempt)?;
    Ok(())
}

/// The note to the attempt's branch (module documentation).
fn note_text(plan: &ReEvaluationPlan, record: &Value) -> String {
    let plain = |v: &Value| v.as_str().map_or_else(|| v.to_string(), str::to_string);
    let cells: Vec<String> = record["retimed"].as_array().into_iter().flatten()
        .map(|p| format!("{} at {} worker{}", plain(&p["template"]), p["workers"], if p["workers"] == 1 { "" } else { "s" })).collect();
    let submission = format!("your submission {} (attempt {}, judged not better than {})", plain(&json!(plan.node.iteration)), plan.attempt, plan.parent);
    let retimed = match cells.len() {
        0 => "No pair met the re-timing rule, so nothing was timed again.".to_string(),
        n => format!("GenDB timed {n} pair{} again, each after waiting for a quiet host: {}. The other pairs were kept as recorded.", if n == 1 { "" } else { "s" }, cells.join(", ")),
    };
    let scores = &record["scores"];
    let score = format!("Parent F {}, G {}; yours F {}, G {}.", plain(&scores["parent"]["finished"]), plain(&scores["parent"]["normalized_time"]),
        plain(&scores["candidate"]["finished"]), plain(&scores["candidate"]["normalized_time"]));
    let result = match record["result"].as_str() {
        Some("admitted") => format!("Result: it is now accepted as {}. Head: {}. Your next submission is judged against the head. {score}", plain(&record["version"]), plain(&record["main_line"]["head"])),
        _ => format!("Result: still not accepted: {}", plain(&record["reason"]).lines().next().unwrap_or("-")),
    };
    format!("GenDB re-evaluated {submission}. Other services loaded this shared host during its interleaved timing, and cells went over the call limit because of that, not because of your code. {retimed}\n\n{result}\n\nRecords: {}.",
        Path::new(&plain(&record["directory"])).join(RE_EVALUATION_FILE).display())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::tree::{MainLineChange, RecordedScore, append_main_line, write_node};
    use crate::engine::score::{NormalizedTime, Score};

    fn node(id: &str, accepted: bool, parents: &[&str], reason: Option<&str>, session: Option<&Path>) -> TreeNode {
        TreeNode { format_version: 1, id: id.into(), accepted, kind: if id == "v000" { NodeKind::FrameworkGenerated } else { NodeKind::Branch },
            branch: if id == "v000" { "main".into() } else { "b1".into() }, parents: parents.iter().map(|p| p.to_string()).collect(), scale: "sf100".into(),
            score: Some(RecordedScore { scale: "sf100".into(), score: Score { finished: 60, normalized_time: NormalizedTime::from_billionths(1) }, cells: 66, beats_both: false, record: PathBuf::new() }),
            reason: reason.map(String::from), session: session.map(Path::to_path_buf), iteration: Some(19), direction: None, rationale: Some("r".into()), created_unix_ms: 1 }
    }

    /// The run of the fixture: v000 and v022 on b1 (the head), and attempt `id` of session 4 with its first
    /// evaluation's records, judged with `reason`. Returns the engine directory.
    fn fixture(root: &Path, id: &str, reason: &str) -> PathBuf {
        let engine = root.join("engine");
        let session = super::super::sessions::session_directory(&engine, "b1", 4);
        let evaluation = session.join("iterations/0019/frozen/evaluation-0");
        fs::create_dir_all(evaluation.join("verus-build")).unwrap();
        fs::write(session.join(SESSION_FILE), "{}").unwrap();
        fs::write(evaluation.join("verus-build/run.json"), "{}").unwrap();
        fs::write(session.join("iterations/0019/frozen/candidate.json"), "{}").unwrap();
        fs::write(evaluation.join("race.json"), json!({"parent":"v022","binding":"v0","calls_per_cell":2,"window_start_unix_ms":1,"window_end_unix_ms":2,"pairs":[]}).to_string()).unwrap();
        for version in [node("v000", true, &[], None, None), node("v022", true, &["v000"], None, None)] {
            fs::create_dir_all(version.directory(&engine)).unwrap();
            write_node(&engine, &version).unwrap();
        }
        append_main_line(&engine, &MainLineChange { version: "v022".into(), previous: None, reason: "r".into(), scale: "sf100".into(), race: None, adopted: None,
            selection: gendb_artifacts::ContentId::from_bytes([1; 32]), at_unix_ms: 1 }).unwrap();
        let attempt = node(id, false, &["v022"], Some(reason), Some(&session));
        let folder = node_directory(&engine, id, false);
        fs::create_dir_all(&folder).unwrap();
        write_json_atomic(&folder.join("attempt.json"), &json!({"format_version":1,"attempt":id,"node":attempt,"evaluation":evaluation})).unwrap();
        write_node(&engine, &attempt).unwrap();
        engine
    }

    const NOT_BETTER: &str = "not better than its parent v022 (the branch head) in one interleaved timing: finished cells 62 vs 60, normalized time 9.942093847 vs 10.348458430 (parent first)";

    /// Done-check: the re-evaluation plan of a fixture record names the frozen submission, the first
    /// evaluation's race and Verus build, the session and the parent; only an attempt refused by the score decision at
    /// the current scale is taken; the parent must still be a head; the record names what was reused.
    #[test]
    fn the_re_evaluation_plan_of_a_recorded_attempt() {
        let root = crate::controller::test_support::scratch_root("engine-re-evaluation-plan");
        let engine = fixture(&root, "b1-a003", NOT_BETTER);
        let plan = ReEvaluationPlan::read(&engine, "b1-a003", "sf100").unwrap();
        let session = super::super::sessions::session_directory(&engine, "b1", 4);
        let frozen = session.join("iterations/0019/frozen");
        assert_eq!((plan.parent.as_str(), plan.session.as_path(), plan.frozen_dir.as_path()), ("v022", session.as_path(), frozen.as_path()));
        assert_eq!((plan.race.clone(), plan.build.clone()), (frozen.join("evaluation-0/race.json"), frozen.join("evaluation-0/verus-build")));
        assert_eq!(plan.folder, engine.join("attempts/b1-a003"));
        let tree = VersionTree::read(&engine).unwrap();
        assert_eq!(tree.branch_head("b1"), Some("v022"));
        plan.check_parent(&tree).unwrap();
        let record = plan.record(&frozen.join("re-evaluation"));
        assert_eq!((record["attempt"].as_str(), record["first_race"].clone(), record["evaluation"].as_str()), (Some("b1-a003"), json!(plan.race), frozen.join("re-evaluation").to_str()));
        // Another scale, another reason, an unknown attempt, a race against another version: refused.
        assert!(ReEvaluationPlan::read(&engine, "b1-a003", "sf10").unwrap_err().contains("was timed at sf100; the run is at sf10 now"));
        assert!(ReEvaluationPlan::read(&engine, "b1-a009", "sf100").unwrap_err().contains("is not a recorded attempt"));
        let refused = fixture(&root.join("refused"), "b1-a004", "refusal: schema_name");
        assert!(ReEvaluationPlan::read(&refused, "b1-a004", "sf100").unwrap_err().starts_with("only an attempt that its interleaved timing judged not better"));
        let other = fixture(&root.join("other"), "b1-a003", NOT_BETTER);
        fs::write(other.join("branches/b1/sessions/session-0004/iterations/0019/frozen/evaluation-0/race.json"), json!({"parent":"v021","binding":"v0","calls_per_cell":2,
            "window_start_unix_ms":1,"window_end_unix_ms":2,"pairs":[]}).to_string()).unwrap();
        assert!(ReEvaluationPlan::read(&other, "b1-a003", "sf100").unwrap_err().contains("against v021, not its parent v022"));
        // A head that moved on: the parent is no longer a head.
        let newer = node("v023", true, &["v022"], None, None);
        fs::create_dir_all(newer.directory(&engine)).unwrap();
        write_node(&engine, &newer).unwrap();
        append_main_line(&engine, &MainLineChange { version: "v023".into(), previous: Some("v022".into()), reason: "r".into(), scale: "sf100".into(), race: None, adopted: None,
            selection: gendb_artifacts::ContentId::from_bytes([2; 32]), at_unix_ms: 2 }).unwrap();
        let moved = plan.check_parent(&VersionTree::read(&engine).unwrap()).unwrap_err();
        assert!(moved.contains("parent v022 is no longer a head (branch b1 head v023, main-line head v023)"), "{moved}");
        fs::remove_dir_all(&root).ok();
    }

    /// Reads a live run's attempt read-only and prints its plan and the pairs the re-evaluation would time again
    /// (`GENDB_RE_EVALUATION_ENGINE_DIR`, `GENDB_RE_EVALUATION_ATTEMPT`, `GENDB_RE_EVALUATION_SCALE`): a check that the
    /// recorded files read back, before the operator runs the command. Writes nothing.
    #[test]
    #[ignore = "reads a live run's attempt records named by GENDB_RE_EVALUATION_ENGINE_DIR, _ATTEMPT and _SCALE"]
    fn a_live_attempt_reads_back() {
        let var = |name: &str| std::env::var(name).unwrap_or_else(|_| panic!("{name}"));
        let engine = PathBuf::from(var("GENDB_RE_EVALUATION_ENGINE_DIR"));
        let plan = ReEvaluationPlan::read(&engine, &var("GENDB_RE_EVALUATION_ATTEMPT"), &var("GENDB_RE_EVALUATION_SCALE")).unwrap();
        println!("plan: parent {}, frozen {}, race {}, build {}", plan.parent, plan.frozen_dir.display(), plan.race.display(), plan.build.display());
        println!("parent still a head: {:?}", plan.check_parent(&VersionTree::read(&engine).unwrap()));
        let race = RecordedRace::read(&plan.race).unwrap();
        let record = super::super::acceptance::recorded_cells(&engine, &plan.parent, &plan.node.scale).expect("the parent's recorded cells");
        let recorded = |p: &crate::engine::race::RacePair| record.iter().find(|c| c.template == p.template && c.workers == p.workers).map(|c| c.status);
        let limit = 60_000_000_000;
        println!("{} pairs, calls per cell {}", race.pairs.len(), race.calls_per_cell);
        for pair in &race.pairs {
            if let Some(reason) = crate::engine::race::suspicion(&pair.timing, recorded(pair), limit) {
                println!("re-timed: {} at {} workers: {reason}", pair.template, pair.workers);
            }
        }
    }

    /// The note and the attempt's record of a re-evaluation: the re-timed cells and why, the result, every
    /// re-evaluation kept in `attempt.json`.
    #[test]
    fn the_branch_is_told_and_the_attempt_keeps_every_re_evaluation() {
        let root = crate::controller::test_support::scratch_root("engine-re-evaluation-records");
        let engine = fixture(&root, "b1-a003", NOT_BETTER);
        let plan = ReEvaluationPlan::read(&engine, "b1-a003", "sf100").unwrap();
        let dir = plan.frozen_dir.join("re-evaluation");
        let record = json!({"attempt":"b1-a003","directory":dir,"result":"admitted","version":"v023","main_line":{"head":"v023","changed":true},"ended_unix_ms":5,
            "retimed_pairs":2,"retimed":[{"template":"Q13","workers":1},{"template":"Q12","workers":32}],
            "scores":{"parent":{"finished":63,"normalized_time":"9.9"},"candidate":{"finished":64,"normalized_time":"9.5"}}});
        let text = note_text(&plan, &record);
        assert!(text.starts_with("GenDB re-evaluated your submission 19 (attempt b1-a003, judged not better than v022). Other services loaded this shared host"), "{text}");
        assert!(text.contains("GenDB timed 2 pairs again, each after waiting for a quiet host: Q13 at 1 worker, Q12 at 32 workers. The other pairs were kept as recorded."), "{text}");
        assert!(text.contains("Result: it is now accepted as v023. Head: v023. Your next submission is judged against the head. Parent F 63, G 9.9; yours F 64, G 9.5."), "{text}");
        assert!(text.ends_with(&format!("Records: {}.", dir.join(RE_EVALUATION_FILE).display())), "{text}");
        let still = json!({"directory":dir,"result":"not_admitted","reason":"not better than its parent v022 ...\nmore","retimed":[],"ended_unix_ms":6});
        assert!(note_text(&plan, &still).contains("No pair met the re-timing rule, so nothing was timed again.\n\nResult: still not accepted: not better than its parent v022 ..."));
        record_in_attempt(&plan, &record).unwrap();
        record_in_attempt(&plan, &still).unwrap();
        let attempt: Value = read_json(&plan.folder.join("attempt.json")).unwrap();
        let results: Vec<&str> = attempt["re_evaluations"].as_array().unwrap().iter().map(|e| e["result"].as_str().unwrap()).collect();
        assert_eq!(results, ["admitted", "not_admitted"]);
        assert_eq!(attempt["re_evaluations"][0]["record"], json!(dir.join(RE_EVALUATION_FILE)));
        assert_eq!(read_json::<Value>(&plan.folder.join(RE_EVALUATION_FILE)).unwrap()["result"], "not_admitted", "the latest");
        assert_eq!(attempt["node"]["id"], "b1-a003", "the attempt's record is kept");
        fs::remove_dir_all(&root).ok();
    }
}
