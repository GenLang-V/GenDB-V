//! A submission's evaluation in a run of several workloads (`engine.workloads`; the records
//! `evaluation.members` and `evaluation.combined`). [`evaluate_members`] is the order, over the steps of one workload
//! ([`MemberSteps`]; real: [`BenchSteps`] on the session's bench; tests: canned), each step gating:
//! 1. every workload's crate frozen beside the primary's (the freeze, `EngineBench::freeze_side_crates`; a refusal is an
//!    attempt before this order starts); when the request sets the one-engine rule ([`super::one_engine`]), a submission
//!    that is not one engine is refused here, before any build or timing;
//! 2. Verus on every workload's whole crate, the primary first;
//! 3. every workload's storages, the storage policy and its budget rule (a check workload is exempt);
//! 4. every check workload's answers: every template at every visible binding at the smallest and the largest
//!    configured worker count, one call each, every answer against the saved answers, before any timing (a wrong answer
//!    refuses the submission and is flagged; a call that did not finish, or an answer not compared, refuses it);
//! 5. every counted workload's interleaved timing against the parent's side of that workload at its scale, the
//!    primary's first;
//! 6. the combined decision ([`combined_decision`]: the sums of the counted workloads' scores of these races, parent
//!    against candidate; no guard per workload): not better, the submission is an attempt and every kept workload stays
//!    `not_run`, unless the one-engine rule accepts it as the first one-engine version of the line
//!    ([`super::one_engine::OneEngineRule::transition`], recorded in the combined decision);
//! 7. every kept workload's timing against the parent's side of it (recorded and shown, never deciding; a wrong answer
//!    refuses the submission and is flagged);
//! 8. every workload's variants at its first scale;
//! 9. the admission in every library in lockstep (`engine::stage::admit_in_lockstep`, after this order).
//!
//! Every workload's status ([`MemberStatus`]: `not_run`, `refused` with the step, `checked`, `timed`) is written to
//! `<evaluation>/members.json` after every change ([`MemberStatuses`]), and the combined decision to
//! `<evaluation>/combined.json`, so the evaluation record names them whatever the outcome.
//!
//! Trust: none in proofs. The order, the statuses, the answers' summary and the combined decision are host code used for
//! decisions and records; each crate is verified whole by Verus and every answer is compared with the saved answers by
//! the checked cells (`admission::engine::EngineRunner::cell`).

use super::super::acceptance::{
    CheckedEngine, ENGINE_FINISHED_CHECKS_KIND, ENGINE_RACE_KIND, Failure, NOT_BETTER_REASON, Parent, Runnable, SUBMISSION_PLAN, StepTimes, answer_failure, lineage_parents, race_failure,
    race_summary, recorded_cells,
};
use super::super::race::RaceReport;
use super::super::role::{EngineBench, EngineCells, float_free, storage_inputs, storage_view};
use super::super::score::{CellResult, CombinedScore, Score};
use super::super::submission::members::MemberRecord;
use super::super::submission::{EngineBuild, FrozenEngine, engine_version_id};
use super::super::timing::{AnswerCell, EngineStatement, check_answers};
use super::super::tree::{RecordedScore, VersionTree};
use super::one_engine::{ONE_ENGINE_STEP, OneEngineRule, Transition};
use super::{LineageOf, MemberKeep, StageRole, records, side_evaluation_dir, side_frozen_dir};
use crate::controller::records::{read_json, write_json_atomic};
use crate::controller::request::{MemberRole, WorkloadForm};
use crate::query::evaluation::ResolvedStorage;
use crate::storage::engine_library::BudgetRule;
use crate::tools::TrialVerification;
use gendb_artifacts::verus::{VERUS_ENGINE_LINEAGE_KIND, VerusEngineLineageV1};
use gendb_verification::admission::AdmissionError;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

/// Every workload's status in one evaluation (`<evaluation>/members.json`).
pub const MEMBERS_FILE: &str = "members.json";
/// The combined decision of one evaluation (`<evaluation>/combined.json`).
pub const COMBINED_FILE: &str = "combined.json";
/// A check workload's answers in its evaluation directory.
pub const CHECK_FILE: &str = records::CHECK_FILE;

// ------------------------------------------------------------------------------------------------ statuses

/// One workload's status in one evaluation (the workloads fixture `evaluation.members[]`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MemberStatus {
    pub name: String,
    /// `counted`, `check` or `kept`.
    pub role: String,
    /// `not_run` (an earlier step refused the submission, or a kept workload after a combined score not better),
    /// `refused` (this workload's step refused the submission), `checked` (a check workload verified and answered) or
    /// `timed` (verified, its storages checked and timed against the parent's side).
    pub status: String,
    /// The refusing step (`freeze`, `one_engine`, `verus`, `storages`, `answers`, `timing` or `variants`), when refused.
    pub step: Option<String>,
    /// The refusal's first line, when refused.
    pub reason: Option<String>,
    /// Its race report, when timed.
    pub race: Option<PathBuf>,
    /// A check workload's answers (`calls`, `agreed`, `record`), when checked.
    pub check: Option<Value>,
}

impl MemberStatus {
    fn not_run(name: &str, role: MemberRole) -> Self {
        Self { name: name.into(), role: role.name().into(), status: "not_run".into(), step: None, reason: None, race: None, check: None }
    }
}

/// Every workload's status of one evaluation, written to `<dir>/members.json` after every change.
pub struct MemberStatuses {
    file: PathBuf,
    statuses: Vec<MemberStatus>,
}

impl MemberStatuses {
    /// Every workload of `members` (`(name, role)`, the primary first) `not_run`, written.
    pub fn start(dir: &Path, members: &[(String, MemberRole)]) -> Result<Self, AdmissionError> {
        fs::create_dir_all(dir).map_err(AdmissionError::tool)?;
        let this = Self { file: dir.join(MEMBERS_FILE), statuses: members.iter().map(|(name, role)| MemberStatus::not_run(name, *role)).collect() };
        this.write()?;
        Ok(this)
    }

    /// The statuses written in `dir`; every workload of `members` `not_run` when none were written.
    pub fn read(dir: &Path, members: &[(String, MemberRole)]) -> Vec<MemberStatus> {
        read_json(&dir.join(MEMBERS_FILE)).unwrap_or_else(|_| members.iter().map(|(name, role)| MemberStatus::not_run(name, *role)).collect())
    }

    pub fn statuses(&self) -> &[MemberStatus] {
        &self.statuses
    }

    fn write(&self) -> Result<(), AdmissionError> {
        write_json_atomic(&self.file, &self.statuses).map_err(AdmissionError::tool)
    }

    fn set(&mut self, name: &str, change: impl FnOnce(&mut MemberStatus)) -> Result<(), AdmissionError> {
        let status = self.statuses.iter_mut().find(|s| s.name == name).ok_or_else(|| AdmissionError::tool(format!("{name} is not a workload of this evaluation")))?;
        change(status);
        self.write()
    }

    /// Workload `name` timed against the parent's side (its race report `race`).
    pub fn timed(&mut self, name: &str, race: &Path) -> Result<(), AdmissionError> {
        self.set(name, |s| {
            s.status = "timed".into();
            s.race = Some(race.to_path_buf());
        })
    }

    /// Check workload `name` verified and answered (`check`: `calls`, `agreed`, `record`).
    pub fn checked(&mut self, name: &str, check: Value) -> Result<(), AdmissionError> {
        self.set(name, |s| {
            s.status = "checked".into();
            s.check = Some(check);
        })
    }

    /// Workload `name` refused the submission at `step` with `reason` (its first line kept).
    pub fn refused(&mut self, name: &str, step: &str, reason: &str) -> Result<(), AdmissionError> {
        self.set(name, |s| {
            s.status = "refused".into();
            s.step = Some(step.into());
            s.reason = Some(reason.lines().next().unwrap_or_default().to_string());
        })
    }

    /// `outcome` of workload `name`'s step `step`: a candidate's failure is recorded as its refusal there (the
    /// framework's stays the framework's), and the outcome passed on.
    pub(in crate::engine) fn at<T>(&mut self, name: &str, step: &str, outcome: Result<T, Failure>) -> Result<T, Failure> {
        if let Err(Failure::Candidate { reason, .. }) = &outcome {
            self.refused(name, step, reason)?;
        }
        outcome
    }
}

// ------------------------------------------------------------------------------------------------ the order

/// One workload's race as the combined decision reads it: its report file, both sides' scores and its cells.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RaceScores {
    pub file: PathBuf,
    pub parent: Score,
    pub candidate: Score,
    pub cells: usize,
}

impl RaceScores {
    /// The scores of the race `report` written to `file`.
    pub fn of(report: &RaceReport, file: &Path) -> Self {
        Self { file: file.to_path_buf(), parent: report.parent_score.score, candidate: report.candidate_score.score, cells: report.candidate_score.cells_total }
    }
}

/// The steps of one workload of a submission (module documentation; real: [`BenchSteps`]; tests: canned). Each keeps
/// what its later steps and the admission need.
pub(in crate::engine) trait MemberSteps {
    /// Step 2: Verus on workload `name`'s whole crate.
    fn verus(&mut self, name: &str) -> Result<(), Failure>;
    /// Step 3: its storages, the storage policy and its budget rule.
    fn storages(&mut self, name: &str) -> Result<(), Failure>;
    /// Step 4: check workload `name`'s answers (`calls`, `agreed`, `file`).
    fn answers(&mut self, name: &str) -> Result<Value, Failure>;
    /// Step 5 (counted) or 7 (kept): its timing against the parent's side of it.
    fn race(&mut self, name: &str) -> Result<RaceScores, Failure>;
    /// Step 8: its variants at its first scale.
    fn variants(&mut self, name: &str) -> Result<(), Failure>;
}

/// The combined decision of one evaluation (the workloads fixture `evaluation.combined`, the rule `engine::score::COMBINED_RULE`):
/// both sides' combined scores over the counted workloads' races `(workload, race)` (the primary first), and whether the
/// candidate's is better.
pub fn combined_decision(races: &[(&str, &RaceScores)]) -> Result<(Value, bool), AdmissionError> {
    let sums = |parent_side: bool| -> Result<CombinedScore, AdmissionError> {
        let scores: Vec<(&str, Score, usize)> = races.iter().map(|(name, r)| (*name, if parent_side { r.parent } else { r.candidate }, r.cells)).collect();
        CombinedScore::of(&scores).map_err(|e| AdmissionError::tool(e.to_string()))
    };
    let (parent, candidate) = (sums(true)?, sums(false)?);
    let better = candidate.is_better_than(&parent);
    let record = json!({"parent":{"score":parent.score,"cells":parent.cells},"candidate":{"score":candidate.score,"cells":candidate.cells},"better":better,
        "workloads":candidate.workloads});
    Ok((record, better))
}

/// The combined decision recorded in the evaluation `dir`, if any.
pub fn recorded_combined(dir: &Path) -> Value {
    read_json(&dir.join(COMBINED_FILE)).unwrap_or(Value::Null)
}

/// The evaluation's order (module documentation, steps 2-8) over `members` (`(name, role)`, the primary first,
/// counted) through `steps`, every status recorded in `statuses`, the combined decision written to
/// `<dir>/combined.json`. `parent` names the parent in a refusal; `one_engine` is the request's one-engine rule when it
/// sets one (`None`: the combined score alone decides). Returns the combined decision's record; a failure names its
/// workload (but the primary's), and a combined score not better is the candidate's failure (an attempt) unless the
/// one-engine rule accepts it.
pub(in crate::engine) fn evaluate_members(members: &[(String, MemberRole)], steps: &mut impl MemberSteps, statuses: &mut MemberStatuses, parent: &Parent, dir: &Path,
    one_engine: Option<&OneEngineRule>) -> Result<Value, Failure> {
    let primary = members.first().map(|(n, _)| n.clone()).ok_or_else(|| AdmissionError::tool("a run of several workloads without its primary workload"))?;
    let named = |name: &str, failure: Failure| if name == primary { failure } else { failure.of_workload(name, None) };
    let every: Vec<&str> = members.iter().map(|(n, _)| n.as_str()).collect();
    let of_role = |role: MemberRole| members.iter().filter(move |(_, r)| *r == role).map(|(n, _)| n.as_str());
    // 1. The one-engine rule: a submission that is not one engine is refused before any build or timing; each workload
    //    that breaks it is recorded as refusing it at this step.
    if let Some(reason) = one_engine.and_then(OneEngineRule::refusal) {
        let breaking = one_engine.map(OneEngineRule::breaking_workloads).unwrap_or_default();
        for name in if breaking.is_empty() { vec![primary.clone()] } else { breaking } {
            statuses.refused(&name, ONE_ENGINE_STEP, &reason)?;
        }
        return Err(Failure::Candidate { reason, flagged: false, score: None });
    }
    // 2-3. Verus on every crate, then every workload's storages.
    for name in &every {
        statuses.at(name, "verus", steps.verus(name)).map_err(|f| named(name, f))?;
    }
    for name in &every {
        statuses.at(name, "storages", steps.storages(name)).map_err(|f| named(name, f))?;
    }
    // 4. Every check workload's answers, before any timing.
    for name in of_role(MemberRole::Check) {
        let check = statuses.at(name, "answers", steps.answers(name)).map_err(|f| named(name, f))?;
        statuses.checked(name, json!({"calls":check["calls"],"agreed":check["agreed"],"record":check["file"]}))?;
    }
    // 5. Every counted workload's timing against the parent's side of it, the primary's first.
    let mut races: Vec<(&str, RaceScores)> = vec![];
    for name in of_role(MemberRole::Counted) {
        let race = statuses.at(name, "timing", steps.race(name)).map_err(|f| named(name, f))?;
        statuses.timed(name, &race.file)?;
        races.push((name, race));
    }
    // 6. The combined decision (and, not better, the one-engine rule's transition).
    let counted: Vec<(&str, &RaceScores)> = races.iter().map(|(n, r)| (*n, r)).collect();
    let (mut combined, better) = combined_decision(&counted)?;
    let transition = match (better, one_engine) {
        (false, Some(rule)) => rule.transition(&parent.id, &counted),
        _ => Transition::NotApplicable,
    };
    if let Transition::Accepted(record) = &transition {
        combined[super::one_engine::ONE_ENGINE_TRANSITION] = record.clone();
    }
    write_json_atomic(&dir.join(COMBINED_FILE), &combined).map_err(AdmissionError::tool)?;
    if !better && !matches!(transition, Transition::Accepted(_)) {
        let text = |v: &Value| v.as_str().map_or_else(|| v.to_string(), str::to_string);
        let unfinished = match &transition {
            Transition::Unfinished(why) => format!("; {why}"),
            _ => String::new(),
        };
        return Err(Failure::Candidate {
            reason: format!("{NOT_BETTER_REASON} {} ({}) by the combined score over {}: finished cells {} vs {}, normalized time {} vs {} (parent first){unfinished}",
                parent.id, parent.chosen, races.iter().map(|(n, _)| *n).collect::<Vec<_>>().join(", "), text(&combined["parent"]["score"]["finished"]),
                text(&combined["candidate"]["score"]["finished"]), text(&combined["parent"]["score"]["normalized_time"]), text(&combined["candidate"]["score"]["normalized_time"])),
            flagged: false,
            score: None,
        });
    }
    // 7. Every kept workload's timing (recorded and shown, never deciding).
    for name in of_role(MemberRole::Kept) {
        let race = statuses.at(name, "timing", steps.race(name)).map_err(|f| named(name, f))?;
        statuses.timed(name, &race.file)?;
    }
    // 8. Every workload's variants.
    for name in &every {
        statuses.at(name, "variants", steps.variants(name)).map_err(|f| named(name, f))?;
    }
    Ok(combined)
}

// ------------------------------------------------------------------------------------------------ the real steps

/// What one workload's steps hold: its frozen crate and evaluation directory, its build, storages and their policy,
/// its race and answers, and its checks.
struct MemberState {
    role: MemberRole,
    frozen: PathBuf,
    evaluation: PathBuf,
    engine: FrozenEngine,
    build: Option<EngineBuild>,
    storages: Vec<ResolvedStorage>,
    storage_policy: Value,
    rule: Option<BudgetRule>,
    /// Its parent version ready to run (its race's parent side); the primary's is resolved with its storages.
    parent_run: Option<Runnable>,
    race: Option<(RaceReport, PathBuf, RecordedScore)>,
    check: Option<Value>,
    checks: Value,
}

/// What the admission of an accepted submission needs from [`BenchSteps::finish`]: the primary's score, record
/// (without the admission), build record and evidence, and every other workload's [`MemberKeep`].
pub(in crate::engine) struct Finished {
    pub score: RecordedScore,
    pub record: Value,
    pub build: Value,
    pub evidence: Vec<(String, Value)>,
    pub others: Vec<MemberKeep>,
}

/// The real steps of a submission's workloads (module documentation) on the session's bench: the primary on the bench
/// itself (its records at the evaluation's top, its race the evaluation's `race.json`), every other workload on the
/// bench viewing it (`EngineBench::on_side`; its records under `<evaluation>/workloads/<name>/`).
pub(in crate::engine) struct BenchSteps<'s, 'a> {
    bench: &'s mut EngineBench<'a>,
    stage: &'s StageRole,
    dir: &'s Path,
    parent: &'s Parent,
    timings: &'s mut StepTimes,
    /// The primary's candidate label in its race (`<branch> iteration <n>`).
    label: String,
    states: BTreeMap<String, MemberState>,
}

impl<'s, 'a> BenchSteps<'s, 'a> {
    /// The steps of the submission frozen in `frozen_dir` (the primary's `engine`, every other crate beside it), its
    /// evaluation in `dir`, against `parent`.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::engine) fn new(bench: &'s mut EngineBench<'a>, stage: &'s StageRole, engine: FrozenEngine, frozen_dir: &Path, dir: &'s Path, parent: &'s Parent, timings: &'s mut StepTimes,
        label: String) -> Result<Self, AdmissionError> {
        let state = |role: MemberRole, frozen: PathBuf, evaluation: PathBuf, engine: FrozenEngine| MemberState { role, frozen, evaluation, engine, build: None, storages: vec![],
            storage_policy: Value::Null, rule: None, parent_run: None, race: None, check: None, checks: Value::Null };
        let mut states = BTreeMap::new();
        states.insert(stage.workload.clone(), state(stage.role, frozen_dir.to_path_buf(), dir.to_path_buf(), engine));
        for side in &stage.sides {
            let frozen = side_frozen_dir(WorkloadForm::Workloads, frozen_dir, &side.name);
            let evaluation = side_evaluation_dir(WorkloadForm::Workloads, dir, &side.name);
            fs::create_dir_all(&evaluation).map_err(AdmissionError::tool)?;
            let engine: FrozenEngine = read_json(&frozen.join("candidate.json")).map_err(AdmissionError::tool)?;
            states.insert(side.name.clone(), state(side.role, frozen, evaluation, engine));
        }
        Ok(Self { bench, stage, dir, parent, timings, label, states })
    }

    /// Every workload's record of its frozen crate (`(workload, record)`, the primary first), which the one-engine rule
    /// reads ([`OneEngineRule::of`]).
    pub(in crate::engine) fn member_records(&self) -> Vec<(String, Option<MemberRecord>)> {
        std::iter::once(self.stage.workload.clone())
            .chain(self.stage.sides.iter().map(|s| s.name.clone()))
            .map(|name| {
                let record = self.states.get(&name).and_then(|s| s.engine.workload.as_ref()).and_then(|w| w.member.clone());
                (name, record)
            })
            .collect()
    }

    /// The primary's recorded score of its race, once timed (an attempt after the races keeps it).
    pub(in crate::engine) fn primary_score(&self) -> Option<RecordedScore> {
        self.states.get(&self.stage.workload).and_then(|s| s.race.as_ref()).map(|(_, _, score)| score.clone())
    }

    /// Run `work` on workload `name`'s bench (the primary's own, every other's view of it) with its state.
    fn on<T>(&mut self, name: &str, work: impl FnOnce(&mut EngineBench<'_>, &mut MemberState, &mut StepTimes) -> Result<T, Failure>) -> Result<T, Failure> {
        let state = self.states.get_mut(name).ok_or_else(|| AdmissionError::tool(format!("{name} is not a workload of this run")))?;
        let timings = &mut *self.timings;
        match self.stage.side(name) {
            Some(side) => self.bench.on_side(side, |bench| work(bench, state, timings)),
            None => work(self.bench, state, timings),
        }
    }

    /// The step label of workload `name` (the primary's steps are named as a run of one workload's).
    fn step(&self, name: &str, step: &str) -> String {
        if name == self.stage.workload { step.to_string() } else { format!("{name}:{step}") }
    }

    /// The admission's inputs once the order accepted the submission ([`Finished`]): every workload's record and
    /// evidence, each with its lineage in its own library.
    pub(in crate::engine) fn finish(mut self, lineage: &LineageOf, tree: &VersionTree) -> Result<Finished, Failure> {
        let primary = self.stage.workload.clone();
        let parent = self.parent;
        let mut others = vec![];
        let mut primary_parts = None;
        let names: Vec<String> = std::iter::once(primary.clone()).chain(self.stage.sides.iter().map(|s| s.name.clone())).collect();
        for name in names {
            let (frozen, evaluation, build, evidence, record) = self.on(&name, |bench, state, _| -> Result<_, Failure> {
                let parents = lineage_parents(tree, &bench.bench.store()?, parent, lineage.merge_from.as_deref(), lineage.session_kind)?;
                let lineage = VerusEngineLineageV1 { branch: lineage.branch.clone(), kind: lineage.kind.clone(), parents };
                let build = state.build.clone().ok_or_else(|| AdmissionError::tool(format!("workload {name}: no build")))?;
                let mut evidence = vec![(VERUS_ENGINE_LINEAGE_KIND.to_string(), json!(lineage))];
                let mut record = json!({"finished_checks":state.checks,"storage_policy_at_evaluation":state.storage_policy,
                    "storage":{"assets":state.storages.iter().map(storage_view).collect::<Vec<_>>(),"budget_rule":state.rule},
                    "build":build.record,"crate_version":engine_version_id(&state.engine, &state.frozen)?,"parent":parent.id});
                if let Some((report, file, score)) = &state.race {
                    let summary = float_free(&race_summary(report, file));
                    evidence.push((ENGINE_RACE_KIND.to_string(), summary.clone()));
                    record["race"] = json!(file);
                    record["race_summary"] = summary;
                    record["score"] = json!(score);
                    record["candidate_cells"] = json!(report.candidate_score.cells.iter().map(|c| CellResult { template: c.template.clone(), workers: c.workers, status: c.status }).collect::<Vec<_>>());
                }
                // A check workload's answers are among its checks' evidence.
                let mut checks = state.checks.clone();
                if let Some(check) = &state.check {
                    checks["answers"] = check.clone();
                    record["check"] = check.clone();
                }
                evidence.push((ENGINE_FINISHED_CHECKS_KIND.to_string(), float_free(&checks)));
                if name != primary {
                    let scale = bench.inputs().general.as_ref().map_or_else(String::new, |g| g.scale.name.clone());
                    record["role"] = json!(state.role.name());
                    record["scale"] = json!(scale);
                    record["module_report"] = json!(state.engine.workload.as_ref().map(|w| &w.module_report));
                    record["member"] = json!(state.engine.workload.as_ref().and_then(|w| w.member.as_ref()));
                }
                Ok((state.frozen.clone(), state.evaluation.clone(), build.record, evidence, record))
            })?;
            if name == primary {
                primary_parts = Some((build, evidence, record));
            } else {
                others.push(MemberKeep { name, frozen, evaluation, build, evidence, record });
            }
        }
        let (build, evidence, mut record) = primary_parts.ok_or_else(|| AdmissionError::tool("the primary's admission inputs are missing"))?;
        record["parent_chosen"] = json!(parent.chosen);
        let score = self.primary_score().ok_or_else(|| AdmissionError::tool("the primary was not timed"))?;
        Ok(Finished { score, record, build, evidence, others })
    }
}

impl MemberSteps for BenchSteps<'_, '_> {
    fn verus(&mut self, name: &str) -> Result<(), Failure> {
        let step = self.step(name, "verus");
        self.on(name, |bench, state, timings| {
            let locks = bench.bench.config.locks.clone();
            let build = timings.time(step, || bench.builds.compile(&locks, &state.engine, &state.frozen, &state.evaluation.join("verus-build"), true))?;
            state.build = Some(build);
            Ok(())
        })
    }

    fn storages(&mut self, name: &str) -> Result<(), Failure> {
        let step = self.step(name, "storages");
        let primary = name == self.stage.workload;
        let (parent, dir) = (self.parent, self.dir);
        self.on(name, |bench, state, timings| {
            timings.time(step, || -> Result<(), Failure> {
                let rule = bench.budget_rule()?;
                state.storages = bench.storages(&state.engine, &state.frozen, &state.evaluation, TrialVerification::WholeCrate)?;
                state.storage_policy = bench.check_storage_policy(&state.engine, &state.frozen, &state.storages, &rule)?;
                state.rule = Some(rule);
                // The primary's parent, ready to run (its race's parent side), as a run of one workload resolves it.
                if primary {
                    state.parent_run = Some(bench.admitted_runnable(&parent.id, &dir.join("parent-storages")).map_err(Failure::Framework)?);
                }
                Ok(())
            })
        })
    }

    fn answers(&mut self, name: &str) -> Result<Value, Failure> {
        let step = self.step(name, "answers");
        let workload = name.to_string();
        self.on(name, |bench, state, timings| {
            let build = state.build.clone().ok_or_else(|| AdmissionError::tool(format!("workload {workload}: answers before its build")))?;
            let check = timings.time(step, || bench.check_answers_here(&workload, &build.library, &state.storages, &state.evaluation))?;
            state.check = Some(check.clone());
            Ok(check)
        })
    }

    fn race(&mut self, name: &str) -> Result<RaceScores, Failure> {
        let step = self.step(name, "interleaved_timing");
        let primary = name == self.stage.workload;
        let (parent, label, workload) = (self.parent, self.label.clone(), name.to_string());
        self.on(name, |bench, state, timings| {
            let engine_dir = bench.config.engine_dir.clone();
            let general = bench.inputs().general.clone().ok_or_else(|| AdmissionError::tool(format!("workload {workload}: no general inputs")))?;
            let build = state.build.clone().ok_or_else(|| AdmissionError::tool(format!("workload {workload}: a race before its build")))?;
            let parent_run = match state.parent_run.take() {
                Some(run) => run,
                None => bench.admitted_runnable(&parent.id, &state.evaluation.join("parent-storages")).map_err(Failure::Framework)?,
            };
            let candidate_label = if primary { label.clone() } else { format!("{label} ({workload})") };
            let candidate_run = Runnable { label: candidate_label, library: build.library.clone(), inputs: storage_inputs(&state.storages) };
            // The parent's recorded cells on this workload (the primary's are the version folder's own).
            let parent_record = if primary { recorded_cells(&engine_dir, &parent.id, &general.scale.name) } else { records::workload_cells(&engine_dir, &parent.id, &workload, &general.scale.name) };
            let raced = timings.time(step, || bench.race_runnables(&parent_run, &candidate_run, parent_record.as_deref(), SUBMISSION_PLAN.cell_calls, &state.evaluation.join("race")));
            let report = raced.map_err(|error| race_failure(&engine_dir, &parent.id, error))?;
            let file = state.evaluation.join("race.json");
            write_json_atomic(&file, &json!(report)).map_err(AdmissionError::tool)?;
            let score = RecordedScore::of(&general.scale.name, &report.candidate_score, &file);
            let scores = RaceScores::of(&report, &file);
            state.parent_run = Some(parent_run);
            state.race = Some((report, file, score));
            Ok(scores)
        })
    }

    fn variants(&mut self, name: &str) -> Result<(), Failure> {
        let step = self.step(name, "variants");
        let workload = name.to_string();
        self.on(name, |bench, state, timings| {
            let build = state.build.clone().ok_or_else(|| AdmissionError::tool(format!("workload {workload}: variants before its build")))?;
            let uses = storage_inputs(&state.storages);
            let subject = CheckedEngine { library: &build.library, inputs: &uses, frozen: Some((&state.engine.storage_uses, &state.frozen)) };
            let checks = timings.time(step, || match &state.race {
                Some((report, _, _)) => bench.check_finished_templates(SUBMISSION_PLAN, &subject, &report.candidate_score, &state.evaluation),
                // A check workload has no race: every variant's answer.
                None => bench.variant_answers(&subject, &BTreeSet::new(), &state.evaluation).map(|variants| json!({"plan":SUBMISSION_PLAN.record(),"variants":variants})),
            })?;
            state.checks = checks;
            Ok(())
        })
    }
}

impl EngineBench<'_> {
    /// A check workload's answers on this bench (the workload's own, or a root's check side, `engine::stage::root`): the
    /// engine `library` over `storages`, every template at every visible binding at [`answer_workers`], one call each,
    /// against the saved answers; written to `<evaluation>/check.json`. Returns its check record (`calls`, `agreed`,
    /// `file`). A wrong answer refuses the submission and is flagged; a call that did not finish, or an answer not
    /// compared with saved answers, refuses it.
    pub(in crate::engine) fn check_answers_here(&mut self, name: &str, library: &Path, storages: &[ResolvedStorage], evaluation: &Path) -> Result<Value, Failure> {
        let inputs = self.config.inputs.clone();
        let statements: Vec<EngineStatement> = inputs.statements.official.iter().chain(inputs.statements.other_bindings.iter().flat_map(|(_, s)| s)).map(|s| s.statement.clone()).collect();
        let workers = answer_workers(&inputs.workers);
        let uses = storage_inputs(storages);
        let cells = EngineCells { runner: self.runner(library, &uses), checks: &inputs.checks, adhoc: &[], bound: None };
        let locks = self.bench.config.locks.clone();
        let mut answered: Vec<AnswerCell> = vec![];
        for w in &workers {
            let at = check_answers(&cells, &statements, *w, &evaluation.join("answers"), || locks.timing()).map_err(|e| answer_failure(e, &format!("workload {name}: an answer")))?;
            answered.extend(at);
        }
        let file = evaluation.join(CHECK_FILE);
        let agreed = answered.iter().filter(|c| c.checked).count();
        let bindings: BTreeSet<&str> = statements.iter().map(|s| s.binding.as_str()).collect();
        write_json_atomic(&file, &json!({"workload":name,"workers":workers,"bindings":bindings,"calls":answered.len(),"agreed":agreed,"cells":answered,
            "meaning":"a check workload's answers: every template at every visible binding, one call each at the smallest and the largest configured worker count, every answer against the saved answers; no time is read"}))
            .map_err(AdmissionError::tool)?;
        if let Some(cell) = answered.iter().find(|c| c.unfinished.is_some()) {
            return Err(Failure::Candidate {
                reason: format!("refusal: check workload {name}: {} at {} with {} workers did not finish ({:?}): a check workload answers every template", cell.template, cell.binding, cell.workers, cell.unfinished),
                flagged: false,
                score: None,
            });
        }
        if let Some(cell) = answered.iter().find(|c| !c.checked) {
            return Err(Failure::Candidate {
                reason: format!("refusal: check workload {name}: {} at {} with {} workers was not checked against saved answers ({})", cell.template, cell.binding, cell.workers, cell.status),
                flagged: false,
                score: None,
            });
        }
        Ok(json!({"calls":answered.len(),"agreed":agreed,"file":file}))
    }
}

/// The worker counts a check workload's answers are checked at: the smallest and the largest configured count (one
/// count when they are equal).
pub fn answer_workers(workers: &[usize]) -> Vec<usize> {
    let mut counts: Vec<usize> = workers.iter().min().into_iter().chain(workers.iter().max()).copied().collect();
    counts.dedup();
    counts
}
