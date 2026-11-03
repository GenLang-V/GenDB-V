//! The roles' decisions (`RolePolicy`): the author prompt of every call, the objective over the session's trials, and
//! the early stop of a correctness objective. [`VerifiedQueryPolicy`] decides for a query session,
//! [`StoragePolicy`] for the workload storage session.
//!
//! Every prompt is structured Markdown (`prompts::sections`): key paths and scope rules first, then the task, the goal
//! (what a submission must be), how to work, the evaluation, inputs, tools, the submission and the process appendix,
//! then the call's data (`prompts::data_sections`, rendered from the views prepared here): CURRENT FACTS AND PATHS (the
//! prepared context, the targets and every submission's official result), HANDOFF FROM EARLIER ATTEMPTS (a fresh
//! session: the record paths, the local trial log and the author's NOTES.md), LEDGER (`LedgerState::author_view`) and
//! LATEST FEEDBACK (the latest call and its evaluation). Everything else the author needs is a file mapped by
//! `files.author_contract`; nothing here is specific to a query or a dataset.

use super::data_sections::{self, AuthorKind, DataViews};
use super::sections;
use crate::controller::benchmark_inputs::TargetSource;
use crate::controller::ledger::framework_failure;
use crate::controller::limits::count_guard_text;
use crate::controller::{PromptInput, RolePolicy, StopReason, Trial, qualification_order};
use crate::storage::flat::FIXED_FLAT;
use crate::storage::policy::{PHYSICAL_ONLY, UNRESTRICTED, storage_choices};
use gendb_verification::admission::bindings::CONCRETE_BINDING;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::path::Path;

/// `objective.kind` of the correctness objective: the first exact verified candidate is qualified and the run stops.
pub const CORRECTNESS_OBJECTIVE: &str = "verified_correctness";
/// `objective.kind` of the performance objective: every submission is measured until the submission guard.
pub const PERFORMANCE_OBJECTIVE: &str = "verified_performance";

/// `objective.kind` of the workload storage session: the first verified, built submission is admitted.
pub const STORAGE_OBJECTIVE: &str = "verified_storage";

/// The rule of the storage objective (context, brief and objective status).
pub const STORAGE_RULE: &str = "every submitted storage crate verifies whole with 0 errors (--no-cheating) against the fixed storage entry, its stored library builds its asset over the current prepared data with status Ok, and the checks of the run's validation policy pass (validation.json: under tests_and_references every tiny input of the statements that read its tables also builds; under formal_proofs nothing more); then every storage is admitted and the session stops";

/// How both roles are asked to treat stored data (prompts and contracts).
pub const STORAGE_CHOICE_TEXT: &str = "The stored organization of data is a first-class design choice: stored size, preparation (build) cost, read/decode cost and query execution cost trade off. Measure them with the tools (storage_build reports stored bytes, canonical column bytes and build time; trial/profile report per storage use the aggregate read requests, requested elements and requested bytes (counts, not a per-extent trace), the stored bytes and the child's device reads, and the query time), choose, and explain your choice briefly in the manifest's layout.choice and your submission's data_access_analysis. Reusing an admitted storage is a valid choice; nothing requires a new version, a particular layout or a weighting of these costs, and no performance win is promised. Storage bounds: the storage budget over all serving storage (CURRENT FACTS, Storage), the only hard limit, and the storage_policy (CURRENT FACTS, Storage; stored-data.json storage_policy); every build also keeps the filesystem's free-space reserve, a device protection and not a size limit (stored-data.json free_space_reserve)";

/// How a query author treats stored data under `fixed_flat` (contracts): the data is fixed, the data access is theirs.
pub const FIXED_FLAT_DATA_ACCESS_TEXT: &str = "The stored data is fixed and already prepared: one flat_<table> storage per table (storages.json), every column a plain typed array in source row order (storage_policy). You design, build and register no storage. Your choice is the runtime data access: which columns and row extents your readers request, in which order and at which worker count, and which transient structures (hash tables, sorted or partitioned copies, bitmaps, group tables) each call builds inside the timed call and discards. trial/profile report per storage use the aggregate read requests, requested elements and requested bytes (counts, not a per-extent trace), the stored bytes and the child's device reads, and the query time. Explain this design briefly in your submission's data_access_analysis. No particular access pattern is required and no performance win is promised";

/// Shared by both author roles: checks are repeated only when something changed or is still unresolved.
pub const CHECK_ECONOMY_TEXT: &str = "Check economy: once a check passes, repeat it only after a meaningful code or specification change, to diagnose a concrete failure, or to settle a check that is still unresolved; do not sweep solver settings (rlimit, seeds) or re-run passing proofs just to measure margin. Trials, repairs and the measurements your design or optimization needs are not limited by this";

/// Where reusable implementations come from (both roles' prompts and contract indexes).
pub const IMPLEMENTATION_PROVENANCE_TEXT: &str = "Reusable implementations are exactly the ones listed in the supplied admitted catalogs: the search index of all admitted code, proofs and general modules (files.search_index), files.library where your context names it (admitted query code, copied under prior-verus-code) and the contract's storages.json (admitted storages with their interfaces). An empty catalog means you write new code from the supplied specifications and APIs. Do not search old output runs, other libraries, scratch directories or repository history for earlier implementations. The SQLSpec library and proof helpers in your crates are always available";

/// The rule of the correctness objective (context, brief and objective status).
pub const CORRECTNESS_RULE: &str = "Verus checks the whole frozen crate with 0 errors and the compiled library meets the checks of the run's validation policy at every configured worker count (validation.json: tests_and_references compares exactly with independent references at every admission binding and runs the generated tiny cases; formal_proofs runs the benchmark bindings on the full data and requires agreement with the saved answers of other engines where given)";

/// How exact verified submissions of the execution-time objective are ranked (`query::evaluation` computes `score_ns`).
pub const SCORE_RULE: &str = "score_ns = the geometric mean of the exact hot medians over the whole benchmark matrix: every benchmark binding at every configured worker count, each cell weighing equally (so every binding and every worker count weighs equally, and a given relative speedup counts the same at a fast and at a slow cell); lower is better; no score unless every cell was measured. A concrete statement has one benchmark binding";

pub const PERFORMANCE_RULE: &str = "every submission must first be an exact verified candidate (whole-crate Verus --no-cheating with 0 errors, then the checks of the run's validation policy at every configured worker count, validation.json; anything else is recorded and never promoted). The same submission is measured at every benchmark binding (a concrete statement's one binding, or the user's named bindings of a template: samples of the parameter domain, not the proof domain) and every configured worker count. Among exact verified submissions the lowest score_ns wins, where score_ns = the geometric mean of the exact hot medians over that whole matrix; one submission is selected for all cells (never a per-binding or per-worker-count winner). User-supplied runtime targets, per benchmark binding and worker count, are search guidance with their recorded provenance and timing scope, not a same-window comparison. The run continues until the user's submission or cost guard, or ends earlier by the user's early stop when one is set (early_stop, with its rule); the exact verified submission with the lowest score_ns is qualified and served, and its final hot runtime is measured again at every benchmark binding and worker count in timing windows of its own. A slower or failed submission is recorded and does not replace a faster one";

/// A user-supplied runtime target of the execution-time objective at one benchmark binding and worker count: search
/// guidance with its provenance, never a same-window comparison (no win over the system that produced it is claimed
/// from it).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RuntimeTarget {
    /// The benchmark binding (by name) the target was measured at; absent for a concrete statement, whose one binding
    /// is `statement`.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub binding: Option<String>,
    pub workers: usize,
    /// Hot median wall time, in nanoseconds, a candidate should beat at `workers`.
    pub median_ns: u64,
    /// Who measured what, where and when (system, host, data version, date).
    pub provenance: String,
    /// What the measured time includes and excludes (for example: one hot query call, output decoding excluded).
    pub timing_scope: String,
    /// The system whose measured time this target is (for example `ReferenceDB`, another synthesized engine), named in the prompt's goal and target
    /// table. Absent: the engine a GenDB baselines provenance names (`TargetSource`: the faster of DuckDB and Umbra), and
    /// the request keeps its identity.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub system: Option<String>,
}

impl RuntimeTarget {
    /// The benchmark binding the target is for.
    pub fn binding_name(&self) -> &str {
        self.binding.as_deref().unwrap_or(CONCRETE_BINDING)
    }

    /// Who set the target as the prompt names it: its `system`, else the setting engine of a GenDB baselines provenance,
    /// else `-`.
    pub fn set_by(&self) -> String {
        match &self.system {
            Some(system) => system.clone(),
            None => TargetSource::parse(&self.provenance).as_ref().map_or_else(|| "-".to_string(), TargetSource::setting_engine),
        }
    }
}

/// The one reference system every target names (`RuntimeTarget::system`), when all of them name the same one: the goal
/// then names that system instead of DuckDB and Umbra. `None` without targets, or when any target names none or another.
pub fn reference_system(targets: &[RuntimeTarget]) -> Option<&str> {
    let first = targets.first()?.system.as_deref()?;
    targets.iter().all(|t| t.system.as_deref() == Some(first)).then_some(first)
}

/// The user's optional early stop of the execution-time objective: the submission guard is a maximum, and the search
/// ends before the next author call once the submission the session would select (the first in
/// `qualification_order`: lowest score_ns) has, at every benchmark binding and configured worker count, an exact hot
/// median at least `min_speedup` times below that cell's runtime target (`median_ns * min_speedup <=
/// target.median_ns`). Tying the stop to the selected submission means the served candidate is the one that met the
/// threshold; a faster scoring submission that misses it at some cell keeps the search open. Medians of different
/// submissions never combine; the request must supply a target at every cell. Qualification, admission and
/// the final serve are unchanged: if the witness then fails qualification, the next submission in the same order is
/// qualified as usual, may not meet the threshold, and the stop is not undone (the summary records the witness and
/// every qualification attempt).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct EarlyStop {
    /// The whole-number speedup over every target that ends the search (at least 1).
    pub min_speedup: u32,
}

impl EarlyStop {
    /// The rule as authors and records read it.
    pub fn rule(&self) -> String {
        format!(
            "the user's early stop: once the exact verified submission with the lowest score_ns (the one GenDB selects) has, at every benchmark binding and configured worker count, an official exact hot median at most 1/{n} of that cell's runtime target (at least {n}x faster than every target), no further candidate is requested, even below the submission guard; that submission is qualified, served and measured again as usual. Medians of different submissions do not combine, and a failed or unverified submission or a local trial never triggers it. When your own local verified trials already indicate this threshold at every benchmark binding and configured worker count, submit promptly for the official evaluation instead of polishing further in the same call",
            n = self.min_speedup
        )
    }
}

/// Which objective a prepared context declares (`objective.kind`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Objective {
    Correctness,
    Performance,
}

impl Objective {
    pub fn of(context: &Value) -> Objective {
        if context["objective"]["kind"] == PERFORMANCE_OBJECTIVE { Objective::Performance } else { Objective::Correctness }
    }
}

/// The verified query role's policy. It holds no state: every decision is a function of the prepared context and
/// the ledger's trials.
#[derive(Clone, Copy, Debug, Default)]
pub struct VerifiedQueryPolicy;

impl RolePolicy for VerifiedQueryPolicy {
    fn author_prompt(&self, input: &PromptInput) -> String {
        author_prompt(input)
    }

    fn repair_revision(&self, evaluation: &Value) -> Option<&'static str> {
        framework_repair(evaluation)
    }

    fn submission_code(&self, frozen_dir: &Path, candidate: &Value, workspace: Option<&Path>) -> Value {
        crate::query::candidate::submission_code(frozen_dir, candidate, workspace)
    }

    fn objective_status(&self, context: &Value, trials: &[Trial]) -> Value {
        objective_status(context, trials)
    }

    /// The correctness objective needs one exact verified candidate; the execution-time objective stops early only by
    /// the user's `early_stop` rule. Either stops before the next author call.
    fn search_stop(&self, context: &Value, trials: &[Trial]) -> Option<StopReason> {
        match Objective::of(context) {
            Objective::Correctness => trials.iter().any(Trial::eligible).then_some(StopReason::FirstEligibleCandidate),
            Objective::Performance => early_stop_witness(context, trials).map(|_| StopReason::EarlyStopMinSpeedup),
        }
    }
}

/// The speedup factor of the early-stop bar the prompt states: the user's `early_stop.min_speedup` of this objective
/// (for the workload role, of its first statement that sets one); 5 when none is set.
fn bar_factor(context: &Value) -> u64 {
    let of = |objective: &Value| objective["early_stop"]["min_speedup"].as_u64();
    of(&context["objective"])
        .or_else(|| context["statements"].as_array().into_iter().flatten().find_map(|s| of(&s["objective"])))
        .unwrap_or(5)
}

/// `text` with the bar placeholders replaced by the factor of `context` (`5x`, `1/5`).
fn with_bar(text: String, context: &Value) -> String {
    let factor = bar_factor(context);
    text.replace(sections::BAR_FRACTION, &format!("1/{factor}")).replace(sections::BAR, &format!("{factor}x"))
}

/// The role sections both prompts share in their "How to work" text.
fn how_to_work(template: &str, common_dir: &str) -> String {
    template
        .replace("@PROOF_ADVICE@", sections::PROOF_ADVICE)
        .replace("@REUSE_ADVICE@", &sections::REUSE_ADVICE.replace("@COMMON_DIR@", common_dir))
        .replace("@PARALLEL_ADVICE@", sections::PARALLEL_ADVICE)
        .replace("@CHECK_ECONOMY@", sections::CHECK_ECONOMY)
}

/// A query role section with its objective-dependent phrases (`sections::QUERY_OBJECTIVE_PHRASES`) for `objective`.
fn for_objective(section: &str, objective: Objective) -> String {
    sections::QUERY_OBJECTIVE_PHRASES.iter().fold(section.to_string(), |text, &(placeholder, execution_time, correctness)| {
        text.replace(placeholder, match objective {
            Objective::Performance => execution_time,
            Objective::Correctness => correctness,
        })
    })
}

/// The key paths at the top of a prompt: every `files` entry of the prepared context and this prompt's saved copy, then
/// the scope rules.
fn key_paths(context: &Value, prompt_file: &Path) -> String {
    let mut lines = vec!["# Key paths and scope".to_string(), String::new()];
    for (name, path) in context["files"].as_object().into_iter().flatten().filter(|(_, path)| !path.is_null()) {
        lines.push(format!("- `{name}`: {}", path.as_str().map_or_else(|| path.to_string(), str::to_string)));
    }
    lines.push(format!("- `this_prompt`: {} (this complete prompt, saved before the call; reread it there)", prompt_file.display()));
    lines.push(String::new());
    lines.push(sections::SCOPE_RULES.to_string());
    lines.join("\n")
}

/// Every submission's official result as the next attempt reads it: counted or not (a framework failure is not), the
/// status, the first line of its error, the score, an unchanged resubmission's original, and per benchmark cell of
/// `cells` the official exact median and whether it is at or below the early-stop bar (target / `factor`). A continuing
/// session's incumbent (iteration 0) also carries its provenance (`incumbent`), its directory and whether its
/// evaluation is a render-only stand-in (`render_only`).
pub fn submission_results(trials: &[Trial], cells: &[(String, u64)], targets: &[RuntimeTarget], factor: Option<u64>) -> Value {
    let results: Vec<Value> = trials
        .iter()
        .map(|trial| {
            let e = &trial.evaluation;
            let cells: Vec<Value> = cells
                .iter()
                .map(|(binding, workers)| {
                    let median = exact_median_meeting(trial, binding, *workers, |_| true);
                    let target = targets.iter().find(|t| t.binding_name() == binding && t.workers as u64 == *workers).map(|t| t.median_ns);
                    let met_bar = median.zip(target).zip(factor).map(|((m, t), f)| u128::from(m) * u128::from(f) <= u128::from(t));
                    json!({"binding":binding,"workers":workers,"median_ns":median,"met_bar":met_bar})
                })
                .collect();
            let mut result = json!({"iteration":trial.iteration,"counted":!trial.framework_failure(),"status":e["status"],"eligible":e["eligible"],
                "failure_class":e["failure_class"],"error_first_line":e["error"].as_str().map(|error| error.lines().next().unwrap_or_default()),
                "score_ns":e["score_ns"],"duplicate_of_iteration":e["duplicate_of_iteration"],"cells":cells});
            if trial.candidate.get("incumbent").is_some() {
                result["incumbent"] = trial.candidate["incumbent"].clone();
                result["directory"] = json!(trial.directory);
                result["render_only"] = json!(e.get(crate::controller::run::RENDER_ONLY_FIELD).is_some());
            }
            result
        })
        .collect();
    json!(results)
}

/// The complete prompt of one query author call.
pub fn author_prompt(input: &PromptInput) -> String {
    let context = input.context;
    let objective = Objective::of(context);
    let trials = evaluated_trials(input.feedback);
    let runtime_targets = runtime_targets(&context["runtime_targets"]);
    let factor = configured_early_stop(context).map(|stop| u64::from(stop.min_speedup.max(1)));
    let (targets, cells) = match objective {
        Objective::Performance => (json!({"cells":target_cells(&runtime_targets, factor),"early_stop_factor":factor}), benchmark_cells(context)),
        Objective::Correctness => (json!({"cells":[]}), vec![]),
    };
    let data = data_sections::render(&DataViews {
        author: AuthorKind::Query,
        context,
        targets: &targets,
        submissions: &submission_results(&trials, &cells, &runtime_targets, factor),
        objective: &objective_status(context, &trials),
        handoff: input.handoff,
        ledger: input.ledger,
        latest: &latest_delta(input.feedback, &trials),
    });
    let goal = match (objective, reference_system(&runtime_targets)) {
        (Objective::Performance, None) => sections::QUERY_GOAL.replace("@TARGET@", sections::GOAL_TARGET),
        (Objective::Performance, Some(system)) => sections::QUERY_GOAL.replace("@TARGET@", &sections::GOAL_TARGET_SYSTEM.replace("@SYSTEM@", system)),
        (Objective::Correctness, _) => sections::CORRECTNESS_QUERY_GOAL.to_string(),
    };
    let policy = if context["storage_policy"]["kind"] == PHYSICAL_ONLY { sections::PHYSICAL_ONLY_POLICY } else { "" };
    // Under fixed_flat the stored data is fixed: its own task, storage, ownership, way of working and tool sections.
    let flat = context["storage_policy"]["kind"] == FIXED_FLAT;
    let pick = |default: &'static str, fixed_flat: &'static str| if flat { fixed_flat } else { default };
    // The correctness objective has its own evaluation and way of working (no targets, selection or measuring advice).
    let (evaluation, way_of_working) = match objective {
        Objective::Performance => (sections::QUERY_EVALUATION, pick(sections::QUERY_HOW_TO_WORK, sections::FLAT_QUERY_HOW_TO_WORK)),
        Objective::Correctness => (sections::CORRECTNESS_QUERY_EVALUATION, sections::CORRECTNESS_QUERY_HOW_TO_WORK),
    };
    let parts = [
        key_paths(context, input.prompt_file),
        format!("GenDB owns evaluation and is requesting submission {}/{}.", input.submission, count_guard_text(input.limits.max_iterations)),
        pick(sections::QUERY_TASK, sections::FLAT_QUERY_TASK).to_string(),
        goal,
        for_objective(pick(sections::QUERY_STORAGE, sections::FIXED_FLAT_STORAGE), objective),
        pick(sections::QUERY_FIXED, sections::FLAT_QUERY_FIXED).to_string(),
        policy.to_string(),
        evaluation.replace(sections::CORRECTNESS_GATE, sections::QUERY_CORRECTNESS_GATE),
        sections::ATTEMPTS.to_string(),
        how_to_work(way_of_working, "`src/agent/common/`"),
        for_objective(sections::QUERY_INPUTS, objective),
        for_objective(pick(sections::QUERY_TOOLS, sections::FLAT_QUERY_TOOLS), objective),
        sections::submission("verus-query.json"),
        sections::PROCESSES_APPENDIX.to_string(),
        data,
    ];
    with_bar(parts.iter().filter(|part| !part.is_empty()).cloned().collect::<Vec<_>>().join("\n\n"), context)
}

/// The user's runtime targets recorded in a context (`runtime_targets`); none when absent.
fn runtime_targets(recorded: &Value) -> Vec<RuntimeTarget> {
    serde_json::from_value(recorded.clone()).unwrap_or_default()
}

/// Per runtime target, its cell as the prompt shows it: the target, the early-stop bar (target / `factor`), the engine
/// that set it and its provenance (`source` when GenDB's baselines form parses, else the text) and timing scope.
fn target_cells(targets: &[RuntimeTarget], factor: Option<u64>) -> Vec<Value> {
    targets
        .iter()
        .map(|t| {
            // A target that names its system is shown with its own provenance, never read as a baselines provenance.
            let source = if t.system.is_some() { None } else { TargetSource::parse(&t.provenance) };
            json!({"binding":t.binding_name(),"workers":t.workers,"target_ns":t.median_ns,"bar_ns":factor.map(|f| t.median_ns / f),
                "engine":t.set_by(),"system":t.system,
                "source":source.map(|s| json!({"file":s.file,"key":s.key,"remark":s.remark,
                    "engines":s.engine_ms.iter().map(|(engine, _)| engine.as_str()).collect::<Vec<_>>().join(" and ")})),
                "provenance":t.provenance,"timing_scope":t.timing_scope})
        })
        .collect()
}

/// The evaluated trials among the feedback events (serialized `Trial`s), the last record per iteration, in iteration
/// order. Call and local-job events are not trials.
pub(super) fn evaluated_trials(feedback: &[Value]) -> Vec<Trial> {
    let mut by_iteration = BTreeMap::new();
    for event in feedback.iter().filter(|event| event.get("evaluation").is_some_and(|e| !e.is_null())) {
        if let Ok(trial) = serde_json::from_value::<Trial>(event.clone()) {
            by_iteration.insert(trial.iteration, trial);
        }
    }
    by_iteration.into_values().collect()
}

/// The latest call's delta: the call, its outcome, its local jobs (with the session's so far) and, once evaluated, the
/// evaluation digest of its iteration; `incumbent` when the only event so far is a continuing session's incumbent. A call, its local jobs and its trial arrive as separate events of one iteration
/// (`controller::role::{call_event, local_jobs_event}`); the latest non-null value of each field is shown.
pub(super) fn latest_delta(feedback: &[Value], trials: &[Trial]) -> Value {
    let Some(last) = feedback.last() else { return Value::Null };
    let iteration = &last["iteration"];
    let latest = |field: &str| {
        feedback.iter().rev().filter(|event| &event["iteration"] == iteration).map(|event| &event[field]).find(|v| !v.is_null()).cloned().unwrap_or(Value::Null)
    };
    let call = latest("call");
    let jobs_of_call = feedback.iter().rev().find(|event| event["local_jobs"].is_object() && event["call"] == call);
    let session_jobs = feedback.iter().rev().find(|event| event["session_local_jobs"].is_object());
    let trial = trials.iter().rev().find(|t| iteration.as_u64() == Some(u64::from(t.iteration)));
    let evaluation = trial.map(|trial| {
        let e = &trial.evaluation;
        json!({"status":e["status"],"eligible":e["eligible"],"failure_class":e["failure_class"],"error":e["error"],"verus_record":e["verus_record"],
            "verus":e["verus"],"runs":runs_view(e),"boundary_cases":e.pointer("/boundary/cases").and_then(Value::as_array).map(Vec::len),
            "score_ns":e["score_ns"],"storage":storage_view(e),"duplicate_of_iteration":e["duplicate_of_iteration"],"record":trial.directory,
            "counted":!framework_failure(e),
            "framework_failure":framework_failure(e).then_some("the framework failed, not your candidate: this submission was NOT counted and its verdict is never reused; you may resubmit the same candidate")})
    });
    // Before the first call of a continuing session the only event is the incumbent (iteration 0, no call).
    let incumbent = trial.is_some_and(|trial| trial.candidate.get("incumbent").is_some()) && call.is_null();
    json!({"iteration":iteration,"call":call,"author_outcome":latest("author_outcome"),
        "local_jobs":jobs_of_call.map(|event| event["local_jobs"].clone()),"session_local_jobs":session_jobs.map(|event| event["session_local_jobs"].clone()),
        "evaluation":evaluation,"incumbent":incumbent})
}

/// One run per admission binding and worker count over the prepared data (`real_data.cells`; the scored
/// `measurements` are a copy of the benchmark bindings' cells): exactness, hot runtime, per-call CPU and device reads,
/// dispatch and storage requests. Each field's meaning is stated once; the full cells stay in the evaluation record.
fn runs_view(evaluation: &Value) -> Value {
    let Some(cells) = evaluation.pointer("/real_data/cells").and_then(Value::as_array) else { return Value::Null };
    let per_call = |cell: &Value, field: &str| cell["usage"].as_array().into_iter().flatten().map(|call| call[field].clone()).collect::<Vec<_>>();
    let runs: Vec<Value> = cells
        .iter()
        .map(|c| {
            json!({"binding":c["binding"],"arguments":c["arguments"],"workers":c["workers"],"status":c["status"],"comparison":c["comparison"],
                "reference_rows":c["reference_rows"],"median_hot_ns":c["median_hot_wall_ns"],
                "per_call":{"wall_ns":per_call(c, "wall_ns"),"caller_cpu_ns":per_call(c, "caller_cpu_ns"),"process_user_ns":per_call(c, "process_user_ns"),
                    "process_system_ns":per_call(c, "process_system_ns"),"device_read_bytes":c.pointer("/process_io/read_bytes_per_call")},
                "calling_thread_share_permille":c["calling_thread_share_permille"],
                "dispatch":{"spawned":c.pointer("/dispatch/spawned"),"joined":c.pointer("/dispatch/joined"),"ranges_reported":c.pointer("/dispatch/ranges_reported")},
                "storage_requests":c["storage_requests"]})
        })
        .collect();
    json!({"cells":runs,"meaning":{
        "per_call":"index 0 is the warm call, then the hot calls; median_hot_ns is the median hot wall_ns; score_ns uses median_hot_ns of every benchmark binding (evaluation measurements) at every worker count; caller_cpu_ns is the calling thread, process_user_ns and process_system_ns all threads of the child",
        "wall_ns":evaluation.pointer("/measurements/0/boundary"),"device_read_bytes":cells.first().and_then(|c| c.pointer("/process_io/meaning")),
        "storage_requests":evaluation["requested_bytes_meaning"],"dispatch":"the last call's spawned and joined workers and reported row ranges (the ranges are in the evaluation record)"}})
}

/// Per storage, the asset the evaluation read (query `storage[]`) or checked and built (workload storage
/// `storages[].asset`): its size and its recorded one-time build, and whether this evaluation reused the asset or
/// built it (and so paid the build).
fn storage_view(evaluation: &Value) -> Value {
    let read = evaluation["storage"].as_array().into_iter().flatten().map(|s| {
        json!({"name":s["name"],"package":s["package"],"asset":s["asset"],"admitted":s["admitted"],"storage_bytes":s["storage_bytes"],
            "build_wall_ns":s["build_wall_ns"],"asset_reused":s["asset_built_now"].as_bool().map(|built| !built)})
    });
    let built = evaluation["storages"].as_array().into_iter().flatten().map(|s| {
        let asset = &s["asset"];
        json!({"name":s["name"],"package":s["package"],"asset":asset["asset"],"storage_bytes":asset["storage_bytes"],
            "canonical_column_bytes":asset["canonical_column_bytes"],"build_wall_ns":asset["build_wall_ns"],"asset_reused":asset["built_now"].as_bool().map(|built| !built)})
    });
    let assets: Vec<Value> = read.chain(built).collect();
    if assets.is_empty() {
        return Value::Null;
    }
    json!({"assets":assets,"meaning":"build_wall_ns is the asset's recorded one-time build; this evaluation paid it only where asset_reused is false. storage_bytes: the stored parts"})
}

/// The objective over the session's trials. Correctness: met at the first eligible trial. Execution time: the
/// benchmark matrix of the submission the session selects, against the user's runtime targets when supplied
/// (`execution_time_status`).
pub fn objective_status(context: &Value, trials: &[Trial]) -> Value {
    match Objective::of(context) {
        Objective::Performance => {
            let targets: Vec<RuntimeTarget> = serde_json::from_value(context["runtime_targets"].clone()).unwrap_or_default();
            let mut objective = execution_time_status(&benchmark_cells(context), &targets, trials, configured_early_stop(context));
            objective["kind"] = json!(PERFORMANCE_OBJECTIVE);
            objective["exact_verified_iterations"] = json!(trials.iter().filter(|t| t.eligible()).map(|t| t.iteration).collect::<Vec<_>>());
            let best = trials.iter().filter(|t| t.eligible() && t.score_ns().is_finite()).min_by(|a, b| a.score_ns().total_cmp(&b.score_ns()));
            objective["current_best_score"] = json!({"score_ns":best.map(|t| t.evaluation["score_ns"].clone()),"iteration":best.map(|t| t.iteration),"selection":SCORE_RULE});
            if let Some(stop) = configured_early_stop(context) {
                let witness = early_stop_witness(context, trials);
                objective["early_stop"] = json!({"min_speedup":stop.min_speedup,"status":if witness.is_some() {"met"} else {"not_met"},
                    "witness":witness,"rule":stop.rule()});
            }
            objective
        }
        Objective::Correctness => {
            let met = trials.iter().find(|t| t.eligible());
            json!({"status":if met.is_some() {"met"} else {"unmet"},"kind":CORRECTNESS_OBJECTIVE,
                "iteration":met.map(|t| t.iteration),"rule":CORRECTNESS_RULE})
        }
    }
}

/// The benchmark matrix of the prepared context: every benchmark binding (`objective.bindings[].name`; a context
/// without them, prepared before benchmark bindings existed, has the concrete binding) at every configured worker
/// count (`hardware.threads`), bindings outer.
fn benchmark_cells(context: &Value) -> Vec<(String, u64)> {
    let named: Vec<String> = context["objective"]["bindings"].as_array().into_iter().flatten().filter_map(|b| b["name"].as_str().map(str::to_string)).collect();
    let bindings = if named.is_empty() { vec![CONCRETE_BINDING.to_string()] } else { named };
    let workers: Vec<u64> = serde_json::from_value(context["hardware"]["threads"].clone()).unwrap_or_default();
    bindings.iter().flat_map(|b| workers.iter().map(move |&w| (b.clone(), w))).collect()
}

/// The benchmark matrix of the submission the session selects (the first in `qualification_order`: lowest score_ns):
/// per cell its exact hot median, and the user's target when one is supplied. Without targets the status is `open`
/// (optimize until the user's guards; an unchanged resubmission ends the search); with targets it is `met` when the
/// selected submission is exact and below the target at every targeted cell, else `unmet`. With the user's early stop,
/// each targeted cell also states its early-stop bound (`early_stop_max_ns` = target / min_speedup, the witness
/// condition `median * min_speedup <= target` in whole ns) and whether the selected median meets it
/// (`early_stop_met`), separate from the 1x `met`. Medians of different submissions never combine; historical and saved
/// medians never count; the final measurement of the served package is the recorded result.
fn execution_time_status(cells: &[(String, u64)], targets: &[RuntimeTarget], trials: &[Trial], early_stop: Option<EarlyStop>) -> Value {
    let selected = qualification_order(trials).first().copied();
    let target_at = |binding: &str, workers: u64| targets.iter().find(|t| t.binding_name() == binding && t.workers as u64 == workers);
    let mut all_met = true;
    let matrix: Vec<Value> = cells
        .iter()
        .map(|(binding, workers)| {
            let median = selected.and_then(|trial| exact_median_meeting(trial, binding, *workers, |_| true));
            let target = target_at(binding, *workers).map(|t| t.median_ns);
            let met = target.map(|t| median.is_some_and(|m| m < t));
            all_met &= met.unwrap_or(true);
            let mut cell = json!({"binding":binding,"workers":workers,"selected_median_ns":median,"target_median_ns":target,"met":met,
                "target_minus_selected_ns":target.zip(median).map(|(t, m)| (i128::from(t) - i128::from(m)).to_string())});
            if let (Some(stop), Some(target)) = (early_stop.filter(|stop| stop.min_speedup >= 1), target) {
                cell["early_stop_max_ns"] = json!(target / u64::from(stop.min_speedup));
                cell["early_stop_met"] = json!(median.is_some_and(|m| u128::from(m) * u128::from(stop.min_speedup) <= u128::from(target)));
            }
            cell
        })
        .collect();
    let (status, rule) = match (targets.is_empty(), all_met) {
        (true, _) => ("open", "no runtime target: lower score_ns of candidates submitted in this run until the user's guards; the selected submission's matrix is shown"),
        (false, met) => (if met { "met" } else { "unmet" }, "the selected submission (lowest score_ns) has, at every targeted benchmark binding and worker count, an exact hot median below the user's target (per cell: met = below the 1x target; with an early stop, early_stop_met = at most early_stop_max_ns, which is what early_stop.status requires at every cell)"),
    };
    json!({"status":status,"selected_iteration":selected.map(|t| t.iteration),"matrix":matrix,"rule":rule,
        "target_source":"each target's provenance and timing_scope: runtime_targets in CURRENT FACTS and performance.json",
        "basis":"official submitted measurements in this run of one selected submission (never a combination of submissions) against user-supplied targets (search guidance with provenance); no same-window comparison with the system that produced a target is made or claimed"})
}

/// The user's early stop recorded in the prepared context (`objective.early_stop`), if any.
fn configured_early_stop(context: &Value) -> Option<EarlyStop> {
    serde_json::from_value(context["objective"]["early_stop"].clone()).ok()
}

/// The user's early stop is met by the trial selected first (`qualification_order`): at every benchmark binding and
/// configured worker count a runtime target exists, and every measurement cell of that trial there is exact with
/// `median_ns * min_speedup <= target`. Returns the witness (iteration, threshold and per cell median and target);
/// `None` without an early stop, without a complete target matrix, without an eligible trial or when the selected
/// trial misses the threshold at some cell (another trial meeting it there does not count).
fn early_stop_witness(context: &Value, trials: &[Trial]) -> Option<Value> {
    let stop = configured_early_stop(context).filter(|stop| stop.min_speedup >= 1)?;
    let targets: Vec<RuntimeTarget> = serde_json::from_value(context["runtime_targets"].clone()).ok()?;
    let target_at = |binding: &str, w: u64| targets.iter().find(|t| t.binding_name() == binding && t.workers as u64 == w).map(|t| t.median_ns);
    let target_ns: Vec<(String, u64, u64)> =
        benchmark_cells(context).into_iter().map(|(b, w)| target_at(&b, w).map(|ns| (b, w, ns))).collect::<Option<_>>()?;
    if target_ns.is_empty() {
        return None;
    }
    let selected = *qualification_order(trials).first()?;
    let cells: Vec<Value> = target_ns
        .iter()
        .map(|(binding, workers, target)| {
            let median = exact_median_meeting(selected, binding, *workers, |median| u128::from(median) * u128::from(stop.min_speedup) <= u128::from(*target))?;
            Some(json!({"binding":binding,"workers":workers,"median_ns":median,"target_median_ns":target}))
        })
        .collect::<Option<_>>()?;
    Some(json!({"iteration":selected.iteration,"min_speedup":stop.min_speedup,"cells":cells,"selection":"lowest score_ns (qualified first)"}))
}

/// The trial's largest exact hot median at benchmark binding `binding` and `workers` when it has at least one
/// measurement cell there, every such cell's result was checked (exact, or agreeing with saved answers under the
/// validation policy formal_proofs: `checked_cell_status`) and each median passes `meets`. A measurement without a binding
/// name (recorded before benchmark bindings existed) is the concrete binding's.
fn exact_median_meeting(trial: &Trial, binding: &str, workers: u64, meets: impl Fn(u64) -> bool) -> Option<u64> {
    let mut largest = None;
    let at_cell = |cell: &&Value| cell["workers"].as_u64() == Some(workers) && cell["binding"].as_str().unwrap_or(CONCRETE_BINDING) == binding;
    for cell in trial.evaluation["measurements"].as_array()?.iter().filter(at_cell) {
        let median = cell["median_ns"].as_u64().filter(|&median| gendb_verification::admission::validation::checked_cell_status(&cell["status"]) && meets(median))?;
        largest = largest.max(Some(median));
    }
    largest
}

/// The workload storage role's policy: the storage prompt, and the objective that admits the first verified, built
/// submission. It holds no state.
#[derive(Clone, Copy, Debug, Default)]
pub struct StoragePolicy;

impl RolePolicy for StoragePolicy {
    fn author_prompt(&self, input: &PromptInput) -> String {
        storage_author_prompt(input)
    }

    fn objective_status(&self, _context: &Value, trials: &[Trial]) -> Value {
        storage_objective_status(trials)
    }

    /// One verified, built submission is admitted; the session stops before the next author call.
    fn search_stop(&self, _context: &Value, trials: &[Trial]) -> Option<StopReason> {
        trials.iter().any(Trial::eligible).then_some(StopReason::FirstEligibleCandidate)
    }

    fn repair_revision(&self, evaluation: &Value) -> Option<&'static str> {
        framework_repair(evaluation)
    }
}

/// Known framework defects that judged a retained submission wrongly, with the repair revision under which the
/// framework re-evaluates it on resume (`controller::run`, no author call):
/// - `lossless-theorem-record-1`: storage publication looked for `theorem_storage_lossless` in `gendb_entry.rs`
///   (it is in the generated binding module) and refused every storage.
fn framework_repair(evaluation: &Value) -> Option<&'static str> {
    let error = evaluation["error"].as_str()?;
    error.contains("does not define theorem gendb_entry::storage::theorem_storage_lossless").then_some("lossless-theorem-record-1")
}

/// The complete prompt of one workload storage author call.
pub fn storage_author_prompt(input: &PromptInput) -> String {
    let context = input.context;
    let trials = evaluated_trials(input.feedback);
    let by_statement: Vec<Vec<Value>> = context["statements"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|statement| target_cells(&runtime_targets(&statement["objective"]["runtime_targets"]), None))
        .collect();
    let data = data_sections::render(&DataViews {
        author: AuthorKind::WorkloadStorage,
        context,
        targets: &json!({"by_statement":by_statement}),
        submissions: &submission_results(&trials, &[], &[], None),
        objective: &storage_objective_status(&trials),
        handoff: input.handoff,
        ledger: input.ledger,
        latest: &latest_delta(input.feedback, &trials),
    });
    let choices = storage_choices(context["storage_policy"]["kind"].as_str().unwrap_or(UNRESTRICTED));
    let policy = if context["storage_policy"]["kind"] == PHYSICAL_ONLY {
        sections::PHYSICAL_ONLY_POLICY.to_string()
    } else {
        format!("# Storage policy: unrestricted\n\nYou may choose {choices}; every choice must be proved against the fixed storage obligation.")
    };
    let parts = [
        key_paths(context, input.prompt_file),
        format!("GenDB owns evaluation and is requesting submission {}/{}.", input.submission, count_guard_text(input.limits.max_iterations)),
        sections::WORKLOAD_TASK.to_string(),
        sections::WORKLOAD_GOAL.replace("@TARGET@", &workload_goal_target(context)),
        sections::WORKLOAD_FIXED.to_string(),
        policy,
        sections::WORKLOAD_EVALUATION.to_string(),
        sections::ATTEMPTS.to_string(),
        how_to_work(sections::WORKLOAD_HOW_TO_WORK, "the storage crate's `src/builder/common/` (builder code) or `src/stores/<name>/interface/common/` (reader code)"),
        sections::WORKLOAD_INPUTS.to_string(),
        sections::WORKLOAD_TOOLS.to_string(),
        sections::submission("verus-storages.json"),
        sections::PROCESSES_APPENDIX.to_string(),
        data,
    ];
    with_bar(parts.iter().filter(|part| !part.is_empty()).cloned().collect::<Vec<_>>().join("\n\n"), context)
}

/// The workload goal's target sentence: the one reference system every statement's targets name, else DuckDB and Umbra.
fn workload_goal_target(context: &Value) -> String {
    let targets: Vec<RuntimeTarget> = context["statements"].as_array().into_iter().flatten().flat_map(|s| runtime_targets(&s["objective"]["runtime_targets"])).collect();
    match reference_system(&targets) {
        Some(system) => sections::WORKLOAD_GOAL_TARGET_SYSTEM.replace("@SYSTEM@", system),
        None => sections::WORKLOAD_GOAL_TARGET.to_string(),
    }
}

/// The storage objective over the session's trials: met at the first eligible (verified, built) trial.
pub fn storage_objective_status(trials: &[Trial]) -> Value {
    let met = trials.iter().find(|t| t.eligible());
    json!({"status":if met.is_some() {"met"} else {"unmet"},"kind":STORAGE_OBJECTIVE,"iteration":met.map(|t| t.iteration),"rule":STORAGE_RULE})
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::controller::ledger::TrialStatus;
    use crate::controller::limits::tests::limits;

    /// A call's saved prompt as the controller names it.
    const PROMPT: &str = "/run/queries/query-0000/calls/0002/prompt.txt";

    fn trial(iteration: u32, evaluation: Value) -> Trial {
        serde_json::from_value(json!({"iteration":iteration,"call_id":iteration,"candidate":{},"status":TrialStatus::Evaluated,"evaluation":evaluation})).unwrap()
    }

    fn targets() -> Value {
        json!([{"workers":1,"median_ns":1000,"provenance":"fixture engine, fixture host","timing_scope":"hot query call"}])
    }

    #[test]
    fn correctness_objective_is_met_and_stops_at_the_first_eligible_trial() {
        let context = json!({"objective":{"kind":CORRECTNESS_OBJECTIVE}});
        let failed = trial(1, json!({"eligible":false,"status":"proof_failure"}));
        assert_eq!(objective_status(&context, std::slice::from_ref(&failed))["status"], "unmet");
        assert_eq!(VerifiedQueryPolicy.search_stop(&context, std::slice::from_ref(&failed)), None);
        let trials = [failed, trial(2, json!({"eligible":true,"status":"verified_exact"}))];
        let status = objective_status(&context, &trials);
        assert_eq!((status["status"].as_str(), status["iteration"].as_u64()), (Some("met"), Some(2)));
        assert_eq!(VerifiedQueryPolicy.search_stop(&context, &trials), Some(StopReason::FirstEligibleCandidate));
    }

    #[test]
    fn execution_time_objective_compares_the_selected_submission_with_owner_targets_or_stays_open() {
        let context = json!({"objective":{"kind":PERFORMANCE_OBJECTIVE},"hardware":{"threads":[1]},"runtime_targets":targets()});
        let slow = trial(1, json!({"eligible":true,"measurements":[{"workers":1,"status":"exact","median_ns":1500}]}));
        let status = objective_status(&context, std::slice::from_ref(&slow));
        assert_eq!((status["status"].as_str(), status["kind"].as_str()), (Some("unmet"), Some(PERFORMANCE_OBJECTIVE)));
        assert_eq!(status["matrix"][0]["target_minus_selected_ns"], "-500");
        assert_eq!(status["matrix"][0]["binding"], CONCRETE_BINDING, "a measurement recorded without a binding is the concrete binding's");
        assert!(status["matrix"][0].get("provenance").is_none(), "provenance is stated once, in the facts");
        assert_eq!(VerifiedQueryPolicy.search_stop(&context, std::slice::from_ref(&slow)), None, "execution time runs to the user's guards");
        let trials = [slow, trial(2, json!({"eligible":true,"score_ns":900,"measurements":[{"workers":1,"status":"exact","median_ns":900}]}))];
        let status = objective_status(&context, &trials);
        assert_eq!((status["current_best_score"]["score_ns"].as_u64(), status["current_best_score"]["iteration"].as_u64()), (Some(900), Some(2)));
        assert_eq!((status["status"].as_str(), status["matrix"][0]["met"].as_bool()), (Some("met"), Some(true)));
        assert_eq!(status["selected_iteration"], 2);
        assert_eq!(status["exact_verified_iterations"], json!([1, 2]));
        let without_targets = json!({"objective":{"kind":PERFORMANCE_OBJECTIVE},"hardware":{"threads":[1]},"runtime_targets":[]});
        let open = objective_status(&without_targets, &trials);
        assert_eq!((open["status"].as_str(), open["matrix"][0]["selected_median_ns"].as_u64()), (Some("open"), Some(900)));
        assert_eq!(VerifiedQueryPolicy.search_stop(&without_targets, &trials), None);
        // Per-cell bests of different submissions never make the objective met.
        let two = json!({"objective":{"kind":PERFORMANCE_OBJECTIVE},"hardware":{"threads":[1, 4]},
            "runtime_targets":[{"workers":1,"median_ns":1000,"provenance":"p","timing_scope":"s"},{"workers":4,"median_ns":1000,"provenance":"p","timing_scope":"s"}]});
        let cells = |one: u64, four: u64| json!([{"workers":1,"status":"exact","median_ns":one},{"workers":4,"status":"exact","median_ns":four}]);
        let split = [trial(1, json!({"eligible":true,"score_ns":100,"measurements":cells(10, 2000)})), trial(2, json!({"eligible":true,"score_ns":200,"measurements":cells(2000, 10)}))];
        assert_eq!(objective_status(&two, &split)["status"], "unmet");
    }

    /// A template's matrix: the selected submission must meet the factor at every benchmark binding and worker count;
    /// a cell measured at another binding never stands in.
    #[test]
    fn template_early_stop_needs_every_binding_and_worker_cell_of_the_selected_submission() {
        let target = |binding: &str, workers: u64| json!({"binding":binding,"workers":workers,"median_ns":1000,"provenance":"fixture engine","timing_scope":"hot query call"});
        let context = json!({"objective":{"kind":PERFORMANCE_OBJECTIVE,"early_stop":{"min_speedup":5},
                "bindings":[{"name":"qgen","origin":"benchmark","arguments":["15"]},{"name":"wide","origin":"benchmark","arguments":["49"]}]},
            "hardware":{"threads":[1, 4]},"runtime_targets":[target("qgen", 1), target("qgen", 4), target("wide", 1), target("wide", 4)]});
        let cell = |binding: &str, workers: u64, median: u64| json!({"binding":binding,"workers":workers,"status":"exact","median_ns":median});
        let all = trial(1, json!({"eligible":true,"score_ns":100,"measurements":[cell("qgen", 1, 200), cell("qgen", 4, 100), cell("wide", 1, 150), cell("wide", 4, 50)]}));
        assert_eq!(VerifiedQueryPolicy.search_stop(&context, std::slice::from_ref(&all)), Some(StopReason::EarlyStopMinSpeedup));
        let witness = &objective_status(&context, std::slice::from_ref(&all))["early_stop"]["witness"];
        assert_eq!(witness["cells"].as_array().map(Vec::len), Some(4));
        assert_eq!(witness["cells"][3], json!({"binding":"wide","workers":4,"median_ns":50,"target_median_ns":1000}));
        let one_binding = trial(1, json!({"eligible":true,"score_ns":100,"measurements":[cell("qgen", 1, 200), cell("qgen", 4, 100)]}));
        assert_eq!(VerifiedQueryPolicy.search_stop(&context, &[one_binding]), None, "a binding without cells never meets the threshold");
        let slow_wide = trial(1, json!({"eligible":true,"score_ns":100,"measurements":[cell("qgen", 1, 200), cell("qgen", 4, 100), cell("wide", 1, 150), cell("wide", 4, 201)]}));
        let status = objective_status(&context, &[slow_wide]);
        assert_eq!(status["early_stop"]["status"], "not_met");
        assert_eq!((status["status"].as_str(), status["matrix"].as_array().map(Vec::len)), (Some("met"), Some(4)), "below every target, not 5x everywhere");
        let slowest = &status["matrix"][3];
        assert_eq!((slowest["met"].as_bool(), slowest["early_stop_max_ns"].as_u64(), slowest["early_stop_met"].as_bool()), (Some(true), Some(200), Some(false)), "1x met, 5x not: {slowest}");
        assert_eq!(status["matrix"][2]["early_stop_met"], true);
    }

    #[test]
    fn early_stop_needs_one_exact_verified_trial_beating_every_target_by_the_factor() {
        let target = |workers: u64, median_ns: u64| json!({"workers":workers,"median_ns":median_ns,"provenance":"fixture engine","timing_scope":"hot query call"});
        let context = |targets: Value| json!({"objective":{"kind":PERFORMANCE_OBJECTIVE,"early_stop":{"min_speedup":5}},"hardware":{"threads":[1, 4]},"runtime_targets":targets});
        let measured = |iteration: u32, eligible: bool, one: u64, four: u64| {
            trial(iteration, json!({"eligible":eligible,"status":if eligible {"verified_exact"} else {"proof_failure"},"score_ns":one.min(four),
                "measurements":[{"workers":1,"status":"exact","median_ns":one},{"workers":4,"status":"exact","median_ns":four}]}))
        };
        let full = context(json!([target(1, 1000), target(4, 500)]));
        let fast = measured(1, true, 200, 100);
        assert_eq!(VerifiedQueryPolicy.search_stop(&full, std::slice::from_ref(&fast)), Some(StopReason::EarlyStopMinSpeedup), "5x exactly at both counts");
        let status = objective_status(&full, std::slice::from_ref(&fast));
        assert_eq!((status["early_stop"]["status"].as_str(), status["early_stop"]["witness"]["iteration"].as_u64()), (Some("met"), Some(1)));
        assert_eq!(status["early_stop"]["witness"]["cells"][1], json!({"binding":"statement","workers":4,"median_ns":100,"target_median_ns":500}));

        let short = measured(1, true, 200, 101);
        assert_eq!(VerifiedQueryPolicy.search_stop(&full, std::slice::from_ref(&short)), None, "just under 5x at one count");
        assert_eq!(objective_status(&full, std::slice::from_ref(&short))["early_stop"]["status"], "not_met");
        let unverified = measured(1, false, 1, 1);
        assert_eq!(VerifiedQueryPolicy.search_stop(&full, std::slice::from_ref(&unverified)), None, "a failed submission never stops early");
        let mixed = [measured(1, true, 200, 400), measured(2, true, 900, 100)];
        assert_eq!(VerifiedQueryPolicy.search_stop(&full, &mixed), None, "per-count wins of different submissions do not combine");
        // The witness must be the submission selection picks: a lower-scoring submission that misses 5x at 4 workers
        // keeps the search open although a later one meets 5x everywhere; once the selected one meets it, it stops.
        let mut winner_misses = measured(1, true, 10, 150);
        winner_misses.evaluation["score_ns"] = json!(39);
        let mut witness_only = measured(2, true, 200, 100);
        witness_only.evaluation["score_ns"] = json!(141);
        let unselected = [winner_misses, witness_only.clone()];
        assert_eq!(qualification_order(&unselected)[0].iteration, 1);
        assert_eq!(VerifiedQueryPolicy.search_stop(&full, &unselected), None, "the selected submission misses the threshold at 4 workers");
        let mut slower = measured(1, true, 900, 900);
        slower.evaluation["score_ns"] = json!(900);
        let selected = [slower, witness_only];
        assert_eq!(VerifiedQueryPolicy.search_stop(&full, &selected), Some(StopReason::EarlyStopMinSpeedup));
        assert_eq!(objective_status(&full, &selected)["early_stop"]["witness"]["iteration"], 2);
        let mut inexact = fast.clone();
        inexact.evaluation["measurements"][1]["status"] = json!("mismatch");
        assert_eq!(VerifiedQueryPolicy.search_stop(&full, &[inexact]), None);

        let incomplete = context(json!([target(1, 1000)]));
        assert_eq!(VerifiedQueryPolicy.search_stop(&incomplete, std::slice::from_ref(&fast)), None, "a missing target never establishes the stop");
        let mut legacy = full.clone();
        legacy["objective"].as_object_mut().unwrap().remove("early_stop");
        assert_eq!(VerifiedQueryPolicy.search_stop(&legacy, std::slice::from_ref(&fast)), None, "without early_stop the search runs to the guards");
        assert!(objective_status(&legacy, std::slice::from_ref(&fast)).get("early_stop").is_none());
        assert!(objective_status(&legacy, std::slice::from_ref(&fast))["matrix"][0].get("early_stop_max_ns").is_none(), "no early stop, no per-cell bound");

        let limits = limits();
        let prompt = |context: &Value| author_prompt(&PromptInput { context, feedback: &[], iteration: 1, submission: 1, limits: &limits, ledger: &json!({}), prompt_file: Path::new(PROMPT), handoff: &Value::Null });
        assert!(prompt(&full).contains("at most 1/5 of the target in every cell") && prompt(&full).contains("submit promptly"));
        assert!(prompt(&full).contains("| Binding | Workers | Target ms | Set by | 5x bar ms | Selected meets bar |"), "the early-stop bar per cell is a current fact");
        assert!(prompt(&full).contains("| statement | 1 | 0.001 | - | 0.000 | - |"), "{}", prompt(&full));
    }

    #[test]
    fn storage_objective_stops_at_the_first_verified_built_submission() {
        let failed = trial(1, json!({"eligible":false,"status":"proof_failure"}));
        assert_eq!(StoragePolicy.search_stop(&json!({}), std::slice::from_ref(&failed)), None);
        let trials = [failed, trial(2, json!({"eligible":true,"status":"verified_built"}))];
        assert_eq!(StoragePolicy.search_stop(&json!({}), &trials), Some(StopReason::FirstEligibleCandidate));
        assert_eq!(storage_objective_status(&trials)["iteration"], 2);
        let limits = limits();
        let prompt = storage_author_prompt(&PromptInput { context: &json!({"scope":"verus_workload_storage"}), feedback: &[], iteration: 1, submission: 1, limits: &limits, ledger: &json!({}), prompt_file: Path::new(PROMPT), handoff: &Value::Null });
        assert!(prompt.contains("storage_register") && prompt.contains("verus-storages.json") && prompt.contains("Complete lossless storage"));
        assert!(prompt.contains("First passing submission ends the session") && prompt.contains("diagnostic quer"));
        assert!(prompt.contains(PROMPT), "the storage author can reread this prompt too");
        assert!(prompt.contains("Storage policy: unrestricted"), "unrestricted keeps the historical choices");
        assert!(prompt.contains("the fastest of DuckDB and Umbra for each statement"), "targets without a system: both engines");
        let duckdb_only = json!({"scope":"verus_workload_storage","statements":[{"index":0,"sql":"SELECT 1","objective":{"runtime_targets":[{"workers":1,"median_ns":5,
            "system":"DuckDB","provenance":"/w/targets.json Q1 v0 1 threads: DuckDB (0.000005) ms, DuckDB 1.5.6","timing_scope":"hot median"}]}}]});
        let single = storage_author_prompt(&PromptInput { context: &duckdb_only, feedback: &[], iteration: 1, submission: 1, limits: &limits, ledger: &json!({}), prompt_file: Path::new(PROMPT), handoff: &Value::Null });
        assert!(single.contains("run **faster than DuckDB**") && !single.contains("the fastest of DuckDB and Umbra"), "one engine's targets: that engine");
        let physical = json!({"scope":"verus_workload_storage","storage_policy":{"kind":PHYSICAL_ONLY}});
        let restricted = storage_author_prompt(&PromptInput { context: &physical, feedback: &[], iteration: 1, submission: 1, limits: &limits, ledger: &json!({}), prompt_file: Path::new(PROMPT), handoff: &Value::Null });
        let restricted_query = author_prompt(&PromptInput { context: &physical, feedback: &[], iteration: 1, submission: 1, limits: &limits, ledger: &json!({}), prompt_file: Path::new(PROMPT), handoff: &Value::Null });
        for text in [&restricted, &restricted_query] {
            assert!(text.contains("Storage policy: physical_only") && text.contains("data_policy") && !text.contains("pre-aggregates"), "{text}");
            assert!(text.contains("Co-clustering") && text.contains("Cross-table row locators") && text.contains("Run offsets and row counts"), "both roles read the own-table boundary");
            assert!(text.contains("base_payload") && text.contains("Covering indexes") && text.contains("storage_payload_duplicate") && !text.contains("optionally carrying copies"), "both roles read the one-copy rule");
        }
        let query = author_prompt(&PromptInput { context: &json!({"scope":"verus_query_over_stored_data"}), feedback: &[], iteration: 1, submission: 1, limits: &limits, ledger: &json!({}), prompt_file: Path::new(PROMPT), handoff: &Value::Null });
        for section in [sections::CHECK_ECONOMY, sections::PROCESSES_APPENDIX, sections::SCOPE_RULES, sections::ATTEMPTS] {
            assert!(prompt.contains(section) && query.contains(section), "both roles carry the shared sections");
        }
        for text in [&prompt, &query] {
            assert!(!text.contains("recipe") && !text.contains("as little time") && !text.contains("persistent Claude session"), "rejected wording");
            assert!(text.contains("verus --profile") && text.contains("Do not raise rlimit") && text.contains("NOTES.md"));
        }
        for text in [&prompt, &query] {
            assert!(!["</invoke>", "<invoke", "<parameter", "</content>"].iter().any(|markup| text.contains(markup)), "no tool markup in author prompts");
        }
        // Declared integrity constraints are a current fact of both roles exactly when the context carries them.
        assert!(!prompt.contains("## Integrity constraints") && !query.contains("## Integrity constraints"));
        let declared = |scope: &str| json!({"scope":scope,"integrity_constraints":{"trust":"user_declared","declarations":[{"table":"t","sql":"PRIMARY KEY (k)"}],"details":"integrity-constraints.json"}});
        let constrained_storage = storage_author_prompt(&PromptInput { context: &declared("verus_workload_storage"), feedback: &[], iteration: 1, submission: 1, limits: &limits, ledger: &json!({}), prompt_file: Path::new(PROMPT), handoff: &Value::Null });
        let constrained_query = author_prompt(&PromptInput { context: &declared("verus_query_over_stored_data"), feedback: &[], iteration: 1, submission: 1, limits: &limits, ledger: &json!({}), prompt_file: Path::new(PROMPT), handoff: &Value::Null });
        for text in [&constrained_storage, &constrained_query] {
            assert!(text.contains("## Integrity constraints") && text.contains("- t: PRIMARY KEY (k)"), "{text}");
        }
    }

    #[test]
    fn prompt_states_the_submission_rule_and_the_latest_evaluation() {
        let context = json!({"scope":"verus_query","sql":"SELECT 1","objective":{"kind":CORRECTNESS_OBJECTIVE},"files":{"author_contract":"/w/contract/verus/index.json"}});
        let evaluated = json!(trial(1, json!({"eligible":false,"status":"proof_failure","failure_class":"proof_failure","error":"proof_failure: Verus"})));
        let feedback = [json!({"iteration":1,"attempt":0,"author_outcome":"success","provider_reported_cost_usd":"0.5","tokens":{}}), evaluated];
        let limits = limits();
        let prompt = author_prompt(&PromptInput { context: &context, feedback: &feedback, iteration: 2, submission: 2, limits: &limits, ledger: &json!({"spent_usd":"0.5"}), prompt_file: Path::new(PROMPT), handoff: &Value::Null });
        assert!(prompt.contains(crate::controller::author::CANDIDATE_MANIFEST_RULE) && prompt.contains("absolute inside that workspace"));
        assert!(prompt.contains("/w/contract/verus/index.json") && prompt.contains("first exact verified submission"));
        assert!(prompt.contains("fixed link definitions") && prompt.contains("Readability"));
        let latest = prompt.split("# LATEST FEEDBACK\n").nth(1).unwrap();
        assert!(prompt.contains("## Official results\n\n- Submission 1: proof_failure (counted); proof_failure: proof_failure: Verus.\n\nObjective: not met yet"), "{prompt}");
        assert!(latest.contains("## Latest call: the latest call, ended with submission 1") && latest.contains("## Submission 1: proof_failure"), "{latest}");
        assert!(latest.contains("- Failure: proof_failure:\n\n```text\nproof_failure: Verus\n```"), "{latest}");
        assert!(!prompt.contains("```json"), "no raw JSON block in the data sections");
        assert!(prompt.contains(&format!("`this_prompt`: {PROMPT}")), "the author can reread this prompt");
    }

    /// Under the correctness objective the prompt asks for the simplest correct implementation and states no
    /// execution-time rule or advice (selection, targets, early stop, measuring first, the trial's bar,
    /// `performance.json`), under either storage policy; the execution-time prompt keeps them. No placeholder is left.
    #[test]
    fn correctness_prompt_asks_for_the_simplest_implementation_without_execution_time_rules() {
        let limits = limits();
        let prompt = |context: &Value| author_prompt(&PromptInput { context, feedback: &[], iteration: 1, submission: 1, limits: &limits, ledger: &json!({}), prompt_file: Path::new(PROMPT), handoff: &Value::Null });
        let context = |objective: &str, storage_policy: Value| json!({"scope":"verus_query_over_stored_data","sql":"SELECT 1","objective":{"kind":objective},
            "hardware":{"threads":[1]},"observed_hardware":{"cpu_features":"sse4_2 avx2"},"storage_policy":storage_policy});
        let execution_time = ["Measure first", "lowest `score_ns` wins", "Runtime targets", "**Early stop.**", "of the target", "5x", "One `trial` times",
            "add parallelism", "where it is faster", "Fast path plus general path", "First measure your query", "performance.json", "until your submissions run out"];
        for storage_policy in [crate::storage::flat::author_view(), json!({"kind":PHYSICAL_ONLY})] {
            let correctness = prompt(&context(CORRECTNESS_OBJECTIVE, storage_policy.clone()));
            for text in execution_time {
                assert!(!correctness.contains(text), "{text}: {correctness}");
            }
            assert!(correctness.contains("Write the **simplest correct implementation**: straightforward code and proofs a reader can follow. Do no performance work"), "{correctness}");
            assert!(correctness.contains("unless the query or its proof needs them") && !correctness.contains("src/agent/common/"), "no advice to write general modules");
            assert!(correctness.contains(sections::QUERY_CORRECTNESS_GATE) && correctness.contains("- **Admission.** The first submission that passes the gate is qualified and served"));
            assert!(correctness.contains("The times are recorded but select nothing") && correctness.contains("a second consecutive unchanged resubmission ends the run"));
            assert!(correctness.contains(sections::PROOF_ADVICE) && correctness.contains(sections::CHECK_ECONOMY));
            // The correctness Reuse paragraph is the first part of the shared one, word for word.
            let reuse = correctness.split("**Reuse.**").nth(1).and_then(|rest| rest.split("\n\n").next()).unwrap_or_default();
            assert!(reuse.contains("Search the index of all admitted code") && sections::REUSE_ADVICE.starts_with(&format!("**Reuse.**{reuse}")), "{reuse}");
            assert!(correctness.contains("reports per cell: median, min and max.") && correctness.contains("`files.author_contract` `hardware.observed.cpu_features`"));
            let speed = prompt(&context(PERFORMANCE_OBJECTIVE, storage_policy.clone()));
            for text in ["Measure first, prove later", "lowest `score_ns` wins", "**Early stop.**", "reports per cell: target, 5x bar, median, min and max, met.",
                "**`performance.json`** holds the measurement protocol", "`performance.json` `observed_hardware.cpu_features`"] {
                assert!(speed.contains(text), "{text}: {speed}");
            }
            if storage_policy["kind"] == PHYSICAL_ONLY {
                assert!(correctness.contains("- **Start from the shared storage** (") && speed.contains("- **First measure your query on the shared storage** ("));
            }
            for text in [&correctness, &speed] {
                assert!(!text.contains('@'), "no placeholder is left: {text}");
            }
        }
    }

    /// Targets that name one system put that system in the goal and the Set by column without the DuckDB/Umbra
    /// wording; a continuing session's incumbent (iteration 0) has its own section, column and line, and is named when
    /// it is the selected candidate.
    #[test]
    fn system_targets_and_the_incumbent_are_named_in_the_prompt() {
        let target = |workers: u64| json!({"workers":workers,"median_ns":1_000_000,"system":"ReferenceDB","timing_scope":"engine call at GenDB's boundary + pool join",
            "provenance":"ReferenceDB engine, boundary + join, from /s/per_cell_tables.md"});
        let context = json!({"scope":"verus_query","sql":"SELECT 1","objective":{"kind":PERFORMANCE_OBJECTIVE,"early_stop":{"min_speedup":1}},
            "hardware":{"threads":[1, 32]},"runtime_targets":[target(1), target(32)],"files":{"author_contract":"/w/contract/verus/index.json"}});
        let mut incumbent = trial(0, json!({"eligible":true,"status":"verified","score_ns":1_500_000,
            "measurements":[{"workers":1,"status":"exact","median_ns":3_000_000},{"workers":32,"status":"exact","median_ns":750_000}]}));
        incumbent.call_id = 0;
        incumbent.directory = Some("/run/queries/query-0001/iterations/0000".into());
        incumbent.candidate = json!({"candidate_manifest":"verus-query.json","rationale":"r","data_access_analysis":"d",
            "incumbent":{"record":"/run/queries/query-0001/iterations/0000/incumbent.json","source_session":"/earlier/queries/query-0017",
                "provenance":{"source_iteration":1,"manifest":"/run/queries/query-0001/author/verus-query.json","source_notes":"/run/queries/query-0001/iterations/0000/NOTES.md"}}});
        let feedback = [json!(incumbent)];
        let limits = limits();
        let prompt = author_prompt(&PromptInput { context: &context, feedback: &feedback, iteration: 1, submission: 1, limits: &limits, ledger: &json!({}), prompt_file: Path::new(PROMPT), handoff: &Value::Null });
        assert!(prompt.contains("**faster than ReferenceDB in every cell**") && prompt.contains("ReferenceDB's measured times"), "{prompt}");
        assert!(!prompt.contains("DuckDB") && !prompt.contains("Umbra") && !prompt.contains("both engines"), "{prompt}");
        assert!(prompt.contains("| ReferenceDB |") && prompt.contains("Targets: ReferenceDB engine, boundary + join, from /s/per_cell_tables.md"), "{prompt}");
        assert!(prompt.contains("## Incumbent\n\nThis session continues from the package admitted by an earlier session (`/earlier/queries/query-0017`, its submission 1)"), "{prompt}");
        assert!(prompt.contains("Incumbent ms") && prompt.contains("- Incumbent: verified (not a submission); score 1.500 ms"), "{prompt}");
        assert!(prompt.contains("Early stop (the goal): not met. The incumbent (selected: lowest score, 1.500 ms) is at or below the 1x bar in 1 of 2 cells"), "{prompt}");
        let latest = prompt.split("# LATEST FEEDBACK\n").nth(1).unwrap();
        assert!(latest.contains("No earlier call in this session. The incumbent's evaluation") && latest.contains("## Incumbent: verified"), "{latest}");
        assert!(latest.contains("Exact and verified: yes; not a submission; score 1.500 ms") && !latest.contains("Submission 0"), "{latest}");
    }

    #[test]
    fn feedback_shows_each_run_once_and_storage_assets_from_the_v4_record() {
        let io = json!({"meaning":"device reads","read_bytes":0,"read_bytes_per_call":[4096,0,0,0]});
        let requests = json!([{"name":"lineitem_q6_cube","use_index":0,"requests":6,"elements":6946356,"bytes":61127925,"stored_bytes":61127925}]);
        let usage = |wall: u64| json!({"wall_ns":wall,"caller_cpu_ns":wall - 1000,"process_user_ns":wall - 2000,"process_system_ns":0});
        let cell = json!({"binding":"statement","arguments":[],"workers":32,"status":"exact","comparison":"multiset equal (no ORDER BY)","reference_rows":1,"calls":4,
            "warm_wall_ns":1064621,"hot_wall_ns":[535546,504617,480842],"median_hot_wall_ns":504617,"calling_thread_share_permille":996,"parallel_dispatch_observed":false,
            "dispatch":{"spawned":0,"joined":0,"ranges":[],"ranges_reported":0},"usage":[usage(1064621),usage(535546),usage(504617),usage(480842)],
            "process_io":io,"storage_requests":requests});
        let evaluation = json!({"eligible":true,"status":"verified_exact","score_ns":504617,"requested_bytes_meaning":"extent requests, not device reads",
            "measurements":[{"workers":32,"status":"exact","binding":"statement","median_ns":504617,"samples_ns":[535546,504617,480842],"warm_ns":1064621,
                "calling_thread_share_permille":996,"storage_requests":requests,"process_io":io,"boundary":"one hot library call"}],
            "real_data":{"cells":[cell]},
            "storage":[{"name":"lineitem_q6_cube","package":"p1","admitted":false,"asset":"a1","storage_bytes":61127925,"build_wall_ns":43458461606_u64,"asset_built_now":false}]});
        let feedback = [json!(trial(1, evaluation))];
        let latest = latest_delta(&feedback, &evaluated_trials(&feedback));
        let shown = &latest["evaluation"];
        for gone in ["measurements", "real_data", "asset_bytes", "asset_build_wall_ns", "storages"] {
            assert!(shown.get(gone).is_none(), "{gone} is not repeated in the feedback: {shown}");
        }
        let run = &shown["runs"]["cells"][0];
        assert_eq!((run["status"].as_str(), run["median_hot_ns"].as_u64(), run["workers"].as_u64()), (Some("exact"), Some(504617), Some(32)));
        assert_eq!((run["per_call"]["wall_ns"][0].as_u64(), run["per_call"]["device_read_bytes"][0].as_u64()), (Some(1064621), Some(4096)));
        assert_eq!(run["storage_requests"], requests);
        assert_eq!((shown["runs"]["meaning"]["wall_ns"].as_str(), shown["runs"]["meaning"]["device_read_bytes"].as_str()), (Some("one hot library call"), Some("device reads")));
        let asset = &shown["storage"]["assets"][0];
        assert_eq!((asset["name"].as_str(), asset["asset"].as_str(), asset["storage_bytes"].as_u64()), (Some("lineitem_q6_cube"), Some("a1"), Some(61127925)));
        assert_eq!((asset["build_wall_ns"].as_u64(), asset["asset_reused"].as_bool()), (Some(43458461606), Some(true)));
    }

    /// Render both prompts over representative contexts (a template query with targets and early stop; the workload
    /// author; a fresh second attempt with its handoff; the flat query under both objectives) into
    /// `$GENDB_RENDER_PROMPTS/*.md` for review. Writes files only.
    #[test]
    #[ignore = "renders the prompts for review: GENDB_RENDER_PROMPTS=<dir>; -- --ignored"]
    fn render_prompts_for_review() {
        let dir = std::path::PathBuf::from(std::env::var("GENDB_RENDER_PROMPTS").expect("GENDB_RENDER_PROMPTS"));
        std::fs::create_dir_all(&dir).unwrap();
        let ws = "/run/queries/query-0004/author";
        let target = |binding: &str, workers: u64, ns: u64| json!({"binding":binding,"workers":workers,"median_ns":ns,
            "provenance":"results/tpch-sf100/duckdb-umbra-baselines/targets.json Q05 v0: the faster of DuckDB and Umbra","timing_scope":"median of 3 hot runs after 1 warm run"});
        let mut targets = vec![];
        for b in ["v0", "v1", "v2"] { for (w, ns) in [(1, 9_000_000_000u64), (32, 420_000_000), (64, 380_000_000)] { targets.push(target(b, w, ns)); } }
        let files = json!({"workspace":ws,"author_contract":format!("{ws}/contract/verus/index.json"),"crate":format!("{ws}/verus"),"agent_module_root":format!("{ws}/verus/src/agent/mod.rs"),
            "notes":format!("{ws}/NOTES.md"),"search_index":format!("{ws}/search-index.json"),"storages":format!("{ws}/contract/verus/storages.json"),
            "performance":format!("{ws}/contract/verus/performance.json"),"toolchain":format!("{ws}/contract/verus/toolchain.json"),"manifest_example":format!("{ws}/verus-query-example.json"),
            "new_storages":format!("{ws}/new-storages"),"library":format!("{ws}/verus-library.json"),"full_context":"/run/queries/query-0004/context.json"});
        let query_context = json!({"scope":"verus_query_over_stored_data","sql":"SELECT n_name, SUM(l_extendedprice * (1 - l_discount)) AS revenue FROM ... WHERE r_name = $1 AND o_orderdate >= $2 ...",
            "parameters":[{"index":1,"type":"text","binding":{"free":{}}},{"index":2,"type":"date","binding":{"free":{}}}],"statement_key":"<key>",
            "objective":{"kind":PERFORMANCE_OBJECTIVE,"bindings":[{"name":"v0","origin":"benchmark","arguments":["ASIA","1994-01-01"]},{"name":"v1","origin":"benchmark","arguments":["EUROPE","1995-01-01"]},{"name":"v2","origin":"benchmark","arguments":["AMERICA","1993-01-01"]}],"early_stop":{"min_speedup":5}},
            "hardware":{"threads":[1, 32, 64]},"observed_hardware":{"logical_cpus":128,"crash_dumps":"coredump_filter 0"},"files":files,
            "local_tools":{"actions":["storage_check","storage_verify","storage_compile","storage_build","storage_register","check","verify","compile","trial","profile"]},
            "output":"Return CandidateSubmission whose candidate_manifest is a verus-query.json inside this workspace; files.author_contract maps every input",
            "storage_policy":{"kind":PHYSICAL_ONLY},"runtime_targets":targets,
            "storage_budget":{"budget_bytes":100_000_000_000u64,"used_bytes":61_000_000_000u64,"left_bytes":39_000_000_000u64,"used_by":[{"name":"lineitem_by_order","storage_bytes":41_000_000_000u64}]},
            "performance":{"free_bytes_at_prepare":300_000_000_000u64,"evaluation_timing":"1 warm + 3 hot ...","worker_counts":[1, 32, 64],"worker_count_meaning":"the maximum a call may use, not a requirement"},
            "integrity_constraints":{"trust":"user_declared","declarations":[{"table":"orders","sql":"PRIMARY KEY (o_orderkey)"}],"details":"integrity-constraints.json"}});
        let limits = crate::controller::Limits { max_iterations: 3, ..limits() };
        let prompt_file = Path::new("/run/queries/query-0004/calls/0001/prompt.txt");
        let first = author_prompt(&PromptInput { context: &query_context, feedback: &[], iteration: 1, submission: 1, limits: &limits, ledger: &json!({"submissions":{"used":0,"limit":3}}), prompt_file, handoff: &Value::Null });
        std::fs::write(dir.join("query-first-attempt.md"), &first).unwrap();
        let cells = |m: u64| json!([{"binding":"v0","workers":1,"status":"exact","median_ns":m},{"binding":"v0","workers":32,"status":"exact","median_ns":m / 20},{"binding":"v0","workers":64,"status":"exact","median_ns":m / 22}]);
        let evaluated = json!(trial(1, json!({"eligible":true,"status":"verified_exact","score_ns":400_000_000u64,"measurements":cells(2_400_000_000)})));
        let handoff = json!({"local_trials":[{"call":"0001","job_id":7,"job":"0007-t7","action":"trial","status":"completed","crate_version":"3fa2c19be0d1","verified":false,
            "cells":[{"binding":"v0","workers":1,"status":"exact","median_hot_ns":2_600_000_000u64}],"record":"/run/queries/query-0004/calls/0001/local-jobs/0007-t7/result.json"}],
            "submission_code":[{"iteration":1,"code":{"crate_version":"3fa2c19be0d1","frozen_crate":"/run/queries/query-0004/iterations/0001/frozen/crate","workspace":"same"}}],
            "notes":{"file":format!("{ws}/NOTES.md"),"text":"# Notes\nDesign: hash join of ... Tried: ... Untried: ... Proof difficulties: rlimit in the row link, solved by hiding eval_expr."},
            "paths":{"workspace":ws,"earlier_prompts":"/run/queries/query-0004/calls","submission_records":"/run/queries/query-0004/iterations"}});
        let second = author_prompt(&PromptInput { context: &query_context, feedback: &[evaluated], iteration: 2, submission: 2, limits: &limits, ledger: &json!({"submissions":{"used":1,"limit":3}}),
            prompt_file: Path::new("/run/queries/query-0004/calls/0002/prompt.txt"), handoff: &handoff });
        std::fs::write(dir.join("query-second-attempt.md"), &second).unwrap();
        // The same query under storage_policy fixed_flat: the author's inputs as the brief writes them (flat storages
        // only, no storage tools, no new-storages directory).
        let mut flat_context = query_context.clone();
        flat_context["storage_policy"] = crate::storage::flat::author_view();
        flat_context["local_tools"]["actions"] = json!(crate::tools::offered_actions(true).iter().map(|a| a.name()).collect::<Vec<_>>());
        flat_context["files"]["new_storages"] = Value::Null;
        flat_context["storage_budget"] = json!({"budget_bytes":null,"used_bytes":158_618_806_633u64,"left_bytes":null,
            "used_by":[{"name":"flat_lineitem","storage_bytes":115_678_477_059u64}]});
        let flat = author_prompt(&PromptInput { context: &flat_context, feedback: &[], iteration: 1, submission: 1, limits: &limits, ledger: &json!({"submissions":{"used":0,"limit":3}}), prompt_file, handoff: &Value::Null });
        std::fs::write(dir.join("query-fixed-flat-first-attempt.md"), &flat).unwrap();
        // The same flat query under the correctness objective: no targets and no performance.json.
        let mut correctness_context = flat_context.clone();
        correctness_context["objective"] = json!({"kind":CORRECTNESS_OBJECTIVE});
        correctness_context["runtime_targets"] = json!([]);
        correctness_context["files"]["performance"] = Value::Null;
        let correctness = author_prompt(&PromptInput { context: &correctness_context, feedback: &[], iteration: 1, submission: 1, limits: &limits, ledger: &json!({"submissions":{"used":0,"limit":3}}), prompt_file, handoff: &Value::Null });
        std::fs::write(dir.join("query-fixed-flat-correctness-first-attempt.md"), &correctness).unwrap();
        let mut workload_context = query_context.clone();
        workload_context["scope"] = json!("verus_workload_storage");
        workload_context["statements"] = json!([{"index":0,"sql":"SELECT ... (Q1)","parameters":[],"objective":{"kind":PERFORMANCE_OBJECTIVE,"runtime_targets":"..."}}]);
        workload_context["files"] = json!({"workspace":"/run/workload-storage/session/author","author_contract":"/run/workload-storage/session/author/contract/storage/index.json","notes":"/run/workload-storage/session/author/NOTES.md","search_index":"/run/workload-storage/session/author/search-index.json"});
        let workload = storage_author_prompt(&PromptInput { context: &workload_context, feedback: &[], iteration: 1, submission: 1, limits: &limits, ledger: &json!({}), prompt_file, handoff: &Value::Null });
        std::fs::write(dir.join("workload-first-attempt.md"), &workload).unwrap();
    }
}
