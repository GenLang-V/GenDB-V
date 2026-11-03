//! The facts of a stage run: one engine serves several workloads, a goal workload
//! whose score decides every submission and kept workloads that are verified, timed against the parent and shown, never
//! deciding. Rendered from the context's stage view (the stage fixture, `engine_general_sections::stage_of`): the copy GenDB
//! refreshes before each call (`stage`), else the one the session was prepared with (`general.stage`). A context without
//! one (a run with one workload) renders nothing here.
//!
//! The exact keys are the fixture `stage-fixture.json` beside this file, which also holds the kept part of a stage
//! submission's evaluation record and `version.json` `workloads`; [`fixture_shape_errors`] compares a record with it.
//! The stage view:
//! - `goal`: the goal workload's name;
//! - `seed`: `run` and `version`, the accepted version of another general-line run this run was seeded from, and
//!   `out_of_the_box`, that version's code frozen for the goal workload when the run was prepared: `status` (`refused`
//!   at freeze, `not_assembled` by rustc, `not_verified` by Verus, or `verified`), `step` (the step that stopped it, or
//!   `timing` when it was timed), `first_errors` (the first lines of the blocking errors), `score` (a recorded score,
//!   `engine::tree::RecordedScore`, when it was timed; else null) and `record` (`OUT_OF_THE_BOX.md`);
//! - `workloads[]`, the goal first: `name`, `role` (`goal` or `kept`), `scale` (where it is timed), `first_scale`
//!   (where its variants are checked), `library` (its own library), `training` (its training facts at `scale`, as
//!   `engine::facts::training_facts` writes them), `head` (the version whose numbers follow: the head), `cells` (the
//!   head's recorded cells at `scale`, `engine::score::CellResult`; null when none), `score` (the head's recorded score
//!   there; null when none), `storage` (`budget_bytes`: the original data size at `scale`, `plain_storage_bytes`,
//!   `serving_bytes` of the head, `reads_only_plain`, `original_data_record`), `module_lines` (lines of the head's
//!   `workloads/<name>/**`; 0 without a module), `last_race` (kept: `version`, `parent` and `record`, the race report of
//!   the last accepted version against its parent on this workload; null before one, and for the goal) and
//!   `reference` (kept: the seed's timing at `scale` when the run was prepared, `version`, `score` and `cells`; null for
//!   the goal).
//!
//! The evaluation record of a stage submission adds `kept_workloads[]`: `name`, `status` (`not_run`: the goal decided
//! first; `refused`: a kept workload's step refused the submission; `timed`: verified, its storages checked and timed
//! against the parent), `reason` (the first line of a refusal, else null) and `race` (the race report when timed).
//!
//! A stage version's `version.json` adds `workloads.<name>` (read by `output::engine::general`): `role`, `scale`,
//! `score` (its recorded score; `record` names its timing record, a race report or a score record, whose cells the
//! output tables show), `times` (`<scale>.race`), `storage` (`serving_bytes`, `budget_bytes`, `plain_storage_bytes`,
//! `decision`), `proof` (`errors`, `verified`, `wall_ns` of its whole-crate Verus run), `admission` (`library`,
//! `package`) and `module_lines`.
//!
//! Sections: [`workloads`] (`## Workloads`, one line per workload), [`kept_workloads`] (one section per kept workload:
//! its totals, cells, last race, reference, storage and module), [`out_of_the_box`], and [`kept_evaluation`] (the kept
//! lines of a stage submission's evaluation). Reading only, like the rest of the facts.

use super::*;
use crate::prompts::engine_general_sections::stage_of;

/// One workload of the stage view, with the head's cells read.
struct Workload<'a> {
    entry: &'a Value,
    cells: Vec<CellResult>,
}

impl<'a> Workload<'a> {
    fn name(&self) -> String {
        plain(&self.entry["name"])
    }

    fn is_goal(&self) -> bool {
        self.entry["role"] == "goal"
    }

    fn scale(&self) -> String {
        plain(&self.entry["scale"])
    }

    fn training(&self) -> &'a Value {
        &self.entry["training"]
    }

    /// `` `tpch` (kept) at sf100 ``.
    fn label(&self) -> String {
        format!("`{}` ({}) at {}", self.name(), plain(&self.entry["role"]), self.scale())
    }
}

/// The workloads of the stage view, the goal first as recorded.
fn workloads_of(stage: &Value) -> Vec<Workload<'_>> {
    stage["workloads"].as_array().into_iter().flatten().map(|entry| Workload { entry, cells: recorded_cells(&entry["cells"]) }).collect()
}

/// Recorded cells (`engine::score::CellResult` as JSON); none when absent or unreadable.
pub(super) fn recorded_cells(value: &Value) -> Vec<CellResult> {
    serde_json::from_value(value.clone()).unwrap_or_default()
}

/// A recorded score (`engine::tree::RecordedScore` as JSON) as text: `F 12/66 finished, G 2.471`.
pub(super) fn recorded_score(score: &Value) -> String {
    if !score.is_object() {
        return "no score recorded".into();
    }
    format!("F {}/{} finished, G {}{}", plain(&score["score"]["finished"]), plain(&score["cells"]), decimal(&score["score"]["normalized_time"], 3),
        if score["beats_both"] == true { ", beats both baselines" } else { "" })
}

/// The totals of `cells` over `training`'s templates at each of its worker counts, as the score counts them.
pub(super) fn totals_of(training: &Value, cells: &[CellResult], limit_ns: u64) -> Vec<Option<u64>> {
    training_workers(training).into_iter().map(|w| total_over(training, cells, w, limit_ns)).collect()
}

/// `a / b / c` of totals in ms (`-` where a total is unknown).
pub(super) fn totals_text(totals: &[Option<u64>]) -> String {
    per_workers(totals.iter().map(|t| t.map_or("-".to_string(), |ns| ms_rounded(&serde_json::json!(ns)))))
}

/// Where `totals` lie below each baseline's saved total: `below Umbra at 1 and 64 workers; below DuckDB at 1, 32 and 64
/// workers`, or that they lie below neither.
pub(super) fn below_baselines(training: &Value, totals: &[Option<u64>]) -> String {
    let counts = training_workers(training);
    let below = |engine: &str| -> Vec<u64> {
        counts.iter().zip(totals).filter_map(|(w, total)| {
            let baseline = baseline_totals_of(training, *w).and_then(|(umbra, duckdb, _, _)| number(if engine == "umbra" { &umbra } else { &duckdb }))?;
            (total.is_some_and(|t| (t as f64) < baseline)).then_some(*w)
        }).collect()
    };
    let at = |workers: Vec<u64>| -> String {
        let names: Vec<String> = workers.iter().map(u64::to_string).collect();
        match names.as_slice() {
            [one] => format!("at {one} worker{}", if one == "1" { "" } else { "s" }),
            [rest @ .., last] => format!("at {} and {last} workers", rest.join(", ")),
            [] => String::new(),
        }
    };
    let parts: Vec<String> = [("Umbra", below("umbra")), ("DuckDB", below("duckdb"))].into_iter().filter(|(_, w)| !w.is_empty()).map(|(name, w)| format!("below {name} {}", at(w))).collect();
    if parts.is_empty() { "below neither baseline's total".into() } else { parts.join("; ") }
}

/// The storage of a workload's head at its scale in one sentence (the rule of the Storage section).
fn storage_sentence(entry: &Value) -> String {
    let storage = &entry["storage"];
    let (serving, budget, plain_bytes) = (&storage["serving_bytes"], &storage["budget_bytes"], &storage["plain_storage_bytes"]);
    let against = match (storage["reads_only_plain"].as_bool(), serving.as_u64(), budget.as_u64()) {
        (Some(true), _, _) => "plain storage only: allowed as is".to_string(),
        (Some(false), Some(s), Some(b)) if s > b => format!("with changed storage, above the budget by {} ({} bytes)", size(&serde_json::json!(s - b)), s - b),
        (Some(false), Some(s), Some(b)) => format!("with changed storage, room left {} ({} bytes)", size(&serde_json::json!(b - s)), b - s),
        _ => "not compared".to_string(),
    };
    format!(
        "serves {} ({} bytes), {against}; the budget for a storage change is the original data size, {} ({} bytes); the plain storage {}, {} times the original",
        size(serving),
        plain(serving),
        size(budget),
        plain(budget),
        size(plain_bytes),
        times(plain_bytes, budget)
    )
}

/// The storage of a workload's head in a few words, against its budget (the overview; [`storage_sentence`] in full).
fn storage_brief(entry: &Value) -> String {
    let storage = &entry["storage"];
    let (serving, budget) = (&storage["serving_bytes"], &storage["budget_bytes"]);
    match (storage["reads_only_plain"].as_bool(), serving.as_u64(), budget.as_u64()) {
        (Some(true), _, _) => format!("{} of plain storage only (allowed as is)", size(serving)),
        (Some(false), Some(s), Some(b)) if s > b => format!("{} with changed storage, above its {} budget", size(serving), size(budget)),
        (Some(false), Some(_), Some(_)) => format!("{} with changed storage, within its {} budget", size(serving), size(budget)),
        _ => size(serving),
    }
}

/// `workloads/<name>/`: its lines, or that the head has none.
fn module_text(entry: &Value) -> String {
    match entry["module_lines"].as_u64() {
        Some(0) | None => format!("workload module `workloads/{}/`: none yet", plain(&entry["name"])),
        Some(lines) => format!("workload module `workloads/{}/`: {lines} lines", plain(&entry["name"])),
    }
}

/// `## Workloads` (module documentation): one line per workload with its head's score, totals against the faster
/// baseline's, where they lie below each baseline, its storage and its module.
pub fn workloads(context: &Value) -> Vec<String> {
    let Some(stage) = stage_of(context) else { return vec![] };
    let limit = call_limit_ns(context);
    let all = workloads_of(stage);
    let counts = all.first().map(|w| per_workers(training_workers(w.training()).iter().map(u64::to_string))).unwrap_or_default();
    let mut lines = vec![
        "## Workloads".to_string(),
        String::new(),
        format!(
            "One engine serves {}: the goal's score decides every submission (Goal); every kept workload is verified, timed against the parent and shown, never deciding (Stage 2). Totals in ms at {counts} workers (each cell's time, or the call limit when unfinished), against the faster baseline's totals.",
            counted(all.len(), "workload")
        ),
        String::new(),
    ];
    for w in &all {
        let totals = totals_of(w.training(), &w.cells, limit);
        let targets: Vec<Option<u64>> = training_workers(w.training()).into_iter().map(|c| baseline_totals_of(w.training(), c).and_then(|(_, _, target, _)| target.as_u64())).collect();
        lines.push(format!(
            "- {}: head {}, {}. Totals {} against {}; {}. Storage: {}. The {}.",
            w.label(),
            plain(&w.entry["head"]),
            recorded_score(&w.entry["score"]),
            totals_text(&totals),
            totals_text(&targets),
            below_baselines(w.training(), &totals),
            storage_brief(w.entry),
            module_text(w.entry)
        ));
    }
    lines
}

/// One section per kept workload (module documentation).
pub fn kept_workloads(context: &Value) -> Vec<String> {
    let Some(stage) = stage_of(context) else { return vec![] };
    let mut lines: Vec<String> = vec![];
    for w in workloads_of(stage).iter().filter(|w| !w.is_goal()) {
        if !lines.is_empty() {
            lines.push(String::new());
        }
        lines.extend(kept_workload(context, stage, w));
    }
    lines
}

/// The section of one kept workload: its head's score and the variants, its totals per worker count, its cells per
/// template, the last accepted version's race against its parent here, the seed's timing as reference, its storage and
/// its module.
fn kept_workload(context: &Value, stage: &Value, w: &Workload) -> Vec<String> {
    let training = w.training();
    let limit = call_limit_ns(context);
    let head = plain(&w.entry["head"]);
    let counts = training_workers(training);
    let counts_text = per_workers(counts.iter().map(u64::to_string));
    let variants = &training["variants"];
    let mut lines = vec![
        format!("## Kept workload `{}` at {}", w.name(), w.scale()),
        String::new(),
        format!(
            "Head {head}: {} (recorded and shown; it does not decide). Variants: {} frozen rewrites, {} with AST bytes of their own, checked at {} for every accepted version.",
            recorded_score(&w.entry["score"]),
            plain(&variants["frozen"]),
            plain(&variants["timed"]),
            plain(&w.entry["first_scale"])
        ),
        String::new(),
    ];
    let count = training["templates"].as_array().map_or(0, Vec::len);
    for c in &counts {
        let (umbra, duckdb, target, engine) = baseline_totals_of(training, *c).unwrap_or((Value::Null, Value::Null, Value::Null, Value::Null));
        let total = total_over(training, &w.cells, *c, limit);
        let finished = w.cells.iter().filter(|cell| cell.workers as u64 == *c && cell.status.is_finished()).count();
        let ratio = total.zip(number(&target)).filter(|(_, t)| *t > 0.0).map_or("-".to_string(), |(e, t)| format!("{:.3}", e as f64 / t));
        let baselines = match engine.as_str() {
            Some("umbra") => format!("Umbra {} (the target), DuckDB {}", ms_rounded(&umbra), ms_rounded(&duckdb)),
            Some("duckdb") => format!("Umbra {}, DuckDB {} (the target)", ms_rounded(&umbra), ms_rounded(&duckdb)),
            _ => format!("Umbra {}, DuckDB {}", ms_rounded(&umbra), ms_rounded(&duckdb)),
        };
        lines.push(format!("- {}: {baselines}; {head} (head) {}, {finished}/{count} finished, ratio {ratio}.", worker_count(*c), total.map_or("-".to_string(), |t| ms_rounded(&serde_json::json!(t)))));
    }
    lines.extend([
        String::new(),
        format!(
            "Per template (the tables it reads): the faster baseline's saved hot median, then the head's cell, in ms at {counts_text} workers. SQL, parameters, every visible binding and both baselines: `files.workloads.{}.templates`.",
            w.name()
        ),
        String::new(),
    ]);
    let binding = plain(&training["timing_binding"]);
    for t in training["templates"].as_array().into_iter().flatten() {
        let name = plain(&t["name"]);
        let tables: Vec<String> = t["tables"].as_array().into_iter().flatten().map(plain).collect();
        lines.push(format!(
            "- {name} ({}): {}; {head} {}",
            tables.join(", "),
            per_workers(counts.iter().map(|c| faster_baseline(t, &binding, *c).map_or("-".to_string(), |b| ms_rounded(&serde_json::json!(b))))),
            per_workers(counts.iter().map(|c| cell_of(&w.cells, &name, *c).map_or("-".to_string(), |cell| cell_text(&cell.status))))
        ));
    }
    lines.push(String::new());
    let last = &w.entry["last_race"];
    if last.is_object() {
        let record = last["record"].as_str().map(PathBuf::from);
        let summary = record.as_deref().and_then(read_json).map_or_else(|| "its race record cannot be read".to_string(), |race| race_summary(&race, training, limit));
        lines.push(format!(
            "- The last accepted version against its parent here ({} against {}, one window at {}): {summary}. Record: {}.",
            plain(&last["version"]),
            plain(&last["parent"]),
            w.scale(),
            record.as_deref().map_or("-".to_string(), |r| records_path(context, r))
        ));
    } else {
        lines.push("- No accepted version of this run has been timed against its parent here yet.".to_string());
    }
    let reference = &w.entry["reference"];
    if reference.is_object() {
        let totals = totals_of(training, &recorded_cells(&reference["cells"]), limit);
        let seed = &stage["seed"];
        lines.push(format!(
            "- Reference: the seed {} ({}), timed alone at {} when this run was prepared, as {}: {}; totals {} ms.",
            plain(&seed["version"]),
            records_path(context, Path::new(&plain(&seed["run"]))),
            w.scale(),
            plain(&reference["version"]),
            recorded_score(&reference["score"]),
            totals_text(&totals)
        ));
    }
    lines.push(format!("- Storage at {} (its library `{}`): the head {}.", w.scale(), plain(&w.entry["library"]), storage_sentence(w.entry)));
    lines.push(format!("- Its {}.", module_text(w.entry)));
    lines
}

/// A JSON record read from `path`; `None` when it cannot be read.
pub(super) fn read_json(path: &Path) -> Option<Value> {
    std::fs::read_to_string(path).ok().and_then(|text| serde_json::from_str(&text).ok())
}

/// One race report (`engine::race`, `race.json`) in one sentence: each side's totals per worker count over `training`'s
/// templates with their ratios, the cells faster and slower, and the window's length.
pub(super) fn race_summary(race: &Value, training: &Value, limit_ns: u64) -> String {
    let side = |which: &str| recorded_cells(&race[which]["cells"]);
    let (parent, candidate) = (totals_of(training, &side("parent_score"), limit_ns), totals_of(training, &side("candidate_score"), limit_ns));
    let pairs: Vec<String> = parent.iter().zip(&candidate).map(|(p, c)| format!("{} → {}", p.map_or("-".to_string(), |ns| ms_rounded(&serde_json::json!(ns))), c.map_or("-".to_string(), |ns| ms_rounded(&serde_json::json!(ns))))).collect();
    let ratios: Vec<String> = parent.iter().zip(&candidate).map(|(p, c)| match (p, c) {
        (Some(p), Some(c)) if *p > 0 => format!("{:.2}", *c as f64 / *p as f64),
        _ => "-".to_string(),
    }).collect();
    let cell_ratios: Vec<f64> = race["pairs"].as_array().into_iter().flatten().filter_map(|p| number(&p["candidate_over_parent"])).collect();
    let (faster, slower) = (cell_ratios.iter().filter(|r| **r < 1.0).count(), cell_ratios.iter().filter(|r| **r > 1.0).count());
    let window = match (race["window_start_unix_ms"].as_u64(), race["window_end_unix_ms"].as_u64()) {
        (Some(start), Some(end)) if end >= start => format!("; the timing took {}", minutes(end - start)),
        _ => String::new(),
    };
    format!(
        "parent {} vs yours {}; totals {} ms (yours / parent {}); {} faster, {} slower{window}",
        recorded_side(&race["parent_score"]),
        recorded_side(&race["candidate_score"]),
        pairs.join(" / "),
        ratios.join(" / "),
        counted(faster, "cell"),
        counted(slower, "cell")
    )
}

/// One side's score in a race report: `F 66/66, G 2.471`.
fn recorded_side(score: &Value) -> String {
    format!("F {}/{}, G {}", plain(&score["score"]["finished"]), plain(&score["cells_total"]), decimal(&score["score"]["normalized_time"], 3))
}

/// `## Out of the box: the seed on <goal>` (module documentation): the seed's code frozen for the goal workload when the
/// run was prepared, how far it got, its first errors and the record.
pub fn out_of_the_box(context: &Value) -> Vec<String> {
    let Some(stage) = stage_of(context) else { return vec![] };
    let (seed, goal) = (&stage["seed"], plain(&stage["goal"]));
    let record = &seed["out_of_the_box"];
    let outcome = match record["status"].as_str() {
        Some("refused") => "refused at freeze (the source rules or the manifest)".to_string(),
        Some("not_assembled") => "not assembled: rustc stopped it".to_string(),
        Some("not_verified") => "assembled, not verified: Verus stopped it".to_string(),
        Some("verified") => format!("verified, then timed alone: {}", recorded_score(&record["score"])),
        _ => plain(&record["status"]),
    };
    let mut lines = vec![
        format!("## Out of the box: the seed on `{goal}`"),
        String::new(),
        format!(
            "When this run was prepared, GenDB froze the seed {} ({}) for `{goal}` over its plain storage under this run's rules: {outcome} (step `{}`).",
            plain(&seed["version"]),
            records_path(context, Path::new(&plain(&seed["run"]))),
            plain(&record["step"])
        ),
    ];
    let errors: Vec<String> = record["first_errors"].as_array().into_iter().flatten().map(plain).collect();
    if !errors.is_empty() {
        lines.extend([String::new(), "First errors:".to_string(), String::new()]);
        lines.extend(fenced("text", &errors.join("\n")));
    }
    lines.push(String::new());
    lines.push(format!("Record: {}.", record["record"].as_str().map_or("-".to_string(), |r| records_path(context, Path::new(r)))));
    lines
}

/// The kept lines of a stage submission's evaluation (module documentation): per kept workload, whether it was
/// evaluated and how, then the per-template race of every kept workload that was timed.
pub fn kept_evaluation(context: &Value, evaluation: &Value) -> Vec<String> {
    let Some(stage) = stage_of(context) else { return vec![] };
    let limit = call_limit_ns(context);
    let all = workloads_of(stage);
    let mut lines = vec![];
    let mut tables = vec![];
    for kept in evaluation["kept_workloads"].as_array().into_iter().flatten() {
        let name = plain(&kept["name"]);
        let workload = all.iter().find(|w| w.name() == name);
        let scale = workload.map_or("-".to_string(), Workload::scale);
        lines.push(match kept["status"].as_str() {
            Some("not_run") => format!("- Kept workload `{name}`: not verified or timed: a submission not better on the goal workload is not evaluated further."),
            Some("refused") => format!("- Kept workload `{name}`: it refused the submission: {}.", first_line(&kept["reason"])),
            Some("timed") => {
                let race = kept["race"].as_str().and_then(|r| read_json(Path::new(r)));
                let summary = match (&race, workload) {
                    (Some(race), Some(w)) => race_summary(race, w.training(), limit),
                    _ => "its race record cannot be read".to_string(),
                };
                if let (Some(race), Some(w)) = (&race, workload) {
                    let view = serde_json::json!({"engine":{"training":w.training()}});
                    let mut table = race_table(&view, race);
                    if let Some(heading) = table.first_mut() {
                        *heading = format!("## Interleaved timing per template on `{name}` at {scale} (recorded, not deciding)");
                    }
                    tables.push(table);
                }
                let record = kept["race"].as_str().map_or("-".to_string(), |r| records_path(context, Path::new(r)));
                format!("- Kept workload `{name}`: verified, its storages checked, and timed against the parent's `{name}` side at {scale} (recorded, not deciding): {summary}. Record: {record}.")
            }
            _ => format!("- Kept workload `{name}`: {}.", plain(&kept["status"])),
        });
    }
    for table in tables {
        lines.push(String::new());
        lines.extend(table);
    }
    lines
}

/// The stage fixture (module documentation).
#[cfg(test)]
pub(crate) const FIXTURE: &str = include_str!("stage-fixture.json");

/// Where `record` differs in shape from `fixture`: a key one has and the other lacks, or a value of another JSON type,
/// as paths (`workloads[0].storage.serving_bytes`). Null on either side matches anything; arrays compare their first
/// elements; `training`, `cells` and `score` are the serde forms of existing records and are not compared. For the stage tests'
/// test of its stage context, evaluation record and `version.json` against [`FIXTURE`].
#[cfg(test)]
pub(crate) fn fixture_shape_errors(record: &Value, fixture: &Value) -> Vec<String> {
    fn walk(record: &Value, fixture: &Value, path: &str, errors: &mut Vec<String>) {
        match (record, fixture) {
            (Value::Null, _) | (_, Value::Null) => {}
            (Value::Object(r), Value::Object(f)) => {
                for key in r.keys().filter(|k| !f.contains_key(*k)) {
                    errors.push(format!("{path}.{key}: not in the fixture"));
                }
                for (key, value) in f {
                    match r.get(key) {
                        None => errors.push(format!("{path}.{key}: missing")),
                        Some(_) if ["training", "cells", "score"].contains(&key.as_str()) => {}
                        Some(found) => walk(found, value, &format!("{path}.{key}"), errors),
                    }
                }
            }
            (Value::Array(r), Value::Array(f)) => {
                if let (Some(r), Some(f)) = (r.first(), f.first()) {
                    walk(r, f, &format!("{path}[0]"), errors);
                }
            }
            (r, f) if std::mem::discriminant(r) == std::mem::discriminant(f) => {}
            (r, f) => errors.push(format!("{path}: {} where the fixture has {}", kind(r), kind(f))),
        }
    }
    fn kind(value: &Value) -> &'static str {
        match value {
            Value::Null => "null",
            Value::Bool(_) => "a boolean",
            Value::Number(_) => "a number",
            Value::String(_) => "a string",
            Value::Array(_) => "an array",
            Value::Object(_) => "an object",
        }
    }
    let mut errors = vec![];
    walk(record, fixture, "", &mut errors);
    errors
}
