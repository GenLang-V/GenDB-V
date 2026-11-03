//! The facts of a run of several workloads (one engine, general for any schema,
//! data and query of SQLSpec, tuned for the counted workloads). One engine serves every workload of the request's
//! `engine.workloads`; each has a role: `counted` (its score is part of the combined score that decides every
//! submission), `check` (its crate is verified and every template answered by every submission, never timed; the
//! generality fixture) or `kept` (timed against the parent and shown, never deciding). Rendered from the context's
//! workloads view (the workloads fixture, `engine_general_sections::workloads_of`): the copy GenDB refreshes before each call
//! (top-level `workloads`), else the one the session was prepared with (`general.workloads`); the combined score
//! likewise (top-level `combined_score`, else `general.combined_score`). A context without the view (one workload, a
//! continued run, a stage run) renders nothing here, and the general facts are as before.
//!
//! The exact keys are the fixture `workloads-fixture.json` beside this file; `stage::fixture_shape_errors` compares a
//! record with it (in the stage tests). The workloads view, the primary workload first:
//! - `name`, `role` (`counted`, `check` or `kept`) and `primary` (true for the workload whose request is the run's
//!   top-level request: its training facts are also `engine.training`, its scale `general.scale`, and its sections are
//!   the general facts' own);
//! - `scale` (where it is timed or checked), `first_scale` (where its variants are checked), `library` (its own);
//! - `training`: its training facts at `scale` (`engine::facts::training_facts`; a check workload's templates may have
//!   no baselines and `baseline_totals` may be empty);
//! - `head`: the version whose numbers follow (the line's head);
//! - `side_origin`: where the root `v000`'s side of this workload came from: `kind` (`seed`: a seed's code, module
//!   and storages; `out_of_the_box`: the primary seed's code, which verified here; `version_0`: GenDB's version 0
//!   over the plain storage), `seed` (`run`, `version`, `workload` of a multi-workload version, or `source`, an exported
//!   engine folder; null without a seed), `out_of_the_box` (the primary seed's code frozen for this workload when the
//!   run was prepared: `status` `refused` | `not_assembled` | `not_verified` | `verified`, `step`, `first_errors`,
//!   `record`; null when not tried) and `record` (the side's record);
//! - `cells`, `score`: the head's recorded cells (`engine::score::CellResult`) and score (`engine::tree::RecordedScore`)
//!   at `scale`; null for a check workload (never timed);
//! - `totals_ms`, `targets_ms`: the head's total and the faster baseline's total in ms per worker count (keys: the
//!   worker counts as text), as the score counts them (an unfinished cell counts the call limit); null for a check
//!   workload;
//! - `budget`: `rule` (`original_data_size`, or `exempt` for a check workload),
//!   `budget_bytes` (the original data size at `scale`; null when exempt), `plain_storage_bytes`, `reads_only_plain`
//!   (the head reads only plain flat storages: allowed as is) and `original_data_record`;
//! - `serving_bytes`: the head's serving storage at `scale` (every part file of the storages it reads, counted once);
//! - `general`: what of the head is specific to this workload (reported): `own_module_lines` (lines of
//!   its own `workloads/<name>/**`; 0 when it uses the default module `workloads/default/`), `inherited_storages`
//!   (storages it reads that are not a family's and not plain flat storages, inherited from a seed), `family_storages`
//!   (the families it reads) and `plan_lines` (lines of its plans `plans/<name>/**`);
//! - `last_race`: counted and kept: `version`, `parent` and `record` (the race report) of the last accepted version's
//!   timing against its parent on this workload; null before one, and for a check workload;
//! - `last_check`: a check workload's last accepted check: `version`, `calls`, `agreed` and `record`; null otherwise.
//!
//! The combined score: `head`, `score` (`finished`, `normalized_time`: the sums of the counted workloads' F and G,
//! exact billionths as text), `cells` and `workloads` (the counted workloads summed).
//!
//! The evaluation record of a submission adds `members[]` (`name`, `role`, `status`: `not_run` (not evaluated: an
//! earlier step refused the submission, or a kept workload after a combined score not better), `refused` (this
//! workload's step refused the submission; `step` names it: `freeze`, `verus`, `storages`, `answers`, `timing` or
//! `variants`, and `reason` its first line), `checked` (a check workload verified and answered) or `timed` (verified,
//! storages checked and timed against the parent's side); `race`: the race report when timed; `check`: `calls`,
//! `agreed`, `record` when checked) and `combined` (`parent` and `candidate`, each `score` and `cells`, `better`,
//! `workloads`; null when no combined decision was reached). The primary workload's race report is also the
//! evaluation's own `race.json`.
//!
//! `version.json` adds `workloads.<name>` (`role`, `primary`, `scale`, `score`, `times` (`<scale>`: `race`,
//! `check`), `storage` (`serving_bytes`, `budget_bytes`, `plain_storage_bytes`, `decision`), `proof` (`errors`,
//! `verified`, `wall_ns`), `admission` (`library`, `package`), `general` (as above), `check` (as `last_check` without
//! `version`, or null) and `origin` (the root's `side_origin`; null for every other version)), `combined_score` (as
//! above, without `head`) and `general` (`one_engine`: true when no workload has an own module or an inherited
//! storage, the condition for naming a publication version; `own_modules`, the workloads with one; `inherited_storages`,
//! `[{workload, storages}]`; `shared_digest`, the SHA-256 of the shared sources `agent/**`, `workloads/default/**`,
//! `storages/*/**`). The fixture's `version` is v001's, `version_root` the root's.
//!
//! Sections: [`scale_sentence`] (the Scale facts' head line), [`overview`] (`## Workloads`: the combined score, one
//! line per workload and the one-engine status), [`sides`] (`## The root's sides`), [`member_sections`] (one section
//! per workload other than the primary), [`evaluation_lines`] and [`evaluation_tables`] (a submission's combined
//! decision and every workload's outcome and race). Reading only, like the rest of the facts.

use super::stage::{below_baselines, race_summary, read_json, recorded_cells, recorded_score, totals_text};
use super::*;
use crate::prompts::engine_general_sections::workloads_of;

/// The workloads fixture (module documentation).
#[cfg(test)]
pub(crate) const FIXTURE: &str = include_str!("workloads-fixture.json");

/// One workload of the workloads view, with the head's cells read.
struct Member<'a> {
    entry: &'a Value,
    cells: Vec<CellResult>,
}

impl<'a> Member<'a> {
    fn name(&self) -> String {
        plain(&self.entry["name"])
    }

    fn role(&self) -> &'a str {
        self.entry["role"].as_str().unwrap_or("-")
    }

    fn is_primary(&self) -> bool {
        self.entry["primary"] == true
    }

    fn scale(&self) -> String {
        plain(&self.entry["scale"])
    }

    fn training(&self) -> &'a Value {
        &self.entry["training"]
    }

    /// `` `tpch` (counted, primary) at sf100 ``.
    fn label(&self) -> String {
        format!("`{}` ({}{}) at {}", self.name(), self.role(), if self.is_primary() { ", primary" } else { "" }, self.scale())
    }

    /// The head's totals per worker count of its training facts, ns (`totals_ms`).
    fn totals(&self) -> Vec<Option<u64>> {
        by_workers(&self.entry["totals_ms"], self.training())
    }

    /// The faster baseline's totals per worker count, ns (`targets_ms`).
    fn targets(&self) -> Vec<Option<u64>> {
        by_workers(&self.entry["targets_ms"], self.training())
    }
}

/// The workloads of the view, in its order (the primary first).
fn members(view: &Value) -> Vec<Member<'_>> {
    view.as_array().into_iter().flatten().map(|entry| Member { entry, cells: recorded_cells(&entry["cells"]) }).collect()
}

/// The workloads of `context`'s view; empty without one.
fn members_of(context: &Value) -> Vec<Member<'_>> {
    workloads_of(context).map(members).unwrap_or_default()
}

/// The combined score of `context`: the refreshed copy (top-level `combined_score`), else the prepared one.
fn combined_of(context: &Value) -> &Value {
    [&context["combined_score"], &context["general"]["combined_score"]].into_iter().find(|c| c.is_object()).unwrap_or(&Value::Null)
}

/// A value per worker count of `training` from an object keyed by the worker count as text, in ms, as ns.
fn by_workers(values: &Value, training: &Value) -> Vec<Option<u64>> {
    training_workers(training).iter().map(|w| number(&values[w.to_string()]).map(|ms| (ms * 1e6).round() as u64)).collect()
}

/// A combined or recorded score's `score` and `cells` as text: `F 30/30, G 16.263`.
fn score_short(score: &Value) -> String {
    format!("F {}/{}, G {}", plain(&score["score"]["finished"]), plain(&score["cells"]), decimal(&score["score"]["normalized_time"], 3))
}

/// The counted workloads a combined score sums, in backticks: `` `tpch` and `sec` ``.
fn summed(score: &Value) -> String {
    let names: Vec<String> = score["workloads"].as_array().into_iter().flatten().map(|n| format!("`{}`", plain(n))).collect();
    if names.is_empty() { "the counted workloads".to_string() } else { names.join(" and ") }
}

/// A seed run named by its last two path components (`continued/run`): other records of that run are not inputs, so no path
/// is given (the input boundary of a continued run).
fn run_name(run: &Value) -> String {
    let path = PathBuf::from(plain(run));
    let parts: Vec<String> = path.components().rev().take(2).map(|c| c.as_os_str().to_string_lossy().into_owned()).collect();
    parts.into_iter().rev().collect::<Vec<_>>().join("/")
}

/// The head line of the Scale facts in a run of several workloads: the primary workload's scale and the combined score;
/// `None` for every other run.
pub fn scale_sentence(context: &Value) -> Option<String> {
    let all = members_of(context);
    let primary = all.iter().find(|m| m.is_primary()).or(all.first())?;
    let combined = combined_of(context);
    let head = if combined.is_object() {
        format!(
            "Head {} (the best version so far): combined F {}/{} finished, G {} over {} (Workloads).",
            plain(&combined["head"]),
            plain(&combined["score"]["finished"]),
            plain(&combined["cells"]),
            decimal(&combined["score"]["normalized_time"], 3),
            summed(combined)
        )
    } else {
        "No combined score recorded yet.".to_string()
    };
    Some(format!("Scale **{}** of the primary workload `{}`; every workload stays at its scale for the whole run (Workloads). {head}", primary.scale(), primary.name()))
}

/// What an evaluation also runs on the workloads other than the primary, for the Scale facts' estimate of its time (the
/// estimate's numbers are the primary's): every other crate's Verus run, every other counted or kept workload's race
/// (its cells) and every check workload's calls; `None` for every other run or without another workload.
pub fn evaluation_time_others(context: &Value) -> Option<String> {
    let others: Vec<String> = members_of(context).iter().filter(|m| !m.is_primary()).map(|m| {
        let training = m.training();
        let templates = training["templates"].as_array().map_or(0, Vec::len);
        if m.role() == "check" {
            let bindings = 1 + training["other_bindings"].as_array().map_or(0, Vec::len);
            let workers = training_workers(training);
            let ends = match (workers.iter().min(), workers.iter().max()) {
                (Some(low), Some(high)) if low != high => format!("{low} and {high} workers"),
                (Some(one), _) => worker_count(*one),
                _ => "its worker counts".to_string(),
            };
            format!("`{}`: {} at {} at {ends}, one call each", m.name(), counted(templates, "template"), counted(bindings, "binding"))
        } else {
            format!("`{}`: {} timed the same way at {}", m.name(), counted(templates * training_workers(training).len(), "cell"), m.scale())
        }
    }).collect();
    (!others.is_empty()).then(|| format!("In this run the evaluation also runs Verus on every other workload's crate and builds its storages, then {}.", others.join("; ")))
}

/// ` on `tpch`` after a heading of the primary workload's own sections in a run of several workloads; empty otherwise.
pub fn on_primary(context: &Value) -> String {
    let all = members_of(context);
    all.iter().find(|m| m.is_primary()).or(all.first()).map_or(String::new(), |m| format!(" on `{}`", m.name()))
}

/// What of a workload's head is specific to it (`general`), in a few words: its module, its inherited and family
/// storages and its plans.
fn code_text(entry: &Value) -> String {
    let general = &entry["general"];
    let names = |key: &str| -> Vec<String> { general[key].as_array().into_iter().flatten().map(|n| format!("`{}`", plain(n))).collect() };
    let module = match general["own_module_lines"].as_u64() {
        Some(0) | None => "no own module (it uses the default module `workloads/default/` where the version has one)".to_string(),
        Some(lines) => format!("its own module `workloads/{}/` ({lines} lines)", plain(&entry["name"])),
    };
    let mut parts = vec![module];
    let inherited = names("inherited_storages");
    if !inherited.is_empty() {
        parts.push(format!("inherited storages {} (to be replaced: One engine for every workload)", inherited.join(", ")));
    }
    let families = names("family_storages");
    if !families.is_empty() {
        parts.push(format!("family storages {}", families.join(", ")));
    }
    parts.push(match general["plan_lines"].as_u64() {
        Some(0) | None => "no plan".to_string(),
        Some(lines) => format!("plans of {lines} lines (`plans/{}/`)", plain(&entry["name"])),
    });
    parts.join("; ")
}

/// A workload's storage against its budget in a few words (the overview).
fn storage_brief(entry: &Value) -> String {
    let (budget, serving) = (&entry["budget"], &entry["serving_bytes"]);
    match (budget["rule"].as_str(), budget["reads_only_plain"].as_bool(), serving.as_u64(), budget["budget_bytes"].as_u64()) {
        (Some("exempt"), Some(true), _, _) => format!("{} of plain storage only (exempt from the budget)", size(serving)),
        (Some("exempt"), _, _, _) => format!("{} (exempt from the budget)", size(serving)),
        (_, Some(true), _, _) => format!("{} of plain storage only (allowed as is)", size(serving)),
        (_, Some(false), Some(s), Some(b)) if s > b => format!("{} with changed storage, above its {} budget", size(serving), size(&budget["budget_bytes"])),
        (_, Some(false), Some(_), Some(_)) => format!("{} with changed storage, within its {} budget", size(serving), size(&budget["budget_bytes"])),
        _ => size(serving),
    }
}

/// A workload's storage at its scale in one sentence (its own section).
fn storage_sentence(entry: &Value) -> String {
    let (budget, serving) = (&entry["budget"], &entry["serving_bytes"]);
    if budget["rule"] == "exempt" {
        return format!("the head serves {} ({} bytes){}; a check workload is exempt from the budget", size(serving), plain(serving),
            if budget["reads_only_plain"] == true { " of plain storage only" } else { "" });
    }
    let (limit, plain_bytes) = (&budget["budget_bytes"], &budget["plain_storage_bytes"]);
    let against = match (budget["reads_only_plain"].as_bool(), serving.as_u64(), limit.as_u64()) {
        (Some(true), _, _) => "plain storage only: allowed as is".to_string(),
        (Some(false), Some(s), Some(b)) if s > b => format!("with changed storage, above the budget by {} ({} bytes)", size(&serde_json::json!(s - b)), s - b),
        (Some(false), Some(s), Some(b)) => format!("with changed storage, room left {} ({} bytes)", size(&serde_json::json!(b - s)), b - s),
        _ => "not compared".to_string(),
    };
    format!("the head serves {} ({} bytes), {against}; the budget for a storage change is the original data size, {} ({} bytes); the plain storage {}, {} times the original",
        size(serving), plain(serving), size(limit), plain(limit), size(plain_bytes), times(plain_bytes, limit))
}

/// A check record (`last_check`, an evaluation's `check`) as text: `12 of 12 calls agreed`.
fn check_text(check: &Value) -> String {
    format!("{} of {} calls agreed", plain(&check["agreed"]), plain(&check["calls"]))
}

/// `## Workloads` (module documentation): the combined score, one line per workload with its head's score (or check),
/// totals against the faster baseline's, storage and code, and whether the engine is one engine yet.
pub fn overview(context: &Value) -> Vec<String> {
    let all = members_of(context);
    if all.is_empty() {
        return vec![];
    }
    let counts = all.iter().find(|m| m.role() != "check").or(all.first()).map(|m| per_workers(training_workers(m.training()).iter().map(u64::to_string))).unwrap_or_default();
    let mut lines = vec![
        "## Workloads".to_string(),
        String::new(),
        format!(
            "One engine serves {}: the combined score over the counted workloads (the sums of their F and G; the head's: Scale) decides every submission (Goal); a check workload must verify and answer, never timed; a kept workload is timed and shown, never deciding (One engine for every workload). Totals in ms at {counts} workers (each cell's time, or the call limit when unfinished), against the faster baseline's totals.",
            counted(all.len(), "workload")
        ),
        String::new(),
    ];
    for m in &all {
        let line = if m.role() == "check" {
            let check = &m.entry["last_check"];
            let answered = if check.is_object() { format!("{} ({})", check_text(check), plain(&check["version"])) } else { "no check recorded yet".to_string() };
            format!("- {}: head {}, {answered}; never timed, not in the score. Storage: {}. Code: {}.", m.label(), plain(&m.entry["head"]), storage_brief(m.entry), code_text(m.entry))
        } else {
            let totals = m.totals();
            format!("- {}: head {}, {}. Totals {} against {}; {}. Storage: {}. Code: {}.", m.label(), plain(&m.entry["head"]), recorded_score(&m.entry["score"]), totals_text(&totals),
                totals_text(&m.targets()), below_baselines(m.training(), &totals), storage_brief(m.entry), code_text(m.entry))
        };
        lines.push(line);
    }
    lines.push(String::new());
    lines.push(one_engine_line(&all));
    lines
}

/// Whether the head is one engine yet: no workload with its own module or an inherited storage.
fn one_engine_line(all: &[Member]) -> String {
    let own: Vec<String> = all.iter().filter(|m| m.entry["general"]["own_module_lines"].as_u64().unwrap_or(0) > 0).map(|m| format!("`{}`", m.name())).collect();
    let inherited: Vec<String> = all.iter().filter(|m| m.entry["general"]["inherited_storages"].as_array().is_some_and(|s| !s.is_empty())).map(|m| format!("`{}`", m.name())).collect();
    if own.is_empty() && inherited.is_empty() {
        "One engine: every workload is served by the shared engine and the default module, over storage families and plain flat storages only.".to_string()
    } else {
        format!(
            "One engine: not yet. Own modules: {}; inherited storages: {} (the transition, One engine for every workload).",
            if own.is_empty() { "none".to_string() } else { own.join(", ") },
            if inherited.is_empty() { "none".to_string() } else { inherited.join(", ") }
        )
    }
}

/// `## The root's sides` (module documentation): where each side of `v000` came from, in a full prompt.
pub fn sides(context: &Value) -> Vec<String> {
    let all = members_of(context);
    if all.is_empty() {
        return vec![];
    }
    let mut lines = vec![
        "## The root's sides".to_string(),
        String::new(),
        "The root `v000` has one side per workload (One engine for every workload); the first submission is judged on each workload against its side. A seed run is named by the last two parts of its path: its other records are not inputs.".to_string(),
        String::new(),
    ];
    for m in &all {
        let origin = &m.entry["side_origin"];
        let measured = if m.role() == "check" { format!("answered at {}", m.scale()) } else { format!("timed alone at {}", m.scale()) };
        let place = if m.is_primary() { "Your workspace starts from it, with its notebook.".to_string() } else { format!("Read-only in your workspace: `root-sides/{}/`.", m.name()) };
        let seed = &origin["seed"];
        let from = match origin["kind"].as_str() {
            Some("seed") if !seed["source"].is_null() => format!("the exported engine `{}`: its code, module and storages, verified whole and {measured} when this run was prepared", run_name(&seed["source"])),
            Some("seed") => format!(
                "the seed {} of the run `{}`{}: its code, module and storages, verified whole and {measured} when this run was prepared",
                plain(&seed["version"]),
                run_name(&seed["run"]),
                seed["workload"].as_str().map_or(String::new(), |w| format!(" (its workload `{w}`)"))
            ),
            Some("out_of_the_box") => format!("no seed; the primary seed's code, which verified here out of the box, then {measured}"),
            Some("version_0") => format!("no seed; GenDB's version 0 (the verified interpreter over the plain storage), {measured}"),
            _ => plain(&origin["kind"]),
        };
        lines.push(format!("- {}: {from}. {place} Record: {}.", m.label(), origin["record"].as_str().map_or("-".to_string(), |r| records_path(context, Path::new(r)))));
        let tried = &origin["out_of_the_box"];
        if tried.is_object() && origin["kind"] != "out_of_the_box" {
            let outcome = match tried["status"].as_str() {
                Some("refused") => "refused at freeze (the source rules or the manifest)".to_string(),
                Some("not_assembled") => "not assembled: rustc stopped it".to_string(),
                Some("not_verified") => "assembled, not verified: Verus stopped it".to_string(),
                Some("verified") => "verified".to_string(),
                _ => plain(&tried["status"]),
            };
            lines.push(format!(
                "  The primary seed's code frozen for `{}` out of the box: {outcome} (step `{}`). Record: {}.",
                m.name(),
                plain(&tried["step"]),
                tried["record"].as_str().map_or("-".to_string(), |r| records_path(context, Path::new(r)))
            ));
            let errors: Vec<String> = tried["first_errors"].as_array().into_iter().flatten().map(plain).collect();
            if !errors.is_empty() {
                lines.extend(fenced("text", &errors.join("\n")).into_iter().map(|l| format!("  {l}")));
            }
        }
    }
    lines
}

/// One section per workload other than the primary (module documentation), in a full prompt.
pub fn member_sections(context: &Value) -> Vec<String> {
    let mut lines: Vec<String> = vec![];
    for m in members_of(context).iter().filter(|m| !m.is_primary()) {
        if !lines.is_empty() {
            lines.push(String::new());
        }
        lines.extend(if m.role() == "check" { check_section(context, m) } else { timed_section(context, m) });
    }
    lines
}

/// The section of a counted or kept workload other than the primary: its head's score and the variants, its totals per
/// worker count, its cells per template, the last accepted version's race against its parent here, its storage and its
/// code.
fn timed_section(context: &Value, m: &Member) -> Vec<String> {
    let training = m.training();
    let limit = call_limit_ns(context);
    let head = plain(&m.entry["head"]);
    let counts = training_workers(training);
    let variants = &training["variants"];
    let (heading, meaning) = match m.role() {
        "kept" => ("Kept", "recorded and shown; it does not decide"),
        _ => ("Counted", "part of the combined score"),
    };
    let variants = match variants["frozen"].as_u64() {
        Some(0) | None => "No variants.".to_string(),
        Some(frozen) => format!("Variants: {frozen} frozen rewrites, {} with AST bytes of their own, checked at {} for every accepted version.", plain(&variants["timed"]), plain(&m.entry["first_scale"])),
    };
    let mut lines = vec![
        format!("## {heading} workload `{}` at {}", m.name(), m.scale()),
        String::new(),
        format!("Head {head}: {} ({meaning}). {variants}", recorded_score(&m.entry["score"])),
        String::new(),
    ];
    let count = training["templates"].as_array().map_or(0, Vec::len);
    for c in &counts {
        let (umbra, duckdb, target, engine) = baseline_totals_of(training, *c).unwrap_or((Value::Null, Value::Null, Value::Null, Value::Null));
        let total = total_over(training, &m.cells, *c, limit);
        let finished = m.cells.iter().filter(|cell| cell.workers as u64 == *c && cell.status.is_finished()).count();
        let ratio = total.zip(number(&target)).filter(|(_, t)| *t > 0.0).map_or("-".to_string(), |(e, t)| format!("{:.3}", e as f64 / t));
        let baselines = match engine.as_str() {
            Some("umbra") => format!("Umbra {} (the target), DuckDB {}", ms_rounded(&umbra), ms_rounded(&duckdb)),
            Some("duckdb") if umbra.is_null() => format!("DuckDB {} (the target; Umbra did not time every template)", ms_rounded(&duckdb)),
            Some("duckdb") => format!("Umbra {}, DuckDB {} (the target)", ms_rounded(&umbra), ms_rounded(&duckdb)),
            _ => format!("Umbra {}, DuckDB {}", ms_rounded(&umbra), ms_rounded(&duckdb)),
        };
        lines.push(format!("- {}: {baselines}; {head} (head) {}, {finished}/{count} finished, ratio {ratio}.", worker_count(*c), total.map_or("-".to_string(), |t| ms_rounded(&serde_json::json!(t)))));
    }
    lines.extend([
        String::new(),
        format!(
            "Per template (the tables it reads): the faster baseline's saved hot median, then the head's cell, in ms at {} workers. SQL, parameters, every visible binding and both baselines: `files.workloads.{}.templates`.",
            per_workers(counts.iter().map(u64::to_string)),
            m.name()
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
            per_workers(counts.iter().map(|c| cell_of(&m.cells, &name, *c).map_or("-".to_string(), |cell| cell_text(&cell.status))))
        ));
    }
    lines.push(String::new());
    let last = &m.entry["last_race"];
    if last.is_object() {
        let record = last["record"].as_str().map(PathBuf::from);
        let summary = record.as_deref().and_then(read_json).map_or_else(|| "its race record cannot be read".to_string(), |race| race_summary(&race, training, limit));
        lines.push(format!(
            "- The last accepted version against its parent here ({} against {}, one window at {}): {summary}. Record: {}.",
            plain(&last["version"]),
            plain(&last["parent"]),
            m.scale(),
            record.as_deref().map_or("-".to_string(), |r| records_path(context, r))
        ));
    } else {
        lines.push("- No accepted version of this run has been timed against its parent here yet: the head's numbers are its side's, timed alone when the run was prepared.".to_string());
    }
    lines.push(format!("- Storage at {} (its library `{}`): {}.", m.scale(), plain(&m.entry["library"]), storage_sentence(m.entry)));
    lines.push(format!("- Its code: {}.", code_text(m.entry)));
    lines
}

/// The section of a check workload: what every submission checks there, its head's last check, its templates, its
/// storage and its code.
fn check_section(context: &Value, m: &Member) -> Vec<String> {
    let training = m.training();
    let templates: Vec<&Value> = training["templates"].as_array().into_iter().flatten().collect();
    let bindings: Vec<String> = std::iter::once(plain(&training["timing_binding"])).chain(training["other_bindings"].as_array().into_iter().flatten().map(plain)).collect();
    let check = &m.entry["last_check"];
    let head = if check.is_object() {
        format!("Head {}: {} at {} ({}). Record: {}.", plain(&m.entry["head"]), check_text(check), m.scale(), plain(&check["version"]),
            check["record"].as_str().map_or("-".to_string(), |r| records_path(context, Path::new(r))))
    } else {
        format!("Head {}: no check recorded yet.", plain(&m.entry["head"]))
    };
    let listed: Vec<String> = templates.iter().map(|t| {
        let tables: Vec<String> = t["tables"].as_array().into_iter().flatten().map(plain).collect();
        format!("{} ({})", plain(&t["name"]), tables.join(", "))
    }).collect();
    vec![
        format!("## Check workload `{}` at {}", m.name(), m.scale()),
        String::new(),
        format!(
            "Every submission verifies this workload's crate whole and answers each of its {} at every visible binding ({}) with the saved answers, before any timing (rule 12); it is never timed and not in the score. {head}",
            counted(templates.len(), "template"),
            bindings.join(", ")
        ),
        String::new(),
        format!("- Templates (the tables each reads): {}. SQL, parameters and bindings: `files.workloads.{}.templates`.", listed.join(", "), m.name()),
        format!("- Storage at {} (its library `{}`): {}.", m.scale(), plain(&m.entry["library"]), storage_sentence(m.entry)),
        format!("- Its code: {}.", code_text(m.entry)),
    ]
}

/// The combined decision and every workload's outcome in a submission's evaluation (module documentation); empty for an
/// evaluation of every other run.
pub fn evaluation_lines(context: &Value, evaluation: &Value) -> Vec<String> {
    let all = members_of(context);
    if all.is_empty() {
        return vec![];
    }
    let limit = call_limit_ns(context);
    let mut lines = vec![];
    let combined = &evaluation["combined"];
    if combined.is_object() {
        lines.push(format!(
            "- Combined score over {} (the decision): parent {}; yours {}: {}.",
            summed(combined),
            score_short(&combined["parent"]),
            score_short(&combined["candidate"]),
            if combined["better"] == true { "better" } else { "not better" }
        ));
    }
    for outcome in evaluation["members"].as_array().into_iter().flatten() {
        let name = plain(&outcome["name"]);
        let member = all.iter().find(|m| m.name() == name);
        let label = member.map_or_else(|| format!("`{name}` ({})", plain(&outcome["role"])), Member::label);
        lines.push(match outcome["status"].as_str() {
            Some("not_run") => format!("- {label}: not evaluated{}.", outcome["reason"].as_str().map_or(String::new(), |r| format!(": {}", r.lines().next().unwrap_or_default()))),
            Some("refused") => format!("- {label}: it refused the submission at step `{}`: {}.", plain(&outcome["step"]), first_line(&outcome["reason"])),
            Some("checked") => format!("- {label}: verified and answered: {}. Record: {}.", check_text(&outcome["check"]),
                outcome["check"]["record"].as_str().map_or("-".to_string(), |r| records_path(context, Path::new(r)))),
            Some("timed") => {
                let race = outcome["race"].as_str().and_then(|r| read_json(Path::new(r)));
                let summary = match (&race, member) {
                    (Some(race), Some(m)) => race_summary(race, m.training(), limit),
                    _ => "its race record cannot be read".to_string(),
                };
                let deciding = if outcome["role"] == "kept" { " (recorded, not deciding)" } else { "" };
                let record = outcome["race"].as_str().map_or("-".to_string(), |r| records_path(context, Path::new(r)));
                format!("- {label}: timed against the parent's `{name}` side{deciding}: {summary}. Record: {record}.")
            }
            _ => format!("- {label}: {}.", plain(&outcome["status"])),
        });
    }
    lines
}

/// The per-template race of every timed workload other than the primary (whose race is the evaluation's own table), in
/// a submission's evaluation; empty for an evaluation of every other run.
pub fn evaluation_tables(context: &Value, evaluation: &Value) -> Vec<String> {
    let all = members_of(context);
    let mut lines = vec![];
    for outcome in evaluation["members"].as_array().into_iter().flatten().filter(|o| o["status"] == "timed") {
        let Some(member) = all.iter().find(|m| m.name() == plain(&outcome["name"]) && !m.is_primary()) else { continue };
        let Some(race) = outcome["race"].as_str().and_then(|r| read_json(Path::new(r))) else { continue };
        let view = serde_json::json!({"engine":{"training":member.training()}});
        let mut table = race_table(&view, &race);
        if let Some(heading) = table.first_mut() {
            let deciding = if member.role() == "kept" { " (recorded, not deciding)" } else { "" };
            *heading = format!("## Interleaved timing per template on `{}` at {}{deciding}", member.name(), member.scale());
        }
        lines.push(String::new());
        lines.extend(table);
    }
    lines
}
