//! The readable engine folders of a general-line run's output home (written by
//! GenDB after `gendb engine prepare` and after every session of `engine::branches`):
//!
//! ```text
//! engine/README.md            the run at a glance: line, ladder, main-line head, branches with their directions,
//!                             every version's score per scale, attempts, spend
//! engine/TREE.md, tree.json   the version tree (copies of the run's views)
//! engine/FINDINGS.md          the findings log (copy)
//! engine/PROFILE.md           the main-line head's profile (copy), when it has one (version 0's, or an earlier
//!                             build's; the development evaluation profiles nothing, the final evaluation profiles
//!                             under the run's engine/final/)
//! engine/scales/<scale>.md    per scale: the totals per worker count of every version timed there against both
//!                             baselines, and every version's cell per template
//! engine/versions/vNNN/       one version, complete (code, code-view, NOTES.md, version.json, node.json, race.json,
//!                             cells, variant answers, PROFILE.md and profile/ when profiled, admission, receipts)
//! engine/attempts/<id>/       one attempt (code and its reading view when it was frozen, notes, attempt.json,
//!                             race.json when it was timed, receipts)
//! ```
//!
//! The run directory's `engine/` is the source; each copy is replaced whole on every write. Baselines per scale come
//! from the timing records (each score record holds the faster baseline per cell and both baselines' totals), so the
//! output needs nothing outside the run. Reading only: nothing here proves, builds or measures.
//!
//! A stage run (one engine for several workloads; its versions' `version.json` carry `workloads`, the
//! keys of the fixture `prompts/engine_facts/general/stage-fixture.json`) adds to the README a table of every
//! version's score on every workload, and per kept workload its tables at its scale (`engine/workloads/<name>/<scale>.md`,
//! from each version's recorded timing of it). [`workloads_readme`] is the per-workload section of a version's own
//! README. A run without a stage writes its output as before.
//!
//! A run of several workloads (`engine.workloads`; its versions' `version.json` carry `workloads`,
//! `combined_score` and `general`, the keys of the fixture `prompts/engine_facts/general/workloads-fixture.json`) adds
//! to the README a table of every version's combined score, its score (or check) on every workload and whether it is
//! one engine, and per counted or kept workload other than the primary its tables at its scale
//! (`engine/workloads/<name>/<scale>.md`); [`workloads_readme`] then writes that run's per-workload section.

use super::{OutputError, copy_tree, io_error, write_text};
use crate::engine::branches::LadderState;
use crate::engine::profile::PROFILE_FILE;
use crate::engine::score::{CellResult, CellStatus};
use crate::engine::sessions::RunSpend;
use crate::engine::tree::{self, VersionTree, node_directory};
use crate::controller::limits::Money;
use crate::controller::records;
use crate::controller::request::WorkloadRequest;
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

/// The baselines and the call limit of one scale, as the per-scale tables need them.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct ScaleColumns {
    pub binding: String,
    pub workers: Vec<u64>,
    /// Templates in training order.
    pub templates: Vec<String>,
    /// The faster baseline's median per `(template, workers)`, ns.
    pub faster_ns: BTreeMap<(String, u64), u64>,
    /// Both baselines' totals per worker count: `(umbra, duckdb)`, ns (Umbra `None` when it did not time every template:
    /// a statement measured on DuckDB only, `engine::totals::BaselineCell`).
    pub totals_ns: BTreeMap<u64, (Option<u64>, u64)>,
    pub call_limit_ns: u64,
}

impl ScaleColumns {
    /// From the training facts of a prepared scale (`engine::facts::training_facts`) and the call limit.
    pub fn from_training(training: &Value, call_limit_ns: u64) -> Self {
        let binding = training["timing_binding"].as_str().unwrap_or("-").to_string();
        let workers: Vec<u64> = training["workers"].as_array().into_iter().flatten().filter_map(Value::as_u64).collect();
        let mut columns = ScaleColumns { binding: binding.clone(), workers: workers.clone(), call_limit_ns, ..Default::default() };
        for t in training["templates"].as_array().into_iter().flatten() {
            let name = t["name"].as_str().unwrap_or("-").to_string();
            for cell in t["baselines"].as_array().into_iter().flatten().filter(|c| c["binding"] == binding.as_str()) {
                if let (Some(w), Some(d)) = (cell["workers"].as_u64(), cell["duckdb_ns"].as_u64()) {
                    columns.faster_ns.insert((name.clone(), w), cell["umbra_ns"].as_u64().map_or(d, |u| u.min(d)));
                }
            }
            columns.templates.push(name);
        }
        for total in training["baseline_totals"].as_array().into_iter().flatten().filter(|t| t["binding"] == binding.as_str()) {
            if let (Some(w), Some(d)) = (total["workers"].as_u64(), total["duckdb_ns"].as_u64()) {
                columns.totals_ns.insert(w, (total["umbra_ns"].as_u64(), d));
            }
        }
        columns
    }

    /// From one score record (`engine::score::ScaleScore`, alone as `score.json` or as a side of a race report): its
    /// cells' faster baselines and its worker totals. `None` when the record has no cells.
    pub fn from_score_record(record: &Value, version: &str) -> Option<Self> {
        let score = score_side(record, version);
        let cells = score["cells"].as_array().filter(|c| !c.is_empty())?;
        let mut columns = ScaleColumns { binding: score["binding"].as_str().unwrap_or("-").to_string(), call_limit_ns: score["call_limit_ns"].as_u64().unwrap_or(0), ..Default::default() };
        for cell in cells {
            let (Some(template), Some(w)) = (cell["template"].as_str(), cell["workers"].as_u64()) else { continue };
            if !columns.templates.iter().any(|t| t == template) {
                columns.templates.push(template.to_string());
            }
            if !columns.workers.contains(&w) {
                columns.workers.push(w);
            }
            if let Some(faster) = cell["faster_baseline_ns"].as_u64() {
                columns.faster_ns.insert((template.to_string(), w), faster);
            }
        }
        for total in score["workers"].as_array().into_iter().flatten() {
            if let (Some(w), Some(d)) = (total["workers"].as_u64(), total["duckdb_ns"].as_u64()) {
                columns.totals_ns.insert(w, (total["umbra_ns"].as_u64(), d));
            }
        }
        columns.workers.sort_unstable();
        Some(columns)
    }
}

/// The score of `version` in a score record: a race report's side that is `version` (its parent's, else its
/// candidate's), or the record itself.
fn score_side<'a>(record: &'a Value, version: &str) -> &'a Value {
    match (record.get("candidate_score"), record.get("parent_score")) {
        (Some(candidate), Some(parent)) => if record["parent"] == version { parent } else { candidate },
        _ => record,
    }
}

fn ms(ns: u64) -> String {
    format!("{:.3}", ns as f64 / 1e6)
}

/// One cell as the tables show it: its median in ms, or why it did not finish.
fn cell_text(status: &CellStatus) -> String {
    match status {
        CellStatus::Finished { median_ns } => ms(*median_ns),
        CellStatus::Unchecked { median_ns } => format!("{} unchecked", ms(*median_ns)),
        CellStatus::Unfinished { reason } => match reason {
            gendb_runtime::worker::UnfinishedReason::OverTimeLimit => "time limit".into(),
            gendb_runtime::worker::UnfinishedReason::OverMemoryLimit => "memory limit".into(),
            gendb_runtime::worker::UnfinishedReason::ChildFailure => "child failed".into(),
        },
    }
}

/// A version's recorded cells at `scale` (`versions/<id>/cells/<scale>.json`).
pub fn version_cells(engine_dir: &Path, version: &str, scale: &str) -> Option<Vec<CellResult>> {
    let text = fs::read_to_string(node_directory(engine_dir, version, true).join("cells").join(format!("{scale}.json"))).ok()?;
    serde_json::from_str(&text).ok()
}

/// The scales any version has a score at, in the ladder's order when known (`scale.json` moves), else by name.
fn scales_of(tree: &VersionTree, ladder: Option<&LadderState>) -> Vec<String> {
    let mut found: BTreeSet<String> = tree.versions().filter_map(|n| n.score.as_ref().map(|s| s.scale.clone())).collect();
    found.extend(tree.scale_scores.keys().map(|(_, s)| s.clone()));
    let mut ordered: Vec<String> = vec![];
    if let Some(first) = tree.version(tree::ROOT_VERSION).map(|n| n.scale.clone()) {
        ordered.push(first);
    }
    for moved in ladder.iter().flat_map(|l| l.moves.iter()).filter_map(|m| m["to"].as_str()) {
        if !ordered.iter().any(|s| s == moved) {
            ordered.push(moved.to_string());
        }
    }
    ordered.retain(|s| found.contains(s));
    ordered.extend(found.into_iter().filter(|s| !ordered.contains(s)).collect::<Vec<_>>());
    ordered
}

/// The baselines of `scale` from the first score record at that scale that has cells.
fn columns_of(tree: &VersionTree, scale: &str) -> Option<ScaleColumns> {
    let records = tree.versions().filter_map(|n| {
        let score = tree.score_at(&n.id, scale)?;
        let text = fs::read_to_string(&score.record).ok()?;
        Some((n.id.clone(), serde_json::from_str::<Value>(&text).ok()?))
    });
    records.into_iter().find_map(|(id, record)| ScaleColumns::from_score_record(&record, &id))
}

/// One version's row in the per-scale tables: the version, its score there as text, and its cells.
struct ScaleRow<'a> {
    node: &'a tree::TreeNode,
    score: String,
    cells: Vec<CellResult>,
}

/// The per-scale tables (module documentation): totals per worker count of every version with cells at `scale`
/// against both baselines, then every version's cell per template.
pub fn scale_markdown(engine_dir: &Path, tree: &VersionTree, scale: &str, columns: &ScaleColumns) -> String {
    let rows: Vec<ScaleRow> = tree.versions().filter_map(|n| version_cells(engine_dir, &n.id, scale).map(|cells| ScaleRow {
        node: n,
        score: tree.score_at(&n.id, scale).map_or("-".to_string(), |s| format!("F {}/{}, G {}", s.score.finished, s.cells, s.score.normalized_time)),
        cells,
    })).collect();
    let intro = format!(
        "# Scale {scale}\n\nEvery version timed at {scale}, at binding {}: cell times in ms (a cell's median hot call; an unfinished cell counts the call limit of {} s in the totals). Ratio = total / the faster baseline's total. Generated by GenDB from the run's records.\n\n",
        columns.binding,
        columns.call_limit_ns / 1_000_000_000
    );
    intro + &scale_tables(&rows, columns, "..")
}

/// The totals and per-template tables of `rows` against `columns`' baselines; `up` leads from the table's file to the
/// engine directory (the version links).
fn scale_tables(rows: &[ScaleRow], columns: &ScaleColumns, up: &str) -> String {
    let workers_text = columns.workers.iter().map(u64::to_string).collect::<Vec<_>>().join(" / ");
    let mut out = String::from("## Totals per worker count\n\n| Version | Branch | Score |");
    for w in &columns.workers {
        out.push_str(&format!(" {w} workers ms (ratio) |"));
    }
    out.push_str(&format!("\n|---|---|---|{}\n", "---:|".repeat(columns.workers.len())));
    for (engine, pick) in [("Umbra", 0usize), ("DuckDB", 1)] {
        out.push_str(&format!("| {engine} | baseline | - |"));
        for w in &columns.workers {
            let total = columns.totals_ns.get(w).and_then(|(u, d)| if pick == 0 { *u } else { Some(*d) });
            out.push_str(&format!(" {} |", total.map_or("-".to_string(), ms)));
        }
        out.push('\n');
    }
    for ScaleRow { node, score, cells } in rows {
        out.push_str(&format!("| [{}]({up}/versions/{}/README.md) | {} | {score} |", node.id, node.id, node.branch));
        for w in &columns.workers {
            let total: Option<u64> = columns.templates.iter().map(|t| cells.iter().find(|c| &c.template == t && c.workers as u64 == *w).map(|c| c.status.time_ns(columns.call_limit_ns))).sum();
            let target = columns.totals_ns.get(w).map(|(u, d)| u.map_or(*d, |u| u.min(*d))).filter(|t| *t > 0);
            out.push_str(&match (total, target) {
                (Some(total), Some(target)) => format!(" {} ({:.3}) |", ms(total), total as f64 / target as f64),
                (Some(total), None) => format!(" {} |", ms(total)),
                _ => " - |".to_string(),
            });
        }
        out.push('\n');
    }
    out.push_str(&format!("\n## Per template ({workers_text} workers)\n\n| Template | Faster baseline |"));
    for row in rows {
        out.push_str(&format!(" {} |", row.node.id));
    }
    out.push_str(&format!("\n|---|---:|{}\n", "---:|".repeat(rows.len())));
    for template in &columns.templates {
        let baseline: Vec<String> = columns.workers.iter().map(|w| columns.faster_ns.get(&(template.clone(), *w)).map_or("-".to_string(), |ns| ms(*ns))).collect();
        out.push_str(&format!("| {template} | {} |", baseline.join(" / ")));
        for row in rows {
            let shown: Vec<String> = columns.workers.iter().map(|w| row.cells.iter().find(|c| &c.template == template && c.workers as u64 == *w).map_or("-".to_string(), |c| cell_text(&c.status))).collect();
            out.push_str(&format!(" {} |", shown.join(" / ")));
        }
        out.push('\n');
    }
    if rows.is_empty() {
        out.push_str("\nNo version has cells recorded at this scale yet.\n");
    }
    out
}

/// The run at a glance (module documentation).
fn readme(tree: &VersionTree, ladder: Option<&LadderState>, scales: &[String], spend: Option<Value>, head_profiled: bool) -> String {
    let current = ladder.map_or(0, |l| l.current);
    // The first one-engine version accepted by the request's one-engine rule did not beat its parent
    // (`engine::stage::one_engine`).
    let transition = crate::engine::stage::one_engine::ONE_ENGINE_TRANSITION;
    let beat = if tree.main_line.iter().any(|c| c.reason == transition) {
        format!(" and beat its parent in one interleaved timing, but the first one-engine version (main-line reason {transition}), which the request's one-engine rule accepted without beating it")
    } else {
        " and beat its parent in one interleaved timing".to_string()
    };
    let mut out = format!("# General engine\n\nOne verified engine for every supported query on the schema, optimized from version 0 (the verified SQLSpec interpreter over the flat storage) by branches in long sessions. Every version passed Verus on the whole crate against the fixed engine entry{beat}; every attempt is kept. Score at a scale: F finished cells, then G = the sum over worker counts of the engine's total over the faster baseline's total (lower is better). Generated by GenDB from the run's records.\n\n");
    out.push_str(&format!(
        "- Scale ladder: {}; current scale index {current}; moves: {}.\n",
        if scales.is_empty() { "-".to_string() } else { scales.join(" -> ") },
        ladder.map_or("none".to_string(), |l| if l.moves.is_empty() { "none".into() } else { l.moves.iter().map(|m| format!("to {} (main-line head {})", m["to"].as_str().unwrap_or("-"), m["main_line_head"].as_str().unwrap_or("-"))).collect::<Vec<_>>().join(", ") })
    ));
    let head = tree.main_line_head();
    out.push_str(&format!("- Main-line head: {}.\n", head.map_or("none yet".to_string(), |h| format!("[{h}](versions/{h}/README.md)"))));
    if let Some(spend) = spend {
        let dollars = spend["spent"].as_str().and_then(|d| d.parse::<f64>().ok()).map_or("-".to_string(), |d| format!("${d:.2}"));
        out.push_str(&format!("- Spend of the engine agents' calls (provider-reported, every session): {dollars} (complete: {}); framework work (version 0, timings, builds) is not included.\n",
            spend["complete"]));
    }
    let profile = if head_profiled { "main-line head's profile: [PROFILE.md](PROFILE.md)" } else { "the main-line head has no recorded profile" };
    out.push_str(&format!("- Versions: {}; attempts: {} ([TREE.md](TREE.md)); findings log: [FINDINGS.md](FINDINGS.md); {profile}.\n", tree.versions().count(), tree.attempts().count()));
    if !scales.is_empty() {
        out.push_str(&format!("- Per-scale tables: {}.\n", scales.iter().map(|s| format!("[{s}](scales/{s}.md)")).collect::<Vec<_>>().join(", ")));
    }
    let branches: BTreeSet<&str> = tree.nodes.iter().map(|n| n.branch.as_str()).filter(|b| *b != tree::MAIN).collect();
    if !branches.is_empty() {
        out.push_str("\n## Branches\n\n| Branch | Head | Versions | Attempts | Direction |\n|---|---|---:|---:|---|\n");
        for b in branches {
            let direction = tree.of_branch(b).filter(|n| n.direction.is_some()).max_by_key(|n| n.created_unix_ms).and_then(|n| n.direction.clone());
            out.push_str(&format!("| {b} | {} | {} | {} | {} |\n", tree.branch_head(b).unwrap_or("-"), tree.of_branch(b).filter(|n| n.accepted).count(), tree.of_branch(b).filter(|n| !n.accepted).count(),
                one_line(direction.as_deref())));
        }
    }
    out.push_str("\n## Versions\n\n| Version | Branch | Kind | Parents | Score | Later scores | Direction |\n|---|---|---|---|---|---|---|\n");
    for n in tree.versions() {
        let score = n.score.as_ref().map_or("-".to_string(), |s| format!("{}: F {}/{}, G {}", s.scale, s.score.finished, s.cells, s.score.normalized_time));
        let later: Vec<String> = tree.scale_scores.iter().filter(|((v, _), _)| *v == n.id).map(|((_, s), r)| format!("{s}: F {}/{}, G {}", r.score.finished, r.cells, r.score.normalized_time)).collect();
        out.push_str(&format!("| [{}](versions/{}/README.md) | {} | {:?} | {} | {score} | {} | {} |\n", n.id, n.id, n.branch, n.kind, n.parents.join(", "), if later.is_empty() { "-".into() } else { later.join("; ") },
            one_line(n.direction.as_deref())));
    }
    out
}

/// A stage run's versions with their workloads (`version.json` `workloads`), in tree order; empty for a
/// run without a stage.
fn stage_versions<'a>(engine_dir: &Path, tree: &'a VersionTree) -> Vec<(&'a tree::TreeNode, Value)> {
    tree.versions()
        .filter_map(|n| {
            let record: Value = serde_json::from_str(&fs::read_to_string(node_directory(engine_dir, &n.id, true).join("version.json")).ok()?).ok()?;
            record["workloads"].is_object().then(|| (n, record["workloads"].clone()))
        })
        .collect()
}

/// The workloads of `workloads` (`version.json` `workloads`): the goal (in a run of several workloads, the primary)
/// first, then the others by name, as `(name, record)`.
fn ordered_workloads(workloads: &Value) -> Vec<(&String, &Value)> {
    let mut all: Vec<(&String, &Value)> = workloads.as_object().into_iter().flatten().collect();
    all.sort_by_key(|(name, record)| (record["role"] != "goal" && record["primary"] != true, name.as_str()));
    all
}

/// The versions of a run of several workloads with their `version.json` (it carries `combined_score`, the workloads fixture), in
/// tree order; empty for every other run.
fn member_versions<'a>(engine_dir: &Path, tree: &'a VersionTree) -> Vec<(&'a tree::TreeNode, Value)> {
    tree.versions()
        .filter_map(|n| {
            let record: Value = serde_json::from_str(&fs::read_to_string(node_directory(engine_dir, &n.id, true).join("version.json")).ok()?).ok()?;
            record["combined_score"].is_object().then_some((n, record))
        })
        .collect()
}

/// A workload's result in one version as the tables show it: its recorded score, or a check workload's check
/// (`checked 12/12`).
fn member_result_text(record: &Value) -> String {
    if record["role"] == "check" {
        let check = &record["check"];
        return if check.is_object() { format!("checked {}/{}", check["agreed"], check["calls"]) } else { "-".into() };
    }
    recorded_score_text(&record["score"])
}

/// The README's section of a run of several workloads (module documentation).
fn members_section(versions: &[(&tree::TreeNode, Value)], tables: &[(String, String)]) -> String {
    let Some((_, newest)) = versions.last() else { return String::new() };
    let columns = ordered_workloads(&newest["workloads"]);
    let links: Vec<String> = tables.iter().map(|(workload, scale)| format!("[{workload} at {scale}](workloads/{workload}/{scale}.md)")).collect();
    let mut out = format!(
        "\n## Workloads\n\nOne engine for every workload of the run: the combined score (the sums of the counted workloads' F and G) decided every version; every check workload was verified and answered by every version, never timed; a kept workload was timed and shown, never deciding (`version.json` `workloads`, `combined_score`, `general`). One engine: no workload has its own module or an inherited storage. Workload tables: {}.\n\n| Version | Combined |",
        if links.is_empty() { "-".to_string() } else { links.join(", ") }
    );
    for (name, record) in &columns {
        let primary = if record["primary"] == true { ", primary" } else { "" };
        out.push_str(&format!(" {name} ({}{primary}, {}) |", record["role"].as_str().unwrap_or("-"), record["scale"].as_str().unwrap_or("-")));
    }
    out.push_str(&format!(" One engine |\n|---|---|{}---|\n", "---|".repeat(columns.len())));
    for (node, record) in versions {
        out.push_str(&format!("| [{}](versions/{}/README.md) | {} |", node.id, node.id, recorded_score_text(&record["combined_score"])));
        for (name, _) in &columns {
            out.push_str(&format!(" {} |", member_result_text(&record["workloads"][name.as_str()])));
        }
        out.push_str(&format!(" {} |\n", match record["general"]["one_engine"].as_bool() {
            Some(true) => "yes",
            Some(false) => "no",
            None => "-",
        }));
    }
    out
}

/// A recorded score (`engine::tree::RecordedScore` as JSON) as the tables show it: `F 12/66, G 2.470858685`.
fn recorded_score_text(score: &Value) -> String {
    if !score.is_object() {
        return "-".into();
    }
    let text = |v: &Value| v.as_str().map_or_else(|| v.to_string(), str::to_string);
    format!("F {}/{}, G {}", text(&score["score"]["finished"]), text(&score["cells"]), text(&score["score"]["normalized_time"]))
}

/// The README's stage section (module documentation): every version's score on every workload, and the kept
/// workloads' tables.
fn workloads_section(versions: &[(&tree::TreeNode, Value)], tables: &[(String, String)]) -> String {
    let Some((_, newest)) = versions.last() else { return String::new() };
    let columns = ordered_workloads(newest);
    let links: Vec<String> = tables.iter().map(|(workload, scale)| format!("[{workload} at {scale}](workloads/{workload}/{scale}.md)")).collect();
    let mut out = format!(
        "\n## Workloads\n\nA stage run: one engine serves every workload. The goal's score decided every version; every kept workload was verified, timed against the parent and is shown, never deciding (`version.json` `workloads`). Kept workloads' tables: {}.\n\n| Version |",
        if links.is_empty() { "-".to_string() } else { links.join(", ") }
    );
    for (name, record) in &columns {
        out.push_str(&format!(" {name} ({}, {}) |", record["role"].as_str().unwrap_or("-"), record["scale"].as_str().unwrap_or("-")));
    }
    out.push_str(&format!("\n|---|{}\n", "---|".repeat(columns.len())));
    for (node, workloads) in versions {
        out.push_str(&format!("| [{}](versions/{}/README.md) |", node.id, node.id));
        for (name, _) in &columns {
            out.push_str(&format!(" {} |", recorded_score_text(&workloads[name.as_str()]["score"])));
        }
        out.push('\n');
    }
    out
}

/// The tables of the kept workload `workload` at its scale (module documentation), from each version's recorded timing
/// of it (`version.json` `workloads.<name>.score.record`: a race report or a score record); `None` when no version has
/// a readable record. Returns the scale and the Markdown.
fn workload_markdown(versions: &[(&tree::TreeNode, Value)], workload: &str) -> Option<(String, String)> {
    workload_tables(versions, workload, "the kept workload", "A kept workload's numbers are recorded and shown; the goal's score decided every version")
}

/// [`workload_markdown`] with the wording of the workload's `kind` and the sentence on what decided (`decided`).
fn workload_tables(versions: &[(&tree::TreeNode, Value)], workload: &str, kind: &str, decided: &str) -> Option<(String, String)> {
    let mut columns: Option<ScaleColumns> = None;
    let mut scale = String::new();
    let mut rows: Vec<ScaleRow> = vec![];
    for (node, workloads) in versions {
        let record = &workloads[workload];
        let Some(score) = record["score"].as_object().map(|_| &record["score"]) else { continue };
        let Some(timing) = score["record"].as_str().and_then(|p| fs::read_to_string(p).ok()).and_then(|t| serde_json::from_str::<Value>(&t).ok()) else { continue };
        scale = record["scale"].as_str().unwrap_or("-").to_string();
        if columns.is_none() {
            columns = ScaleColumns::from_score_record(&timing, &node.id);
        }
        let cells: Vec<CellResult> = serde_json::from_value(score_side(&timing, &node.id)["cells"].clone()).unwrap_or_default();
        rows.push(ScaleRow { node, score: recorded_score_text(score), cells });
    }
    let columns = columns?;
    let intro = format!(
        "# Workload `{workload}` at {scale}\n\nEvery version timed on {kind} `{workload}` at {scale}, at binding {}: cell times in ms (a cell's median hot call; an unfinished cell counts the call limit of {} s in the totals). Ratio = total / the faster baseline's total. {decided}. Generated by GenDB from each version's recorded timing of this workload (`version.json` `workloads`).\n\n",
        columns.binding,
        columns.call_limit_ns / 1_000_000_000
    );
    Some((scale, intro + &scale_tables(&rows, &columns, "../..")))
}

/// The per-workload section of a stage version's own `README.md`, from its `version.json` record:
/// each workload's role, scale, score, serving storage against its budget, its whole-crate Verus run and its module, and
/// where its timing is recorded; `None` for a version without `workloads`.
pub fn workloads_readme(version: &Value) -> Option<String> {
    let workloads = version["workloads"].as_object().map(|_| &version["workloads"])?;
    if version["combined_score"].is_object() {
        return Some(members_readme(version));
    }
    let text = |v: &Value| v.as_str().map_or_else(|| v.to_string(), str::to_string);
    let mut out = String::from("## Workloads\n\nOne engine, one crate per workload: the goal's score decided this version; every kept workload was verified, timed against the parent and is shown, never deciding.\n\n| Workload | Role | Scale | Score | Serving bytes | Budget bytes | Verus | Workload module |\n|---|---|---|---|---:|---:|---:|---:|\n");
    for (name, record) in ordered_workloads(workloads) {
        let verus = record["proof"]["wall_ns"].as_u64().map_or("-".to_string(), |ns| format!("{:.1} s", ns as f64 / 1e9));
        out.push_str(&format!("| {name} | {} | {} | {} | {} | {} | {verus} | {} lines |\n", text(&record["role"]), text(&record["scale"]), recorded_score_text(&record["score"]),
            text(&record["storage"]["serving_bytes"]), text(&record["storage"]["budget_bytes"]), text(&record["module_lines"])));
    }
    let records: Vec<String> = ordered_workloads(workloads).iter().map(|(name, record)| format!("`{name}`: `{}`", record["score"]["record"].as_str().unwrap_or("-"))).collect();
    out.push_str(&format!("\nTiming records: {}.\n", records.join("; ")));
    Some(out)
}

/// The per-workload section of a version's own `README.md` in a run of several workloads, from its
/// `version.json` record: the combined score, each workload's role, scale, score or check, serving storage against its
/// budget, its whole-crate Verus run and what of it is specific to that workload, whether the version is one engine and
/// where every timing and check is recorded.
fn members_readme(version: &Value) -> String {
    let text = |v: &Value| v.as_str().map_or_else(|| v.to_string(), str::to_string);
    let workloads = ordered_workloads(&version["workloads"]);
    let general = &version["general"];
    let mut out = format!(
        "## Workloads\n\nOne engine for every workload: the combined score decided this version, {} over {}; every check workload was verified and answered; a kept workload was timed and shown, never deciding.\n\n| Workload | Role | Scale | Score or check | Serving bytes | Budget bytes | Verus | Own module | Inherited storages | Plans |\n|---|---|---|---|---:|---:|---:|---:|---|---:|\n",
        recorded_score_text(&version["combined_score"]),
        version["combined_score"]["workloads"].as_array().map_or("-".to_string(), |w| w.iter().map(text).collect::<Vec<_>>().join(" and "))
    );
    for (name, record) in &workloads {
        let verus = record["proof"]["wall_ns"].as_u64().map_or("-".to_string(), |ns| format!("{:.1} s", ns as f64 / 1e9));
        let inherited: Vec<String> = record["general"]["inherited_storages"].as_array().into_iter().flatten().map(text).collect();
        let role = if record["primary"] == true { format!("{} (primary)", text(&record["role"])) } else { text(&record["role"]) };
        out.push_str(&format!("| {name} | {role} | {} | {} | {} | {} | {verus} | {} lines | {} | {} lines |\n", text(&record["scale"]), member_result_text(record),
            text(&record["storage"]["serving_bytes"]), text(&record["storage"]["budget_bytes"]), text(&record["general"]["own_module_lines"]),
            if inherited.is_empty() { "-".to_string() } else { inherited.join(", ") }, text(&record["general"]["plan_lines"])));
    }
    out.push_str(&format!("\nOne engine: {}{}.\n", match general["one_engine"].as_bool() {
        Some(true) => "yes",
        Some(false) => "not yet",
        None => "-",
    }, general["shared_digest"].as_str().map_or(String::new(), |d| format!(" (shared sources' digest `{d}`)"))));
    let records: Vec<String> = workloads.iter().map(|(name, record)| {
        let place = record["score"]["record"].as_str().or_else(|| record["check"]["record"].as_str()).unwrap_or("-");
        format!("`{name}`: `{place}`")
    }).collect();
    out.push_str(&format!("\nTiming and check records: {}.\n", records.join("; ")));
    out
}

/// `text` on one table line (first line, `|` escaped), or `-`.
fn one_line(text: Option<&str>) -> String {
    text.and_then(|t| t.lines().next()).map_or("-".to_string(), |t| t.replace('|', "\\|"))
}

/// Write `<home>/engine/` from a general-line run's engine directory `engine_dir` (module documentation); returns what
/// was written.
pub fn write_general_engine(home: &Path, engine_dir: &Path) -> Result<Value, OutputError> {
    let tree = VersionTree::read(engine_dir).map_err(|e| OutputError(e.to_string()))?;
    let ladder = LadderState::read(engine_dir).ok();
    let out = home.join("engine");
    for node in &tree.nodes {
        let source = node.directory(engine_dir);
        if source.is_dir() {
            let target = out.join(if node.accepted { "versions" } else { "attempts" }).join(&node.id);
            copy_tree(&source, &target)?;
        }
    }
    for file in ["TREE.md", "tree.json", tree::FINDINGS_MARKDOWN] {
        if engine_dir.join(file).is_file() {
            fs::copy(engine_dir.join(file), out.join(file)).map_err(|e| io_error(&out.join(file), e))?;
        }
    }
    // The head's profile, when it has one; a copy of an earlier head's is removed.
    let head_profile = tree.main_line_head().map(|head| node_directory(engine_dir, head, true).join(PROFILE_FILE)).filter(|p| p.is_file());
    match &head_profile {
        Some(profile) => fs::copy(profile, out.join(PROFILE_FILE)).map(drop).map_err(|e| io_error(&out.join(PROFILE_FILE), e))?,
        None if out.join(PROFILE_FILE).is_file() => fs::remove_file(out.join(PROFILE_FILE)).map_err(|e| io_error(&out.join(PROFILE_FILE), e))?,
        None => {}
    }
    let scales = scales_of(&tree, ladder.as_ref());
    let mut written = vec![];
    for scale in &scales {
        let columns = columns_of(&tree, scale).unwrap_or_default();
        write_text(&out.join("scales").join(format!("{scale}.md")), &scale_markdown(engine_dir, &tree, scale, &columns))?;
        written.push(scale.clone());
    }
    // A stage run: the kept workloads' tables, and every version's score on every workload in the README. A run of several
    // workloads: the tables of every timed workload other than the primary, and every version's combined score and
    // results.
    let stage = stage_versions(engine_dir, &tree);
    let members = member_versions(engine_dir, &tree);
    let mut tables: Vec<(String, String)> = vec![];
    if let Some((_, newest)) = stage.last() {
        let several = !members.is_empty();
        let timed_elsewhere = |record: &Value| if several { record["primary"] != true && record["role"] != "check" } else { record["role"] != "goal" };
        for (name, record) in ordered_workloads(newest).into_iter().filter(|(_, record)| timed_elsewhere(record)) {
            let markdown = if several {
                let kind = format!("the {} workload", record["role"].as_str().unwrap_or("-"));
                workload_tables(&stage, name, &kind, "The combined score over the counted workloads decided every version")
            } else {
                workload_markdown(&stage, name)
            };
            if let Some((scale, markdown)) = markdown {
                write_text(&out.join("workloads").join(name).join(format!("{scale}.md")), &markdown)?;
                tables.push((name.clone(), scale));
            }
        }
    }
    let spend = RunSpend::new(engine_dir, Money::UNSET).now().ok().map(|now| json!({"spent":now.spent.decimal(),"complete":now.complete}));
    let workloads_text = if members.is_empty() { workloads_section(&stage, &tables) } else { members_section(&members, &tables) };
    let readme_text = readme(&tree, ladder.as_ref(), &scales, spend, head_profile.is_some()) + &workloads_text;
    write_text(&out.join("README.md"), &readme_text)?;
    let mut summary = json!({"engine":out,"versions":tree.versions().count(),"attempts":tree.attempts().count(),"scales":written});
    if !stage.is_empty() {
        summary["workload_tables"] = json!(tables.iter().map(|(w, s)| format!("{w}/{s}")).collect::<Vec<_>>());
    }
    Ok(summary)
}

/// The general line's output home, when the request names one (`output_home`): written after `gendb engine prepare` and
/// after every session; a failure is recorded under the run (`output-error-<ms>.json`), never fatal.
pub fn write_general_output(request: &WorkloadRequest, root: &Path, engine_dir: &Path) {
    let Some(home) = &request.output_home else { return };
    if let Err(error) = write_general_engine(home, engine_dir) {
        let record = root.join(format!("output-error-{}.json", records::now_unix_ms()));
        let _ = records::write_json_atomic(&record, &json!({"output_home":home,"error":error.to_string()}));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prompts::engine_facts::general::tests as fixture;

    /// The output home of the scripted run: every version and attempt folder, the tree, the findings, the main-line
    /// head's profile, the per-scale table with both baselines and every version's cells, and the README.
    #[test]
    fn the_general_output_home_has_every_record_and_the_scale_tables() {
        let root = fixture::scratch("general-output");
        let run = fixture::scripted_run(&root.join("run"));
        let home = root.join("home");
        let written = write_general_engine(&home, &run.engine_dir).unwrap();
        assert_eq!((written["versions"].as_u64(), written["attempts"].as_u64(), written["scales"][0].as_str()), (Some(2), Some(2), Some("sf1")));
        for file in ["engine/README.md", "engine/TREE.md", "engine/tree.json", "engine/FINDINGS.md", "engine/PROFILE.md", "engine/scales/sf1.md", "engine/versions/v001/code-view/agent/mod.rs.md",
            "engine/versions/v001/race.json", "engine/versions/v000/profile/Q09-w64.json", "engine/attempts/b1-a001/code/agent/mod.rs", "engine/attempts/b1-a002/attempt.json"] {
            assert!(home.join(file).is_file(), "{file}");
        }
        let scale = fs::read_to_string(home.join("engine/scales/sf1.md")).unwrap();
        assert!(scale.contains("| [v001](../versions/v001/README.md) | b1 | F 9/9, G 41.250000000 | 10050.000 (29.559) |"), "{scale}");
        assert!(scale.contains("| Q09 | 300.000 / 20.000 / 25.000 | time limit / time limit / memory limit | 9000.000 / 700.000 / 650.000 |"), "{scale}");
        let readme = fs::read_to_string(home.join("engine/README.md")).unwrap();
        assert!(readme.contains("- Main-line head: [v001](versions/v001/README.md).") && readme.contains("| b1 | v001 | 1 | 2 | vectorized operators"), "{readme}");
        assert!(readme.contains("- Spend of the engine agents' calls (provider-reported, every session): $55.50 (complete: true)"), "{readme}");
        // A second write replaces the copies whole.
        write_general_engine(&home, &run.engine_dir).unwrap();
        fs::remove_dir_all(&root).unwrap();
    }

    /// A stage run's output home: the README's table of every version's score on every
    /// workload, the kept workload's tables at its scale from each version's recorded timing of it, and a version's own
    /// per-workload README section.
    #[test]
    fn a_stage_run_output_shows_every_version_on_every_workload() {
        use crate::prompts::engine_facts::general::tests::stage_run::*;
        let root = fixture::scratch("general-output-stage");
        let run = stage_run(&root);
        stage_first_submission(&run);
        let home = root.join("home");
        let written = write_general_engine(&home, &run.engine_dir).unwrap();
        assert_eq!(written["workload_tables"], json!(["tpch/sf100"]));
        let readme = fs::read_to_string(home.join("engine/README.md")).unwrap();
        assert!(readme.contains("\n## Workloads\n\nA stage run: one engine serves every workload.") && readme.contains("Kept workloads' tables: [tpch at sf100](workloads/tpch/sf100.md)."), "{readme}");
        assert!(readme.contains("| Version | sec (goal, sf3) | tpch (kept, sf100) |\n|---|---|---|\n| [v000](versions/v000/README.md) | F 3/18, G 1185.104912800 | F 12/12, G 2.316701349 |\n| [v001](versions/v001/README.md) | F 17/18, G 128.456566853 | F 12/12, G 2.314361561 |"), "{readme}");
        let kept = fs::read_to_string(home.join("engine/workloads/tpch/sf100.md")).unwrap();
        assert!(kept.starts_with("# Workload `tpch` at sf100\n\nEvery version timed on the kept workload `tpch` at sf100, at binding v0:"), "{kept}");
        assert!(kept.contains("| [v000](../../versions/v000/README.md) | main | F 12/12, G 2.316701349 | 47713.762 (0.784) | 3444.462 (0.862) | 2877.506 (0.671) |"), "{kept}");
        assert!(kept.contains("| [v001](../../versions/v001/README.md) | b1 | F 12/12, G 2.314361561 |") && kept.contains("| Q18 | 17501.337 / 1472.139 / 1527.797 | 16344.826 / 1358.196 / 1207.340 | 16200.000 / 1371.000 / 1188.000 |"), "{kept}");
        let version: Value = serde_json::from_str(&fs::read_to_string(node_directory(&run.engine_dir, "v001", true).join("version.json")).unwrap()).unwrap();
        let section = workloads_readme(&version).unwrap();
        assert!(section.contains("| sec | goal | sf3 | F 17/18, G 128.456566853 | 4987654321 | 5439582957 | 271.0 s | 214 lines |") && section.contains("| tpch | kept | sf100 | F 12/12, G 2.314361561 | 90766134568 | 114641618862 | 268.0 s | 388 lines |"), "{section}");
        assert!(workloads_readme(&json!({"version":"v000"})).is_none());
        fs::remove_dir_all(&root).unwrap();
    }

    /// A run of several workloads' output home: the README's table of every version's combined
    /// score, its result on every workload (a check workload's check) and whether it is one engine; the tables of the
    /// other counted workload at its scale; a version's own per-workload section with the combined score, every
    /// workload's code report and the one-engine status.
    #[test]
    fn a_run_of_several_workloads_output_shows_the_combined_score_and_every_workload() {
        use crate::prompts::engine_facts::general::tests::workloads_run::*;
        let root = fixture::scratch("general-output-workloads");
        let run = workloads_run(&root);
        workloads_first_submission(&run);
        let home = root.join("home");
        let written = write_general_engine(&home, &run.engine_dir).unwrap();
        assert_eq!(written["workload_tables"], json!(["sec/sf3"]));
        let readme = fs::read_to_string(home.join("engine/README.md")).unwrap();
        assert!(readme.contains("\n## Workloads\n\nOne engine for every workload of the run: the combined score") && readme.contains("Workload tables: [sec at sf3](workloads/sec/sf3.md)."), "{readme}");
        assert!(readme.contains("| Version | Combined | tpch (counted, primary, sf100) | anyschema (check, tiny) | sec (counted, sf3) | One engine |\n|---|---|---|---|---|---|\n"), "{readme}");
        assert!(readme.contains("| [v000](versions/v000/README.md) | F 30/30, G 17.889687204 | F 12/12, G 2.545797717 | checked 12/12 | F 18/18, G 15.343889487 | no |"), "{readme}");
        assert!(readme.contains("| [v001](versions/v001/README.md) | F 30/30, G 16.263352004 | F 12/12, G 2.314361561 | checked 12/12 | F 18/18, G 13.948990443 | no |"), "{readme}");
        let other = fs::read_to_string(home.join("engine/workloads/sec/sf3.md")).unwrap();
        assert!(other.starts_with("# Workload `sec` at sf3\n\nEvery version timed on the counted workload `sec` at sf3, at binding v0:") && other.contains("The combined score over the counted workloads decided every version."), "{other}");
        let version: Value = serde_json::from_str(&fs::read_to_string(node_directory(&run.engine_dir, "v001", true).join("version.json")).unwrap()).unwrap();
        let section = workloads_readme(&version).unwrap();
        assert!(section.starts_with("## Workloads\n\nOne engine for every workload: the combined score decided this version, F 30/30, G 16.263352004 over tpch and sec;"), "{section}");
        assert!(section.contains("| tpch | counted (primary) | sf100 | F 12/12, G 2.314361561 | 90766134568 | 114641618862 | 268.0 s | 1657 lines | narrowpack, narrowpack2, narrowpack3, narrowpack4, narrowpack5, narrowpack6 | 0 lines |")
            && section.contains("| anyschema | check | tiny | checked 12/12 | 1048576 | null | 41.0 s | 0 lines | - | 0 lines |") && section.contains("One engine: not yet (shared sources' digest `5555"), "{section}");
        fs::remove_dir_all(&root).unwrap();
    }

    /// Writes the run of several workloads' output home (the scripted run after its first accepted version) under
    /// `GENDB_GENERAL_RENDER_DIR/workloads-output-home/` for review, with `v001`'s per-workload README section.
    #[test]
    #[ignore = "writes the output home of a run of several workloads under GENDB_GENERAL_RENDER_DIR for review"]
    fn write_workloads_output_render() {
        use crate::prompts::engine_facts::general::tests::workloads_run::*;
        let out = std::path::PathBuf::from(std::env::var("GENDB_GENERAL_RENDER_DIR").expect("GENDB_GENERAL_RENDER_DIR")).join("workloads-output-home");
        fs::remove_dir_all(&out).ok();
        let run = workloads_run(&out.join("fixture"));
        workloads_first_submission(&run);
        let written = write_general_engine(&out.join("home"), &run.engine_dir).unwrap();
        let version: Value = serde_json::from_str(&fs::read_to_string(node_directory(&run.engine_dir, "v001", true).join("version.json")).unwrap()).unwrap();
        fs::write(out.join("v001-workloads-readme.md"), workloads_readme(&version).unwrap()).unwrap();
        println!("workloads output home: {written}");
    }

    /// Writes the stage run's output home (the scripted stage run after its first accepted version) under `GENDB_GENERAL_RENDER_DIR/stage-output-home/` for review, with the per-workload section of
    /// `v001`'s README as `v001-workloads-readme.md`.
    #[test]
    #[ignore = "writes the stage output home under GENDB_GENERAL_RENDER_DIR for review"]
    fn write_stage_output_render() {
        use crate::prompts::engine_facts::general::tests::stage_run::*;
        let out = std::path::PathBuf::from(std::env::var("GENDB_GENERAL_RENDER_DIR").expect("GENDB_GENERAL_RENDER_DIR")).join("stage-output-home");
        fs::remove_dir_all(&out).ok();
        let run = stage_run(&out.join("fixture"));
        stage_first_submission(&run);
        let written = write_general_engine(&out.join("home"), &run.engine_dir).unwrap();
        let version: Value = serde_json::from_str(&fs::read_to_string(node_directory(&run.engine_dir, "v001", true).join("version.json")).unwrap()).unwrap();
        fs::write(out.join("v001-workloads-readme.md"), workloads_readme(&version).unwrap()).unwrap();
        println!("stage output home: {written}");
    }

    /// Golden: without a stage, the output home's README and per-scale table are byte for byte
    /// as before the stage output was added (digest recorded with the unchanged output code; paths under the scratch root
    /// written as `<root>`).
    #[test]
    fn the_general_output_without_a_stage_renders_as_before() {
        let root = fixture::scratch("general-output-unchanged");
        let run = fixture::scripted_run(&root.join("run"));
        let home = root.join("home");
        write_general_engine(&home, &run.engine_dir).unwrap();
        let text: String = ["engine/README.md", "engine/scales/sf1.md"].iter().map(|f| fs::read_to_string(home.join(f)).unwrap()).collect();
        let text = text.replace(&root.display().to_string(), "<root>");
        fs::remove_dir_all(&root).unwrap();
        assert_eq!(crate::prompts::engine_policy::tests::sha256_hex(&text), GENERAL_OUTPUT_GOLDEN, "the general output home changed:\n{text}");
    }

    const GENERAL_OUTPUT_GOLDEN: &str = "7906fea638410f7dc120c1e0e7db5e5119528f46be81304703f1b210f197a023";
}
