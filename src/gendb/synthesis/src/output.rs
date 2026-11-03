//! The readable output home of a workload, written by GenDB itself, e.g. `output/tpch-sf100/`:
//!
//! ```text
//! README.md                          the workload at a glance (queries, storages, evaluation)
//! workload/README.md                 the workload storage session: selected attempt, storages
//! workload/storage/<name>/           README.md, interface/, builder/ (author code of one admitted storage)
//! workload/attempts/<n>/README.md    one workload submission
//! queries/qNN/README.md              template, parameters, result per cell, storages, attempts, proof scope
//! queries/qNN/query.sql, spec.rs     the SQL template and its emitted SQLSpec statement (`query.rs`)
//! queries/qNN/code/, code-view/      the selected submission's author code, and its reading view
//! queries/qNN/attempts/<n>/          README.md per submission (+ code/ of a submission that was not selected,
//!                                    + NOTES.md when the session kept the author's notes)
//! baselines/, evaluation/, reviews/  written by the baseline runner, `gendb evaluate` and the reviewers
//! engine/                            an engine run's versions and rounds (`engine`, written by `engine::rounds`)
//! records/                           the same paths with the raw machine records (JSON) behind each README
//! ```
//!
//! Names are readable (no content hashes or machine numbering in paths); every folder has a README; every file exists
//! once (the selected submission's code only under `code/`). Framework files are not copied: they stay once in the
//! library, as the blobs of the admitted build record and a version manifest `<library>/framework/<kind>-<version>.json`;
//! `gendb rebuild qNN` ([`rebuild`]) assembles the full crate from them and the author code here.
//!
//! The controller calls [`write_query`] after a query session closes (admission and selection done) and
//! [`write_workload`] after the workload storage session; both replace that query's (workload's) folders and the
//! top-level README, and never touch other queries. Reading only: nothing here proves, builds or measures.

mod code_view;
pub mod engine;
pub mod evaluation;
mod query;
mod rebuild;
mod workload;

pub use code_view::code_view;
pub use query::{QueryOutput, write_query};
pub use rebuild::rebuild;
pub use workload::{WorkloadOutput, write_workload};

use serde_json::{Value, json};
use std::fmt;
use std::path::{Path, PathBuf};

/// Why an output folder could not be written.
#[derive(Debug)]
pub struct OutputError(pub String);

impl fmt::Display for OutputError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for OutputError {}

pub(crate) fn io_error(path: &Path, e: impl fmt::Display) -> OutputError {
    OutputError(format!("{}: {e}", path.display()))
}

/// Write `text` to `path`, creating its parent directories. The file is written beside it and renamed into place, so
/// controllers writing the same file at once (the top-level READMEs) never leave it interleaved: the last one wins.
pub(crate) fn write_text(path: &Path, text: &str) -> Result<(), OutputError> {
    let parent = path.parent().ok_or_else(|| OutputError(format!("{} has no parent", path.display())))?;
    std::fs::create_dir_all(parent).map_err(|e| io_error(parent, e))?;
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_nanos()).unwrap_or_default();
    let name = path.file_name().and_then(|n| n.to_str()).unwrap_or("file");
    let staging = parent.join(format!(".{name}.{}-{nanos}.tmp", std::process::id()));
    std::fs::write(&staging, text).map_err(|e| io_error(&staging, e))?;
    std::fs::rename(&staging, path).map_err(|e| io_error(path, e))
}

/// Write `value` as pretty JSON to `path`.
pub(crate) fn write_json(path: &Path, value: &Value) -> Result<(), OutputError> {
    write_text(path, &format!("{}\n", serde_json::to_string_pretty(value).unwrap_or_default()))
}

/// The JSON at `path`, or `None` when it does not exist or does not parse.
pub(crate) fn read_json(path: &Path) -> Option<Value> {
    serde_json::from_str(&std::fs::read_to_string(path).ok()?).ok()
}

/// The current evaluation of one submission's iteration directory: the newest framework repair's re-evaluation
/// (`reevaluation-<revision>.json`, its `evaluation`, with `repaired_by` naming the revision) when the controller
/// repaired it, else `evaluation.json`; `Null` when there is none.
pub(crate) fn iteration_evaluation(dir: &Path) -> Value {
    let mut repairs: Vec<(std::time::SystemTime, PathBuf)> = std::fs::read_dir(dir)
        .into_iter()
        .flatten()
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.file_name().and_then(|n| n.to_str()).is_some_and(|n| n.starts_with("reevaluation-") && n.ends_with(".json")))
        .filter_map(|p| Some((std::fs::metadata(&p).ok()?.modified().ok()?, p)))
        .collect();
    repairs.sort();
    if let Some((_, path)) = repairs.last()
        && let Some(record) = read_json(path)
    {
        let mut evaluation = record["evaluation"].clone();
        evaluation["repaired_by"] = record["revision"].clone();
        evaluation["original_evaluation"] = json!(dir.join("evaluation.json"));
        return evaluation;
    }
    read_json(&dir.join("evaluation.json")).unwrap_or(Value::Null)
}

/// A byte count in readable decimal units (`9.77 MB`, `41.20 GB`).
pub(crate) fn byte_size(bytes: u64) -> String {
    let b = bytes as f64;
    match bytes {
        0..1_000_000 => format!("{:.1} kB", b / 1e3),
        1_000_000..1_000_000_000 => format!("{:.2} MB", b / 1e6),
        _ => format!("{:.2} GB", b / 1e9),
    }
}

/// Every regular file under `root`, as paths relative to it, sorted.
pub(crate) fn files_under(root: &Path) -> Vec<PathBuf> {
    fn walk(root: &Path, dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = std::fs::read_dir(dir) else { return };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                walk(root, &path, out);
            } else if let Ok(relative) = path.strip_prefix(root) {
                out.push(relative.to_path_buf());
            }
        }
    }
    let mut out = vec![];
    walk(root, root, &mut out);
    out.sort();
    out
}

/// Copy every file under `from` to the same relative path under `to`; with `view`, also write the reading view of each
/// `.rs` file under `view` (the same relative path). Returns the relative paths copied.
pub(crate) fn copy_code(from: &Path, to: &Path, view: Option<&Path>) -> Result<Vec<PathBuf>, OutputError> {
    let files = files_under(from);
    for relative in &files {
        let source = from.join(relative);
        let text = std::fs::read_to_string(&source).map_err(|e| io_error(&source, e))?;
        write_text(&to.join(relative), &text)?;
        if let Some(view) = view
            && relative.extension().is_some_and(|x| x == "rs")
        {
            write_text(&view.join(relative), &code_view(&text))?;
        }
    }
    Ok(files)
}

/// Build a folder in a sibling staging directory with `fill`, then replace `target` with it (so a reader never sees a
/// half-written folder and no stale file survives).
pub(crate) fn replace_dir(target: &Path, fill: impl FnOnce(&Path) -> Result<(), OutputError>) -> Result<(), OutputError> {
    let parent = target.parent().ok_or_else(|| OutputError(format!("{} has no parent", target.display())))?;
    std::fs::create_dir_all(parent).map_err(|e| io_error(parent, e))?;
    let name = target.file_name().and_then(|n| n.to_str()).unwrap_or("folder");
    let staging = parent.join(format!(".{name}.staging"));
    if staging.exists() {
        std::fs::remove_dir_all(&staging).map_err(|e| io_error(&staging, e))?;
    }
    std::fs::create_dir_all(&staging).map_err(|e| io_error(&staging, e))?;
    fill(&staging)?;
    if target.exists() {
        std::fs::remove_dir_all(target).map_err(|e| io_error(target, e))?;
    }
    std::fs::rename(&staging, target).map_err(|e| io_error(target, e))
}

/// The iteration directories `iterations/NNNN` of a session, with their numbers, ascending.
pub(crate) fn iterations(session: &Path) -> Vec<(u32, PathBuf)> {
    let mut out: Vec<(u32, PathBuf)> = std::fs::read_dir(session.join("iterations"))
        .into_iter()
        .flatten()
        .flatten()
        .filter_map(|e| Some((e.file_name().to_str()?.parse().ok()?, e.path())))
        .collect();
    out.sort();
    out
}

/// The qualified iterations of a session summary (`summary.json` `qualification`), in order.
pub(crate) fn qualified_iterations(summary: &Value) -> Vec<u32> {
    summary["qualification"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|q| q["result"]["qualified"] == true)
        .filter_map(|q| q["iteration"].as_u64().map(|i| i as u32))
        .collect()
}

/// Nanoseconds as milliseconds with three decimals.
pub(crate) fn ms(ns: u64) -> String {
    format!("{:.3}", ns as f64 / 1e6)
}

/// Rewrite the top-level README of the home from what its folders hold.
pub(crate) fn write_home_readme(home: &Path) -> Result<(), OutputError> {
    let mut text = String::from(
        "# GenDB workload output\n\nWritten by GenDB (`gendb_synthesis::output`). Every folder has a README; raw machine records are under \
         `records/` at the same paths. Framework files are kept once in the library (see each query's README); `gendb rebuild qNN` \
         assembles a query's full crate.\n\n",
    );
    text.push_str("| Folder | What |\n|---|---|\n");
    text.push_str("| [workload/](workload/README.md) | shared storage designed by the workload agent, and storages added by query agents |\n");
    text.push_str("| [queries/](queries/README.md) | one folder per query: template, result per cell, code, attempts |\n");
    for (folder, what) in [("bindings", "visible and hidden parameter bindings"), ("baselines", "DuckDB and Umbra baselines"), ("evaluation", "final evaluation on the hidden bindings (`gendb evaluate`)"), ("reviews", "trajectory reviews")] {
        if home.join(folder).exists() {
            text.push_str(&format!("| [{folder}/]({folder}/) | {what} |\n"));
        }
    }
    text.push_str("| [records/](records/) | raw machine records behind every README |\n");
    let queries: Vec<String> = std::fs::read_dir(home.join("queries"))
        .into_iter()
        .flatten()
        .flatten()
        .filter(|e| e.path().is_dir())
        .filter_map(|e| e.file_name().to_str().map(String::from))
        .filter(|n| !n.starts_with('.'))
        .collect();
    let mut queries = queries;
    queries.sort();
    text.push_str("\n## Queries\n\n");
    let mut index = String::from("# Queries\n\n| Query | Status |\n|---|---|\n");
    for q in &queries {
        let status = read_json(&home.join("records/queries").join(q).join("query.json")).map(|v| v["status_line"].as_str().unwrap_or("").to_string()).unwrap_or_default();
        text.push_str(&format!("- [{q}](queries/{q}/README.md): {status}\n"));
        index.push_str(&format!("| [{q}]({q}/README.md) | {status} |\n"));
    }
    write_text(&home.join("queries/README.md"), &index)?;
    write_text(&home.join("README.md"), &text)
}

/// The subdirectories of `dir` with their names, sorted.
pub(crate) fn subdirectories(dir: &Path) -> Vec<(String, PathBuf)> {
    let mut out: Vec<(String, PathBuf)> = std::fs::read_dir(dir)
        .into_iter()
        .flatten()
        .flatten()
        .filter(|e| e.path().is_dir())
        .filter_map(|e| Some((e.file_name().to_str()?.to_string(), e.path())))
        .collect();
    out.sort();
    out
}
