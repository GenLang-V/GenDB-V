//! `queries/qNN/` and `records/queries/qNN/` of the output home: one query session after it closed.

use super::rebuild::record_framework_version;
use super::workload::{open_library, package_of, storage_version_dir, write_admitted_storage, write_storage, write_storage_index};
use super::{
    OutputError, copy_code, iterations, ms, qualified_iterations, read_json, replace_dir, subdirectories, write_home_readme, write_json,
    write_text,
};
use crate::controller::request::QueryRequest;
use gendb_frontend::params::BindingRequest;
use serde_json::{Value, json};
use std::path::{Path, PathBuf};

/// The speedup a cell must reach when the request sets no early stop (aim for at least 5x per cell).
const DEFAULT_BAR: u32 = 5;

/// One closed query session to publish.
pub struct QueryOutput<'a> {
    /// The query's folder name, e.g. `q01`.
    pub name: &'a str,
    /// The query as requested (SQL, parameters with names, objective with targets and early stop).
    pub request: &'a QueryRequest,
    /// The query session's root directory (`<run>/queries/query-NNNN`: `summary.json`, `iterations/`, `author/`).
    pub session: &'a Path,
    /// The library root of the run (admitted builds and framework files).
    pub library: &'a Path,
}

/// One submission of the session.
struct Attempt {
    number: u32,
    dir: PathBuf,
    evaluation: Value,
    qualification: Value,
}

impl Attempt {
    fn src(&self) -> PathBuf {
        self.dir.join("frozen/crate/src")
    }
}

/// Write `queries/<name>/` and `records/queries/<name>/` of the output `home` from the closed session, every storage the
/// selected submission reads that the home lacks (`workload/storage/<storage>/v<N>/`, then the storage indexes), and the
/// top-level README. Returns the query's record.
pub fn write_query(home: &Path, q: &QueryOutput<'_>) -> Result<Value, OutputError> {
    let summary = read_json(&q.session.join("summary.json")).unwrap_or(Value::Null);
    let attempt = |(number, dir): (u32, PathBuf)| Attempt {
        evaluation: super::iteration_evaluation(&dir),
        qualification: read_json(&dir.join("qualification.json")).unwrap_or(Value::Null),
        number,
        dir,
    };
    let mut attempts: Vec<Attempt> = iterations(q.session).into_iter().map(attempt).collect();
    // A reselection holds only its copy of the selected submission: the author's other submissions stay in the closed
    // source session and are published from there.
    if let Some(source) = summary["source_accounting"]["session"].as_str() {
        let own: Vec<u32> = attempts.iter().map(|a| a.number).collect();
        attempts.extend(iterations(Path::new(source)).into_iter().filter(|(number, _)| !own.contains(number)).map(attempt));
        attempts.sort_by_key(|a| a.number);
    }
    let selected = selected_attempt(&summary, &attempts);
    let bar = q.request.objective.early_stop().map_or(DEFAULT_BAR, |s| s.min_speedup);
    // The README's cells: the served package's final measurement when the closure recorded it, else the evaluation.
    let resolution = read_json(&q.session.join("resolution.json")).unwrap_or(Value::Null);
    let final_cells = selected.map(|a| final_cell_rows(q.request, &resolution, &a.qualification, bar)).unwrap_or_default();
    let timing = if final_cells.is_empty() { "submission_evaluation" } else { "final_measurement" };
    let cells = if final_cells.is_empty() { selected.map(|a| cell_rows(q.request, &a.evaluation, bar)).unwrap_or_default() } else { final_cells };
    let met = !cells.is_empty() && cells.iter().all(|c| c["met"] == true);
    let status_line = match selected {
        Some(a) => format!(
            "attempt {} selected; {} of {} cells at least {bar}x faster than the target",
            a.number,
            cells.iter().filter(|c| c["met"] == true).count(),
            cells.len()
        ),
        None => format!("no selected submission ({} attempts)", attempts.len()),
    };

    // The storage versions the selected submission reads, each by its exact package: the ones it added from its frozen
    // crates, every other one from the library when the home lacks it; `version` is the library's number of the package.
    let mut added = vec![];
    let mut storages: Vec<Value> = selected.map(|a| a.evaluation["storage"].as_array().cloned().unwrap_or_default()).unwrap_or_default();
    if let Some(a) = selected {
        let store = open_library(q.library)?;
        for (storage, dir) in subdirectories(&a.dir.join("frozen/storages")) {
            let package = package_of(&a.evaluation["storage"], &storage)
                .ok_or_else(|| OutputError(format!("{} attempt {}: the evaluation names no package for storage {storage}", q.name, a.number)))?;
            write_storage(home, &store, &storage, package, &dir, &format!("added by {} (attempt {})", q.name, a.number))?;
            added.push(storage);
        }
        for s in &mut storages {
            let (Some(name), Some(package)) = (s["name"].as_str(), s["package"].as_str()) else {
                return Err(OutputError(format!("{} attempt {}: a storage use without name and package: {s}", q.name, a.number)));
            };
            let version = write_admitted_storage(home, &store, name, package)?;
            s["version"] = json!(version);
        }
        write_storage_index(home)?;
    }
    let build = selected.and_then(|a| a.qualification["build"].as_str().map(String::from));
    let framework = match &build {
        Some(id) => record_framework_version(q.library, id, "query").ok(),
        None => None,
    };

    replace_dir(&home.join("queries").join(q.name), |dir| {
        write_text(&dir.join("query.sql"), &format!("{}\n", q.request.sql.trim_end()))?;
        if let Some(spec) = selected.or(attempts.last()).map(|a| a.src().join("query.rs"))
            && let Ok(text) = std::fs::read_to_string(&spec)
        {
            write_text(&dir.join("spec.rs"), &text)?;
        }
        if let Some(a) = selected {
            copy_code(&a.src().join("agent"), &dir.join("code"), Some(&dir.join("code-view")))?;
            write_text(&dir.join("code/README.md"), "# Code\n\nThe selected submission's author code (`crate::agent`), as verified and admitted. Authoritative.\n")?;
            write_text(
                &dir.join("code-view/README.md"),
                "# Code view\n\nThe reading view of `../code/`: proof and spec functions, proof blocks, asserts, ghost \
                 variables, invariants and decreases removed; each function's requires/ensures kept as comments; line numbers \
                 unchanged. Reading only, never compiled; `../code/` is authoritative.\n",
            )?;
        }
        for a in &attempts {
            write_attempt(dir, q, a, selected.map(|s| s.number), bar)?;
        }
        write_text(&dir.join("attempts/README.md"), &attempts_index(&attempts, selected.map(|s| s.number)))?;
        write_text(&dir.join("README.md"), &query_readme(q, &summary, &resolution, selected, &attempts, &cells, timing, bar, &storages, &added, framework.as_deref()))
    })?;

    let record = json!({"query":q.name,"status_line":status_line,"selected_attempt":selected.map(|a| a.number),"all_cells_met":met,
        "bar_speedup":bar,"cells":cells,"cells_from":timing,"attempts":attempts.len(),"reported_cost_usd":summary["reported_cost_usd"],
        "session":q.session,"storages_added":added});
    replace_dir(&home.join("records/queries").join(q.name), |dir| {
        write_json(&dir.join("query.json"), &record)?;
        write_json(&dir.join("summary.json"), &summary)?;
        for a in &attempts {
            let target = dir.join("attempts").join(a.number.to_string());
            for (file, value) in [("evaluation.json", &a.evaluation), ("qualification.json", &a.qualification)] {
                if !value.is_null() {
                    write_json(&target.join(file), value)?;
                }
            }
        }
        let rebuild = json!({"query":q.name,"library":q.library,"build":build,"framework_manifest":framework,
            "storages":storages.iter().map(|s| s["name"].clone()).collect::<Vec<_>>(),
            "storage_versions":storages.iter().map(|s| json!({"name":s["name"],"package":s["package"],"version":s["version"],
                "folder":format!("workload/storage/{}", storage_version_dir(s["name"].as_str().unwrap_or("?"), s["version"].as_u64().unwrap_or(0) as usize))})).collect::<Vec<_>>(),
            "selected_attempt":selected.map(|a| a.number),
            "author_code":format!("queries/{}/code", q.name)});
        write_json(&dir.join("rebuild.json"), &rebuild)?;
        write_text(&dir.join("README.md"), &format!("# Records of {}\n\nRaw machine records behind `queries/{0}/`: `query.json` (what the README shows), the session `summary.json`, per attempt `evaluation.json` and `qualification.json`, and `rebuild.json` (what `gendb rebuild {0}` reads).\n", q.name))
    })?;
    write_home_readme(home)?;
    Ok(record)
}

/// The selected submission: the session's best score when it is qualified, else the last qualified one.
fn selected_attempt<'a>(summary: &Value, attempts: &'a [Attempt]) -> Option<&'a Attempt> {
    let qualified = qualified_iterations(summary);
    let best = summary["objective"]["current_best_score"]["iteration"].as_u64().map(|i| i as u32).filter(|i| qualified.contains(i));
    let number = best.or(qualified.last().copied())?;
    attempts.iter().find(|a| a.number == number)
}

/// The cells of an evaluation (`measurements`) with the request's target, the bar (target / `bar`) and whether it is met.
fn cell_rows(request: &QueryRequest, evaluation: &Value, bar: u32) -> Vec<Value> {
    evaluation["measurements"].as_array().into_iter().flatten().map(|m| cell_row(request, &m["binding"], &m["workers"], &m["median_ns"], &m["status"], bar)).collect()
}

/// The cells of the closure's final measurement (`resolution.json` `final_measurement`: the served package of the
/// selected submission, each cell in a timing window of its own); empty when it was not recorded for that package.
fn final_cell_rows(request: &QueryRequest, resolution: &Value, qualification: &Value, bar: u32) -> Vec<Value> {
    let cells: Vec<&Value> = resolution["final_measurement"]["cells"].as_array().into_iter().flatten().collect();
    if cells.is_empty() || qualification["package"].is_null() || cells.iter().any(|c| c["gendb"]["package"] != qualification["package"]) {
        return vec![];
    }
    cells.into_iter().map(|c| cell_row(request, &c["binding"], &c["workers"], &c["gendb"]["median_ns"], &c["gendb"]["status"], bar)).collect()
}

fn cell_row(request: &QueryRequest, binding: &Value, workers: &Value, median: &Value, status: &Value, bar: u32) -> Value {
    let binding = binding.as_str().unwrap_or("statement");
    let workers = workers.as_u64().unwrap_or(0) as usize;
    let target = request.objective.runtime_targets().iter().find(|t| t.workers == workers && t.binding.as_deref().unwrap_or("statement") == binding).map(|t| t.median_ns);
    let median = median.as_u64();
    let speedup = match (target, median) {
        (Some(t), Some(m)) if m > 0 => Some(t as f64 / m as f64),
        _ => None,
    };
    json!({"binding":binding,"workers":workers,"median_ns":median,"status":status,"target_ns":target,
        "bar_ns":target.map(|t| t / bar as u64),"speedup":speedup.map(|s| (s * 100.0).round() / 100.0),
        "met":speedup.is_some_and(|s| s >= bar as f64)})
}

fn cell_table(cells: &[Value], bar: u32) -> String {
    let mut t = format!("| Binding | Workers | GenDB ms | Target ms | {bar}x bar ms | Speedup | Met | Result check |\n|---|---:|---:|---:|---:|---:|---|---|\n");
    for c in cells {
        let num = |k: &str| c[k].as_u64().map(ms).unwrap_or_else(|| "-".into());
        t.push_str(&format!(
            "| {} | {} | {} | {} | {} | {} | {} | {} |\n",
            c["binding"].as_str().unwrap_or(""),
            c["workers"],
            num("median_ns"),
            num("target_ns"),
            num("bar_ns"),
            c["speedup"].as_f64().map(|s| format!("{s:.2}x")).unwrap_or_else(|| "-".into()),
            if c["met"] == true { "yes" } else { "no" },
            c["status"].as_str().unwrap_or("-")
        ));
    }
    t
}

/// Per engine, the saved-answer verdicts over every compared call of the final measurement (empty when not recorded).
fn engine_verdicts(resolution: &Value) -> String {
    let mut engines: Vec<(String, u64, u64, u64, Vec<String>)> = vec![];
    let comparisons = resolution["final_measurement"]["cells"].as_array().into_iter().flatten().flat_map(|c| c["gendb"]["comparisons"].as_array().cloned().unwrap_or_default());
    for comparison in comparisons.filter_map(|c| c.as_str().and_then(|text| serde_json::from_str::<Value>(text).ok())) {
        for e in comparison["engines"].as_array().into_iter().flatten() {
            let name = e["engine"].as_str().unwrap_or("?").to_string();
            let index = engines.iter().position(|x| x.0 == name).unwrap_or_else(|| {
                engines.push((name, 0, 0, 0, vec![]));
                engines.len() - 1
            });
            let entry = &mut engines[index];
            if e["verdict"] == "agrees" {
                entry.1 += 1;
                entry.2 += u64::from(e["numeric_within_tolerance_only"] == true);
            } else {
                entry.3 += 1;
                if let Some(detail) = e["detail"].as_str().filter(|d| !entry.4.iter().any(|x| x == d)) {
                    entry.4.push(detail.to_string());
                }
            }
        }
    }
    if engines.is_empty() {
        return String::new();
    }
    let parts: Vec<String> = engines
        .iter()
        .map(|(name, agrees, tolerance, disagrees, details)| {
            let mut text = format!("{name} agrees in {agrees} of {} calls", agrees + disagrees);
            if *tolerance > 0 {
                text.push_str(&format!(" ({tolerance} only within the numeric tolerance)"));
            }
            if *disagrees > 0 {
                text.push_str(&format!(", disagrees in {disagrees} ({})", details.join("; ")));
            }
            text
        })
        .collect();
    format!("\nPer engine over the final measurement's compared calls: {}.\n", parts.join("; "))
}

fn parameter_table(request: &QueryRequest) -> String {
    if request.parameters.is_empty() {
        return "None: a concrete statement.\n".into();
    }
    let mut t = String::from("| Name | Placeholder | Type | Domain |\n|---|---|---|---|\n");
    for p in &request.parameters {
        let domain = match &p.binding {
            BindingRequest::Fixed(v) => format!("fixed `{v}`"),
            BindingRequest::Free { min: None, max: None } => "every value of the type".into(),
            BindingRequest::Free { min, max } => format!("[{}, {}]", min.as_deref().unwrap_or("type minimum"), max.as_deref().unwrap_or("type maximum")),
        };
        t.push_str(&format!("| {} | ${} | {} | {} |\n", p.name.as_deref().unwrap_or("-"), p.index, p.sql_type, domain));
    }
    t
}

fn attempt_status(a: &Attempt) -> String {
    let qualified = a.qualification["qualified"] == true || !a.qualification["admission"].is_null() && a.qualification["error"].is_null();
    let status = a.evaluation["status"].as_str().unwrap_or("not evaluated");
    let eligible = if a.evaluation["eligible"] == true { "eligible" } else { "not eligible" };
    let error = a.qualification["error"].as_str().map(|e| format!("; qualification error: {e}")).unwrap_or_default();
    let repaired = a.evaluation["repaired_by"].as_str().map(|r| format!("; re-evaluated by the framework repair `{r}`")).unwrap_or_default();
    format!("{status}, {eligible}{}{repaired}{error}", if qualified { ", qualified" } else { "" })
}

fn attempts_index(attempts: &[Attempt], selected: Option<u32>) -> String {
    let mut t = String::from("# Attempts\n\nOne folder per submission (a fresh author session each; at most 3).\n\n");
    for a in attempts {
        let mark = if Some(a.number) == selected { " (selected)" } else { "" };
        let incumbent = if is_incumbent(a) { " (the incumbent this session continued from; not an author submission)" } else { "" };
        t.push_str(&format!("- [attempt {0}]({0}/README.md){mark}{incumbent}: {1}\n", a.number, attempt_status(a)));
    }
    t
}

/// The incumbent of a continuing session (iteration 0 with its provenance record, `controller::layout::INCUMBENT_FILE`).
fn is_incumbent(a: &Attempt) -> bool {
    a.dir.join(crate::controller::layout::INCUMBENT_FILE).is_file()
}

fn write_attempt(dir: &Path, q: &QueryOutput<'_>, a: &Attempt, selected: Option<u32>, bar: u32) -> Result<(), OutputError> {
    let target = dir.join("attempts").join(a.number.to_string());
    let is_selected = Some(a.number) == selected;
    let mut text = format!("# {} attempt {}\n\nStatus: {}.\n\n", q.name, a.number, attempt_status(a));
    if is_selected {
        text.push_str("This is the selected submission: its code is [`../../code/`](../../code/).\n\n");
    } else if a.src().join("agent").exists() {
        copy_code(&a.src().join("agent"), &target.join("code"), None)?;
        text.push_str("Its author code is in [`code/`](code/).\n\n");
    }
    if is_incumbent(a) {
        let record = read_json(&a.dir.join(crate::controller::layout::INCUMBENT_FILE)).unwrap_or(Value::Null);
        text.push_str(&format!(
            "The incumbent: the package admitted by the earlier session `{}` (its submission {}), written into this session's workspace before the first author call, frozen with this run's framework and evaluated afresh here. It competed in selection like a submission but is not one; its provenance is `{}`.\n\n",
            record["source_session"].as_str().unwrap_or("-"),
            record["provenance"]["source_iteration"],
            a.dir.join(crate::controller::layout::INCUMBENT_FILE).display()
        ));
    }
    // A reselection's copy (`source.json`): the author's records stay in the closed source session.
    let source = read_json(&a.dir.join("source.json")).unwrap_or(Value::Null);
    let source_iteration = source["source_iteration"].as_str().map(PathBuf::from);
    if let (Some(session), Some(iteration)) = (source["source_session"].as_str(), &source_iteration) {
        text.push_str(&format!(
            "Recovered without an author (reselection) from the closed author session `{session}`: the same frozen sources, evaluated afresh, qualified and served here. The author's prompt, trajectory and receipt are in `{session}/calls/{:04}/` (`prompt.txt`, `stdout.jsonl`, `receipt.json`); the original evaluation is `{}` and its qualification `{}`.\n\n",
            source["source_call_id"].as_u64().unwrap_or(0),
            iteration.join("evaluation.json").display(),
            iteration.join("qualification.json").display()
        ));
    }
    let cells = cell_rows(q.request, &a.evaluation, bar);
    if !cells.is_empty() {
        text.push_str("## Official cells\n\n");
        if source_iteration.is_some() {
            text.push_str("The fresh evaluation of this copy:\n\n");
        }
        text.push_str(&cell_table(&cells, bar));
    }
    if let Some(iteration) = &source_iteration {
        let original = cell_rows(q.request, &read_json(&iteration.join("evaluation.json")).unwrap_or(Value::Null), bar);
        if !original.is_empty() {
            text.push_str("\nThe original evaluation of the author's submission (source session):\n\n");
            text.push_str(&cell_table(&original, bar));
        }
        if let Some(error) = read_json(&iteration.join("qualification.json")).and_then(|q| q["error"].as_str().map(String::from)) {
            text.push_str(&format!("\nIts qualification in the source session failed: {error}\n"));
        }
    }
    let notes_dirs = [Some(a.dir.clone()), Some(a.dir.join("frozen")), source_iteration.clone()];
    for notes in notes_dirs.into_iter().flatten().map(|d| d.join("NOTES.md")) {
        if let Ok(n) = std::fs::read_to_string(&notes) {
            write_text(&target.join("NOTES.md"), &n)?;
            text.push_str("\nThe author's notes for the next attempt: [`NOTES.md`](NOTES.md) (hints; GenDB's records are authoritative).\n");
            break;
        }
    }
    text.push_str(&format!("\nRaw records: `records/queries/{}/attempts/{}/`.\n", q.name, a.number));
    write_text(&target.join("README.md"), &text)
}

#[allow(clippy::too_many_arguments)]
fn query_readme(
    q: &QueryOutput<'_>,
    summary: &Value,
    resolution: &Value,
    selected: Option<&Attempt>,
    attempts: &[Attempt],
    cells: &[Value],
    timing: &str,
    bar: u32,
    storages: &[Value],
    added: &[String],
    framework: Option<&str>,
) -> String {
    let mut t = format!("# {}\n\nTemplate: [`query.sql`](query.sql). Emitted SQLSpec statement: [`spec.rs`](spec.rs).\n\n", q.name.to_uppercase());
    t.push_str("## Parameters\n\n");
    t.push_str(&parameter_table(q.request));
    t.push_str("\n## Result\n\n");
    match selected {
        Some(a) => {
            if timing == "final_measurement" {
                t.push_str(&format!(
                    "Selected: attempt {0} of {1}. Final measurement of the served package: each cell in an exclusive timing window of its own, the median of 3 hot calls after 1 warm call of one library call. The submission's own evaluation is in [attempt {0}](attempts/{0}/README.md).\n\n",
                    a.number,
                    attempts.len()
                ));
            } else {
                t.push_str(&format!("Selected: attempt {} of {}. Times are hot medians (1 warm + 3 hot) of one library call in the submission's evaluation.\n\n", a.number, attempts.len()));
            }
            t.push_str(&cell_table(cells, bar));
            let validation = if resolution["final_measurement"]["validation"].is_object() { &resolution["final_measurement"]["validation"] } else { &a.evaluation["real_data"]["validation"] };
            if validation["policy"] == "formal_proofs" {
                t.push_str(&format!(
                    "\nResult check (validation policy `formal_proofs`): each result is compared with the saved answers of other engines ({}) at its binding; text, integers and dates exactly, other numerics as decimals or within relative tolerance {}. `saved_answers_agree`: every engine agrees; `saved_answers_agree_partly`: at least one agrees and the others' differences are recorded in the raw records. This is integration evidence about the trusted base and environment, not part of the proof. No tiny-database tests or reference-engine runs were made.\n",
                    validation["required_engines"].as_array().into_iter().flatten().filter_map(Value::as_str).collect::<Vec<_>>().join(", "),
                    validation["numeric_relative_tolerance"].as_str().map(String::from).or_else(|| validation["numeric_relative_tolerance"].as_f64().map(|f| format!("{f:e}"))).unwrap_or_else(|| "-".into())
                ));
                t.push_str(&engine_verdicts(resolution));
            }
        }
        None => t.push_str(&format!("No submission was selected ({} attempts; see [attempts](attempts/README.md)).\n", attempts.len())),
    }
    let source = &summary["source_accounting"];
    if source.is_object() {
        let source_summary = source["summary"].as_str().and_then(|p| read_json(Path::new(p))).unwrap_or(Value::Null);
        t.push_str(&format!(
            "\nAuthor: the closed session `{}` ({} calls, {} submissions, author elapsed {} ms, provider-reported author cost ${}; receipts in its `calls/`), counted there once. Recovery: this session ({}, {}) selected that session's submission without an author and evaluated, qualified and served it afresh; it made no provider call.\n",
            source["session"].as_str().unwrap_or("?"),
            source["calls"],
            source["iterations"],
            source_summary["author_elapsed_ms"],
            source["reported_cost_usd"].as_str().unwrap_or("unknown"),
            summary["status"].as_str().unwrap_or("unknown"),
            summary["reason"].as_str().unwrap_or("")
        ));
    } else {
        t.push_str(&format!("\nSession: {} ({}). Provider-reported author cost: ${}.\n", summary["status"].as_str().unwrap_or("unknown"), summary["reason"].as_str().unwrap_or(""), summary["reported_cost_usd"].as_str().unwrap_or("unknown")));
    }
    t.push_str("\n## Storages read\n\n");
    if storages.is_empty() {
        t.push_str("None recorded.\n");
    }
    for s in storages {
        let name = s["name"].as_str().unwrap_or("?");
        let bytes = s["storage_bytes"].as_u64().map(|b| format!(", {} stored", super::byte_size(b))).unwrap_or_default();
        let origin = if added.iter().any(|a| a == name) { ", added by this query" } else { "" };
        let version = s["version"].as_u64().unwrap_or(0) as usize;
        let folder = storage_version_dir(name, version);
        t.push_str(&format!("- [{name} v{version}](../../workload/storage/{folder}/README.md) (package `{}`){bytes}{origin}\n", s["package"].as_str().unwrap_or("?")));
    }
    t.push_str("\n## Code and proof\n\n");
    t.push_str("- [`code/`](code/): the author code that was verified and admitted (authoritative); [`code-view/`](code-view/): the reading view.\n");
    if let Some(a) = selected {
        let entry = a.qualification["entry_identity"].as_str().unwrap_or("unknown");
        t.push_str(&format!(
            "- Verified by Verus (`--no-cheating`) as one crate with the fixed entry `{entry}`: total correctness relative to the entry's outcome contract, under the declared domains and the trusted base (the toolchain, SQLSpec as the meaning of SQL, the translator, the runtime and the entry's trusted assumptions, listed in the package's TCB record){}. Under the trusted assumptions every call terminates and returns rows allowed by the SQL meaning, exactly the statement's SQL error, `Capacity` (only outside the capacity domain: an intermediate of the canonical evaluation is not machine-representable), `ParamRefused` (exactly outside the parameter domain) or `Refused` (exactly for a worker count outside 1..=64); the fixed claim also permits `WorkerFailed` without a condition, which the trusted assumption `worker_failure` excludes. A process abort (allocation failure, stack exhaustion, failed thread creation, an unwind on the calling thread) ends a call with no outcome; the trusted assumption `calling_thread_progress` excludes it. The final theorem states what each outcome means (partial correctness); termination comes from Verus's termination checks. Performance is not proved.\n",
            if entry.ends_with("v5") { " and the declared integrity constraints (trusted as the user's declaration)" } else { "" }
        ));
        t.push_str(&format!("- Package `{}`, claim `{}`, build `{}` in the library.\n", a.qualification["package"].as_str().unwrap_or("-"), a.qualification["claim"].as_str().unwrap_or("-"), a.qualification["build"].as_str().unwrap_or("-")));
    }
    if let Some(f) = framework {
        t.push_str(&format!("- Framework files: kept once in the library, version manifest `{f}`. `gendb rebuild {}` assembles the full crate.\n", q.name));
    }
    t.push_str(&format!("\n[Attempts](attempts/README.md) · raw records: `records/queries/{}/`\n", q.name));
    t
}
