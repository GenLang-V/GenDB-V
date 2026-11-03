//! HANDOFF FROM EARLIER ATTEMPTS (a fresh session: where every record is, the author's notes verbatim, the log of
//! local trials and profiles) and LEDGER (submissions, cost guard and spend, earlier calls without a candidate).

use super::format::{Align, dollars, fenced, ms, number, plain, table};
use super::{AuthorKind, DataViews};
use gendb_verification::admission::validation::checked_cell_status;
use serde_json::{Value, json};

/// The HANDOFF FROM EARLIER ATTEMPTS section.
pub fn handoff(views: &DataViews) -> Vec<String> {
    let handoff = views.handoff;
    let paths = &handoff["paths"];
    let frozen = match views.author {
        AuthorKind::Query => "`frozen/crate/` (the submitted crate), `frozen/manifest.json`",
        AuthorKind::WorkloadStorage => "`frozen/storages/<name>/` (each submitted storage crate), `frozen/submission.json`",
        AuthorKind::Engine | AuthorKind::GeneralEngine => "`frozen/crate/` (the submitted engine crate), `frozen/manifest.json`",
    };
    let mut lines = vec![
        "# HANDOFF FROM EARLIER ATTEMPTS".to_string(),
        String::new(),
        "You are a fresh session. GenDB's facts are authoritative; the earlier author's notes are hints. Your code from earlier attempts is in the workspace, and every earlier file stays on disk: read what you need on demand. The official result of every submission is in CURRENT FACTS.".to_string(),
        String::new(),
        format!("- Submission records: `{}/<NNNN>/`: `evaluation.json` (the full evaluation), {frozen}, `NOTES.md` (your notes as they were at that submission).", plain(&paths["submission_records"])),
        format!("- Earlier calls: `{}/<NNNN>/`: `prompt.txt` (that call's prompt), `local-jobs/<job>/result.json` (each local job's full result).", plain(&paths["earlier_prompts"])),
        String::new(),
        "## Notes of the earlier attempt".to_string(),
        String::new(),
        "The workspace `NOTES.md` (`files.notes`) as this session started, written by the earlier author:".to_string(),
        String::new(),
    ];
    match handoff["notes"]["text"].as_str() {
        Some(text) => lines.extend(fenced("markdown", text)),
        None => lines.push("(no NOTES.md was written)".to_string()),
    }
    lines.extend([String::new(), "## Local trials and profiles".to_string(), String::new()]);
    let trials = handoff["local_trials"].as_array().cloned().unwrap_or_default();
    if trials.is_empty() {
        lines.push("None.".to_string());
    } else {
        let matrix: Vec<(String, u64)> = views.targets["cells"].as_array().into_iter().flatten()
            .map(|c| (plain(&c["binding"]), c["workers"].as_u64().unwrap_or_default())).collect();
        let score = if matrix.is_empty() { "" } else { " Score: the geometric mean over the whole benchmark matrix, as the official score, when the row has a checked median in every cell." };
        lines.push(format!(
            "Hot medians in ms per benchmark cell (binding/workers). V = verified, U = unverified (`verification: not_run`); a median marked `!` did not pass its result check (the status is in the record). Crate: the short identity of the exact crate content, as in the submission lines.{score} Record: `{}/<call>/local-jobs/<job>/result.json`.",
            plain(&paths["earlier_prompts"])
        ));
        lines.push(String::new());
        lines.extend(trial_table(&trials, &matrix));
    }
    lines
}

/// One row per local trial or profile, in record order. With a single statement (a query author) every benchmark
/// cell is a column, and a row measured at every cell of the benchmark `matrix` gets its score; with several
/// statements (the workload storage author's diagnostic queries) each row lists its own cells.
fn trial_table(trials: &[Value], matrix: &[(String, u64)]) -> Vec<String> {
    let per_statement = trials.iter().any(|t| !t["statement"].is_null());
    let status = |t: &Value| match t["failure_class"].as_str() {
        Some(class) => format!("{} ({class})", plain(&t["status"])),
        None => plain(&t["status"]),
    };
    let median = |c: &Value| format!("{}{}", ms(&c["median_hot_ns"]), if checked_cell_status(&c["status"]) { "" } else { "!" });
    let cell_name = |c: &Value| format!("{}/{}", plain(&c["binding"]), plain(&c["workers"]));
    let leading = |t: &Value| {
        let mut row = vec![plain(&t["call"]), plain(&t["job"])];
        if per_statement {
            row.push(plain(&t["statement"]));
        }
        row.extend([plain(&t["action"]), if t["verified"] == true { "V" } else { "U" }.to_string(), status(t), plain(&t["crate_version"])]);
        row
    };
    let mut header = vec![("Call", Align::Left), ("Job", Align::Left)];
    if per_statement {
        header.push(("Statement", Align::Right));
    }
    header.extend([("Action", Align::Left), ("V/U", Align::Left), ("Status", Align::Left), ("Crate", Align::Left)]);
    if per_statement {
        header.push(("Cells (binding/workers: ms)", Align::Left));
        let rows: Vec<Vec<String>> = trials
            .iter()
            .map(|t| {
                let cells: Vec<String> = t["cells"].as_array().into_iter().flatten().map(|c| format!("{}: {}", cell_name(c), median(c))).collect();
                let mut row = leading(t);
                row.push(cells.join("; "));
                row
            })
            .collect();
        return table(&header, &rows);
    }
    let mut columns: Vec<(String, u64)> = vec![];
    for cell in trials.iter().flat_map(|t| t["cells"].as_array().cloned().unwrap_or_default()) {
        let key = (plain(&cell["binding"]), cell["workers"].as_u64().unwrap_or_default());
        if !columns.contains(&key) {
            columns.push(key);
        }
    }
    columns.sort();
    let headings: Vec<String> = columns.iter().map(|(binding, workers)| format!("{binding}/{workers}")).collect();
    header.extend(headings.iter().map(|h| (h.as_str(), Align::Right)));
    if !matrix.is_empty() {
        header.push(("Score ms", Align::Right));
    }
    let cell_of = |t: &Value, binding: &str, workers: u64| -> Option<Value> {
        t["cells"].as_array().into_iter().flatten().find(|c| plain(&c["binding"]) == binding && c["workers"].as_u64() == Some(workers)).cloned()
    };
    let rows: Vec<Vec<String>> = trials
        .iter()
        .map(|t| {
            let mut row = leading(t);
            for (binding, workers) in &columns {
                row.push(cell_of(t, binding, *workers).as_ref().map_or_else(String::new, median));
            }
            if !matrix.is_empty() {
                let checked: Option<Vec<f64>> = matrix.iter()
                    .map(|(binding, workers)| cell_of(t, binding, *workers).filter(|c| checked_cell_status(&c["status"])).and_then(|c| number(&c["median_hot_ns"])))
                    .collect();
                row.push(checked.map_or_else(String::new, |medians| ms(&json!(geometric_mean(&medians)))));
            }
            row
        })
        .collect();
    table(&header, &rows)
}

/// The geometric mean of positive values (the official score's mean over the benchmark matrix).
fn geometric_mean(values: &[f64]) -> f64 {
    (values.iter().map(|v| v.ln()).sum::<f64>() / values.len() as f64).exp()
}

/// The LEDGER section.
pub fn ledger(ledger: &Value) -> Vec<String> {
    let mut lines = vec!["# LEDGER".to_string(), String::new()];
    let submissions = &ledger["submissions"];
    if submissions.is_object() {
        let uncounted: Vec<String> = submissions["not_counted_framework_failures"].as_array().into_iter().flatten().map(plain).collect();
        lines.push(format!(
            "- Submissions: {} used of {}; {} left including this call; framework failures not counted: {}.",
            plain(&submissions["used"]),
            plain(&submissions["limit"]),
            plain(&submissions["remaining_including_this_call"]),
            if uncounted.is_empty() { "none".to_string() } else { uncounted.join(", ") }
        ));
    }
    if !ledger["spent_usd"].is_null() {
        let guard = if ledger["max_cost_usd"] == "unset" {
            "none".to_string()
        } else {
            format!("{} (left {})", dollars(&ledger["max_cost_usd"]), dollars(&ledger["remaining_usd"]))
        };
        let complete = if ledger["spent_complete"] == false { " (incomplete: a receipt had no cost)" } else { "" };
        let calls = ledger["earlier_calls"].as_u64().unwrap_or_default();
        lines.push(format!(
            "- Cost guard: {guard}. Provider-reported cost of the {calls} earlier calls of this session: {}{complete}. Every call's receipt: `{}` (`calls[]`).",
            dollars(&ledger["spent_usd"]),
            plain(&ledger["file"])
        ));
    }
    for run in ledger["runs_without_candidate"].as_array().into_iter().flatten() {
        let range = if run["first_call"] == run["last_call"] {
            format!("Call {}", plain(&run["first_call"]))
        } else {
            format!("Calls {}-{} ({} calls)", plain(&run["first_call"]), plain(&run["last_call"]), plain(&run["calls"]))
        };
        let last = if run["calls"].as_u64().unwrap_or(1) > 1 { "; the last" } else { "" };
        lines.push(format!("- {range} of iteration {} ended without a candidate{last}: {}.", plain(&run["iteration"]), plain(&run["last_outcome"]).lines().next().unwrap_or_default()));
    }
    let this_call = &ledger["this_call"];
    if this_call.is_object() {
        lines.push(format!("- This call: call {} (iteration {}, attempt {}).", plain(&this_call["call"]), plain(&this_call["iteration"]), plain(&this_call["attempt"])));
    }
    lines
}
