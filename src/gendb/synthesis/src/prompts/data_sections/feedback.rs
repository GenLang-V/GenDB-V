//! LATEST FEEDBACK: the latest call (in a fresh session, the previous session's last call), its local jobs and, once
//! evaluated, its submission: verdict, error, Verus result, storages, and one table row per measured run. Before the
//! first call of a session that continues from an incumbent, the incumbent's evaluation in the same form.

use super::format::{Align, fenced, ms, plain, seconds, size, table};
use super::{AuthorKind, DataViews};
use serde_json::Value;

/// An error longer than this many bytes is shown as its first and last lines (the full text is in the record).
const ERROR_SHOWN_BYTES: usize = 8 * 1024;
const ERROR_HEAD_LINES: usize = 150;
const ERROR_TAIL_LINES: usize = 50;

/// The LATEST FEEDBACK section.
pub fn latest_feedback(views: &DataViews) -> Vec<String> {
    let latest = views.latest;
    let mut lines = vec!["# LATEST FEEDBACK".to_string(), String::new()];
    if latest.is_null() {
        lines.push("No earlier call in this session.".to_string());
        return lines;
    }
    if latest["incumbent"] == true {
        lines.push("No earlier call in this session. The incumbent's evaluation, made before this call:".to_string());
        lines.push(String::new());
        lines.push(format!("## Incumbent: {}", plain(&latest["evaluation"]["status"])));
        lines.push(String::new());
        lines.push(verdict_line(&latest["evaluation"]).replacen("; counted: yes", "; not a submission", 1).replacen("; counted: no", "; not a submission", 1));
        lines.extend(submission_detail(&latest["evaluation"]));
        lines.extend([String::new(), "Older detail: the incumbent's records under the session's `iterations/0000/` and `full_context`.".to_string()]);
        return lines;
    }
    let session = if views.handoff.is_null() { "" } else { " (the previous session's last call)" };
    let call = latest["call"].as_u64().map_or_else(|| "the latest call".to_string(), |call| format!("call {call}"));
    let evaluation = &latest["evaluation"];
    lines.push(match evaluation.is_object() {
        true => format!("## Latest call: {call}{session}, ended with submission {}", plain(&latest["iteration"])),
        false => format!("## Latest call: {call}{session}, ended without a submission: {}", plain(&latest["author_outcome"])),
    });
    lines.push(String::new());
    lines.extend(local_jobs(latest, &call));
    if evaluation.is_object() {
        lines.push(String::new());
        lines.extend(submission(latest["iteration"].as_u64().unwrap_or_default(), evaluation, views.author));
    }
    lines.extend([
        String::new(),
        "Older detail: each submission's records under the session's `iterations/<NNNN>/`, each earlier call's `prompt.txt` and `local-jobs/` under `calls/<NNNN>/` (beside `this_prompt`), and `full_context`.".to_string(),
    ]);
    lines
}

/// The latest call's local jobs and the session's so far, with the last job's error verbatim.
fn local_jobs(latest: &Value, call: &str) -> Vec<String> {
    let of_call = &latest["local_jobs"];
    let counts = |summary: &Value| {
        let actions: Vec<String> = summary["by_action"].as_object().into_iter().flatten().map(|(action, n)| format!("{action} {n}")).collect();
        format!("{} ({}); {} refused", plain(&summary["jobs"]), actions.join(", "), plain(&summary["failed_jobs"]))
    };
    let session = &latest["session_local_jobs"];
    if !of_call.is_object() {
        let so_far = if session.is_object() { format!(" The session so far: {}.", counts(session)) } else { String::new() };
        return vec![format!("Local jobs of {call}: none.{so_far}")];
    }
    let last = &of_call["latest"];
    let class = last["failure_class"].as_str().map(|c| format!(", {c}")).unwrap_or_default();
    let mut lines = vec![format!(
        "Local jobs of {call}: {}. Last: job {} {} {}{class}. The session so far: {}.",
        counts(of_call),
        plain(&last["job_id"]),
        plain(&last["action"]),
        plain(&last["status"]),
        counts(session)
    )];
    if let Some(error) = last["error"].as_str() {
        lines.push(String::new());
        lines.extend(fenced("text", error));
    }
    lines
}

/// The evaluation of submission `iteration`. The general line leaves out the verdict line: its evaluation section states
/// the verdict, `eligible` there means accepted (an attempt that verified and was only slower would read "exact and
/// verified: no"), and nothing is counted against a submission limit.
fn submission(iteration: u64, evaluation: &Value, author: AuthorKind) -> Vec<String> {
    let mut lines = vec![format!("## Submission {iteration}: {}", plain(&evaluation["status"])), String::new()];
    if let Some(note) = evaluation["framework_failure"].as_str() {
        lines.push(format!("- **Framework failure**: {note}."));
    }
    if author != AuthorKind::GeneralEngine {
        lines.push(verdict_line(evaluation));
    }
    lines.extend(submission_detail(evaluation));
    lines
}

/// "Exact and verified" and "counted", with the score and an unchanged resubmission.
fn verdict_line(evaluation: &Value) -> String {
    let mut verdict = format!(
        "- Exact and verified: {}; counted: {}",
        if evaluation["eligible"] == true { "yes" } else { "no" },
        if evaluation["counted"] == false { "no" } else { "yes" }
    );
    if !evaluation["score_ns"].is_null() {
        verdict.push_str(&format!("; score {} ms", ms(&evaluation["score_ns"])));
    }
    if let Some(earlier) = evaluation["duplicate_of_iteration"].as_u64() {
        verdict.push_str(&format!("; unchanged from submission {earlier} (not measured again)"));
    }
    verdict + "."
}

/// The failure, the Verus result, the storages, the record and the measured runs of an evaluation.
fn submission_detail(evaluation: &Value) -> Vec<String> {
    let mut lines = vec![];
    if let Some(error) = evaluation["error"].as_str() {
        lines.push(format!("- Failure: {}:", plain(&evaluation["failure_class"])));
        lines.push(String::new());
        lines.extend(fenced("text", &shown_error(error, &evaluation["record"])));
        lines.push(String::new());
    }
    let verus = &evaluation["verus"];
    if verus.is_object() {
        lines.push(format!(
            "- Verus (whole crate, --no-cheating): {}; outcome {}; {}. Record: `{}`.",
            plain(&verus["detail"]),
            plain(&verus["outcome"]),
            seconds(&verus["wall_ns"]),
            plain(&verus["record"])
        ));
    } else if !evaluation["verus_record"].is_null() {
        lines.push(format!("- Verus record: `{}`.", plain(&evaluation["verus_record"])));
    }
    if !evaluation["boundary_cases"].is_null() {
        lines.push(format!("- Tiny boundary cases run: {}.", plain(&evaluation["boundary_cases"])));
    }
    let assets: Vec<String> = evaluation["storage"]["assets"].as_array().into_iter().flatten().map(storage_asset).collect();
    if !assets.is_empty() {
        lines.push(format!("- Storages ({}): {}.", if evaluation["storage"]["assets"][0]["canonical_column_bytes"].is_null() { "read" } else { "built" }, assets.join("; ")));
    }
    lines.push(format!("- Record: `{}` (`evaluation.json` holds every field in full).", plain(&evaluation["record"])));
    let runs = &evaluation["runs"];
    if runs["cells"].as_array().is_some_and(|cells| !cells.is_empty()) {
        lines.push(String::new());
        lines.extend(runs_table(runs));
    }
    lines
}

/// An evaluation error verbatim; one longer than [`ERROR_SHOWN_BYTES`] as its first and last lines.
fn shown_error(error: &str, record: &Value) -> String {
    let lines: Vec<&str> = error.lines().collect();
    if error.len() <= ERROR_SHOWN_BYTES || lines.len() <= ERROR_HEAD_LINES + ERROR_TAIL_LINES {
        return error.to_string();
    }
    let omitted = lines.len() - ERROR_HEAD_LINES - ERROR_TAIL_LINES;
    format!(
        "{}\n... ({omitted} lines omitted; the full text is `error` in {}/evaluation.json)\n{}",
        lines[..ERROR_HEAD_LINES].join("\n"),
        plain(record),
        lines[lines.len() - ERROR_TAIL_LINES..].join("\n")
    )
}

/// One storage an evaluation read or built: package prefix, admitted or new, size, canonical column bytes (built),
/// recorded one-time build and whether this evaluation paid it.
fn storage_asset(asset: &Value) -> String {
    let package = asset["package"].as_str().map(|p| format!("package {}", &p[..p.len().min(12)])).unwrap_or_default();
    let admitted = match asset["admitted"].as_bool() {
        Some(true) => ", admitted",
        Some(false) => ", new",
        None => "",
    };
    let canonical = if asset["canonical_column_bytes"].is_null() { String::new() } else { format!(", canonical columns {}", size(&asset["canonical_column_bytes"])) };
    let paid = match asset["asset_reused"].as_bool() {
        Some(true) => "reused",
        Some(false) => "built and paid in this evaluation",
        None => "-",
    };
    format!("{} ({package}{admitted}, {} stored{canonical}, one-time build {}, {paid})", plain(&asset["name"]), size(&asset["storage_bytes"]), seconds(&asset["build_wall_ns"]))
}

/// One row per measured run (admission binding x worker count), then each column's meaning and the result check's
/// meaning, tolerance and engines once.
fn runs_table(runs: &Value) -> Vec<String> {
    let cells = runs["cells"].as_array().cloned().unwrap_or_default();
    let with_reference_rows = cells.iter().any(|c| !c["reference_rows"].is_null());
    let mut header = vec![("Binding", Align::Left), ("Workers", Align::Right), ("Check", Align::Left)];
    if with_reference_rows {
        header.push(("Reference rows", Align::Right));
    }
    header.extend([
        ("Median ms", Align::Right),
        ("Wall ms (warm; hot)", Align::Left),
        ("Caller CPU ms", Align::Left),
        ("User ms", Align::Left),
        ("Sys ms", Align::Left),
        ("Device read B", Align::Left),
        ("Calling-thread share (permille)", Align::Right),
        ("Spawned/joined/ranges", Align::Left),
        ("Storage reads (requests / elements / bytes)", Align::Left),
    ]);
    let mut engines: Option<Value> = None;
    let rows: Vec<Vec<String>> = cells
        .iter()
        .map(|cell| {
            let comparison = comparison(&cell["comparison"]);
            if engines.is_none() && comparison["engines"].is_array() {
                engines = Some(comparison.clone());
            }
            let per_call = &cell["per_call"];
            let mut row = vec![plain(&cell["binding"]), plain(&cell["workers"]), check(&cell["status"], &comparison)];
            if with_reference_rows {
                row.push(plain(&cell["reference_rows"]));
            }
            let dispatch = &cell["dispatch"];
            row.extend([
                ms(&cell["median_hot_ns"]),
                calls_ms(&per_call["wall_ns"]),
                calls_ms(&per_call["caller_cpu_ns"]),
                calls_ms(&per_call["process_user_ns"]),
                calls_ms(&per_call["process_system_ns"]),
                device_reads(&per_call["device_read_bytes"]),
                plain(&cell["calling_thread_share_permille"]),
                format!("{}/{}/{}", plain(&dispatch["spawned"]), plain(&dispatch["joined"]), plain(&dispatch["ranges_reported"])),
                storage_reads(&cell["storage_requests"]),
            ]);
            row
        })
        .collect();
    let mut lines = table(&header, &rows);
    let meaning = &runs["meaning"];
    lines.push(String::new());
    lines.push(format!(
        "Per call: the warm call, then the hot calls; the median is the median hot wall time, and the score uses the medians of every benchmark binding at every worker count. Caller CPU is the calling thread's; user and sys are all threads of the child. Wall: {}. Device read: {}. Storage reads: {}. Dispatch: {}.",
        plain(&meaning["wall_ns"]),
        plain(&meaning["device_read_bytes"]),
        plain(&meaning["storage_requests"]),
        plain(&meaning["dispatch"])
    ));
    if let Some(engines) = engines {
        lines.push(String::new());
        let described: Vec<String> = engines["engines"].as_array().into_iter().flatten().map(|e| format!("{}: {}", plain(&e["engine"]), plain(&e["description"]))).collect();
        lines.push(format!(
            "Check: {}; numeric relative tolerance {}. Engines: {}. Each saved answer's path and order check: the record.",
            plain(&engines["meaning"]),
            plain(&engines["numeric_relative_tolerance"]),
            described.join("; ")
        ));
    }
    lines
}

/// A run's result comparison: the recorded JSON (a document or a JSON text), or its plain text as `{"text": ...}`.
fn comparison(recorded: &Value) -> Value {
    match recorded {
        Value::String(text) => serde_json::from_str::<Value>(text).ok().filter(Value::is_object).unwrap_or_else(|| serde_json::json!({"text":text})),
        other => other.clone(),
    }
}

/// The check column: the run's status, the agreeing engines and every other engine with its verdict.
fn check(status: &Value, comparison: &Value) -> String {
    let status = plain(status);
    if let Some(text) = comparison["text"].as_str() {
        return format!("{status} ({text})");
    }
    let engines = comparison["engines"].as_array().cloned().unwrap_or_default();
    if engines.is_empty() {
        return status;
    }
    let agreeing: Vec<String> = engines.iter().filter(|e| e["verdict"] == "agrees").map(|e| plain(&e["engine"])).collect();
    let others: Vec<String> = engines.iter().filter(|e| e["verdict"] != "agrees").map(|e| format!("{} {}", plain(&e["engine"]), plain(&e["verdict"]))).collect();
    let mut shown = agreeing.join(", ");
    if !others.is_empty() {
        shown = if shown.is_empty() { others.join(", ") } else { format!("{shown}; {}", others.join(", ")) };
    }
    format!("{status} ({shown})")
}

/// Per-call times: the warm call, then the hot calls.
fn calls_ms(values: &Value) -> String {
    let calls: Vec<String> = values.as_array().into_iter().flatten().map(ms).collect();
    match calls.split_first() {
        None => "-".to_string(),
        Some((warm, hot)) => format!("{warm}; {}", hot.join(" ")),
    }
}

/// Per-call device reads; one value with `(all)` when every call read the same.
fn device_reads(values: &Value) -> String {
    let reads: Vec<String> = values.as_array().into_iter().flatten().map(plain).collect();
    match reads.first() {
        None => "-".to_string(),
        Some(first) if reads.iter().all(|r| r == first) => format!("{first} (all)"),
        Some(_) => reads.join(" "),
    }
}

/// Each storage use's requests, requested elements and requested bytes.
fn storage_reads(uses: &Value) -> String {
    let shown: Vec<String> = uses.as_array().into_iter().flatten()
        .map(|u| format!("{}: {} / {} / {}", plain(&u["name"]), plain(&u["requests"]), plain(&u["elements"]), plain(&u["bytes"])))
        .collect();
    if shown.is_empty() { "-".to_string() } else { shown.join("; ") }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_long_error_keeps_its_first_and_last_lines_and_names_the_record() {
        let error: String = (0..400).map(|i| format!("line {i} {}\n", "x".repeat(40))).collect();
        let shown = shown_error(&error, &Value::String("/r/iterations/0002".into()));
        assert!(shown.starts_with("line 0 ") && shown.trim_end().ends_with(&format!("line 399 {}", "x".repeat(40))));
        assert!(shown.contains("(200 lines omitted; the full text is `error` in /r/iterations/0002/evaluation.json)") && !shown.contains("line 150 "));
        assert_eq!(shown_error("short", &Value::Null), "short");
    }
}
