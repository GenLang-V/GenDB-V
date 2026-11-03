//! The engine author's own data sections, rendered deterministically as Markdown from
//! the prepared context (`context.engine`, `context.round`; written by `engine::role`): no raw JSON, times in ms with 3
//! decimals.
//!
//! - [`engine_facts`], the head of CURRENT FACTS, leading with the totals gap per worker count:
//!   - Totals: per worker count the baselines' totals, the target (the faster one), the latest version's total, the
//!     gap and the margin, and the stop status;
//!   - Latest round: how the previous round ended (a new version, or the attempt's failure with its error);
//!   - Training set: per template the tables it reads, the saved Umbra and DuckDB medians and the latest version's
//!     official median at every worker count, and Umbra's share of its total;
//!   - Versions: every accepted version's totals, variant ratio summary and other-binding totals;
//!   - Variants: the kinds, how many are timed, and the latest ratio summary;
//!   - Rounds: one line per earlier round.
//! - [`rounds_handoff`], HANDOFF FROM EARLIER ROUNDS: where the versions and rounds are on disk, and the `NOTES.md`
//!   carried into this round, verbatim.
//!
//! The shared Storage, Integrity constraints and Host sections, the ledger and the latest feedback come from
//! `data_sections` (`render_engine`). Everything here is recorded data; nothing is a hint about a query.
//!
//! The general engine line's own data sections are in [`general`].

pub mod general;

use super::data_sections::format::{Align, dollars, fenced, ms, number, plain, table};
use serde_json::Value;

/// The engine's CURRENT FACTS head.
pub fn engine_facts(context: &Value) -> Vec<String> {
    let engine = &context["engine"];
    let latest = engine["versions"].as_array().and_then(|v| v.last()).cloned().unwrap_or(Value::Null);
    let blocks = [totals(engine, &latest), latest_round(context), training_set(engine, &latest), versions(engine), variants(engine, &latest), rounds(engine)];
    blocks.into_iter().filter(|b| !b.is_empty()).collect::<Vec<_>>().join(&String::new())
}

/// `a / b / c` of one value per worker count.
fn per_workers(values: impl IntoIterator<Item = String>) -> String {
    values.into_iter().collect::<Vec<_>>().join(" / ")
}

fn workers(engine: &Value) -> Vec<u64> {
    engine["training"]["workers"].as_array().into_iter().flatten().filter_map(Value::as_u64).collect()
}

/// The totals table: the leading section of the feedback.
fn totals(engine: &Value, latest: &Value) -> Vec<String> {
    let binding = plain(&engine["training"]["timing_binding"]);
    let count = engine["training"]["templates"].as_array().map_or(0, Vec::len);
    let mut lines = vec![
        format!("## Totals against the targets (binding {binding})"),
        String::new(),
        format!("Sum over the {count} training templates of each one's hot median, in ms. The goal: below both baselines' totals at every worker count."),
        String::new(),
    ];
    let version = plain(&latest["version"]);
    let rows: Vec<Vec<String>> = if latest.is_null() {
        engine["training"]["baseline_totals"]
            .as_array()
            .into_iter()
            .flatten()
            .filter(|t| t["binding"] == binding.as_str())
            .map(|t| vec![plain(&t["workers"]), ms(&t["umbra_ns"]), ms(&t["duckdb_ns"]), format!("{} ({})", ms(&t["target_ns"]), plain(&t["target_engine"]))])
            .collect()
    } else {
        latest["totals"]["workers"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|t| {
                let gap = number(&t["gap_ns"]).map_or("-".to_string(), |g| format!("{}{:.3}", if g > 0.0 { "+" } else { "" }, g / 1e6));
                let margin = number(&t["margin"]).map_or("-".to_string(), |m| format!("{m:.3}x"));
                vec![plain(&t["workers"]), ms(&t["umbra_ns"]), ms(&t["duckdb_ns"]), format!("{} ({})", ms(&t["target_ns"]), plain(&t["target_engine"])), ms(&t["engine_ns"]), gap,
                    margin, if t["below_both"] == true { "yes" } else { "no" }.to_string()]
            })
            .collect()
    };
    let mut header = vec![("Workers", Align::Right), ("Umbra", Align::Right), ("DuckDB", Align::Right), ("Target (faster)", Align::Right)];
    let engine_heading = format!("{version} total");
    if !latest.is_null() {
        header.extend([(engine_heading.as_str(), Align::Right), ("Gap to target", Align::Right), ("Margin", Align::Right), ("Below both", Align::Left)]);
    }
    lines.extend(table(&header, &rows));
    lines.push(String::new());
    lines.push(match latest.is_null() {
        true => "No version yet: the first accepted version gives the first totals.".to_string(),
        false if latest["totals"]["stop"]["stop"] == true => format!("Stop: met by {version} (margin reached {}).", margin_text(&latest["totals"]["stop"]["margin_reached"])),
        false => {
            let reasons: Vec<String> = latest["totals"]["stop"]["reasons"].as_array().into_iter().flatten().map(plain).collect();
            format!("Stop: not met by {version} ({}). Margin = target / total; above 1 is below the target.", reasons.join("; "))
        }
    });
    lines
}

fn margin_text(margin: &Value) -> String {
    number(margin).map_or("-".to_string(), |m| format!("{m:.3}x"))
}

/// How the previous round ended.
fn latest_round(context: &Value) -> Vec<String> {
    let number_now = plain(&context["round"]["number"]);
    let Some(previous) = context["engine"]["rounds"].as_array().and_then(|r| r.last()) else {
        return vec!["## Latest round".to_string(), String::new(), format!("This is round {number_now}: no earlier round.")];
    };
    let mut lines = vec!["## Latest round".to_string(), String::new()];
    let round = plain(&previous["round"]);
    match previous["outcome"].as_str() {
        Some("version") => {
            let version = context["engine"]["versions"].as_array().into_iter().flatten().find(|v| v["version"] == previous["version"]).cloned().unwrap_or(Value::Null);
            lines.push(format!(
                "Round {round} was accepted as {}: its official results are the latest above (version folder `{}`, its `README.md` first).",
                plain(&previous["version"]),
                plain(&version["directory"])
            ));
            if version["timing"]["status"].as_str().is_some_and(|status| status != "timed") {
                lines.push(String::new());
                lines.push(format!(
                    "Its official timing: {} ({} failed cells{}); a worker count with a failed cell has no total (`timing.json` in the folder).",
                    plain(&version["timing"]["status"]),
                    plain(&version["timing"]["failed_cells"]),
                    version["timing"]["error"].as_str().map_or(String::new(), |e| format!("; {e}"))
                ));
            }
        }
        _ => {
            lines.push(format!(
                "Round {round} ended without a new version: {} ({}). Its workspace stays at `{}`; record `{}`. This round starts from {}.",
                plain(&previous["status"]),
                plain(&previous["reason"]),
                plain(&previous["workspace"]),
                plain(&previous["evaluation_record"]),
                plain(&context["round"]["seed"]["description"])
            ));
            if let Some(error) = previous["error"].as_str() {
                lines.push(String::new());
                lines.push(format!("Failure ({}):", plain(&previous["failure_class"])));
                lines.push(String::new());
                lines.extend(fenced("text", &shown_error(error)));
            }
        }
    }
    lines
}

/// An error verbatim, or its first 150 and last 50 lines when longer than 8 KiB (the record holds it whole).
fn shown_error(error: &str) -> String {
    let lines: Vec<&str> = error.lines().collect();
    if error.len() <= 8 * 1024 || lines.len() <= 200 {
        return error.to_string();
    }
    format!("{}\n... ({} lines omitted; the full text is in the record)\n{}", lines[..150].join("\n"), lines.len() - 200, lines[lines.len() - 50..].join("\n"))
}

/// One row per template: tables read, the saved medians, the latest version's medians, Umbra's share.
fn training_set(engine: &Value, latest: &Value) -> Vec<String> {
    let training = &engine["training"];
    let binding = plain(&training["timing_binding"]);
    let counts = workers(engine);
    let counts_text = per_workers(counts.iter().map(u64::to_string));
    let version = plain(&latest["version"]);
    let baseline = |template: &Value, w: u64, field: &str| -> Value {
        template["baselines"].as_array().into_iter().flatten().find(|c| c["binding"] == binding.as_str() && c["workers"].as_u64() == Some(w)).map_or(Value::Null, |c| c[field].clone())
    };
    let umbra_total = |w: u64| -> Option<f64> {
        training["baseline_totals"].as_array().into_iter().flatten().find(|t| t["binding"] == binding.as_str() && t["workers"].as_u64() == Some(w)).and_then(|t| number(&t["umbra_ns"]))
    };
    let engine_median = |name: &str, w: u64| -> Value {
        latest["totals"]["templates"]
            .as_array()
            .into_iter()
            .flatten()
            .find(|r| r["template"] == name && r["workers"].as_u64() == Some(w))
            .map_or(Value::Null, |r| r["engine"]["median_ns"].clone())
    };
    let rows: Vec<Vec<String>> = training["templates"]
        .as_array()
        .into_iter()
        .flatten()
        .map(|t| {
            let name = plain(&t["name"]);
            let tables: Vec<String> = t["tables"].as_array().into_iter().flatten().map(plain).collect();
            let mut row = vec![name.clone(), tables.join(", ")];
            row.push(per_workers(counts.iter().map(|w| ms(&baseline(t, *w, "umbra_ns")))));
            row.push(per_workers(counts.iter().map(|w| ms(&baseline(t, *w, "duckdb_ns")))));
            if !latest.is_null() {
                row.push(per_workers(counts.iter().map(|w| ms(&engine_median(&name, *w)))));
            }
            row.push(per_workers(counts.iter().map(|w| match (number(&baseline(t, *w, "umbra_ns")), umbra_total(*w)) {
                (Some(cell), Some(total)) if total > 0.0 => format!("{:.1}", 100.0 * cell / total),
                _ => "-".to_string(),
            })));
            row
        })
        .collect();
    let umbra = format!("Umbra ms ({counts_text})");
    let duckdb = format!("DuckDB ms ({counts_text})");
    let ours = format!("{version} ms ({counts_text})");
    let share = format!("Umbra share % ({counts_text})");
    let mut header = vec![("Template", Align::Left), ("Reads", Align::Left), (umbra.as_str(), Align::Right), (duckdb.as_str(), Align::Right)];
    if !latest.is_null() {
        header.push((ours.as_str(), Align::Right));
    }
    header.push((share.as_str(), Align::Right));
    let mut lines = vec![
        format!("## Training set at binding {binding}"),
        String::new(),
        format!("Per template: the tables it reads; the saved hot medians of Umbra and DuckDB{} at {counts_text} workers; and Umbra's share of its own total (where the time is). SQL, parameters, every visible binding and the baselines at the other bindings: `files.templates`.",
            if latest.is_null() { String::new() } else { format!(" and {version}'s official medians") }),
        String::new(),
    ];
    lines.extend(table(&header, &rows));
    let qualified: Vec<String> = latest["totals"]["qualifications"].as_array().into_iter().flatten().map(|q| format!("{} ({}: {})", plain(&q["template"]), plain(&q["agreement"]), plain(&q["meaning"]))).collect();
    if !qualified.is_empty() {
        lines.push(String::new());
        lines.push(format!("Baseline qualifications: {}.", qualified.join("; ")));
    }
    lines
}

/// One line per accepted version.
fn versions(engine: &Value) -> Vec<String> {
    let list = engine["versions"].as_array().cloned().unwrap_or_default();
    let mut lines = vec!["## Versions".to_string(), String::new()];
    if list.is_empty() {
        lines.push("None yet.".to_string());
        return lines;
    }
    for v in &list {
        let totals: Vec<String> = v["totals"]["workers"].as_array().into_iter().flatten().map(|t| ms(&t["engine_ns"])).collect();
        let mut line = format!(
            "- {} (round {}, crate {}): totals {} ms; margin reached {}",
            plain(&v["version"]),
            plain(&v["round"]),
            plain(&v["crate_version"]),
            per_workers(totals),
            margin_text(&v["totals"]["stop"]["margin_reached"])
        );
        if let Some(summary) = v["variants"]["summary"].as_array().and_then(|s| s.first()) {
            line.push_str(&format!("; variants at {} workers: {}", plain(&summary["workers"]), ratio_summary(summary)));
        }
        for other in v["other_bindings"].as_array().into_iter().flatten() {
            let totals: Vec<String> = other["totals"]["workers"].as_array().into_iter().flatten().map(|t| ms(&t["engine_ns"])).collect();
            line.push_str(&format!("; {} totals {} ms", plain(&other["binding"]), per_workers(totals)));
        }
        line.push_str(&format!("; folder `{}`.", plain(&v["directory"])));
        lines.push(line);
    }
    lines
}

fn ratio_summary(summary: &Value) -> String {
    let largest = &summary["largest"];
    let largest = if largest.is_null() { String::new() } else { format!(", largest {:.2} ({})", number(&largest["ratio"]).unwrap_or(0.0), plain(&largest["variant"]["id"])) };
    let mean = number(&summary["geometric_mean"]).map_or("-".to_string(), |m| format!("{m:.2}"));
    format!("{} compared, geometric mean ratio {mean}{largest}", plain(&summary["compared"]))
}

/// The variants: kinds, counts and the latest ratio summary.
fn variants(engine: &Value, latest: &Value) -> Vec<String> {
    let v = &engine["training"]["variants"];
    let kinds: Vec<String> = v["kinds"].as_array().into_iter().flatten().map(plain).collect();
    let mut line = format!(
        "{} frozen variants of {} kinds ({}). {} have AST bytes of their own and are timed for every version at 64 workers (1 warm + 1 hot call); {} equal their template's or another variant's bytes and are not timed. Each must return its template's saved answers; the ratios to the template's official median are a report, never a bound.",
        plain(&v["frozen"]),
        kinds.len(),
        kinds.join(", "),
        plain(&v["timed"]),
        plain(&v["not_timed"])
    );
    if let Some(summary) = latest["variants"]["summary"].as_array().and_then(|s| s.first()) {
        line.push_str(&format!(" {}: {}; per variant: `{}`.", plain(&latest["version"]), ratio_summary(summary), plain(&latest["variants"]["report"])));
    }
    vec!["## Variants".to_string(), String::new(), line]
}

/// One line per earlier round.
fn rounds(engine: &Value) -> Vec<String> {
    let list = engine["rounds"].as_array().cloned().unwrap_or_default();
    if list.is_empty() {
        return vec![];
    }
    let mut lines = vec!["## Rounds".to_string(), String::new()];
    for r in &list {
        let outcome = match r["outcome"].as_str() {
            Some("version") => format!("accepted as {}", plain(&r["version"])),
            _ => format!("no version: {}", plain(&r["status"])),
        };
        lines.push(format!(
            "- Round {}: {outcome}; seeded from {}; provider-reported cost {}; session `{}`.",
            plain(&r["round"]),
            plain(&r["seed"]),
            dollars(&r["reported_cost_usd"]),
            plain(&r["directory"])
        ));
    }
    lines
}

/// HANDOFF FROM EARLIER ROUNDS: where versions and rounds are, and the carried notes verbatim. Empty in round 1 of a
/// run without notes.
pub fn rounds_handoff(context: &Value) -> Vec<String> {
    let round = &context["round"];
    let notes = &round["notes"];
    let earlier = context["engine"]["rounds"].as_array().is_some_and(|r| !r.is_empty());
    if !earlier && notes["text"].is_null() {
        return vec![];
    }
    let mut lines = vec![
        "# HANDOFF FROM EARLIER ROUNDS".to_string(),
        String::new(),
        format!(
            "You are a fresh session of round {}. GenDB's facts above are authoritative; the notes are hints. This round's workspace was seeded from {}.",
            plain(&round["number"]),
            plain(&round["seed"]["description"])
        ),
        String::new(),
        format!("- Versions: `{}/vNNN/` (code, admission record, cells, totals, variant ratios, notes); read-only copies of their sources are under `files.versions`.", plain(&context["files"]["versions_records"])),
        format!("- Earlier rounds: `{}/round-NNNN/` (each round's calls with their prompts and local jobs, its submission and evaluation, and its workspace `author/`).", plain(&context["files"]["rounds"])),
        String::new(),
        "## Notes carried into this round".to_string(),
        String::new(),
    ];
    match notes["text"].as_str() {
        Some(text) => {
            lines.push(format!("The workspace `NOTES.md` (`files.notes`) as this round started, written in {}:", plain(&notes["from"])));
            lines.push(String::new());
            lines.extend(fenced("markdown", text));
        }
        None => lines.push("(no NOTES.md was written)".to_string()),
    }
    lines
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    fn context(versions: Value, rounds: Value) -> Value {
        json!({"round":{"number":3,"seed":{"description":"v1"},"notes":{"text":"# Notes\nplan","from":"v1 (round 1)"}},
            "files":{"versions_records":"/run/engine/versions","rounds":"/run/engine/rounds"},
            "engine":{"training":{"timing_binding":"v0","workers":[1,32],
                "templates":[{"name":"Q01","tables":["lineitem"],"baselines":[{"binding":"v0","workers":1,"umbra_ns":1_000_000,"duckdb_ns":2_000_000},{"binding":"v0","workers":32,"umbra_ns":500_000,"duckdb_ns":400_000}]}],
                "baseline_totals":[{"binding":"v0","workers":1,"umbra_ns":1_000_000,"duckdb_ns":2_000_000,"target_ns":1_000_000,"target_engine":"umbra"},
                    {"binding":"v0","workers":32,"umbra_ns":500_000,"duckdb_ns":400_000,"target_ns":400_000,"target_engine":"duckdb"}],
                "variants":{"kinds":["commuted_comparisons"],"frozen":2,"timed":1,"not_timed":1}},
                "versions":versions,"rounds":rounds}})
    }

    /// Without a version the totals show the baselines only; the facts never print JSON.
    #[test]
    fn round_one_facts_show_the_baseline_totals_and_no_version() {
        let lines = engine_facts(&context(json!([]), json!([])));
        let text = lines.join("\n");
        assert!(text.starts_with("## Totals against the targets (binding v0)"), "{text}");
        assert!(text.contains("| 1 | 1.000 | 2.000 | 1.000 (umbra) |") && text.contains("| 32 | 0.500 | 0.400 | 0.400 (duckdb) |"), "{text}");
        assert!(text.contains("No version yet") && text.contains("This is round 3: no earlier round.") && text.contains("| Q01 | lineitem | 1.000 / 0.500 | 2.000 / 0.400 | 100.0 / 100.0 |"), "{text}");
        assert!(!text.contains('{'), "no raw JSON: {text}");
    }

    /// With a version the totals lead with its gap and margin; a failed later round shows its error and seed.
    #[test]
    fn later_round_facts_lead_with_the_gap_and_show_the_failed_round() {
        let totals = json!({"workers":[{"workers":1,"engine_ns":2_000_000,"umbra_ns":1_000_000,"duckdb_ns":2_000_000,"target_ns":1_000_000,"target_engine":"umbra","gap_ns":1_000_000,"margin":0.5,"below_both":false}],
            "templates":[{"template":"Q01","workers":1,"engine":{"median_ns":2_000_000,"checked":true}}],"stop":{"stop":false,"margin_reached":0.5,"reasons":["1 workers: engine total 2000000 ns is not below Umbra's 1000000 ns"]}});
        let versions = json!([{"version":"v1","round":1,"crate_version":"abc","directory":"/run/engine/versions/v001","totals":totals,
            "variants":{"summary":[{"workers":64,"compared":1,"geometric_mean":1.5,"largest":{"ratio":1.5,"variant":{"id":"Q01-commuted_comparisons"}}}],"report":"/v/variants.md"}}]);
        let rounds = json!([{"round":1,"outcome":"version","version":"v1","seed":"empty","reported_cost_usd":"1.5","directory":"/r1"},
            {"round":2,"outcome":"attempt","status":"proof_failure","reason":"iteration_limit","error":"Verus: postcondition not satisfied","failure_class":"proof_failure","workspace":"/r2/author","evaluation_record":"/r2/e.json","seed":"v1","reported_cost_usd":"2","directory":"/r2"}]);
        let text = engine_facts(&context(versions, rounds)).join("\n");
        assert!(text.contains("| 1 | 1.000 | 2.000 | 1.000 (umbra) | 2.000 | +1.000 | 0.500x | no |"), "{text}");
        assert!(text.contains("Round 2 ended without a new version: proof_failure") && text.contains("postcondition not satisfied") && text.contains("This round starts from v1"), "{text}");
        assert!(text.contains("- v1 (round 1, crate abc): totals 2.000 ms; margin reached 0.500x; variants at 64 workers: 1 compared, geometric mean ratio 1.50, largest 1.50 (Q01-commuted_comparisons)"), "{text}");
        let handoff = rounds_handoff(&context(json!([]), json!([{"round":1}]))).join("\n");
        assert!(handoff.contains("# HANDOFF FROM EARLIER ROUNDS") && handoff.contains("# Notes\nplan") && handoff.contains("written in v1 (round 1)"), "{handoff}");
    }

    /// An accepted round points at its version folder; a version whose official timing had a failed cell says so, and
    /// the worker count without a total shows no engine total.
    #[test]
    fn an_accepted_round_with_a_failed_timing_cell_says_so() {
        let totals = json!({"workers":[{"workers":1,"engine_ns":null,"umbra_ns":1_000_000,"duckdb_ns":2_000_000,"target_ns":1_000_000,"target_engine":"umbra","gap_ns":null,"margin":null,"below_both":false,"missing_templates":["Q01"]}],
            "templates":[],"stop":{"stop":false,"margin_reached":null,"reasons":["1 workers: no engine total (missing Q01)"]}});
        let versions = json!([{"version":"v1","round":1,"crate_version":"abc","directory":"/run/engine/versions/v001","totals":totals,
            "timing":{"status":"timed_with_failed_cells","failed_cells":1}}]);
        let rounds = json!([{"round":1,"outcome":"version","version":"v1","seed":"empty","reported_cost_usd":"1.5","directory":"/r1"}]);
        let text = engine_facts(&context(versions, rounds)).join("\n");
        assert!(text.contains("Round 1 was accepted as v1") && text.contains("`/run/engine/versions/v001`"), "{text}");
        assert!(text.contains("Its official timing: timed_with_failed_cells (1 failed cells)"), "{text}");
        assert!(!text.contains('{'), "no raw JSON: {text}");
    }
}
