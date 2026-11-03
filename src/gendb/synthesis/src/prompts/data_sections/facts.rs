//! CURRENT FACTS AND PATHS: what is being solved (a query author's own statement, or every workload statement for the
//! storage author), the official results so far, the storage situation, the declared integrity constraints and the
//! host. Paths are the Key paths at the top of the prompt (`files.<name>`), so they are not repeated here.

use super::format::{Align, cpu_list, fenced, ms, plain, size, table};
use super::{AuthorKind, DataViews};
use crate::prompts::policy::Objective;
use serde_json::Value;
use std::collections::BTreeMap;

/// The CPU flags the host line names (vector, bit-manipulation and crypto instructions); the full list is in a file.
const NAMED_CPU_FLAGS: [&str; 19] =
    ["sse4_1", "sse4_2", "ssse3", "avx", "avx2", "fma", "f16c", "bmi1", "bmi2", "popcnt", "abm", "lzcnt", "movbe", "adx", "aes", "pclmulqdq", "sha_ni", "vaes", "vpclmulqdq"];

/// The CURRENT FACTS AND PATHS section.
pub fn current_facts(views: &DataViews) -> Vec<String> {
    let context = views.context;
    let mut lines = vec![
        "# CURRENT FACTS AND PATHS".to_string(),
        String::new(),
        "Paths are the Key paths at the top (`files.<name>` in the instructions). The full prepared context is `full_context`.".to_string(),
    ];
    let mut add = |section: Vec<String>| {
        if !section.is_empty() {
            lines.push(String::new());
            lines.extend(section);
        }
    };
    match views.author {
        AuthorKind::Query => {
            add(query(context));
            add(incumbent(views));
            add(query_results(views));
        }
        AuthorKind::WorkloadStorage => {
            add(statements(context, views.targets));
            add(submission_list(views, "## Official results"));
        }
        AuthorKind::Engine | AuthorKind::GeneralEngine => {}
    }
    add(storage(context));
    add(integrity_constraints(context));
    add(host(views));
    lines
}

/// The CURRENT FACTS AND PATHS section of an engine author: the engine's own facts (`engine_facts`, rendered by
/// `prompts::engine_facts`), then the shared Storage, Integrity constraints and Host sections.
pub fn engine_current_facts(views: &DataViews, engine_facts: &[String]) -> Vec<String> {
    let mut lines = current_facts(views);
    // The shared sections follow the three header lines of `current_facts`.
    let shared = lines.split_off(3);
    if !engine_facts.is_empty() {
        lines.push(String::new());
        lines.extend(engine_facts.iter().cloned());
    }
    lines.extend(shared);
    lines
}

/// The CURRENT FACTS AND PATHS section of the general engine line: the line's own facts (`general_facts`, rendered by
/// `prompts::engine_facts::general`, which also state the storage and the disk), then its compact Integrity constraints
/// and Host sections. The key paths at the top of its prompt say what `files.<name>` names, so no line repeats it here.
pub fn general_current_facts(views: &DataViews, general_facts: &[String]) -> Vec<String> {
    let mut lines = vec!["# CURRENT FACTS AND PATHS".to_string()];
    for section in [general_facts.to_vec(), general_integrity_constraints(views.context), general_host(views.context)] {
        if !section.is_empty() {
            lines.push(String::new());
            lines.extend(section);
        }
    }
    lines
}

/// The declared integrity constraints of the general line: what they mean for the engine and their trust in one
/// sentence, the contract file, and one line per table.
fn general_integrity_constraints(context: &Value) -> Vec<String> {
    let constraints = &context["integrity_constraints"];
    let declarations = constraints["declarations"].as_array().cloned().unwrap_or_default();
    if declarations.is_empty() {
        return vec![];
    }
    let mut sentence = String::new();
    if let Some(in_words) = constraints["in_words"].as_str() {
        let mut letters = in_words.chars();
        sentence.push_str(&letters.next().map(|first| first.to_uppercase().chain(letters).collect::<String>()).unwrap_or_default());
        sentence.push_str(". ");
    }
    let file = constraints["details"].as_str().and_then(|p| std::path::Path::new(p).file_name()).map(|f| f.to_string_lossy().into_owned());
    sentence.push_str(&format!("Trust: {}. Details: contract `{}`.", plain(&constraints["trust"]), file.unwrap_or_else(|| plain(&constraints["details"]))));
    let mut tables: Vec<(String, Vec<String>)> = vec![];
    for declaration in &declarations {
        let table = plain(&declaration["table"]);
        match tables.iter_mut().find(|(name, _)| *name == table) {
            Some((_, sqls)) => sqls.push(plain(&declaration["sql"])),
            None => tables.push((table, vec![plain(&declaration["sql"])])),
        }
    }
    let mut lines = vec!["## Integrity constraints".to_string(), String::new(), sentence, String::new()];
    lines.extend(tables.into_iter().map(|(table, sqls)| format!("- {table}: {}", sqls.join("; "))));
    lines
}

/// The host of the general line as observed once at preparation, compact: the worker counts, CPU and NUMA in one line,
/// the caches grouped by how many logical CPUs share each, memory, the named CPU flags and the crash-dump setting.
/// The timing protocol is in the instructions (The loop), so it is not repeated here.
fn general_host(context: &Value) -> Vec<String> {
    let observed = &context["observed_hardware"];
    let workers: Vec<String> = context["hardware"]["threads"].as_array().into_iter().flatten().map(plain).collect();
    if workers.is_empty() && !observed.is_object() {
        return vec![];
    }
    let mut lines = vec!["## Host".to_string(), String::new()];
    let counts = if workers.is_empty() { String::new() } else { format!("; worker counts {}", workers.join(", ")) };
    lines.push(format!("Observed once at preparation{counts}."));
    if !observed.is_object() {
        return lines;
    }
    let numa: Vec<String> = observed["numa_nodes"].as_array().into_iter().flatten()
        .map(|n| {
            let node = plain(&n["node"]);
            let node = if node.starts_with("node") { node } else { format!("node{node}") };
            format!("{node} CPUs {} (distances {})", cpu_list(n["cpu_list"].as_str().unwrap_or_default()), plain(&n["distance"]))
        })
        .collect();
    let numa_nodes = observed["numa_nodes"].as_array().map_or(0, Vec::len);
    let memory_nodes = observed["allowed_memory_nodes"].as_str().unwrap_or_default();
    let memory_note = if memory_nodes.is_empty() || memory_nodes == format!("0-{}", numa_nodes.saturating_sub(1)) || numa_nodes <= 1 { String::new() } else { format!("; allowed memory nodes {memory_nodes}") };
    lines.push(format!(
        "- CPU: {}; {} packages, {} physical cores, {} logical CPUs in affinity ({}){memory_note}{}.",
        plain(&observed["cpu_model"]),
        plain(&observed["packages_in_affinity"]),
        plain(&observed["physical_cores_in_affinity"]),
        plain(&observed["logical_cpus_in_affinity"]),
        plain(&observed["affinity_cpu_list"]),
        if numa.is_empty() { String::new() } else { format!("; NUMA {}", numa.join(", ")) }
    ));
    let caches = observed["caches"].as_array().cloned().unwrap_or_default();
    if !caches.is_empty() {
        let same_lines = caches.windows(2).all(|pair| pair[0]["line_bytes"] == pair[1]["line_bytes"]);
        let mut groups: Vec<(String, Vec<String>)> = vec![];
        for c in &caches {
            let line = if same_lines { String::new() } else { format!(", {} B lines", plain(&c["line_bytes"])) };
            let entry = format!("L{} {} {} x{}", plain(&c["level"]), plain(&c["type"]), plain(&c["size_per_instance"]), plain(&c["instances_visible_to_affinity"]));
            let shared = format!("each shared by {} logical CPUs{line}", plain(&c["logical_cpus_sharing_each_instance"]));
            match groups.last_mut().filter(|(s, _)| *s == shared) {
                Some((_, entries)) => entries.push(entry),
                None => groups.push((shared, vec![entry])),
            }
        }
        let grouped: Vec<String> = groups.into_iter().map(|(shared, entries)| format!("{} ({shared})", entries.join(", "))).collect();
        let line = if same_lines { format!("; {} B lines", plain(&caches[0]["line_bytes"])) } else { String::new() };
        lines.push(format!("- Caches: {}{line}.", grouped.join(", ")));
    }
    let memory = &observed["host_memory_bytes"];
    if memory.is_object() {
        lines.push(format!("- Memory: {} total, {} available when observed ({}); swap free {}.", size(&memory["total"]), size(&memory["available"]), plain(&observed["memory_scope"]), size(&memory["swap_free"])));
    }
    if let Some(features) = observed["cpu_features"].as_str() {
        let named: Vec<&str> = features.split_whitespace().filter(|flag| NAMED_CPU_FLAGS.contains(flag) || flag.starts_with("avx512") || flag.starts_with("amx")).collect();
        lines.push(format!("- Vector, bit and crypto instructions: {} (every flag: `files.data` `hardware.observed.cpu_features`).", named.join(" ")));
    }
    let dumps = &observed["crash_dumps"];
    if dumps.is_object() {
        let error = dumps["containment_error"].as_str().map(|e| format!(", containment error: {e}")).unwrap_or_default();
        lines.push(format!("- Crash dumps: coredump_filter {}, contained {}{error}.", plain(&dumps["coredump_filter"]), plain(&dumps["contained"])));
    } else if !dumps.is_null() {
        lines.push(format!("- Crash dumps: {}.", plain(dumps)));
    }
    lines
}

/// The query author's statement: SQL, parameters and benchmark bindings.
fn query(context: &Value) -> Vec<String> {
    let mut lines = vec!["## Query".to_string(), String::new()];
    lines.extend(fenced("sql", context["sql"].as_str().unwrap_or_default()));
    let parameters = parameters(&context["parameters"]);
    if !parameters.is_empty() {
        lines.push(String::new());
        lines.extend(parameters);
    }
    let bindings = context["objective"]["bindings"].as_array().cloned().unwrap_or_default();
    if !bindings.is_empty() {
        lines.extend([String::new(), "Benchmark bindings (samples of the parameter domain, not the proof domain):".to_string(), String::new()]);
        // `origin` is shown only when some binding is not a user benchmark binding.
        let with_origin = bindings.iter().any(|b| !b["origin"].is_null() && b["origin"] != "benchmark");
        let mut header = vec![("Binding", Align::Left), ("Arguments", Align::Left)];
        if with_origin {
            header.push(("Origin", Align::Left));
        }
        let rows: Vec<Vec<String>> = bindings
            .iter()
            .map(|b| {
                let mut row = vec![plain(&b["name"]), arguments(&b["arguments"])];
                if with_origin {
                    row.push(plain(&b["origin"]));
                }
                row
            })
            .collect();
        lines.extend(table(&header, &rows));
    }
    lines
}

/// A binding's arguments, comma-separated.
fn arguments(arguments: &Value) -> String {
    let listed: Vec<String> = arguments.as_array().into_iter().flatten().map(plain).collect();
    if listed.is_empty() { "-".to_string() } else { listed.join(", ") }
}

/// The declared parameters: placeholder, slot, type and domain (`[min, max]` or the domain text verbatim).
fn parameters(parameters: &Value) -> Vec<String> {
    let rows: Vec<Vec<String>> = parameters
        .as_array()
        .into_iter()
        .flatten()
        .map(|p| vec![format!("${}", plain(&p["index"])), plain(&p["slot"]), plain(&p["type"]), domain(&p["binding"])])
        .collect();
    if rows.is_empty() {
        return vec![];
    }
    table(&[("Placeholder", Align::Left), ("Slot", Align::Right), ("Type", Align::Left), ("Domain", Align::Left)], &rows)
}

fn domain(binding: &Value) -> String {
    let free = &binding["free"];
    if let Some(text) = free["domain"].as_str() {
        text.to_string()
    } else if !free["min"].is_null() || !free["max"].is_null() {
        format!("[{}, {}]", plain(&free["min"]), plain(&free["max"]))
    } else {
        binding.to_string()
    }
}

/// A continuing session's incumbent (the submission view of iteration 0, `policy::submission_results`): where it comes
/// from, what GenDB wrote and froze, and how it competes. Empty for every other session.
fn incumbent(views: &DataViews) -> Vec<String> {
    let Some(incumbent) = views.submissions.as_array().into_iter().flatten().find(|s| s["incumbent"].is_object()) else { return vec![] };
    let record = &incumbent["incumbent"];
    let provenance = &record["provenance"];
    let directory = plain(&incumbent["directory"]);
    let mut lines = vec![
        "## Incumbent".to_string(),
        String::new(),
        format!(
            "This session continues from the package admitted by an earlier session (`{}`, its submission {}). Before this call GenDB wrote that package's manifest (`{}`, its storage uses pinned to the admitted storages it reads) and its author files (`src/agent/**`) into your workspace, froze them with the current framework (`{directory}/frozen/crate`) and evaluated them like a submission: column Incumbent below.",
            plain(&record["source_session"]),
            plain(&provenance["source_iteration"]),
            plain(&provenance["manifest"]),
        ),
        "The incumbent is not one of your submissions, but it competes like one: it stays selected, and is the package admitted and served after this session, unless a submission of yours is exact, verified and has a lower score_ns. The early stop counts it like a submission.".to_string(),
    ];
    let mut sources = format!("Its earlier author's submission (rationale, data access analysis) and provenance: `{}`", plain(&record["record"]));
    if let Some(notes) = provenance["source_notes"].as_str() {
        sources.push_str(&format!("; that author's notes: `{notes}` (hints written for that session's targets; GenDB's facts here are authoritative)"));
    }
    lines.push(sources + ".");
    if incumbent["render_only"] == true {
        lines.push("Render only: column Incumbent shows the source session's recorded evaluation; nothing was evaluated for this render.".to_string());
    }
    lines
}

/// How a submission view is named in the prompt: `the incumbent` (iteration 0 of a continuing session) or `submission N`.
fn candidate_name(submission: &Value) -> String {
    if submission["incumbent"].is_object() { "the incumbent".to_string() } else { format!("submission {}", plain(&submission["iteration"])) }
}

/// The early-stop factor of the targets, when the objective sets one.
fn bar_factor(targets: &Value) -> Option<u64> {
    targets["early_stop_factor"].as_u64()
}

/// A query author's targets and official results: one table row per benchmark cell with the target, the engine that
/// set it, the early-stop bar and every submission's official median; then one line per submission, the selection and
/// early-stop status, the targets' provenance, and whether the workspace still holds a submission's code.
fn query_results(views: &DataViews) -> Vec<String> {
    let cells = views.targets["cells"].as_array().cloned().unwrap_or_default();
    if cells.is_empty() {
        return submission_list(views, "## Official results");
    }
    let factor = bar_factor(views.targets);
    let submissions = views.submissions.as_array().cloned().unwrap_or_default();
    let selected = &views.objective["matrix"];
    let mut header = vec![("Binding", Align::Left), ("Workers", Align::Right), ("Target ms", Align::Right), ("Set by", Align::Left)];
    let bar_heading = factor.map(|f| format!("{f}x bar ms"));
    if let Some(heading) = &bar_heading {
        header.push((heading.as_str(), Align::Right));
    }
    let submission_headings: Vec<String> =
        submissions.iter().map(|s| if s["incumbent"].is_object() { "Incumbent ms".to_string() } else { format!("Sub {} ms", plain(&s["iteration"])) }).collect();
    header.extend(submission_headings.iter().map(|h| (h.as_str(), Align::Right)));
    header.push((if factor.is_some() { "Selected meets bar" } else { "Selected below target" }, Align::Left));
    let rows: Vec<Vec<String>> = cells
        .iter()
        .map(|cell| {
            let same_cell = |other: &&Value| other["binding"] == cell["binding"] && other["workers"] == cell["workers"];
            let mut row = vec![plain(&cell["binding"]), plain(&cell["workers"]), ms(&cell["target_ns"]), plain(&cell["engine"])];
            if factor.is_some() {
                row.push(ms(&cell["bar_ns"]));
            }
            for submission in &submissions {
                let result = submission["cells"].as_array().into_iter().flatten().find(same_cell);
                row.push(result.map_or_else(|| "-".to_string(), |r| format!("{}{}", ms(&r["median_ns"]), if r["met_bar"] == true { " *" } else { "" })));
            }
            let selected_cell = selected.as_array().into_iter().flatten().find(same_cell);
            let meets = selected_cell.filter(|c| !c["selected_median_ns"].is_null()).map(|c| if factor.is_some() { &c["early_stop_met"] } else { &c["met"] });
            row.push(meets.map_or("-", |met| if *met == true { "yes" } else { "no" }).to_string());
            row
        })
        .collect();
    let mut blocks = vec![vec!["## Targets and official results".to_string()], table(&header, &rows)];
    if submissions.iter().any(|s| s["cells"].as_array().into_iter().flatten().any(|c| c["met_bar"] == true)) {
        blocks.push(vec!["`*`: that submission's official exact median is at or below the bar.".to_string()]);
    }
    blocks.extend(submission_blocks(views));
    blocks.push(vec![performance_status(views, factor, cells.len())]);
    blocks.push(target_provenance(&cells, AuthorKind::Query));
    paragraphs(blocks)
}

/// Blocks of lines separated by one empty line (empty blocks left out).
fn paragraphs(blocks: Vec<Vec<String>>) -> Vec<String> {
    blocks.into_iter().filter(|block| !block.is_empty()).collect::<Vec<_>>().join(&String::new())
}

/// The objective as the goal reads it: the early stop (the selected submission at or below the bar in every cell)
/// first, the 1x targets second.
fn performance_status(views: &DataViews, factor: Option<u64>, cells: usize) -> String {
    let objective = views.objective;
    let matrix = objective["matrix"].as_array().cloned().unwrap_or_default();
    let count = |field: &str| matrix.iter().filter(|c| c[field] == true).count();
    let Some(selected_iteration) = objective["selected_iteration"].as_u64() else {
        return match factor {
            Some(f) => format!("Early stop (the goal): not met; no exact verified submission yet. It needs one submission at or below the {f}x bar in all {cells} cells."),
            None => "Objective: no exact verified submission yet.".to_string(),
        };
    };
    let score = ms(&objective["current_best_score"]["score_ns"]);
    let below_target = format!("{} of {} cells are below the 1x target", count("met"), matrix.len());
    let selected = views
        .submissions
        .as_array()
        .into_iter()
        .flatten()
        .find(|s| s["iteration"].as_u64() == Some(selected_iteration))
        .map_or_else(|| format!("submission {selected_iteration}"), candidate_name);
    let mut name = selected.clone();
    name[..1].make_ascii_uppercase();
    match factor {
        Some(f) if objective["early_stop"]["status"] == "met" => {
            format!("Early stop (the goal): met by {selected} (selected: lowest score, {score} ms), at or below the {f}x bar in all {cells} cells.")
        }
        Some(f) => format!(
            "Early stop (the goal): not met. {name} (selected: lowest score, {score} ms) is at or below the {f}x bar in {} of {cells} cells; one submission must be in all {cells}. For reference, {below_target} (that alone is not the goal).",
            count("early_stop_met")
        ),
        None => format!("Objective ({}): {selected} (selected: lowest score, {score} ms); {below_target}.", plain(&objective["status"])),
    }
}

/// One list line per submission (status, whether it counted, score, its first error line, and its frozen code when
/// the handoff identifies it), then whether the workspace still holds a submission's code.
fn submission_blocks(views: &DataViews) -> Vec<Vec<String>> {
    let code = submission_code(views.handoff);
    let lines: Vec<String> = views
        .submissions
        .as_array()
        .into_iter()
        .flatten()
        .map(|s| {
            let iteration = s["iteration"].as_u64().unwrap_or_default();
            let mut line = if s["incumbent"].is_object() {
                format!("- Incumbent: {} (not a submission)", plain(&s["status"]))
            } else {
                let counted = if s["counted"] == false { " (framework failure: not counted)" } else { " (counted)" };
                format!("- Submission {iteration}: {}{counted}", plain(&s["status"]))
            };
            if let Some(earlier) = s["duplicate_of_iteration"].as_u64() {
                let of = if earlier == 0 && views.submissions.as_array().into_iter().flatten().any(|s| s["incumbent"].is_object()) { "the incumbent".to_string() } else { format!("submission {earlier}") };
                line.push_str(&format!("; unchanged resubmission of {of}"));
            }
            if !s["score_ns"].is_null() {
                line.push_str(&format!("; score {} ms", ms(&s["score_ns"])));
            }
            if let Some(error) = s["error_first_line"].as_str() {
                line.push_str(&format!("; {}: {error}", plain(&s["failure_class"])));
            }
            if let Some(code) = code.get(&iteration) {
                if let Some(version) = code["crate_version"].as_str() {
                    line.push_str(&format!("; crate {version}"));
                }
                if let Some(path) = code["frozen_crate"].as_str() {
                    line.push_str(&format!(" (frozen: `{path}`)"));
                }
            }
            line + "."
        })
        .collect();
    vec![lines, workspace_line(&code).into_iter().collect()]
}

/// Every submission's code facts from the handoff, by iteration.
fn submission_code(handoff: &Value) -> BTreeMap<u64, Value> {
    handoff["submission_code"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(|entry| Some((entry["iteration"].as_u64()?, entry["code"].clone())))
        .filter(|(_, code)| code.is_object())
        .collect()
}

/// Whether the workspace still holds a submission's code (without it, authors compared it by hand).
fn workspace_line(code: &BTreeMap<u64, Value>) -> Option<String> {
    if code.is_empty() {
        return None;
    }
    let same: Vec<String> = code.iter().filter(|(_, c)| c["workspace"] == "same").map(|(i, _)| i.to_string()).collect();
    Some(if !same.is_empty() {
        format!("Workspace now: the submitted manifest and the crate's `src/agent` files are exactly those of submission {} (workspace storages not compared).", same.join(", "))
    } else if code.values().all(|c| c["workspace"] == "changed") {
        "Workspace now: the submitted manifest or the crate's `src/agent` files differ from every submission.".to_string()
    } else {
        "Workspace now: not compared with the submissions for this prompt.".to_string()
    })
}

/// The official results without per-cell targets (the workload storage author, or a correctness objective): one line
/// per submission and the objective.
fn submission_list(views: &DataViews, heading: &str) -> Vec<String> {
    let mut blocks = vec![vec![heading.to_string()]];
    if views.submissions.as_array().is_none_or(Vec::is_empty) {
        blocks.push(vec!["No submission yet.".to_string()]);
    } else {
        blocks.extend(submission_blocks(views));
    }
    blocks.push(vec![objective_line(views.objective)]);
    paragraphs(blocks)
}

/// The objective of a correctness or storage session: met by its first exact verified (or verified and built)
/// submission.
pub fn objective_line(objective: &Value) -> String {
    match objective["iteration"].as_u64() {
        Some(iteration) if objective["status"] == "met" => format!("Objective: met by submission {iteration}."),
        _ => "Objective: not met yet (the first passing submission meets it and ends the session).".to_string(),
    }
}

/// Where the targets come from: grouped by source file, benchmark key and remark when the provenance has GenDB's
/// baselines form (`TargetSource`); any other provenance verbatim with its cells. A target that names its system
/// (`RuntimeTarget::system`) has one measured time per cell, the table's, so its line names no two engines' times.
fn target_provenance(cells: &[Value], author: AuthorKind) -> Vec<String> {
    let (shown, engine_times) = match author {
        AuthorKind::Query | AuthorKind::Engine | AuthorKind::GeneralEngine => ("column Set by", "`performance.json` `runtime_targets[].provenance`"),
        AuthorKind::WorkloadStorage => ("named after each target", "`workload.json` and `performance.json` (`statements[].objective.runtime_targets[].provenance`)"),
    };
    // (what, timing scope, named system) -> the cells or keys it covers.
    let mut groups: BTreeMap<(String, String, bool), Vec<String>> = BTreeMap::new();
    for cell in cells {
        let source = &cell["source"];
        let (what, keys) = if source.is_object() {
            let from = format!("the faster of {} per cell ({shown}), {}; from `{}`", plain(&source["engines"]), plain(&source["remark"]), plain(&source["file"]));
            (from, plain(&source["key"]))
        } else {
            (plain(&cell["provenance"]), format!("{}/{}", plain(&cell["binding"]), plain(&cell["workers"])))
        };
        let entry = groups.entry((what, plain(&cell["timing_scope"]), cell["system"].is_string())).or_default();
        if !entry.contains(&keys) {
            entry.push(keys);
        }
    }
    groups
        .into_iter()
        .map(|((what, scope, named_system), keys)| {
            let keys = if keys.len() > 3 { format!("{} keys, {} to {}", keys.len(), keys[0], keys[keys.len() - 1]) } else { keys.join(", ") };
            if named_system {
                format!("Targets: {what} ({keys}); timing scope: {scope}.")
            } else {
                format!("Targets: {what} ({keys}); both engines' times per cell: {engine_times}; timing scope: {scope}.")
            }
        })
        .collect()
}

/// Every workload statement (the storage author): SQL, parameters, the columns it reads, and its benchmark bindings
/// with the target per worker count and the engine that set it (`targets.by_statement[index]`).
fn statements(context: &Value, targets: &Value) -> Vec<String> {
    let statements = context["statements"].as_array().cloned().unwrap_or_default();
    let mut lines = vec![
        "## Statements".to_string(),
        String::new(),
        "Every workload statement: its SQL, parameters, the columns it reads, and per benchmark binding the runtime target in ms at each worker count, with the engine that set it. The tools' `statement` argument is the statement index. Full per-statement inputs: `workload.json`.".to_string(),
    ];
    let cells_of = |statement: &Value| -> Vec<Value> {
        statement["index"].as_u64().and_then(|i| targets["by_statement"][i as usize].as_array().cloned()).unwrap_or_default()
    };
    let all_cells: Vec<Value> = statements.iter().flat_map(cells_of).collect();
    if !all_cells.is_empty() {
        lines.push(String::new());
        lines.extend(target_provenance(&all_cells, AuthorKind::WorkloadStorage));
    }
    for statement in &statements {
        lines.push(String::new());
        let key = statement["statement_key"].as_str().map(|key| format!(" (key {})", &key[..key.len().min(12)])).unwrap_or_default();
        lines.extend([format!("### Statement {}{key}", plain(&statement["index"])), String::new()]);
        lines.extend(fenced("sql", statement["sql"].as_str().unwrap_or_default()));
        let parameters = parameters(&statement["parameters"]);
        if !parameters.is_empty() {
            lines.push(String::new());
            lines.extend(parameters);
        }
        lines.extend([String::new(), format!("Reads: {}.", demand(&statement["demand"]))]);
        lines.extend(statement_targets(statement, &cells_of(statement)));
    }
    lines
}

/// The columns a statement reads, per table (`row count only` when only its row count is read).
fn demand(demand: &Value) -> String {
    let tables: Vec<String> = demand
        .as_array()
        .into_iter()
        .flatten()
        .map(|t| {
            let columns: Vec<String> = t["columns"].as_array().into_iter().flatten().map(plain).collect();
            let read = if t["row_count_only"] == true || columns.is_empty() { "row count only".to_string() } else { columns.join(", ") };
            format!("{}({read})", plain(&t["table"]))
        })
        .collect();
    if tables.is_empty() { "-".to_string() } else { tables.join("; ") }
}

/// A statement's benchmark bindings with the target (and the engine that set it) per worker count.
fn statement_targets(statement: &Value, cells: &[Value]) -> Vec<String> {
    if cells.is_empty() {
        return vec![String::new(), format!("Objective: {} (no runtime targets).", plain(&statement["objective"]["kind"]))];
    }
    let mut workers: Vec<u64> = cells.iter().filter_map(|c| c["workers"].as_u64()).collect();
    workers.sort_unstable();
    workers.dedup();
    let mut bindings: Vec<String> = vec![];
    for cell in cells {
        let binding = plain(&cell["binding"]);
        if !bindings.contains(&binding) {
            bindings.push(binding);
        }
    }
    let arguments_of = |binding: &str| {
        statement["objective"]["benchmark_bindings"].as_array().into_iter().flatten().find(|b| b["name"] == binding).map_or_else(|| "-".to_string(), |b| arguments(&b["arguments"]))
    };
    let headings: Vec<String> = workers.iter().map(|w| format!("{w} {} ms", if *w == 1 { "worker" } else { "workers" })).collect();
    let mut header = vec![("Binding", Align::Left), ("Arguments", Align::Left)];
    header.extend(headings.iter().map(|h| (h.as_str(), Align::Right)));
    let rows: Vec<Vec<String>> = bindings
        .iter()
        .map(|binding| {
            let mut row = vec![binding.clone(), arguments_of(binding)];
            for w in &workers {
                let cell = cells.iter().find(|c| plain(&c["binding"]) == *binding && c["workers"].as_u64() == Some(*w));
                row.push(cell.map_or_else(|| "-".to_string(), |c| format!("{} ({})", ms(&c["target_ns"]), plain(&c["engine"]))));
            }
            row
        })
        .collect();
    let mut lines = vec![String::new()];
    lines.extend(table(&header, &rows));
    lines
}

/// The storage policy, the storage budget as read before this call, the counted storages and the free disk space at
/// preparation.
fn storage(context: &Value) -> Vec<String> {
    let mut lines = vec!["## Storage".to_string(), String::new()];
    if let Some(policy) = context["storage_policy"]["kind"].as_str() {
        lines.push(format!("- Storage policy: `{policy}`."));
    }
    let budget = &context["storage_budget"];
    if budget.is_object() {
        if budget["budget_bytes"].is_null() {
            lines.push(format!("- Storage budget: none. {}", plain(&budget["meaning"])));
        } else {
            lines.push(format!(
                "- Storage budget: {}; used {}; left {} (bytes: {} / {} / {}). Read from the library before this call: a snapshot, not a reservation; the counting rules are in `{}`.",
                size(&budget["budget_bytes"]),
                size(&budget["used_bytes"]),
                size(&budget["left_bytes"]),
                plain(&budget["budget_bytes"]),
                plain(&budget["used_bytes"]),
                plain(&budget["left_bytes"]),
                plain(&budget["file"])
            ));
        }
        if let Some(error) = budget["refresh_error"].as_str() {
            lines.push(format!("- Budget refresh: {error}."));
        }
        let counted: Vec<String> = budget["used_by"].as_array().into_iter().flatten()
            .map(|s| format!("{} {}", plain(&s["name"]), size(if s["counted_bytes"].is_null() { &s["storage_bytes"] } else { &s["counted_bytes"] })))
            .collect();
        if !counted.is_empty() {
            lines.push(format!("- Counted storages (package ids and sizes in `storages.json`): {}.", counted.join("; ")));
        }
    }
    let free = &context["performance"]["free_bytes_at_prepare"];
    if !free.is_null() {
        lines.push(format!("- Free disk space when this session was prepared (not refreshed): {} ({} bytes).", size(free), plain(free)));
    }
    if lines.len() == 2 { vec![] } else { lines }
}

/// The run's declared integrity constraints, one line per table.
fn integrity_constraints(context: &Value) -> Vec<String> {
    let constraints = &context["integrity_constraints"];
    let declarations = constraints["declarations"].as_array().cloned().unwrap_or_default();
    if declarations.is_empty() {
        return vec![];
    }
    let mut lines = vec!["## Integrity constraints".to_string(), String::new()];
    let mut sentence = String::new();
    if let Some(in_words) = constraints["in_words"].as_str() {
        let mut letters = in_words.chars();
        let capitalized: String = letters.next().map(|first| first.to_uppercase().chain(letters).collect()).unwrap_or_default();
        sentence.push_str(&format!("{capitalized}. "));
    }
    sentence.push_str(&format!("Trust: {} ({}). Details: `{}`.", plain(&constraints["trust"]), plain(&constraints["basis"]), plain(&constraints["details"])));
    lines.push(sentence);
    lines.push("(A fixed entry is the framework's fixed claim a crate is verified against: the query entry is the final SQL claim of every query crate, a storage entry the claim of a storage builder; `obligations.json` states each.)".to_string());
    lines.push(String::new());
    let mut tables: Vec<(String, Vec<String>)> = vec![];
    for declaration in &declarations {
        let table = plain(&declaration["table"]);
        match tables.iter_mut().find(|(name, _)| *name == table) {
            Some((_, sqls)) => sqls.push(plain(&declaration["sql"])),
            None => tables.push((table, vec![plain(&declaration["sql"])])),
        }
    }
    lines.extend(tables.into_iter().map(|(table, sqls)| format!("- {table}: {}", sqls.join("; "))));
    lines
}

/// The configured worker counts, the timing protocol and the host as observed once at preparation.
fn host(views: &DataViews) -> Vec<String> {
    let context = views.context;
    let observed = &context["observed_hardware"];
    let mut lines = vec!["## Host and measurement".to_string(), String::new()];
    let workers: Vec<String> = context["hardware"]["threads"].as_array().into_iter().flatten().map(plain).collect();
    if !workers.is_empty() {
        lines.push(format!("- Worker counts measured: {} (each the maximum a call may use, not a requirement).", workers.join(", ")));
    }
    if let Some(timing) = context["performance"]["evaluation_timing"].as_str() {
        lines.push(format!("- Timing: {timing}."));
    }
    if observed.is_object() {
        lines.extend(observed_host(observed, cpu_flags_file(views)));
    }
    if lines.len() == 2 { vec![] } else { lines }
}

/// Where every CPU flag is listed: a query author's `performance.json` under the execution-time objective (the
/// correctness objective writes none, so its contract index), the other roles' `data.json`.
fn cpu_flags_file(views: &DataViews) -> &'static str {
    match views.author {
        AuthorKind::Query if Objective::of(views.context) == Objective::Performance => "`performance.json` `observed_hardware.cpu_features`",
        AuthorKind::Query => "`files.author_contract` `hardware.observed.cpu_features`",
        AuthorKind::WorkloadStorage | AuthorKind::Engine | AuthorKind::GeneralEngine => "`data.json` `hardware.observed.cpu_features`",
    }
}

/// The observed host: CPU, NUMA, caches, memory, the named CPU flags (every flag: `flags_file`) and the crash-dump
/// setting.
fn observed_host(observed: &Value, flags_file: &str) -> Vec<String> {
    let mut lines = vec![];
    let memory_nodes = observed["allowed_memory_nodes"].as_str().unwrap_or_default();
    let numa_nodes = observed["numa_nodes"].as_array().cloned().unwrap_or_default();
    let all_nodes = format!("0-{}", numa_nodes.len().saturating_sub(1));
    let memory_note = if memory_nodes.is_empty() || memory_nodes == all_nodes || numa_nodes.len() <= 1 { String::new() } else { format!("; allowed memory nodes {memory_nodes}") };
    lines.push(format!(
        "- CPU: {}; {} packages, {} physical cores, {} logical CPUs in affinity ({}){memory_note}.",
        plain(&observed["cpu_model"]),
        plain(&observed["packages_in_affinity"]),
        plain(&observed["physical_cores_in_affinity"]),
        plain(&observed["logical_cpus_in_affinity"]),
        plain(&observed["affinity_cpu_list"])
    ));
    for node in &numa_nodes {
        lines.push(format!("- NUMA {}: CPUs {}; distances {}.", plain(&node["node"]), cpu_list(node["cpu_list"].as_str().unwrap_or_default()), plain(&node["distance"])));
    }
    let caches: Vec<String> = observed["caches"].as_array().into_iter().flatten()
        .map(|c| format!("L{} {} {} x{} (each shared by {} logical CPUs, {} B lines)", plain(&c["level"]), plain(&c["type"]), plain(&c["size_per_instance"]),
            plain(&c["instances_visible_to_affinity"]), plain(&c["logical_cpus_sharing_each_instance"]), plain(&c["line_bytes"])))
        .collect();
    if !caches.is_empty() {
        lines.push(format!("- Caches: {}.", caches.join("; ")));
    }
    let memory = &observed["host_memory_bytes"];
    if memory.is_object() {
        lines.push(format!("- Memory: {} total, {} available when observed, swap free {} ({}).", size(&memory["total"]), size(&memory["available"]), size(&memory["swap_free"]), plain(&observed["memory_scope"])));
    }
    if let Some(features) = observed["cpu_features"].as_str() {
        let named: Vec<&str> = features.split_whitespace().filter(|flag| NAMED_CPU_FLAGS.contains(flag) || flag.starts_with("avx512") || flag.starts_with("amx")).collect();
        lines.push(format!("- Vector, bit and crypto instructions: {} (the full flag list: {flags_file}).", named.join(" ")));
    }
    let dumps = &observed["crash_dumps"];
    if dumps.is_object() {
        let error = dumps["containment_error"].as_str().map(|e| format!(", containment error: {e}")).unwrap_or_default();
        lines.push(format!("- Crash dumps: coredump_filter {}, contained {}{error}.", plain(&dumps["coredump_filter"]), plain(&dumps["contained"])));
    } else if !dumps.is_null() {
        lines.push(format!("- Crash dumps: {}.", plain(dumps)));
    }
    if !observed["source"].is_null() {
        lines.push(format!("- Observed once at preparation ({}); unavailable values are empty.", plain(&observed["source"])));
    }
    lines
}
