//! `workload/` and `records/workload/` of the output home: the workload storage session and every admitted storage.
//!
//! Every published storage is one admitted package: `workload/storage/<name>/v<N>/` with its README, `interface/` and
//! `builder/`, and `records/workload/storage/<name>/v<N>/storage.json` (name, package, version, origin). `N` is the
//! package's position in the library's append-only version stream of the name (1 = first admitted), so the label is
//! fixed by the library at admission and never allocated by a writer. Two versions of one name (a query may register a
//! new version while another admitted query still reads the old one) never overwrite each other, and queries link the
//! exact version they read. `workload/storage/<name>/README.md` lists the versions of a name and
//! `workload/storage/README.md` every published version ([`write_storage_index`]).

use super::{subdirectories as storage_dirs, OutputError, copy_code, iterations, qualified_iterations, read_json, replace_dir, write_home_readme, write_json, write_text};
use gendb_artifacts::verus::{VerusBuildV1, VerusSourceOwnerV1, VerusStoragePackageV1};
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_verification::obligations::DeclaredSource;
use serde_json::{Value, json};
use std::path::Path;

/// One closed workload storage session to publish.
pub struct WorkloadOutput<'a> {
    /// The workload storage session's root (`<run>/workload-storage/session`).
    pub session: &'a Path,
    /// The library root of the run (admitted storage versions).
    pub library: &'a Path,
}

/// Write `workload/` (README, `attempts/`) and `workload/storage/<name>/` for every storage of the selected submission,
/// `records/workload/`, and the top-level README. Storages added later by query sessions are kept.
pub fn write_workload(home: &Path, w: &WorkloadOutput<'_>) -> Result<Value, OutputError> {
    let summary = read_json(&w.session.join("summary.json")).unwrap_or(Value::Null);
    let selected = qualified_iterations(&summary).last().copied();
    let all = iterations(w.session);
    let mut storages = vec![];
    if let Some((n, dir)) = all.iter().find(|(n, _)| Some(*n) == selected) {
        let store = open_library(w.library)?;
        let evaluation = super::iteration_evaluation(dir);
        for (name, storage) in storage_dirs(&dir.join("frozen/storages")) {
            let package = package_of(&evaluation["storages"], &name)
                .ok_or_else(|| OutputError(format!("workload attempt {n}: the evaluation names no package for storage {name}")))?;
            let version = write_storage(home, &store, &name, package, &storage, &format!("workload storage session, attempt {n}"))?;
            storages.push(json!({"name":name,"package":package,"version":version}));
        }
    }
    let index = write_storage_index(home)?;
    let evaluations: Vec<(u32, Value, Value, std::path::PathBuf)> = all
        .iter()
        .map(|(n, dir)| (*n, super::iteration_evaluation(dir), read_json(&dir.join("qualification.json")).unwrap_or(Value::Null), dir.clone()))
        .collect();

    let mut text = String::from("# Workload storage\n\nShared storage designed by the workload agent for all queries, plus storages added by query agents.\n\n");
    text.push_str(&format!(
        "Session: {} ({}); selected attempt: {}; provider-reported author cost: ${}.\n\n## Storages\n\n",
        summary["status"].as_str().unwrap_or("unknown"),
        summary["reason"].as_str().unwrap_or(""),
        selected.map_or("none".into(), |n| n.to_string()),
        summary["reported_cost_usd"].as_str().unwrap_or("unknown")
    ));
    text.push_str("Every published version (admitted package) of every storage name, including storages added by query sessions: [`storage/README.md`](storage/README.md).\n\n");
    text.push_str(&index);
    if let Some((_, evaluation, _, _)) = evaluations.iter().find(|(n, ..)| Some(*n) == selected) {
        text.push_str(&admission_section(evaluation, &summary));
    }
    text.push_str("\n[Attempts](attempts/README.md) · raw records: `records/workload/`\n");
    write_text(&home.join("workload/README.md"), &text)?;
    replace_dir(&home.join("workload/attempts"), |dir| {
        let mut index = String::from("# Workload attempts\n\n");
        for (n, evaluation, _, iteration) in &evaluations {
            let mark = if Some(*n) == selected { " (selected)" } else { "" };
            let repaired = evaluation["repaired_by"].as_str().map(|r| format!("; re-evaluated by the framework repair `{r}` (the first evaluation was a framework defect)")).unwrap_or_default();
            let status = format!("{}, {}{repaired}", evaluation["status"].as_str().unwrap_or("not evaluated"), if evaluation["eligible"] == true { "eligible" } else { "not eligible" });
            index.push_str(&format!("- [attempt {n}]({n}/README.md){mark}: {status}\n"));
            let mut text = format!("# Workload attempt {n}{mark}\n\nStatus: {status}.\n");
            if let Ok(notes) = std::fs::read_to_string(iteration.join("NOTES.md")) {
                write_text(&dir.join(n.to_string()).join("NOTES.md"), &notes)?;
                text.push_str("\nThe author's notes for the next attempt: [`NOTES.md`](NOTES.md) (hints; GenDB's records are authoritative).\n");
            }
            text.push_str(&format!("\nRaw records: `records/workload/attempts/{n}/`.\n"));
            write_text(&dir.join(n.to_string()).join("README.md"), &text)?;
        }
        write_text(&dir.join("README.md"), &index)
    })?;
    let record = json!({"selected_attempt":selected,"storages":storages,"session":w.session,"reported_cost_usd":summary["reported_cost_usd"]});
    write_json(&home.join("records/workload/workload.json"), &record)?;
    write_json(&home.join("records/workload/summary.json"), &summary)?;
    for (n, evaluation, qualification, _) in &evaluations {
        let target = home.join("records/workload/attempts").join(n.to_string());
        write_json(&target.join("evaluation.json"), evaluation)?;
        if !qualification.is_null() {
            write_json(&target.join("qualification.json"), qualification)?;
        }
    }
    write_text(&home.join("records/workload/README.md"), "# Workload records\n\n`workload.json`, the session `summary.json`, per attempt `evaluation.json` / `qualification.json`, and per storage version `storage/<name>@<package12>/storage.json`.\n")?;
    write_home_readme(home)?;
    Ok(record)
}

/// The admission evidence of the selected submission: its recorded claim, column coverage, storage budget, per storage
/// the proof result, stored bytes, build time and tiny-input builds, and the author's elapsed time (from the
/// evaluation record and the session summary; nothing is recomputed).
fn admission_section(evaluation: &Value, summary: &Value) -> String {
    let mut text = String::from("\n## Admission evidence\n\n");
    text.push_str(&format!("Claim recorded with the evaluation: {}\n\n", evaluation["claim"].as_str().unwrap_or("none")));
    let coverage = &evaluation["coverage"];
    let tables = coverage["tables"].as_array().map(|t| t.iter().map(|t| format!("{} {}", t["table"].as_str().unwrap_or("?"), t["columns"])).collect::<Vec<_>>().join(", ")).unwrap_or_default();
    text.push_str(&format!("Column coverage: complete {}, missing columns {} ({tables}).\n\n", coverage["complete"], coverage["missing_columns"]));
    let budget = &evaluation["storage_budget"];
    text.push_str(&format!("Storage budget: {} new serving bytes of {} allowed ({} left).\n\n", budget["new_bytes"], budget["allowance_bytes"], budget["left_bytes_after"]));
    text.push_str("| Storage | Package | Verus (verified items, errors) | Stored bytes | Build s | Tiny-input builds |\n|---|---|---|---:|---:|---|\n");
    for storage in evaluation["storages"].as_array().into_iter().flatten() {
        let asset = &storage["asset"];
        text.push_str(&format!("| {} | `{}` | {}, {} | {} | {:.1} | {} |\n",
            storage["name"].as_str().unwrap_or("?"), storage["package"].as_str().unwrap_or("?"),
            storage["verification"]["verified"], storage["verification"]["errors"], asset["storage_bytes"],
            asset["build_wall_ns"].as_f64().unwrap_or(0.0) / 1e9, storage["tiny_builds"]["status"].as_str().unwrap_or("?")));
    }
    text.push_str(&format!("\nAuthor: {} call(s), {} submission(s), elapsed {} ms (provider sessions); framework evaluation of the selected submission {} ns (session-cached checked builds reused).\n",
        summary["calls"], summary["iterations"], summary["author_elapsed_ms"], evaluation["framework_evaluation_ns"]));
    text.push_str("\nThe storage claim is the fixed storage entry's, checked by Verus for each crate: total correctness relative to its outcome contract under its trusted assumptions (on `Ok` its parts represent the stored source rows; its readers' ensures); a full-data build is required to succeed. No query result is part of storage admission. Layout descriptions in each storage README are the author's prose: only the interface's specifications are proof premises.\n");
    text
}

/// The package id of storage `name` in an evaluation's storage list (`[{name, package, ..}]`).
pub(crate) fn package_of<'a>(storages: &'a Value, name: &str) -> Option<&'a str> {
    storages.as_array().into_iter().flatten().find(|s| s["name"] == name).and_then(|s| s["package"].as_str())
}

pub(crate) fn open_library(library: &Path) -> Result<ObjectStore, OutputError> {
    ObjectStore::open_existing(library).map_err(|e| super::io_error(library, e))
}

/// The version number of admitted storage package `package` of `name`: its position in the library's version stream of
/// the name, oldest first (1 = the first admitted version). A package the stream does not hold is an error, never a guess.
pub(crate) fn storage_version(store: &ObjectStore, name: &str, package: &str) -> Result<usize, OutputError> {
    let versions = gendb_artifacts::verus::storage_versions(store, name).map_err(|e| OutputError(format!("versions of storage {name}: {e}")))?;
    versions
        .iter()
        .rev()
        .position(|(_, admission)| admission.package.to_hex() == package)
        .map(|index| index + 1)
        .ok_or_else(|| OutputError(format!("storage {name}: package {package} is not an admitted version in the library")))
}

/// The folder of version `version` of storage `name`, relative to `workload/storage/` (and `records/workload/storage/`).
pub fn storage_version_dir(name: &str, version: usize) -> String {
    format!("{name}/v{version}")
}

/// Write version folder `workload/storage/<name>/v<N>/` (README, `interface/`, `builder/`) from a frozen storage
/// directory (`storage.json` and `crate/src`) of the admitted `package`, and `records/workload/storage/<name>/v<N>/storage.json`.
/// `origin` says which session added it. Other versions are left as they are; call [`write_storage_index`] afterwards.
/// Returns `N`.
pub fn write_storage(home: &Path, store: &ObjectStore, name: &str, package: &str, frozen: &Path, origin: &str) -> Result<usize, OutputError> {
    let version = storage_version(store, name, package)?;
    let src = frozen.join("crate/src");
    let manifest = read_json(&frozen.join("storage.json")).unwrap_or(Value::Null);
    let folder = storage_version_dir(name, version);
    replace_dir(&home.join("workload/storage").join(&folder), |dir| {
        copy_code(&src.join("stores").join(name).join("interface"), &dir.join("interface"), None)?;
        copy_code(&src.join("builder"), &dir.join("builder"), None)?;
        write_code_readmes(dir)?;
        write_text(&dir.join("README.md"), &storage_readme(name, version, package, &manifest, origin))
    })?;
    let mut record = if manifest.is_object() { manifest } else { json!({}) };
    record["origin"] = json!(origin);
    write_version_record(home, name, version, package, record)?;
    Ok(version)
}

/// Write the version folder of an admitted storage `name` (`package`) that the output home lacks, from the `store`: its
/// interface and builder as the admitted build stored them, and the admission's description (layout, parts). Used for a
/// version a query reads that no published session submitted (for example one an author registered with
/// `storage_register` during a call). An existing folder is kept. Returns its version number.
pub fn write_admitted_storage(home: &Path, store: &ObjectStore, name: &str, package: &str) -> Result<usize, OutputError> {
    let version = storage_version(store, name, package)?;
    let folder = home.join("workload/storage").join(storage_version_dir(name, version));
    if folder.exists() {
        return Ok(version);
    }
    let error = |what: &str, e: &dyn std::fmt::Display| OutputError(format!("storage {name} package {package}: {what}: {e}"));
    let id = ContentId::parse_hex(package).map_err(|e| error("package id", &e))?;
    let record: VerusStoragePackageV1 = store.read(id).and_then(|o| o.decode()).map_err(|e| error("package record", &e))?;
    let build: VerusBuildV1 = store.read(record.build).and_then(|o| o.decode()).map_err(|e| error("build record", &e))?;
    let description = crate::storage::catalog::description_of(store, id, name).map_err(|e| error("admission description", &e))?;
    let declaration: Option<DeclaredSource> = serde_json::from_value(record.declaration.clone()).ok();
    let tables: Vec<Value> = declaration.iter().flat_map(|d| &d.tables).map(|t| json!({"table":t.name,
        "columns":t.columns.iter().filter(|c| !c.row_count_only).map(|c| &c.name).collect::<Vec<_>>()})).collect();
    let registered_by = &description["registered_by"];
    let origin = format!("admitted from the library (registered by the {} session {})", registered_by["role"].as_str().unwrap_or("?"), registered_by["session"].as_str().unwrap_or("?"));
    let manifest = json!({"layout":description["layout"],"tables":tables,"parts":description["parts"]});
    let interface = format!("stores/{name}/interface/");
    replace_dir(&folder, |dir| {
        for source in build.sources.iter().filter(|s| s.owner == VerusSourceOwnerV1::Agent) {
            let target = if let Some(rest) = source.path.strip_prefix(&interface) {
                dir.join("interface").join(rest)
            } else if let Some(rest) = source.path.strip_prefix("builder/") {
                dir.join("builder").join(rest)
            } else {
                continue;
            };
            let bytes = store.read_blob(source.blob, Some(source.bytes)).map_err(|e| error(&source.path, &e))?;
            write_text(&target, &String::from_utf8(bytes).map_err(|e| error(&source.path, &e))?)?;
        }
        write_code_readmes(dir)?;
        write_text(&dir.join("README.md"), &storage_readme(name, version, package, &json!({"manifest":manifest}), &origin))
    })?;
    write_version_record(home, name, version, package, json!({"manifest":manifest,"description":description,"origin":origin}))?;
    Ok(version)
}

fn write_code_readmes(dir: &Path) -> Result<(), OutputError> {
    write_text(&dir.join("interface/README.md"), "# Interface\n\nThe storage's contract (`represents`: what the stored parts mean) and its verified readers, as admitted; query crates copy these files unchanged.\n")?;
    write_text(&dir.join("builder/README.md"), "# Builder\n\nThe verified builder that produced the stored parts.\n")
}

fn write_version_record(home: &Path, name: &str, version: usize, package: &str, mut record: Value) -> Result<(), OutputError> {
    record["name"] = json!(name);
    record["version"] = json!(version);
    record["package"] = json!(package);
    write_json(&home.join("records/workload/storage").join(storage_version_dir(name, version)).join("storage.json"), &record)
}

/// Rewrite the storage indexes from the published version folders: `workload/storage/<name>/README.md` (the versions of
/// one name) and `workload/storage/README.md` (every version). A name-only view written by an older GenDB
/// (`<name>/interface`, `<name>/builder`, `records/workload/storage/<name>/storage.json`; it showed whichever version was
/// published last) is removed once the name has version folders. Returns the index's list (Markdown) for the workload
/// README.
pub fn write_storage_index(home: &Path) -> Result<String, OutputError> {
    let root = home.join("workload/storage");
    let records = home.join("records/workload/storage");
    let mut list = String::new();
    for (name, dir) in storage_dirs(&root) {
        let mut versions: Vec<(usize, String)> =
            storage_dirs(&dir).into_iter().filter_map(|(v, _)| Some((v.strip_prefix('v')?.parse().ok()?, v))).collect();
        if versions.is_empty() {
            continue;
        }
        versions.sort();
        for legacy in [dir.join("interface"), dir.join("builder"), records.join(&name).join("storage.json")] {
            let removed = if legacy.is_dir() { std::fs::remove_dir_all(&legacy) } else if legacy.exists() { std::fs::remove_file(&legacy) } else { Ok(()) };
            removed.map_err(|e| super::io_error(&legacy, e))?;
        }
        let mut text = format!("# Storage `{name}`\n\nPublished versions (admitted packages, numbered in the library's admission order); each query links the version it reads.\n\n");
        list.push_str(&format!("- `{name}`:"));
        for (_, folder) in &versions {
            let record = read_json(&records.join(&name).join(folder).join("storage.json")).unwrap_or(Value::Null);
            let origin = record["origin"].as_str().unwrap_or("origin unknown");
            text.push_str(&format!("- [`{folder}`]({folder}/README.md): package `{}`, {origin}\n", record["package"].as_str().unwrap_or("?")));
            list.push_str(&format!(" [{folder}](storage/{name}/{folder}/README.md) ({origin})"));
        }
        list.push('\n');
        write_text(&dir.join("README.md"), &text)?;
    }
    let all = format!("# Storages\n\nEvery published storage version (`<name>/v<N>`, numbered in the library's admission order of the name); a version is one admitted package and never overwrites another.\n\n{}",
        list.replace("](storage/", "]("));
    write_text(&root.join("README.md"), &all)?;
    Ok(list)
}

fn storage_readme(name: &str, version: usize, package: &str, storage: &Value, origin: &str) -> String {
    let m = &storage["manifest"];
    let mut t = format!("# Storage `{name}`, version {version}\n\nPackage: `{package}`. Origin: {origin}. All versions of this name: [`../README.md`](../README.md).\n\n");
    if let Some(summary) = m["layout"]["summary"].as_str() {
        t.push_str(&format!("{summary}\n\n"));
    }
    for (label, key) in [("Units", "units"), ("Why", "choice")] {
        if let Some(v) = m["layout"][key].as_str() {
            t.push_str(&format!("{label}: {v}\n\n"));
        }
    }
    t.push_str("## Tables and columns\n\n");
    for table in m["tables"].as_array().into_iter().flatten() {
        let columns: Vec<&str> = table["columns"].as_array().into_iter().flatten().filter_map(Value::as_str).collect();
        t.push_str(&format!("- `{}`: {}\n", table["table"].as_str().unwrap_or("?"), columns.join(", ")));
    }
    if let Some(parts) = m["parts"].as_array() {
        t.push_str("\n## Parts\n\n");
        for p in parts {
            t.push_str(&format!("- {}\n", p.as_str().unwrap_or("")));
        }
    }
    if let Some(notes) = m["notes"].as_str().filter(|n| !n.is_empty()) {
        t.push_str(&format!("\n## Notes\n\n{notes}\n"));
    }
    t.push_str("\n## Code\n\n- [`interface/`](interface/): the storage's contract (`represents`) and readers, as admitted.\n- [`builder/`](builder/): the verified builder.\n");
    t
}
