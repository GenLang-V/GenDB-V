//! The search index of all admitted author code: every author source of every admitted query package
//! and every admitted storage package, copied read-only into the workspace (`admitted-code/`), with one entry per file
//! (origin, kind, one-line description from the module header, public items with signatures and clauses) in
//! `search-index.json`, and one grep-able line per item in `search-index.txt`.
//!
//! Modules under a `common/` directory are the authors' general modules (no query constants in their specifications);
//! the index marks them `general`. Later authors search the index and copy or adapt what they choose; nothing is
//! composed automatically, and Verus checks every copy again in the new crate. Reading material only: the index never
//! decides applicability.
//!
//! An engine run may name read-only reuse libraries (`engine.reuse_libraries`, [`ReuseLibrary`]): their admitted author
//! code is indexed and copied the same way, after the run's own library, with the library named (not its path) in
//! each entry's origin. A build already indexed from the run's own library (a seeded storage, content-addressed alike) is not
//! repeated. Those libraries are only read; their code is offered for reuse, never counted in the run's budget and
//! never served.
//!
//! A general engine line run ([`write_engine_search_index`]) also indexes
//! the agent modules of every version of every branch (`origin.status` `accepted version`) and of every attempt that
//! passed Verus on the whole crate but was not accepted (`verified, not accepted`), from the run's records
//! (`<run>/engine/{versions,attempts}/<id>/code/agent/**`), each with its branch, version, parents, direction, score and
//! measured effect from the findings log; their module lines are marked `engine` and `verified-not-accepted`. Reuse
//! means copying a module into one's own crate, where Verus checks it again. In a run of several workloads
//! (`engine.workloads`) it also indexes the code of the root's other sides
//! (`versions/v000/root-sides/<workload>/code/**`: each side's shared engine, modules, families and plans, `origin.status`
//! `root side`) and of the seeds' common ancestor (`root-sides/ancestor/code/**`, `seeds' common ancestor`), marked
//! `root-side`.

use super::common::write;
use crate::query::source_items::{module_doc, public_items};
use crate::storage::catalog::write_read_only;
use crate::storage::policy::StoredDataPolicy;
use gendb_artifacts::verus::{
    self as records, VERUS_STORAGE_ADMISSION_KIND, VerusImplementationV1, VerusPackageAdmissionV2, VerusQueryPackageV3, VerusSourceOwnerV1,
    VerusStorageAdmissionV1, VerusStoragePackageV1,
};
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_verification::admission::AdmissionError;
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

/// The index files under the workspace.
pub const INDEX_FILE: &str = "search-index.json";
pub const INDEX_TEXT_FILE: &str = "search-index.txt";
/// Where the admitted sources are copied, under the workspace.
pub const CODE_DIRECTORY: &str = "admitted-code";

/// The origin kind of a storage build's author files.
const STORAGE_CRATE: &str = "storage_crate";

/// A library offered read-only for reuse: its admitted author code is indexed and copied, nothing else is read and
/// nothing is written to it.
pub struct ReuseLibrary<'a> {
    pub path: &'a Path,
    pub store: &'a ObjectStore,
}

impl ReuseLibrary<'_> {
    /// The name authors see (`origin.reuse_library`): the directory holding the library (`tpch-sf100-single-copy` for
    /// `<...>/tpch-sf100-single-copy/library`), not its path, since the library itself is no author input.
    fn label(&self) -> String {
        let name = |p: &Path| p.file_name().map(|n| n.to_string_lossy().into_owned());
        self.path.parent().and_then(name).or_else(|| name(self.path)).unwrap_or_else(|| "reuse".into())
    }
}

/// What one indexed author file is.
struct Origin {
    /// `query_module`, or [`STORAGE_CRATE`] (its files are `storage_interface` or `storage_builder`).
    kind: &'static str,
    /// The directory under `admitted-code/` (readable name plus a short package id).
    directory: String,
    /// What it implements: the statement's SQL, or the storage's name and package.
    about: Value,
}

/// The records of a general engine line run whose versions and verified attempts the index covers.
pub struct EngineRecords<'a> {
    /// `<run>/engine`.
    pub engine_dir: &'a Path,
}

/// Write the index of every admitted author source of `store`, then of each `reuse` library, that the run's storage
/// `policy` allows into `workspace`; returns the index file. A storage the policy makes ineligible (excluded by the
/// user's review, or not registered under the policy) and a query package that reads one are left out.
pub fn write_search_index(store: &ObjectStore, reuse: &[ReuseLibrary<'_>], workspace: &Path, policy: &StoredDataPolicy) -> Result<PathBuf, AdmissionError> {
    write_index(store, reuse, None, workspace, policy)
}

/// [`write_search_index`] of a general engine line run: the admitted code first, then every version's and every
/// verified attempt's agent modules from `engine`'s records (module documentation).
pub fn write_engine_search_index(store: &ObjectStore, reuse: &[ReuseLibrary<'_>], engine: &EngineRecords<'_>, workspace: &Path, policy: &StoredDataPolicy) -> Result<PathBuf, AdmissionError> {
    write_index(store, reuse, Some(engine), workspace, policy)
}

fn write_index(store: &ObjectStore, reuse: &[ReuseLibrary<'_>], engine: Option<&EngineRecords<'_>>, workspace: &Path, policy: &StoredDataPolicy) -> Result<PathBuf, AdmissionError> {
    let code_root = workspace.join(CODE_DIRECTORY);
    let mut entries = vec![];
    let mut seen_builds = BTreeSet::new();
    let mut own_builds = BTreeSet::new();
    let libraries = std::iter::once((None, store)).chain(reuse.iter().map(|r| (Some(r.label()), r.store)));
    for (reuse_library, library) in libraries {
        for (build, mut origin) in admitted_builds(library, policy)? {
            if reuse_library.is_some() && own_builds.contains(&build) {
                continue;
            }
            if !seen_builds.insert((build, origin.directory.clone())) {
                continue;
            }
            if let Some(label) = &reuse_library {
                origin.about["reuse_library"] = json!(label);
            } else {
                own_builds.insert(build);
            }
            let Ok(evidence) = records::check_build_evidence(library, build) else { continue };
            for source in evidence.sources.iter().filter(|s| s.owner == VerusSourceOwnerV1::Agent) {
                let bytes = library.read_blob(source.blob, Some(source.bytes)).map_err(AdmissionError::tool)?;
                let text = String::from_utf8(bytes).map_err(AdmissionError::tool)?;
                let local = code_root.join(&origin.directory).join(&source.path);
                write_read_only(&local, &text)?;
                entries.push(entry(&origin, &source.path, &local, &text));
            }
        }
    }
    if let Some(engine) = engine {
        entries.extend(engine_entries(engine, &code_root)?);
    }
    let reuse_note = if reuse.is_empty() {
        String::new()
    } else {
        format!(". Entries whose origin names a reuse_library ({}) come from a library offered read-only for reuse: their code is for reading and adapting only, it is not admitted in your run's library, never served and never counted in your storage budget; per-query programs there may name their query's constants, which your own rules may refuse",
            reuse.iter().map(ReuseLibrary::label).collect::<Vec<_>>().join(", "))
    };
    let root_sides_note = if entries.iter().any(|e| e["origin"]["status"] == ROOT_SIDE || e["origin"]["status"] == COMMON_ANCESTOR) { ROOT_SIDES_NOTE } else { "" };
    let index = workspace.join(INDEX_FILE);
    write(&index, &json!({"format_version":1,"entries":entries,
        "use":format!("every admitted author source (query modules, storage interfaces and builders), copied read-only under admitted-code/; general = a module under a common/ directory (a specification without query constants). Search by name, description or specification (grep the one-line-per-item search-index.txt), then read the file; copy a module as-is or adapt it into your own crate, where Verus checks it again. Nothing is composed automatically{reuse_note}{}{}",
            if engine.is_some() { ENGINE_NOTE } else { "" }, root_sides_note)}))?;
    let lines: Vec<String> = entries.iter().flat_map(index_lines).collect();
    fs::write(workspace.join(INDEX_TEXT_FILE), lines.join("\n") + "\n").map_err(AdmissionError::tool)?;
    Ok(index)
}

/// One file's index entry.
fn entry(origin: &Origin, path: &str, local: &Path, text: &str) -> Value {
    let doc = module_doc(text);
    let description = doc.split(". ").next().unwrap_or_default().trim_end_matches('.').to_string();
    let items: Vec<Value> = public_items(path, text, true)["items"]
        .as_array()
        .into_iter()
        .flatten()
        .filter(|item| item["kind"] != "re-export")
        .map(|item| json!({"kind":item["kind"],"name":item["name"],"line":item["line"],"signature":item.get("signature").or(item.get("text")),
            "requires":item["requires"],"ensures":item["ensures"],"doc":item["doc"]}))
        .collect();
    let kind = match origin.kind {
        STORAGE_CRATE if path.starts_with("builder/") => "storage_builder",
        STORAGE_CRATE => "storage_interface",
        other => other,
    };
    json!({"kind":kind,"general":path.split('/').any(|part| part == "common"),"origin":origin.about,"path":path,"file":local,
        "description":description,"items":items})
}

/// The grep-able lines of one entry: `<file>:<line>\t<kind> <name>\t<module description>\t<signature>`; the module line
/// is marked `general` for a general module and `reuse` for a reuse library's file.
fn index_lines(entry: &Value) -> Vec<String> {
    let file = entry["file"].as_str().unwrap_or_default();
    let description = entry["description"].as_str().unwrap_or_default();
    let general = if entry["general"] == true { "general " } else { "" };
    let reuse = if entry["origin"]["reuse_library"].is_string() { "reuse " } else { "" };
    let unaccepted = if entry["origin"]["status"] == VERIFIED_NOT_ACCEPTED { "verified-not-accepted " } else { "" };
    let root_side = if entry["origin"]["status"] == ROOT_SIDE || entry["origin"]["status"] == COMMON_ANCESTOR { "root-side " } else { "" };
    let mut lines = vec![format!("{file}:1\t{reuse}{unaccepted}{root_side}{general}{} module\t{description}", entry["kind"].as_str().unwrap_or_default())];
    for item in entry["items"].as_array().into_iter().flatten() {
        let signature = item["signature"].as_str().unwrap_or_default().replace('\n', " ");
        lines.push(format!("{file}:{}\t{} {}\t{description}\t{signature}", item["line"], item["kind"].as_str().unwrap_or_default(), item["name"].as_str().unwrap_or_default()));
    }
    lines
}

/// The index's note on a general engine line run's engine entries.
const ENGINE_NOTE: &str = ". Entries of kind engine_module are the agent modules of this run's engine versions (origin.status accepted version) and of attempts that passed Verus on the whole crate but were not accepted (verified, not accepted), with their branch, version, direction, score and measured effect; their code is verified in its own crate only, so a copy is checked again in yours";
/// The index's note on a run of several workloads' root-side entries (added after [`ENGINE_NOTE`] when it has some).
const ROOT_SIDES_NOTE: &str = ". In a run of several workloads, entries with origin.status root side are the code of the root's other sides (its shared engine, modules, families and plans; origin.workload) and seeds' common ancestor the code of the version every seeded side descends from: verified sides of v000, read-only";
/// `origin.status` of an accepted version's module.
const ACCEPTED_VERSION: &str = "accepted version";
/// `origin.status` of a verified attempt's module.
const VERIFIED_NOT_ACCEPTED: &str = "verified, not accepted";
/// `origin.status` of a root side's module (a run of several workloads).
const ROOT_SIDE: &str = "root side";
/// `origin.status` of the seeds' common ancestor's module (a run of several workloads).
const COMMON_ANCESTOR: &str = "seeds' common ancestor";

/// The engine entries of a general-line run (module documentation): every version's agent modules, then every verified
/// attempt's, copied read-only under `admitted-code/engine-<id>/`.
fn engine_entries(engine: &EngineRecords<'_>, code_root: &Path) -> Result<Vec<Value>, AdmissionError> {
    let tree = crate::engine::tree::VersionTree::read(engine.engine_dir).map_err(AdmissionError::tool)?;
    let effects: BTreeMap<String, Value> = crate::engine::tree::read_lines(&engine.engine_dir.join(crate::engine::tree::FINDINGS_FILE))
        .map_err(AdmissionError::tool)?
        .into_iter()
        .filter_map(|f| Some((f["node"].as_str()?.to_string(), f)))
        .collect();
    let mut entries = vec![];
    for node in tree.versions().chain(tree.attempts()) {
        let folder = node.directory(engine.engine_dir);
        if !node.accepted && !verified_attempt(&folder) {
            continue;
        }
        let finding = effects.get(&node.id);
        let about = json!({"engine_version":node.id,"status":if node.accepted { ACCEPTED_VERSION } else { VERIFIED_NOT_ACCEPTED },"branch":node.branch,"kind":node.kind,
            "parents":node.parents,"direction":node.direction,"score":node.score.as_ref().map(|s| format!("{}: F {}/{}, G {}", s.scale, s.score.finished, s.cells, s.score.normalized_time)),
            "effect":finding.map(|f| &f["effect"]),"findings":finding.map(|f| &f["findings"]),"reason":node.reason,"folder":folder});
        let origin = Origin { kind: "engine_module", directory: format!("engine-{}", node.id), about };
        let agent = folder.join("code");
        let mut files = vec![];
        collect_files(&agent.join("agent"), &mut files);
        files.sort();
        for file in files {
            let relative = file.strip_prefix(&agent).unwrap_or(&file).display().to_string();
            let text = fs::read_to_string(&file).map_err(AdmissionError::tool)?;
            let local = code_root.join(&origin.directory).join(&relative);
            write_read_only(&local, &text)?;
            entries.push(entry(&origin, &relative, &local, &text));
        }
    }
    entries.extend(root_side_entries(engine, code_root)?);
    Ok(entries)
}

/// The engine entries of the root's other sides and of the seeds' common ancestor in a run of several workloads (module
/// documentation): every `.rs` file of `versions/v000/root-sides/<name>/code/`, copied read-only under
/// `admitted-code/engine-v000-<name>/`; none in any other run.
fn root_side_entries(engine: &EngineRecords<'_>, code_root: &Path) -> Result<Vec<Value>, AdmissionError> {
    let sides = crate::engine::tree::node_directory(engine.engine_dir, crate::engine::tree::ROOT_VERSION, true).join(crate::engine::stage::root::ROOT_SIDES_DIRECTORY);
    let mut names: Vec<String> = fs::read_dir(&sides).into_iter().flatten().flatten().filter(|e| e.path().is_dir()).map(|e| e.file_name().to_string_lossy().into_owned()).collect();
    names.sort();
    let mut entries = vec![];
    for name in names {
        let folder = sides.join(&name);
        let ancestor = name == crate::engine::stage::root::ANCESTOR_DIRECTORY;
        let about = json!({"engine_version":crate::engine::tree::ROOT_VERSION,"status":if ancestor { COMMON_ANCESTOR } else { ROOT_SIDE },"workload":if ancestor { Value::Null } else { json!(name) },
            "kind":"workload_seed","folder":folder});
        let origin = Origin { kind: "engine_module", directory: format!("engine-{}-{name}", crate::engine::tree::ROOT_VERSION), about };
        let code = folder.join("code");
        let mut files = vec![];
        collect_files(&code, &mut files);
        files.sort();
        for file in files {
            let relative = file.strip_prefix(&code).unwrap_or(&file).display().to_string();
            let text = fs::read_to_string(&file).map_err(AdmissionError::tool)?;
            let local = code_root.join(&origin.directory).join(&relative);
            write_read_only(&local, &text)?;
            entries.push(entry(&origin, &relative, &local, &text));
        }
    }
    Ok(entries)
}

/// Whether an attempt passed Verus on the whole crate: its evaluation's whole-crate run (`attempt.json` names the
/// evaluation directory; `verus-build/run.json`) reports success with 0 errors.
fn verified_attempt(folder: &Path) -> bool {
    let read = |path: &Path| fs::read_to_string(path).ok().and_then(|t| serde_json::from_str::<Value>(&t).ok());
    let Some(attempt) = read(&folder.join("attempt.json")) else { return false };
    let Some(run) = attempt["evaluation"].as_str().and_then(|dir| read(&Path::new(dir).join("verus-build/run.json"))) else { return false };
    let verification = &run["verification"];
    verification["success"] == true && verification["errors"] == 0 && verification["is-verifying-entire-crate"] == true
}

/// Every `.rs` file under `dir` (none when it does not exist).
fn collect_files(dir: &Path, found: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(dir).into_iter().flatten().flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_files(&path, found);
        } else if path.extension().is_some_and(|e| e == "rs") {
            found.push(path);
        }
    }
}

/// Every admitted build with author sources the storage `policy` allows: the implementations of admitted query packages
/// over stored data, and the builds of admitted storage packages.
fn admitted_builds(store: &ObjectStore, policy: &StoredDataPolicy) -> Result<Vec<(ContentId, Origin)>, AdmissionError> {
    let mut builds = vec![];
    for object in store.list_kind(records::VERUS_PACKAGE_ADMISSION_V2_KIND).map_err(AdmissionError::tool)? {
        let admission: VerusPackageAdmissionV2 = object.decode().map_err(AdmissionError::tool)?;
        let package: VerusQueryPackageV3 = store.read(admission.package).and_then(|o| o.decode()).map_err(AdmissionError::tool)?;
        if policy.ineligible_use(store, package.storage_uses.iter().map(|u| (u.name.as_str(), u.package)))?.is_some() {
            continue;
        }
        let sql = store.read(package.claim).and_then(|o| o.decode::<Value>()).map_err(AdmissionError::tool)?["sql"].clone();
        for implementation in &package.implementations {
            let record: VerusImplementationV1 = store.read(*implementation).and_then(|o| o.decode()).map_err(AdmissionError::tool)?;
            let directory = format!("query@{}", &admission.package.to_hex()[..8]);
            builds.push((record.build, Origin { kind: "query_module", directory, about: json!({"sql":sql,"package":admission.package}) }));
        }
    }
    for object in store.list_kind(VERUS_STORAGE_ADMISSION_KIND).map_err(AdmissionError::tool)? {
        let admission: VerusStorageAdmissionV1 = object.decode().map_err(AdmissionError::tool)?;
        let package: VerusStoragePackageV1 = store.read(admission.package).and_then(|o| o.decode()).map_err(AdmissionError::tool)?;
        if policy.ineligible(store, admission.package, &package.name)?.is_some() {
            continue;
        }
        let directory = format!("{}@{}", package.name, &admission.package.to_hex()[..8]);
        let about = json!({"storage":package.name,"package":admission.package,"tables":package.tables.iter().map(|t| &t.table).collect::<Vec<_>>()});
        builds.push((package.build, Origin { kind: STORAGE_CRATE, directory, about }));
    }
    Ok(builds)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The index of a library without admitted code, and one indexed author file, as the schema-engine and query
    /// contracts render them.
    fn schema_line_index_texts() -> String {
        let root = crate::controller::test_support::scratch_root("search-index-golden");
        let store = ObjectStore::open(root.join("library")).unwrap();
        let workspace = root.join("workspace");
        fs::create_dir_all(&workspace).unwrap();
        let index = write_search_index(&store, &[], &workspace, &StoredDataPolicy::default()).unwrap();
        let mut text = fs::read_to_string(&index).unwrap().replace(&root.display().to_string(), "<root>");
        text.push_str(&fs::read_to_string(workspace.join(INDEX_TEXT_FILE)).unwrap());
        let origin = Origin { kind: "query_module", directory: "query@00000000".into(), about: json!({"sql":"SELECT 1","package":"p"}) };
        let source = "//! Hash join over two key columns. Builds on the smaller side.\nuse vstd::prelude::*;\nverus! {\n/// Probe one key.\npub fn probe(k: u64) -> (r: bool)\n    ensures r == (k > 0),\n{ k > 0 }\n}\n";
        let entry = entry(&origin, "common/join.rs", Path::new("/w/admitted-code/query@00000000/common/join.rs"), source);
        text.push_str(&serde_json::to_string_pretty(&entry).unwrap());
        text.push_str(&index_lines(&entry).join("\n"));
        fs::remove_dir_all(&root).ok();
        text
    }

    /// Golden: the schema-engine (and query) search index renders byte for byte as before the general line's engine
    /// entries were added (digest recorded with the unchanged index code).
    #[test]
    fn the_schema_line_search_index_renders_as_before() {
        let text = schema_line_index_texts();
        assert_eq!(crate::prompts::engine_policy::tests::sha256_hex(&text), SCHEMA_INDEX_GOLDEN, "the search index changed:\n{text}");
    }

    const SCHEMA_INDEX_GOLDEN: &str = "ba6fe10c0d082d32b0c0cdc35de700b8b6e77cd9182e1d507d3787be20936ee4";

    /// A general-line index covers every version of every branch and the verified attempt (marked), not the refused
    /// one, each with its branch, version, direction and measured effect.
    #[test]
    fn the_engine_index_covers_versions_and_verified_attempts() {
        let root = crate::controller::test_support::scratch_root("search-index-engine");
        let run = crate::prompts::engine_facts::general::tests::scripted_run(&root.join("run"));
        let store = ObjectStore::open(root.join("library")).unwrap();
        let workspace = root.join("workspace");
        fs::create_dir_all(&workspace).unwrap();
        let index = write_engine_search_index(&store, &[], &EngineRecords { engine_dir: &run.engine_dir }, &workspace, &StoredDataPolicy::default()).unwrap();
        let index: Value = serde_json::from_str(&fs::read_to_string(index).unwrap()).unwrap();
        let entries = index["entries"].as_array().unwrap();
        let versions: Vec<&str> = entries.iter().map(|e| e["origin"]["engine_version"].as_str().unwrap()).collect();
        assert_eq!(versions, ["v000", "v001", "b1-a001"], "every version, the verified attempt, not the refused one");
        let attempt = &entries[2];
        assert_eq!((attempt["kind"].as_str(), attempt["origin"]["status"].as_str(), attempt["origin"]["branch"].as_str()), (Some("engine_module"), Some(VERIFIED_NOT_ACCEPTED), Some("b1")));
        assert_eq!(entries[1]["origin"]["effect"]["finished"], 9);
        assert!(entries[1]["items"].as_array().unwrap().iter().any(|i| i["name"] == "hash_join"));
        assert!(workspace.join(CODE_DIRECTORY).join("engine-v001/agent/mod.rs").is_file());
        let text = fs::read_to_string(workspace.join(INDEX_TEXT_FILE)).unwrap();
        assert!(text.contains("verified-not-accepted engine_module module\tRadix-partitioned hash joins (slower here)"), "{text}");
        assert!(index["use"].as_str().unwrap().ends_with(ENGINE_NOTE));
        fs::remove_dir_all(&root).ok();
    }
}
