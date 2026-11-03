//! `gendb engine export RUN_DIR VERSION OUT` (the stage fixture): the engine source of one
//! accepted version of a general-line run, as a folder a later run names as a seed (`engine.workloads` `seed: {"source":
//! OUT}`; `engine::submission::members::write_source_root` reads it) and a user reads:
//! - `agent/**`: the shared engine (the version's `code/agent/**`);
//! - `workloads/default/**`: the shared default workload module, when the version has one;
//! - `storages/<family>/**`: every storage family's source (`verus-family.json`, `default_plan.rs`, builder, interface);
//! - `plans/<workload>/<family>.rs`: the workloads' plans (a new workload has none and gets each family's default plan);
//! - `manifest.json` (`engine::submission::members::EXPORT_MANIFEST_FILE`): the version's manifest as the engine's
//!   source states it: its modules, compiler and notes, the families at their folder paths and the default module's
//!   declarations; no storage use and no workload entry (those name packages of the exporting run's libraries);
//! - `README.md`: what the folder holds, how a run seeds from it, and per workload of the version its proof and its
//!   admission (library, package id), from the version's `version.json`;
//! - `export.json`: the record (the run, the version, every file with its bytes and SHA-256, the version's one-engine
//!   record).
//!
//! An own module of a workload (`code/workloads/<name>/`) is not exported: it opens storages of the exporting run's
//! libraries. The run's records are only read; `OUT` must not exist (the folder is staged beside it and renamed once
//! complete). No Verus runs here: a seed from the folder is frozen, verified and checked again by the run that names it.
//!
//! Trust: none in proofs; copying files and writing records.

use super::submission::members::{EXPORT_MANIFEST_FILE, VERSION_FAMILIES_DIRECTORY, WORKSPACE_FAMILIES_DIRECTORY};
use super::submission::{DEFAULT_WORKLOAD, EngineManifest, FamilyDeclaration, PLANS_DIRECTORY, WORKLOADS_DIRECTORY};
use super::tree::{NODE_FILE, VersionTree, node_directory};
use crate::controller::records::{now_unix_ms, read_json};
use crate::storage::family::FAMILY_MANIFEST_FILE;
use gendb_verification::admission::AdmissionError;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::fs;
use std::path::{Path, PathBuf};

/// The export's record file in the exported folder.
pub const EXPORT_RECORD_FILE: &str = "export.json";

/// Export the accepted version `version` of the run `run_dir` into the new folder `out` (module documentation). Returns
/// the export record (also `out/export.json`).
pub fn export_version(run_dir: &Path, version: &str, out: &Path) -> Result<Value, AdmissionError> {
    let root = run_dir.canonicalize().map_err(|e| AdmissionError::missing_input(format!("{}: {e}", run_dir.display())))?;
    let engine_dir = root.join("engine");
    let tree = VersionTree::read(&engine_dir).map_err(AdmissionError::tool)?;
    if tree.version(version).is_none() {
        return Err(AdmissionError::missing_input(format!("{version} is not an accepted version of the run {}", root.display())));
    }
    let folder = node_directory(&engine_dir, version, true);
    if !folder.join(NODE_FILE).is_file() || !folder.join("code/agent/mod.rs").is_file() {
        return Err(AdmissionError::missing_input(format!("{}: not a complete version folder with code/agent/mod.rs", folder.display())));
    }
    if fs::symlink_metadata(out).is_ok() {
        return Err(AdmissionError::missing_input(format!("{} exists: the export writes a new folder", out.display())));
    }
    let parent = out.parent().filter(|p| !p.as_os_str().is_empty()).unwrap_or(Path::new("."));
    fs::create_dir_all(parent).map_err(|e| AdmissionError::tool(format!("{}: {e}", parent.display())))?;
    let name = out.file_name().map(|n| n.to_string_lossy().into_owned()).ok_or_else(|| AdmissionError::missing_input(format!("{}: no folder name", out.display())))?;
    let staging = parent.join(format!(".{name}.staging-{}", now_unix_ms()));
    let outcome = write_export(&root, version, &folder, &staging, out);
    match outcome {
        Ok(record) => {
            fs::rename(&staging, out).map_err(|e| AdmissionError::tool(format!("{} -> {}: {e}", staging.display(), out.display())))?;
            Ok(record)
        }
        Err(error) => {
            let _ = fs::remove_dir_all(&staging);
            Err(error)
        }
    }
}

/// The folder's files (module documentation) into `staging`; every recorded path names `out`.
fn write_export(root: &Path, version: &str, folder: &Path, staging: &Path, out: &Path) -> Result<Value, AdmissionError> {
    let code = folder.join("code");
    copy_tree(&code.join("agent"), &staging.join("agent"))?;
    let default_module = code.join(WORKLOADS_DIRECTORY).join(DEFAULT_WORKLOAD);
    if default_module.is_dir() {
        copy_tree(&default_module, &staging.join(WORKLOADS_DIRECTORY).join(DEFAULT_WORKLOAD))?;
    }
    if code.join(PLANS_DIRECTORY).is_dir() {
        copy_tree(&code.join(PLANS_DIRECTORY), &staging.join(PLANS_DIRECTORY))?;
    }
    let manifest_file = ["seed-manifest.json", "manifest.json"].into_iter().map(|f| folder.join(f)).find(|p| p.is_file())
        .ok_or_else(|| AdmissionError::missing_input(format!("{}: no manifest", folder.display())))?;
    let manifest: EngineManifest = read_json(&manifest_file).map_err(AdmissionError::tool)?;
    let mut families = vec![];
    for family in &manifest.families {
        let source = code.join(VERSION_FAMILIES_DIRECTORY).join(&family.name);
        if !source.join(FAMILY_MANIFEST_FILE).is_file() {
            return Err(AdmissionError::missing_input(format!("family {}: {} has no {FAMILY_MANIFEST_FILE}", family.name, source.display())));
        }
        copy_tree(&source, &staging.join(WORKSPACE_FAMILIES_DIRECTORY).join(&family.name))?;
        families.push(FamilyDeclaration { name: family.name.clone(), source: Path::new(WORKSPACE_FAMILIES_DIRECTORY).join(&family.name).join(FAMILY_MANIFEST_FILE) });
    }
    // The engine's source only: the storage uses and workload entries name packages of the exporting run's libraries.
    let exported = EngineManifest { storage_uses: vec![], workloads: vec![], families, ..manifest.for_seed() };
    fs::write(staging.join(EXPORT_MANIFEST_FILE), format!("{}\n", serde_json::to_string_pretty(&exported).map_err(AdmissionError::tool)?)).map_err(AdmissionError::tool)?;
    let record_of: Value = read_json(&folder.join("version.json")).unwrap_or(Value::Null);
    let proofs = workload_proofs(&record_of);
    fs::write(staging.join("README.md"), readme(root, version, &exported, &proofs, &record_of["general"])).map_err(AdmissionError::tool)?;
    let mut files = vec![];
    for file in tree_files(staging)? {
        let bytes = fs::read(staging.join(&file)).map_err(AdmissionError::tool)?;
        files.push(json!({"file":file,"bytes":bytes.len(),"sha256":Sha256::digest(&bytes).iter().map(|b| format!("{b:02x}")).collect::<String>()}));
    }
    let record = json!({"format_version":1,"run":root,"version":version,"folder":out,"files":files,"workloads":proofs,"general":record_of["general"],
        "families":exported.families.iter().map(|f| &f.name).collect::<Vec<_>>(),"default_module":default_module.is_dir(),"exported_unix_ms":now_unix_ms(),
        "seed":{"source":out},"meaning":"the engine source of one accepted version: a later run names it as a seed (engine.workloads seed {\"source\": <this folder>}) and verifies it again; nothing here is evidence by itself"});
    fs::write(staging.join(EXPORT_RECORD_FILE), format!("{}\n", serde_json::to_string_pretty(&record).map_err(AdmissionError::tool)?)).map_err(AdmissionError::tool)?;
    Ok(record)
}

/// Every workload's proof and admission of the version (`version.json` `workloads.<name>`; a version of one workload has
/// its own `proof` and `admission`), as `{workload, role, proof, admission}`.
fn workload_proofs(version: &Value) -> Vec<Value> {
    match version["workloads"].as_object() {
        Some(workloads) => workloads
            .iter()
            .map(|(name, w)| json!({"workload":name,"role":w["role"],"proof":w["proof"],"admission":w["admission"]}))
            .collect(),
        None => vec![json!({"workload":null,"role":null,"proof":{"errors":version["proof"]["verification"]["errors"],"verified":version["proof"]["verification"]["verified"],"wall_ns":version["proof"]["wall_ns"]},
            "admission":{"package":version["admission"]["package"],"library_version":version["admission"]["library_version"]}})],
    }
}

/// `README.md` of the exported folder.
fn readme(root: &Path, version: &str, manifest: &EngineManifest, proofs: &[Value], general: &Value) -> String {
    let text = |v: &Value| v.as_str().map_or_else(|| v.to_string(), str::to_string);
    let mut out = format!(
        "# Exported engine: version {version} of `{}`\n\nThe engine source of one accepted version of a general-line run (written by `gendb engine export`):\n\n- `agent/`: the shared engine;\n- `{WORKLOADS_DIRECTORY}/{DEFAULT_WORKLOAD}/`: the shared default workload module{};\n- `{WORKSPACE_FAMILIES_DIRECTORY}/<family>/`: the storage families ({});\n- `{PLANS_DIRECTORY}/<workload>/<family>.rs`: the workloads' plans (a new workload uses each family's default plan);\n- `{EXPORT_MANIFEST_FILE}`: its manifest (modules, compiler, notes, families, default module; no storage use);\n- `{EXPORT_RECORD_FILE}`: every file with its SHA-256.\n\nA run seeds a workload's side from this folder with `\"seed\": {{\"source\": \"<this folder>\"}}` in `engine.workloads`: GenDB writes the side's workspace from it (`write_source_root`), freezes it for that workload's schema, verifies the whole crate again and checks it (version 0 is the fallback when it does not verify there).\n\n## Proofs and admissions in the exporting run\n\n| Workload | Role | Verus errors | Verified items | Library | Package |\n|---|---|---:|---:|---|---|\n",
        root.display(),
        if manifest.default_modules.is_empty() { " (none in this version)" } else { "" },
        if manifest.families.is_empty() { "none in this version".to_string() } else { manifest.families.iter().map(|f| format!("`{}`", f.name)).collect::<Vec<_>>().join(", ") },
    );
    for p in proofs {
        out.push_str(&format!("| {} | {} | {} | {} | {} | {} |\n", text(&p["workload"]), text(&p["role"]), text(&p["proof"]["errors"]), text(&p["proof"]["verified"]),
            text(&p["admission"]["library"]), text(&p["admission"]["package"])));
    }
    if general.is_object() {
        out.push_str(&format!("\nOne engine: {} (own modules: {}; inherited storages: {}).\n", text(&general["one_engine"]), text(&general["own_modules"]), text(&general["inherited_storages"])));
    }
    out.push_str("\nThese records are of the exporting run; a run that seeds from this folder proves and checks its own crates.\n");
    out
}

/// Copy the tree `from` to `to` (directories and regular files; symbolic links skipped), file bytes unchanged and every
/// copy writable (the version folder keeps the frozen crate's read-only modes; the exported copy is the user's).
fn copy_tree(from: &Path, to: &Path) -> Result<(), AdmissionError> {
    super::role::copy_tree(from, to, false)?;
    super::role::make_writable(to)
}

/// Every file under `dir`, relative to it, sorted.
fn tree_files(dir: &Path) -> Result<Vec<PathBuf>, AdmissionError> {
    let mut found = vec![];
    let mut stack = vec![PathBuf::new()];
    while let Some(relative) = stack.pop() {
        for entry in fs::read_dir(dir.join(&relative)).map_err(AdmissionError::tool)? {
            let entry = entry.map_err(AdmissionError::tool)?;
            let path = relative.join(entry.file_name());
            if entry.file_type().map_err(AdmissionError::tool)?.is_dir() {
                stack.push(path);
            } else {
                found.push(path);
            }
        }
    }
    found.sort();
    Ok(found)
}
