//! Verus runs over a frozen crate of either kind (a query crate `gendb_query` or a storage crate `gendb_store`): the
//! whole-crate verification (local `verify`), the one verify-and-compile run whose record is evidence (`compile`), the
//! module-scoped diagnostic verification and the unverified diagnostic build of a query crate (`compile_unverified`,
//! authors' `verification: "not_run"` trials); the last two are never evidence. Each run holds the host activity lease and writes
//! `<out>/run.json` (`VerusRun::record`). After a compiling run, every declared item must be one of the functions
//! Verus reported.

use super::candidate::CompilerChoice;
use super::host_locks::HostLocks;
use super::source_items::{ItemSource, describe_item, spec_clauses};
use crate::controller::records::write_new_json;
use gendb_artifacts::verus::VerusItemV1;
use gendb_registry::CrateKind;
use gendb_verification::admission::qualification::CandidateModule;
use gendb_verification::admission::{AdmissionError, FailureClass};
use gendb_verification::obligations::{CANDIDATE_CRATE_NAME, ENGINE_CRATE_NAME, STORAGE_CRATE_NAME};
use gendb_verification::verus::{self, CodegenOptions, FrozenCrate, VerusMode, VerusOptions, VerusRun, VerusToolchain};
use serde_json::{Value, json};
use std::fs;
use std::path::{Path, PathBuf};

/// Verus solver threads of every author crate run (verification speed only).
const VERUS_THREADS: u32 = 8;

/// The failure class named `name` (Verus and toolchain errors report the author-contract names).
fn class_named(name: &str) -> FailureClass {
    FailureClass::ALL.into_iter().find(|class| class.name() == name).unwrap_or(FailureClass::ToolFailure)
}

/// The Verus `--crate-name` of a crate kind.
pub fn crate_name(kind: CrateKind) -> &'static str {
    match kind {
        CrateKind::Query => CANDIDATE_CRATE_NAME,
        CrateKind::Storage => STORAGE_CRATE_NAME,
        CrateKind::Engine => ENGINE_CRATE_NAME,
    }
}

/// The Verus options of an author crate with the author's code generation choice.
pub fn crate_options(kind: CrateKind, choice: &CompilerChoice) -> VerusOptions {
    VerusOptions {
        crate_name: crate_name(kind).into(),
        codegen: CodegenOptions { opt_level: choice.opt_level, target_cpu: choice.target_cpu.clone() },
        num_threads: Some(VERUS_THREADS),
    }
}

fn toolchain() -> Result<VerusToolchain, AdmissionError> {
    VerusToolchain::from_env().map_err(|e| AdmissionError::new(class_named(e.failure_class()), e))
}

/// Write the run record; a run that did not verify (or compile) is an error of its outcome's class carrying the
/// verbatim diagnostics.
fn settle(run: VerusRun, out: &Path, scope: Option<&[String]>) -> Result<(Value, VerusRun), AdmissionError> {
    let mut record = run.record();
    if let Some(modules) = scope {
        record["scope"] = json!(modules);
    }
    write_new_json(&out.join("run.json"), &record).map_err(AdmissionError::tool)?;
    if let Some(class) = run.outcome.failure_class() {
        let scope = scope.map(|modules| format!(" (modules {modules:?})")).unwrap_or_default();
        return Err(AdmissionError::new(class_named(class), format!("Verus {}{scope}: {}\n{}", json!(run.outcome), run.detail, run.rendered_errors())));
    }
    Ok((record, run))
}

/// One whole-crate verification (no library).
pub fn verify(locks: &HostLocks, krate: &FrozenCrate, kind: CrateKind, choice: &CompilerChoice, out: &Path) -> Result<Value, AdmissionError> {
    let toolchain = toolchain()?;
    let _lease = locks.activity().map_err(AdmissionError::tool)?;
    let run = verus::run_verus(&toolchain, krate, &crate_options(kind, choice), VerusMode::Verify, out).map_err(|e| AdmissionError::new(class_named(e.failure_class()), e))?;
    settle(run, out, None).map(|(record, _)| record)
}

/// The one whole-crate verify-and-compile run: its record and the compiled library of that same directory.
pub fn compile(locks: &HostLocks, krate: &FrozenCrate, kind: CrateKind, choice: &CompilerChoice, out: &Path) -> Result<(Value, PathBuf), AdmissionError> {
    let toolchain = toolchain()?;
    let _lease = locks.activity().map_err(AdmissionError::tool)?;
    let run = verus::run_verus(&toolchain, krate, &crate_options(kind, choice), VerusMode::VerifyAndCompile, out)
        .map_err(|e| AdmissionError::new(class_named(e.failure_class()), e))?;
    let (record, run) = settle(run, out, None)?;
    let library = run.artifact.ok_or_else(|| AdmissionError::tool("Verus compiled without a library"))?;
    Ok((record, library))
}

/// Diagnostic build of the whole crate without proof checking (`rust_verify --no-verify`): its record and library.
/// Never evidence; the caller labels every result of this library `diagnostic_unverified`.
pub fn compile_unverified(locks: &HostLocks, krate: &FrozenCrate, kind: CrateKind, choice: &CompilerChoice, out: &Path) -> Result<(Value, PathBuf), AdmissionError> {
    let toolchain = toolchain()?;
    let _lease = locks.activity().map_err(AdmissionError::tool)?;
    let run = verus::compile_unverified(&toolchain, krate, &crate_options(kind, choice), out).map_err(|e| AdmissionError::new(class_named(e.failure_class()), e))?;
    let (record, run) = settle(run, out, None)?;
    let library = run.artifact.ok_or_else(|| AdmissionError::tool("unverified build without a library"))?;
    Ok((record, library))
}

/// Diagnostic verification of only `modules` and their descendants (never evidence).
pub fn verify_modules(locks: &HostLocks, krate: &FrozenCrate, kind: CrateKind, choice: &CompilerChoice, modules: &[String], out: &Path) -> Result<Value, AdmissionError> {
    let toolchain = toolchain()?;
    let _lease = locks.activity().map_err(AdmissionError::tool)?;
    // An invalid scope is missing_input (the request names it); an output-directory failure is the tool's.
    let run = verus::verify_modules(&toolchain, krate, &crate_options(kind, choice), modules, out)
        .map_err(|e| AdmissionError::new(class_named(e.failure_class()), e))?;
    settle(run, out, Some(modules)).map(|(record, _)| record)
}

/// One declared author module of a frozen crate.
#[derive(Clone, Debug)]
pub struct DeclaredModule {
    /// Relative to the crate's `src/` (`agent/mod.rs`, `stores/x/interface/mod.rs`, `builder/mod.rs`).
    pub file: String,
    pub role: String,
    pub items: Vec<String>,
}

/// Crate module path of a file relative to `src/` (`agent/mod.rs` -> `agent`, `stores/x/interface/zone.rs` ->
/// `stores::x::interface::zone`).
pub fn module_path(file: &str) -> Result<String, AdmissionError> {
    let stem = file.strip_suffix(".rs").ok_or_else(|| AdmissionError::refusal(format!("module {file} is not a .rs file")))?;
    let mut parts: Vec<&str> = stem.split('/').collect();
    if parts.len() > 1 && parts.last() == Some(&"mod") {
        parts.pop();
    }
    Ok(parts.join("::"))
}

/// Every source of a frozen crate, for contract resolution.
fn frozen_sources(krate: &FrozenCrate) -> Result<Vec<ItemSource>, AdmissionError> {
    krate
        .framework_files
        .iter()
        .chain(&krate.author_files)
        .map(|path| {
            let file = krate.root.join("src").join(path);
            let text = fs::read_to_string(&file).map_err(|e| AdmissionError::tool(format!("{}: {e}", file.display())))?;
            Ok(ItemSource { provenance: json!({"path":path,"file":file}), path: path.clone(), text })
        })
        .collect()
}

/// Every declared item must be one of the functions Verus reported for this crate (`func-details` of the run's
/// `--output-json` stdout). The records carry each item's own clause text and its effective checked contract.
pub fn declared_items(modules: &[DeclaredModule], krate: &FrozenCrate, kind: CrateKind, verus_stdout: &str) -> Result<Vec<Value>, AdmissionError> {
    let output: Value = serde_json::from_str(verus_stdout.trim()).map_err(AdmissionError::tool)?;
    let reported = output["func-details"].as_object().ok_or_else(|| AdmissionError::tool("Verus output lacks func-details"))?;
    let sources = frozen_sources(krate)?;
    let crate_name = crate_name(kind);
    let mut items = vec![];
    for module in modules {
        let source = &sources.iter().find(|s| s.path == module.file).ok_or_else(|| AdmissionError::tool(format!("{} absent from the frozen crate", module.file)))?.text;
        let module_path = module_path(&module.file)?;
        for item in &module.items {
            let full = format!("{crate_name}::{module_path}::{item}");
            if !reported.contains_key(&full) {
                return Err(AdmissionError::refusal(format!("declared item {full} is not among the functions Verus checked in this crate")));
            }
            let name = item.rsplit("::").next().unwrap_or(item);
            let clauses = spec_clauses(source, name);
            let described = describe_item(&sources, &module.file, &module.role, &full);
            items.push(json!({"path":full,"module":module.file,"module_role":module.role,"item_role":described["item_role"],
                "checked_by_verus":true,"requires":clauses.as_ref().map(|c| c.1.clone()),"ensures":clauses.as_ref().map(|c| c.2.clone()),
                "signature":clauses.as_ref().map(|c| c.0.clone()),
                "text_extraction":if clauses.is_some() {"lexical, unique `fn NAME` in the file (the item's own clauses only)"} else {"not unique in the file; see the stored source"},
                "effective_contract":described["contract"]}));
        }
    }
    Ok(items)
}

/// The recorded item of a declared-item record.
pub fn item_record(item: &Value) -> VerusItemV1 {
    VerusItemV1 {
        path: item["path"].as_str().unwrap_or_default().into(),
        requires: serde_json::from_value(item["requires"].clone()).unwrap_or_default(),
        ensures: serde_json::from_value(item["ensures"].clone()).unwrap_or_default(),
    }
}

/// The query crate's `agent/` modules with their declared item records, as qualification records them (`file`
/// relative to `src/agent/`).
pub fn agent_modules(modules: &[DeclaredModule], items: &[Value]) -> Vec<CandidateModule> {
    modules
        .iter()
        .filter_map(|module| {
            let file = module.file.strip_prefix("agent/")?;
            Some(CandidateModule {
                file: file.to_string(),
                role: module.role.clone(),
                items: items.iter().filter(|item| item["module"] == json!(module.file)).map(item_record).collect(),
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn module_paths_of_every_author_root() {
        assert_eq!(module_path("agent/mod.rs").unwrap(), "agent");
        assert_eq!(module_path("agent/kernels/sum.rs").unwrap(), "agent::kernels::sum");
        assert_eq!(module_path("stores/by_day/interface/mod.rs").unwrap(), "stores::by_day::interface");
        assert_eq!(module_path("builder/mod.rs").unwrap(), "builder");
        assert_eq!(module_path("notes.txt").unwrap_err().class, FailureClass::Refusal);
    }
}
