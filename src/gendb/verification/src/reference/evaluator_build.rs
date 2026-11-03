//! The two Verus runs of the reference workflow: the whole-library check and the evaluator build of one statement.
//!
//! An evaluator crate (`gendb_sqlspec::evaluator::crate_files`) is written once by `freeze_framework_crate`
//! (read-only; the generated statement files go through the refusal scanner, the trusted shim and the fixed SQLSpec
//! library files do not) and then verified and compiled by ONE `rust_verify --no-cheating --compile` run over exactly
//! that snapshot, so the verified sources are the compiled sources. The library check freezes every library file the
//! same way. Nothing here hashes files.
//!
//! The fixed library is framework text, verified in every crate that carries it; the refusal list's author-source
//! rules (for example its macro allowlist, which the library's `matches!` would not pass) apply to author files, as
//! in candidate, storage and query crates.

use super::{create_output_dir, io_error, read_json, write_json, write_text, ReferenceError};
use crate::verus::{
    freeze_framework_crate, run_verus, CodegenOptions, FrameworkSource, FreezeError, FrozenCrate, VerusMode, VerusOptions,
    VerusOutcome, VerusRun, VerusToolchain,
};
use gendb_frontend::ast::AstDocument;
use gendb_sqlspec::evaluator::{self, echo_text, EvaluatorLibrary, CRATE_IDENTITY, UNSCANNED_TRUSTED_FILES};
use gendb_sqlspec::library::{self, Module, EVALUATOR_MODULES};
use serde_json::{json, Value};
use std::fs;
use std::path::{Path, PathBuf};

/// Crate name of the library check.
pub const LIBRARY_CRATE_NAME: &str = "gendb_verus_sql_library";
/// Crate name of an evaluator build when the caller names none.
pub const DEFAULT_EVALUATOR_CRATE_NAME: &str = "gendb_sql_query";

/// Options of library checks and evaluator builds: `opt_level` 1, no target CPU, Verus's default thread count.
pub fn evaluator_options(crate_name: &str) -> VerusOptions {
    VerusOptions { crate_name: crate_name.into(), codegen: CodegenOptions { opt_level: 1, target_cpu: None }, num_threads: None }
}

/// Result of [`check_library`].
#[derive(Debug)]
pub struct LibraryCheck {
    pub frozen: FrozenCrate,
    pub run: VerusRun,
    /// Also written to `<out>/record.json`.
    pub record: Value,
}

impl LibraryCheck {
    pub fn verified(&self) -> bool {
        self.run.outcome == VerusOutcome::Verified
    }
}

/// Freeze the whole library (root + every file, `pins` and `link` included) under `<out>/crate`, verify it
/// (`<out>/verus`), and write the run logs and `<out>/record.json`. `out` must not exist.
pub fn check_library(toolchain: &VerusToolchain, out: &Path) -> Result<LibraryCheck, ReferenceError> {
    create_output_dir(out)?;
    let files: Vec<FrameworkSource> = library::FILES.iter().map(|f| FrameworkSource { path: f.path.into(), text: f.text.into() }).collect();
    let frozen = freeze_framework_crate(&files, &unscanned_files(&files), &out.join("crate"))?;
    let run = run_verus(toolchain, &frozen, &evaluator_options(LIBRARY_CRATE_NAME), VerusMode::Verify, &out.join("verus"))?;
    write_run_logs(out, &run)?;
    let record = json!({
        "kind": "gendb-sql-library-check",
        "crate_identity": CRATE_IDENTITY,
        "toolchain": toolchain_record(toolchain),
        "frozen_root": frozen.root,
        "files": frozen.framework_files,
        "sources": library::FILES.iter().map(|f| json!({ "path": f.path, "source": f.source })).collect::<Vec<_>>(),
        "scanned": "none: every file is fixed library text (framework text; the author-source rules apply to author files)",
        "run": run_summary(&run),
    });
    write_json(&out.join("record.json"), &record)?;
    Ok(LibraryCheck { frozen, run, record })
}

/// A library snapshot recorded by [`check_library`] (`<dir>/record.json`, `<dir>/crate`); only a verified one.
pub fn load_checked_library(dir: &Path) -> Result<FrozenCrate, ReferenceError> {
    let path = dir.join("record.json");
    let record = read_json(&path)?;
    let malformed = |message: String| ReferenceError::Record { path: path.clone(), message };
    if record["run"]["outcome"] != json!("verified") {
        return Err(malformed(format!("not a verified library check (outcome {})", record["run"]["outcome"])));
    }
    let files = record["files"].as_array().ok_or_else(|| malformed("record without files".into()))?;
    let files = files.iter().filter_map(|f| f.as_str().map(str::to_owned)).collect();
    Ok(FrozenCrate::from_recorded(dir.join("crate"), Vec::new(), files))
}

/// The files of `files` the refusal scan does not read: the trusted shim and every file that is a fixed SQLSpec
/// library file (same path and text; generated files such as the crate root are scanned).
fn unscanned_files(files: &[FrameworkSource]) -> Vec<&str> {
    let fixed_library = |file: &FrameworkSource| library::FILES.iter().any(|f| f.path == file.path && f.text == file.text);
    files.iter().filter(|f| UNSCANNED_TRUSTED_FILES.contains(&f.path.as_str()) || fixed_library(f)).map(|f| f.path.as_str()).collect()
}

/// Status of an evaluator build.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize)]
#[serde(rename_all = "snake_case")]
pub enum BuildStatus {
    /// Verified, compiled, echo equal (and library files equal to the checked snapshot when one was given).
    Ok,
    /// Named refusal of the parser or the emitter (`executable_domain`); nothing was built.
    Refused,
    /// Verus reported failed proof obligations.
    ProofFailure,
    /// Verus/rustc refused the source without a failed obligation, or the refusal scanner refused a file.
    Rejected,
    ToolFailure,
    /// The compiled library's executable AST differs from the document, or its library files differ from the
    /// checked snapshot; the library is not used.
    Mismatch,
}

/// How an evaluator is built: its crate name, and optionally a checked library snapshot whose files the evaluator
/// crate must contain unchanged.
#[derive(Clone, Copy, Debug)]
pub struct BuildOptions<'a> {
    pub crate_name: &'a str,
    pub checked_library: Option<&'a FrozenCrate>,
}

impl Default for BuildOptions<'_> {
    fn default() -> Self {
        BuildOptions { crate_name: DEFAULT_EVALUATOR_CRATE_NAME, checked_library: None }
    }
}

/// Result of [`build_evaluator`].
#[derive(Debug)]
pub struct EvaluatorBuild {
    pub status: BuildStatus,
    /// Present only for `Ok`.
    pub library: Option<PathBuf>,
    /// Also written to `<out>/build.json` (except for a refused AST document, see `build_ast_file`).
    pub record: Value,
}

/// Emit, freeze, verify and compile the evaluator crate of `doc` under `out` (which must not exist), load the
/// compiled library, compare its echo with the document, and write `<out>/build.json`. `ast_path` names the
/// document's file for the record and later runs.
pub fn build_evaluator(
    toolchain: &VerusToolchain,
    doc: &AstDocument,
    ast_path: &Path,
    out: &Path,
    options: &BuildOptions,
) -> Result<EvaluatorBuild, ReferenceError> {
    create_output_dir(out)?;
    let finish = |status: BuildStatus, library: Option<PathBuf>, mut record: Value| -> Result<EvaluatorBuild, ReferenceError> {
        record["status"] = json!(status);
        record["ast"] = json!(ast_path);
        write_json(&out.join("build.json"), &record)?;
        Ok(EvaluatorBuild { status, library, record })
    };
    let files: Vec<FrameworkSource> = match evaluator::crate_files(doc) {
        Ok(files) => files.into_iter().map(|f| FrameworkSource { path: f.path, text: f.text }).collect(),
        Err(e) => return finish(BuildStatus::Refused, None, json!({ "kind": "gendb-sql-query-build", "refusal": { "reason": e.reason, "detail": e.detail } })),
    };
    let frozen = match freeze_framework_crate(&files, &unscanned_files(&files), &out.join("crate")) {
        Ok(frozen) => frozen,
        // The refusal scanner refused a framework file: recorded, nothing verified.
        Err(refused @ FreezeError::Refused { .. }) => {
            return finish(BuildStatus::Rejected, None, json!({ "kind": "gendb-sql-query-build", "freeze": refused }));
        }
        Err(e) => return Err(e.into()),
    };
    let run = run_verus(toolchain, &frozen, &evaluator_options(options.crate_name), VerusMode::VerifyAndCompile, &out.join("verus"))?;
    write_run_logs(out, &run)?;
    let mut record = json!({
        "kind": "gendb-sql-query-build",
        "crate_identity": CRATE_IDENTITY,
        "crate_name": options.crate_name,
        "toolchain": toolchain_record(toolchain),
        "frozen_root": frozen.root,
        "files": frozen.framework_files,
        "unscanned_trusted": UNSCANNED_TRUSTED_FILES,
        "unscanned_library": "the fixed SQLSpec library files (framework text)",
        "run": run_summary(&run),
        "library": run.artifact,
    });
    let library = match (run.outcome, &run.artifact) {
        (VerusOutcome::Compiled, Some(library)) => library.clone(),
        (VerusOutcome::ProofFailure, _) => return finish(BuildStatus::ProofFailure, None, record),
        (VerusOutcome::Rejected, _) => return finish(BuildStatus::Rejected, None, record),
        _ => return finish(BuildStatus::ToolFailure, None, record),
    };
    if let Some(checked) = options.checked_library {
        match compare_with_checked_library(checked, &frozen) {
            Ok(shared) => record["library_files_equal_checked"] = json!({ "checked_root": checked.root, "files": shared }),
            Err(e) => {
                record["library_files_equal_checked"] = json!({ "checked_root": checked.root, "error": e });
                return finish(BuildStatus::Mismatch, None, record);
            }
        }
    }
    let expected = echo_text(doc);
    let echoed = EvaluatorLibrary::load(&library)?.echo()?;
    write_text(&out.join("echo.expected.txt"), &expected)?;
    write_text(&out.join("echo.library.txt"), &echoed)?;
    let equal = expected == echoed;
    record["echo"] = json!({ "equal": equal, "bytes": expected.len() });
    finish(if equal { BuildStatus::Ok } else { BuildStatus::Mismatch }, equal.then_some(library), record)
}

/// Byte comparison of an evaluator snapshot's library files with a checked library snapshot: the evaluator crate
/// must hold exactly the checked snapshot's files of the evaluator modules, with identical bytes. Returns the
/// shared paths; `Err` describes the first difference.
fn compare_with_checked_library(checked: &FrozenCrate, evaluator_crate: &FrozenCrate) -> Result<Vec<String>, String> {
    let evaluator_file = |p: &String| Module::of_path(p).is_some_and(|m| EVALUATOR_MODULES.contains(&m));
    let mut expected: Vec<String> = checked.framework_files.iter().filter(|p| evaluator_file(p)).cloned().collect();
    let mut shared: Vec<String> = evaluator_crate.framework_files.iter().filter(|p| evaluator_file(p)).cloned().collect();
    expected.sort();
    shared.sort();
    if expected != shared {
        return Err(format!("library file sets differ: checked {expected:?} vs evaluator crate {shared:?}"));
    }
    for p in &shared {
        let a = fs::read(checked.root.join("src").join(p)).map_err(|e| format!("{p}: {e}"))?;
        let b = fs::read(evaluator_crate.root.join("src").join(p)).map_err(|e| format!("{p}: {e}"))?;
        if a != b {
            return Err(format!("{p} differs from the checked library"));
        }
    }
    Ok(shared)
}

fn toolchain_record(toolchain: &VerusToolchain) -> Value {
    json!({ "verus": toolchain.pin.verus.version, "commit": toolchain.pin.verus.commit, "rust": toolchain.pin.rust.toolchain })
}

/// Summary of one Verus run for records (the full stdout/stderr are written next to it).
fn run_summary(run: &VerusRun) -> Value {
    json!({
        "mode": run.mode,
        "outcome": run.outcome,
        "detail": run.detail,
        "verification": run.verification,
        "exit_code": run.exit_code,
        "wall_ns": run.wall_ns,
        "program": run.invocation.program,
        "args": run.invocation.args,
        "artifact": run.artifact,
        "errors": run.rendered_errors(),
    })
}

fn write_run_logs(dir: &Path, run: &VerusRun) -> Result<(), ReferenceError> {
    let stdout = dir.join("verus.stdout.json");
    fs::write(&stdout, &run.stdout).map_err(io_error(&stdout))?;
    let stderr = dir.join("verus.stderr.txt");
    fs::write(&stderr, &run.stderr).map_err(io_error(&stderr))
}
