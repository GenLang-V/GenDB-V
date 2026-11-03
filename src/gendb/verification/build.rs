//! Export two content identities of the sources a query preflight's evidence is computed by
//! (`admission::preflight::reuse`). Each is a SHA-256 over the exact bytes of a set of workspace files (path and
//! content), the workspace manifest and lock file (dependency versions, e.g. DataFusion), and the compiler with its
//! settings. Nothing outside `src/gendb` is read; no data is hashed.
//!
//! - `GENDB_PREFLIGHT_SOURCES`: every file of the crates the preflight path is compiled from or reads at run time:
//!   `artifacts`, `frontend` (with the Python SQL frontend it runs), `registry`, `runtime`, `sqlspec` (the Verus
//!   library it embeds), `storage` and `verification`. Only `synthesis`, `cli` and `dashboard` are outside it.
//! - `GENDB_REFERENCE_SOURCES`: the subset that computes the exact prepared-data reference answers: `artifacts`,
//!   `frontend`, `sqlspec` (result codec, the verified finalization semantics), `storage` (capture, IPC decoding, the
//!   DataFusion session) and `verification` without the parts no reference calls: the fixed author entries and
//!   obligations, storage admission, qualification, candidate execution and serving checks, the baseline runner, the
//!   evidence bookkeeping (`preflight/reuse.rs`, which checks every reused rows file by its SHA-256) and this file.
//!   `runtime` and `registry` are outside it: what references use of them (binding values, statement keys) is in the
//!   statement record the evidence identity compares.
//!
//! In each crate, the folders `tests`, `examples`, `benches`, `target`, `__pycache__` and hidden entries are skipped
//! (not compiled into the executable and not read by it).

use sha2::{Digest, Sha256};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

const PREFLIGHT_CRATES: &[&str] = &["artifacts", "frontend", "registry", "runtime", "sqlspec", "storage", "verification"];
const REFERENCE_CRATES: &[&str] = &["artifacts", "frontend", "sqlspec", "storage", "verification"];
/// Paths (relative to the workspace) outside the reference set; a folder excludes everything under it.
const NOT_REFERENCE: &[&str] = &[
    "verification/build.rs",
    "verification/obligations",
    "verification/src/obligations.rs",
    "verification/src/obligations",
    "verification/src/baseline.rs",
    "verification/src/admission/storage.rs",
    "verification/src/admission/qualification.rs",
    "verification/src/admission/qualification_v4.rs",
    "verification/src/admission/served.rs",
    "verification/src/admission/stored_execution.rs",
    "verification/src/admission/execution.rs",
    "verification/src/admission/preflight/reuse.rs",
];
const WORKSPACE_FILES: &[&str] = &["Cargo.toml", "Cargo.lock"];
const SKIPPED_FOLDERS: &[&str] = &["tests", "examples", "benches", "target", "__pycache__"];

fn main() {
    let manifest = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let workspace = manifest.parent().expect("the crate is inside the workspace").to_path_buf();
    let mut files = vec![];
    for name in PREFLIGHT_CRATES {
        let root = workspace.join(name);
        println!("cargo:rerun-if-changed={}", root.display());
        collect(&root, &mut files);
    }
    for file in WORKSPACE_FILES {
        println!("cargo:rerun-if-changed={}", workspace.join(file).display());
    }
    let relative = |path: &PathBuf| path.strip_prefix(&workspace).expect("inside the workspace").to_string_lossy().into_owned();
    let mut files: Vec<String> = files.iter().map(relative).chain(WORKSPACE_FILES.iter().map(|f| f.to_string())).collect();
    files.sort();
    let in_reference_set = |path: &String| {
        let crate_name = path.split('/').next().unwrap_or_default();
        (WORKSPACE_FILES.contains(&path.as_str()) || REFERENCE_CRATES.contains(&crate_name))
            && !NOT_REFERENCE.iter().any(|x| path == x || path.starts_with(&format!("{x}/")))
    };
    let compiler = compiler_and_settings();
    let preflight = identity(&workspace, files.iter(), &compiler);
    let reference = identity(&workspace, files.iter().filter(|p| in_reference_set(p)), &compiler);
    println!("cargo:rustc-env=GENDB_PREFLIGHT_SOURCES={preflight}");
    println!("cargo:rustc-env=GENDB_REFERENCE_SOURCES={reference}");
}

/// `sha256:<hex>` over each file's relative path, length and bytes, then the compiler and its settings.
fn identity<'a>(workspace: &Path, files: impl Iterator<Item = &'a String>, compiler: &str) -> String {
    let mut digest = Sha256::new();
    for path in files {
        let bytes = fs::read(workspace.join(path)).unwrap_or_else(|e| panic!("{path}: {e}"));
        digest.update(path.as_bytes());
        digest.update([0]);
        digest.update((bytes.len() as u64).to_le_bytes());
        digest.update(&bytes);
    }
    digest.update(compiler.as_bytes());
    let hex: String = digest.finalize().iter().map(|byte| format!("{byte:02x}")).collect();
    format!("sha256:{hex}")
}

/// `rustc -vV` and the build settings Cargo passes to build scripts.
fn compiler_and_settings() -> String {
    let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".into());
    let version = Command::new(&rustc).arg("-vV").output().map(|o| String::from_utf8_lossy(&o.stdout).into_owned()).unwrap_or_default();
    assert!(!version.is_empty(), "the compiler version must be known: {rustc} -vV");
    let mut text = version;
    for key in ["PROFILE", "OPT_LEVEL", "DEBUG", "CARGO_ENCODED_RUSTFLAGS", "TARGET"] {
        text.push_str(&format!("|{key}={}", std::env::var(key).unwrap_or_default()));
    }
    text
}

/// Every file under `folder`, skipping [`SKIPPED_FOLDERS`] and hidden entries.
fn collect(folder: &Path, files: &mut Vec<PathBuf>) {
    let entries = fs::read_dir(folder).unwrap_or_else(|e| panic!("{}: {e}", folder.display()));
    for entry in entries {
        let path = entry.expect("folder entry").path();
        let name = path.file_name().and_then(|n| n.to_str()).unwrap_or_default().to_string();
        if name.starts_with('.') {
            continue;
        }
        if path.is_dir() {
            if !SKIPPED_FOLDERS.contains(&name.as_str()) {
                collect(&path, files);
            }
        } else {
            files.push(path);
        }
    }
}
