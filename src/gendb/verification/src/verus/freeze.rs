//! Write-once, read-only crate snapshots: the exact source set a Verus run checks and compiles.
//!
//! An author crate has one or more author roots, each a directory of the crate's `src/` that one author owns: `agent/`
//! of a v3 candidate or a v4 query crate, `builder/` and `stores/<name>/interface/` of a storage crate. Every author
//! file is read once, written into the snapshot and scanned by the one author-source scan ([`scan_source`]) with its
//! path relative to `src/`; the scanned bytes are the written bytes. A framework file at an author path (a query
//! crate's copy of a storage interface, `gendb_registry::author_definition`) is author text too and is scanned the
//! same way, so no author text enters a snapshot unscanned.

use super::refusal::{scan_source, RefusalFinding};
use gendb_registry::author_definition;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Component, Path, PathBuf};

/// The author root of v3 candidates and v4 query crates.
const AGENT_ROOT: &str = "agent";

/// A framework-owned file written into the crate's `src/` (for example `lib.rs`).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FrameworkSource {
    /// Relative to `src/`; never inside an author root of the crate it is written into.
    pub path: String,
    pub text: String,
}

/// A frozen crate directory: `<root>/src/lib.rs`, framework files under `src/`, author files under their roots.
#[derive(Clone, Debug, Serialize)]
pub struct FrozenCrate {
    pub root: PathBuf,
    /// Files under `src/agent/`, relative to it, sorted (v3 candidates and v4 query crates; empty for a storage crate).
    pub agent_files: Vec<String>,
    /// Framework files, relative to `src/`, in the order they were given.
    pub framework_files: Vec<String>,
    /// Every author file of every author root, relative to `src/`, sorted.
    pub author_files: Vec<String>,
}

impl FrozenCrate {
    /// A v3 or query snapshot frozen earlier, from its directory and its recorded file lists (for example a candidate
    /// record): its author files are `agent/<file>`.
    pub fn from_recorded(root: PathBuf, agent_files: Vec<String>, framework_files: Vec<String>) -> Self {
        let author_files = agent_files.iter().map(|f| format!("{AGENT_ROOT}/{f}")).collect();
        Self { root, agent_files, framework_files, author_files }
    }

    /// A snapshot of any crate kind frozen earlier, from its recorded author files (relative to `src/`).
    pub fn from_recorded_author_files(root: PathBuf, author_files: Vec<String>, framework_files: Vec<String>) -> Self {
        Self { root, agent_files: files_under(AGENT_ROOT, &author_files), framework_files, author_files }
    }

    /// `<root>/src/lib.rs`, the file `rust_verify` is started on.
    pub fn crate_root(&self) -> PathBuf {
        self.root.join("src/lib.rs")
    }
}

/// The files of `author_files` under `root/`, relative to it.
fn files_under(root: &str, author_files: &[String]) -> Vec<String> {
    author_files.iter().filter_map(|f| f.strip_prefix(root)?.strip_prefix('/')).map(String::from).collect()
}

/// One author root of a crate: the directory `crate_directory` of the crate's `src/` (for example `"agent"`,
/// `"builder"`, `"stores/lineitem_by_date/interface"`), copied from the workspace directory `source`.
#[derive(Clone, Copy, Debug)]
pub struct AuthorRoot<'a> {
    pub crate_directory: &'a str,
    pub source: &'a Path,
}

#[derive(Clone, Debug, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum FreezeError {
    /// Author source refused by the refusal list or the file-set rule. The snapshot is kept read-only as evidence.
    Refused { findings: Vec<RefusalFinding> },
    /// Framework or filesystem problem, not the author's.
    Framework { message: String },
}

impl FreezeError {
    pub fn failure_class(&self) -> &'static str {
        match self {
            Self::Refused { .. } => "refusal",
            Self::Framework { .. } => "tool_failure",
        }
    }

    /// The findings with paths relative to the author root `root` instead of `src/` (the v3 candidate records name
    /// author files relative to `agent/`).
    fn relative_to(self, root: &str) -> Self {
        match self {
            Self::Refused { mut findings } => {
                for finding in &mut findings {
                    if let Some(relative) = finding.file.strip_prefix(root).and_then(|rest| rest.strip_prefix('/')) {
                        finding.file = relative.to_string();
                    }
                }
                Self::Refused { findings }
            }
            framework => framework,
        }
    }
}

impl fmt::Display for FreezeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Refused { findings } => {
                write!(f, "refusal-list findings {}", serde_json::to_string(findings).map_err(|_| fmt::Error)?)
            }
            Self::Framework { message } => f.write_str(message),
        }
    }
}

impl std::error::Error for FreezeError {}

fn framework_error(message: impl Into<String>) -> FreezeError {
    FreezeError::Framework { message: message.into() }
}

/// A v3 candidate or v4 query crate with the one author root `agent/`: [`freeze_author_crate`] with findings named
/// relative to `agent/`, as the v3 records name them.
pub fn freeze_crate(agent_dir: &Path, framework: &[FrameworkSource], destination: &Path) -> Result<FrozenCrate, FreezeError> {
    let agent = AuthorRoot { crate_directory: AGENT_ROOT, source: agent_dir };
    freeze_author_crate(framework, &[agent], destination).map_err(|e| e.relative_to(AGENT_ROOT))
}

/// Copy every author root into `<destination>/src/<crate_directory>/`, write the framework files, scan every author
/// file (every copied file and every framework file at an author path) with its path relative to `src/`, and make the
/// whole directory read-only. `destination` must not exist. Each root holds only directories and `.rs` files with
/// plain names (no symlinks) and its own `mod.rs`; a violation is a `file_set` finding.
///
/// Nothing is written (a framework error) when the framework file set is invalid, an author root is not a plain
/// relative path of the registry's author roots, two roots are equal or nested, a framework file lies inside an
/// author root, or an author tree cannot be read.
pub fn freeze_author_crate(framework: &[FrameworkSource], author_roots: &[AuthorRoot<'_>], destination: &Path) -> Result<FrozenCrate, FreezeError> {
    check_new_destination(destination)?;
    check_framework_paths(framework)?;
    check_author_roots(author_roots, framework)?;
    let trees: Vec<AuthorTree> = author_roots.iter().map(read_author_tree).collect::<Result<_, _>>()?;
    let src = destination.join("src");
    let mut findings = Vec::new();
    for f in framework {
        write_new_file(&src.join(&f.path), f.text.as_bytes())?;
        if author_definition(&f.path).is_some() {
            findings.extend(scan_source(&f.path, &f.text));
        }
    }
    let mut author_files = Vec::new();
    for (root, tree) in author_roots.iter().zip(trees) {
        fs::create_dir_all(src.join(root.crate_directory)).map_err(|e| framework_error(e.to_string()))?;
        findings.extend(tree.findings);
        for (path, bytes) in tree.files {
            write_new_file(&src.join(&path), &bytes)?;
            // The scanned bytes are the bytes just written into the snapshot.
            match std::str::from_utf8(&bytes) {
                Ok(text) => findings.extend(scan_source(&path, text)),
                Err(_) => findings.push(RefusalFinding::file_set(path.as_str(), "not UTF-8")),
            }
            author_files.push(path);
        }
    }
    author_files.sort();
    seal(destination, findings, author_files, framework)
}

/// Write a framework-only crate (no `agent/` tree) to `<destination>/src/`, scan every file except the listed
/// `unscanned` ones (trusted FFI files, which the refusal list forbids by design), and make the whole directory
/// read-only. Same write-once discipline as [`freeze_crate`].
pub fn freeze_framework_crate(framework: &[FrameworkSource], unscanned: &[&str], destination: &Path) -> Result<FrozenCrate, FreezeError> {
    check_new_destination(destination)?;
    check_framework_paths(framework)?;
    if let Some(u) = unscanned.iter().find(|u| !framework.iter().any(|f| f.path == **u)) {
        return Err(framework_error(format!("unscanned file {u} is not a framework file")));
    }
    let src = destination.join("src");
    let mut findings = Vec::new();
    for f in framework {
        write_new_file(&src.join(&f.path), f.text.as_bytes())?;
        if !unscanned.contains(&f.path.as_str()) {
            findings.extend(scan_source(&f.path, &f.text));
        }
    }
    seal(destination, findings, Vec::new(), framework)
}

fn check_new_destination(destination: &Path) -> Result<(), FreezeError> {
    if destination.exists() {
        return Err(framework_error(format!("{} already exists; a frozen crate is written once", destination.display())));
    }
    Ok(())
}

/// Framework files include `lib.rs`; every path is a unique relative `.rs` path of plain module names.
fn check_framework_paths(framework: &[FrameworkSource]) -> Result<(), FreezeError> {
    if !framework.iter().any(|f| f.path == "lib.rs") {
        return Err(framework_error("framework files must include lib.rs"));
    }
    let mut paths: Vec<&str> = framework.iter().map(|f| f.path.as_str()).collect();
    paths.sort_unstable();
    for (i, path) in paths.iter().enumerate() {
        let plain = is_plain_relative(path) && path.ends_with(".rs") && Path::new(path).components().all(|c| is_plain_name(&c.as_os_str().to_string_lossy()));
        if !plain || (i > 0 && paths[i - 1] == *path) {
            return Err(framework_error(format!("invalid or duplicate framework file path {path}")));
        }
    }
    Ok(())
}

fn is_plain_relative(path: &str) -> bool {
    !path.is_empty() && Path::new(path).components().all(|c| matches!(c, Component::Normal(_)))
}

/// A module name, optionally with `.rs`: ASCII letters, digits and `_`.
fn is_plain_name(name: &str) -> bool {
    let stem = name.strip_suffix(".rs").unwrap_or(name);
    !stem.is_empty() && stem.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
}

/// Every author root is a plain relative directory (module names, no `.rs` component) whose `mod.rs` the registry
/// classifies as author text (`builder`, `agent`, `stores/<name>/interface`); no two roots are equal or nested; no
/// framework file lies inside a root.
fn check_author_roots(author_roots: &[AuthorRoot<'_>], framework: &[FrameworkSource]) -> Result<(), FreezeError> {
    if author_roots.is_empty() {
        return Err(framework_error("an author crate has at least one author root"));
    }
    for (i, root) in author_roots.iter().enumerate() {
        let directory = root.crate_directory;
        let plain = !directory.is_empty() && directory.split('/').all(|part| is_plain_name(part) && !part.ends_with(".rs"));
        if !plain || author_definition(&format!("{directory}/mod.rs")).is_none() {
            return Err(framework_error(format!(
                "invalid author root {directory:?}: not a plain directory of an author root of the registry (builder, agent, stores/<name>/interface)"
            )));
        }
        if let Some(other) = author_roots[..i].iter().find(|o| contains_path(o.crate_directory, directory) || contains_path(directory, o.crate_directory)) {
            return Err(framework_error(format!("author roots {:?} and {directory:?} are equal or nested", other.crate_directory)));
        }
        if let Some(f) = framework.iter().find(|f| contains_path(directory, &f.path)) {
            return Err(framework_error(format!("invalid framework file path {}: {directory}/ belongs to the author", f.path)));
        }
    }
    Ok(())
}

/// `path` is `directory` or lies below it.
fn contains_path(directory: &str, path: &str) -> bool {
    path.strip_prefix(directory).is_some_and(|rest| rest.is_empty() || rest.starts_with('/'))
}

/// One author root read into memory.
struct AuthorTree {
    /// `(path relative to src/, bytes)`, sorted by path.
    files: Vec<(String, Vec<u8>)>,
    /// File-set findings: entries that are not plain directories or plain `.rs` files, and a missing root `mod.rs`.
    findings: Vec<RefusalFinding>,
}

/// Read a whole author root before anything is written, so an unreadable tree leaves no snapshot.
fn read_author_tree(root: &AuthorRoot<'_>) -> Result<AuthorTree, FreezeError> {
    let mut files = Vec::new();
    let mut findings = Vec::new();
    let mut directories = vec![(root.source.to_path_buf(), root.crate_directory.to_string())];
    while let Some((dir, relative)) = directories.pop() {
        let mut entries: Vec<_> = fs::read_dir(&dir)
            .map_err(|e| framework_error(format!("{}: {e}", dir.display())))?
            .collect::<Result<_, _>>()
            .map_err(|e| framework_error(e.to_string()))?;
        entries.sort_by_key(|e| e.file_name());
        for entry in entries {
            let name = entry.file_name().to_string_lossy().into_owned();
            let path = format!("{relative}/{name}");
            // symlink_metadata: a symlink is neither a directory nor a file here, so it is refused.
            let meta = fs::symlink_metadata(entry.path()).map_err(|e| framework_error(e.to_string()))?;
            if meta.is_dir() && is_plain_name(&name) && !name.ends_with(".rs") {
                directories.push((entry.path(), path));
            } else if meta.is_file() && name.ends_with(".rs") && is_plain_name(&name) {
                files.push((path, fs::read(entry.path()).map_err(|e| framework_error(e.to_string()))?));
            } else {
                findings.push(RefusalFinding::file_set(path, "only directories and `.rs` files with plain names (no symlinks) are allowed"));
            }
        }
    }
    files.sort();
    let module_root = format!("{}/mod.rs", root.crate_directory);
    if !files.iter().any(|(path, _)| *path == module_root) {
        findings.push(RefusalFinding::file_set(module_root.as_str(), &format!("the author module root {module_root} is missing")));
    }
    Ok(AuthorTree { files, findings })
}

fn write_new_file(path: &Path, bytes: &[u8]) -> Result<(), FreezeError> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|e| framework_error(format!("{}: {e}", parent.display())))?;
    }
    fs::write(path, bytes).map_err(|e| framework_error(format!("{}: {e}", path.display())))
}

/// Make the snapshot read-only, then report its findings or the frozen crate.
fn seal(destination: &Path, findings: Vec<RefusalFinding>, author_files: Vec<String>, framework: &[FrameworkSource]) -> Result<FrozenCrate, FreezeError> {
    make_read_only(destination).map_err(|e| framework_error(format!("read-only {}: {e}", destination.display())))?;
    if !findings.is_empty() {
        return Err(FreezeError::Refused { findings });
    }
    Ok(FrozenCrate {
        root: destination.to_path_buf(),
        agent_files: files_under(AGENT_ROOT, &author_files),
        framework_files: framework.iter().map(|f| f.path.clone()).collect(),
        author_files,
    })
}

fn make_read_only(path: &Path) -> std::io::Result<()> {
    let meta = fs::symlink_metadata(path)?;
    if meta.is_dir() {
        for entry in fs::read_dir(path)? {
            make_read_only(&entry?.path())?;
        }
        fs::set_permissions(path, fs::Permissions::from_mode(0o555))
    } else {
        fs::set_permissions(path, fs::Permissions::from_mode(0o444))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn source(path: &str) -> FrameworkSource {
        FrameworkSource { path: path.into(), text: String::new() }
    }

    #[test]
    fn framework_paths_are_plain_unique_and_include_the_root() {
        assert!(check_framework_paths(&[source("lib.rs"), source("gendb_entry/binder.rs")]).is_ok());
        assert!(check_framework_paths(&[source("query.rs")]).is_err());
        for bad in ["../x.rs", "/abs.rs", "a-b.rs", "x.txt", "lib.rs"] {
            assert!(check_framework_paths(&[source("lib.rs"), source(bad)]).is_err(), "{bad}");
        }
    }

    #[test]
    fn failure_classes_and_record_shape() {
        let refused = FreezeError::Refused { findings: vec![RefusalFinding::file_set("x.txt", "d")] };
        assert_eq!((refused.failure_class(), framework_error("m").failure_class()), ("refusal", "tool_failure"));
        // Records (and the SQL build record) read the serialized `kind` tag.
        assert_eq!(serde_json::to_value(&refused).unwrap()["kind"], "refused");
        assert_eq!(refused.to_string(), r#"refusal-list findings [{"file":"x.txt","line":0,"rule":"file_set","detail":"d"}]"#);
    }

    #[test]
    fn author_roots_are_registry_roots_disjoint_and_free_of_framework_files() {
        let root = |crate_directory| AuthorRoot { crate_directory, source: Path::new("unused") };
        let framework = [source("lib.rs"), source("stores/s/declaration.rs")];
        assert!(check_author_roots(&[root("stores/s/interface"), root("builder")], &framework).is_ok());
        assert!(check_author_roots(&[root("agent")], &framework).is_ok());
        let refused = |roots: &[AuthorRoot<'_>], framework: &[FrameworkSource]| match check_author_roots(roots, framework) {
            Err(FreezeError::Framework { message }) => message,
            other => panic!("{other:?}"),
        };
        assert!(refused(&[], &framework).contains("at least one author root"));
        for bad in ["", "gendb_entry", "stores/s", "../agent", "agent/", "builder.rs", "stores/S-x/interface"] {
            assert!(refused(&[root(bad)], &framework).contains("invalid author root"), "{bad}");
        }
        assert!(refused(&[root("agent"), root("agent")], &framework).contains("equal or nested"));
        assert!(refused(&[root("stores/s/interface"), root("stores/s/interface/inner")], &framework).contains("equal or nested"));
        let inside = [source("lib.rs"), source("builder/helper.rs")];
        assert!(refused(&[root("builder")], &inside).contains("builder/helper.rs: builder/ belongs to the author"));
        // `builder_extra/` is not inside `builder/`.
        assert!(check_author_roots(&[root("builder")], &[source("lib.rs"), source("builder_extra.rs")]).is_ok());
    }

    #[test]
    fn v3_findings_stay_relative_to_agent() {
        let finding = |file: &str| RefusalFinding::file_set(file, "d");
        let refused = FreezeError::Refused { findings: vec![finding("agent/mod.rs"), finding("agent/x/y.rs"), finding("builder/mod.rs")] };
        let FreezeError::Refused { findings } = refused.relative_to(AGENT_ROOT) else { panic!() };
        let files: Vec<&str> = findings.iter().map(|f| f.file.as_str()).collect();
        assert_eq!(files, ["mod.rs", "x/y.rs", "builder/mod.rs"]);
        let recorded = FrozenCrate::from_recorded("/f".into(), vec!["mod.rs".into(), "a/b.rs".into()], vec![]);
        assert_eq!(recorded.author_files, ["agent/mod.rs", "agent/a/b.rs"]);
        let storage = FrozenCrate::from_recorded_author_files("/f".into(), vec!["builder/mod.rs".into(), "agent/mod.rs".into()], vec![]);
        assert_eq!(storage.agent_files, ["mod.rs"]);
    }
}
