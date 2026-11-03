//! Import of a frozen query candidate retained by another session, for a fresh evaluation in this one
//! (`SynthesisRole::import_frozen`, used by the reselection without an author, `controller::reselect`).
//!
//! Only the frozen sources and their metadata are copied (the layout `candidate::freeze` writes):
//! - the query crate's recorded files (`crate/src/<framework and author files>`);
//! - each workspace storage's recorded crate files and its `storage.json`;
//! - `candidate.json`, `decision.json` and `manifest.json`.
//!
//! The source's evaluation and qualification outputs (`evaluation-<k>/`, `qualification-<ms>/`) are never copied. The
//! one kind of location metadata, `modules[].source` (the path of each captured source file), is rebased onto the copy
//! in `candidate.json` and each `storage.json`. Every other copied byte is compared with its source after the copy.
//! The source directory is only read; the import writes no library record.

use super::candidate::{FrozenCandidate, StorageSource};
use crate::controller::records::{read_json, write_new_json};
use crate::storage::freeze::read_frozen_storage;
use gendb_verification::admission::AdmissionError;
use std::fs;
use std::path::{Component, Path, PathBuf};

/// The records of a frozen query directory copied as they are (`candidate.json` is rewritten with its locations
/// rebased).
const UNCHANGED_RECORDS: [&str; 2] = ["decision.json", "manifest.json"];

/// Copy the frozen candidate in `source` into the fresh directory `target`; the candidate as it reads in `target`.
pub fn import_frozen(source: &Path, target: &Path) -> Result<FrozenCandidate, AdmissionError> {
    let candidate: FrozenCandidate = read_json(&source.join("candidate.json")).map_err(AdmissionError::tool)?;
    fs::create_dir(target).map_err(|e| AdmissionError::tool(format!("{}: {e}", target.display())))?;
    copy_crate_files(source, target, candidate.framework_files.iter().chain(&candidate.author_files))?;
    for record in UNCHANGED_RECORDS {
        copy_verified(&source.join(record), &target.join(record))?;
    }
    for storage_use in candidate.storage_uses.iter().filter(|u| matches!(u.source, StorageSource::Workspace { .. })) {
        let (from, storage) = candidate.workspace_storage(source, &storage_use.name)?;
        let to = target.join("storages").join(&storage_use.name);
        copy_crate_files(&from, &to, storage.framework_files.iter().chain(&storage.author_files))?;
        let mut rebased = storage.clone();
        for module in &mut rebased.modules {
            module.source = rebase(&module.source, source, target)?;
        }
        write_new_json(&to.join("storage.json"), &rebased).map_err(AdmissionError::tool)?;
        same_except_locations(&storage, &read_frozen_storage(&to)?, |s| &mut s.modules, |m| &mut m.source, source, target)?;
    }
    let mut rebased = candidate.clone();
    for module in &mut rebased.modules {
        module.source = rebase(&module.source, source, target)?;
    }
    write_new_json(&target.join("candidate.json"), &rebased).map_err(AdmissionError::tool)?;
    let written: FrozenCandidate = read_json(&target.join("candidate.json")).map_err(AdmissionError::tool)?;
    same_except_locations(&candidate, &written, |c| &mut c.modules, |m| &mut m.source, source, target)?;
    Ok(written)
}

/// `path` (a captured source file under `source`) at the same place under `target`.
fn rebase(path: &Path, source: &Path, target: &Path) -> Result<PathBuf, AdmissionError> {
    let relative = path
        .strip_prefix(source)
        .map_err(|_| AdmissionError::tool(format!("recorded source {} lies outside the frozen directory {}", path.display(), source.display())))?;
    Ok(target.join(relative))
}

/// The written record equals its source once its rebased locations are mapped back, so the import changed nothing
/// but locations.
fn same_except_locations<T: Clone + PartialEq, M>(
    original: &T,
    written: &T,
    modules: impl Fn(&mut T) -> &mut Vec<M>,
    location: impl Fn(&mut M) -> &mut PathBuf,
    source: &Path,
    target: &Path,
) -> Result<(), AdmissionError> {
    let mut restored = written.clone();
    for module in modules(&mut restored).iter_mut() {
        let path = location(module);
        *path = rebase(path, target, source)?;
    }
    if restored != *original {
        return Err(AdmissionError::tool(format!("the imported record under {} differs from its source beyond locations", target.display())));
    }
    Ok(())
}

/// Copy the recorded crate files `files` (relative to `<from>/crate/src`) to `<to>/crate/src`.
fn copy_crate_files<'a>(from: &Path, to: &Path, files: impl Iterator<Item = &'a String>) -> Result<(), AdmissionError> {
    let (from, to) = (from.join("crate/src"), to.join("crate/src"));
    for file in files {
        let relative = Path::new(file);
        if relative.components().any(|c| !matches!(c, Component::Normal(_))) {
            return Err(AdmissionError::tool(format!("recorded crate file {file} is not a relative path inside its crate")));
        }
        copy_verified(&from.join(relative), &to.join(relative))?;
    }
    Ok(())
}

/// Copy one file (permissions included) and compare the copy with its source byte for byte.
fn copy_verified(from: &Path, to: &Path) -> Result<(), AdmissionError> {
    let failed = |e: std::io::Error| AdmissionError::tool(format!("copy {} -> {}: {e}", from.display(), to.display()));
    if let Some(parent) = to.parent() {
        fs::create_dir_all(parent).map_err(failed)?;
    }
    fs::copy(from, to).map_err(failed)?;
    if fs::read(from).map_err(failed)? != fs::read(to).map_err(failed)? {
        return Err(AdmissionError::tool(format!("the copy {} differs from its source {}", to.display(), from.display())));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::controller::records::create_dir;
    use crate::controller::test_support::scratch_root;
    use serde_json::json;

    /// A frozen directory shaped like `candidate::freeze`'s output: one agent file, one framework file, one workspace
    /// storage with one author file, and an earlier evaluation output that must not be copied.
    fn frozen_fixture(root: &Path) -> PathBuf {
        let frozen = root.join("source/iterations/0002/frozen");
        let storage = frozen.join("storages/s1");
        for (path, text) in [
            (frozen.join("crate/src/lib.rs"), "framework"),
            (frozen.join("crate/src/agent/mod.rs"), "agent code"),
            (storage.join("crate/src/builder/mod.rs"), "builder code"),
            (storage.join("crate/src/schema.rs"), "storage framework"),
            (frozen.join("evaluation-0/verus-build/libgendb_query.so"), "old build"),
            (frozen.join("decision.json"), "{\"rationale\":\"r\"}"),
            (frozen.join("manifest.json"), "{\"crate_dir\":\"verus\"}"),
        ] {
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(&path, text).unwrap();
        }
        let storage_record = json!({"manifest":crate::storage::manifest::StorageManifest::example(),
            "declaration":{"tables":[]},"compiler":{"opt_level":3,"target_cpu":null},
            "modules":[{"file":"builder/mod.rs","role":"builder","items":["build"],"source":storage.join("crate/src/builder/mod.rs")}],
            "author_files":["builder/mod.rs"],"framework_files":["schema.rs"]});
        fs::write(storage.join("storage.json"), storage_record.to_string()).unwrap();
        let candidate = json!({"kind":"verus_rust_stored","format_version":2,"statement_key":"k","sql":"q","entry_identity":"e",
            "storage_uses":[{"name":"s1","source":{"workspace":{"manifest":"new/verus-storage.json"}},"declaration":{"tables":[]}}],
            "compiler":{"opt_level":3,"target_cpu":null},
            "modules":[{"file":"agent/mod.rs","role":"entry","items":["query"],"source":frozen.join("crate/src/agent/mod.rs")},
                {"file":"storages/s1/builder/mod.rs","role":"builder","items":["build"],"source":storage.join("crate/src/builder/mod.rs")}],
            "author_files":["agent/mod.rs"],"framework_files":["lib.rs"],"notes":"n"});
        fs::write(frozen.join("candidate.json"), candidate.to_string()).unwrap();
        frozen
    }

    /// Every file under `root`, relative to it, sorted.
    fn files(root: &Path) -> Vec<PathBuf> {
        fn walk(root: &Path, dir: &Path, out: &mut Vec<PathBuf>) {
            for entry in fs::read_dir(dir).unwrap() {
                let path = entry.unwrap().path();
                if path.is_dir() {
                    walk(root, &path, out);
                } else {
                    out.push(path.strip_prefix(root).unwrap().to_path_buf());
                }
            }
        }
        let mut out = vec![];
        walk(root, root, &mut out);
        out.sort();
        out
    }

    /// The copy holds exactly the frozen sources and records, byte-equal except the rebased source locations; the
    /// earlier evaluation output stays behind and the source directory is unchanged.
    #[test]
    fn import_copies_frozen_sources_only_and_rebases_locations() {
        let root = scratch_root("query-import");
        create_dir(&root).unwrap();
        let source = frozen_fixture(&root);
        let before: Vec<(PathBuf, Vec<u8>)> = files(&source).into_iter().map(|f| (f.clone(), fs::read(source.join(&f)).unwrap())).collect();
        let target = root.join("reselect/iterations/0002/frozen");
        create_dir(target.parent().unwrap()).unwrap();
        let imported = import_frozen(&source, &target).unwrap();
        let copied = files(&target);
        assert!(!copied.iter().any(|f| f.starts_with("evaluation-0")), "no evaluation output is copied: {copied:?}");
        assert_eq!(copied.len(), before.len() - 1);
        for (file, bytes) in &before {
            if file.starts_with("evaluation-0") {
                continue;
            }
            let text = fs::read(target.join(file)).unwrap();
            if file.ends_with("candidate.json") || file.ends_with("storage.json") {
                assert!(!String::from_utf8_lossy(&text).contains(source.to_str().unwrap()), "{file:?} names no source location");
            } else {
                assert_eq!(&text, bytes, "{file:?} is byte-equal");
            }
        }
        assert!(imported.modules.iter().all(|m| m.source.starts_with(&target) && m.source.is_file()));
        let storage = read_frozen_storage(&target.join("storages/s1")).unwrap();
        assert_eq!(storage.modules[0].source, target.join("storages/s1/crate/src/builder/mod.rs"));
        let after: Vec<(PathBuf, Vec<u8>)> = files(&source).into_iter().map(|f| (f.clone(), fs::read(source.join(&f)).unwrap())).collect();
        assert_eq!(after, before, "the source is only read");
        assert!(import_frozen(&source, &target).is_err(), "the target must be fresh");
    }
}
