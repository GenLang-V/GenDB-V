//! Embeds the SQLSpec Verus library at compile time. Writes `$OUT_DIR/library_files.rs`: one `LibraryFile` per
//! Verus source file, with its logical path in an assembled crate, its physical path under `sqlspec/` and its text
//! (`include_str!` of the absolute path, so Cargo rebuilds when a file changes).
//!
//! Physical folder -> logical path in assembled crates (the module paths agents, the translator and the fixed
//! entry import stay `crate::{spec,exec,bridge,link,pins}::…`):
//!   library.rs           -> lib.rs            (root of the checked library crate)
//!   spec.rs              -> spec/mod.rs
//!   syntax/<rel>         -> spec/<rel>
//!   semantics/<rel>      -> spec/<rel>
//!   interpreter/<rel>    -> exec/<rel>        (except interpreter/host/: the evaluator entry and shim, embedded
//!                                              separately by `gendb_sqlspec::evaluator`)
//!   proofs/bridge/<rel>  -> bridge/<rel>
//!   proofs/link/mod.rs   -> link.rs           (candidate crates use the non-mod-rs form)
//!   proofs/link/<rel>    -> link/<rel>
//!   proofs/examples/<rel>-> pins/<rel>
//! Two physical files with one logical path, or a folder that cannot be read, fail the build.

use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};

/// A physical folder and the logical module folder its files are copied to.
struct Tree {
    physical: &'static str,
    logical: &'static str,
    /// `mod.rs` of the folder becomes `<logical>.rs` beside the folder instead of `<logical>/mod.rs`.
    module_file_beside: bool,
    /// Subfolder (relative to `physical`) that is not part of the library.
    excluded: Option<&'static str>,
}

const SINGLE_FILES: &[(&str, &str)] = &[("library.rs", "lib.rs"), ("spec.rs", "spec/mod.rs")];

const TREES: &[Tree] = &[
    Tree { physical: "syntax", logical: "spec", module_file_beside: false, excluded: None },
    Tree { physical: "semantics", logical: "spec", module_file_beside: false, excluded: None },
    Tree { physical: "interpreter", logical: "exec", module_file_beside: false, excluded: Some("host") },
    Tree { physical: "proofs/bridge", logical: "bridge", module_file_beside: false, excluded: None },
    Tree { physical: "proofs/link", logical: "link", module_file_beside: true, excluded: None },
    Tree { physical: "proofs/examples", logical: "pins", module_file_beside: false, excluded: None },
];

fn main() {
    let manifest = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    println!("cargo:rerun-if-changed=build.rs");
    // logical path -> physical path relative to the manifest directory
    let mut files: BTreeMap<String, String> = BTreeMap::new();
    let mut add = |logical: String, physical: String| {
        if let Some(previous) = files.insert(logical.clone(), physical.clone()) {
            panic!("SQLSpec library: {previous} and {physical} both map to {logical}");
        }
    };
    for (physical, logical) in SINGLE_FILES {
        println!("cargo:rerun-if-changed={physical}");
        add(logical.to_string(), physical.to_string());
    }
    for tree in TREES {
        println!("cargo:rerun-if-changed={}", tree.physical);
        for relative in rust_files(&manifest.join(tree.physical), "") {
            if tree.excluded.is_some_and(|x| relative.starts_with(&format!("{x}/"))) {
                continue;
            }
            let logical = if tree.module_file_beside && relative == "mod.rs" {
                format!("{}.rs", tree.logical)
            } else {
                format!("{}/{relative}", tree.logical)
            };
            add(logical, format!("{}/{relative}", tree.physical));
        }
    }
    let mut out = String::from("&[\n");
    for (logical, physical) in &files {
        let absolute = manifest.join(physical);
        let _ = writeln!(
            out,
            "    LibraryFile {{ path: {logical:?}, source: {physical:?}, text: include_str!({:?}) }},",
            absolute.to_str().expect("UTF-8 source path")
        );
    }
    out.push_str("]\n");
    let target = PathBuf::from(std::env::var("OUT_DIR").expect("OUT_DIR")).join("library_files.rs");
    fs::write(&target, out).unwrap_or_else(|e| panic!("{}: {e}", target.display()));
}

/// Every `.rs` file under `dir`, as `/`-separated paths relative to `dir`.
fn rust_files(dir: &Path, prefix: &str) -> Vec<String> {
    let mut found = Vec::new();
    let entries = fs::read_dir(dir).unwrap_or_else(|e| panic!("SQLSpec library folder {}: {e}", dir.display()));
    for entry in entries {
        let entry = entry.unwrap_or_else(|e| panic!("{}: {e}", dir.display()));
        let name = entry.file_name().into_string().unwrap_or_else(|n| panic!("non-UTF-8 file name {n:?}"));
        let relative = if prefix.is_empty() { name.clone() } else { format!("{prefix}/{name}") };
        let kind = entry.file_type().unwrap_or_else(|e| panic!("{}: {e}", entry.path().display()));
        if kind.is_dir() {
            found.extend(rust_files(&entry.path(), &relative));
        } else if kind.is_file() && name.ends_with(".rs") {
            found.push(relative);
        }
    }
    found
}
