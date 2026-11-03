//! The one assembly of a candidate crate's framework files, and the fixed entry texts it copies.
//!
//! The fixed Verus files live at the crate root under `verification/obligations/` with their logical paths
//! (`gendb_entry.rs`, `gendb_entry/<module>.rs`) and are embedded at compile time, so a binary assembles the entry it
//! was built with and reads no source tree at run time. The same holds for the SQLSpec library
//! (`gendb_sqlspec::library`) and the ABI files (`gendb_runtime::abi`).

use super::binder_module::binder_module;
use super::declared::DeclaredSource;
use super::params_module::{check_free_params, params_module, ArgumentAbi};
use super::source_module::{source_module, STATEMENT_SOURCE};
use super::AssemblyError;
use crate::verus::FrameworkSource;
use gendb_frontend::columns::SourceDeclaration;
use gendb_frontend::params::Instance;
use gendb_frontend::translator::{emit_instance_module, EmitOptions};
use gendb_runtime::abi::{GENDB_ABI_SOURCE, GENDB_SHIM_SOURCE};
use gendb_sqlspec::library::{self, CANDIDATE_MODULES};

/// Identity of the fixed entry and its generators, recorded with builds, packages and claims. The fixed entry text
/// names it, and admission refuses a build whose `gendb_entry.rs` does not.
pub const ENTRY_IDENTITY: &str = gendb_artifacts::verus::VERUS_ENTRY_V3_IDENTITY;

/// `crate::gendb_entry`: the final claim and the two entry functions.
pub const ENTRY_SOURCE: &str = include_str!("../../obligations/gendb_entry.rs");

/// Verus `--crate-name` of every candidate crate; recorded item paths start with it (`gendb_query::agent::build`).
pub const CANDIDATE_CRATE_NAME: &str = "gendb_query";

/// The fixed submodules of `crate::gendb_entry` that every crate kind (v3 candidate, storage, query v4) carries
/// unchanged, in assembly order: `(logical path, text)`.
pub(super) const ENTRY_SUBMODULE_FILES: [(&str, &str); 5] = [
    ("gendb_entry/runtime.rs", include_str!("../../obligations/gendb_entry/runtime.rs")),
    ("gendb_entry/parallel.rs", include_str!("../../obligations/gendb_entry/parallel.rs")),
    ("gendb_entry/layout.rs", include_str!("../../obligations/gendb_entry/layout.rs")),
    ("gendb_entry/work.rs", include_str!("../../obligations/gendb_entry/work.rs")),
    ("gendb_entry/source_check.rs", include_str!("../../obligations/gendb_entry/source_check.rs")),
];

/// The submodules `gendb_entry.rs` declares: the fixed ones and the generated `binder`.
pub(super) const ENTRY_SUBMODULES: [&str; 6] = ["binder", "layout", "parallel", "runtime", "source_check", "work"];

/// Every framework file of the candidate crate of the statement instance `inst` (fixed parameters substituted,
/// `gendb_frontend::params::instantiate`), whose delivered columns are `delivered`
/// (`gendb_frontend::columns::source_declaration` of `inst.doc`). `identity` names the statement in generated
/// headers only. The author's `agent/` module is the only missing part.
///
/// The freeze writes these files and admission compares a build's files with a fresh call byte for byte, so this
/// is the one place a candidate crate is assembled.
pub fn candidate_framework_files(inst: &Instance, delivered: &SourceDeclaration, identity: &str) -> Result<Vec<FrameworkSource>, AssemblyError> {
    let query = emit_instance_module(inst, &EmitOptions::candidate()).map_err(AssemblyError::Emit)?;
    let source = DeclaredSource::of_statement(&inst.doc, delivered)?;
    let schema_widths: Vec<usize> = inst.doc.tables.iter().map(|t| t.columns.len()).collect();
    source.check_deliverable(&schema_widths)?;
    check_free_params(&inst.free, ArgumentAbi::SharedParamArg)?;

    let file = |path: &str, text: String| FrameworkSource { path: path.into(), text };
    let mut files = vec![file("lib.rs", crate_root())];
    files.extend(library::module_files(CANDIDATE_MODULES).into_iter().map(|f| file(f.path, f.text.into())));
    files.push(file("query.rs", query));
    files.push(file("gendb_source.rs", source_module(&source, &schema_widths, identity, &STATEMENT_SOURCE)));
    files.push(file("gendb_params.rs", params_module(&inst.free, identity, ArgumentAbi::SharedParamArg)));
    files.push(file("gendb_abi.rs", GENDB_ABI_SOURCE.into()));
    files.push(file("gendb_shim.rs", GENDB_SHIM_SOURCE.into()));
    files.push(file("gendb_entry.rs", ENTRY_SOURCE.into()));
    files.extend(ENTRY_SUBMODULE_FILES.iter().map(|(path, text)| file(path, (*text).into())));
    files.push(file("gendb_entry/binder.rs", binder_module(&source, identity, ENTRY_IDENTITY)));
    Ok(files)
}

/// Crate root of a candidate: the library's crate attributes and module declarations, then the statement, source,
/// parameter, ABI and entry modules, `agent` (the only author module) and the private shim.
fn crate_root() -> String {
    let mut o = format!("// FRAMEWORK FILE: crate root of a GenDB Verus candidate (gendb_verification::obligations, {ENTRY_IDENTITY}).\n");
    for attribute in library::crate_attributes() {
        o.push_str(attribute);
        o.push('\n');
    }
    o.push_str(&library::module_declarations(CANDIDATE_MODULES));
    o.push_str("pub mod query;\npub mod gendb_source;\npub mod gendb_params;\n");
    o.push_str("pub mod gendb_abi;\npub mod gendb_entry;\npub mod agent;\nmod gendb_shim;\n");
    o
}

/// The framework-only check crate of a candidate's framework files: every file except the shim, with no `agent`
/// module and with `gendb_entry.rs` reduced to its submodule declarations (the entry's own items need the author's
/// module and are checked in every candidate crate). It checks the library, the emitted statement, the generated
/// source/parameter/binder modules, the ABI types and the fixed entry submodules before any author runs; the files
/// it keeps are byte-equal to the candidate's.
pub fn framework_check_files(framework: &[FrameworkSource]) -> Vec<FrameworkSource> {
    let mut entry_modules = String::from("// FRAMEWORK CHECK ONLY: the submodules of the fixed entry (its items need the author's module).\n");
    for module in ENTRY_SUBMODULES {
        entry_modules.push_str(&format!("pub mod {module};\n"));
    }
    let mut files = Vec::new();
    for f in framework {
        match f.path.as_str() {
            "gendb_shim.rs" => {}
            "gendb_entry.rs" => files.push(FrameworkSource { path: f.path.clone(), text: entry_modules.clone() }),
            "lib.rs" => {
                let root: String = f.text.lines().filter(|l| !matches!(l.trim(), "pub mod agent;" | "mod gendb_shim;")).map(|l| format!("{l}\n")).collect();
                files.push(FrameworkSource { path: f.path.clone(), text: root });
            }
            _ => files.push(f.clone()),
        }
    }
    files
}
