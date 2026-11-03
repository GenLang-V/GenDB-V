//! The one assembly of a query crate over stored data (fixed query entry v4, `gendb-verus-entry-v4`; entry v5,
//! `gendb-verus-entry-v5`, when the dataset declares integrity constraints).
//!
//! A query crate checks one statement instance and the author's `agent/` module against the storages it reads. The
//! fixed entry is chosen by the instance alone ([`query_entry`]): v5 exactly when its schema declares constraints, which
//! the request's `integrity_constraints` alone puts there. Its files, relative to `src/` (the author's `agent/**` is
//! the only missing part):
//!
//! | Path | Origin |
//! |---|---|
//! | `lib.rs`, `stores.rs` | generated roots |
//! | `spec/**`, `exec/**`, `bridge/**`, `link.rs`, `link/**` | SQLSpec library |
//! | `schema.rs` | `gendb_frontend::translator::emit_column_schema_module` (the dataset DDL's columns) |
//! | `query.rs` | `gendb_frontend::translator::emit_statement_module` (imports `crate::schema::schema_spec`) |
//! | `stores/<name>/{mod,declaration}.rs` | generated from each storage's declaration (the storage build's text) |
//! | `stores/<name>/interface/**` | copied unchanged from the storage's checked build (author text, read-only here) |
//! | `gendb_params.rs` | the parameter generator (arguments `QueryArg`) |
//! | `gendb_abi.rs` | runtime ABI types (shared with storage crates) |
//! | `gendb_arguments.rs` | the query-only argument type `QueryArg` (with `text`) |
//! | `gendb_constraints.rs` | entry v5 only: `gendb_frontend::translator::emit_constraints_module` (the declared constraints over `schema_spec`) |
//! | `gendb_entry.rs` | fixed query entry v4, `verification/obligations/query_entry.rs`; v5: `verification/obligations/query_entry_v5.rs` |
//! | `gendb_entry/{runtime,parallel,layout,work,source_check}.rs`, `gendb_entry/stored.rs` | fixed, as in storage crates |
//! | `gendb_entry/results.rs` | fixed, query crates only: the columnar answer `ResultColumns` and its view (`verification/obligations/gendb_entry/results.rs`) |
//! | `gendb_entry/stores.rs` | generated: one `StoredParts` per storage use, `stored_ok` |
//!
//! The storages must cover the statement's demand ([`check_storage_coverage`]); that is a preflight for the author,
//! not a soundness condition (without a demanded column the claim would only be unprovable). The files that do not
//! depend on the storages form the statement check crate ([`query_statement_check_files`]), which the preflight
//! verifies before any author runs.

use super::claim::{AgentItem, TrustedAssumption, QUERY_AUTHOR_OBLIGATIONS, QUERY_TRUSTED_ASSUMPTIONS, QUERY_V5_AUTHOR_OBLIGATIONS, QUERY_V5_TRUSTED_ASSUMPTIONS};
use super::crate_files::{
    constraints_file, crate_root, file, library_files, schema_file, schema_widths, shared_entry_files, storage_module_files, stores_list_file,
};
use super::declared::DeclaredSource;
use super::params_module::{check_free_params, params_module, ArgumentAbi};
use super::storage_crate::StorageName;
use super::AssemblyError;
use crate::verus::FrameworkSource;
use gendb_frontend::columns::SourceDeclaration;
use gendb_frontend::params::Instance;
use gendb_frontend::translator::{emit_statement_module, EmitOptions};
use gendb_runtime::abi::{GENDB_ABI_SOURCE, GENDB_ARGUMENTS_SOURCE};
use std::collections::BTreeSet;
use std::fmt::Write as _;

/// Identity of the fixed query entry v4, recorded with builds, packages and claims.
pub const QUERY_ENTRY_IDENTITY: &str = gendb_artifacts::verus::VERUS_ENTRY_V4_IDENTITY;

/// `crate::gendb_entry` of a query crate without declared constraints (entry v4).
pub const QUERY_ENTRY_SOURCE: &str = include_str!("../../obligations/query_entry.rs");

/// Identity of the fixed query entry v5 (entry v4 plus the declared constraints as hypothesis of `bound_db`).
pub const QUERY_ENTRY_V5_IDENTITY: &str = gendb_artifacts::verus::VERUS_ENTRY_V5_IDENTITY;

/// `crate::gendb_entry` of a query crate whose schema declares integrity constraints (entry v5).
pub const QUERY_ENTRY_V5_SOURCE: &str = include_str!("../../obligations/query_entry_v5.rs");

/// `crate::gendb_entry::results` of every query crate (entry v4 and v5): the columnar answer and its fixed view.
pub const QUERY_RESULTS_SOURCE: &str = include_str!("../../obligations/gendb_entry/results.rs");

/// One fixed query entry: its identity, Verus text, the TCB's named assumptions and the name records use for it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct QueryEntry {
    pub identity: &'static str,
    pub source: &'static str,
    pub trusted_assumptions: &'static [TrustedAssumption],
    /// What its query author provides (`crate::agent`).
    pub author_obligations: &'static [AgentItem],
    /// Human-readable name (`query entry v4`).
    pub name: &'static str,
}

/// The fixed query entry v4.
pub const QUERY_ENTRY_V4: QueryEntry = QueryEntry {
    identity: QUERY_ENTRY_IDENTITY,
    source: QUERY_ENTRY_SOURCE,
    trusted_assumptions: QUERY_TRUSTED_ASSUMPTIONS,
    author_obligations: QUERY_AUTHOR_OBLIGATIONS,
    name: "query entry v4",
};

/// The fixed query entry v5.
pub const QUERY_ENTRY_V5: QueryEntry = QueryEntry {
    identity: QUERY_ENTRY_V5_IDENTITY,
    source: QUERY_ENTRY_V5_SOURCE,
    trusted_assumptions: QUERY_V5_TRUSTED_ASSUMPTIONS,
    author_obligations: QUERY_V5_AUTHOR_OBLIGATIONS,
    name: "query entry v5 (the declared integrity constraints as hypothesis)",
};

/// The fixed entry of every query crate of `inst`: v5 exactly when a table of its schema declares a constraint (then
/// the crate also carries `gendb_constraints.rs`), v4 otherwise. The one selector of crate assembly, preflight,
/// admission and records.
pub fn query_entry(inst: &Instance) -> QueryEntry {
    if inst.doc.tables.iter().any(|t| !t.constraints.is_empty()) { QUERY_ENTRY_V5 } else { QUERY_ENTRY_V4 }
}

/// One storage a query reads: its name, its declaration and the interface files of its checked storage build
/// (`stores/<name>/interface/**`, paths relative to `src/`, the build's bytes).
#[derive(Clone, Copy, Debug)]
pub struct StorageUse<'a> {
    pub name: &'a StorageName,
    pub declaration: &'a DeclaredSource,
    pub interface: &'a [FrameworkSource],
}

/// Every file of the query crate of the statement instance `inst` (fixed parameters substituted), whose demanded
/// columns are `delivered` (`gendb_frontend::columns::source_declaration` of `inst.doc`), reading `uses` in that order
/// (the order of `abi_query`'s `uses` and of `Stores`). `identity` names the statement in generated headers only. The
/// author's `agent/` module is the only missing part; the trusted shim is added by `with_trusted_shim`.
pub fn query_crate_files(
    inst: &Instance,
    delivered: &SourceDeclaration,
    uses: &[StorageUse<'_>],
    identity: &str,
) -> Result<Vec<FrameworkSource>, AssemblyError> {
    let schema = &inst.doc.tables;
    let widths = schema_widths(schema);
    check_free_params(&inst.free, ArgumentAbi::QueryArg)?;
    check_distinct_uses(uses)?;
    for u in uses {
        u.declaration.check_deliverable(&widths)?;
        check_interface_files(u)?;
    }
    check_storage_coverage(&DeclaredSource::of_statement(&inst.doc, delivered)?, uses)?;
    let query = emit_statement_module(inst, &EmitOptions::candidate()).map_err(AssemblyError::Emit)?;
    let (entry, constraints) = entry_and_constraints(inst)?;

    let header = format!("// FRAMEWORK FILE: crate root of a GenDB query crate over stored data (gendb_verification::obligations, {}).", entry.identity);
    let modules = ["schema", "gendb_constraints", "query", "stores", "gendb_params", "gendb_abi", "gendb_arguments", "gendb_entry", "agent"];
    let mut files = vec![crate_root(&header, &root_modules(&modules, constraints.is_some()))];
    files.extend(library_files());
    files.push(schema_file(schema)?);
    files.extend(constraints);
    files.push(file("query.rs", query));
    files.push(stores_list_file(&uses.iter().map(|u| u.name).collect::<Vec<_>>()));
    for u in uses {
        files.extend(storage_module_files(u.name, u.declaration, &widths));
        let mut interface = u.interface.to_vec();
        interface.sort_by(|a, b| a.path.cmp(&b.path));
        files.extend(interface);
    }
    files.push(file("gendb_params.rs", params_module(&inst.free, identity, ArgumentAbi::QueryArg)));
    files.push(file("gendb_abi.rs", GENDB_ABI_SOURCE));
    files.push(file("gendb_arguments.rs", GENDB_ARGUMENTS_SOURCE));
    files.push(file("gendb_entry.rs", entry.source));
    files.extend(shared_entry_files());
    files.push(file("gendb_entry/results.rs", QUERY_RESULTS_SOURCE));
    files.push(file("gendb_entry/stores.rs", stores_module(uses, identity, entry.identity)));
    Ok(files)
}

/// The fixed entry of `inst` and its `gendb_constraints.rs` (present exactly for entry v5).
fn entry_and_constraints(inst: &Instance) -> Result<(QueryEntry, Option<FrameworkSource>), AssemblyError> {
    // Both follow from the same condition: the emitter writes the module exactly when a table declares a constraint.
    Ok((query_entry(inst), constraints_file(&inst.doc.tables)?))
}

/// `modules` without `gendb_constraints` unless the crate carries it.
fn root_modules<'a>(modules: &[&'a str], constrained: bool) -> Vec<&'a str> {
    modules.iter().copied().filter(|m| constrained || *m != "gendb_constraints").collect()
}

/// The statement-level check crate of a query crate: every file of `query_crate_files(inst, ..)` that does not depend
/// on the storages the author chooses, checked by Verus before any author runs. It holds the SQLSpec library,
/// `schema.rs`, `gendb_constraints.rs` (entry v5: so `lemma_declared_schema` is proved here), `query.rs`,
/// `gendb_params.rs`, `gendb_abi.rs`, `gendb_arguments.rs` and the fixed entry submodules shared with storage crates
/// (`gendb_entry/{runtime,parallel,layout,work,source_check,stored}.rs`), with `gendb_entry.rs` reduced to their `pub
/// mod` declarations (the entry's items need the storages and the author's module) and a crate root without `stores`,
/// `agent` or the shim. Every file except `lib.rs` and `gendb_entry.rs` is byte-equal to its copy in every query
/// crate of the same statement. Deterministic, no I/O.
pub fn query_statement_check_files(inst: &Instance, identity: &str) -> Result<Vec<FrameworkSource>, AssemblyError> {
    check_free_params(&inst.free, ArgumentAbi::QueryArg)?;
    let query = emit_statement_module(inst, &EmitOptions::candidate()).map_err(AssemblyError::Emit)?;
    let (fixed_entry, constraints) = entry_and_constraints(inst)?;
    let header = format!(
        "// FRAMEWORK CHECK ONLY: crate root of the statement-level check of a GenDB query crate ({}); no storage, author module or shim.",
        fixed_entry.identity
    );
    let entry_submodules: Vec<FrameworkSource> = shared_entry_files().chain([file("gendb_entry/results.rs", QUERY_RESULTS_SOURCE)]).collect();
    let mut entry = String::from("// FRAMEWORK CHECK ONLY: the fixed submodules of the query entry (its items need the storages and the author's module).\n");
    for submodule in &entry_submodules {
        let name = submodule.path.strip_prefix("gendb_entry/").and_then(|p| p.strip_suffix(".rs")).expect("an entry submodule path");
        let _ = writeln!(entry, "pub mod {name};");
    }
    let modules = ["schema", "gendb_constraints", "query", "gendb_params", "gendb_abi", "gendb_arguments", "gendb_entry"];
    let mut files = vec![crate_root(&header, &root_modules(&modules, constraints.is_some()))];
    files.extend(library_files());
    files.push(schema_file(&inst.doc.tables)?);
    files.extend(constraints);
    files.push(file("query.rs", query));
    files.push(file("gendb_params.rs", params_module(&inst.free, identity, ArgumentAbi::QueryArg)));
    files.push(file("gendb_abi.rs", GENDB_ABI_SOURCE));
    files.push(file("gendb_arguments.rs", GENDB_ARGUMENTS_SOURCE));
    files.push(file("gendb_entry.rs", entry));
    files.extend(entry_submodules);
    Ok(files)
}

/// Every demanded column of the statement (`demand`, its declared source) is stored by some storage use, and every
/// table it enumerates is stored by some use (a table read only for its row count needs any storage of that table).
/// Otherwise `Coverage` with the reason `storage_does_not_cover_demand` and the first missing column or table.
pub fn check_storage_coverage(demand: &DeclaredSource, uses: &[StorageUse<'_>]) -> Result<(), AssemblyError> {
    let stored_tables: BTreeSet<usize> = uses.iter().flat_map(|u| u.declaration.tables.iter().map(|t| t.table_id)).collect();
    let stored_columns: BTreeSet<(usize, usize)> = uses
        .iter()
        .flat_map(|u| u.declaration.tables.iter().flat_map(|t| t.relation_columns().into_iter().map(move |(_, c)| (t.table_id, c.ordinal))))
        .collect();
    for t in &demand.tables {
        if !stored_tables.contains(&t.table_id) {
            return Err(AssemblyError::Coverage(format!("storage_does_not_cover_demand: no storage stores table {}", t.name)));
        }
        for (_, c) in t.relation_columns() {
            if !stored_columns.contains(&(t.table_id, c.ordinal)) {
                return Err(AssemblyError::Coverage(format!("storage_does_not_cover_demand: no storage stores {}.{}", t.name, c.name)));
            }
        }
    }
    Ok(())
}

fn check_distinct_uses(uses: &[StorageUse<'_>]) -> Result<(), AssemblyError> {
    if uses.is_empty() {
        return Err(AssemblyError::Storage("a query crate reads at least one storage".into()));
    }
    let names: BTreeSet<&StorageName> = uses.iter().map(|u| u.name).collect();
    if names.len() != uses.len() {
        return Err(AssemblyError::Storage("a storage is used twice".into()));
    }
    Ok(())
}

/// The interface files of a use lie under `stores/<name>/interface/`, include its `mod.rs` and are plain `.rs` paths.
pub(super) fn check_interface_files(u: &StorageUse<'_>) -> Result<(), AssemblyError> {
    let prefix = u.name.interface_prefix();
    for f in u.interface {
        let module_name = |part: &str| !part.is_empty() && part.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
        let plain = f.path.strip_prefix(&prefix).and_then(|rest| rest.strip_suffix(".rs")).is_some_and(|rest| rest.split('/').all(module_name));
        if !plain {
            return Err(AssemblyError::Storage(format!("interface file {} of storage {} is not a plain file under {prefix}", f.path, u.name)));
        }
    }
    if !u.interface.iter().any(|f| f.path == format!("{prefix}mod.rs")) {
        return Err(AssemblyError::Storage(format!("storage {} has no interface root {prefix}mod.rs", u.name)));
    }
    Ok(())
}

/// `gendb_entry/stores.rs`: `Stores` (one `StoredParts` per use, named after its storage), its view, `stored_ok` (the
/// conjunction of the storages' `represents` over their `stored_relations(db)`), the view of the host's use list and
/// the framework-only constructor and counter read.
pub(super) fn stores_module(uses: &[StorageUse<'_>], identity: &str, entry_identity: &str) -> String {
    let n = uses.len();
    let mut o = String::new();
    let _ = writeln!(o, "// FRAMEWORK FILE, GENERATED by gendb_verification::obligations ({entry_identity}): the storage uses of");
    let _ = writeln!(o, "// {identity}, in the order of `abi_query`'s `uses`.");
    for (k, u) in uses.iter().enumerate() {
        let _ = writeln!(o, "// Use {k} = storage `{}` (`crate::stores::{}`).", u.name, u.name);
    }
    o.push_str(
        "use vstd::prelude::*;\nuse crate::gendb_abi::Part;\nuse crate::spec::value::Database;\n\
         use super::layout::{parts_view, PartView};\nuse super::stored::{RequestCounts, StoredParts};\n\nverus! {\n\n",
    );
    let _ = writeln!(o, "/// Number of storage uses (the length of `abi_query`'s `uses`).\npub const STORAGE_USES: usize = {n};\n");
    o.push_str("/// The stored parts of every storage use, one field per use (named after the storage).\npub struct Stores {\n");
    for u in uses {
        let _ = writeln!(o, "    pub {}: StoredParts,", u.name);
    }
    o.push_str("}\n\n/// The view of `Stores`: the parts of every use.\npub struct StoresView {\n");
    for u in uses {
        let _ = writeln!(o, "    pub {}: Seq<PartView>,", u.name);
    }
    let view = uses.iter().map(|u| format!("{0}: self.{0}@", u.name)).collect::<Vec<_>>().join(", ");
    let _ = writeln!(
        o,
        "}}\n\nimpl View for Stores {{\n    type V = StoresView;\n\n    open spec fn view(&self) -> StoresView {{\n        StoresView {{ {view} }}\n    }}\n}}\n"
    );
    o.push_str(
        "/// The parts of every use represent the stored relations of `db` under that storage's own relation.\n\
         pub open spec fn stored_ok(sv: StoresView, db: Database) -> bool {\n",
    );
    for u in uses {
        let _ = writeln!(
            o,
            "    &&& crate::stores::{0}::interface::represents(sv.{0}, crate::stores::{0}::declaration::stored_relations(db))",
            u.name
        );
    }
    let fields = uses.iter().enumerate().map(|(k, u)| format!("{}: parts_view(uses[{k}]@)", u.name)).collect::<Vec<_>>().join(", ");
    let _ = writeln!(
        o,
        "}}\n\n/// The view of the host's use list (`uses[k]`: the parts of use k).\npub open spec fn uses_view(uses: Seq<Vec<Part>>) -> StoresView {{\n    StoresView {{ {fields} }}\n}}\n"
    );
    o.push_str(
        "/// The handles of the host's use list (framework only).\npub(super) fn open_stores(uses: Vec<Vec<Part>>) -> (s: Stores)\n    \
         requires uses.len() == STORAGE_USES,\n    ensures s@ == uses_view(uses@),\n{\n    let ghost given = uses@;\n    let mut uses = uses;\n",
    );
    for k in (0..n).rev() {
        let _ = writeln!(o, "    let parts_{k} = uses.pop().unwrap();\n    assert(parts_{k} == given[{k}]);");
    }
    let handles = uses.iter().enumerate().map(|(k, u)| format!("{}: StoredParts::new(parts_{k}, {k})", u.name)).collect::<Vec<_>>().join(", ");
    let _ = writeln!(o, "    Stores {{ {handles} }}\n}}\n");
    o.push_str("/// The request counts of every use, in use order (framework only).\npub(super) fn request_counts(s: &Stores) -> Vec<RequestCounts> {\n    let mut counts = Vec::new();\n");
    for u in uses {
        let _ = writeln!(o, "    counts.push(s.{}.request_counts());", u.name);
    }
    o.push_str("    counts\n}\n\n} // verus!\n");
    o
}
