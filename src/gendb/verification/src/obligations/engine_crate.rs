//! The one assembly of an engine crate (fixed engine entry `gendb-verus-engine-entry-v1`): one verified engine for a
//! whole schema. It reads the storages it names and answers any supported statement, which arrives at call time as AST
//! bytes (`gendb_frontend::engine_encode`); nothing in the crate is per statement.
//!
//! Files, relative to `src/` (the author's `agent/**` is the only missing part; the trusted shim is added by
//! `with_trusted_shim` with `gendb_runtime::abi::GENDB_ENGINE_SHIM_SOURCE`):
//!
//! | Path | Origin |
//! |---|---|
//! | `lib.rs`, `stores.rs` | generated roots |
//! | `spec/**`, `exec/**`, `bridge/**`, `link.rs`, `link/**` | SQLSpec library |
//! | `engine_link/**` | the engine-only proof toolkit, embedded from `sqlspec/engine_link/` without `examples/` ([`engine_toolkit_files`]) |
//! | `schema.rs` | `gendb_frontend::translator::emit_column_schema_module` (the dataset DDL's columns) |
//! | `gendb_constraints.rs` | `gendb_frontend::translator::emit_constraints_module` (required: the engine claim assumes the declared constraints) |
//! | `stores/<name>/{mod,declaration}.rs` | generated from each storage's declaration (the storage build's text) |
//! | `stores/<name>/interface/**` | copied unchanged from the storage's checked build |
//! | `gendb_abi.rs` | runtime ABI types (shared with storage crates) |
//! | `gendb_ast_codec.rs` | the AST codec (`runtime/verus/engine_codec.rs`: `decode_spec`, `decode_query`, `render_spec`, `render_query`) |
//! | `gendb_entry.rs` | fixed engine entry, `verification/obligations/engine_entry.rs` |
//! | `gendb_entry/{runtime,parallel,layout,work,source_check}.rs`, `gendb_entry/stored.rs` | fixed, as in storage and query crates |
//! | `gendb_entry/results.rs` | fixed, as in query crates: the columnar answer |
//! | `gendb_entry/stores.rs` | generated, as in query crates: one `StoredParts` per storage use, `stored_ok` |
//! | `gendb_entry/schema_exec.rs` | generated: the column schema as executable data, proved equal to `schema_spec()` |
//! | `flat_tables.rs`, `flat_tables/plain.rs` | generated, when a use is a generated flat storage (or always in a stage run's crate, `FlatAccess::Uniform`): its tables by table and column id (`flat_tables`), with the plain-columns vocabulary |
//! | `whole_schema.rs` | generated, when a use stores every column of every table and is not a generated flat storage (a storage family's instance): `lemma_<store>`, its stored relations are the database's tables (`whole_schema`) |
//!
//! Every storage closure file is the same text as in storage and query crates, so the composition rule
//! (`check_storage_composition`) applies unchanged. The engine-only files (`gendb_ast_codec.rs`, the entry,
//! `schema_exec.rs`, `engine_link/**`, `flat_tables.rs`) are in no storage's closure: admitted storages stay current.
//! A crate none of whose uses is a generated flat storage has no `flat_tables.rs` and the same crate root as before, so
//! it assembles byte for byte as before the flat access existed (unit test with a golden digest); likewise a crate
//! without a whole-schema use has no `whole_schema.rs`.
//!
//! **Stage runs** (one engine source, one crate per workload): each workload's
//! crate is this assembly over that workload's schema and uses with [`FlatAccess::Uniform`]
//! ([`engine_crate_files_with`]): `flat_tables.rs` is always there, with its nullable items, so the shared `agent/**`
//! compiles against every workload's crate. The author's `agent/` then holds the shared engine and, as
//! `agent/workload/**`, that workload's module (composed by the freeze, `gendb_synthesis::engine::submission`); nothing
//! else of the assembly changes, and every other crate keeps [`FlatAccess::AsUsed`].
//!
//! [`check_engine_coverage`] is the admission rule that the uses together store every column of every table (with each
//! storage's lossless lemma this makes the bound database unique); it is not needed for soundness and the assembly does
//! not apply it.

use super::claim::ENGINE_CLAIM_V1;
use super::crate_files::{constraints_file, crate_root, file, library_files, schema_file, schema_widths, shared_entry_files, storage_module_files, stores_list_file};
use super::flat_tables::{flat_access_files_with, generated_flat_table, FlatAccess, FlatAccessSite};
use super::storage_crate::StorageName;
use super::whole_schema::{schema_exec_text, whole_schema_declaration, whole_schema_file};
use super::query_crate::{check_interface_files, stores_module, StorageUse, QUERY_RESULTS_SOURCE};
use super::AssemblyError;
use crate::verus::FrameworkSource;
use gendb_frontend::ast::TableDef;
use gendb_runtime::abi::{ENGINE_CODEC_SOURCE, GENDB_ABI_SOURCE};
use std::collections::BTreeSet;

/// Identity of the fixed engine entry, recorded with engine builds, packages and claims (the claim's own).
pub const ENGINE_ENTRY_IDENTITY: &str = ENGINE_CLAIM_V1.entry_identity;

/// `crate::gendb_entry` of an engine crate.
pub const ENGINE_ENTRY_SOURCE: &str = include_str!("../../obligations/engine_entry.rs");

/// The Verus `--crate-name` of engine crates (their library is `libgendb_engine.so`).
pub const ENGINE_CRATE_NAME: &str = "gendb_engine";

/// The logical path of the AST codec in engine crates (`crate::gendb_ast_codec`).
pub const ENGINE_CODEC_PATH: &str = "gendb_ast_codec.rs";

/// The directory of the engine-only proof toolkit in engine crates (`crate::engine_link`, root `engine_link/mod.rs`).
pub const ENGINE_TOOLKIT_DIRECTORY: &str = "engine_link/";

/// The engine-only proof toolkit, embedded from `sqlspec/engine_link/` (logical path, text), root first, then in the
/// order of `engine_link/mod.rs`. Its `examples/` (the checked instances) are left out: they are the separate module
/// `engine_pins` of the toolkit's own check crate only. SQLSpec's build does not embed this folder (SQLSpec stays
/// unchanged), so the list is kept here; a test checks it is exactly the folder's `.rs` files outside `examples/`.
const ENGINE_TOOLKIT: &[(&str, &str)] = &[
    ("engine_link/mod.rs", include_str!("../../../sqlspec/engine_link/mod.rs")),
    ("engine_link/bag.rs", include_str!("../../../sqlspec/engine_link/bag.rs")),
    ("engine_link/ops.rs", include_str!("../../../sqlspec/engine_link/ops.rs")),
    ("engine_link/bound.rs", include_str!("../../../sqlspec/engine_link/bound.rs")),
    ("engine_link/locality.rs", include_str!("../../../sqlspec/engine_link/locality.rs")),
    ("engine_link/classes.rs", include_str!("../../../sqlspec/engine_link/classes.rs")),
    ("engine_link/classes_values.rs", include_str!("../../../sqlspec/engine_link/classes_values.rs")),
    ("engine_link/classes_sound.rs", include_str!("../../../sqlspec/engine_link/classes_sound.rs")),
    ("engine_link/classes_exec_ops.rs", include_str!("../../../sqlspec/engine_link/classes_exec_ops.rs")),
    ("engine_link/classes_exec.rs", include_str!("../../../sqlspec/engine_link/classes_exec.rs")),
    ("engine_link/order_free.rs", include_str!("../../../sqlspec/engine_link/order_free.rs")),
    ("engine_link/congruence.rs", include_str!("../../../sqlspec/engine_link/congruence.rs")),
    ("engine_link/decorrelate.rs", include_str!("../../../sqlspec/engine_link/decorrelate.rs")),
    ("engine_link/colmap.rs", include_str!("../../../sqlspec/engine_link/colmap.rs")),
    ("engine_link/remap.rs", include_str!("../../../sqlspec/engine_link/remap.rs")),
    ("engine_link/joins.rs", include_str!("../../../sqlspec/engine_link/joins.rs")),
    ("engine_link/keys.rs", include_str!("../../../sqlspec/engine_link/keys.rs")),
    ("engine_link/topk.rs", include_str!("../../../sqlspec/engine_link/topk.rs")),
];

/// The engine-only proof toolkit files every engine crate carries under [`ENGINE_TOOLKIT_DIRECTORY`] (root
/// `engine_link/mod.rs` first): the same text in every engine crate, outside every storage closure.
pub fn engine_toolkit_files() -> Vec<FrameworkSource> {
    ENGINE_TOOLKIT.iter().map(|&(path, text)| file(path, text)).collect()
}

/// Every file of the engine crate over the dataset schema `schema` (a document's `tables`, with the request's declared
/// integrity constraints), reading `uses` in that order (the order of `abi_engine_query`'s `uses` and of `Stores`).
/// The crate carries the engine-only proof toolkit ([`engine_toolkit_files`], module `crate::engine_link`) and, when a
/// use is a generated flat storage, the flat access module `flat_tables.rs` (`obligations::flat_tables`). `identity`
/// names the engine in generated headers only. The author's `agent/` module is the only missing part; the trusted shim
/// is added by `with_trusted_shim`.
///
/// Refused: a schema without declared integrity constraints (`engine_requires_declared_constraints`: the engine claim
/// is stated under them), no storage use, a storage used twice, an undeliverable declaration, malformed interface
/// paths.
pub fn engine_crate_files(
    schema: &[TableDef],
    uses: &[StorageUse<'_>],
    identity: &str,
) -> Result<Vec<FrameworkSource>, AssemblyError> {
    engine_crate_files_with(schema, uses, identity, FlatAccess::AsUsed)
}

/// [`engine_crate_files`] with the flat access module `access`: [`FlatAccess::AsUsed`] is that assembly;
/// [`FlatAccess::Uniform`] is the crate of one workload of a stage run (module documentation), whose `flat_tables.rs`
/// is always present with its nullable items. Same refusals.
pub fn engine_crate_files_with(
    schema: &[TableDef],
    uses: &[StorageUse<'_>],
    identity: &str,
    access: FlatAccess,
) -> Result<Vec<FrameworkSource>, AssemblyError> {
    let widths = schema_widths(schema);
    if uses.is_empty() {
        return Err(AssemblyError::Storage("an engine crate reads at least one storage".into()));
    }
    let names: BTreeSet<_> = uses.iter().map(|u| u.name).collect();
    if names.len() != uses.len() {
        return Err(AssemblyError::Storage("a storage is used twice".into()));
    }
    for u in uses {
        u.declaration.check_deliverable(&widths)?;
        check_interface_files(u)?;
    }
    let Some(constraints) = constraints_file(schema)? else {
        return Err(AssemblyError::Constraints(
            "engine_requires_declared_constraints: the engine claim is stated under the request's declared integrity constraints, and \
             this schema declares none"
                .into(),
        ));
    };

    let flat_access = flat_access_files_with(schema, uses, FlatAccessSite::Engine, access);
    // The whole-schema module, for the uses that store every column of every table and are not generated flat storages.
    let whole: Vec<&StorageName> = uses.iter().filter(|u| whole_schema_declaration(schema, u.declaration) && generated_flat_table(schema, u).is_none()).map(|u| u.name).collect();
    let whole_schema = (!whole.is_empty()).then(|| whole_schema_file(schema, &whole));
    let header = format!("// FRAMEWORK FILE: crate root of a GenDB engine crate (gendb_verification::obligations, {ENGINE_ENTRY_IDENTITY}).");
    let mut modules = vec!["engine_link", "schema", "gendb_constraints", "stores", "gendb_abi", "gendb_ast_codec", "gendb_entry"];
    if !flat_access.is_empty() {
        modules.push(FlatAccessSite::Engine.module());
    }
    if whole_schema.is_some() {
        modules.push("whole_schema");
    }
    modules.push("agent");
    let mut files = vec![crate_root(&header, &modules)];
    files.extend(library_files());
    files.extend(engine_toolkit_files());
    files.push(schema_file(schema)?);
    files.push(constraints);
    files.push(stores_list_file(&uses.iter().map(|u| u.name).collect::<Vec<_>>()));
    for u in uses {
        files.extend(storage_module_files(u.name, u.declaration, &widths));
        let mut interface = u.interface.to_vec();
        interface.sort_by(|a, b| a.path.cmp(&b.path));
        files.extend(interface);
    }
    files.push(file("gendb_abi.rs", GENDB_ABI_SOURCE));
    files.push(file(ENGINE_CODEC_PATH, ENGINE_CODEC_SOURCE));
    files.push(file("gendb_entry.rs", ENGINE_ENTRY_SOURCE));
    files.extend(shared_entry_files());
    files.push(file("gendb_entry/results.rs", QUERY_RESULTS_SOURCE));
    files.push(file("gendb_entry/stores.rs", engine_stores_module(uses, identity)));
    // The engine entry hands the executable schema to the verified `check_ordered`.
    files.push(file("gendb_entry/schema_exec.rs", schema_exec_text(schema, ENGINE_ENTRY_IDENTITY)));
    files.extend(flat_access);
    files.extend(whole_schema);
    Ok(files)
}

/// `gendb_entry/stores.rs` of an engine crate: the query crates' generated module (one `StoredParts` per use,
/// `stored_ok`, `uses_view`), with its comments naming the engine entry's `abi_engine_query`.
fn engine_stores_module(uses: &[StorageUse<'_>], identity: &str) -> String {
    stores_module(uses, identity, ENGINE_ENTRY_IDENTITY).replace("`abi_query`'s `uses`", "`abi_engine_query`'s `uses`")
}

/// The engine's storage uses together store every column of every table of `schema` (a row-count carrier is not a
/// stored column). Otherwise `Coverage` with the reason `engine_storage_coverage_incomplete` and the first missing column.
pub fn check_engine_coverage(schema: &[TableDef], uses: &[StorageUse<'_>]) -> Result<(), AssemblyError> {
    let stored: BTreeSet<(usize, usize)> = uses
        .iter()
        .flat_map(|u| u.declaration.tables.iter().flat_map(|t| t.relation_columns().into_iter().map(move |(_, c)| (t.table_id, c.ordinal))))
        .collect();
    for (table_id, table) in schema.iter().enumerate() {
        for (ordinal, column) in table.columns.iter().enumerate() {
            if !stored.contains(&(table_id, ordinal)) {
                return Err(AssemblyError::Coverage(format!(
                    "engine_storage_coverage_incomplete: no storage use stores {}.{}",
                    table.name, column.name
                )));
            }
        }
    }
    Ok(())
}
