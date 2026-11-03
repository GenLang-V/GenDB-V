//! The one assembly of a storage crate's framework files (fixed storage entry `gendb-verus-storage-entry-v1`, or
//! `gendb-verus-storage-entry-v2` for a builder that assumes the run's declared integrity constraints).
//!
//! A storage crate checks one storage: its generated declaration, the author's interface
//! (`stores/<name>/interface/**`) and builder (`builder/**`), the delivered source of the declared columns and the
//! fixed storage entry. The entry is chosen by the storage manifest's opt-in alone ([`storage_entry`]): v2 when it sets
//! `uses_declared_constraints`, which needs a run that declares constraints (otherwise `declared_constraints_unavailable`);
//! the declarations are the dataset schema's, i.e. the run's, never the author's. Without the opt-in every file is the
//! v1 text, byte for byte, in every run. Its files, relative to `src/` (author files are the only missing part):
//!
//! | Path | Origin |
//! |---|---|
//! | `lib.rs`, `stores.rs` | generated roots |
//! | `spec/**`, `exec/**`, `bridge/**`, `link.rs`, `link/**` | SQLSpec library |
//! | `schema.rs` | `gendb_frontend::translator::emit_column_schema_module` (the dataset DDL's columns) |
//! | `stores/<name>/{mod,declaration}.rs` | generated from the storage declaration (data only) |
//! | `gendb_source.rs`, `gendb_entry/binder.rs` | the v3 source and binder generators, for the storage declaration |
//! | `gendb_abi.rs` | runtime ABI types |
//! | `gendb_constraints.rs` | entry v2 only: `gendb_frontend::translator::emit_constraints_module` (the run's declared constraints; the query entry v5's text) |
//! | `gendb_entry.rs` | fixed storage entry, `verification/obligations/storage_entry.rs`; v2: `verification/obligations/storage_entry_v2.rs` |
//! | `gendb_entry/{runtime,parallel,layout,work,source_check}.rs` | fixed, the v3 files |
//! | `gendb_entry/stored.rs` | the registry's read handle (`gendb_registry::STORED_PARTS_SOURCE`) |
//! | `gendb_entry/storage.rs` | generated binding of the entry to `stores::<name>` |
//! | `stores/<name>/interface/**`, `builder/**` | the author's |
//!
//! A storage built from admitted storages ([`derived_storage_crate_files`], fixed entry
//! `gendb-verus-storage-entry-derived-v1`, `verification/obligations/storage_entry_derived.rs`) has no delivered source
//! (`gendb_source.rs`, `gendb_entry/binder.rs` are absent). Instead it carries, as a query crate does, every source
//! storage's `stores/<source>/{mod,declaration}.rs` and interface files (copied byte for byte from the source's checked
//! build) and the generated source handles `gendb_entry/sources.rs` (the query crates' `gendb_entry/stores.rs` text under
//! a name query crates do not have), plus `gendb_entry/derivation.rs` (the parts it
//! inherits unchanged from one source, and whether its builder assumes the declared constraints). Its builder reads
//! the sources only through their readers and `StoredParts` extents. When a source is a generated flat storage, the
//! crate also carries `sources_flat.rs` and `sources_flat/plain.rs` (`crate::sources_flat`, `obligations::flat_tables`): the
//! flat sources' tables by table and column id, so a builder can read them without naming a table or column. It is a crate-root module that
//! no query or engine crate has, and no storage closure contains it; a derived crate without a flat source assembles
//! byte for byte as before. When the derived storage's own declaration stores every column of every table (a storage
//! family's instance, `whole_schema::whole_schema_declaration`), the crate also carries `schema_exec.rs`
//! (`crate::schema_exec`: the column schema as executable data) and `whole_schema.rs` (`crate::whole_schema`: its stored
//! relations are the database's tables), crate-root modules in no closure, and its `sources_flat.rs` is the uniform
//! module (`FlatAccess::Uniform`): always there, with the nullable items for every schema (`nullable_column(t, c)` false
//! for every column of a schema without nullable columns, `nullable_column_slice` then never callable), so one family
//! builder text compiles and verifies in the instance of every workload; over a schema with a nullable flat column it
//! is the as-used text byte for byte. Every other derived crate is unchanged.

use super::binder_module::binder_module;
use super::claim::{AgentItem, TrustedAssumption, STORAGE_AUTHOR_OBLIGATIONS, STORAGE_TRUSTED_ASSUMPTIONS, STORAGE_V2_AUTHOR_OBLIGATIONS, STORAGE_V2_TRUSTED_ASSUMPTIONS};
use super::crate_files::{
    constraints_file, crate_root, file, library_files, schema_file, schema_widths, shared_entry_files, storage_module_files, stores_list_file,
};
use super::claim::{STORAGE_DERIVED_AUTHOR_OBLIGATIONS, STORAGE_DERIVED_TRUSTED_ASSUMPTIONS, STORAGE_DERIVED_V2_TRUSTED_ASSUMPTIONS};
use super::declared::DeclaredSource;
use super::flat_tables::{flat_access_files_with, FlatAccess, FlatAccessSite};
use super::query_crate::{check_interface_files, stores_module, StorageUse};
use super::source_module::{source_module, STORAGE_SOURCE, STORAGE_V2_SOURCE};
use super::whole_schema::{storage_schema_exec_file, whole_schema_declaration, whole_schema_file};
use super::AssemblyError;
use crate::verus::FrameworkSource;
use gendb_frontend::ast::TableDef;
use gendb_runtime::abi::GENDB_ABI_SOURCE;
use std::fmt;
use std::fmt::Write as _;

/// Identity of the fixed storage entry v1, recorded with storage builds and packages.
pub const STORAGE_ENTRY_IDENTITY: &str = gendb_artifacts::verus::VERUS_STORAGE_ENTRY_V1_IDENTITY;

/// `crate::gendb_entry` of a storage crate whose builder assumes no declared constraint (entry v1).
pub const STORAGE_ENTRY_SOURCE: &str = include_str!("../../obligations/storage_entry.rs");

/// Identity of the fixed storage entry v2 (entry v1 plus the declared constraints as a hypothesis of the build).
pub const STORAGE_ENTRY_V2_IDENTITY: &str = gendb_artifacts::verus::VERUS_STORAGE_ENTRY_V2_IDENTITY;

/// `crate::gendb_entry` of a storage crate whose builder assumes the run's declared constraints (entry v2).
pub const STORAGE_ENTRY_V2_SOURCE: &str = include_str!("../../obligations/storage_entry_v2.rs");

/// One fixed storage entry: its identity, Verus text, the TCB's named assumptions and the name records use for it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StorageEntry {
    pub identity: &'static str,
    pub source: &'static str,
    pub trusted_assumptions: &'static [TrustedAssumption],
    /// What its storage author provides (interface and builder).
    pub author_obligations: &'static [AgentItem],
    /// Human-readable name (`storage entry v1`).
    pub name: &'static str,
    /// The entry functions a package records with their checked `requires`/`ensures` text: the ABI function and the
    /// two theorems (their names differ between entries).
    pub recorded_items: [&'static str; 3],
}

/// The recorded items of the storage entries over source columns (v1, v2).
const SOURCE_ENTRY_ITEMS: [&str; 3] = ["abi_build_storage", "theorem_storage_built", "theorem_storage_build_total"];
/// The recorded items of the derived storage entry.
const DERIVED_ENTRY_ITEMS: [&str; 3] = ["abi_build_derived_storage", "theorem_storage_built", "theorem_storage_build_total"];

/// The fixed storage entry v1.
pub const STORAGE_ENTRY_V1: StorageEntry = StorageEntry {
    identity: STORAGE_ENTRY_IDENTITY,
    source: STORAGE_ENTRY_SOURCE,
    trusted_assumptions: STORAGE_TRUSTED_ASSUMPTIONS,
    author_obligations: STORAGE_AUTHOR_OBLIGATIONS,
    name: "storage entry v1",
    recorded_items: SOURCE_ENTRY_ITEMS,
};

/// The fixed storage entry v2.
pub const STORAGE_ENTRY_V2: StorageEntry = StorageEntry {
    identity: STORAGE_ENTRY_V2_IDENTITY,
    source: STORAGE_ENTRY_V2_SOURCE,
    trusted_assumptions: STORAGE_V2_TRUSTED_ASSUMPTIONS,
    author_obligations: STORAGE_V2_AUTHOR_OBLIGATIONS,
    name: "storage entry v2 (the builder assumes the declared integrity constraints)",
    recorded_items: SOURCE_ENTRY_ITEMS,
};

/// The fixed entry of a storage crate: v2 exactly when its manifest opts in with `uses_declared_constraints` (then the
/// crate also carries `gendb_constraints.rs`), v1 otherwise. The one selector of assembly, publication and records.
pub fn storage_entry(uses_declared_constraints: bool) -> StorageEntry {
    if uses_declared_constraints { STORAGE_ENTRY_V2 } else { STORAGE_ENTRY_V1 }
}

/// Identity of the derived storage entry (a storage built from admitted storages).
pub const STORAGE_ENTRY_DERIVED_IDENTITY: &str = gendb_artifacts::verus::VERUS_STORAGE_ENTRY_DERIVED_IDENTITY;

/// `crate::gendb_entry` of a storage crate built from admitted storages.
pub const STORAGE_ENTRY_DERIVED_SOURCE: &str = include_str!("../../obligations/storage_entry_derived.rs");

/// The derived storage entry, its builder assuming no declared constraint.
pub const STORAGE_ENTRY_DERIVED: StorageEntry = StorageEntry {
    identity: STORAGE_ENTRY_DERIVED_IDENTITY,
    source: STORAGE_ENTRY_DERIVED_SOURCE,
    trusted_assumptions: STORAGE_DERIVED_TRUSTED_ASSUMPTIONS,
    author_obligations: STORAGE_DERIVED_AUTHOR_OBLIGATIONS,
    name: "derived storage entry (built from admitted storages)",
    recorded_items: DERIVED_ENTRY_ITEMS,
};

/// The derived storage entry, its builder assuming the run's declared constraints (`derivation::assumed`).
pub const STORAGE_ENTRY_DERIVED_V2: StorageEntry = StorageEntry {
    identity: STORAGE_ENTRY_DERIVED_IDENTITY,
    source: STORAGE_ENTRY_DERIVED_SOURCE,
    trusted_assumptions: STORAGE_DERIVED_V2_TRUSTED_ASSUMPTIONS,
    author_obligations: STORAGE_DERIVED_AUTHOR_OBLIGATIONS,
    name: "derived storage entry (built from admitted storages; the builder assumes the declared integrity constraints)",
    recorded_items: DERIVED_ENTRY_ITEMS,
};

/// The fixed entry of a storage crate: derived when it is built from admitted storages, else [`storage_entry`].
pub fn storage_entry_of(derived: bool, uses_declared_constraints: bool) -> StorageEntry {
    match (derived, uses_declared_constraints) {
        (true, false) => STORAGE_ENTRY_DERIVED,
        (true, true) => STORAGE_ENTRY_DERIVED_V2,
        (false, constrained) => storage_entry(constrained),
    }
}

/// The admitted sources of a derived storage: one use per source (name, declaration and the interface files of its
/// checked build, in use order) and the source whose parts the new storage inherits unchanged, if any.
#[derive(Clone, Copy, Debug)]
pub struct Derivation<'a> {
    pub sources: &'a [StorageUse<'a>],
    /// Index into `sources` of the extended source.
    pub extends: Option<usize>,
}

/// Verus `--crate-name` of every storage crate.
pub const STORAGE_CRATE_NAME: &str = "gendb_store";

/// The name of a storage: its module `crate::stores::<name>` in storage and query crates and the field of
/// `Stores` in query crates. A lowercase Rust identifier (`[a-z][a-z0-9_]*`, at most 64 bytes) that is not a keyword.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StorageName(String);

impl StorageName {
    pub fn new(name: &str) -> Result<StorageName, AssemblyError> {
        let mut chars = name.chars();
        let lowercase_identifier = chars.next().is_some_and(|c| c.is_ascii_lowercase())
            && chars.all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_');
        if !lowercase_identifier || name.len() > 64 || RUST_KEYWORDS.contains(&name) {
            return Err(AssemblyError::Storage(format!(
                "storage name {name:?} is not a lowercase Rust identifier ([a-z][a-z0-9_]*, at most 64 bytes, not a keyword)"
            )));
        }
        Ok(StorageName(name.to_string()))
    }

    pub fn as_str(&self) -> &str {
        &self.0
    }

    /// `stores/<name>/interface/`: the prefix of the author's interface files.
    pub fn interface_prefix(&self) -> String {
        format!("stores/{}/interface/", self.0)
    }
}

impl fmt::Display for StorageName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

/// Strict and reserved Rust keywords (edition 2021), which cannot name a module.
const RUST_KEYWORDS: &[&str] = &[
    "as", "break", "const", "continue", "crate", "else", "enum", "extern", "false", "fn", "for", "if", "impl", "in", "let", "loop",
    "match", "mod", "move", "mut", "pub", "ref", "return", "self", "static", "struct", "super", "trait", "true", "type", "unsafe",
    "use", "where", "while", "async", "await", "dyn", "abstract", "become", "box", "do", "final", "macro", "override", "priv",
    "typeof", "unsized", "virtual", "yield", "try",
];

/// Every framework file of the storage crate of storage `name` over the dataset schema `schema` (a document's
/// `tables`, with the run's declared constraints) that stores `declaration` (`DeclaredSource::for_storage`), with the
/// fixed entry `storage_entry(uses_declared_constraints)`. The opt-in in a run whose schema declares no constraint is
/// refused (`declared_constraints_unavailable`), before any build. The author's `stores/<name>/interface/**` and
/// `builder/**` are the only missing parts; the trusted shim is added by `with_trusted_shim`.
///
/// Deterministic, no I/O: admission compares a build's files with a fresh call byte for byte, as for v3 candidates.
pub fn storage_crate_files(
    schema: &[TableDef],
    name: &StorageName,
    declaration: &DeclaredSource,
    uses_declared_constraints: bool,
) -> Result<Vec<FrameworkSource>, AssemblyError> {
    let widths = schema_widths(schema);
    declaration.check_deliverable(&widths)?;
    let entry = storage_entry(uses_declared_constraints);
    let constraints = if uses_declared_constraints {
        Some(constraints_file(schema)?.ok_or_else(|| {
            AssemblyError::Constraints(format!(
                "declared_constraints_unavailable: storage {name} sets uses_declared_constraints, but this run declares no integrity constraints"
            ))
        })?)
    } else {
        None
    };
    let identity = format!("storage {name}");
    let header = format!("// FRAMEWORK FILE: crate root of a GenDB storage crate (gendb_verification::obligations, {}).", entry.identity);
    let modules: &[&str] = if constraints.is_some() {
        &["schema", "gendb_constraints", "stores", "gendb_source", "gendb_abi", "gendb_entry", "builder"]
    } else {
        &["schema", "stores", "gendb_source", "gendb_abi", "gendb_entry", "builder"]
    };
    let site = if constraints.is_some() { &STORAGE_V2_SOURCE } else { &STORAGE_SOURCE };
    let mut files = vec![crate_root(&header, modules)];
    files.extend(library_files());
    files.push(schema_file(schema)?);
    files.extend(constraints);
    files.push(stores_list_file(&[name]));
    files.extend(storage_module_files(name, declaration, &widths));
    files.push(file("gendb_source.rs", source_module(declaration, &widths, &identity, site)));
    files.push(file("gendb_abi.rs", GENDB_ABI_SOURCE));
    files.push(file("gendb_entry.rs", entry.source));
    files.extend(shared_entry_files());
    files.push(file("gendb_entry/binder.rs", binder_module(declaration, &identity, entry.identity)));
    files.push(file("gendb_entry/storage.rs", storage_binding_module(name, declaration, entry.identity)));
    Ok(files)
}

/// Every framework file of the crate of storage `name` built from admitted storages (`derivation`), over the dataset
/// schema `schema`, storing `declaration`, with the derived entry ([`storage_entry_of`]). The new storage's name must
/// differ from every source's; the sources are distinct, each with its interface root. When a source is a generated
/// flat storage, or always for a whole-schema storage (a family's instance, uniform access), the crate carries
/// `sources_flat.rs` (see the module documentation). The author's
/// `stores/<name>/interface/**` and `builder/**` are the only missing parts; the trusted shim is added by
/// `with_trusted_shim`. Deterministic, no I/O.
pub fn derived_storage_crate_files(
    schema: &[TableDef],
    name: &StorageName,
    declaration: &DeclaredSource,
    derivation: Derivation<'_>,
    uses_declared_constraints: bool,
) -> Result<Vec<FrameworkSource>, AssemblyError> {
    let widths = schema_widths(schema);
    declaration.check_deliverable(&widths)?;
    let sources = derivation.sources;
    if sources.is_empty() {
        return Err(AssemblyError::Storage(format!("storage {name} is built from admitted storages but names none")));
    }
    let mut names = std::collections::BTreeSet::new();
    for source in sources {
        if source.name == name || !names.insert(source.name) {
            return Err(AssemblyError::Storage(format!(
                "storage {name}: source {} is named twice or has the new storage's name (a derived storage needs its own name)",
                source.name
            )));
        }
        source.declaration.check_deliverable(&widths)?;
        check_interface_files(source)?;
    }
    if derivation.extends.is_some_and(|k| k >= sources.len()) {
        return Err(AssemblyError::Storage(format!("storage {name}: the extended source is not one of its sources")));
    }
    let entry = storage_entry_of(true, uses_declared_constraints);
    let constraints = if uses_declared_constraints {
        Some(constraints_file(schema)?.ok_or_else(|| {
            AssemblyError::Constraints(format!(
                "declared_constraints_unavailable: storage {name} sets uses_declared_constraints, but this run declares no integrity constraints"
            ))
        })?)
    } else {
        None
    };
    let identity = format!("storage {name} (built from admitted storages)");
    // A whole-schema storage (a storage family's instance): the executable schema and its relations by table id, and the
    // uniform flat access, so one family builder text compiles in the instance of every schema.
    let whole = whole_schema_declaration(schema, declaration);
    let access = if whole { FlatAccess::Uniform } else { FlatAccess::AsUsed };
    let flat_access = flat_access_files_with(schema, sources, FlatAccessSite::DerivedSources, access);
    let whole_schema = whole.then(|| [storage_schema_exec_file(schema), whole_schema_file(schema, &[name])]);
    let header = format!("// FRAMEWORK FILE: crate root of a GenDB storage crate built from admitted storages (gendb_verification::obligations, {}).", entry.identity);
    let mut modules: Vec<&str> = if constraints.is_some() {
        vec!["schema", "gendb_constraints", "stores", "gendb_abi", "gendb_entry"]
    } else {
        vec!["schema", "stores", "gendb_abi", "gendb_entry"]
    };
    if !flat_access.is_empty() {
        modules.push(FlatAccessSite::DerivedSources.module());
    }
    if whole_schema.is_some() {
        modules.extend(["schema_exec", "whole_schema"]);
    }
    modules.push("builder");
    let mut files = vec![crate_root(&header, &modules)];
    files.extend(library_files());
    files.push(schema_file(schema)?);
    files.extend(constraints.clone());
    let all_names: Vec<&StorageName> = sources.iter().map(|u| u.name).chain([name]).collect();
    files.push(stores_list_file(&all_names));
    for source in sources {
        files.extend(storage_module_files(source.name, source.declaration, &widths));
        let mut interface = source.interface.to_vec();
        interface.sort_by(|a, b| a.path.cmp(&b.path));
        files.extend(interface);
    }
    files.extend(storage_module_files(name, declaration, &widths));
    files.push(file("gendb_abi.rs", GENDB_ABI_SOURCE));
    files.push(file("gendb_entry.rs", entry.source));
    files.extend(shared_entry_files());
    files.push(file("gendb_entry/sources.rs", stores_module(sources, &identity, entry.identity)));
    files.push(file("gendb_entry/derivation.rs", derivation_module(name, derivation, constraints.is_some(), entry.identity)));
    files.push(file("gendb_entry/storage.rs", derived_binding_module(name, entry.identity)));
    files.extend(flat_access);
    files.extend(whole_schema.into_iter().flatten());
    Ok(files)
}

/// `gendb_entry/derivation.rs`: the parts the new storage inherits (the extended source's whole part list, or none)
/// and what its builder assumes of the database besides its sources (the declared constraints, or nothing).
fn derivation_module(name: &StorageName, derivation: Derivation<'_>, constrained: bool, entry_identity: &str) -> String {
    let mut o = String::new();
    let _ = writeln!(o, "// FRAMEWORK FILE, GENERATED by gendb_verification::obligations ({entry_identity}): the derivation of storage `{name}`.");
    let (inherited, extended) = match derivation.extends {
        Some(k) => (format!("sv.{}", derivation.sources[k].name), format!("source `{}`: its parts, unchanged, come first", derivation.sources[k].name)),
        None => ("Seq::empty()".to_string(), "no source: all of its parts come from its builder".to_string()),
    };
    let _ = writeln!(o, "// It extends {extended}.");
    o.push_str("use vstd::prelude::*;\nuse crate::spec::value::Database;\nuse super::layout::PartView;\nuse super::sources::StoresView;\n");
    if constrained {
        o.push_str("use crate::gendb_constraints::declared_db;\nuse crate::spec::constraints::constraints_hold;\n");
    }
    let assumed = if constrained { "constraints_hold(declared_db(db))" } else { "true" };
    let _ = write!(
        o,
        "\nverus! {{\n\n/// The parts the new storage inherits unchanged, before its builder's parts.\n\
         pub open spec fn inherited(sv: StoresView) -> Seq<PartView> {{\n    {inherited}\n}}\n\n\
         /// What the builder may assume of the database besides its sources.\n\
         pub open spec fn assumed(db: Database) -> bool {{\n    {assumed}\n}}\n\n}} // verus!\n"
    );
    o
}

/// `gendb_entry/storage.rs` of a derived storage crate: the entry's names for the new storage's `represents` and
/// `stored_relations`.
fn derived_binding_module(name: &StorageName, entry_identity: &str) -> String {
    format!(
        "// FRAMEWORK FILE, GENERATED by gendb_verification::obligations ({entry_identity}): binds the derived storage\n\
         // entry to storage `{name}` (its interface's `represents` and its declaration's `stored_relations`).\n\
         use vstd::prelude::*;\n\
         pub use crate::stores::{name}::interface::represents;\npub use crate::stores::{name}::declaration::stored_relations;\n\nverus! {{\n\n{}}} // verus!\n",
        lossless_theorem(name)
    )
}

/// `gendb_entry/storage.rs`: the storage entry's names for the storage's `represents` and `stored_relations`, and the
/// proof that a bound source's relations are the stored relations of its database (the two generated modules state
/// the same table ids and ordinals).
fn storage_binding_module(name: &StorageName, declaration: &DeclaredSource, entry_identity: &str) -> String {
    let mut o = String::new();
    let _ = writeln!(o, "// FRAMEWORK FILE, GENERATED by gendb_verification::obligations ({entry_identity}): binds the storage");
    let _ = writeln!(o, "// entry to storage `{name}` (its interface's `represents` and its declaration's `stored_relations`).");
    let _ = write!(
        o,
        "use vstd::prelude::*;\nuse crate::spec::value::Database;\nuse crate::gendb_source::*;\n\
         use crate::stores::{name}::declaration::*;\npub use crate::stores::{name}::interface::represents;\n\
         pub use crate::stores::{name}::declaration::stored_relations;\n\nverus! {{\n\n"
    );
    o.push_str(
        "/// A source bound to `db` (the storage source binding) delivers exactly the stored relations of `db`.\n\
         pub proof fn lemma_source_is_stored(v: SourceView, db: Database)\n    requires source_columns_are_tables(v, db),\n    \
         ensures tables(v) == stored_relations(db),\n{\n",
    );
    for j in 0..declaration.tables.len() {
        let _ = writeln!(o, "    assert(source_table_t{j}() == stored_table_t{j}() && source_cols_t{j}() == stored_cols_t{j}());");
    }
    o.push_str("    assert(tables(v) =~= stored_relations(db));\n}\n\n");
    o.push_str(&lossless_theorem(name));
    o.push_str("} // verus!\n");
    o
}

/// The fixed theorem of complete lossless storage, in every storage crate's binding module: the
/// parts determine the relations they represent, so every stored column of every stored table is recoverable from the
/// parts alone. Proved by the author's `lemma_represents_determines` (claim item `lossless`).
fn lossless_theorem(name: &StorageName) -> String {
    format!(
        "/// Complete lossless storage: two relations the same parts represent are equal, so the parts determine every\n\
         /// stored column of every stored table (proved by the author's `lemma_represents_determines`).\n\
         pub proof fn theorem_storage_lossless(parts: Seq<crate::gendb_entry::layout::PartView>, a: Seq<Seq<crate::spec::value::Row>>, b: Seq<Seq<crate::spec::value::Row>>)\n    \
         requires\n        represents(parts, a),\n        represents(parts, b),\n    ensures\n        a == b,\n{{\n    \
         crate::stores::{name}::interface::lemma_represents_determines(parts, a, b);\n}}\n\n"
    )
}
