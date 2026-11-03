//! The registry of the storage-aware verified path: one structured index of the reusable definitions and interfaces
//! that storage crates, query crates (fixed entry v4/v5) and engine crates (fixed engine entry v1) are assembled from,
//! and the one physical definition of the stored-parts read interface ([`STORED_PARTS_SOURCE`],
//! `registry/verus/stored.rs`).
//!
//! The index is not a second definition of anything. Each [`Definition`] names the file that is the authority for it
//! (SQLSpec for the SQL meaning and the fixed source/answer definitions, the frontend for the typed AST and the
//! emitted schema and statement, `verification/obligations` for the fixed claims and the generated modules, this crate
//! for the read interface, the author for interfaces, builders and queries) and the logical path where assembled
//! crates carry it. Consumers:
//! - `gendb_verification::obligations` copies [`STORED_PARTS_SOURCE`] into both crate kinds, computes a storage's
//!   dependency closure from the [`Presence::Shared`] definitions ([`closure_definition`]) and finds the author files
//!   the source rules apply to ([`author_definition`]); its tests check that the assembled crates contain exactly the
//!   files this index lists for their kind;
//! - author contexts (synthesis) render [`DEFINITIONS`] (serializable) so authors see which files hold which items
//!   without reading framework source.
//!
//! Logical paths are relative to a crate's `src/`. `<storage>` stands for a storage's name (its module
//! `crate::stores::<storage>`); a path ending in `/**` covers every file below that directory.
//!
//! Most definitions are in every crate of their kind ([`definitions_for`]). A few are generated only when a crate's
//! storages call for them ([`Presence::Optional`], [`optional_definitions_for`]): the flat access modules of crates
//! that read generated flat storages (`flat_tables.rs`, `sources_flat.rs`) and the source handles of storage crates
//! built from admitted storages (`gendb_entry/sources.rs`, `gendb_entry/derivation.rs`). Such a storage crate carries
//! those instead of the source binding files of a storage built from source columns (`gendb_source.rs`,
//! `gendb_entry/binder.rs`), and its `gendb_entry.rs` and `gendb_entry/storage.rs` are the derived entry and binding
//! under the same paths. A storage that stores every column of every table (the instance of a storage family in a run
//! of several workloads) adds the whole-schema files ([`WHOLE_SCHEMA_DEFINITIONS`]): `whole_schema.rs` in its storage
//! crate and in the engine crates that read it, and `schema_exec.rs` in its storage crate.
//!
//! A crate is assembled in one [`ConstraintMode`]: without declared integrity constraints (a query crate of a request
//! that declares none, and every storage crate that does not opt in), or under the request's declared constraints (a
//! query crate of the fixed entry v5, a storage crate of the storage entry v2), which carries the generated
//! `gendb_constraints.rs` and its kind's constrained entry instead of the unconstrained one. Each definition names the
//! modes whose crates carry it.
//! Engine crates exist only under declared constraints (their entry's claim is stated under them).

use serde::Serialize;

/// The stored-parts read handle (`crate::gendb_entry::stored` in storage and query crates): extents of immutable parts
/// and descriptive request counters. Verus text, checked in every crate that carries it.
pub const STORED_PARTS_SOURCE: &str = include_str!("../verus/stored.rs");

/// The placeholder for a storage's name in [`Definition::crate_path`].
pub const STORAGE_PLACEHOLDER: &str = "<storage>";

/// The crate kinds of the storage-aware path.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum CrateKind {
    /// A storage crate: one storage's declaration, interface and builder, and the fixed storage entry.
    Storage,
    /// A query crate of the fixed entry v4: one statement, its query code and the interfaces of the storages it reads.
    Query,
    /// An engine crate of the fixed engine entry v1: one engine for the whole schema (statements arrive as AST bytes at
    /// call time), its code and the interfaces of the storages it reads.
    Engine,
}

/// Whether a crate is assembled under the request's declared integrity constraints.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ConstraintMode {
    /// No declared constraint assumed: query entry v4, storage entry v1.
    Unconstrained,
    /// Under the declared constraints: query entry v5 or storage entry v2, with `gendb_constraints.rs`.
    Declared,
}

/// Definitions carried by crates of every mode.
const EVERY_MODE: &[ConstraintMode] = &[ConstraintMode::Unconstrained, ConstraintMode::Declared];
/// Definitions carried only by crates without declared constraints.
const UNCONSTRAINED: &[ConstraintMode] = &[ConstraintMode::Unconstrained];
/// Definitions carried only by crates under declared constraints.
const DECLARED: &[ConstraintMode] = &[ConstraintMode::Declared];

/// Where a definition appears.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Presence {
    /// Byte for byte the same text in a storage crate and in every query crate that reads that storage: the
    /// dependency closure of the storage's interface (compared at admission). Equal text is not enough on its own for
    /// equal meaning (Rust resolves methods through every `impl` of the crate, and some macros expand differently per
    /// crate): the claim also rests on the central author-source rules (`gendb_verification::verus::scan_source`:
    /// implementation ownership, the supported macros) holding for every author file of both builds, and on the same
    /// pinned toolchain. See `gendb_verification::obligations` (`closure`).
    Shared,
    /// In both kinds and outside every storage closure: compared at admission with a fresh generation of its own crate
    /// (crate roots, the entry roots, the `stores` module list, the declared-constraints module).
    PerKind,
    /// Only in storage crates.
    StorageOnly,
    /// Only in query crates.
    QueryOnly,
    /// Only in the crates that read stored parts through `Stores` and answer statements: query and engine crates.
    Readers,
    /// Only in engine crates.
    EngineOnly,
    /// Only in some crates of one kind: generated when the crate's storages call for it (the definition's summary says
    /// when), for example the flat access module of an engine crate that reads generated flat storages. Outside every
    /// storage closure. [`definitions_for`] does not list it (it lists what every crate of a kind carries);
    /// [`optional_definitions_for`] does.
    Optional(CrateKind),
    /// Not copied into crates: the authority other definitions are generated from.
    Reference,
}

impl Presence {
    /// Whether every crate of `kind` carries the definition (an [`Presence::Optional`] one: no, only some do).
    pub fn in_crate(self, kind: CrateKind) -> bool {
        match self {
            Presence::Shared | Presence::PerKind => true,
            Presence::StorageOnly => kind == CrateKind::Storage,
            Presence::QueryOnly => kind == CrateKind::Query,
            Presence::Readers => kind == CrateKind::Query || kind == CrateKind::Engine,
            Presence::EngineOnly => kind == CrateKind::Engine,
            Presence::Optional(_) | Presence::Reference => false,
        }
    }

    /// Whether some crates of `kind` carry the definition and others do not ([`Presence::Optional`]).
    pub fn optional_in(self, kind: CrateKind) -> bool {
        self == Presence::Optional(kind)
    }
}

/// What a definition is for.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum Role {
    /// Part of the fixed meaning the claims are stated with (SQL semantics, schema, statement, source relations).
    FixedMeaning,
    /// A fixed claim: an entry's obligations and theorems.
    FixedClaim,
    /// How stored data is represented and read.
    ReadInterface,
    /// Checked library code and verified helpers authors may call (never part of the claim's meaning).
    Library,
    /// Generated data-only binding code (column/argument binders, module lists, crate roots).
    Binding,
    /// Written by an author; the listed items are required (optional items are the author's choice).
    Author,
}

/// Who writes a definition's text.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case", tag = "kind")]
pub enum Origin {
    /// A source file, relative to `src/gendb/`, copied unchanged (or read by the frontend).
    Source { path: &'static str },
    /// Generated by `generator` from `input` (data only).
    Generated { generator: &'static str, input: &'static str },
    /// The storage author (workload or query author) or the query author.
    Author,
}

/// One reusable definition or interface.
#[derive(Clone, Copy, Debug, Serialize)]
pub struct Definition {
    pub name: &'static str,
    /// Logical path in assembled crates (`None` for a [`Presence::Reference`]).
    pub crate_path: Option<&'static str>,
    pub presence: Presence,
    /// The constraint modes whose crates carry it.
    pub modes: &'static [ConstraintMode],
    pub role: Role,
    pub origin: Origin,
    /// The items authors use or must provide (paths relative to the file's module).
    pub items: &'static [&'static str],
    pub summary: &'static str,
}

impl Definition {
    /// Whether the logical crate path `path` belongs to this definition, for the storage named `storage`.
    pub fn covers(&self, path: &str, storage: &str) -> bool {
        let Some(pattern) = self.crate_path else { return false };
        let pattern = pattern.replace(STORAGE_PLACEHOLDER, storage);
        match pattern.strip_suffix("/**") {
            Some(directory) => path.strip_prefix(directory).is_some_and(|rest| rest.starts_with('/')),
            None => path == pattern,
        }
    }
}

/// The definitions every crate of `kind` assembled in `mode` carries.
pub fn definitions_for(kind: CrateKind, mode: ConstraintMode) -> impl Iterator<Item = &'static Definition> {
    DEFINITIONS.iter().filter(move |d| d.presence.in_crate(kind) && d.modes.contains(&mode))
}

/// The definitions only some crates of `kind` assembled in `mode` carry ([`Presence::Optional`]): each summary says
/// which crates.
pub fn optional_definitions_for(kind: CrateKind, mode: ConstraintMode) -> impl Iterator<Item = &'static Definition> {
    DEFINITIONS.iter().filter(move |d| d.presence.optional_in(kind) && d.modes.contains(&mode))
}

/// The author definition ([`Origin::Author`]) that covers `path`, whatever the storage's name: `Some` exactly for the
/// author files of an assembled crate (`builder/**`, `stores/<storage>/interface/**`, `agent/**`; in an engine crate
/// `agent/**` is the engine author's, whose definition names the same path).
pub fn author_definition(path: &str) -> Option<&'static Definition> {
    let storage = path.strip_prefix("stores/").and_then(|rest| rest.split('/').next()).unwrap_or_default();
    DEFINITIONS.iter().find(|d| matches!(d.origin, Origin::Author) && d.covers(path, storage))
}

/// The [`Presence::Shared`] definition that covers `path` for storage `storage`: `Some` exactly for the files of a
/// storage's dependency closure.
pub fn closure_definition(path: &str, storage: &str) -> Option<&'static Definition> {
    DEFINITIONS.iter().find(|d| d.presence == Presence::Shared && d.covers(path, storage))
}

const OBLIGATIONS: &str = "gendb_verification::obligations";
/// The generator of the flat access modules (`gendb_verification::obligations::flat_tables`, identity
/// `gendb-flat-tables-v1`).
const FLAT_TABLES_GENERATOR: &str = "gendb_verification::obligations::flat_tables";
/// The generator of the whole-schema files (`gendb_verification::obligations`, its `whole_schema` module).
const WHOLE_SCHEMA_GENERATOR: &str = "gendb_verification::obligations::whole_schema";

/// The optional definitions of the whole-schema files, generated only for a storage that stores every column of every
/// table in table and column order (the instance of a storage family): the general
/// engine contract lists them only in a run of several workloads (`engine.workloads`), so every other contract renders
/// as before.
pub const WHOLE_SCHEMA_DEFINITIONS: [&str; 3] = ["whole_schema", "storage_schema_exec", "engine_whole_schema"];

/// Every definition, grouped: meaning, read interface, fixed claims, library, bindings, author files. Where two paths
/// overlap (`link/query.rs` and `link/**`), the earlier, more specific definition describes the file.
pub const DEFINITIONS: &[Definition] = &[
    // ------------------------------------------------------------------------------------------------ meaning
    Definition {
        name: "typed_ast",
        crate_path: None,
        presence: Presence::Reference,
        modes: EVERY_MODE,
        role: Role::FixedMeaning,
        origin: Origin::Source { path: "frontend/ast/ast_schema.json" },
        items: &[],
        summary: "The one typed AST schema: the parser's output, the Rust decoder and the Verus constructors the schema and \
                  statement modules are emitted with.",
    },
    Definition {
        name: "sql_semantics",
        crate_path: Some("spec/**"),
        presence: Presence::Shared,
        modes: EVERY_MODE,
        role: Role::FixedMeaning,
        origin: Origin::Source { path: "sqlspec/spec.rs, sqlspec/syntax/, sqlspec/semantics/" },
        items: &["spec::order::ordered_ok", "spec::order::denote_body", "spec::typing::db_wf", "spec::value::{Database, Row, Val}"],
        summary: "SQLSpec: the fixed meaning of the supported PostgreSQL fragment (trusted definitions; every claim is stated \
                  with them).",
    },
    Definition {
        name: "source_and_answer_definitions",
        crate_path: Some("link/query.rs"),
        presence: Presence::Shared,
        modes: EVERY_MODE,
        role: Role::FixedMeaning,
        origin: Origin::Source { path: "sqlspec/proofs/link/query.rs" },
        items: &["TextCol", "TextView", "text_wf", "text_at", "view_rows", "proj", "proj_all"],
        summary: "Fixed definitions of delivered text columns, projections and answer rows (the rest of the file is optional \
                  toolkit).",
    },
    Definition {
        name: "source_relations",
        crate_path: Some("link/source.rs"),
        presence: Presence::Shared,
        modes: EVERY_MODE,
        role: Role::FixedMeaning,
        origin: Origin::Source { path: "sqlspec/proofs/link/source.rs" },
        items: &["proj_columns", "rows_in_columns", "cols_in_table", "lemma_proj_all_index", "lemma_proj_all_compose", "lemma_source_in_domain"],
        summary: "Fixed definitions of a table's declared columns and their domains, with the projection lemmas (a stored \
                  relation's columns restricted to a query's columns are the query's projection of the table).",
    },
    Definition {
        name: "schema",
        crate_path: Some("schema.rs"),
        presence: Presence::Shared,
        modes: EVERY_MODE,
        role: Role::FixedMeaning,
        origin: Origin::Generated {
            generator: "gendb_frontend::translator::emit_column_schema_module",
            input: "the dataset DDL (AST document tables, columns only)",
        },
        items: &["schema_spec"],
        summary: "The schema every claim is stated over; statement independent, so storage and query crates carry the same \
                  text.",
    },
    Definition {
        name: "declared_constraints",
        crate_path: Some("gendb_constraints.rs"),
        presence: Presence::PerKind,
        modes: DECLARED,
        role: Role::FixedMeaning,
        origin: Origin::Generated {
            generator: "gendb_frontend::translator::emit_constraints_module",
            input: "the request's declared integrity constraints (the dataset DDL's ALTER TABLE ... ADD clauses)",
        },
        items: &["declared_schema", "declared_db", "lemma_declared_schema"],
        summary: "The declared integrity constraints over the column schema: `declared_schema()` (schema_spec's tables and \
                  columns with the declared SQLSpec constraints), `declared_db(db)` (db's tables under it) and the checked \
                  lemma that its columns are schema_spec's and its constraints are well formed. Statement independent: the \
                  same text in query crates of entry v5 and storage crates of storage entry v2, compared with the query key \
                  and the storage package. Not part of any storage closure: interface files may not name it (author-source \
                  rule `interface_names_declared_constraints`).",
    },
    Definition {
        name: "statement",
        crate_path: Some("query.rs"),
        presence: Presence::QueryOnly,
        modes: EVERY_MODE,
        role: Role::FixedMeaning,
        origin: Origin::Generated { generator: "gendb_frontend::translator::emit_statement_module", input: "the statement instance" },
        items: &["query_spec_at", "param_typed", "param_domain", "lemma_query_wf_at"],
        summary: "The statement's meaning at a parameter binding, its parameter domain and typing (imports schema_spec).",
    },
    Definition {
        name: "storage_declaration",
        crate_path: Some("stores/<storage>/declaration.rs"),
        presence: Presence::Shared,
        modes: EVERY_MODE,
        role: Role::FixedMeaning,
        origin: Origin::Generated { generator: "gendb_verification::obligations (declaration_module)", input: "the storage declaration" },
        items: &["stored_table_t{j}", "stored_cols_t{j}", "stored_columns_t{j}", "stored_relations", "lemma_declared_schema", "lemma_stored_relations"],
        summary: "Which columns of which tables a storage stores: `stored_relations(db)`, the declared columns of `db`'s tables \
                  in canonical row order (equalities only), with their schema and domain lemmas.",
    },
    // ------------------------------------------------------------------------------------------ read interface
    Definition {
        name: "part_view",
        crate_path: Some("gendb_entry/layout.rs"),
        presence: Presence::Shared,
        modes: EVERY_MODE,
        role: Role::ReadInterface,
        origin: Origin::Source { path: "verification/obligations/gendb_entry/layout.rs" },
        items: &["PartView", "parts_view", "owned_parts_view", "part_view", "owned_part_view"],
        summary: "The view of stored parts: an ordered list of typed arrays (i8..i128, u8..u64); builders return owned parts \
                  with the same view.",
    },
    Definition {
        name: "stored_parts",
        crate_path: Some("gendb_entry/stored.rs"),
        presence: Presence::Shared,
        modes: EVERY_MODE,
        role: Role::ReadInterface,
        origin: Origin::Source { path: "registry/verus/stored.rs" },
        items: &[
            "StoredParts",
            "StoredParts::part_count",
            "StoredParts::part_len",
            "StoredParts::extent_{i8,i16,i32,i64,i128,u8,u16,u32,u64}",
            "StoredParts::counters",
            "part_len",
            "after_request",
            "saturated",
            "RequestCounts",
        ],
        summary: "The only access to stored data: extents [lo, hi) of immutable parts, zero-copy and lazily mapped, with \
                  saturating request counters (requests, not device I/O). Handles cannot be created, copied or reset by \
                  author code.",
    },
    Definition {
        name: "storage_interface",
        crate_path: Some("stores/<storage>/interface/**"),
        presence: Presence::Shared,
        modes: EVERY_MODE,
        role: Role::Author,
        origin: Origin::Author,
        items: &["represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool"],
        summary: "The storage author's representation relation (required) and readers, lemmas and specs (optional). Checked \
                  in the storage crate and copied unchanged into every query crate that reads the storage. Like every author \
                  file it must pass the author-source rules (implementation ownership, supported macros only).",
    },
    Definition {
        name: "storage_module",
        crate_path: Some("stores/<storage>/mod.rs"),
        presence: Presence::Shared,
        modes: EVERY_MODE,
        role: Role::Binding,
        origin: Origin::Generated { generator: OBLIGATIONS, input: "the storage name" },
        items: &["declaration", "interface"],
        summary: "The module of one storage: its declaration and its interface.",
    },
    // ------------------------------------------------------------------------------------------ fixed claims
    Definition {
        name: "storage_entry",
        crate_path: Some("gendb_entry.rs"),
        presence: Presence::StorageOnly,
        modes: UNCONSTRAINED,
        role: Role::FixedClaim,
        origin: Origin::Source { path: "verification/obligations/storage_entry.rs" },
        items: &["storage_build_meets", "abi_build_storage", "theorem_storage_built", "theorem_storage_build_total", "build_workers_ok", "delivered_source"],
        summary: "The fixed storage entry: on Ok the builder's parts represent the delivered relations; stored and read back \
                  they represent `stored_relations(db)` of the bound database. Its public names are disjoint from the query \
                  entry's, so an interface that names an entry item fails to compile in one of the two crates.",
    },
    Definition {
        name: "storage_entry_v2",
        crate_path: Some("gendb_entry.rs"),
        presence: Presence::StorageOnly,
        modes: DECLARED,
        role: Role::FixedClaim,
        origin: Origin::Source { path: "verification/obligations/storage_entry_v2.rs" },
        items: &[
            "source_witnessed",
            "storage_build_meets",
            "abi_build_storage",
            "theorem_storage_built",
            "theorem_storage_build_total",
            "build_workers_ok",
            "delivered_source",
        ],
        summary: "The fixed storage entry v2 (opt-in `uses_declared_constraints`): the storage entry's claim, with the \
                  builder's input also from a full database satisfying the run's declared constraints (`source_witnessed`, \
                  the user's declaration, never checked against the data). Facts reach the delivered columns only through \
                  that witness, by row position. The storage applies only to runs with exactly that declaration set.",
    },
    Definition {
        name: "query_entry",
        crate_path: Some("gendb_entry.rs"),
        presence: Presence::QueryOnly,
        modes: UNCONSTRAINED,
        role: Role::FixedClaim,
        origin: Origin::Source { path: "verification/obligations/query_entry.rs" },
        items: &[
            "Answer",
            "capacity_domain",
            "bound_db",
            "outcome_ok",
            "answer_meets",
            "stores_ready",
            "served",
            "query_meets",
            "abi_query",
            "theorem_end_to_end",
            "corollary_inside_capacity",
        ],
        summary: "The fixed query entry v4: the v3 SQL claim (result, exact error, capacity, parameter domain, template) for \
                  every database whose stored relations the stored parts represent.",
    },
    Definition {
        name: "query_entry_v5",
        crate_path: Some("gendb_entry.rs"),
        presence: Presence::QueryOnly,
        modes: DECLARED,
        role: Role::FixedClaim,
        origin: Origin::Source { path: "verification/obligations/query_entry_v5.rs" },
        items: &[
            "Answer",
            "capacity_domain",
            "bound_db",
            "outcome_ok",
            "answer_meets",
            "stores_ready",
            "served",
            "query_meets",
            "abi_query",
            "theorem_end_to_end",
            "corollary_inside_capacity",
        ],
        summary: "The fixed query entry v5: the entry v4 claim for every database whose stored relations the stored parts \
                  represent and that satisfies the declared integrity constraints (`bound_db` adds \
                  `constraints_hold(declared_db(db))`, the user's declaration, never checked against the data).",
    },
    Definition {
        name: "stores",
        crate_path: Some("gendb_entry/stores.rs"),
        presence: Presence::Readers,
        modes: EVERY_MODE,
        role: Role::Binding,
        origin: Origin::Generated { generator: OBLIGATIONS, input: "the query's storage uses" },
        items: &["Stores", "StoresView", "stored_ok", "uses_view", "STORAGE_USES"],
        summary: "One `StoredParts` field per storage use (named after the storage) and `stored_ok`, the conjunction of the \
                  storages' `represents` over `stored_relations(db)`. The same generator in query and engine crates.",
    },
    Definition {
        name: "engine_entry",
        crate_path: Some("gendb_entry.rs"),
        presence: Presence::EngineOnly,
        modes: DECLARED,
        role: Role::FixedClaim,
        origin: Origin::Source { path: "verification/obligations/engine_entry.rs" },
        items: &[
            "Answer",
            "supported",
            "capacity_domain",
            "bound_db",
            "outcome_ok",
            "answer_meets",
            "stores_ready",
            "served",
            "engine_meets",
            "abi_engine_query",
            "abi_engine_echo",
            "theorem_engine_end_to_end",
            "corollary_inside_capacity",
        ],
        summary: "The fixed engine entry v1: for the statement the AST bytes mean (`decode_spec`) and every database bound to the \
                  stored parts under the declared integrity constraints, `Malformed` exactly for undecodable bytes, `ParamRefused` \
                  exactly for a statement that is not well typed for the schema (`supported`), otherwise the query entries' served \
                  meaning (rows, exact error, capacity).",
    },
    Definition {
        name: "engine_ast_codec",
        crate_path: Some("gendb_ast_codec.rs"),
        presence: Presence::EngineOnly,
        modes: EVERY_MODE,
        role: Role::FixedMeaning,
        origin: Origin::Source { path: "runtime/verus/engine_codec.rs" },
        items: &["decode_spec", "decode_query", "render_spec", "render_query", "view_decoded"],
        summary: "The AST bytes of an engine call: `decode_spec` is their fixed meaning (a total prefix decoding of the \
                  gendb-sql-ast-v1 constructors, trusted definition), `decode_query` the verified decoder, `render_spec` / \
                  `render_query` the verified echo text in the evaluator's echo grammar.",
    },
    Definition {
        name: "engine_schema_exec",
        crate_path: Some("gendb_entry/schema_exec.rs"),
        presence: Presence::EngineOnly,
        modes: EVERY_MODE,
        role: Role::Binding,
        origin: Origin::Generated { generator: OBLIGATIONS, input: "the dataset DDL's tables and columns" },
        items: &["schema_exec"],
        summary: "The column schema as the interpreter's runtime schema, proved equal to `schema_spec()`; the engine entry hands \
                  it to the verified `check_ordered`.",
    },
    // ------------------------------------------------------------------------------------------ library
    Definition {
        name: "sql_interpreter",
        crate_path: Some("exec/**"),
        presence: Presence::Shared,
        modes: EVERY_MODE,
        role: Role::Library,
        origin: Origin::Source { path: "sqlspec/interpreter/" },
        items: &["exec::relational::domain::fits_query", "exec::value::{EVal, view_row}"],
        summary: "The verified reference interpreter over machine values; `fits_query` defines the capacity domain and \
                  `EVal`/`view_row` the answer values (both part of the claim's meaning).",
    },
    Definition {
        name: "sql_bridge",
        crate_path: Some("bridge/**"),
        presence: Presence::Shared,
        modes: EVERY_MODE,
        role: Role::Library,
        origin: Origin::Source { path: "sqlspec/proofs/bridge/" },
        items: &[],
        summary: "Theorems about the SQL meaning used by the interpreter, the toolkit and authors.",
    },
    Definition {
        name: "link_toolkit_root",
        crate_path: Some("link.rs"),
        presence: Presence::Shared,
        modes: EVERY_MODE,
        role: Role::Library,
        origin: Origin::Source { path: "sqlspec/proofs/link/mod.rs" },
        items: &[],
        summary: "The optional proof toolkit's module list (see the fixed definitions above for its non-optional part).",
    },
    Definition {
        name: "link_toolkit",
        crate_path: Some("link/**"),
        presence: Presence::Shared,
        modes: EVERY_MODE,
        role: Role::Library,
        origin: Origin::Source { path: "sqlspec/proofs/link/" },
        items: &["join::lemma_sum_of_perm", "outcome::lemma_outcome_rows", "expr::lemma_pred_cmp"],
        summary: "Optional generic lemmas from author normal forms to the SQL meaning (the files above take precedence for \
                  `link/query.rs` and `link/source.rs`).",
    },
    Definition {
        name: "abi_types",
        crate_path: Some("gendb_abi.rs"),
        presence: Presence::Shared,
        modes: EVERY_MODE,
        role: Role::Library,
        origin: Origin::Source { path: "runtime/verus/gendb_abi.rs" },
        items: &["Part", "OwnedPart", "Column", "ParamArg", "AbiStatus", "QueryReturn", "BuildReturn"],
        summary: "Data types of the C ABI: delivered columns, stored parts, arguments and statuses.",
    },
    Definition {
        name: "query_arguments",
        crate_path: Some("gendb_arguments.rs"),
        presence: Presence::QueryOnly,
        modes: EVERY_MODE,
        role: Role::Library,
        origin: Origin::Source { path: "runtime/verus/gendb_arguments.rs" },
        items: &["QueryArg"],
        summary: "The statement argument type of query crates: `ParamArg`'s integer, numeric and date arguments plus \
                  `text` (the argument's bytes). Query-only, so `gendb_abi.rs` and every storage closure stay unchanged.",
    },
    Definition {
        name: "query_results",
        crate_path: Some("gendb_entry/results.rs"),
        presence: Presence::Readers,
        modes: EVERY_MODE,
        role: Role::Library,
        origin: Origin::Source { path: "verification/obligations/gendb_entry/results.rs" },
        items: &["ResultColumns", "ResultColumn", "columns_wf", "columns_view", "column_value", "lemma_columns_view", "lemma_columns_view_eq", "text_column", "push_text"],
        summary: "The columnar answer `Answer::Columns(ResultColumns)`: one vector per output column (no allocation per \
                  row); its fixed view `columns_view` is the claim's result rows. Query and engine crates.",
    },
    Definition {
        name: "parallel",
        crate_path: Some("gendb_entry/parallel.rs"),
        presence: Presence::Shared,
        modes: EVERY_MODE,
        role: Role::Library,
        origin: Origin::Source { path: "verification/obligations/gendb_entry/parallel.rs" },
        items: &["WorkerTask", "fork_join", "Dispatch", "MAX_WORKERS"],
        summary: "The verified fork/join: the only way to run work on other threads.",
    },
    Definition {
        name: "runtime_outcomes",
        crate_path: Some("gendb_entry/runtime.rs"),
        presence: Presence::Shared,
        modes: EVERY_MODE,
        role: Role::Library,
        origin: Origin::Source { path: "verification/obligations/gendb_entry/runtime.rs" },
        items: &["QueryError", "WorkerFailure"],
        summary: "Build and query errors; `WorkerFailed` needs the runtime's private token.",
    },
    Definition {
        name: "work_helpers",
        crate_path: Some("gendb_entry/work.rs"),
        presence: Presence::Shared,
        modes: EVERY_MODE,
        role: Role::Library,
        origin: Origin::Source { path: "verification/obligations/gendb_entry/work.rs" },
        items: &["text_bytes", "text_eq", "text_offsets_ok", "filled", "put", "TaskBuffer"],
        summary: "Verified helpers: text values, byte equality, caller-thread allocation for worker outputs, and \
                  `no_unwind` filling of preallocated worker outputs (`put`, `TaskBuffer::push`).",
    },
    Definition {
        name: "column_domains",
        crate_path: Some("gendb_entry/source_check.rs"),
        presence: Presence::Shared,
        modes: EVERY_MODE,
        role: Role::Library,
        origin: Origin::Source { path: "verification/obligations/gendb_entry/source_check.rs" },
        items: &["date32_val", "int32_values_in", "decimal_values_in", "date32_values_in", "text_values_in"],
        summary: "Value views of delivered column kinds (Date32 as a SQL date) and their verified domain decisions.",
    },
    Definition {
        name: "engine_toolkit",
        crate_path: Some("engine_link/**"),
        presence: Presence::EngineOnly,
        modes: EVERY_MODE,
        role: Role::Library,
        origin: Origin::Source { path: "sqlspec/engine_link/" },
        items: &[],
        summary: "The engine-only proof toolkit (generic plan-equivalence and operator lemmas; root `engine_link/mod.rs`): every file \
                  of `sqlspec/engine_link/` except its checked examples, embedded by the engine crate assembly. Engine crates \
                  only, so SQLSpec's library and every storage closure stay unchanged.",
    },
    // ------------------------------------------------------------------------------------------ bindings
    Definition {
        name: "crate_root",
        crate_path: Some("lib.rs"),
        presence: Presence::PerKind,
        modes: EVERY_MODE,
        role: Role::Binding,
        origin: Origin::Generated { generator: OBLIGATIONS, input: "the crate kind" },
        items: &[],
        summary: "Crate attributes and module declarations.",
    },
    Definition {
        name: "stores_list",
        crate_path: Some("stores.rs"),
        presence: Presence::PerKind,
        modes: EVERY_MODE,
        role: Role::Binding,
        origin: Origin::Generated { generator: OBLIGATIONS, input: "the storages of the crate" },
        items: &[],
        summary: "`pub mod <storage>;` for every storage the crate carries.",
    },
    Definition {
        name: "storage_source",
        crate_path: Some("gendb_source.rs"),
        presence: Presence::StorageOnly,
        modes: EVERY_MODE,
        role: Role::Binding,
        origin: Origin::Generated { generator: OBLIGATIONS, input: "the storage declaration" },
        items: &["SourceRef", "SourceView", "tables", "source_wf", "in_domain", "table_t{j}", "source_columns_are_tables"],
        summary: "The builder's input: the delivered columns of the declared tables, their relations and declared domain.",
    },
    Definition {
        name: "storage_column_binder",
        crate_path: Some("gendb_entry/binder.rs"),
        presence: Presence::StorageOnly,
        modes: EVERY_MODE,
        role: Role::Binding,
        origin: Origin::Generated { generator: OBLIGATIONS, input: "the storage declaration" },
        items: &["column_source"],
        summary: "The verified binding of the ABI column list to `SourceRef`.",
    },
    Definition {
        name: "storage_binding",
        crate_path: Some("gendb_entry/storage.rs"),
        presence: Presence::StorageOnly,
        modes: EVERY_MODE,
        role: Role::Binding,
        origin: Origin::Generated { generator: OBLIGATIONS, input: "the storage name and declaration" },
        items: &["represents", "stored_relations", "lemma_source_is_stored"],
        summary: "Binds the storage entry to the storage's interface and declaration.",
    },
    Definition {
        name: "parameters",
        crate_path: Some("gendb_params.rs"),
        presence: Presence::QueryOnly,
        modes: EVERY_MODE,
        role: Role::Binding,
        origin: Origin::Generated { generator: OBLIGATIONS, input: "the free parameters" },
        items: &["Params", "bind_params", "param_source"],
        summary: "The verified parameter binder: `ParamRefused` exactly outside the declared domain.",
    },
    // ------------------------------------------------------------------------------- generated when the storages call for it
    Definition {
        name: "flat_tables",
        crate_path: Some("flat_tables.rs"),
        presence: Presence::Optional(CrateKind::Engine),
        modes: EVERY_MODE,
        role: Role::ReadInterface,
        origin: Origin::Generated { generator: FLAT_TABLES_GENERATOR, input: "the engine's storage uses that are generated flat storages" },
        items: &[
            "TABLE_COUNT",
            "flat_table",
            "is_flat_table",
            "flat_bound",
            "table_rows",
            "materialize_table",
            "ColumnSlice",
            "column_slice",
            "slice_len",
            "slice_wf",
            "slice_value",
            "lemma_flat_table_unique",
            "materialize_database",
            "lemma_flat_database_unique",
            "flat_parts",
            "flat_layout",
            "flat_part_count",
            "flat_part_of",
            "slice_fits",
            "lemma_flat_plain",
        ],
        summary: "Only in an engine crate that reads generated flat storages (`crate::flat_tables`): their tables by table id \
                  and column id, so engine code names no table or column of the schema. Rows, whole tables, typed column \
                  slices and, when every table is flat-stored, the whole database as the interpreter's runtime database \
                  (`materialize_database`, `edb@ == db`), each specified against the bound database; `lemma_flat_plain` states \
                  in the plain-columns vocabulary (`crate::flat_tables::plain`) what the flat parts of a table hold. Generated \
                  and checked by Verus with the crate; in no storage closure.",
    },
    Definition {
        name: "flat_tables_plain",
        crate_path: Some("flat_tables/plain.rs"),
        presence: Presence::Optional(CrateKind::Engine),
        modes: EVERY_MODE,
        role: Role::ReadInterface,
        origin: Origin::Generated { generator: FLAT_TABLES_GENERATOR, input: "none: the plain-columns vocabulary (gendb-plain-columns-v1), fixed text" },
        items: &["plain_column", "plain_columns", "lemma_plain_columns_determine", "read_plain", "plain_slice_fits", "plain_value", "plain_slice_wf", "lemma_proj_identity"],
        summary: "Only with `flat_tables.rs`: the plain-columns vocabulary as its submodule `crate::flat_tables::plain` (the same \
                  text as `plain_columns`), the terms `lemma_flat_plain` states the flat parts in.",
    },
    Definition {
        name: "sources_flat",
        crate_path: Some("sources_flat.rs"),
        presence: Presence::Optional(CrateKind::Storage),
        modes: EVERY_MODE,
        role: Role::ReadInterface,
        origin: Origin::Generated { generator: FLAT_TABLES_GENERATOR, input: "the derived storage's sources that are generated flat storages" },
        items: &[
            "TABLE_COUNT",
            "flat_table",
            "is_flat_table",
            "flat_bound",
            "table_rows",
            "materialize_table",
            "ColumnSlice",
            "column_slice",
            "slice_len",
            "slice_wf",
            "slice_value",
            "slice_fits",
            "lemma_flat_table_unique",
            "flat_parts",
            "flat_layout",
            "flat_part_count",
            "flat_part_of",
            "lemma_flat_plain",
        ],
        summary: "Only in a storage crate built from admitted storages one of which is a generated flat storage \
                  (`crate::sources_flat`): the flat sources' tables by table id and column id for the builder, specified \
                  against the database the sources are bound to (`sources_bound`). The engine's access without the \
                  whole-database functions; builders only (in no storage closure, so never copied into engine crates).",
    },
    Definition {
        name: "sources_flat_plain",
        crate_path: Some("sources_flat/plain.rs"),
        presence: Presence::Optional(CrateKind::Storage),
        modes: EVERY_MODE,
        role: Role::ReadInterface,
        origin: Origin::Generated { generator: FLAT_TABLES_GENERATOR, input: "none: the plain-columns vocabulary (gendb-plain-columns-v1), fixed text" },
        items: &["plain_column", "plain_columns", "lemma_plain_columns_determine", "read_plain", "lemma_proj_identity"],
        summary: "Only with `sources_flat.rs`: the plain-columns vocabulary as `crate::sources_flat::plain` (the same text as \
                  `plain_columns`). A builder that keeps a flat source's parts (`extends`) proves its interface's \
                  `plain_columns` from `lemma_flat_plain`: the two copies are the same open definitions.",
    },
    Definition {
        name: "plain_columns",
        crate_path: Some("stores/<storage>/interface/plain.rs"),
        presence: Presence::Optional(CrateKind::Storage),
        modes: EVERY_MODE,
        role: Role::ReadInterface,
        origin: Origin::Source { path: "verification/src/obligations/plain_columns.rs" },
        items: &["plain_column", "plain_columns", "lemma_plain_columns_determine", "read_plain", "plain_slice_fits", "plain_value", "plain_slice_wf", "lemma_proj_identity"],
        summary: "GenDB's plain-columns vocabulary (`PLAIN_COLUMNS`, identity `gendb-plain-columns-v1`, contract file \
                  `plain-columns.rs`): how the columns of one relation are held as plain typed arrays, by part index and \
                  declared column type, never by name. A storage author who chooses it copies it unchanged into the \
                  interface (`pub mod plain;`), where it is the storage's own closure text (scanned and verified like any \
                  interface file, and carried by every crate that reads the storage).",
    },
    Definition {
        name: "derived_sources",
        crate_path: Some("gendb_entry/sources.rs"),
        presence: Presence::Optional(CrateKind::Storage),
        modes: EVERY_MODE,
        role: Role::Binding,
        origin: Origin::Generated { generator: OBLIGATIONS, input: "the derived storage's admitted sources" },
        items: &["Stores", "StoresView", "stored_ok", "uses_view", "STORAGE_USES"],
        summary: "Only in a storage crate built from admitted storages: one `StoredParts` field per source (named after the \
                  source) and `stored_ok` over them, the query and engine crates' `gendb_entry/stores.rs` text under the \
                  derived entry's name. The builder reads its sources through it.",
    },
    Definition {
        name: "derived_derivation",
        crate_path: Some("gendb_entry/derivation.rs"),
        presence: Presence::Optional(CrateKind::Storage),
        modes: EVERY_MODE,
        role: Role::Binding,
        origin: Origin::Generated { generator: OBLIGATIONS, input: "the derived storage's extended source and constraint choice" },
        items: &["inherited", "assumed"],
        summary: "Only in a storage crate built from admitted storages: the parts the new storage inherits (`inherited`: the \
                  extended source's whole part list, or none) and what its builder assumes of the database besides its \
                  sources (`assumed`: the declared constraints, or nothing).",
    },
    Definition {
        name: "whole_schema",
        crate_path: Some("whole_schema.rs"),
        presence: Presence::Optional(CrateKind::Storage),
        modes: EVERY_MODE,
        role: Role::ReadInterface,
        origin: Origin::Generated { generator: WHOLE_SCHEMA_GENERATOR, input: "the schema and the declarations of the crate's whole-schema stores" },
        items: &["TABLE_COUNT", "stored_type", "lemma_schema_shape", "lemma_<storage>"],
        summary: "Only in a storage crate built from admitted storages whose own declaration stores every column of every \
                  table (a storage family's instance; `crate::whole_schema`): the table count, the shape of the schema \
                  (`lemma_schema_shape`: every table's column count and stored types) and, per whole-schema store, \
                  `lemma_<storage>(db)`: its stored relations are `db.tables`, table for table, so a builder is written by \
                  table id for any table count. Generated and checked by Verus with the crate; in no storage closure.",
    },
    Definition {
        name: "storage_schema_exec",
        crate_path: Some("schema_exec.rs"),
        presence: Presence::Optional(CrateKind::Storage),
        modes: EVERY_MODE,
        role: Role::Binding,
        origin: Origin::Generated { generator: WHOLE_SCHEMA_GENERATOR, input: "the dataset DDL's tables and columns" },
        items: &["schema_exec"],
        summary: "Only with the storage crate's `whole_schema.rs` (`crate::schema_exec`, a crate-root module): the column \
                  schema as executable data, proved equal to `schema_spec()`, the text engine crates carry as \
                  `gendb_entry/schema_exec.rs`; a builder reads each column's type and nullability from it at run time.",
    },
    Definition {
        name: "engine_whole_schema",
        crate_path: Some("whole_schema.rs"),
        presence: Presence::Optional(CrateKind::Engine),
        modes: EVERY_MODE,
        role: Role::ReadInterface,
        origin: Origin::Generated { generator: WHOLE_SCHEMA_GENERATOR, input: "the schema and the declarations of the engine's whole-schema storage uses" },
        items: &["TABLE_COUNT", "stored_type", "lemma_schema_shape", "lemma_<storage>"],
        summary: "Only in an engine crate that reads a storage storing every column of every table that is not a generated \
                  flat storage (a storage family's instance; `crate::whole_schema`): the same items as a storage crate's \
                  `whole_schema.rs` for that use, so the engine opens the store by table id for any schema.",
    },
    // ------------------------------------------------------------------------------------------ author files
    Definition {
        name: "storage_builder",
        crate_path: Some("builder/**"),
        presence: Presence::StorageOnly,
        modes: EVERY_MODE,
        role: Role::Author,
        origin: Origin::Author,
        items: &["build(src: &SourceRef, workers: usize, dispatch: &mut Dispatch) -> Result<Vec<OwnedPart>, QueryError>"],
        summary: "The storage builder: on Ok its parts represent `tables(src@)`. Checked in the storage crate only.",
    },
    Definition {
        name: "query_author",
        crate_path: Some("agent/**"),
        presence: Presence::QueryOnly,
        modes: EVERY_MODE,
        role: Role::Author,
        origin: Origin::Author,
        items: &["query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> Result<Answer, QueryError>"],
        summary: "The query code and its own specifications and proofs; reads stored data through the storages' readers or \
                  `StoredParts` extents.",
    },
    Definition {
        name: "engine_author",
        crate_path: Some("agent/**"),
        presence: Presence::EngineOnly,
        modes: EVERY_MODE,
        role: Role::Author,
        origin: Origin::Author,
        items: &["engine(stores: &mut Stores, q: &EOrderedQuery, workers: usize, dispatch: &mut Dispatch) -> Result<Answer, QueryError>"],
        summary: "The engine: planner, operators, their specifications and proofs, answering every supported statement; reads \
                  stored data through the storages' readers or `StoredParts` extents.",
    },
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn paths_and_presence_are_consistent() {
        let storage = "zones";
        assert!(closure_definition("stores/zones/interface/mod.rs", storage).is_some());
        assert!(closure_definition("stores/other/interface/mod.rs", storage).is_none());
        assert!(closure_definition("stores/zones/interfaces.rs", storage).is_none());
        assert!(closure_definition("spec/value.rs", storage).is_some() && closure_definition("gendb_entry.rs", storage).is_none());
        assert!(closure_definition("builder/mod.rs", storage).is_none() && closure_definition("agent/mod.rs", storage).is_none());
        for author in ["builder/mod.rs", "builder/zones/map.rs", "agent/mod.rs", "stores/zones/interface/mod.rs", "stores/other/interface/a/b.rs"] {
            assert!(author_definition(author).is_some(), "{author}");
        }
        for framework in ["stores/zones/declaration.rs", "stores/zones/mod.rs", "stores/zones/interfaces.rs", "gendb_entry/stored.rs", "spec/value.rs", "lib.rs"] {
            assert!(author_definition(framework).is_none(), "{framework}");
        }
        for d in DEFINITIONS {
            assert_eq!(d.crate_path.is_none(), d.presence == Presence::Reference, "{}", d.name);
            assert!(!d.modes.is_empty() && (d.modes == EVERY_MODE || d.presence != Presence::Shared), "{}: a closure file is in every mode", d.name);
        }
        // In each mode a crate kind has exactly one definition per logical path (the entry differs by mode).
        let declared_module = DEFINITIONS.iter().find(|d| d.name == "declared_constraints").unwrap();
        assert!(declared_module.presence.in_crate(CrateKind::Storage) && declared_module.presence.in_crate(CrateKind::Query));
        assert!(closure_definition("gendb_constraints.rs", storage).is_none(), "the declared-constraints module is in no closure");
        for kind in [CrateKind::Storage, CrateKind::Query, CrateKind::Engine] {
            for mode in [ConstraintMode::Unconstrained, ConstraintMode::Declared] {
                let paths: Vec<&str> = definitions_for(kind, mode).filter_map(|d| d.crate_path).collect();
                let unique: std::collections::BTreeSet<&str> = paths.iter().copied().collect();
                assert_eq!(unique.len(), paths.len(), "{kind:?} {mode:?}");
            }
        }
        // Engine crates carry the read handle, the stores generator and the columnar answer, but no statement, parameters,
        // query arguments or query entry; the engine toolkit is in no other kind and in no closure.
        let engine: Vec<&str> = definitions_for(CrateKind::Engine, ConstraintMode::Declared).map(|d| d.name).collect();
        for name in ["stored_parts", "stores", "query_results", "engine_entry", "engine_ast_codec", "engine_schema_exec", "engine_toolkit", "engine_author"] {
            assert!(engine.contains(&name), "{name}");
        }
        for name in ["statement", "parameters", "query_arguments", "query_entry", "query_entry_v5", "query_author", "storage_builder"] {
            assert!(!engine.contains(&name), "{name}");
        }
        assert!(closure_definition("engine_link/mod.rs", storage).is_none() && closure_definition("gendb_ast_codec.rs", storage).is_none());
        assert!(!definitions_for(CrateKind::Query, ConstraintMode::Declared).any(|d| d.presence == Presence::EngineOnly));
        // Optional definitions: listed only by `optional_definitions_for`; the generated ones are in no closure and never an
        // author's; the plain-columns vocabulary is interface text an author copies (so its storage's closure); a kind's
        // always-present and optional paths together stay unique.
        let optional = |kind: CrateKind| -> Vec<&str> { optional_definitions_for(kind, ConstraintMode::Declared).map(|d| d.name).collect() };
        assert_eq!(optional(CrateKind::Engine), ["flat_tables", "flat_tables_plain", "engine_whole_schema"]);
        assert_eq!(optional(CrateKind::Storage), ["sources_flat", "sources_flat_plain", "plain_columns", "derived_sources", "derived_derivation", "whole_schema", "storage_schema_exec"]);
        assert!(WHOLE_SCHEMA_DEFINITIONS.iter().all(|name| DEFINITIONS.iter().any(|d| d.name == *name && matches!(d.presence, Presence::Optional(_)))));
        assert!(optional(CrateKind::Query).is_empty());
        for d in DEFINITIONS.iter().filter(|d| matches!(d.presence, Presence::Optional(_))) {
            let path = d.crate_path.unwrap().replace(STORAGE_PLACEHOLDER, storage);
            if d.name == "plain_columns" {
                assert!(closure_definition(&path, storage).is_some_and(|c| c.name == "storage_interface"));
                assert!(author_definition(&path).is_some_and(|a| a.name == "storage_interface"));
            } else {
                assert!(closure_definition(&path, storage).is_none() && author_definition(&path).is_none(), "{}", d.name);
            }
            assert!(!definitions_for(CrateKind::Storage, ConstraintMode::Declared).chain(definitions_for(CrateKind::Engine, ConstraintMode::Declared)).any(|a| a.name == d.name));
        }
        for kind in [CrateKind::Storage, CrateKind::Query, CrateKind::Engine] {
            for mode in [ConstraintMode::Unconstrained, ConstraintMode::Declared] {
                let paths: Vec<&str> = definitions_for(kind, mode).chain(optional_definitions_for(kind, mode)).filter_map(|d| d.crate_path).collect();
                let unique: std::collections::BTreeSet<&str> = paths.iter().copied().collect();
                assert_eq!(unique.len(), paths.len(), "{kind:?} {mode:?} with its optional definitions");
            }
        }
        let names: Vec<&str> = DEFINITIONS.iter().map(|d| d.name).collect();
        let mut unique = names.clone();
        unique.sort_unstable();
        unique.dedup();
        assert_eq!(unique.len(), names.len());
    }
}
