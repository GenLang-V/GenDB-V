//! Fixed proof obligations: the fixed entries, the generators of their data-only modules and the one assembly of each
//! crate kind around its author modules.
//!
//! Four crate kinds, each with one assembly function:
//! - a v3 candidate ([`candidate_framework_files`], entry `gendb-verus-entry-v3`): statement, delivered columns and the
//!   author's representation, builder and query in one crate. The saved route: its contracts and claims are unchanged.
//! - a storage crate ([`storage_crate_files`], `gendb-verus-storage-entry-v1`): one storage's declaration, the author's
//!   interface (`represents`, readers) and builder. Claim: on `Ok` the stored parts represent `stored_relations(db)`
//!   of every database the delivered columns are bound to. When the storage manifest opts in with
//!   `uses_declared_constraints` (a run that declares integrity constraints) the crate uses
//!   `gendb-verus-storage-entry-v2` instead ([`storage_entry`]): the builder may also assume that the delivered source
//!   comes from a full database satisfying the run's declared constraints (`source_witnessed`; the same generated
//!   `gendb_constraints.rs`; trusted assumption `declared_integrity_constraints`), and the claim holds for every such
//!   database. Such a storage applies only to runs with exactly that declaration set. A storage built from admitted
//!   storages has its own assembly ([`derived_storage_crate_files`], `gendb-verus-storage-entry-derived-v1`).
//! - an engine crate ([`engine_crate_files`], `gendb-verus-engine-entry-v1`): one engine for the whole schema; the
//!   statement arrives at call time as AST bytes (decoded by the verified `gendb_ast_codec`), and the author's
//!   `engine` answers every supported statement over the storages it reads. Claim: [`ENGINE_CLAIM_V1`]; it is stated under
//!   the request's declared integrity constraints (the query entry v5's `bound_db`).
//!   Two generators serve engine crates over the generated flat storages: `flat_tables` writes the crate's flat access
//!   module (`flat_tables.rs`; `sources_flat.rs` in storage crates built from flat storages), the tables by table and
//!   column id; [`interpreter_engine`] writes version 0 of the general engine (`gendb-interpreter-engine-v0`), whose
//!   `agent/mod.rs` answers every statement with the verified interpreter over that access. [`PLAIN_COLUMNS`] is the
//!   schema-free plain-columns vocabulary a storage interface may carry and the flat access modules state the flat
//!   storages' parts with (`plain_columns`).
//! - a query crate over stored data ([`query_crate_files`], `gendb-verus-entry-v4`): the statement, the author's query
//!   and, copied unchanged, the interfaces of the storages it reads. Claim: the v3 SQL claim for every database whose
//!   stored relations the stored parts represent. When the request declares integrity constraints the crate uses
//!   `gendb-verus-entry-v5` instead ([`query_entry`]): the same claim for every such database that also satisfies the
//!   declared constraints (generated `gendb_constraints.rs`; trusted assumption `declared_integrity_constraints`).
//!
//! The final theorem of each query crate is stated in SQL terms in its fixed entry (`outcome_ok`, `served`,
//! `theorem_end_to_end`; Verus text under `verification/obligations/`). For the emitted statement `query_spec_at(ps)`
//! at a binding `ps` in the declared parameter domain, and for every database of the schema bound to the delivered
//! columns (v3) or to the stored parts (v4), a served `Ok` is an allowed output, `SqlError(e)` is exactly the
//! statement's error and `Capacity` means the database is outside the generic capacity domain. That theorem states
//! what each outcome means (partial correctness); with the proved property `termination` ([`PROVED_PROPERTIES`]) the
//! claim is total correctness relative to the entry's outcome contract (`claim`). Authors write every intermediate
//! specification and proof; nothing here generates a per-query contract.
//!
//! A v3 candidate crate (logical paths under `src/`, all written by [`candidate_framework_files`] except `agent/**`):
//!
//! | Path | Origin |
//! |---|---|
//! | `lib.rs` | generated crate root |
//! | `spec/**`, `exec/**`, `bridge/**`, `link.rs`, `link/**` | SQLSpec library, `gendb_sqlspec::library` (`CANDIDATE_MODULES`) |
//! | `query.rs` | the emitted statement instance, `gendb_frontend::translator::emit_instance_module` |
//! | `gendb_source.rs` | generated from the declared source (data only) |
//! | `gendb_params.rs` | generated from the free parameters (data only) |
//! | `gendb_abi.rs`, `gendb_shim.rs` | ABI v3, `gendb_runtime::abi` |
//! | `gendb_entry.rs`, `gendb_entry/{runtime,parallel,layout,work,source_check}.rs` | fixed text, `verification/obligations/` |
//! | `gendb_entry/binder.rs` | generated ABI column binder (data only) |
//! | `agent/**` | the author's |
//!
//! Storage and query crate layouts: `storage_crate` and `query_crate`. Their shared files, which the registry
//! (`gendb_registry`) indexes, form a storage's dependency closure ([`compare_storage_closure`]).
//!
//! Modules: `declared` (declared columns and their SQL types), the data-only generators `source_module`,
//! `params_module`, `binder_module`, `declaration_module`, `flat_storage`, `flat_tables` and `whole_schema` (the
//! whole-schema files of a storage family's instance and of the engine crates that read one), the engine generator
//! `interpreter_engine`, the assemblies `candidate`, `storage_crate`, `query_crate` and `engine_crate` (with
//! `crate_files`, their shared pieces), `closure` (dependency-closure identity and the composition
//! rule, with the central author-source scan) and `claim` (theorem names, what authors must provide, the entries'
//! trusted assumptions and the proved property `termination`).
//!
//! Trust. Nothing here is a proof, and every file written here is checked by Verus with `--no-cheating` in the
//! crate it belongs to, so a wrong generation fails verification: declared column types are proved equal to the
//! schema, the parameter decision is proved equal to `param_domain`, the binder decides `source_wf` exactly. What these
//! files mean is fixed: the `spec` definitions, the emitted schema and statement, and the source/answer definitions
//! of `link` the claims are stated with ([`FIXED_LINK_DEFINITIONS`]). The host bindings (which columns, parts and
//! arguments are delivered, in which order) are trusted assumptions ([`TRUSTED_ASSUMPTIONS`],
//! [`STORAGE_TRUSTED_ASSUMPTIONS`], [`QUERY_TRUSTED_ASSUMPTIONS`]).

mod binder_module;
mod candidate;
mod claim;
mod closure;
mod crate_files;
mod declaration_module;
mod declared;
mod engine_crate;
mod flat_storage;
mod flat_tables;
mod interpreter_engine;
mod plain_columns;
mod params_module;
mod query_crate;
mod source_module;
mod storage_crate;
#[cfg(test)]
mod tests;
mod whole_schema;

pub use candidate::{candidate_framework_files, framework_check_files, CANDIDATE_CRATE_NAME, ENTRY_IDENTITY, ENTRY_SOURCE};
pub use claim::{
    AgentItem, EngineClaim, ProvedProperty, TrustedAssumption, AGENT_OBLIGATIONS, ENGINE_AUTHOR_OBLIGATIONS, ENGINE_CLAIM_V1, ENGINE_THEOREMS,
    ENGINE_TRUSTED_ASSUMPTIONS, PROVED_PROPERTIES, FIXED_LINK_DEFINITIONS, QUERY_AUTHOR_OBLIGATIONS, QUERY_THEOREMS,
    QUERY_TRUSTED_ASSUMPTIONS, QUERY_V5_AUTHOR_OBLIGATIONS, QUERY_V5_TRUSTED_ASSUMPTIONS, STORAGE_AUTHOR_OBLIGATIONS, STORAGE_THEOREMS,
    STORAGE_TRUSTED_ASSUMPTIONS, STORAGE_V2_AUTHOR_OBLIGATIONS, STORAGE_V2_TRUSTED_ASSUMPTIONS, THEOREMS, TRUSTED_ASSUMPTIONS,
    STORAGE_DERIVED_AUTHOR_OBLIGATIONS, STORAGE_DERIVED_TRUSTED_ASSUMPTIONS, STORAGE_DERIVED_V2_TRUSTED_ASSUMPTIONS,
};
pub use closure::{
    author_source_findings, check_storage_composition, compare_storage_closure, storage_closure, ClosureMismatch, CompositionError,
};
pub use crate_files::{declared_constraints_text, with_trusted_shim};
pub use engine_crate::{
    check_engine_coverage, engine_crate_files, engine_crate_files_with, engine_toolkit_files, ENGINE_CODEC_PATH, ENGINE_CRATE_NAME, ENGINE_ENTRY_IDENTITY,
    ENGINE_ENTRY_SOURCE, ENGINE_TOOLKIT_DIRECTORY,
};
pub use declared::{ColumnKind, DeclaredColumn, DeclaredSource, DeclaredTable, DeclaredType};
pub use flat_storage::{flat_storage, flat_storage_of, FlatBuffer, FlatElem, FlatPart, FlatStorage, FLAT_STORAGE_GENERATOR};
pub use flat_tables::{generated_flat_table, FlatAccess, FlatAccessSite, FLAT_TABLES_GENERATOR};
pub use interpreter_engine::{interpreter_engine, INTERPRETER_ENGINE_GENERATOR};
pub use plain_columns::{plain_columns_interface_file, PLAIN_COLUMNS, PLAIN_COLUMNS_FILE, PLAIN_COLUMNS_IDENTITY};
pub use whole_schema::{whole_schema_declaration, STORAGE_SCHEMA_EXEC_PATH, WHOLE_SCHEMA_GENERATOR, WHOLE_SCHEMA_PATH};
pub use query_crate::{
    check_storage_coverage, query_crate_files, query_entry, query_statement_check_files, QueryEntry, StorageUse, QUERY_ENTRY_IDENTITY,
    QUERY_ENTRY_SOURCE, QUERY_ENTRY_V4, QUERY_ENTRY_V5, QUERY_ENTRY_V5_IDENTITY, QUERY_ENTRY_V5_SOURCE,
};
pub use storage_crate::{
    derived_storage_crate_files, storage_crate_files, storage_entry, storage_entry_of, Derivation, StorageEntry, StorageName, STORAGE_CRATE_NAME,
    STORAGE_ENTRY_DERIVED, STORAGE_ENTRY_DERIVED_IDENTITY, STORAGE_ENTRY_DERIVED_SOURCE, STORAGE_ENTRY_DERIVED_V2, STORAGE_ENTRY_IDENTITY,
    STORAGE_ENTRY_SOURCE, STORAGE_ENTRY_V1, STORAGE_ENTRY_V2, STORAGE_ENTRY_V2_IDENTITY, STORAGE_ENTRY_V2_SOURCE,
};

use gendb_frontend::translator::EmitError;
use std::fmt;

/// Why the framework files of a crate could not be written.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AssemblyError {
    /// The statement instance (or the schema) could not be emitted.
    Emit(EmitError),
    /// The source or storage declaration cannot be delivered through the ABI or does not fit the schema.
    Source(String),
    /// The free parameters are not dense, ordered slots with bounds of their types.
    Params(String),
    /// A storage name, its storage uses or its interface files are not well formed.
    Storage(String),
    /// The storages a query reads do not store a column or table the statement demands
    /// (`storage_does_not_cover_demand`).
    Coverage(String),
    /// A storage opts in to the declared integrity constraints in a run that declares none
    /// (`declared_constraints_unavailable`).
    Constraints(String),
}

impl AssemblyError {
    /// The author-contract failure class: `missing_input` when the chosen storages do not cover the statement (the
    /// author can choose or build another storage), `refusal` for an opt-in the run cannot honour, `tool_failure`
    /// otherwise.
    pub fn failure_class(&self) -> &'static str {
        match self {
            Self::Coverage(_) => "missing_input",
            Self::Constraints(_) => "refusal",
            Self::Emit(_) | Self::Source(_) | Self::Params(_) | Self::Storage(_) => "tool_failure",
        }
    }
}

impl fmt::Display for AssemblyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Emit(e) => e.fmt(f),
            Self::Source(message) | Self::Params(message) | Self::Storage(message) | Self::Coverage(message) | Self::Constraints(message) => {
                f.write_str(message)
            }
        }
    }
}

impl std::error::Error for AssemblyError {}
