//! Host side of the GenDB Verus C ABI: load a Verus-compiled library, call its build entry over normalized source
//! columns or its query entry over stored parts and statement arguments, and check what comes back (status, exact SQL
//! error code, result wire, dispatch evidence, storage request counters, descriptive CPU/wall usage).
//!
//! Two ABI versions, one implementation (`loader`, `call`, `part_sink`), and the engine entries on top of v4:
//! - v3 (entry `gendb-verus-entry-v3`, the current candidates and the saved v3 route): [`VerusLibrary`], one crate
//!   with a build and a query entry over one part list;
//! - v4 (storage crates and storage-use query crates): [`StorageBuildLibrary`] and [`StorageQueryLibrary`], separate
//!   compiled artifacts; a query reads one part list per storage use and reports each use's request counters.
//!
//! - `records`: the C records and constants that the framework shims declare identically, [`expected_layout`] (v3)
//!   and [`expected_layout_v4`];
//! - [`StatementArgument`]: one typed statement argument and its [`ArgumentDescriptor`];
//! - [`CallStatus`], [`CallOutcome`], [`StorageRequestCounts`], [`check_query_wire`]: call results and the
//!   status/error/wire agreement;
//! - build calls write each delivered part straight to its file (`gendb_storage::io::PartFilesWriter`, no host copy);
//! - [`MappedParts`]: one stored parts directory mapped (lazily, with optional kernel advice) as [`PartDescriptor`]s;
//! - [`AbiError`]: typed refusals.
//!
//! The Verus framework sources: [`GENDB_ABI_SOURCE`] (`crate::gendb_abi`, types inside `verus!{}`, every crate kind),
//! [`GENDB_ARGUMENTS_SOURCE`] (`crate::gendb_arguments`, the query-only argument type with `text`) and the trusted C glue `crate::gendb_shim` of the crate kind: [`GENDB_SHIM_SOURCE`] (v3 candidates),
//! [`GENDB_STORAGE_SHIM_SOURCE`] (v4 storage crates; [`GENDB_STORAGE_NULLABLE_SHIM_SOURCE`] when the declaration has a
//! nullable column), [`GENDB_QUERY_SHIM_V4_SOURCE`] (v4 query crates). Saved ABI
//! v1/v2 packages are served only by the earlier GenDB version (not part of this repository).
//!
//! TRUSTED (not verified): this module, the framework shims and the `dlopen` loader. The shims hand verified code
//! `&'static` slices of host memory. That is honest only when every column, part, argument and the library stay
//! mapped and unchanged until the calling process exits; the caller must be a short-lived child process that never
//! releases them before the OS ends it (no in-process serving lifetime is claimed). No query identity appears here:
//! every library of one kind exports the same symbols.

mod arguments;
mod call;
mod engine;
mod error;
mod library;
mod loader;
mod outcome;
mod part_sink;
mod parts;
mod records;
mod storage_library;
#[cfg(test)]
mod tests;

pub use arguments::StatementArgument;
pub use engine::{
    expected_engine_layout, EngineLibrary, ENGINE_ABI_VERSION, ENGINE_CODEC_SOURCE, ENGINE_ECHO_SYMBOL, ENGINE_LAYOUT_SYMBOL, ENGINE_QUERY_SYMBOL,
    GENDB_ENGINE_SHIM_SOURCE, TRUSTED_ITEMS_ENGINE,
};
pub use error::AbiError;
pub use library::VerusLibrary;
pub use outcome::{
    CallOutcome, CallStatus, CallUsage, DispatchEvidence, RESULT_MAGIC, SQL_ERROR_CODES, StorageRequestCounts,
    check_query_wire,
};
pub use parts::MappedParts;
pub use records::{
    ABI_V4_VERSION, ABI_VERSION, ArgumentDescriptor, BUILD_SYMBOL, LAYOUT_SYMBOL, LAYOUT_V4_SYMBOL, MAX_WORKERS,
    PartDescriptor, QUERY_SYMBOL, REQUEST_COUNT_WORDS, STORAGE_BUILD_SYMBOL, STORAGE_DERIVED_BUILD_SYMBOL, STORAGE_QUERY_SYMBOL, StorageUseDescriptor,
    expected_layout, expected_layout_v4,
};
pub use storage_library::{DerivedStorageBuildLibrary, StorageBuildLibrary, StorageQueryLibrary};

/// `crate::gendb_abi` of every Verus candidate crate: the ABI data types (authors read, never edit, this file).
pub const GENDB_ABI_SOURCE: &str = include_str!("../verus/gendb_abi.rs");
/// `crate::gendb_arguments` of every v4 query crate: the statement argument type `QueryArg` (the shared `ParamArg`
/// plus `text`), kept out of `gendb_abi.rs` so that every storage's dependency closure stays unchanged.
pub const GENDB_ARGUMENTS_SOURCE: &str = include_str!("../verus/gendb_arguments.rs");
/// `crate::gendb_shim` of every Verus candidate crate: the trusted C glue between these records and the verified entry.
pub const GENDB_SHIM_SOURCE: &str = include_str!("../verus/gendb_shim.rs");
/// `crate::gendb_shim` of every v4 storage crate: the shared v4 records, then the storage build entry
/// (`gendb_verus_storage_build_v4` -> `crate::gendb_entry::abi_build_storage`).
pub const GENDB_STORAGE_SHIM_SOURCE: &str =
    concat!(include_str!("../verus/shim_v4/records.rs"), include_str!("../verus/shim_v4/storage_build.rs"));
/// `crate::gendb_shim` of a v4 storage crate whose declaration has a nullable column: the shared v4 records, then the
/// storage build entry that also delivers each nullable column's validity (after its values, as a `Column::Utf8` with
/// no offsets). Every other storage crate keeps [`GENDB_STORAGE_SHIM_SOURCE`], byte for byte.
pub const GENDB_STORAGE_NULLABLE_SHIM_SOURCE: &str =
    concat!(include_str!("../verus/shim_v4/records.rs"), include_str!("../verus/shim_v4/storage_build_nullable.rs"));
/// `crate::gendb_shim` of every v4 storage crate built from admitted storages: the shared v4 records, then the derived
/// build entry (`gendb_verus_storage_build_derived_v4` -> `crate::gendb_entry::abi_build_derived_storage` over one part
/// list per source).
pub const GENDB_STORAGE_DERIVED_SHIM_SOURCE: &str =
    concat!(include_str!("../verus/shim_v4/records.rs"), include_str!("../verus/shim_v4/storage_derive.rs"));
/// `crate::gendb_shim` of every v4 query crate: the shared v4 records, then the query entry
/// (`gendb_verus_query_v4` -> `crate::gendb_entry::abi_query` over one part list per storage use).
pub const GENDB_QUERY_SHIM_V4_SOURCE: &str =
    concat!(include_str!("../verus/shim_v4/records.rs"), include_str!("../verus/shim_v4/query.rs"));

/// Trusted items of the v3 ABI boundary, `(id, statement)`, for the TCB list of admitted v3 packages. The child
/// worker, argument conversion and source delivery items are composed by their owners.
pub const TRUSTED_ITEMS: [(&str, &str); 2] = [
    (
        "shim_v3",
        "runtime/verus/gendb_shim.rs: descriptors -> &'static slices, argument records -> ParamArg, catch_unwind -> \
         abort, worker-count check, GSQLRS1 rows/error/capacity encoding and the call record's error code",
    ),
    (
        "host_abi_v3",
        "gendb_runtime::abi: dlopen, layout-record check, argument descriptors, status decoding, the check that the \
         call record's SQL error code and the error/capacity wires agree",
    ),
];

/// Trusted items of the v4 ABI boundary (storage and query libraries), `(id, statement)`.
pub const TRUSTED_ITEMS_V4: [(&str, &str); 2] = [
    (
        "shim_v4",
        "runtime/verus/shim_v4/{records,storage_build,storage_build_nullable,storage_derive,query}.rs: descriptors -> &'static slices (one part list per \
         storage use or source storage, in declared use order; use count equal to the crate's STORAGE_USES), argument records -> \
         QueryArg (a text argument: the host's bytes as a &'static slice, like a part), catch_unwind -> abort, worker-count check, builder parts to the host sink, GSQLRS1 \
         rows/error/capacity encoding, the call record's error code and every use's request counters",
    ),
    (
        "host_abi_v4",
        "gendb_runtime::abi (v4): dlopen, v4 layout-record check, storage-use and argument descriptors, status \
         decoding, status/error/wire agreement, request counters read back per storage use (all or none), build \
         parts written straight to read-only files with the manifest written last (gendb_storage::io::PartFilesWriter)",
    ),
];
