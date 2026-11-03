//! Storage: trusted import of original-format data, prepared captures, the basic I/O that later executions read, and
//! the admitted storage versions that apply to the current data.
//!
//! - [`import`]: declared datasets, column demand, the trusted Parquet importer, prepared-capture reuse and the
//!   DataFusion reference over a capture.
//! - [`io`]: canonical native source columns, read-only memory, persisted column archives and stored parts.
//! - [`versions`]: the current capture's per-table identities, applicability of admitted storage versions and the
//!   stored asset of each storage use. Storage and reader interfaces are defined once in the registry
//!   (`gendb_registry`) and the fixed obligations (`gendb_verification::obligations`).

pub mod import;
pub mod io;
pub mod versions;
