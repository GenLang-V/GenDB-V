//! Trusted import of original-format data and reuse of prepared captures.
//!
//! A workload's column demand (from the typed-AST source declarations of its statements) is captured once from the
//! declared Parquet files into a prepared root, then shared: later workloads reuse or extend it, and every statement
//! receives a metadata-only projection of it. [`SqlReference`] runs independent DataFusion references over the capture.
//!
//! Trust: the Parquet importer (decoders, filesystem, lifecycle stamps standing for unchanged files) and the capture's
//! row correspondence are trusted, not verified; see `parquet` and `preparation`. Nothing is hashed or rescanned to
//! identify data: captures carry assigned lifecycle versions, checked with declared schemas, ordinals and file extents.
//!
//! - [`dataset`]: declared tables, columns, locations and source versions.
//! - [`demand`]: column demand and statement projections, bound to the declaration.
//! - [`preparation`]: prepare, resume, reuse or extend a prepared root.
//! - `facts`: source data facts computed once during preparation ([`DataFacts`], `data-facts.json`; workload author only).
//! - [`prepared`]: an opened prepared capture ([`PreparedSource`]).
//! - [`reference`]: the DataFusion reference over a capture.

mod dataset;
mod demand;
mod error;
mod facts;
mod parquet;
mod preparation;
mod prepared;
mod reference;
mod snapshot;
#[cfg(test)]
mod tests;

pub use dataset::{DataFormat, DatasetSpec, SourceVersion, TableSpec};
pub use demand::{ColumnDemand, Projection, declaration_projection};
pub use error::{ImportError, Result};
pub use facts::{ColumnFacts, DATA_FACTS_FILE, DataFacts};
pub use preparation::{PreparationMethod, PreparationReport, PreparationRequest, prepare_source};
pub use prepared::{PreparedRecord, PreparedSource};
pub use reference::{REFERENCE_TARGET_PARTITIONS, SqlReference};
