//! Why a statement could not be served. `Display` keeps the earlier version's refusal texts; callers match variants.

use super::statement::StatementError;
use crate::answer::AnswerError;
use crate::worker::WorkerError;
use gendb_artifacts::verus::RecordError;
use gendb_artifacts::{CanonError, StoreError};
use gendb_frontend::params::ParamError;
use gendb_storage::versions::VersionError;
use std::fmt;

#[derive(Debug)]
pub enum ServeError {
    /// The statement key or ABI arguments could not be formed.
    Statement(StatementError),
    /// The key's identity could not be computed.
    Canonical(CanonError),
    /// Reading or resolving library records failed (package, representation, asset, library file).
    Records(RecordError),
    /// No package is admitted for this statement key (another fixed value or free domain is another statement).
    NoPackage,
    /// The admitted package is not a package of exactly this key and its route's ABI (3 or 4).
    PackageMismatch,
    /// The requested worker count lies outside the package's proved worker domain.
    WorkersOutsideDomain { workers: u32, domain: (u32, u32) },
    /// The host refused the argument texts before execution (count, ill-formed or inexact value).
    Arguments(ParamError),
    /// The package's representation record is not a v2 representation.
    RepresentationKind(String),
    /// No asset of the admitted representation is published for the current source versions.
    NoAsset,
    /// A storage use of the admitted v4 package has no asset for the current capture (never served from another route).
    NoStorageAsset { storage: String },
    /// A storage use's stored table is not in the current capture, or the capture lacks metadata.
    StorageVersions(VersionError),
    /// The worker could not run the call (including a child that ended without a result).
    Worker(WorkerError),
    /// The call answered nothing (a refusal or worker failure status), or status, code and wire disagree.
    Answer(AnswerError),
    /// The worker returned no call.
    NoCall,
}

impl fmt::Display for ServeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Statement(error) => write!(f, "{error}"),
            Self::Canonical(error) => write!(f, "{error}"),
            Self::Records(error) => write!(f, "{error}"),
            Self::NoPackage => f.write_str("no admitted Verus package for this statement and parameter declaration"),
            Self::PackageMismatch => f.write_str("the admitted package is not a package of this statement key and its route's ABI"),
            Self::WorkersOutsideDomain { workers, domain } => {
                write!(f, "worker count {workers} outside the package's proved domain {}..={}", domain.0, domain.1)
            }
            Self::Arguments(error) => write!(f, "host refused the arguments: {error}"),
            Self::RepresentationKind(kind) => write!(
                f,
                "package representation record kind {kind} is not a Verus v2 representation (saved v1 representations \
                 are served only by the earlier GenDB version)"
            ),
            Self::NoAsset => {
                f.write_str("no asset of the admitted representation for the current source versions; build it offline")
            }
            Self::NoStorageAsset { storage } => write!(
                f,
                "no_storage_asset: storage {storage} of the admitted package has no asset for the current source versions and row order; build it offline"
            ),
            Self::StorageVersions(error) => write!(f, "{error}"),
            Self::Worker(error) => write!(f, "{error}"),
            Self::Answer(error) => write!(f, "Verus package call: {error}"),
            Self::NoCall => f.write_str("child returned no observation"),
        }
    }
}

impl std::error::Error for ServeError {}

impl From<StatementError> for ServeError {
    fn from(error: StatementError) -> Self {
        Self::Statement(error)
    }
}

impl From<CanonError> for ServeError {
    fn from(error: CanonError) -> Self {
        Self::Canonical(error)
    }
}

impl From<RecordError> for ServeError {
    fn from(error: RecordError) -> Self {
        Self::Records(error)
    }
}

impl From<StoreError> for ServeError {
    fn from(error: StoreError) -> Self {
        Self::Records(RecordError::from(error))
    }
}

impl From<WorkerError> for ServeError {
    fn from(error: WorkerError) -> Self {
        Self::Worker(error)
    }
}

impl From<AnswerError> for ServeError {
    fn from(error: AnswerError) -> Self {
        Self::Answer(error)
    }
}

impl From<VersionError> for ServeError {
    fn from(error: VersionError) -> Self {
        match error {
            VersionError::NoAsset { storage } => Self::NoStorageAsset { storage },
            VersionError::Records(error) => Self::Records(error),
            other => Self::StorageVersions(other),
        }
    }
}
