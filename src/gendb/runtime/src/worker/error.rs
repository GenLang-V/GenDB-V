//! Typed refusals and failures of a worker run. `Display` keeps the earlier version's texts where one existed; callers match
//! variants, not strings (for example [`WorkerError::ChildFailed`] with [`super::ChildFailure::timed_out`]).

use super::parent::ChildFailure;
use crate::abi::AbiError;
use crate::answer::AnswerError;
use gendb_storage::io::StorageIoError;
use std::{fmt, path::PathBuf};

#[derive(Debug)]
pub enum WorkerError {
    /// Reading the request, writing the request/result/stderr files, or starting the child failed.
    File { path: PathBuf, source: std::io::Error },
    /// A request or result file is not valid JSON of its form.
    Json { path: PathBuf, source: serde_json::Error },
    /// The request has no `"abi": "v3"` marker: a saved ABI v1/v2 request (`marker` as found).
    SavedAbi { marker: Option<String> },
    /// The request was written by another build (for example a saved request of the earlier GenDB version).
    BuildIdentity { requested: serde_json::Value },
    /// The request breaks a request rule ([`super::WorkerRequest`]).
    Request(&'static str),
    /// An inline fixture value is not an exact value of its element type.
    Inline(String),
    /// Mapping source columns or stored parts, or storing built parts, failed.
    Storage(StorageIoError),
    /// Loading the library or a call failed at the ABI boundary.
    Abi(AbiError),
    /// A query call's status, error code and wire disagree, or its rows cannot be rendered.
    Answer(AnswerError),
    /// Parent side: the child ended without writing a result (crash, abort, refusal, or the caller's timeout).
    ChildFailed(ChildFailure),
}

impl fmt::Display for WorkerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::File { path, source } => write!(f, "{}: {source}", path.display()),
            Self::Json { path, source } => write!(f, "{}: {source}", path.display()),
            Self::SavedAbi { marker } => write!(
                f,
                "verus run ABI marker {marker:?}: saved ABI v1/v2 requests run only in the earlier GenDB version \
                 (not part of this repository)"
            ),
            Self::BuildIdentity { requested } => write!(
                f,
                "verus native worker build differs: the request names build {requested}, this worker is {}",
                crate::identity::runtime_build_identity()
            ),
            Self::Request(reason) => f.write_str(reason),
            Self::Inline(reason) => f.write_str(reason),
            Self::Storage(error) => write!(f, "{error}"),
            Self::Abi(error) => write!(f, "{error}"),
            Self::Answer(error) => write!(f, "{error}"),
            Self::ChildFailed(failure) => write!(
                f,
                "worker ended without a result (exit {:?}, signal {:?}): {}",
                failure.exit_code,
                failure.signal,
                failure.stderr.trim()
            ),
        }
    }
}

impl std::error::Error for WorkerError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::File { source, .. } => Some(source),
            Self::Json { source, .. } => Some(source),
            Self::Storage(error) => Some(error),
            Self::Abi(error) => Some(error),
            Self::Answer(error) => Some(error),
            _ => None,
        }
    }
}

impl From<StorageIoError> for WorkerError {
    fn from(error: StorageIoError) -> Self {
        Self::Storage(error)
    }
}

impl From<AbiError> for WorkerError {
    fn from(error: AbiError) -> Self {
        Self::Abi(error)
    }
}

impl From<AnswerError> for WorkerError {
    fn from(error: AnswerError) -> Self {
        Self::Answer(error)
    }
}

impl WorkerError {
    pub(super) fn file(path: impl Into<PathBuf>) -> impl FnOnce(std::io::Error) -> Self {
        let path = path.into();
        move |source| Self::File { path, source }
    }

    pub(super) fn json(path: impl Into<PathBuf>) -> impl FnOnce(serde_json::Error) -> Self {
        let path = path.into();
        move |source| Self::Json { path, source }
    }
}
