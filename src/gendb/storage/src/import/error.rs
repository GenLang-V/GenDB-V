//! Typed refusals of original-data import, prepared-source reuse and the DataFusion reference. Callers match variants;
//! `Display` states the reason for records and logs.

use crate::io::StorageIoError;
use std::{fmt, path::PathBuf};

pub type Result<T> = std::result::Result<T, ImportError>;

#[derive(Debug)]
pub enum ImportError {
    /// The declared dataset is malformed or cannot be imported (names, types, locations, format).
    Declaration {
        table: String,
        reason: String,
    },
    /// An original source file disagrees with its declaration or cannot be read.
    Source {
        path: PathBuf,
        reason: String,
    },
    /// A source file's lifecycle stamp (device, inode, size, modification and change times) differs from the one
    /// recorded at preparation, or changed while its columns were read. A new source version must be prepared.
    SourceChanged {
        table: String,
    },
    /// A column demand names an undeclared table or column, or disagrees with the declared column.
    Demand {
        table: String,
        reason: String,
    },
    /// The prepared capture lacks demanded columns: `(table, missing declared ordinals)`; no ordinals means the table
    /// itself was not captured.
    NotCaptured {
        missing: Vec<(String, Vec<usize>)>,
    },
    /// A prepared root, snapshot receipt or registration is malformed, of another version, or does not belong to the
    /// requested dataset.
    Prepared {
        path: PathBuf,
        reason: String,
    },
    /// A reference SQL statement is not a read-only query over the declared tables, or has an unsupported result type.
    Reference(String),
    File {
        path: PathBuf,
        source: std::io::Error,
    },
    Json {
        path: PathBuf,
        source: serde_json::Error,
    },
    Parquet {
        path: PathBuf,
        source: parquet::errors::ParquetError,
    },
    Arrow(arrow::error::ArrowError),
    DataFusion(datafusion::error::DataFusionError),
    /// Source-column normalization, archive or mapping failure.
    Io(StorageIoError),
}

impl ImportError {
    pub(crate) fn file(path: impl Into<PathBuf>) -> impl FnOnce(std::io::Error) -> Self {
        let path = path.into();
        move |source| Self::File { path, source }
    }
    pub(crate) fn json(path: impl Into<PathBuf>) -> impl FnOnce(serde_json::Error) -> Self {
        let path = path.into();
        move |source| Self::Json { path, source }
    }
    pub(crate) fn parquet(path: impl Into<PathBuf>) -> impl FnOnce(parquet::errors::ParquetError) -> Self {
        let path = path.into();
        move |source| Self::Parquet { path, source }
    }
    pub(crate) fn declaration(table: &str, reason: impl Into<String>) -> Self {
        Self::Declaration {
            table: table.into(),
            reason: reason.into(),
        }
    }
    pub(crate) fn demand(table: &str, reason: impl Into<String>) -> Self {
        Self::Demand {
            table: table.into(),
            reason: reason.into(),
        }
    }
    pub(crate) fn prepared(path: impl Into<PathBuf>, reason: impl Into<String>) -> Self {
        Self::Prepared {
            path: path.into(),
            reason: reason.into(),
        }
    }
}

impl fmt::Display for ImportError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Declaration { table, reason } => write!(f, "declared dataset, table {table}: {reason}"),
            Self::Source { path, reason } => write!(f, "source file {}: {reason}", path.display()),
            Self::SourceChanged { table } => {
                write!(
                    f,
                    "source file lifecycle of table {table} changed; prepare a new source version"
                )
            }
            Self::Demand { table, reason } => write!(f, "column demand, table {table}: {reason}"),
            Self::NotCaptured { missing } => write!(f, "the prepared capture lacks demanded columns {missing:?}"),
            Self::Prepared { path, reason } => write!(f, "prepared source {}: {reason}", path.display()),
            Self::Reference(reason) => write!(f, "DataFusion reference: {reason}"),
            Self::File { path, source } => write!(f, "{}: {source}", path.display()),
            Self::Json { path, source } => write!(f, "{}: {source}", path.display()),
            Self::Parquet { path, source } => write!(f, "Parquet {}: {source}", path.display()),
            Self::Arrow(e) => write!(f, "Arrow: {e}"),
            Self::DataFusion(e) => write!(f, "DataFusion: {e}"),
            Self::Io(e) => e.fmt(f),
        }
    }
}

impl std::error::Error for ImportError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::File { source, .. } => Some(source),
            Self::Json { source, .. } => Some(source),
            Self::Parquet { source, .. } => Some(source),
            Self::Arrow(e) => Some(e),
            Self::DataFusion(e) => Some(e),
            Self::Io(e) => Some(e),
            _ => None,
        }
    }
}

impl From<StorageIoError> for ImportError {
    fn from(e: StorageIoError) -> Self {
        Self::Io(e)
    }
}

impl From<arrow::error::ArrowError> for ImportError {
    fn from(e: arrow::error::ArrowError) -> Self {
        Self::Arrow(e)
    }
}

impl From<datafusion::error::DataFusionError> for ImportError {
    fn from(e: datafusion::error::DataFusionError) -> Self {
        Self::DataFusion(e)
    }
}
