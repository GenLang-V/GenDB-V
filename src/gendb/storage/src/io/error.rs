//! Typed refusals of storage I/O. `Display` keeps the earlier version's refusal texts; callers match variants, not strings.

use gendb_artifacts::ColType;
use std::{fmt, path::PathBuf};

pub type Result<T> = std::result::Result<T, StorageIoError>;

/// The leading word of a [`StorageIoError::StorageReserve`] refusal, which a parent reading a child's stderr matches.
pub const STORAGE_RESERVE_REFUSAL: &str = "storage_reserve_reached";

#[derive(Debug)]
pub enum StorageIoError {
    /// A file or directory operation failed.
    File { path: PathBuf, source: std::io::Error },
    /// An archive metadata file is not valid JSON of its format, or could not be encoded.
    Json { path: PathBuf, source: serde_json::Error },
    /// Arrow decoding, encoding or array construction failed.
    Arrow(arrow::error::ArrowError),
    /// Caller-supplied tables, projection or reference tables disagree with the declared shape.
    Shape(&'static str),
    /// A persisted archive is malformed, from another lifecycle, or changed on disk.
    Archive { path: PathBuf, reason: &'static str },
    /// The archive carries non-canonical native encodings (decimal coefficient views or registered storage).
    /// Only the earlier GenDB version (not part of this repository) serves them.
    V7Only { path: PathBuf, file: &'static str },
    /// The declared column type has no canonical native form (e.g. `Binary`, or a decimal outside 1..=38).
    UnsupportedType(ColType),
    /// Anonymous read-only memory could not be mapped or protected.
    Memory(std::io::Error),
    /// A row, byte or offset extent does not fit the address space or the ABI integers.
    Overflow(&'static str),
    /// Writing `write` more bytes under `path` would leave less than the filesystem's free-space `reserve` (`free`
    /// bytes were free): a resource refusal, not a fault of what is written.
    StorageReserve { path: PathBuf, free: u64, reserve: u64, write: u64 },
}

impl StorageIoError {
    pub(crate) fn file(path: impl Into<PathBuf>) -> impl FnOnce(std::io::Error) -> Self {
        let path = path.into();
        move |source| Self::File { path, source }
    }
    pub(crate) fn json(path: impl Into<PathBuf>) -> impl FnOnce(serde_json::Error) -> Self {
        let path = path.into();
        move |source| Self::Json { path, source }
    }
    pub(crate) fn archive(path: impl Into<PathBuf>, reason: &'static str) -> Self {
        Self::Archive {
            path: path.into(),
            reason,
        }
    }
}

impl fmt::Display for StorageIoError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::File { path, source } => write!(f, "{}: {source}", path.display()),
            Self::Json { path, source } => write!(f, "{}: {source}", path.display()),
            Self::Arrow(error) => write!(f, "{error}"),
            Self::Shape(reason) => f.write_str(reason),
            Self::Archive { path, reason } => write!(f, "{reason}: {}", path.display()),
            Self::V7Only { path, file } => write!(
                f,
                "{} holds {file}: non-canonical native source encodings are served only by the earlier GenDB version (not part of this repository)",
                path.display()
            ),
            Self::UnsupportedType(ty) => write!(f, "unsupported native field type {ty:?}"),
            Self::Memory(error) => write!(f, "read-only memory mapping failed: {error}"),
            Self::Overflow(what) => write!(f, "{what} overflow"),
            Self::StorageReserve { path, free, reserve, write } => write!(
                f,
                "{STORAGE_RESERVE_REFUSAL}: writing {write} more bytes under {} would leave less than the {reserve}-byte free-space reserve ({free} bytes free)",
                path.display()
            ),
        }
    }
}

impl std::error::Error for StorageIoError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::File { source, .. } | Self::Memory(source) => Some(source),
            Self::Json { source, .. } => Some(source),
            Self::Arrow(error) => Some(error),
            _ => None,
        }
    }
}

impl From<arrow::error::ArrowError> for StorageIoError {
    fn from(error: arrow::error::ArrowError) -> Self {
        Self::Arrow(error)
    }
}
