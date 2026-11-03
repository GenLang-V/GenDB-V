//! Append-only record streams, stored as ordinary immutable objects.
//!
//! A stream is a chain of `AppendRecord`s: sequence 0 has no predecessor, each later record names its predecessor,
//! and the record nobody names is the head. Appending stores a new record and never rewrites an existing one; the
//! current meaning of a stream (for example the admitted package of a statement) is the subject of its head.
//!
//! Authority is the objects alone. `index/records/<stream>.json` is a derived cache: [`lookup_record_head`]
//! recomputes the head from the stored append records and refuses an index that disagrees.
//!
//! Concurrency: writers of cooperating processes serialize on an exclusive lock of `index/`, readers take a shared
//! lock; readers create no files. Mixed unlocked writers and concurrent maintenance are unsupported.

use crate::content_id::ContentId;
use crate::object_store::{ObjectStore, StoreError};
use crate::record_index::{self, IndexLock, RecordIndex};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::{Path, PathBuf};

pub const APPEND_RECORD_KIND: &str = "gendb.append_record";
pub const APPEND_RECORD_FORMAT_VERSION: u32 = 1;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AppendRecord {
    pub stream: String,
    pub sequence: u64,
    pub previous: Option<ContentId>,
    pub subject: ContentId,
}

/// The head of one valid stream.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct StreamHead {
    pub head: ContentId,
    pub sequence: u64,
}

/// Append `subject` to `stream` and return the new record's identity. `subject` must be a readable stored record.
pub fn append_record(store: &ObjectStore, stream: &str, subject: ContentId) -> Result<ContentId, AppendOnlyError> {
    check_stream_name(stream)?;
    store.read(subject)?;
    let _lock = IndexLock::exclusive(store)?;
    let mut heads = read_stream_heads(store)?;
    let (sequence, previous) = match heads.get(stream) {
        Some(current) => (
            current
                .sequence
                .checked_add(1)
                .ok_or_else(|| AppendOnlyError::InvalidChain(format!("stream {stream} sequence overflow")))?,
            Some(current.head),
        ),
        None => (0, None),
    };
    let record = AppendRecord { stream: stream.to_string(), sequence, previous, subject };
    let id = store.put(APPEND_RECORD_FORMAT_VERSION, APPEND_RECORD_KIND, &record)?;
    // Under the exclusive lock the stored chains are the ones just read plus this record, so the index is written
    // from them rather than from a second read of every record.
    heads.insert(stream.to_string(), StreamHead { head: id, sequence });
    record_index::write_record_indexes(store, &heads)?;
    Ok(id)
}

/// The head record of `stream`, if any, recomputed from the stored records. A derived index entry that names another
/// head is refused, so an index can never authorize an absent or stale record.
pub fn lookup_record_head(store: &ObjectStore, stream: &str) -> Result<Option<ContentId>, AppendOnlyError> {
    check_stream_name(stream)?;
    let _lock = IndexLock::shared(store)?;
    let authoritative = read_stream_heads(store)?.get(stream).map(|current| current.head);
    let indexed = record_index::read_indexed_head(store, stream)?;
    if indexed.is_some() && indexed != authoritative {
        return Err(AppendOnlyError::IndexOnlyAuthorityRefused {
            path: RecordIndex::path(store, stream),
            reason: "index head does not reproduce from immutable objects".to_string(),
        });
    }
    Ok(authoritative)
}

/// Stream names are also index file names: non-empty ASCII letters, digits, `.`, `-` and `_`.
fn check_stream_name(stream: &str) -> Result<(), AppendOnlyError> {
    let valid = !stream.is_empty() && stream.bytes().all(|b| b.is_ascii_alphanumeric() || matches!(b, b'.' | b'-' | b'_'));
    if valid { Ok(()) } else { Err(AppendOnlyError::InvalidStream(stream.to_string())) }
}

/// Read every stored append record and return the head of each stream, refusing any record set that is not a set of
/// contiguous single-successor chains with readable subjects. The caller holds the index lock.
pub(crate) fn read_stream_heads(store: &ObjectStore) -> Result<BTreeMap<String, StreamHead>, AppendOnlyError> {
    let records = read_append_records(store)?;
    let successors_named = check_links(&records)?;
    let mut heads: BTreeMap<String, StreamHead> = BTreeMap::new();
    for (id, record) in records.iter().filter(|(id, _)| !successors_named.contains(id)) {
        let head = StreamHead { head: *id, sequence: record.sequence };
        if heads.insert(record.stream.clone(), head).is_some() {
            return Err(AppendOnlyError::InvalidChain(format!("stream {} has multiple heads", record.stream)));
        }
    }
    for (stream, head) in &heads {
        let length = records.values().filter(|record| &record.stream == stream).count();
        if usize::try_from(head.sequence).ok().and_then(|sequence| sequence.checked_add(1)) != Some(length) {
            return Err(AppendOnlyError::InvalidChain(format!("stream {stream} is not contiguous")));
        }
    }
    Ok(heads)
}

fn read_append_records(store: &ObjectStore) -> Result<BTreeMap<ContentId, AppendRecord>, AppendOnlyError> {
    let mut records = BTreeMap::new();
    for object in store.list_kind(APPEND_RECORD_KIND)? {
        if object.format_version != APPEND_RECORD_FORMAT_VERSION {
            return Err(AppendOnlyError::InvalidChain(format!(
                "record {} uses unsupported envelope version {}",
                object.id, object.format_version
            )));
        }
        let record: AppendRecord = object.decode()?;
        check_stream_name(&record.stream)?;
        store.read(record.subject).map_err(|error| {
            AppendOnlyError::InvalidChain(format!("record {} subject {} is unavailable: {error}", object.id, record.subject))
        })?;
        records.insert(object.id, record);
    }
    Ok(records)
}

/// Check every predecessor link (same stream, previous sequence, at most one successor, one record per position)
/// and return the records that some successor names.
fn check_links(records: &BTreeMap<ContentId, AppendRecord>) -> Result<BTreeSet<ContentId>, AppendOnlyError> {
    let mut positions = BTreeSet::new();
    let mut named = BTreeSet::new();
    for (id, record) in records {
        if !positions.insert((record.stream.as_str(), record.sequence)) {
            return Err(AppendOnlyError::InvalidChain(format!(
                "stream {} has two records at sequence {}",
                record.stream, record.sequence
            )));
        }
        match (record.sequence, record.previous) {
            (0, None) => {}
            (0, Some(_)) | (_, None) => {
                return Err(AppendOnlyError::InvalidChain(format!("record {id} has an invalid previous link")));
            }
            (sequence, Some(previous)) => {
                let predecessor = records.get(&previous).ok_or_else(|| {
                    AppendOnlyError::InvalidChain(format!("record {id} points to missing predecessor {previous}"))
                })?;
                if predecessor.stream != record.stream || predecessor.sequence.checked_add(1) != Some(sequence) {
                    return Err(AppendOnlyError::InvalidChain(format!(
                        "record {id} predecessor is from the wrong stream or sequence"
                    )));
                }
                if !named.insert(previous) {
                    return Err(AppendOnlyError::InvalidChain(format!("record {previous} has multiple successors")));
                }
            }
        }
    }
    Ok(named)
}

#[derive(Debug)]
pub enum AppendOnlyError {
    Store(StoreError),
    Io { path: PathBuf, message: String },
    InvalidStream(String),
    InvalidChain(String),
    IndexOnlyAuthorityRefused { path: PathBuf, reason: String },
}

impl AppendOnlyError {
    pub(crate) fn io(path: &Path, error: std::io::Error) -> Self {
        Self::Io { path: path.to_path_buf(), message: error.to_string() }
    }
}

impl From<StoreError> for AppendOnlyError {
    fn from(error: StoreError) -> Self {
        Self::Store(error)
    }
}

impl fmt::Display for AppendOnlyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Store(error) => error.fmt(f),
            Self::Io { path, message } => write!(f, "{}: {message}", path.display()),
            Self::InvalidStream(stream) => write!(f, "invalid record stream {stream:?}"),
            Self::InvalidChain(reason) => write!(f, "invalid append-only chain: {reason}"),
            Self::IndexOnlyAuthorityRefused { path, reason } => {
                write!(f, "index-only authority refused at {}: {reason}", path.display())
            }
        }
    }
}

impl std::error::Error for AppendOnlyError {}
