//! Derived record indexes (`index/records/<stream>.json`) and the `index/` lock that serializes record writers.
//!
//! Indexes are a cache for inspection and quick lookup, rebuilt only from stored objects; existing index bytes are
//! never an input. Removing `index/` itself during active transactions is unsupported.

use crate::append_only::{AppendOnlyError, StreamHead, read_stream_heads};
use crate::canonical_json::canonical_document;
use crate::content_id::ContentId;
use crate::object_store::{ObjectStore, StoreError};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fs::File;
use std::path::PathBuf;

pub const RECORD_INDEX_FORMAT_VERSION: u32 = 1;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RecordIndex {
    pub format_version: u32,
    pub stream: String,
    pub head: ContentId,
    pub sequence: u64,
}

impl RecordIndex {
    pub fn path(store: &ObjectStore, stream: &str) -> PathBuf {
        store.index_root().join("records").join(format!("{stream}.json"))
    }
}

/// Rewrite every record index from the stored objects alone and return the written files. Offline recovery may
/// recreate an absent `index/`.
pub fn rebuild_indexes(store: &ObjectStore) -> Result<Vec<PathBuf>, AppendOnlyError> {
    let index_root = store.index_root();
    std::fs::create_dir_all(&index_root).map_err(|error| AppendOnlyError::io(&index_root, error))?;
    let _lock = IndexLock::exclusive(store)?;
    write_record_indexes(store, &read_stream_heads(store)?)
}

/// Replace `index/records/` with one canonical file per stream head. The caller holds the exclusive lock.
pub(crate) fn write_record_indexes(
    store: &ObjectStore,
    heads: &BTreeMap<String, StreamHead>,
) -> Result<Vec<PathBuf>, AppendOnlyError> {
    let records_root = store.index_root().join("records");
    match std::fs::remove_dir_all(&records_root) {
        Ok(()) => {}
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => return Err(AppendOnlyError::io(&records_root, error)),
    }
    std::fs::create_dir_all(&records_root).map_err(|error| AppendOnlyError::io(&records_root, error))?;
    let mut written = Vec::with_capacity(heads.len());
    for (stream, head) in heads {
        let index = RecordIndex {
            format_version: RECORD_INDEX_FORMAT_VERSION,
            stream: stream.clone(),
            head: head.head,
            sequence: head.sequence,
        };
        let text = canonical_document(&index).map_err(StoreError::from)?;
        let path = RecordIndex::path(store, stream);
        std::fs::write(&path, format!("{text}\n")).map_err(|error| AppendOnlyError::io(&path, error))?;
        written.push(path);
    }
    Ok(written)
}

/// The head a stream's index file names, if the file exists. An unreadable index is refused, never ignored.
pub(crate) fn read_indexed_head(store: &ObjectStore, stream: &str) -> Result<Option<ContentId>, AppendOnlyError> {
    let path = RecordIndex::path(store, stream);
    match std::fs::read_to_string(&path) {
        Ok(text) => {
            let index: RecordIndex = serde_json::from_str(&text)
                .map_err(|error| AppendOnlyError::IndexOnlyAuthorityRefused { path, reason: error.to_string() })?;
            Ok(Some(index.head))
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(error) => Err(AppendOnlyError::io(&path, error)),
    }
}

/// An advisory lock on the `index/` directory, held until dropped. Readers never create lock files.
pub(crate) struct IndexLock {
    _directory: File,
}

impl IndexLock {
    pub fn shared(store: &ObjectStore) -> Result<Self, StoreError> {
        let (path, directory) = Self::open_index(store)?;
        directory.lock_shared().map_err(|error| StoreError::io(&path, error))?;
        Ok(Self { _directory: directory })
    }

    pub fn exclusive(store: &ObjectStore) -> Result<Self, StoreError> {
        let (path, directory) = Self::open_index(store)?;
        directory.lock().map_err(|error| StoreError::io(&path, error))?;
        Ok(Self { _directory: directory })
    }

    fn open_index(store: &ObjectStore) -> Result<(PathBuf, File), StoreError> {
        let path = store.index_root();
        let directory = File::open(&path).map_err(|error| StoreError::io(&path, error))?;
        Ok((path, directory))
    }
}
