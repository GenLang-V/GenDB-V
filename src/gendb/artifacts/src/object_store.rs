//! The filesystem object store: immutable typed records and raw blobs, each named by its content identity.
//!
//! Layout of a library root: `objects/<hex id>` holds every object, `index/` holds derived record indexes (see
//! `record_index`), `.staging/` holds unpublished writes and `assets/` holds stored asset directories (see
//! `asset_directory`). A typed record is a canonical envelope
//! (`canonical_json`) named by the SHA-256 of its bytes; a blob is raw bytes named by their SHA-256.
//!
//! Publication is atomic: bytes are written and synced in `.staging/`, then hard-linked to their final name, which
//! never replaces an existing file. A reader therefore sees a complete object or none. Publishing identical bytes
//! again is a no-op; different bytes under an existing name are refused.
//!
//! Reads re-check the digest of the bytes they return (the format's existing content-addressing check); nothing here
//! scans or re-hashes the whole library.

use crate::canonical_json::{self, CanonError, EnvelopeError};
use crate::content_id::ContentId;
use serde::Serialize;
use std::fmt;
use std::fs::{File, OpenOptions};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

/// Leading bytes of a retired v1 hex-in-JSON blob (`gendb.blob.v1`). Such an object also hashes to its own name, so
/// the blob reader refuses it explicitly rather than returning envelope bytes as blob content.
const RETIRED_HEX_BLOB_PREFIX: &[u8] = b"{\"format_version\":1,\"kind\":\"gendb.blob.v1\",\"payload\":{\"bytes_hex\":\"";
const RETIRED_HEX_BLOB_KIND: &str = "gendb.blob.v1";

/// Bytes of object header read by [`ObjectStore::list_kind`]; the envelope's `kind` precedes its payload.
const KIND_HEADER_BYTES: u64 = 512;

/// One typed record whose digest, envelope and canonical form were checked when it was read.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerifiedObject {
    pub id: ContentId,
    pub format_version: u32,
    pub kind: String,
    canonical_payload: String,
}

impl VerifiedObject {
    pub fn decode<T: serde::de::DeserializeOwned>(&self) -> Result<T, StoreError> {
        serde_json::from_str(&self.canonical_payload).map_err(|error| StoreError::InvalidEnvelope(error.to_string()))
    }

    pub fn canonical_payload(&self) -> &str {
        &self.canonical_payload
    }
}

/// A library of immutable objects rooted at one directory.
#[derive(Debug, Clone)]
pub struct ObjectStore {
    root: PathBuf,
}

impl ObjectStore {
    /// Open a library, creating `objects/` and `index/` if absent (a new run or admission library).
    pub fn open(root: impl AsRef<Path>) -> Result<Self, StoreError> {
        let store = Self { root: root.as_ref().to_path_buf() };
        for directory in [store.objects_root(), store.index_root()] {
            std::fs::create_dir_all(&directory).map_err(|error| StoreError::io(&directory, error))?;
        }
        Ok(store)
    }

    /// Open an existing library without creating anything (serving and reading saved libraries).
    pub fn open_existing(root: impl AsRef<Path>) -> Result<Self, StoreError> {
        let store = Self { root: root.as_ref().to_path_buf() };
        for directory in [store.objects_root(), store.index_root()] {
            if !directory.is_dir() {
                return Err(StoreError::io(&directory, std::io::ErrorKind::NotFound.into()));
            }
        }
        Ok(store)
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    pub fn objects_root(&self) -> PathBuf {
        self.root.join("objects")
    }

    pub fn index_root(&self) -> PathBuf {
        self.root.join("index")
    }

    pub fn object_path(&self, id: ContentId) -> PathBuf {
        self.objects_root().join(id.to_hex())
    }

    /// Store a typed record as its canonical envelope and return its identity. The envelope is checked to be
    /// readable by [`Self::read`] before it is published.
    pub fn put<T: Serialize>(&self, format_version: u32, kind: &str, payload: &T) -> Result<ContentId, StoreError> {
        if kind.is_empty() {
            return Err(StoreError::InvalidEnvelope("object kind must not be empty".into()));
        }
        let envelope = canonical_json::canonical_envelope(format_version, kind, payload)?;
        let id = canonical_json::sha256(envelope.as_bytes());
        canonical_json::parse_envelope(envelope.as_bytes()).map_err(|error| StoreError::from_envelope(id, error))?;
        self.publish(id, envelope.as_bytes())?;
        Ok(id)
    }

    /// Store raw bytes as a blob named by their SHA-256 ([`blob_id`]); identical bytes share one object.
    pub fn put_blob(&self, bytes: &[u8]) -> Result<ContentId, StoreError> {
        let id = canonical_json::sha256(bytes);
        self.publish(id, bytes)?;
        Ok(id)
    }

    /// Read a typed record, checking its digest, envelope and canonical form. Nothing is trusted from the file name.
    pub fn read(&self, expected: ContentId) -> Result<VerifiedObject, StoreError> {
        let bytes = self.read_named_bytes(expected)?;
        let envelope = canonical_json::parse_envelope(&bytes).map_err(|error| StoreError::from_envelope(expected, error))?;
        Ok(VerifiedObject {
            id: expected,
            format_version: envelope.format_version,
            kind: envelope.kind,
            canonical_payload: envelope.canonical_payload,
        })
    }

    /// Read a blob, checking its digest and, when given, its recorded length.
    pub fn read_blob(&self, expected: ContentId, expected_bytes: Option<u64>) -> Result<Vec<u8>, StoreError> {
        let bytes = self.read_named_bytes(expected)?;
        if bytes.starts_with(RETIRED_HEX_BLOB_PREFIX) {
            return Err(StoreError::RetiredBlobKind { id: expected, kind: RETIRED_HEX_BLOB_KIND });
        }
        if let Some(expected_length) = expected_bytes.filter(|length| *length != bytes.len() as u64) {
            return Err(StoreError::BlobLengthMismatch { id: expected, expected: expected_length, actual: bytes.len() as u64 });
        }
        Ok(bytes)
    }

    /// Every typed record of one `kind`, in identity order, each fully read.
    ///
    /// Discovery reads only a bounded header of each object: the canonical envelope places `kind` before the
    /// payload, so a record of `kind` starts with `{"format_version":<digits>,"kind":<kind>,"payload":`. Payload
    /// bytes cannot imitate that prefix, and every match is then read in full by [`Self::read`].
    pub fn list_kind(&self, kind: &str) -> Result<Vec<VerifiedObject>, StoreError> {
        let objects = self.objects_root();
        let mut kind_marker = String::from(",\"kind\":");
        canonical_json::write_json_string(kind, &mut kind_marker);
        kind_marker.push_str(",\"payload\":");
        let mut ids = Vec::new();
        for entry in std::fs::read_dir(&objects).map_err(|error| StoreError::io(&objects, error))? {
            let entry = entry.map_err(|error| StoreError::io(&objects, error))?;
            let name = entry.file_name();
            let name = name.to_string_lossy();
            if name.starts_with('.') {
                continue;
            }
            let id = ContentId::parse_hex(&name).map_err(|_| StoreError::InvalidObjectName(entry.path()))?;
            if header_has_kind(&entry.path(), &kind_marker)? {
                ids.push(id);
            }
        }
        ids.sort();
        ids.into_iter()
            .map(|id| {
                let object = self.read(id)?;
                if object.kind != kind {
                    return Err(StoreError::InvalidEnvelope(format!("kind header mismatch for {id}")));
                }
                Ok(object)
            })
            .collect()
    }

    fn read_named_bytes(&self, expected: ContentId) -> Result<Vec<u8>, StoreError> {
        let path = self.object_path(expected);
        let bytes = std::fs::read(&path).map_err(|error| StoreError::io(&path, error))?;
        let actual = canonical_json::sha256(&bytes);
        if actual != expected {
            return Err(StoreError::DigestMismatch { expected, actual });
        }
        Ok(bytes)
    }

    /// Make `bytes` visible as `objects/<id>` only once every byte is durable, never replacing an existing object.
    /// Staging lives outside `objects/`, so an interrupted write is never mistaken for an object.
    fn publish(&self, id: ContentId, bytes: &[u8]) -> Result<(), StoreError> {
        static NEXT_STAGING_NAME: AtomicU64 = AtomicU64::new(0);
        let staging = self.root.join(".staging");
        std::fs::create_dir_all(&staging).map_err(|error| StoreError::io(&staging, error))?;
        let (staged, mut file) = loop {
            let path =
                staging.join(format!("put-{}-{}", std::process::id(), NEXT_STAGING_NAME.fetch_add(1, Ordering::Relaxed)));
            match OpenOptions::new().write(true).create_new(true).open(&path) {
                Ok(file) => break (path, file),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(StoreError::io(&path, error)),
            }
        };
        let target = self.object_path(id);
        let linked = (|| {
            file.write_all(bytes).map_err(|error| StoreError::io(&staged, error))?;
            file.sync_all().map_err(|error| StoreError::io(&staged, error))?;
            match std::fs::hard_link(&staged, &target) {
                Ok(()) => {}
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => {
                    let existing = std::fs::read(&target).map_err(|error| StoreError::io(&target, error))?;
                    if existing != bytes {
                        return Err(StoreError::ImmutableConflict { path: target.clone() });
                    }
                }
                Err(error) => return Err(StoreError::io(&target, error)),
            }
            // Also sync after a duplicate: a peer may have linked the object and exited before syncing the entry.
            sync_directory(&self.objects_root())
        })();
        drop(file);
        let removed = std::fs::remove_file(&staged).map_err(|error| StoreError::io(&staged, error));
        linked?;
        removed?;
        sync_directory(&staging)
    }
}

fn header_has_kind(path: &Path, kind_marker: &str) -> Result<bool, StoreError> {
    let mut header = Vec::with_capacity(KIND_HEADER_BYTES as usize);
    File::open(path)
        .and_then(|file| file.take(KIND_HEADER_BYTES).read_to_end(&mut header))
        .map_err(|error| StoreError::io(path, error))?;
    let header = std::str::from_utf8(&header).unwrap_or_default();
    let after_version = header.strip_prefix("{\"format_version\":").and_then(|rest| {
        let digits = rest.bytes().take_while(u8::is_ascii_digit).count();
        (digits > 0).then_some(&rest[digits..])
    });
    Ok(after_version.is_some_and(|rest| rest.starts_with(kind_marker)))
}

fn sync_directory(path: &Path) -> Result<(), StoreError> {
    File::open(path).and_then(|directory| directory.sync_all()).map_err(|error| StoreError::io(path, error))
}

#[derive(Debug)]
pub enum StoreError {
    Io { path: PathBuf, message: String },
    Canonical(CanonError),
    InvalidObjectName(PathBuf),
    InvalidEnvelope(String),
    DigestMismatch { expected: ContentId, actual: ContentId },
    NonCanonicalObject { id: ContentId },
    ImmutableConflict { path: PathBuf },
    RetiredBlobKind { id: ContentId, kind: &'static str },
    BlobLengthMismatch { id: ContentId, expected: u64, actual: u64 },
    /// A stored asset directory could not be placed or is not a library asset directory (the reason says which).
    AssetDirectory { path: PathBuf, reason: String },
}

impl StoreError {
    pub(crate) fn io(path: &Path, error: std::io::Error) -> Self {
        Self::Io { path: path.to_path_buf(), message: error.to_string() }
    }

    fn from_envelope(id: ContentId, error: EnvelopeError) -> Self {
        match error {
            EnvelopeError::Canonical(error) => Self::Canonical(error),
            EnvelopeError::Invalid(message) => Self::InvalidEnvelope(message),
            EnvelopeError::NotCanonical => Self::NonCanonicalObject { id },
        }
    }
}

impl From<CanonError> for StoreError {
    fn from(error: CanonError) -> Self {
        Self::Canonical(error)
    }
}

impl fmt::Display for StoreError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io { path, message } => write!(f, "{}: {message}", path.display()),
            Self::Canonical(error) => error.fmt(f),
            Self::InvalidObjectName(path) => write!(f, "invalid object filename {}", path.display()),
            Self::InvalidEnvelope(message) => write!(f, "invalid object envelope: {message}"),
            Self::DigestMismatch { expected, actual } => write!(f, "object {expected} hashes as {actual}"),
            Self::NonCanonicalObject { id } => write!(f, "object {id} is not canonical JSON"),
            Self::ImmutableConflict { path } => write!(f, "immutable object conflict at {}", path.display()),
            Self::RetiredBlobKind { id, kind } => write!(f, "REFUSE_RETIRED_BLOB_KIND object={id} kind={kind}"),
            Self::BlobLengthMismatch { id, expected, actual } => {
                write!(f, "REFUSE_RAW_BLOB_LENGTH object={id} expected={expected} actual={actual}")
            }
            Self::AssetDirectory { path, reason } => write!(f, "{reason}: {}", path.display()),
        }
    }
}

impl std::error::Error for StoreError {}

/// The identity a blob of `bytes` has in every store (their SHA-256), computed without storing anything.
pub fn blob_id(bytes: &[u8]) -> ContentId {
    canonical_json::sha256(bytes)
}
