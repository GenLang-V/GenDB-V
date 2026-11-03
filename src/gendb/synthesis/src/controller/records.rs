//! Durable JSON records of a synthesis run.
//!
//! Two write disciplines, chosen by what the record is:
//! - mutable controller state (ledger, summaries, latest pointers) is replaced atomically: the new bytes are written to
//!   a `.pending` sibling, synced, renamed over the record and the directory is synced;
//! - immutable evidence (service records, framework error records, evaluation snapshots written once) is created once
//!   and never overwritten.
//!
//! Every error names the record path. Nothing here hashes or rescans data.

use serde::Serialize;
use serde::de::DeserializeOwned;
use std::fmt;
use std::fs::{self, File, OpenOptions};
use std::io::Write;
use std::path::{Path, PathBuf};

/// A record could not be read, decoded, created or replaced.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordError {
    pub path: PathBuf,
    pub detail: String,
}

impl RecordError {
    pub fn new(path: &Path, detail: impl fmt::Display) -> Self {
        Self { path: path.to_path_buf(), detail: detail.to_string() }
    }
}

impl fmt::Display for RecordError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "record {}: {}", self.path.display(), self.detail)
    }
}

impl std::error::Error for RecordError {}

/// Milliseconds since the Unix epoch (wall clock; record timestamps and file-name stamps only).
pub fn now_unix_ms() -> u64 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap_or_default().as_millis() as u64
}

/// A fresh random identifier from the kernel (`/proc/sys/kernel/random/uuid`). Identity generation never reads or
/// hashes user data.
pub fn random_uuid() -> Result<String, RecordError> {
    let source = Path::new("/proc/sys/kernel/random/uuid");
    fs::read_to_string(source).map(|id| id.trim().to_string()).map_err(|e| RecordError::new(source, e))
}

/// Replace `path` atomically with `value` as pretty JSON (stage, sync, rename, sync the directory).
pub fn write_json_atomic(path: &Path, value: &impl Serialize) -> Result<(), RecordError> {
    let bytes = serde_json::to_vec_pretty(value).map_err(|e| RecordError::new(path, e))?;
    let stage = path.with_extension("pending");
    let mut file = OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .open(&stage)
        .map_err(|e| RecordError::new(&stage, e))?;
    file.write_all(&bytes).and_then(|()| file.sync_all()).map_err(|e| RecordError::new(&stage, e))?;
    fs::rename(&stage, path).map_err(|e| RecordError::new(path, e))?;
    let parent = path.parent().ok_or_else(|| RecordError::new(path, "record has no parent directory"))?;
    File::open(parent).and_then(|directory| directory.sync_all()).map_err(|e| RecordError::new(parent, e))
}

/// Create `path` with `value` as pretty JSON; an existing record is never overwritten.
pub fn write_new_json(path: &Path, value: &impl Serialize) -> Result<(), RecordError> {
    let bytes = serde_json::to_vec_pretty(value).map_err(|e| RecordError::new(path, e))?;
    OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .and_then(|mut file| file.write_all(&bytes))
        .map_err(|e| RecordError::new(path, e))
}

/// Read and decode one JSON record.
pub fn read_json<T: DeserializeOwned>(path: &Path) -> Result<T, RecordError> {
    let bytes = fs::read(path).map_err(|e| RecordError::new(path, e))?;
    serde_json::from_slice(&bytes).map_err(|e| RecordError::new(path, e))
}

/// Create a directory (and its parents) for records.
pub fn create_dir(path: &Path) -> Result<(), RecordError> {
    fs::create_dir_all(path).map_err(|e| RecordError::new(path, e))
}

/// The first name of the series `<first>`, `<stem>-1.json`, `<stem>-2.json`, … that does not exist in `directory`,
/// so a resumed controller adds a record instead of overwriting an earlier one.
pub fn next_free_record(directory: &Path, first: &str, stem: &str) -> PathBuf {
    let mut ordinal = 0usize;
    loop {
        let name = if ordinal == 0 { first.to_string() } else { format!("{stem}-{ordinal}.json") };
        let path = directory.join(name);
        if !path.exists() {
            return path;
        }
        ordinal += 1;
    }
}
