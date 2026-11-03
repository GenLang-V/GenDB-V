//! Exclusive library-wide locks that serialize one step across the sessions sharing a library (several controllers may
//! run at once): `<library>/locks/<name>`, held with `flock` until dropped.
//! - `storage-budget.lock`: the storage budget check and the registrations it admits (`storage::budget`);
//! - `reverify-<storage name>.lock`: the re-verification of a stale admitted storage, so two sessions never re-verify
//!   and rebuild the same storage at once (the second finds the first's recorded result).

use gendb_artifacts::ObjectStore;
use gendb_verification::admission::AdmissionError;
use crate::file_lock::FileLock;
use std::fs::OpenOptions;

/// The budget lock's file name.
pub const BUDGET_LOCK: &str = "storage-budget.lock";

/// The re-verification lock's file name of storage `name`.
pub fn reverification_lock(name: &str) -> String {
    format!("reverify-{name}.lock")
}

/// A held library lock; dropping it releases the lock.
pub struct LibraryLock {
    _lock: FileLock,
}

impl LibraryLock {
    /// Wait for and take the exclusive lock `name` of `store`'s library.
    pub fn acquire(store: &ObjectStore, name: &str) -> Result<Self, AdmissionError> {
        let directory = store.root().join("locks");
        std::fs::create_dir_all(&directory).map_err(|e| AdmissionError::tool(format!("{}: {e}", directory.display())))?;
        let path = directory.join(name);
        let file = OpenOptions::new().read(true).write(true).create(true).truncate(false).open(&path).map_err(|e| AdmissionError::tool(format!("{}: {e}", path.display())))?;
        let lock = FileLock::acquire(file, libc::LOCK_EX).map_err(|e| AdmissionError::tool(format!("{}: {e}", path.display())))?;
        Ok(Self { _lock: lock })
    }
}
