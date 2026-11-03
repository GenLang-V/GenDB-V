//! Host-wide leases that keep timed measurements free of concurrent work: every build or Verus run holds a shared
//! activity lease; a timed measurement holds the exclusive timing lease (activity, build and race locks). Author Bash
//! commands take the same shared activity lease through the provider's shell guardian, so an author's own tool calls
//! never exclude each other; they only wait while a timed measurement runs, or while one has waited longer than
//! [`GATE_AFTER`] for the machine (the timing gate, [`HostLocks::timing_gate`], bounds a measurement's wait).
//!
//! Ported from the earlier version's `general_experiment::BarrierPaths` (the request field is still `barriers`, with the same keys).

use serde::{Deserialize, Serialize};
use crate::file_lock::FileLock;
use std::fs::{File, OpenOptions};
use std::path::{Path, PathBuf};

/// The three lock files of a host (absolute paths; created on first use).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HostLocks {
    pub activity_lock: PathBuf,
    pub build_lock: PathBuf,
    pub race_lock: PathBuf,
}

/// Held locks; dropping the lease releases them.
pub struct HostLease {
    _locks: Vec<FileLock>,
}

/// How long a timed measurement waits for the exclusive activity lease before it closes the timing gate
/// ([`HostLocks::timing_gate`]). A framework scheduling constant, not an author decision.
pub const GATE_AFTER: std::time::Duration = std::time::Duration::from_secs(60);

/// The exclusive lock of `path` if it can be taken within `patience` (polled every 50 ms), else `None`.
fn try_lock_for(path: &Path, patience: std::time::Duration) -> Result<Option<FileLock>, String> {
    let started = std::time::Instant::now();
    loop {
        let error = match FileLock::acquire(open_lock_file(path)?, libc::LOCK_EX | libc::LOCK_NB) {
            Ok(lock) => return Ok(Some(lock)),
            Err(error) => error,
        };
        if error.raw_os_error() != Some(libc::EWOULDBLOCK) {
            return Err(format!("{}: {error}", path.display()));
        }
        if started.elapsed() >= patience {
            return Ok(None);
        }
        std::thread::sleep(std::time::Duration::from_millis(50));
    }
}

fn open_lock_file(path: &Path) -> Result<File, String> {
    OpenOptions::new().read(true).write(true).create(true).truncate(false).open(path).map_err(|e| format!("{}: {e}", path.display()))
}

fn lock(path: &Path, mode: i32) -> Result<FileLock, String> {
    FileLock::acquire(open_lock_file(path)?, mode).map_err(|e| format!("{}: {e}", path.display()))
}

impl HostLocks {
    /// The timing gate (`<activity_lock>.gate`). Every new shared holder passes through it (shared, released once the
    /// activity lease is held). A timed measurement first waits for the activity lease without it, for
    /// [`GATE_AFTER`]; only when shared work still holds the machine then does it close the gate (exclusive), so new
    /// shared work waits and the measurement gets the machine when the running shared work ends. flock alone prefers
    /// no one: without the gate, overlapping shared holders could starve a measurement; with the gate closed at once,
    /// every author's shell would wait behind any long shared run (a whole-crate Verus check) whenever a measurement
    /// waits (observed: 300-1300 s queue waits).
    pub fn timing_gate(&self) -> PathBuf {
        PathBuf::from(format!("{}.gate", self.activity_lock.display()))
    }

    pub fn validate(&self) -> Result<(), String> {
        let paths = [&self.activity_lock, &self.build_lock, &self.race_lock];
        if paths.iter().any(|p| !p.is_absolute()) || paths.iter().collect::<std::collections::BTreeSet<_>>().len() != 3 {
            return Err("three distinct absolute activity/build/race lock paths required".into());
        }
        Ok(())
    }

    /// Shared activity lease: waits only while a timed measurement holds the timing lease.
    pub fn activity(&self) -> Result<HostLease, String> {
        self.validate()?;
        let gate = lock(&self.timing_gate(), libc::LOCK_SH)?;
        let lease = lock(&self.activity_lock, libc::LOCK_SH)?;
        drop(gate);
        Ok(HostLease { _locks: vec![lease] })
    }

    /// The lease of maintenance work (cleanup, reclaim, record repair) while author sessions may be live: the shared
    /// activity lease, exactly like an author's own tool call. Maintenance never takes the exclusive timing lease,
    /// which would stop every live author's Bash commands for its whole duration (a 141 s wait in Q14).
    pub fn maintenance(&self) -> Result<HostLease, String> {
        self.activity()
    }

    /// Exclusive timing lease, for timed measurements only (official evaluations, the final measurement, and local
    /// trials and profiles). The caller must not hold an activity lease (no shared-to-exclusive upgrade).
    pub fn timing(&self) -> Result<HostLease, String> {
        self.validate()?;
        let mut locks = vec![];
        let activity = match try_lock_for(&self.activity_lock, GATE_AFTER)? {
            Some(activity) => activity,
            None => {
                locks.push(lock(&self.timing_gate(), libc::LOCK_EX)?);
                lock(&self.activity_lock, libc::LOCK_EX)?
            }
        };
        locks.extend([activity, lock(&self.build_lock, libc::LOCK_EX)?, lock(&self.race_lock, libc::LOCK_EX)?]);
        Ok(HostLease { _locks: locks })
    }
}
