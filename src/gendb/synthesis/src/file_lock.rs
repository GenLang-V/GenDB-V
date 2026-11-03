//! Advisory `flock` locks that are released explicitly.
//!
//! An `flock` lock belongs to the open file description, not to one descriptor. A child process spawned by any thread
//! of this process shares every open description from its fork until its exec closes the close-on-exec descriptors.
//! Merely closing the holder's descriptor inside that window leaves the lock held by the child for the moment, so a
//! non-blocking acquirer sees a free lock as held (observed: spurious `AlreadyOwned` ledger refusals while other test
//! threads spawned the SQL parser). A [`FileLock`] therefore unlocks (`LOCK_UN`, which releases the description's lock
//! whoever else refers to it) before its descriptor closes.

use std::fs::File;
use std::io;
use std::os::fd::AsRawFd;

/// A held `flock` lock on its file; dropping it releases the lock at once.
#[derive(Debug)]
pub struct FileLock {
    file: File,
}

impl FileLock {
    /// Take `operation` (`LOCK_EX` or `LOCK_SH`, optionally with `LOCK_NB`) on `file`, waiting unless `LOCK_NB` is
    /// given. A contended non-blocking request fails with `EWOULDBLOCK`.
    pub fn acquire(file: File, operation: libc::c_int) -> io::Result<Self> {
        // SAFETY: flock on a descriptor `file` owns; no memory is shared.
        if unsafe { libc::flock(file.as_raw_fd(), operation) } != 0 {
            return Err(io::Error::last_os_error());
        }
        Ok(Self { file })
    }
}

impl Drop for FileLock {
    fn drop(&mut self) {
        // SAFETY: flock on a descriptor `self.file` owns. An unlock cannot fail on a valid descriptor that holds the lock.
        unsafe { libc::flock(self.file.as_raw_fd(), libc::LOCK_UN) };
    }
}
