//! Descriptive device-read counter of the worker process (`read_bytes` of `/proc/self/io`), read before and after each
//! v4 call.
//!
//! `/proc/self/io` holds the totals of every thread of the process, so a call's worker threads are included. Its
//! `read_bytes` counts the bytes whose reading from the storage layer this process caused (page faults on mapped part
//! files and readahead included); a page already in the page cache counts 0. It therefore depends on the cache state
//! left by earlier runs and other processes, readahead and the file system: it is environment-sensitive evidence, not
//! an exact device count and never a proof input. The file's `rchar`/`syscr` are not recorded: memory-mapped reads
//! never appear there, and reading `/proc/self/io` itself would be counted in them.

use serde::{Deserialize, Serialize};

const PROCESS_IO_FILE: &str = "/proc/self/io";

/// `read_bytes` of `/proc/<pid>/io`, or `None` when it is absent or not a number.
pub fn parse_read_bytes(text: &str) -> Option<u64> {
    text.lines().find_map(|line| line.strip_prefix("read_bytes")?.strip_prefix(':')?.trim().parse().ok())
}

fn read_bytes_now() -> Option<u64> {
    parse_read_bytes(&std::fs::read_to_string(PROCESS_IO_FILE).ok()?)
}

/// The process I/O of one call (see the module notes for what it means and why it is environment sensitive).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProcessIoDelta {
    /// Bytes the process caused to be read from the storage layer during the call (page-cache hits count 0).
    pub read_bytes: u64,
}

/// Measure the process I/O of `call`: `None` when `/proc/self/io` is unavailable before or after (never zero instead).
pub fn measure_process_io<R>(call: impl FnOnce() -> R) -> (R, Option<ProcessIoDelta>) {
    let before = read_bytes_now();
    let result = call();
    let delta = before.zip(read_bytes_now()).map(|(before, after)| ProcessIoDelta { read_bytes: after.saturating_sub(before) });
    (result, delta)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn process_io_parses_and_measures() {
        let text = "rchar: 3239\nwchar: 32\nsyscr: 63\nsyscw: 6\nread_bytes: 8192\nwrite_bytes: 0\ncancelled_write_bytes: 0\n";
        assert_eq!(parse_read_bytes(text), Some(8192));
        assert_eq!(parse_read_bytes("rchar: 1\nsyscr: 2\n"), None, "read_bytes missing");
        assert_eq!(parse_read_bytes("read_bytes: x\n"), None);
        let (value, delta) = measure_process_io(|| 7);
        assert_eq!(value, 7);
        assert_eq!(delta.is_some(), std::path::Path::new(PROCESS_IO_FILE).exists());
    }
}
