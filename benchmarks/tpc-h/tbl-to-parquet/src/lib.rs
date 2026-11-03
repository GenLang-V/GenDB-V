//! Exact scaled-integer Decimal128 materialization (Arrow/Parquet) of the
//! TPC-H raw input.
//!
//! Every materialized decimal value is checked against an exact parse of the
//! source text into a scaled integer; a nonzero mismatch count is a hard
//! failure, never a tolerance. No floating point value exists anywhere on the
//! write or the check path.
#![forbid(unsafe_code)]

use std::fmt;

pub mod manifest;
pub mod materialize;
pub mod parse;
pub mod schema;
pub mod verify;

/// Stable identifier for this crate, used by skeleton self-checks.
pub const CRATE_NAME: &str = "decimal-store";

/// Workspace-pinned arrow version, recorded verbatim in the manifest.
pub const ARROW_PIN: &str = "58.1.0";
/// Workspace-pinned parquet version, recorded verbatim in the manifest.
pub const PARQUET_PIN: &str = "58.1.0";

/// A hard failure. Every message names enough context (file, line, column,
/// token) to locate the offending byte in the raw input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Error(String);

impl Error {
    /// Build an error from any message-like value.
    pub fn new(message: impl Into<String>) -> Self {
        Error(message.into())
    }

    /// The message text.
    pub fn message(&self) -> &str {
        &self.0
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for Error {}

impl From<std::io::Error> for Error {
    fn from(e: std::io::Error) -> Self {
        Error(format!("io error: {e}"))
    }
}

impl From<arrow::error::ArrowError> for Error {
    fn from(e: arrow::error::ArrowError) -> Self {
        Error(format!("arrow error: {e}"))
    }
}

impl From<parquet::errors::ParquetError> for Error {
    fn from(e: parquet::errors::ParquetError) -> Self {
        Error(format!("parquet error: {e}"))
    }
}

/// Crate result alias.
pub type Result<T> = std::result::Result<T, Error>;

/// Peak resident set size of this process in KiB, read from `/proc/self/status`
/// (`VmHWM`). `None` when the field is unavailable.
pub fn peak_rss_kib() -> Option<u64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    for line in status.lines() {
        if let Some(rest) = line.strip_prefix("VmHWM:") {
            let digits: String = rest.chars().filter(|c| c.is_ascii_digit()).collect();
            return digits.parse().ok();
        }
    }
    None
}

/// Streaming SHA-256 of a file, hex encoded. Reads in fixed 8 MiB blocks so the
/// hash of a multi-gigabyte parquet file costs bounded memory.
pub fn sha256_file(path: &std::path::Path) -> Result<String> {
    use sha2::{Digest, Sha256};
    use std::io::Read;

    let mut file = std::fs::File::open(path)
        .map_err(|e| Error::new(format!("cannot open {} for hashing: {e}", path.display())))?;
    let mut hasher = Sha256::new();
    let mut buf = vec![0u8; 8 << 20];
    loop {
        let n = file.read(&mut buf)?;
        if n == 0 {
            break;
        }
        hasher.update(&buf[..n]);
    }
    let digest = hasher.finalize();
    let mut hex = String::with_capacity(64);
    for byte in digest {
        use fmt::Write as _;
        let _ = write!(hex, "{byte:02x}");
    }
    Ok(hex)
}

#[cfg(test)]
mod tests {
    use super::{CRATE_NAME, Error, peak_rss_kib, sha256_file};

    #[test]
    fn crate_name_is_stable() {
        assert_eq!(CRATE_NAME, "decimal-store");
    }

    #[test]
    fn error_displays_its_message() {
        let e = Error::new("boom");
        assert_eq!(e.to_string(), "boom");
        assert_eq!(e.message(), "boom");
    }

    #[test]
    fn peak_rss_is_readable_on_linux() {
        // The materialization report depends on this; if /proc is unavailable
        // the manifest records null rather than a wrong number.
        if let Some(kib) = peak_rss_kib() {
            assert!(kib > 0);
        }
    }

    #[test]
    fn sha256_matches_known_vector() {
        let dir = crate::schema::test_scratch_dir("sha-vector");
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("abc.txt");
        std::fs::write(&path, b"abc").unwrap();
        assert_eq!(
            sha256_file(&path).unwrap(),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }
}
