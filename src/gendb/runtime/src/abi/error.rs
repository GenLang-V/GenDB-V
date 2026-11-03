//! Typed refusals of the ABI host. `Display` keeps the earlier version's texts; callers match variants, not strings.

use super::outcome::CallStatus;
use gendb_storage::io::StorageIoError;
use std::{fmt, path::PathBuf};

#[derive(Debug)]
pub enum AbiError {
    /// `dlopen` failed (or the path contains NUL); `reason` is the loader's message.
    Open { path: PathBuf, reason: String },
    /// The library lacks one of the ABI symbols (a saved v1/v2 library lacks the v3 layout symbol).
    MissingSymbol { path: PathBuf, symbol: &'static str, reason: String },
    /// The library's layout record differs from [`super::expected_layout`].
    LayoutMismatch { actual: Vec<u64>, expected: Vec<u64> },
    /// The entry returned non-zero: it had no call record to write.
    EntryFailed(i32),
    /// The call record carries a status code outside the ABI table.
    UnknownStatus(u32),
    /// `2 * range_capacity` range words do not fit the address space.
    RangeCapacityOverflow,
    /// The builder delivered parts out of protocol (order, element code, null data), or its part count, result
    /// bytes or status contradict the call record.
    PartDelivery(&'static str),
    /// The query delivered its result wire out of protocol (twice, null data), or its length contradicts the record.
    WireDelivery(&'static str),
    /// Status, SQL error code and result wire disagree ([`super::check_query_wire`]).
    WireMismatch { status: CallStatus, reason: String },
    /// A build returned a query-only status (`SqlError`, `ParamRefused`, `Capacity`).
    BuildStatus(CallStatus),
    /// Copying, storing or mapping parts failed.
    Storage(StorageIoError),
}

impl fmt::Display for AbiError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Open { path, reason } => write!(f, "dlopen {}: {reason}", path.display()),
            Self::MissingSymbol { path, symbol, reason } => write!(f, "{} lacks symbol {symbol}: {reason}", path.display()),
            Self::LayoutMismatch { actual, expected } => {
                write!(f, "verus library ABI layout {actual:?} differs from host {expected:?}")
            }
            Self::EntryFailed(code) => write!(f, "verus entry returned {code}"),
            Self::UnknownStatus(code) => write!(f, "verus v3 shim returned unknown status {code}"),
            Self::RangeCapacityOverflow => f.write_str("range capacity overflow"),
            Self::PartDelivery(reason) | Self::WireDelivery(reason) => f.write_str(reason),
            Self::WireMismatch { status, reason } => write!(f, "result wire inconsistent with status {status:?}: {reason}"),
            Self::BuildStatus(status) => write!(f, "a build returned the query status {status:?}"),
            Self::Storage(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for AbiError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Storage(error) => Some(error),
            _ => None,
        }
    }
}

impl From<StorageIoError> for AbiError {
    fn from(error: StorageIoError) -> Self {
        Self::Storage(error)
    }
}
