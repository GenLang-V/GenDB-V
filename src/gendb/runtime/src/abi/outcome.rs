//! What one call returns: status, exact SQL error code, the result wire, dispatch evidence and usage; and the check
//! that status, error code and wire agree.
//!
//! JSON forms are unchanged from the earlier version's `execution_runtime::verus_abi` (saved run results decode as they are).

use super::error::AbiError;
use serde::{Deserialize, Serialize};

/// GSQLRS1 result wire (the SQLSpec result codec): magic, then status byte 0 = rows, 1 = SQL error followed by one
/// code byte, 2 = capacity. Rows are decoded by the caller with the SQLSpec codec; this module checks the error and
/// capacity wires byte for byte.
pub const RESULT_MAGIC: &[u8; 8] = b"GSQLRS1\0";
const WIRE_ROWS: u8 = 0;
const WIRE_SQL_ERROR: u8 = 1;
const WIRE_CAPACITY: u8 = 2;

/// SQL error codes of the wire and of the call record: 1 numeric_value_out_of_range, 2 datetime_field_overflow,
/// 3 type_error, 4 division_by_zero, 5 cardinality_violation, 6 substring_error, 7 invalid_escape_sequence,
/// 8 invalid_escape_character (the SQLSpec reference evaluator's `error_code` table).
pub const SQL_ERROR_CODES: std::ops::RangeInclusive<u8> = 1..=8;

/// Status of a call.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CallStatus {
    Ok,
    /// Build only: the delivered columns are outside the declared column domains.
    InvalidInput,
    /// Engine entry only: the AST bytes decode to no statement (`decode_spec(ast) is None`). Query and build entries
    /// never produce it.
    Malformed,
    /// A joined worker thread failed (trusted thread/join semantics; never a result).
    WorkerFailed,
    /// The verified entry refused the worker count, or (builds) the verified binder refused the column shapes.
    Refused,
    /// The trusted shim refused the descriptors, arguments or the worker count.
    AbiRefused,
    /// The host part or result sink refused the delivery.
    SinkFailed,
    /// The input is outside the query's capacity domain (never a SQL result).
    Capacity,
    /// The statement's meaning on the database is exactly the SQL error in the call record and the wire.
    SqlError,
    /// The arguments are not a binding in the declared parameter domain (verified entry, before author code); for an
    /// engine call, the decoded statement is not supported (not well typed for the schema, `check_ordered`).
    ParamRefused,
}

impl CallStatus {
    /// Status codes of the call record (the shim's `STATUS_*`).
    pub(super) const CODES: [(u32, Self); 10] = [
        (0, Self::Ok),
        (1, Self::InvalidInput),
        (2, Self::Malformed),
        (3, Self::WorkerFailed),
        (4, Self::Refused),
        (5, Self::Capacity),
        (6, Self::SqlError),
        (7, Self::ParamRefused),
        (16, Self::AbiRefused),
        (17, Self::SinkFailed),
    ];

    pub(super) fn from_code(code: u32) -> Result<Self, AbiError> {
        Self::CODES
            .iter()
            .find(|(known, _)| *known == code)
            .map(|(_, status)| *status)
            .ok_or(AbiError::UnknownStatus(code))
    }
}

/// Observed dispatch of one call as reported by the verified code through the shim: workers spawned and joined, and
/// the declared row range `[lo, hi)` of each spawn (at most the call's range capacity; `ranges_reported` is the full
/// count). Descriptive evidence only.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DispatchEvidence {
    pub spawned: u64,
    pub joined: u64,
    pub ranges: Vec<(u64, u64)>,
    pub ranges_reported: u64,
}

/// Descriptive only. Process CPU covers all threads; `caller_cpu_ns` is the calling thread, so `process - caller` is
/// CPU consumed by other (worker) threads during the call.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CallUsage {
    pub wall_ns: u64,
    pub process_user_ns: u64,
    pub process_system_ns: u64,
    pub caller_cpu_ns: u64,
}

/// Request counters of one storage use of a v4 query call, as the verified read handle (`gendb_entry::stored`)
/// counted them. Descriptive evidence, never a proof input: `requests` extent calls, `elements` and `bytes` their
/// summed lengths (element count times element width), each saturating at `u64::MAX`. They count requests, not
/// element accesses (a returned slice may be read any number of times), not distinct bytes (extents may overlap or
/// repeat) and not device I/O (the page cache, readahead and the lazy mapping decide what the device reads).
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StorageRequestCounts {
    /// Position of the storage use in the query's declared use order.
    pub use_index: u64,
    pub requests: u64,
    pub elements: u64,
    pub bytes: u64,
}

/// One call. `result_wire` is the GSQLRS1 wire exactly as delivered (statuses `Ok`, `SqlError` and `Capacity` only,
/// JSON lowercase hex); `sql_error` is the exact error code of a `SqlError` (equal to the wire's code byte, checked
/// by [`check_query_wire`]). `storage_requests` (v4 query calls only; absent from the JSON when empty, so a v3 call
/// keeps its saved form): the request counters of every storage-use handle the entry reported, in use order.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CallOutcome {
    pub status: CallStatus,
    pub sql_error: Option<u8>,
    #[serde(with = "optional_hex_bytes")]
    pub result_wire: Option<Vec<u8>>,
    pub parts_delivered: u64,
    pub dispatch: DispatchEvidence,
    pub usage: CallUsage,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub storage_requests: Vec<StorageRequestCounts>,
}

/// The agreement of status, error code and wire, checked for every query call. `Ok` carries a rows wire (magic, 0;
/// rows decoded by the caller); `SqlError` exactly `magic, 1, code` with the call record's code in 1..=8; `Capacity`
/// exactly `magic, 2`; every other status neither wire nor code. Returns the SQL error code of a `SqlError`.
pub fn check_query_wire(status: CallStatus, sql_error: u32, wire: Option<&[u8]>) -> Result<Option<u8>, AbiError> {
    let mismatch = |reason: String| Err(AbiError::WireMismatch { status, reason });
    let body = wire.map(|w| w.strip_prefix(RESULT_MAGIC.as_slice()));
    match status {
        CallStatus::SqlError => {
            let code = u8::try_from(sql_error).ok().filter(|c| SQL_ERROR_CODES.contains(c));
            match (code, body) {
                (Some(c), Some(Some(b))) if b == [WIRE_SQL_ERROR, c] => Ok(Some(c)),
                (None, _) => mismatch(format!("call record error code {sql_error} outside 1..=8")),
                _ => mismatch("the error wire differs from magic, 1, code".into()),
            }
        }
        _ if sql_error != 0 => mismatch(format!("call record error code {sql_error} without SqlError")),
        CallStatus::Capacity => match body {
            Some(Some(b)) if b == [WIRE_CAPACITY] => Ok(None),
            _ => mismatch("the capacity wire differs from magic, 2".into()),
        },
        CallStatus::Ok => match body {
            Some(Some(b)) if b.first() == Some(&WIRE_ROWS) => Ok(None),
            _ => mismatch("no rows wire".into()),
        },
        _ => match wire {
            None => Ok(None),
            Some(_) => mismatch("a wire for a status without result".into()),
        },
    }
}

/// `Option<Vec<u8>>` as an optional lowercase hex string.
mod optional_hex_bytes {
    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    pub fn serialize<S: Serializer>(bytes: &Option<Vec<u8>>, serializer: S) -> Result<S::Ok, S::Error> {
        bytes.as_ref().map(|b| b.iter().map(|x| format!("{x:02x}")).collect::<String>()).serialize(serializer)
    }

    pub fn deserialize<'d, D: Deserializer<'d>>(deserializer: D) -> Result<Option<Vec<u8>>, D::Error> {
        Option::<String>::deserialize(deserializer)?
            .map(|text| {
                if text.len() % 2 != 0 {
                    return Err(serde::de::Error::custom("odd hex length"));
                }
                if !text.is_ascii() {
                    return Err(serde::de::Error::custom("non-hex character"));
                }
                (0..text.len())
                    .step_by(2)
                    .map(|i| u8::from_str_radix(&text[i..i + 2], 16).map_err(serde::de::Error::custom))
                    .collect()
            })
            .transpose()
    }
}
