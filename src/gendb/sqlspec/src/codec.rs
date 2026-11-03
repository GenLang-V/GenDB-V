//! Host side of the value wire formats of SQLSpec's executable values (`exec::value::EVal`): the database wire
//! `GSQLDB1` the reference evaluator reads, and the result wire `GSQLRS1` that the evaluator shim and the ABI v3
//! runtime shim (`runtime/verus/gendb_shim.rs`) write.
//!
//! Trust: this codec is a listed trusted component, mirrored byte for byte by the trusted shims
//! (`sqlspec/interpreter/host/shim.rs`, `runtime/verus/gendb_shim.rs`). It decides no value validity: types,
//! NULLs, ranges and text are checked by the verified `check_db` inside the evaluator, and a result's rows are the
//! verified outcome the shim encoded.

use std::fmt;

const DB_MAGIC: &[u8; 8] = b"GSQLDB1\0";
const RESULT_MAGIC: &[u8; 8] = b"GSQLRS1\0";

/// One executable SQL value (`exec::value::EVal`): dates are days and timestamps microseconds since 2000-01-01,
/// numerics a coefficient with its display scale, text UTF-8 bytes (`char(n)` canonical, trailing blanks removed).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum HostValue {
    Null,
    Bool(bool),
    Int(i64),
    Num { coeff: i128, scale: u32 },
    Date(i32),
    Ts(i64),
    Text(Vec<u8>),
}

/// Rows per table, table id = position in the translated schema.
pub type HostTables = Vec<Vec<Vec<HostValue>>>;

/// SQL errors of the semantics (`spec::value::SqlError`) with PostgreSQL's SQLSTATE.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SqlErrorKind {
    NumericValueOutOfRange,
    DatetimeFieldOverflow,
    DivisionByZero,
    CardinalityViolation,
    SubstringError,
    InvalidEscapeSequence,
    InvalidEscapeCharacter,
    /// Not a SQL outcome: the denotation of an ill-typed AST (unreachable after the verified type check).
    TypeError,
}

impl SqlErrorKind {
    /// The error of a result-wire error code (the shims' `sql_error_code`).
    pub fn from_code(code: u8) -> Option<SqlErrorKind> {
        Some(match code {
            1 => SqlErrorKind::NumericValueOutOfRange,
            2 => SqlErrorKind::DatetimeFieldOverflow,
            3 => SqlErrorKind::TypeError,
            4 => SqlErrorKind::DivisionByZero,
            5 => SqlErrorKind::CardinalityViolation,
            6 => SqlErrorKind::SubstringError,
            7 => SqlErrorKind::InvalidEscapeSequence,
            8 => SqlErrorKind::InvalidEscapeCharacter,
            _ => return None,
        })
    }

    pub fn name(self) -> &'static str {
        match self {
            SqlErrorKind::NumericValueOutOfRange => "numeric_value_out_of_range",
            SqlErrorKind::DatetimeFieldOverflow => "datetime_field_overflow",
            SqlErrorKind::DivisionByZero => "division_by_zero",
            SqlErrorKind::CardinalityViolation => "cardinality_violation",
            SqlErrorKind::SubstringError => "substring_error",
            SqlErrorKind::InvalidEscapeSequence => "invalid_escape_sequence",
            SqlErrorKind::InvalidEscapeCharacter => "invalid_escape_character",
            SqlErrorKind::TypeError => "type_error",
        }
    }

    pub fn sqlstate(self) -> Option<&'static str> {
        match self {
            SqlErrorKind::NumericValueOutOfRange => Some("22003"),
            SqlErrorKind::DatetimeFieldOverflow => Some("22008"),
            SqlErrorKind::DivisionByZero => Some("22012"),
            SqlErrorKind::CardinalityViolation => Some("21000"),
            SqlErrorKind::SubstringError => Some("22011"),
            SqlErrorKind::InvalidEscapeSequence => Some("22025"),
            SqlErrorKind::InvalidEscapeCharacter => Some("22019"),
            SqlErrorKind::TypeError => None,
        }
    }
}

/// A decoded result wire. The first four outcomes are the ones the ABI v3 runtime shim writes; the reference
/// evaluator's entry `abi_run` can also report the input-domain outcomes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RunOutcome {
    /// `Done(Ok(rows))`: exactly `denote_top` of the query on the database (canonical order).
    Rows(Vec<Vec<HostValue>>),
    /// `Done(Err(e))`: the SQL error of `denote_top`.
    SqlError(SqlErrorKind),
    /// A concrete exact intermediate is outside the executable domain (`!fits_ordered`); not a SQL outcome.
    Capacity,
    /// The database is outside the input domain (`!db_wf`), decided by the verified checker.
    BadDatabase,
    /// Unreachable by `lemma_query_wf`; reported if it ever appears.
    IllTyped,
    /// The rows violate a declared integrity constraint (`!constraints_hold`), decided by the verified checker.
    ConstraintViolation,
    /// The shim refused malformed wire bytes before any verified code ran.
    WireRefused,
}

/// Result wire bytes that do not decode.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WireError {
    Magic,
    Truncated,
    /// A length or count does not fit `usize`.
    LengthOverflow,
    ValueTag(u8),
    SqlErrorCode(u8),
    Status(u8),
    TrailingBytes,
}

impl fmt::Display for WireError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WireError::Magic => f.write_str("result wire magic"),
            WireError::Truncated => f.write_str("truncated result wire"),
            WireError::LengthOverflow => f.write_str("length overflow"),
            WireError::ValueTag(t) => write!(f, "result value tag {t}"),
            WireError::SqlErrorCode(k) => write!(f, "sql error code {k}"),
            WireError::Status(s) => write!(f, "result status {s}"),
            WireError::TrailingBytes => f.write_str("trailing bytes in result wire"),
        }
    }
}

impl std::error::Error for WireError {}

/// `GSQLDB1`: table count, then per table its row count, per row its arity and values (little endian).
pub fn encode_database(tables: &HostTables) -> Vec<u8> {
    let mut out = DB_MAGIC.to_vec();
    out.extend((tables.len() as u64).to_le_bytes());
    for rows in tables {
        out.extend((rows.len() as u64).to_le_bytes());
        for row in rows {
            out.extend((row.len() as u64).to_le_bytes());
            for v in row {
                encode_value(&mut out, v);
            }
        }
    }
    out
}

/// Value encoding shared by both wires: a tag byte, then the payload.
fn encode_value(out: &mut Vec<u8>, v: &HostValue) {
    match v {
        HostValue::Null => out.push(0),
        HostValue::Bool(b) => out.extend([1, *b as u8]),
        HostValue::Int(x) => {
            out.push(2);
            out.extend(x.to_le_bytes());
        }
        HostValue::Num { coeff, scale } => {
            out.push(3);
            out.extend(coeff.to_le_bytes());
            out.extend(scale.to_le_bytes());
        }
        HostValue::Date(d) => {
            out.push(4);
            out.extend(d.to_le_bytes());
        }
        HostValue::Ts(t) => {
            out.push(5);
            out.extend(t.to_le_bytes());
        }
        HostValue::Text(b) => {
            out.push(6);
            out.extend((b.len() as u64).to_le_bytes());
            out.extend(b);
        }
    }
}

/// The `GSQLRS1` result wire of `Rows(rows)` (status 0), which [`decode_result`] reads back exactly (stored test
/// references).
pub fn encode_result_rows(rows: &[Vec<HostValue>]) -> Vec<u8> {
    let mut out = RESULT_MAGIC.to_vec();
    out.push(0);
    out.extend((rows.len() as u64).to_le_bytes());
    for row in rows {
        out.extend((row.len() as u64).to_le_bytes());
        for v in row {
            encode_value(&mut out, v);
        }
    }
    out
}

/// `GSQLRS1`: a status byte (0 rows, 1 SQL error + code, 2 capacity, 3 bad database, 4 ill typed, 5 wire refused,
/// 6 constraint violation); rows are a row count, then per row its arity and values.
pub fn decode_result(bytes: &[u8]) -> Result<RunOutcome, WireError> {
    let mut r = Reader { bytes, at: 0 };
    if r.take(8)? != RESULT_MAGIC {
        return Err(WireError::Magic);
    }
    let outcome = match r.byte()? {
        0 => {
            let row_count = r.count()?;
            let mut rows = Vec::new();
            for _ in 0..row_count {
                let arity = r.count()?;
                let mut row = Vec::new();
                for _ in 0..arity {
                    row.push(r.value()?);
                }
                rows.push(row);
            }
            RunOutcome::Rows(rows)
        }
        1 => {
            let code = r.byte()?;
            RunOutcome::SqlError(SqlErrorKind::from_code(code).ok_or(WireError::SqlErrorCode(code))?)
        }
        2 => RunOutcome::Capacity,
        3 => RunOutcome::BadDatabase,
        4 => RunOutcome::IllTyped,
        5 => RunOutcome::WireRefused,
        6 => RunOutcome::ConstraintViolation,
        s => return Err(WireError::Status(s)),
    };
    if r.at != bytes.len() {
        return Err(WireError::TrailingBytes);
    }
    Ok(outcome)
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8], WireError> {
        let end = self.at.checked_add(n).ok_or(WireError::LengthOverflow)?;
        let s = self.bytes.get(self.at..end).ok_or(WireError::Truncated)?;
        self.at = end;
        Ok(s)
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N], WireError> {
        Ok(self.take(N)?.try_into().expect("length checked"))
    }

    fn byte(&mut self) -> Result<u8, WireError> {
        Ok(self.array::<1>()?[0])
    }

    fn count(&mut self) -> Result<usize, WireError> {
        usize::try_from(u64::from_le_bytes(self.array()?)).map_err(|_| WireError::LengthOverflow)
    }

    fn value(&mut self) -> Result<HostValue, WireError> {
        Ok(match self.byte()? {
            0 => HostValue::Null,
            1 => HostValue::Bool(self.byte()? != 0),
            2 => HostValue::Int(i64::from_le_bytes(self.array()?)),
            3 => HostValue::Num { coeff: i128::from_le_bytes(self.array()?), scale: u32::from_le_bytes(self.array()?) },
            4 => HostValue::Date(i32::from_le_bytes(self.array()?)),
            5 => HostValue::Ts(i64::from_le_bytes(self.array()?)),
            6 => {
                let len = self.count()?;
                HostValue::Text(self.take(len)?.to_vec())
            }
            t => return Err(WireError::ValueTag(t)),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The value encoding decodes back through the result wire (the two wires share it).
    #[test]
    fn rows_round_trip_through_the_value_encoding() {
        let row = vec![HostValue::Num { coeff: -1, scale: 2 }, HostValue::Text(b"a".to_vec()), HostValue::Null, HostValue::Date(-2191)];
        let database = encode_database(&vec![vec![row.clone()]]);
        assert_eq!(&database[..8], DB_MAGIC);
        let mut wire = RESULT_MAGIC.to_vec();
        wire.push(0);
        // A result's row list has the same shape as one table of the database wire.
        wire.extend(&database[16..]);
        assert_eq!(decode_result(&wire), Ok(RunOutcome::Rows(vec![row.clone()])));
        assert_eq!(encode_result_rows(&[row.clone()]), wire);
        let exact = vec![HostValue::Text(vec![0xff, 0]), HostValue::Num { coeff: -(10i128.pow(37)), scale: 10 }, HostValue::Bool(true), HostValue::Ts(-1), HostValue::Int(i64::MIN)];
        let rows = vec![exact, row, vec![]];
        assert_eq!(decode_result(&encode_result_rows(&rows)), Ok(RunOutcome::Rows(rows)));
        wire.push(0);
        assert_eq!(decode_result(&wire), Err(WireError::TrailingBytes));
        assert_eq!(decode_result(b"GSQLRS1\0\x01\x04"), Ok(RunOutcome::SqlError(SqlErrorKind::DivisionByZero)));
        assert_eq!(decode_result(b"GSQLRS1\0\x01\x09"), Err(WireError::SqlErrorCode(9)));
    }
}
