//! The answer of one query call, as the checked entry states it: rows, the exact SQL error, capacity or parameter
//! refusal. Used by the worker (to record readable observations) and by serving (to return the answer).
//!
//! The status, SQL error code and result wire of a call must agree ([`check_query_wire`], the same check the ABI host
//! applies when the call returns); rows are decoded with the SQLSpec result codec (`gendb_sqlspec::codec`, trusted)
//! and rendered as PostgreSQL output text with `gendb_sqlspec::pg_text::value_json` (trusted).

use crate::abi::{AbiError, CallOutcome, CallStatus, check_query_wire};
use gendb_sqlspec::codec::{HostValue, RunOutcome, SqlErrorKind, WireError, decode_result};
use gendb_sqlspec::pg_text::{NonUtf8Text, value_json};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::fmt;

/// What a query call answered. Each has its checked meaning (`gendb_entry::theorem_end_to_end`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum QueryAnswer {
    /// An allowed output of the statement at the arguments: the exact values decoded from the result wire.
    Rows(Vec<Vec<HostValue>>),
    /// The statement's meaning at the arguments is exactly this SQL error.
    SqlError(SqlErrorAnswer),
    /// The database is outside the capacity domain (not a SQL result).
    Capacity,
    /// The arguments are outside the declared parameter domain (decided by the verified entry before author code).
    ParamRefused,
}

/// The exact SQL error of a `SqlError` call: wire code, SQLSpec name and PostgreSQL SQLSTATE (none for the
/// unreachable `type_error`). JSON form unchanged from run results of the earlier GenDB version.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SqlErrorAnswer {
    pub code: u8,
    pub name: String,
    pub sqlstate: Option<String>,
}

impl SqlErrorAnswer {
    pub fn new(code: u8, kind: SqlErrorKind) -> Self {
        Self { code, name: kind.name().into(), sqlstate: kind.sqlstate().map(String::from) }
    }
}

/// Why a call outcome is not an answer.
#[derive(Debug)]
pub enum AnswerError {
    /// The status answers nothing (worker failure, refusals by the shim or binder, invalid build input).
    NoAnswer(CallStatus),
    /// Status, SQL error code and wire disagree.
    Inconsistent(AbiError),
    /// The rows wire does not decode.
    Wire(WireError),
    /// A rows wire decoded to something other than rows, or an error code has no SQLSpec error.
    Mismatch(String),
    /// A text value is not UTF-8 (it cannot be rendered as PostgreSQL output text).
    Text(NonUtf8Text),
}

impl fmt::Display for AnswerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoAnswer(status) => write!(f, "the call answered nothing: status {status:?}"),
            Self::Inconsistent(error) => write!(f, "{error}"),
            Self::Wire(error) => write!(f, "result wire: {error}"),
            Self::Mismatch(reason) => f.write_str(reason),
            Self::Text(error) => write!(f, "{error}"),
        }
    }
}

impl std::error::Error for AnswerError {}

impl From<NonUtf8Text> for AnswerError {
    fn from(error: NonUtf8Text) -> Self {
        Self::Text(error)
    }
}

impl QueryAnswer {
    /// The answer of a query call. Statuses without an answer are [`AnswerError::NoAnswer`]; every answer re-checks
    /// that status, SQL error code and wire agree (a run result read back from the worker is checked again).
    pub fn of(outcome: &CallOutcome) -> Result<Self, AnswerError> {
        let wire = outcome.result_wire.as_deref();
        check_query_wire(outcome.status, outcome.sql_error.map_or(0, u32::from), wire)
            .map_err(AnswerError::Inconsistent)?;
        match outcome.status {
            CallStatus::Ok => {
                let wire = wire.ok_or_else(|| AnswerError::Mismatch("an Ok call without a rows wire".into()))?;
                match decode_result(wire).map_err(AnswerError::Wire)? {
                    RunOutcome::Rows(rows) => Ok(Self::Rows(rows)),
                    other => Err(AnswerError::Mismatch(format!("result wire {other:?} does not match status Ok"))),
                }
            }
            CallStatus::SqlError => {
                let code =
                    outcome.sql_error.ok_or_else(|| AnswerError::Mismatch("SqlError without an error code".into()))?;
                let kind = SqlErrorKind::from_code(code)
                    .ok_or_else(|| AnswerError::Mismatch(format!("SQL error code {code} has no SQLSpec error")))?;
                Ok(Self::SqlError(SqlErrorAnswer::new(code, kind)))
            }
            CallStatus::Capacity => Ok(Self::Capacity),
            CallStatus::ParamRefused => Ok(Self::ParamRefused),
            status => Err(AnswerError::NoAnswer(status)),
        }
    }

    /// Record form: `{"status":"ok","rows":[...]}` (PostgreSQL output text, NULL as null),
    /// `{"status":"sql_error","code","name","sqlstate"}`, `{"status":"capacity",...}` or
    /// `{"status":"param_refused",...}`.
    pub fn record(&self) -> Result<Value, AnswerError> {
        Ok(match self {
            Self::Rows(rows) => json!({"status": "ok", "rows": rows_json(rows)?}),
            Self::SqlError(error) => {
                json!({"status": "sql_error", "code": error.code, "name": error.name, "sqlstate": error.sqlstate})
            }
            Self::Capacity => json!({
                "status": "capacity",
                "meaning": "the input is outside the capacity domain (checked claim: Capacity implies !capacity_domain)"
            }),
            Self::ParamRefused => json!({
                "status": "param_refused",
                "meaning": "the arguments are outside the declared parameter domain (decided by the verified entry)"
            }),
        })
    }
}

/// Rows as PostgreSQL output text per value (`value_json`: integers as numbers, numeric with its display scale, ISO
/// dates, text; NULL as null). A non-UTF-8 text is an error, never replaced.
pub fn rows_json(rows: &[Vec<HostValue>]) -> Result<Vec<Vec<Value>>, NonUtf8Text> {
    rows.iter().map(|row| row.iter().map(value_json).collect()).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::abi::{CallUsage, DispatchEvidence};

    fn outcome(status: CallStatus, sql_error: Option<u8>, wire: Option<&[u8]>) -> CallOutcome {
        CallOutcome {
            status,
            sql_error,
            result_wire: wire.map(<[u8]>::to_vec),
            parts_delivered: 0,
            dispatch: DispatchEvidence::default(),
            usage: CallUsage::default(),
            storage_requests: vec![],
        }
    }

    /// Every answering status, the status/code/wire agreement and the statuses without an answer.
    #[test]
    fn answers_follow_status_code_and_wire() {
        // Rows wire: status 0, one row of arity 1 holding numeric -5 at scale 2 (tag 3, i128 and u32 little endian).
        let mut rows_wire = b"GSQLRS1\0\x00".to_vec();
        rows_wire.extend(1u64.to_le_bytes());
        rows_wire.extend(1u64.to_le_bytes());
        rows_wire.push(3);
        rows_wire.extend((-5i128).to_le_bytes());
        rows_wire.extend(2u32.to_le_bytes());
        let rows = QueryAnswer::of(&outcome(CallStatus::Ok, None, Some(&rows_wire))).unwrap();
        assert_eq!(rows, QueryAnswer::Rows(vec![vec![HostValue::Num { coeff: -5, scale: 2 }]]));
        assert!(matches!(QueryAnswer::of(&outcome(CallStatus::Ok, None, None)), Err(AnswerError::Inconsistent(_))));
        rows_wire.push(0);
        assert!(matches!(QueryAnswer::of(&outcome(CallStatus::Ok, None, Some(&rows_wire))), Err(AnswerError::Wire(_))));
        let error = QueryAnswer::of(&outcome(CallStatus::SqlError, Some(1), Some(b"GSQLRS1\0\x01\x01"))).unwrap();
        assert_eq!(
            error,
            QueryAnswer::SqlError(SqlErrorAnswer {
                code: 1,
                name: "numeric_value_out_of_range".into(),
                sqlstate: Some("22003".into())
            })
        );
        assert!(matches!(
            QueryAnswer::of(&outcome(CallStatus::SqlError, Some(2), Some(b"GSQLRS1\0\x01\x01"))),
            Err(AnswerError::Inconsistent(_))
        ));
        assert_eq!(
            QueryAnswer::of(&outcome(CallStatus::Capacity, None, Some(b"GSQLRS1\0\x02"))).unwrap(),
            QueryAnswer::Capacity
        );
        assert_eq!(QueryAnswer::of(&outcome(CallStatus::ParamRefused, None, None)).unwrap(), QueryAnswer::ParamRefused);
        assert!(matches!(
            QueryAnswer::of(&outcome(CallStatus::ParamRefused, None, Some(b"GSQLRS1\0\x02"))),
            Err(AnswerError::Inconsistent(_))
        ));
        for status in [CallStatus::WorkerFailed, CallStatus::AbiRefused, CallStatus::Refused, CallStatus::InvalidInput]
        {
            assert!(
                matches!(QueryAnswer::of(&outcome(status, None, None)), Err(AnswerError::NoAnswer(s)) if s == status)
            );
        }
        let record = QueryAnswer::SqlError(SqlErrorAnswer::new(4, SqlErrorKind::DivisionByZero)).record().unwrap();
        assert_eq!(record, json!({"status": "sql_error", "code": 4, "name": "division_by_zero", "sqlstate": "22012"}));
    }

    /// PostgreSQL output text of each value kind; a non-UTF-8 text is refused.
    #[test]
    fn rows_render_as_postgres_text() {
        let rows = vec![
            vec![
                HostValue::Text("\u{e9}t\u{e9}".as_bytes().to_vec()),
                HostValue::Int(3),
                HostValue::Num { coeff: -5, scale: 2 },
            ],
            vec![HostValue::Text(vec![]), HostValue::Date(-2191), HostValue::Null],
        ];
        assert_eq!(
            rows_json(&rows).unwrap(),
            [vec![json!("\u{e9}t\u{e9}"), json!(3), json!("-0.05")], vec![json!(""), json!("1994-01-01"), Value::Null]]
        );
        assert!(rows_json(&[vec![HostValue::Text(vec![0xff])]]).is_err());
    }
}
