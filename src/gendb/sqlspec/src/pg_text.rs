//! PostgreSQL text forms of executable values: input parsing of dates and timestamps (fixtures, parameters) and
//! output rendering of result values (numeric with its display scale, ISO dates/timestamps, text) as JSON.
//! Calendar: proleptic Gregorian, PostgreSQL's epoch 2000-01-01, the representation of `exec::value::EVal`.
//!
//! Trust: rendering is trusted (it produces the rows the host reports); it mirrors PostgreSQL's `numeric_out`,
//! `date_out` and `timestamp_out` for the ISO DateStyle.

use crate::codec::{HostValue, RunOutcome};
use gendb_frontend::ast::{AstDocument, FieldValue};
use serde_json::{json, Value};
use std::fmt;

/// Days from 1970-01-01 to PostgreSQL's epoch 2000-01-01.
const PG_EPOCH_DAYS: i64 = 10957;
const MICROS_PER_DAY: i64 = 86_400_000_000;

/// A result text value that is not UTF-8 (the verified checker admits only UTF-8 text, so this means a codec fault).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NonUtf8Text(pub std::string::FromUtf8Error);

impl fmt::Display for NonUtf8Text {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "result text is not UTF-8: {}", self.0)
    }
}

impl std::error::Error for NonUtf8Text {}

/// Days since 1970-01-01 of a civil date (Howard Hinnant's algorithm; exact for all `i64` years in range).
fn days_from_civil(y: i64, m: i64, d: i64) -> i64 {
    let y = if m <= 2 { y - 1 } else { y };
    let era = y.div_euclid(400);
    let yoe = y - era * 400;
    let mp = (m + 9) % 12;
    let doy = (153 * mp + 2) / 5 + d - 1;
    let doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    era * 146097 + doe - 719468
}

/// The civil date `(year, month, day)` of days since 1970-01-01 (inverse of `days_from_civil`).
fn civil_from_days(z: i64) -> (i64, i64, i64) {
    let z = z + 719468;
    let era = z.div_euclid(146097);
    let doe = z - era * 146097;
    let yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    (if m <= 2 { y + 1 } else { y }, m, d)
}

/// Whether `y-m-d` is a calendar date (astronomical year).
pub fn valid_civil(y: i64, m: i64, d: i64) -> bool {
    let leap = (y % 4 == 0 && y % 100 != 0) || y % 400 == 0;
    let days_in_month = [31, if leap { 29 } else { 28 }, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
    (1..=12).contains(&m) && d >= 1 && d <= days_in_month[(m - 1) as usize]
}

/// `YYYY-MM-DD` (astronomical year; `BC` suffix not accepted) -> days since 2000-01-01.
pub fn parse_date(s: &str) -> Option<i64> {
    let p: Vec<&str> = s.split('-').collect();
    if p.len() != 3 || p[0].len() < 4 || p[1].len() != 2 || p[2].len() != 2 || !p.iter().all(|x| x.bytes().all(|b| b.is_ascii_digit())) {
        return None;
    }
    let (y, m, d) = (p[0].parse().ok()?, p[1].parse().ok()?, p[2].parse().ok()?);
    valid_civil(y, m, d).then(|| days_from_civil(y, m, d) - PG_EPOCH_DAYS)
}

/// `YYYY-MM-DD HH:MM:SS[.ffffff]` -> microseconds since 2000-01-01 00:00:00.
pub fn parse_timestamp(s: &str) -> Option<i64> {
    let (date, time) = s.split_once(' ')?;
    let days = parse_date(date)?;
    let (hms, micros) = match time.split_once('.') {
        Some((a, f)) if !f.is_empty() && f.len() <= 6 && f.bytes().all(|b| b.is_ascii_digit()) => (a, format!("{f:0<6}").parse::<i64>().ok()?),
        Some(_) => return None,
        None => (time, 0),
    };
    let t: Vec<&str> = hms.split(':').collect();
    if t.len() != 3 || !t.iter().all(|x| x.len() == 2 && x.bytes().all(|b| b.is_ascii_digit())) {
        return None;
    }
    let (h, mi, se): (i64, i64, i64) = (t[0].parse().ok()?, t[1].parse().ok()?, t[2].parse().ok()?);
    if h > 23 || mi > 59 || se > 59 {
        return None;
    }
    days.checked_mul(MICROS_PER_DAY)?.checked_add(((h * 60 + mi) * 60 + se) * 1_000_000 + micros)
}

/// `date_out`: `YYYY-MM-DD`, or `YYYY-MM-DD BC` for years before 1.
fn date_text(days: i64) -> String {
    let (y, m, d) = civil_from_days(days + PG_EPOCH_DAYS);
    if y <= 0 { format!("{:04}-{m:02}-{d:02} BC", 1 - y) } else { format!("{y:04}-{m:02}-{d:02}") }
}

/// `timestamp_out`: the date, `HH:MM:SS`, a fraction without trailing zeros, then the `BC` suffix.
fn timestamp_text(micros: i64) -> String {
    let days = micros.div_euclid(MICROS_PER_DAY);
    let rem = micros.rem_euclid(MICROS_PER_DAY);
    let (secs, frac) = (rem / 1_000_000, rem % 1_000_000);
    let date = date_text(days);
    let (date, bc) = match date.strip_suffix(" BC") {
        Some(d) => (d.to_string(), " BC"),
        None => (date, ""),
    };
    let mut t = format!("{date} {:02}:{:02}:{:02}", secs / 3600, secs / 60 % 60, secs % 60);
    if frac != 0 {
        t.push_str(format!(".{frac:06}").trim_end_matches('0'));
    }
    t + bc
}

/// Decimal text of `coeff * 10^-scale` with exactly `scale` fractional digits (PostgreSQL `numeric_out`).
pub fn numeric_text(coeff: i128, scale: u32) -> String {
    let digits = coeff.unsigned_abs().to_string();
    let scale = scale as usize;
    let padded = if digits.len() <= scale { format!("{}{digits}", "0".repeat(scale + 1 - digits.len())) } else { digits };
    let (int, frac) = padded.split_at(padded.len() - scale);
    let sign = if coeff < 0 { "-" } else { "" };
    if scale == 0 { format!("{sign}{int}") } else { format!("{sign}{int}.{frac}") }
}

/// JSON form of an output value: integers as numbers, booleans as booleans, everything else as PostgreSQL
/// output text (numeric with its scale, ISO dates/timestamps, text), NULL as null.
pub fn value_json(v: &HostValue) -> Result<Value, NonUtf8Text> {
    Ok(match v {
        HostValue::Null => Value::Null,
        HostValue::Bool(b) => json!(b),
        HostValue::Int(x) => json!(x),
        HostValue::Num { coeff, scale } => json!(numeric_text(*coeff, *scale)),
        HostValue::Date(d) => json!(date_text(*d as i64)),
        HostValue::Ts(t) => json!(timestamp_text(*t)),
        HostValue::Text(b) => json!(String::from_utf8(b.clone()).map_err(NonUtf8Text)?),
    })
}

/// Result record of one evaluation: status, output column metadata of the translated query (names, PostgreSQL
/// `\gdesc` types, the resolver's static types) and the rows in the evaluator's canonical order.
pub fn result_json(doc: &AstDocument, outcome: &RunOutcome) -> Result<Value, NonUtf8Text> {
    let columns: Vec<Value> = doc
        .output
        .names
        .iter()
        .zip(&doc.output.pg_types)
        .zip(&doc.output.columns)
        .map(|((n, t), c)| json!({ "name": n, "pg_type": t, "nullable": c.nullable, "dscale": c.dscale }))
        .collect();
    let mut r = json!({ "columns": columns });
    match outcome {
        RunOutcome::Rows(rows) => {
            let rows: Vec<Value> =
                rows.iter().map(|row| row.iter().map(value_json).collect::<Result<Vec<_>, _>>().map(Value::from)).collect::<Result<_, _>>()?;
            r["status"] = json!("rows");
            r["row_count"] = json!(rows.len());
            r["rows"] = json!(rows);
            r["ordered"] = json!(!matches!(doc.nodes[doc.root].field("keys"), Some(FieldValue::Children(k)) if k.is_empty()));
        }
        RunOutcome::SqlError(k) => {
            r["status"] = json!(if k.sqlstate().is_some() { "sql_error" } else { "ill_typed" });
            r["error_kind"] = json!(k.name());
            r["sqlstate"] = json!(k.sqlstate());
        }
        RunOutcome::Capacity => r["status"] = json!("capacity"),
        RunOutcome::BadDatabase => r["status"] = json!("invalid_input"),
        RunOutcome::WireRefused => r["status"] = json!("wire_refused"),
        RunOutcome::IllTyped => r["status"] = json!("ill_typed"),
        RunOutcome::ConstraintViolation => r["status"] = json!("constraint_violation"),
    }
    Ok(r)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn calendar_and_numeric_text() {
        assert_eq!(parse_date("2000-01-01"), Some(0));
        assert_eq!(parse_date("1994-01-01"), Some(-2191));
        assert_eq!(date_text(-2191), "1994-01-01");
        assert_eq!(parse_date("1995-02-29"), None);
        assert_eq!(timestamp_text(parse_timestamp("1995-01-01 00:00:00").unwrap()), "1995-01-01 00:00:00");
        assert_eq!(timestamp_text(parse_timestamp("1999-12-31 23:59:59.5").unwrap()), "1999-12-31 23:59:59.5");
        assert_eq!(numeric_text(2410000, 4), "241.0000");
        assert_eq!(numeric_text(-5, 2), "-0.05");
        assert_eq!(numeric_text(7, 0), "7");
    }
}
