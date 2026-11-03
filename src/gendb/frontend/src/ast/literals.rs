//! Literal validity: the PostgreSQL limits and calendar rules a literal node must satisfy (the Verus `type_lit`
//! conditions), and the canonical form of decimal integer text. Shared by the decoder and `crate::params`.

use super::document::{FieldValue, Node};
use super::{err, AstError};

/// PostgreSQL limits that literal validity depends on (the same constants as SQLSpec `spec::limits`).
pub const NUMERIC_DSCALE_MAX: u64 = 16383;
pub const NUMERIC_INT_DIGITS_MAX: u64 = 131072;
pub const NUMERIC_MAX_PRECISION: u64 = 1000;
pub const VARLENA_MAX_CHARS: u64 = 10_485_760;

/// Proleptic Gregorian calendar validity.
pub fn valid_ymd(y: i64, m: i64, d: i64) -> bool {
    if !(1..=12).contains(&m) || d < 1 {
        return false;
    }
    let leap = y % 4 == 0 && (y % 100 != 0 || y % 400 == 0);
    let days_in_month = [31, if leap { 29 } else { 28 }, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31][(m - 1) as usize];
    d <= days_in_month
}

/// The text of `v` if it is a canonical decimal integer: optional `-`, no leading zero, no `-0`.
pub(super) fn canonical_int(v: &serde_json::Value) -> Option<String> {
    let s = v.as_str()?;
    let digits = s.strip_prefix('-').unwrap_or(s);
    let canonical = !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()) && (digits == "0" || !digits.starts_with('0')) && s != "-0";
    canonical.then(|| s.to_owned())
}

/// Literal validity (Verus `type_lit`) of a decoded node and the range of `Table` ids. Other tags are unconstrained here.
pub(super) fn check_literal_and_table(n: &Node, table_count: usize) -> Result<(), AstError> {
    let int = |name: &str| match n.field(name) {
        Some(FieldValue::Int(s)) => s.clone(),
        _ => unreachable!("schema field {name}"),
    };
    let nat = |name: &str| match n.field(name) {
        Some(FieldValue::Nat(v)) => *v,
        _ => unreachable!("schema field {name}"),
    };
    match n.tag.as_str() {
        "Int" => {
            let fits_kind = match n.field("kind") {
                Some(FieldValue::Enum(k)) if k == "Int4" => int("v").parse::<i32>().is_ok(),
                _ => int("v").parse::<i64>().is_ok(),
            };
            if !fits_kind {
                return err("Int literal outside its kind");
            }
        }
        "Num" => {
            let digits = int("coeff").trim_start_matches('-').len() as u64;
            let scale = nat("scale");
            if scale > NUMERIC_DSCALE_MAX || digits > NUMERIC_INT_DIGITS_MAX + scale {
                return err("Num literal outside PostgreSQL's numeric format");
            }
        }
        "Date" => match (int("y").parse::<i64>(), int("m").parse::<i64>(), int("d").parse::<i64>()) {
            (Ok(y), Ok(m), Ok(d)) if valid_ymd(y, m, d) => {}
            _ => return err("Date literal is not a calendar date"),
        },
        "Table" if nat("table") >= table_count as u64 => return err("Table id outside the schema"),
        _ => {}
    }
    Ok(())
}
