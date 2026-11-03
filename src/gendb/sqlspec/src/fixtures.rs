//! Tiny fixture databases in the PostgreSQL reference format (`sqlspec/tests/fixtures/pg_reference/*.json`, format in
//! `sqlspec/tests/postgres_reference.py`): the harness loads the same file into PostgreSQL, and [`Fixture::database_for`]
//! converts it to the evaluator's executable values for the schema the parser resolved.
//!
//! Paths inside a fixture (`ddl[].path`, `cases[].query.path`) are relative to the repository root. Fixtures and the
//! PostgreSQL harness are test data read from the source tree this crate was built from ([`repository_root`]),
//! like the Python parser (`gendb_frontend::parser::SqlParser::pinned`); the Verus library itself is embedded.
//!
//! Trust: [`input_value`] is the input codec (a listed trusted component). It maps each fixture value to the
//! executable value PostgreSQL's input function would store for the column type, and refuses anything it would
//! have to round or guess (a numeric with more fractional digits than the column scale, exponents, non-ISO dates).
//! It does not decide validity: ranges, precision, lengths, NULLs in NOT NULL columns and UTF-8 are checked by the
//! verified `check_db` in the evaluator, which refuses the whole database (`invalid_input`) otherwise.

use crate::codec::{HostTables, HostValue};
use crate::pg_text::{parse_date, parse_timestamp};
use gendb_frontend::ast::{AstDocument, PgType, TableDef};
use serde_json::Value;
use std::collections::BTreeMap;
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};

/// The repository root of the source tree this crate was built from (`<root>/src/gendb/sqlspec`).
pub fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).ancestors().nth(3).expect("sqlspec lives at <repository>/src/gendb/sqlspec").to_path_buf()
}

/// `sqlspec/tests/fixtures`: the PostgreSQL reference fixtures (`pg_reference/`) and the constraint-violating
/// instances that only the evaluator runs (`constraints/`).
pub fn fixtures_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures")
}

/// The PostgreSQL reference harness (`run` records evidence, `compare` checks a candidate against it).
pub fn postgres_harness() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/postgres_reference.py")
}

/// A fixture file that cannot be read, or a value the input codec refuses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FixtureError(pub String);

impl fmt::Display for FixtureError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for FixtureError {}

#[derive(Clone, Debug)]
pub struct FixtureTable {
    pub name: String,
    /// Column names of `rows` followed by the `defaults` columns (the harness's INSERT column list).
    pub columns: Vec<String>,
    pub rows: Vec<Vec<Value>>,
}

/// The statement of a case: inline SQL or a labelled query of a query file.
#[derive(Clone, Debug)]
pub enum CaseQuery {
    Sql(String),
    Labelled { path: PathBuf, label: String },
}

#[derive(Clone, Debug)]
pub struct FixtureCase {
    pub name: String,
    pub query: CaseQuery,
    /// The case object as written (`expect`, `order_keys`, `value_only_columns`, `note`, ...).
    pub raw: Value,
}

#[derive(Clone, Debug)]
pub struct Fixture {
    pub name: String,
    pub path: PathBuf,
    /// Concatenated DDL (`ddl` entries in order).
    pub ddl: String,
    pub tables: Vec<FixtureTable>,
    pub cases: Vec<FixtureCase>,
}

fn field<'a>(v: &'a Value, k: &str, ctx: &str) -> Result<&'a Value, FixtureError> {
    v.get(k).ok_or_else(|| FixtureError(format!("{ctx}: missing `{k}`")))
}

fn text(v: &Value, k: &str, ctx: &str) -> Result<String, FixtureError> {
    field(v, k, ctx)?.as_str().map(str::to_owned).ok_or_else(|| FixtureError(format!("{ctx}: `{k}` must be a string")))
}

fn read(path: &Path) -> Result<String, FixtureError> {
    fs::read_to_string(path).map_err(|e| FixtureError(format!("{}: {e}", path.display())))
}

impl Fixture {
    pub fn load(path: &Path) -> Result<Self, FixtureError> {
        let v: Value = serde_json::from_str(&read(path)?).map_err(|e| FixtureError(format!("{}: {e}", path.display())))?;
        let root = repository_root();
        let mut ddl = String::new();
        for d in v.get("ddl").and_then(Value::as_array).into_iter().flatten() {
            match d.get("path").and_then(Value::as_str) {
                Some(p) => ddl.push_str(&read(&root.join(p))?),
                None => ddl.push_str(&text(d, "sql", "ddl entry")?),
            }
            ddl.push('\n');
        }
        let mut tables = Vec::new();
        for t in v.get("tables").and_then(Value::as_array).into_iter().flatten() {
            tables.push(load_table(t)?);
        }
        let mut cases = Vec::new();
        let listed = field(&v, "cases", "fixture")?.as_array().ok_or_else(|| FixtureError("cases must be a list".into()))?;
        for c in listed {
            let name = text(c, "name", "case")?;
            let query = match (c.get("sql").and_then(Value::as_str), c.get("query")) {
                (Some(sql), None) => CaseQuery::Sql(sql.to_owned()),
                (None, Some(q)) => CaseQuery::Labelled { path: root.join(text(q, "path", &name)?), label: text(q, "label", &name)? },
                _ => return Err(FixtureError(format!("{name}: exactly one of `sql` / `query`"))),
            };
            cases.push(FixtureCase { name, query, raw: c.clone() });
        }
        Ok(Fixture { name: text(&v, "fixture", "fixture")?, path: path.to_path_buf(), ddl, tables, cases })
    }

    /// The fixture's rows as executable values for the resolved schema `doc.tables` (table id = position).
    /// Tables of the schema without fixture rows are empty; columns missing from the fixture are NULL (the
    /// harness's INSERT leaves them to the column default, and the fragment's DDL has no defaults).
    pub fn database_for(&self, doc: &AstDocument) -> Result<HostTables, FixtureError> {
        if let Some(t) = self.tables.iter().find(|t| !doc.tables.iter().any(|d| d.name.eq_ignore_ascii_case(&t.name))) {
            return Err(FixtureError(format!("fixture table {} is not in the resolved schema", t.name)));
        }
        let by_name: BTreeMap<String, &FixtureTable> = self.tables.iter().map(|t| (t.name.to_lowercase(), t)).collect();
        doc.tables.iter().map(|def| table_rows(def, by_name.get(&def.name.to_lowercase()).copied())).collect()
    }
}

/// One `tables[]` entry: explicit columns, then the `defaults` columns not already listed, appended to each row.
fn load_table(t: &Value) -> Result<FixtureTable, FixtureError> {
    let name = text(t, "name", "table")?;
    let mut columns: Vec<String> = field(t, "columns", &name)?
        .as_array()
        .ok_or_else(|| FixtureError(format!("{name}: columns must be a list")))?
        .iter()
        .map(|c| c.as_str().map(str::to_owned).ok_or_else(|| FixtureError(format!("{name}: column names are strings"))))
        .collect::<Result<_, _>>()?;
    let explicit = columns.len();
    let defaults: Vec<(String, Value)> = t
        .get("defaults")
        .and_then(Value::as_object)
        .map(|m| m.iter().filter(|(k, _)| !columns.contains(k)).map(|(k, v)| (k.clone(), v.clone())).collect())
        .unwrap_or_default();
    columns.extend(defaults.iter().map(|(k, _)| k.clone()));
    let mut rows = Vec::new();
    for r in field(t, "rows", &name)?.as_array().ok_or_else(|| FixtureError(format!("{name}: rows must be a list")))? {
        let r = r.as_array().ok_or_else(|| FixtureError(format!("{name}: a row must be a list")))?;
        if r.len() != explicit {
            return Err(FixtureError(format!("{name}: row {r:?} does not match its columns")));
        }
        rows.push(r.iter().cloned().chain(defaults.iter().map(|(_, v)| v.clone())).collect());
    }
    Ok(FixtureTable { name, columns, rows })
}

fn table_rows(def: &TableDef, t: Option<&FixtureTable>) -> Result<Vec<Vec<HostValue>>, FixtureError> {
    let Some(t) = t else { return Ok(Vec::new()) };
    if let Some(n) = t.columns.iter().find(|n| !def.columns.iter().any(|c| c.name.eq_ignore_ascii_case(n))) {
        return Err(FixtureError(format!("{}: fixture column {n} is not in the table", t.name)));
    }
    let positions: Vec<Option<usize>> = def.columns.iter().map(|c| t.columns.iter().position(|n| n.eq_ignore_ascii_case(&c.name))).collect();
    t.rows
        .iter()
        .map(|row| {
            def.columns
                .iter()
                .zip(&positions)
                .map(|(c, p)| match p {
                    None => Ok(HostValue::Null),
                    Some(i) => input_value(&c.ty, &row[*i]).map_err(|e| FixtureError(format!("{}.{}: {e}", t.name, c.name))),
                })
                .collect()
        })
        .collect()
}

/// PostgreSQL input of one fixture value for a column type (see the module header for what is refused).
pub fn input_value(ty: &PgType, v: &Value) -> Result<HostValue, FixtureError> {
    if v.is_null() {
        return Ok(HostValue::Null);
    }
    if v.is_f64() {
        return Err(FixtureError(format!("float {v} refused; exact values must be strings or integers")));
    }
    let s = match v {
        Value::String(s) => s.clone(),
        Value::Number(n) => n.to_string(),
        Value::Bool(b) => b.to_string(),
        other => return Err(FixtureError(format!("unsupported JSON value {other}"))),
    };
    let refused = |reason: String| Err(FixtureError(reason));
    Ok(match ty {
        PgType::Bool => match s.as_str() {
            "true" | "t" => HostValue::Bool(true),
            "false" | "f" => HostValue::Bool(false),
            _ => return refused(format!("{s:?} is not a boolean literal")),
        },
        PgType::Int4 | PgType::Int8 => HostValue::Int(s.trim().parse::<i64>().map_err(|e| FixtureError(format!("{s:?}: {e}")))?),
        PgType::Numeric { typmod: Some((_, scale)) } => numeric_input(s.trim(), *scale as u32)?,
        PgType::Numeric { typmod: None } => return refused("unconstrained numeric column".into()),
        PgType::Date => {
            let days = parse_date(s.trim()).ok_or_else(|| FixtureError(format!("{s:?} is not YYYY-MM-DD")))?;
            HostValue::Date(i32::try_from(days).map_err(|e| FixtureError(e.to_string()))?)
        }
        PgType::Timestamp => HostValue::Ts(parse_timestamp(s.trim()).ok_or_else(|| FixtureError(format!("{s:?} is not YYYY-MM-DD HH:MM:SS[.f]")))?),
        PgType::Text | PgType::Varchar { .. } => HostValue::Text(s.into_bytes()),
        PgType::Bpchar { .. } => HostValue::Text(s.trim_end_matches(' ').as_bytes().to_vec()),
    })
}

/// `[+-]digits[.digits]` at the column scale: fewer fractional digits are padded (exact), more are refused
/// (PostgreSQL would round on input; the fixture should state the stored value).
fn numeric_input(s: &str, scale: u32) -> Result<HostValue, FixtureError> {
    let (negative, body) = match s.strip_prefix('-') {
        Some(b) => (true, b),
        None => (false, s.strip_prefix('+').unwrap_or(s)),
    };
    let (int, frac) = body.split_once('.').unwrap_or((body, ""));
    if int.is_empty() && frac.is_empty() || !int.bytes().chain(frac.bytes()).all(|b| b.is_ascii_digit()) {
        return Err(FixtureError(format!("{s:?} is not a plain decimal")));
    }
    if frac.len() > scale as usize {
        return Err(FixtureError(format!("{s:?} has more than {scale} fractional digits (input rounding is not modelled)")));
    }
    let digits = format!("{int}{frac}{}", "0".repeat(scale as usize - frac.len()));
    let magnitude: i128 = digits.parse().map_err(|e| FixtureError(format!("{s:?}: {e}")))?;
    Ok(HostValue::Num { coeff: if negative { -magnitude } else { magnitude }, scale })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn numeric_and_text_input() {
        let t = PgType::Numeric { typmod: Some((15, 2)) };
        assert_eq!(input_value(&t, &Value::from("10.5")).unwrap(), HostValue::Num { coeff: 1050, scale: 2 });
        assert_eq!(input_value(&t, &Value::from("-0.07")).unwrap(), HostValue::Num { coeff: -7, scale: 2 });
        assert_eq!(input_value(&t, &Value::from(3)).unwrap(), HostValue::Num { coeff: 300, scale: 2 });
        assert!(input_value(&t, &Value::from("1.005")).is_err());
        assert_eq!(input_value(&PgType::Bpchar { n: Some(4) }, &Value::from("ab  ")).unwrap(), HostValue::Text(b"ab".to_vec()));
        assert_eq!(input_value(&PgType::Date, &Value::from("2000-01-02")).unwrap(), HostValue::Date(1));
    }

    #[test]
    fn repository_paths() {
        assert!(repository_root().join("src/gendb/fixtures/tpch-spec/schema.sql").is_file());
        assert!(fixtures_dir().join("pg_reference/tpch_tiny.json").is_file());
        assert!(postgres_harness().is_file());
    }
}
