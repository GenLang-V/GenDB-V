//! Generated tiny cases: small source databases on which a candidate's answers are compared with the verified SQLSpec
//! evaluator of each admission binding's fully fixed instance (LIMIT/OFFSET cleared; the comparison applies them
//! tie-aware). Tests, never proof.
//!
//! Generic over the statement: everything comes from the instance's AST, its column layout
//! (`gendb_frontend::columns::analyze`) and the source declaration (the delivered columns).
//!
//! Model ([`model`]). One row per FROM occurrence of a delivered table (including occurrences inside subqueries) is a
//! *tuple*; a tuple becomes a database by giving every table the distinct rows of its occurrences. Field slots are
//! `(occurrence, delivered column)`. Two slots compared for equality anywhere in the AST (`Col = Col`, through
//! integer/numeric casts, at any depth: join and correlation keys) share one equality class and change together.
//!
//! Search for a qualifying tuple (its result differs from the empty-input result): a deterministic pseudo-random
//! search over per-slot candidates, then single-field refinement. Candidates of a slot ([`constants`]): the constants
//! its column is compared with anywhere in the AST (literals and fixed parameters of the other operand, dates shifted
//! by interval literals, each +-1 unit), the literal probes of its type, domain extremes and small values. When no
//! qualifying tuple is found the case set says so (`qualifying_tuple_found: false`); that is never a refusal or claim.
//! Probes and predicate boundaries use the found tuple as is. Its shared-row form (the occurrences of each table holding
//! one row wherever it still qualifies) builds the value cases and the few companion rows of the join and size cases,
//! which enlarge one table or add rows on top: the verified evaluator's work on a case is the product of its table
//! sizes, rerun per outer row for a scalar subquery.
//!
//! Cases ([`generate`]): empty input; no qualifying row; one row; predicate boundaries (bisection per numeric/date field
//! between probes); more groups than `MAX_WORKERS`; UTF-8 group keys; signed values that cancel; AVG display scales;
//! schema-extreme values; ties at the OFFSET/LIMIT boundary; row counts around every worker count; NULL in each nullable
//! delivered column (beside the same rows without NULL) and in all of them at once; with several occurrences also each
//! table empty in turn, duplicate matches on every side and rows without a match.
//!
//! One database per case ([`complete_database`]): every schema table and column; the evaluator labels it, the
//! candidate's inline input is its projection onto the delivered columns ([`inline_columns`]) and a storage's builder
//! input its projection onto the stored columns ([`storage_case_input`]). Without declared integrity constraints the
//! columns and tables the statement does not deliver hold defaults and no rows; with them a small heuristic completes
//! the database, and only cases the verified evaluator certifies are run ([`certification`]).

mod complete;
mod constants;
mod generate;
mod model;
mod storage_input;

pub use complete::complete_database;
pub use model::Model;
pub use storage_input::{StorageCaseInput, storage_case_input};

use crate::admission::AdmissionError;
use gendb_frontend::ast::PgType;
use gendb_frontend::columns::{SourceDeclaration, SourceType};
use gendb_runtime::worker::{InlineColumn, InlineElem};
use gendb_sqlspec::codec::{HostTables, HostValue, RunOutcome};
use serde_json::{Value, json};

/// Days from 1970-01-01 (Arrow Date32, the ABI's date unit) to 2000-01-01 (the SQLSpec/PostgreSQL date epoch).
pub(crate) const DAYS_1970_TO_2000: i32 = 10957;

/// One field value in its ABI unit: numeric coefficient, Date32 day or integer; or text; or SQL NULL (only in a
/// nullable column).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CaseValue {
    Num(i128),
    Text(String),
    Null,
}

/// Rows of every delivered source table: `tables[j]` holds declaration table `j`'s rows, its delivered columns in order.
pub type CaseTables = Vec<Vec<Vec<CaseValue>>>;

/// One generated case.
#[derive(Clone, Debug)]
pub struct Case {
    pub name: String,
    pub tables: CaseTables,
}

impl Case {
    /// Row count of every delivered table.
    pub fn rows(&self) -> Vec<usize> {
        self.tables.iter().map(Vec::len).collect()
    }
}

fn host_value(ty: SourceType, value: &CaseValue) -> HostValue {
    match (ty, value) {
        (_, CaseValue::Null) => HostValue::Null,
        (SourceType::Decimal { s, .. }, CaseValue::Num(c)) => HostValue::Num { coeff: *c, scale: s },
        (SourceType::Date32, CaseValue::Num(d)) => HostValue::Date((*d - DAYS_1970_TO_2000 as i128) as i32),
        (SourceType::Int32 | SourceType::Int64, CaseValue::Num(i)) => HostValue::Int(*i as i64),
        (_, CaseValue::Text(t)) => HostValue::Text(t.as_bytes().to_vec()),
        (_, CaseValue::Num(n)) => HostValue::Text(n.to_string().into_bytes()),
    }
}

fn default_value(ty: &PgType) -> HostValue {
    match ty {
        PgType::Bool => HostValue::Bool(false),
        PgType::Int4 | PgType::Int8 => HostValue::Int(0),
        PgType::Numeric { typmod } => HostValue::Num { coeff: 0, scale: typmod.map_or(0, |(_, s)| s as u32) },
        PgType::Date => HostValue::Date(0),
        PgType::Timestamp => HostValue::Ts(0),
        PgType::Text | PgType::Varchar { .. } | PgType::Bpchar { .. } => HostValue::Text(vec![]),
    }
}

/// Inline ABI columns of a case: every delivered column of its complete database `database`, table by table, in
/// declaration order (the delivered values the case holds; a nullable column with its validity).
pub fn inline_columns(declaration: &SourceDeclaration, database: &HostTables) -> Result<Vec<InlineColumn>, AdmissionError> {
    let mut columns = vec![];
    for t in &declaration.tables {
        for c in &t.columns {
            let column = inline_column(database, t.table_id, c.ordinal, c.ty, c.nullable)
                .map_err(|e| AdmissionError::tool(format!("tiny-case input of {}.{}: {e}", t.name, c.name)))?;
            columns.push(column);
        }
    }
    Ok(columns)
}

/// Column `ordinal` of table `table_id` of a complete database as the inline column of the ABI type `ty`, row by row:
/// for a `nullable` column a NULL row is the placeholder value with validity 0; `Err` when a value has no such
/// representation (a NULL in a NOT NULL column, or another type).
pub(crate) fn inline_column(database: &HostTables, table_id: usize, ordinal: usize, ty: SourceType, nullable: bool) -> Result<InlineColumn, String> {
    let rows = database.get(table_id).ok_or_else(|| format!("table {table_id} is not in the case's database"))?;
    let mut values = Vec::with_capacity(rows.len());
    let mut validity = Vec::with_capacity(rows.len());
    for row in rows {
        let value = row.get(ordinal).ok_or_else(|| format!("column {ordinal} is not in the case's database"))?;
        if nullable && *value == HostValue::Null {
            values.push(if ty == SourceType::Utf8 { String::new() } else { "0".into() });
            validity.push(0);
        } else {
            values.push(abi_text(ty, value).ok_or_else(|| format!("value {value:?} has no {ty:?} representation"))?);
            validity.push(1);
        }
    }
    Ok(InlineColumn { elem: inline_elem(ty), values, validity: nullable.then_some(validity) })
}

/// A value as inline column text of the ABI type `ty`: the number in its ABI unit, or the text itself.
fn abi_text(ty: SourceType, value: &HostValue) -> Option<String> {
    match (ty, value) {
        (SourceType::Decimal { s, .. }, HostValue::Num { coeff, scale }) if *scale == s => Some(coeff.to_string()),
        (SourceType::Date32, HostValue::Date(d)) => Some((*d as i64 + DAYS_1970_TO_2000 as i64).to_string()),
        (SourceType::Int32 | SourceType::Int64, HostValue::Int(i)) => Some(i.to_string()),
        (SourceType::Utf8, HostValue::Text(t)) => String::from_utf8(t.clone()).ok(),
        _ => None,
    }
}

/// The inline column element of an ABI source type.
fn inline_elem(ty: SourceType) -> InlineElem {
    match ty {
        SourceType::Decimal { .. } => InlineElem::I128,
        SourceType::Date32 | SourceType::Int32 => InlineElem::I32,
        SourceType::Int64 => InlineElem::I64,
        SourceType::Utf8 => InlineElem::Utf8,
    }
}

/// Why a case of a statement with declared integrity constraints is not run.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Uncertified {
    /// The verified evaluator proved that its complete database violates a declared constraint.
    OutsideDeclaredConstraints,
    /// The heuristic completion left a column's declared domain (the evaluator's `BadDatabase`: `db_wf` fails).
    CompletionOutsideDomain,
    /// The verified evaluator returned only Capacity, which may come from its constraint check: not certified, and not
    /// a proved violation either.
    ConstraintsUndecided,
}

impl Uncertified {
    pub fn name(self) -> &'static str {
        match self {
            Self::OutsideDeclaredConstraints => "outside_declared_constraints",
            Self::CompletionOutsideDomain => "completion_outside_domain",
            Self::ConstraintsUndecided => "constraints_undecided",
        }
    }

    pub fn meaning(self) -> &'static str {
        match self {
            Self::OutsideDeclaredConstraints => {
                "the verified evaluator proved that the case's complete database violates a declared constraint (ConstraintViolation): outside the claim's domain, where verified code guarantees nothing (not even termination); not run"
            }
            Self::CompletionOutsideDomain => {
                "the heuristic completion gave a cell a value outside its column's declared domain (the verified evaluator's BadDatabase: db_wf fails): a lost case of the heuristic, not a proved violation; not run"
            }
            Self::ConstraintsUndecided => {
                "the verified evaluator returned Capacity at every binding, which may come from checking the constraints (fits_constraints): neither certified nor a proved violation; not run"
            }
        }
    }
}

/// Whether the verified evaluator's labels of one case (`labels[binding]`) certify that its complete database
/// satisfies the declared constraints: `Done` at some binding (rows or an SQL error) implies `db_wf` and
/// `constraints_hold` (`abi_run_meets`); `ConstraintViolation` proves a violation; `BadDatabase` shows the completion
/// left a column's domain; Capacity alone decides nothing.
pub fn certification(labels: &[RunOutcome]) -> Result<(), Uncertified> {
    if labels.iter().any(|l| matches!(l, RunOutcome::Rows(_) | RunOutcome::SqlError(_))) {
        Ok(())
    } else if labels.iter().any(|l| matches!(l, RunOutcome::ConstraintViolation)) {
        Err(Uncertified::OutsideDeclaredConstraints)
    } else if labels.iter().any(|l| matches!(l, RunOutcome::BadDatabase)) {
        Err(Uncertified::CompletionOutsideDomain)
    } else {
        Err(Uncertified::ConstraintsUndecided)
    }
}

/// The verified evaluator's label of a run case, in author-facing words: what a candidate must answer. Every run case
/// of a statement with declared constraints is certified at some binding, so Capacity at a binding means its database
/// is outside the capacity domain there, exactly as without declarations.
pub fn label_record(label: &RunOutcome) -> Value {
    match label {
        RunOutcome::Rows(r) => json!({"label":"in_capacity_domain_value","rows":r.len(),"required":"Ok rows allowed by ordered_ok (exact comparison)"}),
        RunOutcome::SqlError(k) => json!({"label":"in_capacity_domain_sql_error","error":k.name(),"required":format!("SqlError {} exactly", k.name())}),
        RunOutcome::Capacity => json!({"label":"outside_capacity_domain","required":"any allowed outcome; the verified evaluator proves !capacity_domain; no exact reference outside the domain (rows or an error are status-only)"}),
        RunOutcome::ConstraintViolation => json!({"label":Uncertified::OutsideDeclaredConstraints.name(),"required":"not run: outside the declared constraints"}),
        other => json!({"label":format!("{other:?}")}),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A generated value read back from the complete database is the inline text it always had: the number in its ABI
    /// unit, or the text itself (so default-mode inputs are unchanged).
    #[test]
    fn database_values_project_back_to_their_inline_text() {
        let cases = [
            (SourceType::Decimal { p: 15, s: 2 }, CaseValue::Num(-12345)),
            (SourceType::Date32, CaseValue::Num(DAYS_1970_TO_2000 as i128 + 31)),
            (SourceType::Date32, CaseValue::Num(-719162)),
            (SourceType::Int32, CaseValue::Num(i32::MIN as i128)),
            (SourceType::Int64, CaseValue::Num(i64::MAX as i128)),
            (SourceType::Utf8, CaseValue::Text("\u{e9}A ".into())),
        ];
        for (ty, value) in cases {
            let old = match &value {
                CaseValue::Num(n) => n.to_string(),
                CaseValue::Text(t) => t.clone(),
                CaseValue::Null => unreachable!("no NULL among these values"),
            };
            assert_eq!(abi_text(ty, &host_value(ty, &value)), Some(old), "{ty:?}");
        }
        assert_eq!(abi_text(SourceType::Int64, &HostValue::Null), None);
        assert_eq!(abi_text(SourceType::Decimal { p: 15, s: 2 }, &HostValue::Num { coeff: 1, scale: 3 }), None);
    }

    /// A nullable column's inline input is its values with a placeholder under NULL and its validity; a NOT NULL column
    /// has no validity and refuses a NULL.
    #[test]
    fn nullable_columns_project_with_their_validity() {
        let database: HostTables = vec![vec![vec![HostValue::Int(7), HostValue::Text(b"a".to_vec())], vec![HostValue::Null, HostValue::Null]]];
        let ints = inline_column(&database, 0, 0, SourceType::Int32, true).unwrap();
        assert_eq!((ints.values, ints.validity), (vec!["7".to_string(), "0".to_string()], Some(vec![1, 0])));
        let texts = inline_column(&database, 0, 1, SourceType::Utf8, true).unwrap();
        assert_eq!((texts.values, texts.validity), (vec!["a".to_string(), String::new()], Some(vec![1, 0])));
        assert!(inline_column(&database, 0, 0, SourceType::Int32, false).unwrap_err().contains("Null"));
        let not_null = inline_column(&vec![vec![vec![HostValue::Int(1)]]], 0, 0, SourceType::Int64, false).unwrap();
        assert_eq!(not_null.validity, None);
        assert_eq!(host_value(SourceType::Utf8, &CaseValue::Null), HostValue::Null);
    }
}
