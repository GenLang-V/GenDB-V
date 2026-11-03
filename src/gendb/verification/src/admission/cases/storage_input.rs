//! The builder input of one storage for one tiny case: the case's complete database (the one the verified evaluator
//! labels, [`super::complete_database`]) projected onto the columns the storage stores, so the stored relations are
//! those of the labelled database and the query's answer can be compared with the label: every stored column takes
//! that database's values, row by row (same rows, same order, same multiplicity).
//!
//! Where the statement delivers the column, those are the case's values. Elsewhere they are the database's completion:
//! without declared integrity constraints a stored column the statement does not deliver holds its type's default
//! (numeric 0 at its scale, integer 0, date 2000-01-01, empty text) in every row and a stored table the statement does
//! not read has no rows; with declared constraints those cells and tables hold the heuristic completion the verified
//! evaluator certified (keys distinct, referenced parent rows, CHECK-accepted values). Either way they are synthetic
//! test values, not data and not proof; the record names them.
//!
//! Every value is a value of a database the verified evaluator accepted as well formed (the preflight refuses a case
//! whose database it does not accept), so it lies in its column's declared domain; the fixed storage entry decides that
//! domain again before the builder runs. A stored column whose declared type differs from the schema's (another schema)
//! has no case value: a named `tiny_input_unavailable` tool failure, never the author's.

use super::inline_column;
use crate::admission::AdmissionError;
use crate::obligations::{DeclaredSource, DeclaredType};
use gendb_frontend::columns::{SourceDeclaration, SourceType};
use gendb_runtime::worker::WorkerInput;
use gendb_sqlspec::codec::HostTables;

/// The builder input of one storage for one tiny case.
#[derive(Clone, Debug)]
pub struct StorageCaseInput {
    /// Inline columns in the storage's ABI order (`WorkerInput::Inline`).
    pub input: WorkerInput,
    /// `table.column` of every stored column the statement does not deliver (its values are the database's completion).
    pub synthetic_columns: Vec<String>,
    /// Stored tables the statement does not read (their rows, if any, are the database's completion).
    pub undelivered_tables: Vec<String>,
    /// Row count of every stored table, in declaration order.
    pub rows: Vec<usize>,
}

impl StorageCaseInput {
    /// What this input is, for records: which columns and tables are test fixtures rather than the case's values.
    pub fn record(&self) -> serde_json::Value {
        serde_json::json!({"rows":self.rows,"synthetic_columns":self.synthetic_columns,"undelivered_tables":self.undelivered_tables,
            "meaning":"the tiny case's complete database projected onto the stored columns; synthetic columns and undelivered tables hold its completion (without declared constraints one default value per column and no rows; with them the certified heuristic completion): test fixtures, not data and not proof"})
    }
}

/// The builder input of the storage `declaration` for the tiny case whose complete database is `database`, a case of
/// the statement whose delivered columns are `statement_source` (see the module documentation).
pub fn storage_case_input(declaration: &DeclaredSource, statement_source: &SourceDeclaration, database: &HostTables) -> Result<StorageCaseInput, AdmissionError> {
    let mut columns = Vec::new();
    let mut synthetic_columns = Vec::new();
    let mut undelivered_tables = Vec::new();
    let mut rows = Vec::new();
    for table in &declaration.tables {
        let delivered = statement_source.tables.iter().find(|t| t.table_id == table.table_id);
        if delivered.is_none() {
            undelivered_tables.push(table.name.clone());
        }
        rows.push(database.get(table.table_id).map_or(0, Vec::len));
        for column in &table.columns {
            let ty = source_type(column.ty);
            match delivered.and_then(|t| t.columns.iter().find(|c| c.ordinal == column.ordinal)) {
                Some(c) if c.ty != ty => {
                    return Err(AdmissionError::tool(format!(
                        "tiny_input_unavailable: stored column {}.{}: the statement delivers it as {:?}, the storage declares {ty:?}; no tiny-case input can be given to this storage (the candidate is not implicated)",
                        table.name, column.name, c.ty
                    )));
                }
                Some(_) => {}
                None if delivered.is_some() => synthetic_columns.push(format!("{}.{}", table.name, column.name)),
                None => {}
            }
            let inline = inline_column(database, table.table_id, column.ordinal, ty, column.nullable).map_err(|e| {
                AdmissionError::tool(format!(
                    "tiny_input_unavailable: stored column {}.{}: {e}; no tiny-case input can be given to this storage (the candidate is not implicated)",
                    table.name, column.name
                ))
            })?;
            columns.push(inline);
        }
    }
    Ok(StorageCaseInput { input: WorkerInput::Inline { columns }, synthetic_columns, undelivered_tables, rows })
}

/// The ABI representation of a declared column type.
pub(super) fn source_type(ty: DeclaredType) -> SourceType {
    match ty {
        DeclaredType::Int4 => SourceType::Int32,
        DeclaredType::Int8 => SourceType::Int64,
        DeclaredType::Numeric { precision, scale } => SourceType::Decimal { p: precision, s: scale },
        DeclaredType::Date => SourceType::Date32,
        DeclaredType::Text | DeclaredType::Varchar { .. } | DeclaredType::Bpchar { .. } => SourceType::Utf8,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::admission::cases::{CaseValue, complete_database, inline_columns};
    use crate::obligations::{DeclaredColumn, DeclaredTable};
    use gendb_frontend::ast::{ColumnDef, ConstraintDef, ConstraintTiming, PgType, TableDef};
    use gendb_frontend::columns::{SourceColumn, SourceTable};
    use gendb_runtime::worker::InlineElem;

    fn declared(ordinal: usize, name: &str, ty: DeclaredType, row_count_only: bool) -> DeclaredColumn {
        DeclaredColumn { ordinal, name: name.into(), ty, row_count_only, nullable: false }
    }

    /// t (a int4, b numeric(10,2), c date, d varchar(4)) and u (k char(2)), with the given constraints on t.
    fn schema(constraints: Vec<ConstraintDef>) -> Vec<TableDef> {
        let column = |name: &str, ty| ColumnDef { name: name.into(), ty, nullable: false };
        vec![
            TableDef {
                name: "t".into(),
                columns: vec![
                    column("a", PgType::Int4),
                    column("b", PgType::Numeric { typmod: Some((10, 2)) }),
                    column("c", PgType::Date),
                    column("d", PgType::Varchar { max_chars: Some(4) }),
                ],
                constraints,
            },
            TableDef { name: "u".into(), columns: vec![column("k", PgType::Varchar { max_chars: Some(4) })], constraints: vec![] },
        ]
    }

    /// The statement delivers t.a and t.c (table 0 only).
    fn statement() -> SourceDeclaration {
        let column = |ordinal, name: &str, ty| SourceColumn { ordinal, name: name.into(), ty, row_count_only: false, nullable: false };
        SourceDeclaration {
            tables: vec![SourceTable {
                index: 0,
                table_id: 0,
                name: "t".into(),
                columns: vec![column(0, "a", SourceType::Int32), column(2, "c", SourceType::Date32)],
            }],
        }
    }

    /// The complete database of the case t(a, c) = (7, 2000-01-01), (-1, 2000-02-13), (7, 2000-01-01).
    fn database(constraints: Vec<ConstraintDef>) -> HostTables {
        let row = |a: i128, c: i128| vec![CaseValue::Num(a), CaseValue::Num(c)];
        complete_database(&schema(constraints), &statement(), &vec![vec![row(7, 10957), row(-1, 11000), row(7, 10957)]])
    }

    fn every_column() -> DeclaredSource {
        DeclaredSource {
            tables: vec![
                DeclaredTable {
                    table_id: 0,
                    name: "t".into(),
                    columns: vec![
                        declared(0, "a", DeclaredType::Int4, false),
                        declared(1, "b", DeclaredType::Numeric { precision: 10, scale: 2 }, false),
                        declared(2, "c", DeclaredType::Date, false),
                        declared(3, "d", DeclaredType::Varchar { max_chars: 4 }, false),
                    ],
                },
                DeclaredTable { table_id: 1, name: "u".into(), columns: vec![declared(0, "k", DeclaredType::Varchar { max_chars: 4 }, true)] },
            ],
        }
    }

    fn columns(input: &StorageCaseInput) -> Vec<(InlineElem, Vec<String>)> {
        let WorkerInput::Inline { columns } = &input.input else { panic!("inline input expected") };
        columns.iter().map(|c| (c.elem, c.values.clone())).collect()
    }

    fn text(values: &[&str]) -> Vec<String> {
        values.iter().map(|v| v.to_string()).collect()
    }

    /// Without declared constraints: delivered columns keep the case rows, other stored columns hold the type's default
    /// in every row (the values the inputs always had), and a stored table the statement does not read is empty.
    #[test]
    fn delivered_columns_keep_the_case_rows_and_others_are_defaults_or_empty() {
        let input = storage_case_input(&every_column(), &statement(), &database(vec![])).unwrap();
        assert_eq!(
            columns(&input),
            [
                (InlineElem::I32, text(&["7", "-1", "7"])),
                (InlineElem::I128, text(&["0", "0", "0"])),
                (InlineElem::I32, text(&["10957", "11000", "10957"])),
                (InlineElem::Utf8, text(&["", "", ""])),
                // The carrier of a table the statement does not read: no rows.
                (InlineElem::Utf8, vec![]),
            ]
        );
        assert_eq!((input.synthetic_columns, input.undelivered_tables, input.rows), (vec!["t.b".to_string(), "t.d".into()], vec!["u".to_string()], vec![3, 0]));
    }

    /// With declared constraints the storage input and the candidate's inline input are projections of the same
    /// complete database: t.b (its key) is distinct per row, t.d references u.k, so u holds the referenced row.
    #[test]
    fn constrained_inputs_are_projections_of_one_complete_database() {
        let timing = ConstraintTiming { deferrable: false, initially_deferred: false };
        let key = ConstraintDef::Key { name: None, primary: true, columns: vec![1], nulls_distinct: true, timing: timing.clone() };
        let reference = ConstraintDef::ForeignKey {
            name: None,
            columns: vec![3],
            table: 1,
            ref_columns: vec![0],
            match_full: false,
            on_delete: "no_action".into(),
            on_update: "no_action".into(),
            timing,
        };
        let mut constrained = schema(vec![key, reference]);
        constrained[1].constraints = vec![ConstraintDef::Key { name: None, primary: true, columns: vec![0], nulls_distinct: true, timing: ConstraintTiming { deferrable: false, initially_deferred: false } }];
        let row = |a: i128, c: i128| vec![CaseValue::Num(a), CaseValue::Num(c)];
        let database = complete_database(&constrained, &statement(), &vec![vec![row(7, 10957), row(-1, 11000), row(7, 10957)]]);
        let input = storage_case_input(&every_column(), &statement(), &database).unwrap();
        assert_eq!(
            columns(&input),
            [
                (InlineElem::I32, text(&["7", "-1", "7"])),
                (InlineElem::I128, text(&["1", "2", "3"])),
                (InlineElem::I32, text(&["10957", "11000", "10957"])),
                (InlineElem::Utf8, text(&["", "", ""])),
                (InlineElem::Utf8, text(&[""])),
            ]
        );
        assert_eq!(input.rows, [3, 1]);
        let inline: Vec<Vec<String>> = inline_columns(&statement(), &database).unwrap().into_iter().map(|c| c.values).collect();
        assert_eq!(inline, [columns(&input)[0].1.clone(), columns(&input)[2].1.clone()]);
    }

    #[test]
    fn a_carrier_of_a_read_table_takes_the_case_row_count() {
        let storage = DeclaredSource {
            tables: vec![DeclaredTable { table_id: 0, name: "t".into(), columns: vec![declared(1, "b", DeclaredType::Numeric { precision: 10, scale: 2 }, true)] }],
        };
        let input = storage_case_input(&storage, &statement(), &database(vec![])).unwrap();
        assert_eq!(columns(&input), [(InlineElem::I128, vec!["0".to_string(); 3])]);
        assert_eq!(input.synthetic_columns, ["t.b"]);
    }

    #[test]
    fn a_type_disagreement_is_a_named_input_refusal() {
        // A storage over another schema that declares t.c an int4 where the statement delivers a date.
        let storage = DeclaredSource { tables: vec![DeclaredTable { table_id: 0, name: "t".into(), columns: vec![declared(2, "c", DeclaredType::Int4, false)] }] };
        let error = storage_case_input(&storage, &statement(), &database(vec![])).unwrap_err();
        assert!(error.message.starts_with("tiny_input_unavailable: stored column t.c") && error.class.name() == "tool_failure", "{error}");
    }
}
