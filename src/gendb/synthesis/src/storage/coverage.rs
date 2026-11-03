//! Complete lossless coverage of the workload's data: across the storages a workload keeps, every
//! column of every table of the dataset schema is stored at least once, so the original input could be deleted. Used
//! columns get layouts optimized for execution; the others may be stored only compressed, but they are stored.
//!
//! The check reads declarations only (which columns of which tables each storage stores); it never reads data. A
//! storage's `represents` relation, proved by its builder, is what makes "stored" lossless: the stored relations are the
//! declared columns of the tables, row for row.

use gendb_frontend::ast::TableDef;
use gendb_verification::admission::AdmissionError;
use gendb_verification::obligations::DeclaredSource;
use serde_json::{Value, json};
use std::collections::BTreeSet;

/// Every `(table, column)` of `schema` that none of `storages` stores, in schema order. A table counts as stored only
/// through its stored columns (a row-count carrier stores no column).
pub fn missing_columns<'a>(schema: &'a [TableDef], storages: impl IntoIterator<Item = &'a DeclaredSource>) -> Vec<(&'a str, &'a str)> {
    let stored: BTreeSet<(usize, usize)> = storages
        .into_iter()
        .flat_map(|d| d.tables.iter().flat_map(|t| t.columns.iter().filter(|c| !c.row_count_only).map(move |c| (t.table_id, c.ordinal))))
        .collect();
    schema
        .iter()
        .enumerate()
        .flat_map(|(table_id, table)| table.columns.iter().enumerate().map(move |(ordinal, column)| (table_id, ordinal, table, column)))
        .filter(|(table_id, ordinal, _, _)| !stored.contains(&(*table_id, *ordinal)))
        .map(|(_, _, table, column)| (table.name.as_str(), column.name.as_str()))
        .collect()
}

/// Refuse (`storage_coverage_incomplete`) unless `storages` together store every column of every table of `schema`.
/// `scope` names which storages were counted (in the message).
pub fn check_lossless_coverage<'a>(schema: &'a [TableDef], storages: impl IntoIterator<Item = &'a DeclaredSource>, scope: &str) -> Result<(), AdmissionError> {
    let missing = missing_columns(schema, storages);
    if missing.is_empty() {
        return Ok(());
    }
    let listed: Vec<String> = missing.iter().map(|(t, c)| format!("{t}.{c}")).collect();
    Err(AdmissionError::refusal(format!(
        "storage_coverage_incomplete: {} column(s) are stored by none of {scope}: {}; every column of every table must be stored at least once (columns no query uses may be stored compressed)",
        listed.len(),
        listed.join(", ")
    )))
}

/// The coverage report authors read: per table, its stored and missing columns.
pub fn coverage_report<'a>(schema: &'a [TableDef], storages: impl IntoIterator<Item = &'a DeclaredSource>) -> Value {
    let missing = missing_columns(schema, storages);
    let tables: Vec<Value> = schema
        .iter()
        .map(|t| {
            let absent: Vec<&str> = missing.iter().filter(|(table, _)| *table == t.name).map(|(_, c)| *c).collect();
            json!({"table":t.name,"columns":t.columns.len(),"missing":absent})
        })
        .collect();
    json!({"complete":missing.is_empty(),"missing_columns":missing.len(),"tables":tables,
        "rule":"every column of every table is stored by at least one admitted storage; the workload storage admission refuses otherwise (storage_coverage_incomplete)"})
}

#[cfg(test)]
mod tests {
    use super::*;
    use gendb_frontend::ast::{ColumnDef, PgType};
    use std::collections::BTreeMap;

    #[test]
    fn coverage_counts_stored_columns_across_storages() {
        let column = |name: &str| ColumnDef { name: name.into(), ty: PgType::Int4, nullable: false };
        let schema = vec![
            TableDef { name: "a".into(), columns: vec![column("x"), column("y")], constraints: vec![] },
            TableDef { name: "b".into(), columns: vec![column("z")], constraints: vec![] },
        ];
        let storage = |selection: &[(usize, &[usize])]| {
            let selection: BTreeMap<usize, BTreeSet<usize>> = selection.iter().map(|(t, c)| (*t, c.iter().copied().collect())).collect();
            DeclaredSource::for_storage(&schema, &selection).unwrap()
        };
        let ax = storage(&[(0, &[0])]);
        let rest = storage(&[(0, &[1]), (1, &[])]);
        assert_eq!(missing_columns(&schema, [&ax, &rest]), vec![("b", "z")], "a row-count carrier stores no column");
        assert!(check_lossless_coverage(&schema, [&ax, &rest], "s").unwrap_err().message.starts_with("storage_coverage_incomplete: 1 column(s)"));
        let bz = storage(&[(1, &[0])]);
        assert!(check_lossless_coverage(&schema, [&ax, &rest, &bz], "s").is_ok());
        assert_eq!(coverage_report(&schema, [&ax, &rest, &bz])["complete"], true);
    }
}
