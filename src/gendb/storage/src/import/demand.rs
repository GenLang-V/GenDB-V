//! Column demand: which declared columns a workload needs captured, and the projection that delivers one statement's
//! columns. Demand comes from the typed-AST source declarations of the SQL frontend (`gendb_frontend::columns`), never
//! from an engine plan. Each declared column is bound to the dataset by table name, ordinal, column name, type and
//! nullability; a disagreement is refused rather than delivered under a guessed identity.

use super::dataset::{DatasetSpec, TableSpec};
use super::error::{ImportError, Result};
use gendb_artifacts::ColType;
use gendb_frontend::columns::{SourceColumn, SourceDeclaration, SourceType};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

/// A `(table, strictly increasing declared ordinals)` list in delivery order, as `SourceColumns::project` takes it.
pub type Projection = Vec<(String, Vec<usize>)>;

/// The union of declared columns needed from each source table. A table demanded with no ordinals is captured for its
/// row count only.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ColumnDemand {
    tables: BTreeMap<String, BTreeSet<usize>>,
}

impl ColumnDemand {
    /// Add every column a statement's source declaration delivers, after binding it to `dataset`.
    pub fn add_declaration(&mut self, dataset: &DatasetSpec, declaration: &SourceDeclaration) -> Result<()> {
        for (table, ordinals) in declaration_projection(dataset, declaration)? {
            self.tables.entry(table).or_default().extend(ordinals);
        }
        Ok(())
    }

    /// Add declared columns by ordinal (for callers without a SQL statement, e.g. a workload storage builder).
    pub fn add_columns(&mut self, dataset: &DatasetSpec, table: &str, ordinals: &[usize]) -> Result<()> {
        let declared = declared_table(dataset, table)?;
        if let Some(ordinal) = ordinals.iter().find(|&&o| o >= declared.fields.len()) {
            return Err(ImportError::demand(
                table,
                format!("ordinal {ordinal} is not a declared column"),
            ));
        }
        self.tables.entry(table.to_string()).or_default().extend(ordinals);
        Ok(())
    }

    /// Check that every demanded table and ordinal is declared in `dataset`.
    pub fn check(&self, dataset: &DatasetSpec) -> Result<()> {
        for (table, ordinals) in &self.tables {
            let declared = declared_table(dataset, table)?;
            if ordinals.last().is_some_and(|&o| o >= declared.fields.len()) {
                return Err(ImportError::demand(table, "demanded ordinal is not a declared column"));
            }
        }
        Ok(())
    }

    pub fn is_empty(&self) -> bool {
        self.tables.is_empty()
    }

    /// The demand as a capture projection, tables in name order.
    pub fn projection(&self) -> Projection {
        self.tables
            .iter()
            .map(|(t, o)| (t.clone(), o.iter().copied().collect()))
            .collect()
    }

    /// The demanded columns absent from `captured`: `(table, missing ordinals)`, with no ordinals when the table itself
    /// is absent. Empty when `captured` covers the demand.
    pub fn missing_from(&self, captured: &[(String, Vec<usize>)]) -> Vec<(String, Vec<usize>)> {
        self.tables
            .iter()
            .filter_map(
                |(table, ordinals)| match captured.iter().find(|(name, _)| name == table) {
                    None => Some((table.clone(), ordinals.iter().copied().collect())),
                    Some((_, present)) => {
                        let absent: Vec<usize> = ordinals.iter().copied().filter(|o| !present.contains(o)).collect();
                        (!absent.is_empty()).then(|| (table.clone(), absent))
                    }
                },
            )
            .collect()
    }
}

/// The projection delivering a statement's source declaration: its tables in declaration order, each with its
/// delivered ordinals (row-count carriers included). Every column is bound to `dataset` first.
pub fn declaration_projection(dataset: &DatasetSpec, declaration: &SourceDeclaration) -> Result<Projection> {
    let mut projection = Projection::new();
    for source in &declaration.tables {
        if projection.iter().any(|(name, _)| *name == source.name) {
            return Err(ImportError::demand(&source.name, "table declared twice"));
        }
        let declared = declared_table(dataset, &source.name)?;
        for column in &source.columns {
            bind_column(declared, column)?;
        }
        let ordinals: Vec<usize> = source.columns.iter().map(|c| c.ordinal).collect();
        if ordinals.windows(2).any(|w| w[0] >= w[1]) {
            return Err(ImportError::demand(
                &source.name,
                "delivered ordinals are not strictly increasing",
            ));
        }
        projection.push((source.name.clone(), ordinals));
    }
    Ok(projection)
}

fn declared_table<'a>(dataset: &'a DatasetSpec, table: &str) -> Result<&'a TableSpec> {
    dataset
        .table(table)
        .ok_or_else(|| ImportError::demand(table, "table is not declared in the dataset"))
}

/// The delivered column must be the declared column at its ordinal: same name, same nullability (a nullable column is
/// delivered with its validity), same type.
fn bind_column(table: &TableSpec, column: &SourceColumn) -> Result<()> {
    let refuse = |reason: &str| {
        ImportError::demand(
            &table.name,
            format!("column {} (ordinal {}): {reason}", column.name, column.ordinal),
        )
    };
    let field = table
        .fields
        .get(column.ordinal)
        .ok_or_else(|| refuse("ordinal is not a declared column"))?;
    if field.name != column.name {
        return Err(refuse(&format!(
            "the declared column at this ordinal is {}",
            field.name
        )));
    }
    if field.nullable != column.nullable {
        return Err(refuse(if field.nullable {
            "the declared column is nullable; it is delivered only with its validity"
        } else {
            "the declared column is NOT NULL; it is delivered without validity"
        }));
    }
    if !same_type(field.ty, column.ty) {
        return Err(refuse(&format!(
            "declared type {:?} differs from delivered type {:?}",
            field.ty, column.ty
        )));
    }
    Ok(())
}

fn same_type(declared: ColType, delivered: SourceType) -> bool {
    match (declared, delivered) {
        (ColType::Decimal { p, s }, SourceType::Decimal { p: dp, s: ds }) => {
            u32::from(p) == dp && u32::try_from(s).is_ok_and(|s| s == ds)
        }
        (ColType::Date32, SourceType::Date32)
        | (ColType::I32, SourceType::Int32)
        | (ColType::I64, SourceType::Int64)
        | (ColType::Utf8, SourceType::Utf8) => true,
        _ => false,
    }
}
