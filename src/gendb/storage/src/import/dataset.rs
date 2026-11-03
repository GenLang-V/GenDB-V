//! Declared datasets: tables, their typed columns and original-format locations, and the version of each table's
//! source files recorded at preparation. The declaration is the importer's authority: every file must have exactly the
//! declared Arrow schema; nothing is inferred from the files.

use super::error::{ImportError, Result};
use arrow::datatypes::{DataType, Field, Schema, SchemaRef};
use gendb_artifacts::{ColType, ColumnSpec};
use serde::{Deserialize, Serialize};
use std::{collections::BTreeSet, os::unix::fs::MetadataExt, path::PathBuf, sync::Arc};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum DataFormat {
    Parquet,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TableSpec {
    pub name: String,
    /// Declared columns; a column's ordinal is its position here.
    pub fields: Vec<ColumnSpec>,
    /// Source files in row order: the table's rows are the files' rows in this order.
    pub locations: Vec<PathBuf>,
    pub format: DataFormat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DatasetSpec {
    pub tables: Vec<TableSpec>,
}

impl DatasetSpec {
    pub fn table(&self, name: &str) -> Option<&TableSpec> {
        self.tables.iter().find(|t| t.name == name)
    }

    /// The same declaration with every existing location made canonical. Missing files keep their path, so a
    /// declaration of absent files still compares equal to a saved one and fails only when a file must be read.
    pub fn with_canonical_locations(mut self) -> Result<Self> {
        for location in self.tables.iter_mut().flat_map(|t| t.locations.iter_mut()) {
            if location.exists() {
                *location = location.canonicalize().map_err(ImportError::file(location.as_path()))?;
            }
        }
        Ok(self)
    }

    /// Unique non-empty table and column names, importable column types, and at least one distinct file per table.
    pub fn validate(&self) -> Result<()> {
        let mut names = BTreeSet::new();
        for table in &self.tables {
            if table.name.is_empty() || !names.insert(&table.name) || table.fields.is_empty() {
                return Err(ImportError::declaration(
                    &table.name,
                    "empty or duplicate table name/schema",
                ));
            }
            let mut fields = BTreeSet::new();
            for field in &table.fields {
                if field.name.is_empty() || !fields.insert(&field.name) {
                    return Err(ImportError::declaration(&table.name, "empty or duplicate field name"));
                }
                if arrow_type(field.ty).is_none() {
                    return Err(ImportError::declaration(
                        &table.name,
                        format!("unsupported column type {:?}", field.ty),
                    ));
                }
            }
            if table.locations.is_empty() {
                return Err(ImportError::declaration(
                    &table.name,
                    "import requires explicit Parquet files",
                ));
            }
            if table.locations.iter().collect::<BTreeSet<_>>().len() != table.locations.len() {
                return Err(ImportError::declaration(&table.name, "duplicate file location"));
            }
        }
        Ok(())
    }

    /// The tables this declaration appends to `base`: `base`'s tables must come first, each declared identically
    /// (name, columns in order with type and nullability, locations in order, format). Empty when the two are equal.
    /// Otherwise the refusal reason names the first base table that is missing or declared differently.
    pub(crate) fn appended_to(&self, base: &DatasetSpec) -> std::result::Result<&[TableSpec], String> {
        for (i, prior) in base.tables.iter().enumerate() {
            match self.tables.get(i) {
                Some(table) if table == prior => {}
                Some(table) if table.name == prior.name => {
                    return Err(format!("table {} is declared differently (columns, locations or format)", prior.name));
                }
                _ => return Err(format!("table {} is not declared at position {i}", prior.name)),
            }
        }
        Ok(&self.tables[base.tables.len()..])
    }
}

/// Arrow type of a declared column as stored in original files, or `None` for a decimal outside precision 1..=38 with
/// scale 0..=precision. `Binary` is importable as a declared column; the canonical native form refuses it only if it
/// is demanded.
pub(crate) fn arrow_type(ty: ColType) -> Option<DataType> {
    Some(match ty {
        ColType::Decimal { p, s } if (1..=38).contains(&p) && s >= 0 && s <= p as i8 => DataType::Decimal128(p, s),
        ColType::Decimal { .. } => return None,
        ColType::Date32 => DataType::Date32,
        ColType::Bool => DataType::Boolean,
        ColType::I32 => DataType::Int32,
        ColType::I64 => DataType::Int64,
        ColType::U32 => DataType::UInt32,
        ColType::U64 => DataType::UInt64,
        ColType::Utf8 => DataType::Utf8,
        ColType::Binary => DataType::Binary,
    })
}

/// Declared column type of an Arrow type (the inverse of [`arrow_type`]).
pub(crate) fn column_type(ty: &DataType) -> Option<ColType> {
    Some(match ty {
        DataType::Decimal128(p, s) if (1..=38).contains(p) && *s >= 0 && *s <= *p as i8 => {
            ColType::Decimal { p: *p, s: *s }
        }
        DataType::Date32 => ColType::Date32,
        DataType::Boolean => ColType::Bool,
        DataType::Int32 => ColType::I32,
        DataType::Int64 => ColType::I64,
        DataType::UInt32 => ColType::U32,
        DataType::UInt64 => ColType::U64,
        DataType::Utf8 => ColType::Utf8,
        DataType::Binary => ColType::Binary,
        _ => return None,
    })
}

/// The Arrow schema a source file of these declared columns must have.
pub(crate) fn declared_schema(table: &str, fields: &[ColumnSpec]) -> Result<SchemaRef> {
    let fields = fields
        .iter()
        .map(|f| {
            let ty = arrow_type(f.ty)
                .ok_or_else(|| ImportError::declaration(table, format!("unsupported column type {:?}", f.ty)))?;
            Ok(Field::new(&f.name, ty, f.nullable))
        })
        .collect::<Result<Vec<_>>>()?;
    Ok(Arc::new(Schema::new(fields)))
}

/// The version of one table's source files, recorded at preparation.
///
/// Current preparations record a lifecycle stamp: the JSON list of `(path, device, inode, size, mtime, mtime_nsec,
/// ctime, ctime_nsec)` of every file. It is metadata, not a content check: equal stamps are trusted to mean unchanged
/// files, and no value is read or hashed. Captures prepared before stamps existed carry a saved content label instead;
/// it is read as saved and never recomputed, so such a source cannot be checked for currency.
///
/// Admitted assets are keyed by this string, so its format is fixed.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceVersion {
    pub table: String,
    pub locations: Vec<PathBuf>,
    #[serde(rename = "content_identity")]
    pub version: String,
}

impl SourceVersion {
    /// Stamp the current files of `table`.
    pub fn stamp(table: &TableSpec) -> Result<Self> {
        Ok(Self {
            table: table.name.clone(),
            locations: table.locations.clone(),
            version: lifecycle_stamp(table)?,
        })
    }

    /// Whether this version is a lifecycle stamp (checkable against the current files) rather than a saved label.
    pub fn is_lifecycle_stamp(&self) -> bool {
        self.version.starts_with('[')
    }
}

fn lifecycle_stamp(table: &TableSpec) -> Result<String> {
    let stamps = table
        .locations
        .iter()
        .map(|path| {
            let m = std::fs::metadata(path).map_err(ImportError::file(path.as_path()))?;
            Ok((
                path,
                m.dev(),
                m.ino(),
                m.len(),
                m.mtime(),
                m.mtime_nsec(),
                m.ctime(),
                m.ctime_nsec(),
            ))
        })
        .collect::<Result<Vec<_>>>()?;
    serde_json::to_string(&stamps).map_err(|e| ImportError::declaration(&table.name, e.to_string()))
}

/// Refuse when any table's recorded version is a lifecycle stamp that differs from its current files. Saved labels
/// cannot be checked; when any table carries one, nothing is checked (a legacy capture is trusted as saved).
pub(crate) fn check_current(dataset: &DatasetSpec, versions: &[SourceVersion]) -> Result<()> {
    if !versions
        .iter()
        .all(|v| v.locations.is_empty() || v.is_lifecycle_stamp())
    {
        return Ok(());
    }
    for table in &dataset.tables {
        let recorded = versions
            .iter()
            .find(|v| v.table == table.name)
            .ok_or_else(|| ImportError::declaration(&table.name, "no recorded source version"))?;
        if lifecycle_stamp(table)? != recorded.version {
            return Err(ImportError::SourceChanged {
                table: table.name.clone(),
            });
        }
    }
    Ok(())
}

/// Whether every table has a recorded lifecycle stamp equal to its current files (automatic reuse requires this;
/// saved labels never qualify).
pub(crate) fn all_current(dataset: &DatasetSpec, versions: &[SourceVersion]) -> bool {
    dataset.tables.iter().all(|table| {
        versions.iter().find(|v| v.table == table.name).is_some_and(|recorded| {
            recorded.is_lifecycle_stamp() && lifecycle_stamp(table).is_ok_and(|current| current == recorded.version)
        })
    })
}
