//! The declared source of a statement or of a storage: which columns of which tables the host delivers, in ABI order,
//! with their declared SQL types. It is the only per-query input of `gendb_source.rs` and of the binder, the only
//! per-storage input of a storage declaration (`stores/<name>/declaration.rs`), and it is recorded with every claim
//! (its serialized form is part of the claim record).
//!
//! `gendb_frontend::columns::SourceDeclaration` names the delivered columns by their ABI representation only; the
//! declared SQL type (for example `varchar(8)` rather than Utf8) decides the column domain the entry checks, so it
//! is taken from the statement's schema here, with the declared nullability. A nullable column is delivered as its
//! values plus its validity (one `u8` per row: 0 NULL, otherwise valid); row `i` is SQL NULL exactly when its validity
//! byte is 0, and the value bytes under a NULL row mean nothing. A NOT NULL column has no validity, and its declaration
//! serializes without the field, so every record and generated text of a NOT NULL column is unchanged.

use super::AssemblyError;
use gendb_frontend::ast::{AstDocument, PgType, TableDef};
use gendb_frontend::columns::{declared_columns, SourceDeclaration, SOURCE_DECIMAL_MAX_PRECISION};
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};

/// Declared SQL type of a delivered source column; determines its ABI kind and its SQLSpec value (of a non-NULL row).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum DeclaredType {
    /// `integer`: I32, `Val::Int`.
    Int4,
    /// `bigint`: I64, `Val::Int`.
    Int8,
    /// `numeric(p, s)`, `p <= 38`: I128 coefficient at scale `s`, `Val::Num`.
    Numeric { precision: u32, scale: u32 },
    /// `date`: I32 days since 1970-01-01, `Val::Date(x - 10957)`.
    Date,
    /// `text`: Utf8, `Val::Text`.
    Text,
    /// `varchar(n)`: Utf8, `Val::Text`.
    Varchar { max_chars: u32 },
    /// `char(n)` (canonical, trailing spaces removed): Utf8, `Val::Text`.
    Bpchar { len: u32 },
}

/// Element representation of a delivered column: the `crate::gendb_abi::Column` variant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ColumnKind {
    /// Date32 and Int32 (`&'static [i32]`).
    I32,
    /// Int64 (`&'static [i64]`).
    I64,
    /// Decimal coefficients (`&'static [i128]`).
    I128,
    /// Utf8 offsets + bytes (`TextCol`).
    Utf8,
}

impl ColumnKind {
    /// The variant name in `crate::gendb_abi::Column`.
    pub fn abi_variant(self) -> &'static str {
        match self {
            Self::I32 => "I32",
            Self::I64 => "I64",
            Self::I128 => "I128",
            Self::Utf8 => "Utf8",
        }
    }
}

impl DeclaredType {
    /// The declared type of a schema column, or `None` outside the ABI's column types.
    pub fn of(ty: &PgType) -> Option<DeclaredType> {
        Some(match ty {
            PgType::Int4 => DeclaredType::Int4,
            PgType::Int8 => DeclaredType::Int8,
            PgType::Numeric { typmod: Some((p, s)) } if *p <= SOURCE_DECIMAL_MAX_PRECISION => {
                DeclaredType::Numeric { precision: *p as u32, scale: *s as u32 }
            }
            PgType::Date => DeclaredType::Date,
            PgType::Text => DeclaredType::Text,
            PgType::Varchar { max_chars: Some(n) } => DeclaredType::Varchar { max_chars: u32::try_from(*n).ok()? },
            PgType::Bpchar { n: Some(n) } => DeclaredType::Bpchar { len: u32::try_from(*n).ok()? },
            _ => return None,
        })
    }

    pub fn kind(self) -> ColumnKind {
        match self {
            Self::Int4 | Self::Date => ColumnKind::I32,
            Self::Int8 => ColumnKind::I64,
            Self::Numeric { .. } => ColumnKind::I128,
            Self::Text | Self::Varchar { .. } | Self::Bpchar { .. } => ColumnKind::Utf8,
        }
    }
}

/// One delivered column of a source table.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeclaredColumn {
    /// Column position in the table's schema.
    pub ordinal: usize,
    pub name: String,
    pub ty: DeclaredType,
    /// Delivered only to carry the table's row count: not part of the source relation (the relation is the
    /// projection onto the other columns, possibly none). Always NOT NULL.
    pub row_count_only: bool,
    /// Declared nullable: delivered with its validity. Absent from the serialized form when false.
    #[serde(default, skip_serializing_if = "is_false")]
    pub nullable: bool,
}

fn is_false(b: &bool) -> bool {
    !*b
}

/// One distinct source table `tables(v)[j]`: table id in the schema, delivered columns in ABI order. A table read by
/// several FROM occurrences (a self-join) appears once.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeclaredTable {
    pub table_id: usize,
    pub name: String,
    pub columns: Vec<DeclaredColumn>,
}

impl DeclaredTable {
    /// The columns of the source relation (every delivered column except a row-count carrier), with their field
    /// index `k` of `t{j}_f{k}`.
    pub(super) fn relation_columns(&self) -> Vec<(usize, &DeclaredColumn)> {
        self.columns.iter().enumerate().filter(|(_, c)| !c.row_count_only).collect()
    }
}

/// The delivered source of a statement: field `k` of table `j` is `t{j}_f{k}` in the generated modules, and the ABI
/// column list is `t0_f0, t0_f1, .., t1_f0, ..`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DeclaredSource {
    pub tables: Vec<DeclaredTable>,
}

impl DeclaredSource {
    /// The declared source of the statement `doc` from its delivered columns
    /// (`gendb_frontend::columns::source_declaration`).
    pub fn of_statement(doc: &AstDocument, delivered: &SourceDeclaration) -> Result<DeclaredSource, AssemblyError> {
        Self::of_delivered(&doc.tables, delivered)
    }

    /// The declaration of a storage that stores the chosen columns of the dataset schema `schema` (`selection`: table
    /// id -> column ordinals; a table with no chosen column is stored through a row-count carrier). The delivery rules
    /// are the statements' (`gendb_frontend::columns::declared_columns`).
    pub fn for_storage(schema: &[TableDef], selection: &BTreeMap<usize, BTreeSet<usize>>) -> Result<DeclaredSource, AssemblyError> {
        let delivered = declared_columns(schema, selection).map_err(|e| AssemblyError::Source(e.to_string()))?;
        Self::of_delivered(schema, &delivered)
    }

    /// The declared SQL types of the `delivered` columns, taken from `schema`.
    fn of_delivered(schema: &[TableDef], delivered: &SourceDeclaration) -> Result<DeclaredSource, AssemblyError> {
        let refuse = |message: String| Err(AssemblyError::Source(message));
        let mut tables = Vec::new();
        for t in &delivered.tables {
            let Some(def) = schema.get(t.table_id) else {
                return refuse(format!("source table id {} outside the schema", t.table_id));
            };
            let mut columns = Vec::new();
            for c in &t.columns {
                let Some(col) = def.columns.get(c.ordinal) else {
                    return refuse(format!("{}: ordinal {} outside the table", def.name, c.ordinal));
                };
                if col.nullable != c.nullable || (c.nullable && c.row_count_only) {
                    return refuse(format!("{}.{}: delivered nullability differs from the declared column", def.name, col.name));
                }
                let Some(ty) = DeclaredType::of(&col.ty) else {
                    return refuse(format!("{}.{} ({:?}) has no ABI representation", def.name, col.name, col.ty));
                };
                columns.push(DeclaredColumn { ordinal: c.ordinal, name: c.name.clone(), ty, row_count_only: c.row_count_only, nullable: c.nullable });
            }
            tables.push(DeclaredTable { table_id: t.table_id, name: t.name.clone(), columns });
        }
        Ok(DeclaredSource { tables })
    }

    /// Every delivered field `(j, k, column)` in ABI order.
    pub(super) fn fields(&self) -> impl Iterator<Item = (usize, usize, &DeclaredColumn)> {
        self.tables.iter().enumerate().flat_map(|(j, t)| t.columns.iter().enumerate().map(move |(k, c)| (j, k, c)))
    }

    /// Whether some delivered column is nullable (its generated modules and shim then carry validity; a declaration of
    /// NOT NULL columns only generates exactly the text it generated before nullable columns were delivered).
    pub fn has_nullable(&self) -> bool {
        self.tables.iter().any(|t| t.columns.iter().any(|c| c.nullable))
    }

    /// The generators' precondition: at least one table, every table delivers at least one column (field 0 carries
    /// its row count through the ABI), and every table id, ordinal and numeric precision fits the emitted schema
    /// (`schema_widths[t]` = column count of table `t`) and the ABI.
    pub(super) fn check_deliverable(&self, schema_widths: &[usize]) -> Result<(), AssemblyError> {
        let refuse = |message: String| Err(AssemblyError::Source(message));
        if self.tables.is_empty() {
            return refuse("the statement reads no source table".into());
        }
        for t in &self.tables {
            if t.columns.is_empty() {
                return refuse(format!("source table {} has no delivered column: its row count cannot be passed through the ABI", t.name));
            }
            let Some(&width) = schema_widths.get(t.table_id) else {
                return refuse(format!("source table {} has id {} outside the schema", t.name, t.table_id));
            };
            for c in &t.columns {
                if c.ordinal >= width {
                    return refuse(format!("{}.{}: ordinal {} outside the table", t.name, c.name, c.ordinal));
                }
                if let DeclaredType::Numeric { precision, .. } = c.ty
                    && u64::from(precision) > SOURCE_DECIMAL_MAX_PRECISION
                {
                    return refuse(format!("{}.{}: numeric precision {precision} > 38 has no ABI representation", t.name, c.name));
                }
            }
        }
        Ok(())
    }
}
