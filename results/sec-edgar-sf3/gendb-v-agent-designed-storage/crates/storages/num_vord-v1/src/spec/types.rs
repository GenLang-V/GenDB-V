//! Declared SQL types, table schemas with their integrity-constraint declarations, and the static types used by
//! typing (`spec::typing`).
//!
//! `SqlType`, `Column`, `ScalarTy` and `ColTy` are plain data shared by spec and exec code (their fields are
//! PostgreSQL's own typmod domains, which fit `u32`); `Constraint` and `TableSchema` hold sequences and have
//! separate exec forms (`exec::relational::schema`).
use vstd::prelude::*;
use crate::spec::limits::*;
use crate::spec::ast::Pred;
use crate::spec::constraints::*;

verus! {

/// Declared column type (PostgreSQL names in comments). Unconstrained `numeric`, `timestamptz`, floats,
/// intervals as values and negative numeric scales are outside the fragment (frontend refusal
/// `unsupported_type`).
#[derive(Clone, Copy)]
pub enum SqlType {
    /// `boolean`
    Bool,
    /// `integer` / `int4`
    Int4,
    /// `bigint` / `int8`
    Int8,
    /// `numeric(precision, scale)` / `decimal(p, s)` with `1 <= precision <= 1000`, `0 <= scale <= precision`.
    Numeric { precision: u32, scale: u32 },
    /// `date`
    Date,
    /// `timestamp` (without time zone)
    Timestamp,
    /// `text`
    Text,
    /// `varchar(max_chars)`
    Varchar { max_chars: u32 },
    /// `char(len)` / `bpchar(len)`; values are stored canonical (trailing U+0020 removed).
    Bpchar { len: u32 },
}

/// One table column: declared type and nullability (`NOT NULL` / `PRIMARY KEY` make it non-nullable).
/// Column names are frontend metadata only; the semantics addresses columns by position.
#[derive(Clone, Copy)]
pub struct Column {
    pub ty: SqlType,
    pub nullable: bool,
}

/// A declared integrity constraint of one table (column positions of that table). Its meaning is
/// `spec::constraints::constraints_hold`; which constraints are well-formed is `spec::constraints::constraints_wf`.
pub enum Constraint {
    /// `PRIMARY KEY (cols)` (`primary`) or `UNIQUE [NULLS [NOT] DISTINCT] (cols)`.
    Key { cols: Seq<nat>, primary: bool, nulls_distinct: bool },
    /// `FOREIGN KEY (cols) REFERENCES table (ref_cols) [MATCH FULL]` (MATCH SIMPLE when `!match_full`).
    ForeignKey { cols: Seq<nat>, table: nat, ref_cols: Seq<nat>, match_full: bool },
    /// `CHECK (p)`, `p` over the table's row (environment = the row).
    Check(Pred),
}

/// Spec schema of one table.
pub struct TableSchema {
    pub columns: Seq<Column>,
    pub constraints: Seq<Constraint>,
}

/// Spec schema: table id (DDL order) -> table schema.
pub type Schema = Seq<TableSchema>;

/// Static type of an expression (typing only). `Numeric { scale }` is an upper bound on the display scale
/// (dscale) of every value of the expression: exact for columns and literals, but division and AVG results
/// have a value-dependent dscale (PostgreSQL `select_div_scale`, at most 1000). Value identity (GROUP BY,
/// DISTINCT) is therefore SQL value equality (`spec::equality`), never structural equality of numerics.
#[derive(Clone, Copy)]
pub enum ScalarTy {
    Bool,
    Int4,
    Int8,
    /// Upper bound on the display scale; typing keeps it `<= numeric_dscale_max()`, so it fits `u32`.
    Numeric { scale: u32 },
    Date,
    Timestamp,
    /// `text`, `varchar(n)` and canonical `char(n)`: one comparison family (bytes, C collation).
    Text,
}

/// Static column type of an expression or query output column.
#[derive(Clone, Copy)]
pub struct ColTy {
    pub ty: ScalarTy,
    pub nullable: bool,
}

/// Static type of a declared type (`text`, `varchar(n)` and `char(n)` are one comparison family).
pub open spec fn scalar_ty_of(t: SqlType) -> ScalarTy {
    match t {
        SqlType::Bool => ScalarTy::Bool,
        SqlType::Int4 => ScalarTy::Int4,
        SqlType::Int8 => ScalarTy::Int8,
        SqlType::Numeric { precision, scale } => ScalarTy::Numeric { scale },
        SqlType::Date => ScalarTy::Date,
        SqlType::Timestamp => ScalarTy::Timestamp,
        SqlType::Text => ScalarTy::Text,
        SqlType::Varchar { max_chars } => ScalarTy::Text,
        SqlType::Bpchar { len } => ScalarTy::Text,
    }
}

pub open spec fn col_ty_of(c: Column) -> ColTy {
    ColTy { ty: scalar_ty_of(c.ty), nullable: c.nullable }
}

/// A declared type is inside the fragment (PostgreSQL's typmod rules restricted to non-negative scales).
pub open spec fn sql_type_wf(t: SqlType) -> bool {
    match t {
        SqlType::Numeric { precision, scale } => 1 <= precision <= numeric_max_precision() && scale <= precision,
        SqlType::Varchar { max_chars } => 1 <= max_chars <= char_length_max(),
        SqlType::Bpchar { len } => 1 <= len <= char_length_max(),
        _ => true,
    }
}

/// Every column type is inside the fragment (recursive, so `by (compute)` decides it).
pub open spec fn columns_wf(cols: Seq<Column>) -> bool
    decreases cols.len(),
{
    cols.len() == 0 || (sql_type_wf(cols.last().ty) && columns_wf(cols.drop_last()))
}

/// Every declared column type of every table is inside the fragment.
pub open spec fn tables_wf(schema: Schema) -> bool
    decreases schema.len(),
{
    schema.len() == 0 || (columns_wf(schema.last().columns) && tables_wf(schema.drop_last()))
}

/// Well-formed schema: column types and declared constraints (`spec::constraints::constraints_wf`).
pub open spec fn schema_wf(schema: Schema) -> bool {
    tables_wf(schema) && constraints_wf(schema)
}

} // verus!
