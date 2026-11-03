//! The decoded document: a post-order node arena over the encoding schema, the schema tables it was resolved against,
//! its output metadata and declared statement parameters; or a named refusal of the parser.

use super::schema::{schema, Form};
use crate::params::DocParam;
use serde_json::Value;

/// Verus `ScalarTy` (the static type carried by a typed NULL literal).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarTy {
    pub kind: String,
    pub scale: Option<u64>,
}

/// One decoded field, of the variant its `FieldKind` prescribes.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FieldValue {
    Child(usize),
    Children(Vec<usize>),
    /// Canonical decimal integer (unbounded).
    Int(String),
    Nat(u64),
    OptNat(Option<u64>),
    Fixed(i64),
    Bool(bool),
    Bytes(String),
    ScalarTy(ScalarTy),
    Enum(String),
}

/// PostgreSQL-level type of an annotation or schema column (`typmod`/length absent only on expression types).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PgType {
    Bool,
    Int4,
    Int8,
    Numeric { typmod: Option<(u64, u64)> },
    Date,
    Timestamp,
    Text,
    Varchar { max_chars: Option<u64> },
    Bpchar { n: Option<u64> },
}

/// The resolver's static type of an expression or output column (a claim; the verified checker decides).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ColType {
    pub ty: PgType,
    pub nullable: bool,
    /// Static numeric scale; present exactly for numeric. The Verus type reads it as an upper bound.
    pub dscale: Option<u64>,
    /// PostgreSQL-level annotation (not part of the Verus AST): every value has exactly `dscale` (true), or a
    /// value-dependent display scale up to it (division, AVG, CASE of different scales). Encoded as
    /// `"dscale_exact": false` on a numeric only; absent means exact.
    pub dscale_exact: bool,
}

/// The parser's annotation of a node (not part of the Verus AST).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Annotation {
    /// Of an expression node.
    Type(ColType),
    /// Of a query node: its output columns.
    Columns(Vec<ColType>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    pub tag: String,
    /// In the schema's field order.
    pub fields: Vec<FieldValue>,
    pub annotation: Option<Annotation>,
}

impl Node {
    pub fn field(&self, name: &str) -> Option<&FieldValue> {
        let spec = &schema().kinds[&self.tag];
        spec.fields.iter().position(|(n, _)| n == name).map(|i| &self.fields[i])
    }

    /// The node id of child field `name` (a `ref:` or `box:` field).
    pub fn child(&self, name: &str) -> Option<usize> {
        match self.field(name) {
            Some(FieldValue::Child(c)) => Some(*c),
            _ => None,
        }
    }

    /// The node ids of child list `name` (a `seq:` field).
    pub fn children(&self, name: &str) -> Option<&[usize]> {
        match self.field(name) {
            Some(FieldValue::Children(cs)) => Some(cs),
            _ => None,
        }
    }

    /// `Some(n)` for the statement parameter `$n` (form `param`).
    pub fn param_index(&self) -> Option<u32> {
        match (schema().kinds[&self.tag].form, self.field("index")) {
            (Form::Param, Some(FieldValue::Nat(n))) => Some(*n as u32),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ColumnDef {
    pub name: String,
    pub ty: PgType,
    pub nullable: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TableDef {
    pub name: String,
    pub columns: Vec<ColumnDef>,
    /// Declared integrity constraints in declaration order (Verus `TableSchema::constraints`).
    pub constraints: Vec<ConstraintDef>,
}

/// When PostgreSQL checks a modification against a key or foreign key (metadata: a committed database satisfies the
/// same instance predicate either way).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ConstraintTiming {
    pub deferrable: bool,
    pub initially_deferred: bool,
}

/// One declared constraint of a table (column positions of that table). Its meaning is Verus `spec::constraints`;
/// names, referential actions and timing are metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConstraintDef {
    /// `PRIMARY KEY (columns)` / `UNIQUE [NULLS NOT DISTINCT] (columns)`.
    Key { name: Option<String>, primary: bool, columns: Vec<u64>, nulls_distinct: bool, timing: ConstraintTiming },
    /// `FOREIGN KEY (columns) REFERENCES table (ref_columns) [MATCH FULL]`.
    ForeignKey {
        name: Option<String>,
        columns: Vec<u64>,
        table: u64,
        ref_columns: Vec<u64>,
        match_full: bool,
        on_delete: String,
        on_update: String,
        timing: ConstraintTiming,
    },
    /// `CHECK (p)`: a post-order arena whose last node (`nodes[root]`) is a `pred` over the table's row.
    Check { name: Option<String>, nodes: Vec<Node>, root: usize },
}

/// Referential actions of the parser encoding.
pub const REFERENTIAL_ACTIONS: &[&str] = &["no_action", "restrict", "cascade", "set_null", "set_default"];

/// Output metadata of the statement (one entry per output column).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Output {
    pub names: Vec<String>,
    pub columns: Vec<ColType>,
    pub pg_types: Vec<String>,
}

/// A validated `ok` document.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AstDocument {
    /// The parser's identity record (`identity`, `sqlglot`, `dialect`, `target`).
    pub frontend: Value,
    pub sql: String,
    pub tables: Vec<TableDef>,
    pub output: Output,
    /// Declared statement parameters `$n` (ascending index; empty for a statement without placeholders). After
    /// `params::instantiate`: the free ones only.
    pub params: Vec<DocParam>,
    /// Post-order arena; `nodes[root]` is the `OrderedQuery`.
    pub nodes: Vec<Node>,
    pub root: usize,
}

impl AstDocument {
    /// The statement body: the query node under the `OrderedQuery` root.
    pub fn body(&self) -> usize {
        self.nodes[self.root].child("body").expect("a decoded root has a body")
    }
}

/// A named refusal of the parser.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Refusal {
    pub reason: String,
    pub detail: String,
    pub path: String,
    pub sql: String,
}

/// A decoded parser document: an AST or a named refusal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Translation {
    Ok(AstDocument),
    Refused(Refusal),
}
