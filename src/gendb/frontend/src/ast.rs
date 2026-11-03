//! The resolved typed SQL AST document (`gendb-sql-ast-v1`): its encoding schema, its decoded form and the decoder.
//!
//! The encoding is defined once, in `frontend/ast/ast_schema.json`, and mirrors the Verus AST constructor for
//! constructor: node tags are Verus variant names, field names are Verus field names, and each field kind states how
//! the value is represented in JSON, in the spec AST and in the exec AST. The Python parser reads the same file, so
//! there is no second hand-kept copy.
//!
//! - `schema`: the parsed encoding schema (`schema()`), embedded at compile time.
//! - `document`: the decoded document types (`AstDocument`, `Node`, `TableDef`, ...).
//! - `decode`: decoding and validation of a parser document (`decode`).
//! - `literals`: PostgreSQL limits and the literal validity rules shared by the decoder and `crate::params`.
//!
//! Trust: this is part of the trusted translator. The decoder checks every structural rule; typing beyond literals is
//! decided by the verified checker of the semantics library, not here.

mod decode;
mod document;
mod literals;
mod schema;

pub use decode::decode;
pub use document::{
    Annotation, AstDocument, ColType, ColumnDef, ConstraintDef, ConstraintTiming, FieldValue, Node, Output, PgType, Refusal,
    ScalarTy, TableDef, Translation, REFERENTIAL_ACTIONS,
};
pub use literals::{valid_ymd, NUMERIC_DSCALE_MAX, NUMERIC_INT_DIGITS_MAX, NUMERIC_MAX_PRECISION, VARLENA_MAX_CHARS};
pub use schema::{schema, AstSchema, ChildMode, FieldKind, Form, KindSpec, Machine, SortSpec, SCHEMA_JSON};

use std::fmt;

/// A structural violation of the AST encoding, or a malformed encoding schema.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AstError(pub String);

impl fmt::Display for AstError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid gendb-sql-ast-v1 document: {}", self.0)
    }
}

impl std::error::Error for AstError {}

fn err<T>(msg: impl Into<String>) -> Result<T, AstError> {
    Err(AstError(msg.into()))
}
