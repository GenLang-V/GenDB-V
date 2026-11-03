//! Declared source columns as they appear inside stored records (representation source tables, asset keys).
//!
//! The serde encoding is part of every saved record's bytes and identity: an externally tagged type
//! (`{"Decimal":{"p":15,"s":2}}`, `"Date32"`, `"Utf8"`, ...) and `{"name":..,"nullable":..,"ty":..}`. It equals the
//! encoding of the earlier version's `contracts::{ColType, ColumnSpec}`, so saved v3 records decode and re-encode byte-identically.

use serde::{Deserialize, Serialize};

/// Declared column type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum ColType {
    /// Exact decimal with precision `p` and scale `s`; the stored value is the coefficient `v` of `v * 10^-s`.
    Decimal { p: u8, s: i8 },
    /// Days since 1970-01-01 (Arrow Date32).
    Date32,
    Bool,
    I32,
    I64,
    U32,
    U64,
    /// UTF-8 text, ordered by bytes.
    Utf8,
    /// Raw bytes, ordered by bytes.
    Binary,
}

/// One declared column of a source table.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ColumnSpec {
    pub name: String,
    pub ty: ColType,
    pub nullable: bool,
}
