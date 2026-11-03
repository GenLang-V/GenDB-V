//! The normalized column descriptor shared by storage and the runtime ABI, and the binding that says which source
//! column a descriptor delivers.

use super::error::{Result, StorageIoError};
use gendb_artifacts::{ColType, ColumnSpec};
use serde::{Deserialize, Serialize};

/// One read-only normalized column, passed by pointer to admitted code (the ABI v3 input column; 48 bytes, C layout).
///
/// Pointers borrow buffers owned by a [`super::SourceColumns`] (or another owner that outlives every use):
/// - fixed-width types: `values` holds `len` host-order values of the tag's width;
/// - `NATIVE_TYPE_BOOL`: `values` holds one byte per row, 0 or 1 (never a bitmap);
/// - `NATIVE_TYPE_UTF8`: `offsets` holds `len + 1` i64 byte offsets into `bytes`. Offsets are absolute in the shared
///   value buffer, so the first may be non-zero;
/// - nullable columns: `validity` holds one byte per row (1 valid, 0 NULL); non-nullable columns: null;
/// - `NATIVE_TYPE_CARDINALITY`: row count only, every pointer null.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct NativeColumn {
    pub type_tag: i32,
    pub nullable: i32,
    pub len: i64,
    pub values: *const u8,
    pub offsets: *const i64,
    pub bytes: *const u8,
    pub validity: *const u8,
}

// Type tags of canonical columns. They equal the constants of the Verus ABI shim. Tag 5 (native opaque) and tag 10
// (native registered storage) belong to the earlier version's native path and are never produced here.
/// `I32` and `Date32` (days since 1970-01-01).
pub const NATIVE_TYPE_I32: i32 = 1;
pub const NATIVE_TYPE_I64: i32 = 2;
/// Decimal coefficient `v` of `v * 10^-scale`; the scale is in the binding's declared field.
pub const NATIVE_TYPE_I128: i32 = 3;
pub const NATIVE_TYPE_UTF8: i32 = 4;
pub const NATIVE_TYPE_BOOL: i32 = 6;
pub const NATIVE_TYPE_U32: i32 = 7;
pub const NATIVE_TYPE_U64: i32 = 8;
pub const NATIVE_TYPE_CARDINALITY: i32 = 9;

/// Canonical native type tag of a declared column type.
pub(crate) fn native_type_tag(ty: ColType) -> Result<i32> {
    Ok(match ty {
        ColType::I32 | ColType::Date32 => NATIVE_TYPE_I32,
        ColType::I64 => NATIVE_TYPE_I64,
        ColType::U32 => NATIVE_TYPE_U32,
        ColType::U64 => NATIVE_TYPE_U64,
        ColType::Bool => NATIVE_TYPE_BOOL,
        ColType::Utf8 => NATIVE_TYPE_UTF8,
        ColType::Decimal { p, s } if (1..=38).contains(&p) && s >= 0 && s <= p as i8 => NATIVE_TYPE_I128,
        _ => return Err(StorageIoError::UnsupportedType(ty)),
    })
}

/// Which buffers a canonical descriptor uses, by type tag.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ValueLayout {
    /// `values` holds `width` bytes per row.
    Fixed { width: usize },
    /// `offsets` (i64, rows + 1) and `bytes`.
    Utf8,
    /// No buffers: row count only.
    RowCountOnly,
}

impl ValueLayout {
    pub(crate) fn of_tag(type_tag: i32) -> Option<Self> {
        Some(match type_tag {
            NATIVE_TYPE_I32 | NATIVE_TYPE_U32 => Self::Fixed { width: 4 },
            NATIVE_TYPE_I64 | NATIVE_TYPE_U64 => Self::Fixed { width: 8 },
            NATIVE_TYPE_I128 => Self::Fixed { width: 16 },
            NATIVE_TYPE_BOOL => Self::Fixed { width: 1 },
            NATIVE_TYPE_UTF8 => Self::Utf8,
            NATIVE_TYPE_CARDINALITY => Self::RowCountOnly,
            _ => return None,
        })
    }
}

/// Byte length of `rows` items of `width` bytes.
pub(crate) fn extent(rows: usize, width: usize) -> Result<usize> {
    rows.checked_mul(width).ok_or(StorageIoError::Overflow("column extent"))
}

/// Byte length of the `rows + 1` i64 offsets of a UTF-8 column.
pub(crate) fn utf8_offsets_extent(rows: usize) -> Result<usize> {
    rows.checked_add(1)
        .and_then(|n| n.checked_mul(8))
        .ok_or(StorageIoError::Overflow("offset extent"))
}

/// Which source column one descriptor delivers. Serialized inside archives; the serde form equals the earlier
/// version's `NativeInputBinding` with its canonical encoding (the omitted `encoding` field).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ColumnBinding {
    pub table: String,
    /// Ordinal of the column in the declared source table; `None` for the row-count-only descriptor of a table
    /// projected to no columns.
    pub original_index: Option<usize>,
    /// Position of the descriptor in the owner's descriptor list.
    pub descriptor_index: usize,
    /// Declared column; `None` exactly when `original_index` is `None`.
    pub field: Option<ColumnSpec>,
    pub row_count: usize,
}

impl ColumnBinding {
    /// The row-count-only descriptor of `table` and its binding.
    pub(crate) fn row_count_only(table: &str, descriptor_index: usize, rows: usize) -> Result<(Self, NativeColumn)> {
        let len = i64::try_from(rows).map_err(|_| StorageIoError::Overflow("row count"))?;
        let binding = Self {
            table: table.into(),
            original_index: None,
            descriptor_index,
            field: None,
            row_count: rows,
        };
        let descriptor = NativeColumn {
            type_tag: NATIVE_TYPE_CARDINALITY,
            nullable: 0,
            len,
            values: std::ptr::null(),
            offsets: std::ptr::null(),
            bytes: std::ptr::null(),
            validity: std::ptr::null(),
        };
        Ok((binding, descriptor))
    }
}
