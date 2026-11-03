//! Normalized source columns: projected logical Arrow tables and their canonical native descriptors, with
//! metadata-only projection and read-only protection. Archive persistence is in `archive` and `column_files`.

use super::archive::{ArchiveManifest, ArchiveView};
use super::column::{
    ColumnBinding, NATIVE_TYPE_BOOL, NATIVE_TYPE_UTF8, NativeColumn, ValueLayout, extent, native_type_tag,
    utf8_offsets_extent,
};
use super::error::{Result, StorageIoError};
use super::ipc::arrow_schema;
use super::read_only::ReadOnlyBuffer;
use arrow::{
    array::{Array, ArrayRef, AsArray, BooleanArray, LargeStringArray, StringArray, new_empty_array},
    buffer::OffsetBuffer,
    datatypes::{
        ArrowPrimitiveType, DataType, Date32Type, Decimal128Type, Int32Type, Int64Type, SchemaRef, UInt32Type,
        UInt64Type,
    },
    record_batch::{RecordBatch, RecordBatchOptions},
};
use gendb_artifacts::{ColType, ColumnSpec};
use std::{
    collections::{BTreeMap, BTreeSet},
    path::PathBuf,
    sync::Arc,
};

/// Logical Arrow batches of one source table, projected to some of its declared columns.
#[derive(Clone, Debug)]
pub struct ProjectedTable {
    pub table: String,
    /// Declared ordinals of the projected columns, strictly increasing; `fields[i]` declares `original_indices[i]`.
    pub original_indices: Vec<usize>,
    pub fields: Vec<ColumnSpec>,
    /// Empty in an execution mapping, which does not decode Arrow.
    pub batches: Vec<RecordBatch>,
    pub row_count: usize,
}

/// Canonical native columns of projected source tables, plus the logical tables they were normalized from.
///
/// Descriptors point into buffers this owner keeps alive: normalized heap arrays, or read-only mappings (copied or
/// file-backed). Clones and projections share those buffers; none is mutated after construction.
#[derive(Clone)]
pub struct SourceColumns {
    pub(super) tables: Vec<ProjectedTable>,
    pub(super) bindings: Vec<ColumnBinding>,
    pub(super) descriptors: Vec<NativeColumn>,
    pub(super) heap_columns: Arc<Vec<HeapColumn>>,
    pub(super) read_only_buffers: Vec<Arc<ReadOnlyBuffer>>,
    /// Read-only copy of `descriptors`, set once the columns are protected for native execution.
    pub(super) read_only_descriptors: Option<Arc<ReadOnlyBuffer>>,
    /// Archive metadata of the whole capture (lifecycle, schema, IPC extents).
    pub(super) manifest: ArchiveManifest,
    /// Lifecycle identity of these columns: an assigned version label (or, for a view, its derivation), never a hash
    /// of values.
    pub(super) capture_identity: String,
    /// Canonical directory of the base archive these columns were read from or persisted to.
    pub(super) base_archive: Option<PathBuf>,
    /// Set when these columns are a projection of a base archive.
    pub(super) view: Option<ArchiveView>,
}

// SAFETY: every descriptor target is an immutable heap array or read-only mapping owned (through `Arc`) by this value;
// moving the owner moves no allocation, and only shared reads escape.
unsafe impl Send for SourceColumns {}
unsafe impl Sync for SourceColumns {}

/// Heap allocations one normalized column's descriptor points into. Moving the vectors keeps their heap buffers.
pub(super) struct HeapColumn {
    _array: ArrayRef,
    _validity: Vec<u8>,
    _bool_bytes: Vec<u8>,
}

impl SourceColumns {
    /// Normalize projected tables into canonical native columns with a fresh lifecycle identity.
    pub fn from_projected(tables: Vec<ProjectedTable>) -> Result<Self> {
        Self::normalize(tables, None)
    }

    /// Normalize decoded tables once. `archived` supplies the lifecycle/schema/extent metadata of a loaded or adopted
    /// archive; values are never serialized or hashed to identify the owner.
    pub(super) fn normalize(mut tables: Vec<ProjectedTable>, archived: Option<ArchiveManifest>) -> Result<Self> {
        let mut names = BTreeSet::new();
        let mut bindings = vec![];
        let mut descriptors = vec![];
        let mut heap_columns = vec![];
        for table in &mut tables {
            if table.table.is_empty() || !names.insert(table.table.clone()) {
                return Err(StorageIoError::Shape("invalid duplicate source or projection ordinals"));
            }
            let schema = check_projected_table(table)?;
            let columns = contiguous_columns(table, &schema)?;
            table.batches = rebatch_sharing_buffers(table, &columns, &schema)?;
            if table.fields.is_empty() {
                let (binding, descriptor) =
                    ColumnBinding::row_count_only(&table.table, descriptors.len(), table.row_count)?;
                bindings.push(binding);
                descriptors.push(descriptor);
            }
            for ((field, ordinal), array) in table.fields.iter().zip(&table.original_indices).zip(columns) {
                let (descriptor, heap) = describe_column(field, array, table.row_count)?;
                bindings.push(ColumnBinding {
                    table: table.table.clone(),
                    original_index: Some(*ordinal),
                    descriptor_index: descriptors.len(),
                    field: Some(field.clone()),
                    row_count: table.row_count,
                });
                descriptors.push(descriptor);
                heap_columns.push(heap);
            }
        }
        let manifest = archived.unwrap_or_else(|| ArchiveManifest::fresh(&tables));
        Ok(Self {
            tables,
            bindings,
            descriptors,
            heap_columns: Arc::new(heap_columns),
            read_only_buffers: vec![],
            read_only_descriptors: None,
            capture_identity: manifest.lifecycle_version.clone(),
            manifest,
            base_archive: None,
            view: None,
        })
    }

    /// Metadata-only projection to `(table, ordinals)` pairs, in the given table order. Arrow and native buffers stay
    /// shared; no value is scanned, serialized or hashed. A table projected to no ordinals delivers its row count.
    pub fn project(&self, projection: &[(String, Vec<usize>)]) -> Result<Self> {
        let mut tables = vec![];
        let mut bindings = vec![];
        let mut descriptors = vec![];
        let mut names = BTreeSet::new();
        for (name, ordinals) in projection {
            if !names.insert(name) || ordinals.windows(2).any(|w| w[0] >= w[1]) {
                return Err(StorageIoError::Shape("invalid native view projection"));
            }
            let table = self
                .tables
                .iter()
                .find(|t| &t.table == name)
                .ok_or(StorageIoError::Shape("native view source was not captured"))?;
            let positions = ordinals
                .iter()
                .map(|o| {
                    table
                        .original_indices
                        .iter()
                        .position(|c| c == o)
                        .ok_or(StorageIoError::Shape("native view column was not captured"))
                })
                .collect::<Result<Vec<_>>>()?;
            tables.push(ProjectedTable {
                table: name.clone(),
                original_indices: ordinals.clone(),
                fields: positions.iter().map(|p| table.fields[*p].clone()).collect(),
                batches: table
                    .batches
                    .iter()
                    .map(|b| b.project(&positions))
                    .collect::<std::result::Result<_, _>>()?,
                row_count: table.row_count,
            });
            if ordinals.is_empty() {
                let (binding, descriptor) = ColumnBinding::row_count_only(name, descriptors.len(), table.row_count)?;
                bindings.push(binding);
                descriptors.push(descriptor);
            }
            for ordinal in ordinals {
                let binding = self
                    .bindings
                    .iter()
                    .find(|b| &b.table == name && b.original_index == Some(*ordinal))
                    .ok_or(StorageIoError::Shape("native view binding absent"))?;
                let descriptor_index = descriptors.len();
                descriptors.push(self.descriptors[binding.descriptor_index]);
                bindings.push(ColumnBinding {
                    descriptor_index,
                    ..binding.clone()
                });
            }
        }
        let view = ArchiveView::of_projection(self, projection);
        Ok(Self {
            tables,
            bindings,
            descriptors,
            heap_columns: self.heap_columns.clone(),
            read_only_buffers: self.read_only_buffers.clone(),
            read_only_descriptors: None,
            manifest: self.manifest.clone(),
            capture_identity: view.capture_identity()?,
            base_archive: self.base_archive.clone(),
            view: Some(view),
        })
    }

    /// Attach independently decoded logical tables (for reference checks) to mapped native columns, without
    /// normalizing or converting values again. Table names, ordinals, fields and row counts must agree.
    pub fn with_reference_tables(&self, tables: Vec<ProjectedTable>) -> Result<Self> {
        if tables.len() != self.tables.len() {
            return Err(StorageIoError::Shape("reference/native table membership differs"));
        }
        for (logical, native) in tables.iter().zip(&self.tables) {
            let batch_rows = logical.batches.iter().map(RecordBatch::num_rows).sum::<usize>();
            let row_count_only = logical.fields.is_empty() && logical.batches.is_empty();
            if logical.table != native.table
                || logical.original_indices != native.original_indices
                || logical.fields != native.fields
                || logical.row_count != native.row_count
                || (!row_count_only && batch_rows != logical.row_count)
            {
                return Err(StorageIoError::Shape("reference/native lifecycle interface differs"));
            }
        }
        Ok(Self { tables, ..self.clone() })
    }

    /// Protect every descriptor buffer and the descriptor array for native execution. Buffers already inside a
    /// read-only mapping are kept by address; heap buffers are copied once. Returns the protected columns and the
    /// number of bytes copied (a new projection of protected columns copies only its descriptor array).
    pub fn read_only(&self) -> Result<(Self, u64)> {
        let mut result = self.clone();
        if result.read_only_descriptors.is_some() {
            return Ok((result, 0));
        }
        let mut protector = BufferProtector {
            buffers: std::mem::take(&mut result.read_only_buffers),
            copies: BTreeMap::new(),
            copied_bytes: 0,
        };
        for descriptor in &mut result.descriptors {
            protector.protect_column(descriptor)?;
        }
        result.read_only_buffers = protector.buffers;
        // SAFETY: `NativeColumn` is plain `repr(C)` data; the slice covers exactly the descriptor array.
        let descriptor_bytes = unsafe {
            std::slice::from_raw_parts(
                result.descriptors.as_ptr().cast::<u8>(),
                std::mem::size_of_val(result.descriptors.as_slice()),
            )
        };
        result.read_only_descriptors = Some(Arc::new(ReadOnlyBuffer::copy(descriptor_bytes)?));
        Ok((result, protector.copied_bytes + descriptor_bytes.len() as u64))
    }

    pub fn is_read_only(&self) -> bool {
        self.read_only_descriptors.is_some()
    }

    /// The descriptors, from the read-only copy once protected.
    pub fn descriptors(&self) -> &[NativeColumn] {
        match &self.read_only_descriptors {
            // SAFETY: the mapping holds a copy of exactly `self.descriptors.len()` descriptors and lives with `self`.
            Some(mapping) => unsafe { std::slice::from_raw_parts(mapping.as_ptr().cast(), self.descriptors.len()) },
            None => &self.descriptors,
        }
    }

    pub fn bindings(&self) -> &[ColumnBinding] {
        &self.bindings
    }

    pub fn capture_identity(&self) -> &str {
        &self.capture_identity
    }

    /// Immutable logical tables for independent reference checks against these columns.
    pub fn tables(&self) -> &[ProjectedTable] {
        &self.tables
    }
}

/// Check one table's declared projection, schema, nullability and row count; returns its Arrow schema.
fn check_projected_table(table: &ProjectedTable) -> Result<SchemaRef> {
    if table.original_indices.len() != table.fields.len() || table.original_indices.windows(2).any(|w| w[0] >= w[1]) {
        return Err(StorageIoError::Shape("invalid duplicate source or projection ordinals"));
    }
    i64::try_from(table.row_count).map_err(|_| StorageIoError::Overflow("row count"))?;
    let schema = arrow_schema(&table.fields)?;
    let mut names = BTreeSet::new();
    if table.fields.iter().any(|f| f.name.is_empty() || !names.insert(&f.name)) {
        return Err(StorageIoError::Shape("invalid field names"));
    }
    let mut rows = 0usize;
    for batch in &table.batches {
        if batch.schema().fields() != schema.fields() {
            return Err(StorageIoError::Shape("projected batch schema disagreement"));
        }
        rows = rows
            .checked_add(batch.num_rows())
            .ok_or(StorageIoError::Overflow("row count"))?;
        if table
            .fields
            .iter()
            .zip(batch.columns())
            .any(|(field, array)| !field.nullable && array.null_count() > 0)
        {
            return Err(StorageIoError::Shape("NULL in nonnullable input"));
        }
    }
    if rows != table.row_count && !(table.fields.is_empty() && table.batches.is_empty()) {
        return Err(StorageIoError::Shape("projected row count disagreement"));
    }
    Ok(schema)
}

/// One contiguous array per column. UTF-8 batches are widened to `LargeUtf8` BEFORE concatenation: a narrow
/// concatenation can overflow i32 offsets even though every source batch is individually valid.
fn contiguous_columns(table: &ProjectedTable, schema: &SchemaRef) -> Result<Vec<ArrayRef>> {
    (0..table.fields.len())
        .map(|i| {
            let ty = match table.fields[i].ty {
                ColType::Utf8 => DataType::LargeUtf8,
                _ => schema.field(i).data_type().clone(),
            };
            let chunks = table
                .batches
                .iter()
                .map(|b| {
                    if ty == DataType::LargeUtf8 {
                        arrow::compute::cast(b.column(i), &ty)
                    } else {
                        Ok(b.column(i).clone())
                    }
                })
                .collect::<std::result::Result<Vec<_>, _>>()?;
            Ok(match chunks.as_slice() {
                [] => new_empty_array(&ty),
                [single] => single.clone(),
                _ => arrow::compute::concat(&chunks.iter().map(|a| a.as_ref()).collect::<Vec<_>>())?,
            })
        })
        .collect()
}

/// Logical batches with the source batch boundaries and logical `Utf8` schema, sharing the contiguous columns'
/// buffers. String value bytes stay in the one wide allocation; only each batch's narrow i32 offsets are separate
/// (4 bytes per string row), and no logical `Utf8` batch spans the signed-i32 extent.
fn rebatch_sharing_buffers(
    table: &ProjectedTable,
    columns: &[ArrayRef],
    schema: &SchemaRef,
) -> Result<Vec<RecordBatch>> {
    let lengths = if table.batches.is_empty() {
        vec![table.row_count]
    } else {
        table.batches.iter().map(RecordBatch::num_rows).collect()
    };
    let mut row = 0;
    lengths
        .into_iter()
        .map(|len| {
            let slices = columns
                .iter()
                .map(|column| match column.as_any().downcast_ref::<LargeStringArray>() {
                    Some(wide) => narrow_utf8_slice(wide, row, len),
                    None => Ok(column.slice(row, len)),
                })
                .collect::<Result<Vec<_>>>()?;
            row += len;
            Ok(RecordBatch::try_new_with_options(
                schema.clone(),
                slices,
                &RecordBatchOptions::new().with_row_count(Some(len)),
            )?)
        })
        .collect()
}

/// Rows `[start, start + len)` of a wide string column as a narrow `Utf8` array over the same value bytes.
fn narrow_utf8_slice(wide: &LargeStringArray, start: usize, len: usize) -> Result<ArrayRef> {
    let slice = wide.slice(start, len);
    let offsets = slice.value_offsets();
    let first = offsets[0];
    let byte_start = usize::try_from(first).map_err(|_| StorageIoError::Overflow("string offset"))?;
    let byte_end = usize::try_from(offsets[len]).map_err(|_| StorageIoError::Overflow("string offset"))?;
    let narrow = offsets
        .iter()
        .map(|offset| i32::try_from(offset - first).map_err(|_| StorageIoError::Overflow("narrow string offset")))
        .collect::<Result<Vec<_>>>()?;
    let array = StringArray::try_new(
        OffsetBuffer::new(narrow.into()),
        slice.values().slice_with_length(byte_start, byte_end - byte_start),
        slice.nulls().cloned(),
    )?;
    Ok(Arc::new(array))
}

/// The canonical descriptor of one contiguous column and the heap buffers it points into.
fn describe_column(field: &ColumnSpec, array: ArrayRef, rows: usize) -> Result<(NativeColumn, HeapColumn)> {
    let validity: Vec<u8> = if field.nullable {
        (0..rows).map(|r| u8::from(array.is_valid(r))).collect()
    } else {
        vec![]
    };
    let mut descriptor = NativeColumn {
        type_tag: native_type_tag(field.ty)?,
        nullable: i32::from(field.nullable),
        len: i64::try_from(rows).map_err(|_| StorageIoError::Overflow("row count"))?,
        values: std::ptr::null(),
        offsets: std::ptr::null(),
        bytes: std::ptr::null(),
        validity: if field.nullable {
            validity.as_ptr()
        } else {
            std::ptr::null()
        },
    };
    let mut bool_bytes = vec![];
    match field.ty {
        ColType::I32 => descriptor.values = primitive_values::<Int32Type>(&array)?,
        ColType::Date32 => descriptor.values = primitive_values::<Date32Type>(&array)?,
        ColType::I64 => descriptor.values = primitive_values::<Int64Type>(&array)?,
        ColType::U32 => descriptor.values = primitive_values::<UInt32Type>(&array)?,
        ColType::U64 => descriptor.values = primitive_values::<UInt64Type>(&array)?,
        ColType::Decimal { .. } => descriptor.values = primitive_values::<Decimal128Type>(&array)?,
        ColType::Bool => {
            let booleans = array
                .as_any()
                .downcast_ref::<BooleanArray>()
                .ok_or(StorageIoError::Shape("bool array mismatch"))?;
            bool_bytes = (0..booleans.len()).map(|r| u8::from(booleans.value(r))).collect();
            descriptor.values = bool_bytes.as_ptr();
            debug_assert_eq!(descriptor.type_tag, NATIVE_TYPE_BOOL);
        }
        ColType::Utf8 => {
            let strings = array
                .as_any()
                .downcast_ref::<LargeStringArray>()
                .ok_or(StorageIoError::Shape("UTF8 array mismatch"))?;
            i64::try_from(strings.value_data().len()).map_err(|_| StorageIoError::Overflow("string bytes"))?;
            descriptor.offsets = strings.value_offsets().as_ptr();
            descriptor.bytes = strings.value_data().as_ptr();
            debug_assert_eq!(descriptor.type_tag, NATIVE_TYPE_UTF8);
        }
        ColType::Binary => return Err(StorageIoError::UnsupportedType(field.ty)),
    }
    Ok((
        descriptor,
        HeapColumn {
            _array: array,
            _validity: validity,
            _bool_bytes: bool_bytes,
        },
    ))
}

fn primitive_values<T: ArrowPrimitiveType>(array: &ArrayRef) -> Result<*const u8> {
    let values = array
        .as_primitive_opt::<T>()
        .ok_or(StorageIoError::Shape("array representation mismatch"))?;
    Ok(values.values().as_ptr().cast())
}

/// Moves descriptor buffers into read-only memory during one `read_only` call.
struct BufferProtector {
    buffers: Vec<Arc<ReadOnlyBuffer>>,
    /// Heap address → its protected copy and length, so a buffer shared by two descriptors is copied once.
    copies: BTreeMap<usize, (*const u8, usize)>,
    copied_bytes: u64,
}

impl BufferProtector {
    fn protect_column(&mut self, descriptor: &mut NativeColumn) -> Result<()> {
        let rows = usize::try_from(descriptor.len).map_err(|_| StorageIoError::Overflow("row count"))?;
        if descriptor.nullable != 0 {
            descriptor.validity = self.protect(descriptor.validity, rows)?;
        }
        match ValueLayout::of_tag(descriptor.type_tag)
            .ok_or(StorageIoError::Shape("unsupported native descriptor format"))?
        {
            ValueLayout::Fixed { width } => {
                descriptor.values = self.protect(descriptor.values, extent(rows, width)?)?
            }
            ValueLayout::Utf8 => {
                // SAFETY: a canonical UTF-8 descriptor has `rows + 1` offsets; the last one ends the value bytes.
                let end = unsafe { *descriptor.offsets.add(rows) };
                let value_bytes = usize::try_from(end).map_err(|_| StorageIoError::Overflow("string bytes"))?;
                descriptor.bytes = self.protect(descriptor.bytes, value_bytes)?;
                descriptor.offsets = self
                    .protect(descriptor.offsets.cast(), utf8_offsets_extent(rows)?)?
                    .cast();
            }
            ValueLayout::RowCountOnly => {}
        }
        Ok(())
    }

    fn protect(&mut self, pointer: *const u8, len: usize) -> Result<*const u8> {
        if len == 0 || pointer.is_null() || self.buffers.iter().any(|b| b.contains(pointer, len)) {
            return Ok(pointer);
        }
        if let Some((protected, protected_len)) = self.copies.get(&(pointer as usize)) {
            if *protected_len < len {
                return Err(StorageIoError::Shape("protected buffer extent differs"));
            }
            return Ok(*protected);
        }
        // SAFETY: extents come from framework-normalized typed arrays owned by these columns, not from candidate code.
        let bytes = unsafe { std::slice::from_raw_parts(pointer, len) };
        let copy = Arc::new(ReadOnlyBuffer::copy(bytes)?);
        let protected = copy.as_ptr();
        self.copies.insert(pointer as usize, (protected, len));
        self.copied_bytes += len as u64;
        self.buffers.push(copy);
        Ok(protected)
    }
}
