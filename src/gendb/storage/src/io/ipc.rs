//! Arrow IPC stream files of logical projected tables: the canonical Arrow schema of declared columns, writing one
//! table file, and reading a table stored as one file or as column segments.

use super::error::{Result, StorageIoError};
use super::read_only::ReadOnlyBuffer;
use super::source_columns::ProjectedTable;
use arrow::{
    datatypes::{DataType, Field, Schema, SchemaRef},
    buffer::Buffer,
    ipc::{reader::StreamDecoder, writer::StreamWriter},
    record_batch::{RecordBatch, RecordBatchOptions},
};
use gendb_artifacts::{ColType, ColumnSpec};
use serde::{Deserialize, Serialize};
use std::{collections::BTreeMap, fs, io::Write, path::Path, sync::Arc};

/// One local IPC file holding a strictly increasing subset of a table's captured ordinals.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct IpcSegment {
    /// File name inside the archive directory (one path component).
    pub file: String,
    pub ordinals: Vec<usize>,
    pub ipc_bytes: u64,
}

/// Physical layout of one table of an extended archive, as placed by the snapshot layer (import).
#[derive(Clone, Debug)]
pub struct ArchiveTableLayout {
    pub table: String,
    pub original_indices: Vec<usize>,
    pub fields: Vec<ColumnSpec>,
    pub row_count: usize,
    /// Length of the single `table-<i>.arrow` file, or 0 when `segments` hold the table.
    pub ipc_bytes: u64,
    pub segments: Vec<IpcSegment>,
}

/// Arrow type of a declared column with a canonical native form.
fn arrow_type(ty: ColType) -> Result<DataType> {
    Ok(match ty {
        ColType::I32 => DataType::Int32,
        ColType::I64 => DataType::Int64,
        ColType::U32 => DataType::UInt32,
        ColType::U64 => DataType::UInt64,
        ColType::Bool => DataType::Boolean,
        ColType::Date32 => DataType::Date32,
        ColType::Utf8 => DataType::Utf8,
        ColType::Decimal { p, s } if (1..=38).contains(&p) && s >= 0 && s <= p as i8 => DataType::Decimal128(p, s),
        _ => return Err(StorageIoError::UnsupportedType(ty)),
    })
}

/// Arrow schema of declared columns (logical `Utf8`, not `LargeUtf8`).
pub(crate) fn arrow_schema(fields: &[ColumnSpec]) -> Result<SchemaRef> {
    let fields = fields
        .iter()
        .map(|f| Ok(Field::new(&f.name, arrow_type(f.ty)?, f.nullable)))
        .collect::<Result<Vec<_>>>()?;
    Ok(Arc::new(Schema::new(fields)))
}

/// Write `table`'s batches as one IPC stream.
pub(crate) fn write_ipc(table: &ProjectedTable, output: impl Write) -> Result<()> {
    let mut writer = StreamWriter::try_new(output, arrow_schema(&table.fields)?.as_ref())?;
    for batch in &table.batches {
        writer.write(batch)?;
    }
    writer.finish()?;
    Ok(())
}

/// Read one IPC table file after checking its length and schema against the archive metadata.
pub(crate) fn read_ipc_file(path: &Path, expected_bytes: u64, fields: &[ColumnSpec]) -> Result<Vec<RecordBatch>> {
    if fs::metadata(path).map_err(StorageIoError::file(path))?.len() != expected_bytes {
        return Err(StorageIoError::archive(path, "archive IPC length mismatch"));
    }
    let (schema, batches) = decode_mapped_ipc(path, expected_bytes)?;
    if schema.fields() != arrow_schema(fields)?.fields() {
        return Err(StorageIoError::archive(path, "archive schema disagreement"));
    }
    Ok(batches)
}

/// Decode the IPC stream file `path` (of exactly `bytes` bytes) over a read-only shared mapping of the file: aligned
/// column buffers of the returned batches reference the mapping (file-backed pages the kernel can reclaim and re-read)
/// instead of a decoded heap copy, so a large captured table costs no anonymous memory; a misaligned buffer is copied
/// by the decoder. The mapping lives as long as any batch that references it. Arrow validates every batch as with a
/// reader over the file.
pub(crate) fn decode_mapped_ipc(path: &Path, bytes: u64) -> Result<(SchemaRef, Vec<RecordBatch>)> {
    let len = usize::try_from(bytes).map_err(|_| StorageIoError::Overflow("IPC file length"))?;
    let mapping = Arc::new(ReadOnlyBuffer::map_file(path, len)?);
    let pointer = std::ptr::NonNull::new(mapping.as_ptr().cast_mut()).expect("a mapping is never null");
    // SAFETY: the mapping is valid and read-only for `len` bytes while `mapping` (the owner) lives; the Buffer keeps
    // it alive. An empty file maps one byte, of which none is exposed.
    let mut remaining = unsafe { Buffer::from_custom_allocation(pointer, len, mapping) };
    let mut decoder = StreamDecoder::new();
    let mut batches = vec![];
    while !remaining.is_empty() {
        if let Some(batch) = decoder.decode(&mut remaining)? {
            batches.push(batch);
        }
    }
    decoder.finish()?;
    let schema = decoder.schema().ok_or_else(|| StorageIoError::archive(path, "IPC stream without a schema"))?;
    Ok((schema, batches))
}

/// Read a column-segmented table. `fields[i]` declares `ordinals[i]`. Each local file is checked for extent, schema
/// and row count. Columns are joined per batch by reference: rows are sliced only where the segments' batch
/// boundaries differ, and nothing is re-encoded or copied.
pub fn read_ipc_segments(
    root: &Path,
    segments: &[IpcSegment],
    ordinals: &[usize],
    fields: &[ColumnSpec],
    rows: usize,
) -> Result<Vec<RecordBatch>> {
    let mut covered = segments
        .iter()
        .flat_map(|s| s.ordinals.iter().copied())
        .collect::<Vec<_>>();
    covered.sort_unstable();
    let strictly_increasing = |ordinals: &[usize]| ordinals.windows(2).all(|w| w[0] < w[1]);
    if segments.is_empty()
        || fields.len() != ordinals.len()
        || covered != ordinals
        || !strictly_increasing(&covered)
        || segments
            .iter()
            .any(|s| s.ordinals.is_empty() || !strictly_increasing(&s.ordinals))
    {
        return Err(StorageIoError::archive(
            root,
            "IPC segments do not partition the captured ordinals",
        ));
    }
    let field_of =
        |ordinal: &usize| fields[ordinals.iter().position(|o| o == ordinal).expect("covered ordinal")].clone();
    let mut parts = vec![];
    for segment in segments {
        if Path::new(&segment.file).components().count() != 1 {
            return Err(StorageIoError::archive(root, "IPC segment path is not local"));
        }
        let path = root.join(&segment.file);
        if fs::metadata(&path).map_err(StorageIoError::file(&path))?.len() != segment.ipc_bytes {
            return Err(StorageIoError::archive(&path, "IPC segment extent differs"));
        }
        let (schema, batches) = decode_mapped_ipc(&path, segment.ipc_bytes)?;
        if schema.fields() != arrow_schema(&segment.ordinals.iter().map(field_of).collect::<Vec<_>>())?.fields() {
            return Err(StorageIoError::archive(&path, "IPC segment schema/ordinal mismatch"));
        }
        if batches.iter().map(RecordBatch::num_rows).sum::<usize>() != rows {
            return Err(StorageIoError::archive(&path, "IPC segment row count mismatch"));
        }
        parts.push((
            segment,
            batches.into_iter().filter(|b| b.num_rows() > 0).collect::<Vec<_>>(),
        ));
    }
    let schema = arrow_schema(fields)?;
    // Per segment: (index of the current batch, rows of it already consumed).
    let mut cursors = vec![(0usize, 0usize); parts.len()];
    let mut result = vec![];
    let mut row = 0;
    while row < rows {
        let len = parts
            .iter()
            .zip(&cursors)
            .map(|((_, batches), (batch, consumed))| batches[*batch].num_rows() - consumed)
            .min()
            .expect("at least one segment");
        let mut columns = BTreeMap::new();
        for ((segment, batches), (batch, consumed)) in parts.iter().zip(cursors.iter_mut()) {
            let current = &batches[*batch];
            let slice = if *consumed == 0 && len == current.num_rows() {
                current.clone()
            } else {
                current.slice(*consumed, len)
            };
            for (ordinal, column) in segment.ordinals.iter().zip(slice.columns()) {
                columns.insert(*ordinal, column.clone());
            }
            *consumed += len;
            if *consumed == current.num_rows() {
                *batch += 1;
                *consumed = 0;
            }
        }
        result.push(RecordBatch::try_new_with_options(
            schema.clone(),
            columns.into_values().collect(),
            &RecordBatchOptions::new().with_row_count(Some(len)),
        )?);
        row += len;
    }
    Ok(result)
}
