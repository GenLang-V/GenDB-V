//! The projected snapshot of a capture: one Arrow IPC stream per captured table (or per column segment of an
//! extended table) plus `receipt.json`, which binds the files to the declared dataset, the source versions and the
//! captured ordinals. It sits in the same archive directory as the native column files of `crate::io`, which are
//! normalized from these IPC files; the IPC files are the logical tables the DataFusion reference reads.
//!
//! The receipt format is unchanged from the earlier GenDB version (versions 1 and 2): saved captures open as they are. Checks cover the
//! receipt's lifecycle version, declared schema, ordinals and file extents; nothing is hashed.

use super::dataset::{DatasetSpec, SourceVersion, declared_schema};
use super::error::{ImportError, Result};
use crate::io::{ArchiveTableLayout, IpcSegment, ProjectedTable, decode_mapped_ipc, fresh_lifecycle_version, read_ipc_segments};
use arrow::{
    ipc::writer::StreamWriter,
    record_batch::{RecordBatch, RecordBatchOptions},
};
use serde::{Deserialize, Serialize};
use std::{
    collections::BTreeSet,
    fs,
    io::Write,
    path::{Path, PathBuf},
};

const RECEIPT_FILE: &str = "receipt.json";

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct TableReceipt {
    pub name: String,
    /// Captured declared ordinals, strictly increasing.
    pub ordinals: Vec<usize>,
    pub rows: usize,
    /// Carried from version-1 receipts as saved; never computed or checked.
    #[serde(rename = "ipc_digest", default, skip_serializing_if = "String::is_empty")]
    pub saved_ipc_digest: String,
    /// Length of `table-<i>.arrow`; 0 when `segments` hold the table (or in version-1 receipts, where it is unchecked).
    #[serde(default)]
    pub ipc_bytes: u64,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub segments: Vec<IpcSegment>,
    /// Row-order identity of the table: a label of the capture in which its rows were read from its source files, in
    /// file row order. An extension that links or widens the table keeps it (the extension's recorded assumption is
    /// that unchanged files hold the same rows in the same order); a fresh read of the table gets a new label. Empty
    /// in receipts written before it existed (see [`SnapshotReceipt::row_order_identity`]).
    #[serde(default, skip_serializing_if = "String::is_empty")]
    pub row_order: String,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct SnapshotReceipt {
    /// 1 (legacy: no lifecycle version) or 2.
    pub version: u32,
    /// Assigned at capture; a prepared-root record names the version it expects.
    #[serde(default)]
    pub lifecycle_version: String,
    #[serde(rename = "spec")]
    pub dataset: DatasetSpec,
    /// Label of the source snapshot the capture was taken from, assigned at import.
    #[serde(rename = "snapshot")]
    pub source_snapshot: String,
    #[serde(rename = "bindings")]
    pub source_versions: Vec<SourceVersion>,
    pub tables: Vec<TableReceipt>,
}

impl SnapshotReceipt {
    /// Read the receipt of `archive`; `expected` is the lifecycle version the owning record names (unchecked for
    /// version-1 receipts, which predate lifecycle versions).
    pub fn read(archive: &Path, expected: &str) -> Result<Self> {
        let path = archive.join(RECEIPT_FILE);
        let receipt: Self = serde_json::from_slice(&fs::read(&path).map_err(ImportError::file(&path))?)
            .map_err(ImportError::json(&path))?;
        if !matches!(receipt.version, 1 | 2) {
            return Err(ImportError::prepared(&path, "unsupported receipt version"));
        }
        if receipt.version == 2 && receipt.lifecycle_version != expected {
            return Err(ImportError::prepared(&path, "snapshot lifecycle version differs"));
        }
        let mut names = BTreeSet::new();
        for table in &receipt.tables {
            let declared = receipt
                .dataset
                .table(&table.name)
                .ok_or_else(|| ImportError::prepared(&path, "captured table is not declared"))?;
            if !names.insert(&table.name)
                || table.ordinals.windows(2).any(|w| w[0] >= w[1])
                || table.ordinals.last().is_some_and(|&o| o >= declared.fields.len())
            {
                return Err(ImportError::prepared(
                    &path,
                    "duplicate captured table or invalid captured ordinals",
                ));
            }
        }
        Ok(receipt)
    }

    /// `(table, captured ordinals)` of every captured table (metadata only).
    pub fn coverage(&self) -> Vec<(String, Vec<usize>)> {
        self.tables
            .iter()
            .map(|t| (t.name.clone(), t.ordinals.clone()))
            .collect()
    }

    /// Row-order identity of captured table `name`: its recorded label, or for a receipt written before labels existed
    /// the label `capture:<capture_identity>` of the whole capture (`capture_identity`: the native capture identity of
    /// this receipt's archive), which is never shared with another capture. Metadata only.
    pub fn row_order_identity(&self, name: &str, capture_identity: &str) -> Option<String> {
        self.table(name).map(|(_, table)| row_order_or_capture(table, capture_identity))
    }

    fn table(&self, name: &str) -> Option<(usize, &TableReceipt)> {
        self.tables.iter().enumerate().find(|(_, t)| t.name == name)
    }

    fn write_new(&self, archive: &Path) -> Result<()> {
        let path = archive.join(RECEIPT_FILE);
        let bytes = serde_json::to_vec(self).map_err(ImportError::json(&path))?;
        fs::OpenOptions::new()
            .create_new(true)
            .write(true)
            .open(&path)
            .and_then(|mut file| file.write_all(&bytes))
            .map_err(ImportError::file(&path))
    }

    /// Decode the captured logical table `name` from its IPC file or segments, checking extent, schema and rows.
    pub fn read_table(&self, archive: &Path, name: &str) -> Result<ProjectedTable> {
        let (index, table) = self.table(name).ok_or_else(|| ImportError::NotCaptured {
            missing: vec![(name.to_string(), vec![])],
        })?;
        let declared = self
            .dataset
            .table(name)
            .ok_or_else(|| ImportError::prepared(archive, "captured table is not declared"))?;
        let fields: Vec<_> = table.ordinals.iter().map(|&o| declared.fields[o].clone()).collect();
        let batches = if table.segments.is_empty() {
            read_ipc_table(&archive.join(format!("table-{index}.arrow")), table, name, &fields)?
        } else {
            read_ipc_segments(archive, &table.segments, &table.ordinals, &fields, table.rows)?
        };
        Ok(ProjectedTable {
            table: name.to_string(),
            original_indices: table.ordinals.clone(),
            fields,
            batches,
            row_count: table.rows,
        })
    }
}

fn read_ipc_table(
    path: &Path,
    table: &TableReceipt,
    name: &str,
    fields: &[gendb_artifacts::ColumnSpec],
) -> Result<Vec<RecordBatch>> {
    let bytes = fs::metadata(path).map_err(ImportError::file(path))?.len();
    if table.ipc_bytes != 0 && bytes != table.ipc_bytes {
        return Err(ImportError::prepared(path, "snapshot IPC extent differs"));
    }
    // Mapped, not decoded into the heap: the reference's captured tables stay file-backed (`decode_mapped_ipc`).
    let (schema, batches) = decode_mapped_ipc(path, bytes)?;
    if schema.fields() != declared_schema(name, fields)?.fields() {
        return Err(ImportError::prepared(path, "captured schema/ordinal mismatch"));
    }
    if batches.iter().map(RecordBatch::num_rows).sum::<usize>() != table.rows {
        return Err(ImportError::prepared(path, "captured row count mismatch"));
    }
    Ok(batches)
}

/// Write `table` as one IPC stream and return the file length. A table captured for its row count only is written as
/// one batch without columns carrying that row count.
fn write_ipc(table: &ProjectedTable, path: &Path) -> Result<u64> {
    let schema = declared_schema(&table.table, &table.fields)?;
    let file = fs::File::create(path).map_err(ImportError::file(path))?;
    let mut writer = StreamWriter::try_new(file, &schema)?;
    if table.fields.is_empty() {
        let options = RecordBatchOptions::new().with_row_count(Some(table.row_count));
        writer.write(&RecordBatch::try_new_with_options(schema.clone(), vec![], &options)?)?;
    } else {
        for batch in &table.batches {
            writer.write(batch)?;
        }
    }
    writer.finish()?;
    drop(writer);
    Ok(fs::metadata(path).map_err(ImportError::file(path))?.len())
}

/// Create `archive` and write a fresh capture into it: `table-<i>.arrow` for `tables[i]` and a version-2 receipt with a
/// new lifecycle version.
pub(crate) fn write_capture(
    archive: &Path,
    dataset: &DatasetSpec,
    source_versions: &[SourceVersion],
    source_snapshot: &str,
    tables: &[ProjectedTable],
) -> Result<SnapshotReceipt> {
    fs::create_dir(archive).map_err(ImportError::file(archive))?;
    let lifecycle_version = fresh_lifecycle_version("lifecycle-v2");
    let mut receipts = vec![];
    for (i, table) in tables.iter().enumerate() {
        receipts.push(TableReceipt {
            name: table.table.clone(),
            ordinals: table.original_indices.clone(),
            rows: table.row_count,
            saved_ipc_digest: String::new(),
            ipc_bytes: write_ipc(table, &archive.join(format!("table-{i}.arrow")))?,
            segments: vec![],
            row_order: fresh_row_order(&lifecycle_version),
        });
    }
    let receipt = SnapshotReceipt {
        version: 2,
        lifecycle_version,
        dataset: dataset.clone(),
        source_snapshot: source_snapshot.to_string(),
        source_versions: source_versions.to_vec(),
        tables: receipts,
    };
    receipt.write_new(archive)?;
    Ok(receipt)
}

/// File lengths of an extension's IPC files, from file metadata (not device I/O): the base files it links (nothing is
/// copied or read) and the new files it writes.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct IpcFileBytes {
    pub linked: u64,
    pub written: u64,
}

/// Create `archive` as an extension of the prepared `base` archive by the newly captured columns `added`. Base IPC
/// files are symbolic links to the base's files (never decoded or rewritten); an extended table becomes column
/// segments (its base segments plus one new segment); a newly captured table gets its own file. The new receipt
/// declares `dataset` with `source_versions`: the base's, or a widening of them that declares every base table
/// identically (the caller's check). Returns the new receipt, the layout `crate::io` adopts and the IPC file lengths
/// linked and written. `added` tables must have the base's row count where the base has them.
///
/// Row-order identity: every table of the base keeps its row-order identity (`base_capture_identity` resolves a base
/// receipt without labels), linked or widened, because the widened columns are read from the same, unchanged source
/// files (checked stamps, equal row counts, the recorded assumption of same rows in the same order); a table new to
/// the capture gets a fresh label.
pub(crate) fn write_extension(
    base: &Path,
    base_receipt: &SnapshotReceipt,
    base_capture_identity: &str,
    dataset: &DatasetSpec,
    source_versions: Vec<SourceVersion>,
    added: &[ProjectedTable],
    archive: &Path,
) -> Result<(SnapshotReceipt, Vec<ArchiveTableLayout>, IpcFileBytes)> {
    for table in added {
        if base_receipt
            .table(&table.table)
            .is_some_and(|(_, t)| t.rows != table.row_count)
        {
            return Err(ImportError::SourceChanged {
                table: table.table.clone(),
            });
        }
    }
    fs::create_dir(archive).map_err(ImportError::file(archive))?;
    let lifecycle_version = fresh_lifecycle_version("lifecycle-v2");
    let mut ipc_bytes = IpcFileBytes::default();
    let mut link = |file: &str, name: &str| -> Result<u64> {
        if Path::new(file).components().count() != 1 {
            return Err(ImportError::prepared(base, "base IPC path is not local"));
        }
        let target: PathBuf = base
            .join(file)
            .canonicalize()
            .map_err(ImportError::file(base.join(file)))?;
        std::os::unix::fs::symlink(&target, archive.join(name)).map_err(ImportError::file(archive.join(name)))?;
        let length = fs::metadata(&target).map_err(ImportError::file(&target))?.len();
        ipc_bytes.linked += length;
        Ok(length)
    };
    let mut write = |table: &ProjectedTable, name: &str| -> Result<u64> {
        let length = write_ipc(table, &archive.join(name))?;
        ipc_bytes.written += length;
        Ok(length)
    };
    let mut tables = vec![];
    for (i, prior) in base_receipt.tables.iter().enumerate() {
        let Some(new) = added.iter().find(|t| t.table == prior.name) else {
            // Unchanged table: link its file or segments under the same names.
            let segments = prior
                .segments
                .iter()
                .map(|s| {
                    Ok(IpcSegment {
                        ipc_bytes: link(&s.file, &s.file)?,
                        ..s.clone()
                    })
                })
                .collect::<Result<Vec<_>>>()?;
            let ipc_bytes = if segments.is_empty() {
                link(&format!("table-{i}.arrow"), &format!("table-{i}.arrow"))?
            } else {
                0
            };
            tables.push(TableReceipt {
                ipc_bytes,
                segments,
                saved_ipc_digest: String::new(),
                row_order: row_order_or_capture(prior, base_capture_identity),
                ..prior.clone()
            });
            continue;
        };
        // Extended table: base segments (or its single file as one segment) linked, the new columns appended.
        let mut parts = if prior.segments.is_empty() {
            vec![IpcSegment {
                file: format!("table-{i}.arrow"),
                ordinals: prior.ordinals.clone(),
                ipc_bytes: 0,
            }]
        } else {
            prior.segments.clone()
        };
        parts.retain(|p| !p.ordinals.is_empty());
        let mut segments = vec![];
        for (j, part) in parts.iter().enumerate() {
            let file = format!("table-{i}-{j}.arrow");
            segments.push(IpcSegment {
                ipc_bytes: link(&part.file, &file)?,
                file,
                ordinals: part.ordinals.clone(),
            });
        }
        let file = format!("table-{i}-{}.arrow", parts.len());
        segments.push(IpcSegment {
            ipc_bytes: write(new, &file)?,
            file,
            ordinals: new.original_indices.clone(),
        });
        let mut ordinals: Vec<usize> = segments.iter().flat_map(|s| s.ordinals.iter().copied()).collect();
        ordinals.sort_unstable();
        tables.push(TableReceipt {
            name: prior.name.clone(),
            ordinals,
            rows: prior.rows,
            saved_ipc_digest: String::new(),
            ipc_bytes: 0,
            segments,
            row_order: row_order_or_capture(prior, base_capture_identity),
        });
    }
    for new in added.iter().filter(|t| base_receipt.table(&t.table).is_none()) {
        tables.push(TableReceipt {
            name: new.table.clone(),
            ordinals: new.original_indices.clone(),
            rows: new.row_count,
            saved_ipc_digest: String::new(),
            ipc_bytes: write(new, &format!("table-{}.arrow", tables.len()))?,
            segments: vec![],
            row_order: fresh_row_order(&lifecycle_version),
        });
    }
    let layout = tables
        .iter()
        .map(|t| {
            let declared = dataset
                .table(&t.name)
                .ok_or_else(|| ImportError::prepared(base, "captured table is not declared"))?;
            Ok(ArchiveTableLayout {
                table: t.name.clone(),
                original_indices: t.ordinals.clone(),
                fields: t.ordinals.iter().map(|&o| declared.fields[o].clone()).collect(),
                row_count: t.rows,
                ipc_bytes: t.ipc_bytes,
                segments: t.segments.clone(),
            })
        })
        .collect::<Result<Vec<_>>>()?;
    let receipt = SnapshotReceipt {
        version: 2,
        lifecycle_version,
        dataset: dataset.clone(),
        source_snapshot: base_receipt.source_snapshot.clone(),
        source_versions,
        tables,
    };
    receipt.write_new(archive)?;
    Ok((receipt, layout, ipc_bytes))
}

/// The row-order label of tables read from their source files by the capture with receipt lifecycle `lifecycle_version`.
fn fresh_row_order(lifecycle_version: &str) -> String {
    format!("receipt:{lifecycle_version}")
}

/// A table's recorded row-order label, or `capture:<capture_identity>` when its receipt predates labels.
fn row_order_or_capture(table: &TableReceipt, capture_identity: &str) -> String {
    if table.row_order.is_empty() { format!("capture:{capture_identity}") } else { table.row_order.clone() }
}
