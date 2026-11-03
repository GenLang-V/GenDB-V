//! A prepared source: one captured, persisted version of a declared dataset, opened for execution.
//!
//! A prepared root directory holds `workload.json` (the [`PreparedRecord`]) and `inputs/`, the capture archive (the
//! snapshot receipt and IPC files of `snapshot`, the native column files of `crate::io`). `inputs` is a symbolic link
//! when the root reuses another root's capture. Opening maps the native column files read-only and decodes no data;
//! a captured logical table is decoded from its IPC file only when a reference first reads it.

use super::dataset::{DatasetSpec, SourceVersion, check_current};
use super::demand::{ColumnDemand, Projection, declaration_projection};
use super::error::{ImportError, Result};
use super::snapshot::SnapshotReceipt;
use crate::io::{ProjectedTable, SourceColumns};
use gendb_frontend::columns::SourceDeclaration;
use serde::{Deserialize, Serialize};
use std::{
    collections::BTreeMap,
    fs,
    io::Write,
    path::{Path, PathBuf},
    sync::{Arc, Mutex},
};

pub(crate) const RECORD_FILE: &str = "workload.json";
pub(crate) const ARCHIVE_DIRECTORY: &str = "inputs";

/// `workload.json` of a prepared root (format 2).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PreparedRecord {
    pub format_version: u32,
    pub dataset: DatasetSpec,
    /// The columns this workload asked for (the capture may hold more).
    pub demand: ColumnDemand,
    /// Lifecycle version of the capture's snapshot receipt.
    pub receipt_version: String,
    /// Capture identity of the archive's native columns.
    pub capture_identity: String,
    /// The prepared root whose capture this root reuses or extends, if any.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub base: Option<PathBuf>,
}

/// `workload.json` written by the earlier GenDB version (format 1). Its SQL members and per-query demand directories belong to
/// that version's native path; only the dataset and the two versions are used.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
#[allow(dead_code)]
struct V7PreparedRecord {
    #[serde(default)]
    canonical_capture: bool,
    format_version: u32,
    workload: V7Workload,
    snapshot_identity: String,
    native_capture_identity: String,
    demands: Vec<PathBuf>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
#[allow(dead_code)]
struct V7Workload {
    dataset: DatasetSpec,
    queries: Vec<String>,
}

impl PreparedRecord {
    pub(crate) const FORMAT_VERSION: u32 = 2;

    /// Read the record of a prepared root, format 2 or the earlier version's format 1 (whose demand is then empty: unrecorded).
    pub fn read(root: &Path) -> Result<Self> {
        let path = root.join(RECORD_FILE);
        let bytes = fs::read(&path).map_err(ImportError::file(&path))?;
        let value: serde_json::Value = serde_json::from_slice(&bytes).map_err(ImportError::json(&path))?;
        match value.get("format_version").and_then(serde_json::Value::as_u64) {
            Some(2) => serde_json::from_value(value).map_err(ImportError::json(&path)),
            Some(1) => {
                let legacy: V7PreparedRecord = serde_json::from_value(value).map_err(ImportError::json(&path))?;
                Ok(Self {
                    format_version: 1,
                    dataset: legacy.workload.dataset,
                    demand: ColumnDemand::default(),
                    receipt_version: legacy.snapshot_identity,
                    capture_identity: legacy.native_capture_identity,
                    base: None,
                })
            }
            _ => Err(ImportError::prepared(&path, "unsupported prepared-root record format")),
        }
    }

    pub(crate) fn write_new(&self, root: &Path) -> Result<()> {
        let path = root.join(RECORD_FILE);
        let bytes = serde_json::to_vec_pretty(self).map_err(ImportError::json(&path))?;
        fs::OpenOptions::new()
            .create_new(true)
            .write(true)
            .open(&path)
            .and_then(|mut file| file.write_all(&bytes))
            .map_err(ImportError::file(&path))
    }
}

/// One persisted capture of a declared dataset, opened for execution. Clones of its columns and projections share the
/// read-only mappings; the source stays valid while any of them lives.
pub struct PreparedSource {
    root: PathBuf,
    archive: PathBuf,
    record: PreparedRecord,
    receipt: SnapshotReceipt,
    /// The capture's native columns, mapped read-only; their logical tables carry no batches.
    columns: SourceColumns,
    /// Captured logical tables decoded so far (for references), by table name.
    logical: Mutex<BTreeMap<String, Arc<ProjectedTable>>>,
}

impl PreparedSource {
    /// Open the prepared root `root` for `dataset`: its record must declare the same dataset, every lifecycle-stamped
    /// source must still be current, and the receipt and mapped columns must be the recorded versions of the same
    /// capture (tables, ordinals, fields, rows). Nothing is written, imported or decoded.
    pub fn open(root: &Path, dataset: &DatasetSpec) -> Result<Self> {
        let root = root.canonicalize().map_err(ImportError::file(root))?;
        let record = PreparedRecord::read(&root)?;
        if record.dataset != *dataset {
            return Err(ImportError::prepared(
                &root,
                "prepared source schema/locations differ from the request",
            ));
        }
        let archive = root.join(ARCHIVE_DIRECTORY);
        let archive = archive.canonicalize().map_err(ImportError::file(&archive))?;
        let receipt = SnapshotReceipt::read(&archive, &record.receipt_version)?;
        if receipt.dataset != record.dataset {
            return Err(ImportError::prepared(
                &archive,
                "snapshot dataset differs from the prepared record",
            ));
        }
        check_current(dataset, &receipt.source_versions)?;
        let columns = SourceColumns::map_archive(&archive)?;
        if columns.capture_identity() != record.capture_identity {
            return Err(ImportError::prepared(
                &archive,
                "native capture identity differs from the prepared record",
            ));
        }
        check_capture_matches_receipt(&archive, &columns, &receipt)?;
        Ok(Self {
            root,
            archive,
            record,
            receipt,
            columns,
            logical: Mutex::default(),
        })
    }

    /// Seed the logical-table cache with tables just captured (sharing their buffers), so a fresh import is not
    /// decoded again for its first reference.
    pub(crate) fn with_logical_tables(self, tables: &[ProjectedTable]) -> Self {
        let logical = tables.iter().map(|t| (t.table.clone(), Arc::new(t.clone()))).collect();
        Self {
            logical: Mutex::new(logical),
            ..self
        }
    }

    /// The canonical prepared root directory.
    /// The source data facts of this prepared root (`data-facts.json`, computed during preparation; `None` for a root
    /// prepared before facts existed). For the workload storage author only.
    pub fn data_facts_path(&self) -> std::path::PathBuf {
        self.root.join(super::facts::DATA_FACTS_FILE)
    }

    pub fn root(&self) -> &Path {
        &self.root
    }

    /// The canonical capture archive directory (the target of `inputs`).
    pub fn archive(&self) -> &Path {
        &self.archive
    }

    pub fn record(&self) -> &PreparedRecord {
        &self.record
    }

    pub fn dataset(&self) -> &DatasetSpec {
        &self.record.dataset
    }

    /// Label of the source snapshot this capture was imported from (recorded as the run's source version).
    pub fn source_snapshot(&self) -> &str {
        &self.receipt.source_snapshot
    }

    /// Recorded source version of every declared table.
    pub fn source_versions(&self) -> &[SourceVersion] {
        &self.receipt.source_versions
    }

    /// Recorded source version of `table` (the key admitted assets are bound to).
    pub fn source_version(&self, table: &str) -> Option<&str> {
        self.receipt
            .source_versions
            .iter()
            .find(|v| v.table == table)
            .map(|v| v.version.as_str())
    }

    /// Row count of a captured table.
    pub fn row_count(&self, table: &str) -> Option<usize> {
        self.columns
            .tables()
            .iter()
            .find(|t| t.table == table)
            .map(|t| t.row_count)
    }

    /// Capture identity of the whole capture's native columns.
    pub fn capture_identity(&self) -> &str {
        self.columns.capture_identity()
    }

    /// Row-order identity of a captured table: equal for two captures exactly when they hold the table's rows as one
    /// read of the same source files, in the same order. A reused root shares its base's receipt; an extension keeps the
    /// label of every base table, including a widened one; an import or a changed source gets a new label. Stored
    /// assets of one table built from captures with equal labels, source version and row count relate to the same
    /// row sequence. Metadata only.
    pub fn row_order_identity(&self, table: &str) -> Option<String> {
        self.receipt.row_order_identity(table, self.capture_identity())
    }

    /// `(table, captured ordinals)` of every captured table.
    pub fn coverage(&self) -> Vec<(String, Vec<usize>)> {
        self.receipt.coverage()
    }

    /// The whole capture's native columns (mapped, read-only).
    pub fn columns(&self) -> &SourceColumns {
        &self.columns
    }

    /// The captured columns of `projection`, in its table order, read-only for native execution. Metadata only: the
    /// view shares the capture's mappings, and its capture identity derives from the capture identity and the
    /// projection. Refused with the missing columns when the capture does not cover the projection.
    pub fn project(&self, projection: &[(String, Vec<usize>)]) -> Result<SourceColumns> {
        let mut demand = ColumnDemand::default();
        for (table, ordinals) in projection {
            demand.add_columns(self.dataset(), table, ordinals)?;
        }
        let missing = demand.missing_from(&self.coverage());
        if !missing.is_empty() {
            return Err(ImportError::NotCaptured { missing });
        }
        Ok(self.columns.project(projection)?.read_only()?.0)
    }

    /// The columns a statement's source declaration delivers, bound to the declared dataset, then projected.
    pub fn project_declaration(&self, declaration: &SourceDeclaration) -> Result<SourceColumns> {
        let projection: Projection = declaration_projection(self.dataset(), declaration)?;
        self.project(&projection)
    }

    /// The captured logical table `name`, decoded from its IPC file on first use and kept for later references. The
    /// decoded table must agree with the mapped native columns (ordinals, fields, rows).
    pub fn logical_table(&self, name: &str) -> Result<Arc<ProjectedTable>> {
        let mut decoded = self.logical.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
        if let Some(table) = decoded.get(name) {
            return Ok(table.clone());
        }
        let table = Arc::new(self.receipt.read_table(&self.archive, name)?);
        decoded.insert(name.to_string(), table.clone());
        Ok(table)
    }
}

impl std::fmt::Debug for PreparedSource {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PreparedSource")
            .field("root", &self.root)
            .field("capture_identity", &self.capture_identity())
            .finish_non_exhaustive()
    }
}

/// The snapshot receipt and the native column files describe the same captured tables.
fn check_capture_matches_receipt(archive: &Path, columns: &SourceColumns, receipt: &SnapshotReceipt) -> Result<()> {
    let differs = || ImportError::prepared(archive, "native columns and snapshot receipt describe different tables");
    if columns.tables().len() != receipt.tables.len() {
        return Err(differs());
    }
    for native in columns.tables() {
        let captured = receipt
            .tables
            .iter()
            .find(|t| t.name == native.table)
            .ok_or_else(differs)?;
        let declared = receipt.dataset.table(&native.table).ok_or_else(differs)?;
        let declared_fields = captured.ordinals.iter().map(|&o| &declared.fields[o]);
        if captured.ordinals != native.original_indices
            || captured.rows != native.row_count
            || !declared_fields.eq(native.fields.iter())
        {
            return Err(differs());
        }
    }
    Ok(())
}
