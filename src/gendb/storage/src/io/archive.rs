//! Archive directories of source columns. The on-disk format is unchanged from the earlier GenDB version:
//!
//! - base archive: `manifest.json` ([`ArchiveManifest`]), `capture-version.txt` (lifecycle identity; version-1
//!   archives name it `identity.sha256`, a label that is read, never computed), one IPC stream `table-<i>.arrow` per
//!   table or its column segments, and the `native-buffers/` column files (`column_files`);
//! - view archive: `view.json` ([`ArchiveView`]: base directory, base identity, projection) and `capture-version.txt`,
//!   with no data files.
//!
//! Execution mapping refuses archives with `decimal-views.json` or `registered-views.json` (non-canonical native
//! encodings); only the earlier GenDB version serves them. Checks cover lifecycle identity, schema and file extents only; nothing is
//! hashed.

use super::error::{Result, StorageIoError};
use super::ipc::{IpcSegment, read_ipc_file, read_ipc_segments, write_ipc};
use super::source_columns::{ProjectedTable, SourceColumns};
use gendb_artifacts::ColumnSpec;
use serde::{Deserialize, Serialize};
use std::{
    collections::BTreeSet,
    fs,
    io::Write,
    path::{Path, PathBuf},
};

/// Upper bound on archive metadata JSON files, which never hold values.
const METADATA_LIMIT_BYTES: u64 = 16 * 1024 * 1024;
const MANIFEST_FILE: &str = "manifest.json";
const CAPTURE_VERSION_FILE: &str = "capture-version.txt";
const LEGACY_CAPTURE_VERSION_FILE: &str = "identity.sha256";
const VIEW_FILE: &str = "view.json";
/// Metadata files of the earlier version's non-canonical encodings.
const V7_ONLY_FILES: [&str; 2] = ["decimal-views.json", "registered-views.json"];

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ArchiveManifest {
    /// 1 (legacy: no lifecycle version) or 2.
    pub version: u32,
    #[serde(default)]
    pub lifecycle_version: String,
    pub tables: Vec<ArchivedTable>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ArchivedTable {
    pub table: String,
    pub original_indices: Vec<usize>,
    pub fields: Vec<ColumnSpec>,
    pub row_count: usize,
    /// Length of `table-<i>.arrow`; 0 while the columns are only in memory or when `segments` hold the table.
    pub ipc_bytes: u64,
    /// Carried from version-1 archives as saved; never computed or checked.
    #[serde(rename = "ipc_sha256", default, skip_serializing_if = "String::is_empty")]
    pub saved_ipc_sha256: String,
    /// Column groups in separate IPC files (an extended archive links the base file and adds new columns). Empty: the
    /// single `table-<i>.arrow` file.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub segments: Vec<IpcSegment>,
}

impl ArchiveManifest {
    /// Version-2 metadata of freshly normalized tables, with a new lifecycle version.
    pub fn fresh(tables: &[ProjectedTable]) -> Self {
        Self {
            version: 2,
            lifecycle_version: fresh_lifecycle_version("native-v2"),
            tables: tables
                .iter()
                .map(|t| ArchivedTable {
                    table: t.table.clone(),
                    original_indices: t.original_indices.clone(),
                    fields: t.fields.clone(),
                    row_count: t.row_count,
                    ipc_bytes: 0,
                    saved_ipc_sha256: String::new(),
                    segments: vec![],
                })
                .collect(),
        }
    }
}

/// A projection of a base archive, persisted as metadata only.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct ArchiveView {
    pub version: u32,
    /// Canonical base archive directory; empty until the base is persisted.
    pub source: PathBuf,
    /// Capture identity of the base archive.
    pub source_identity: String,
    /// `(table, declared ordinals)` pairs, in delivery order.
    pub projection: Vec<(String, Vec<usize>)>,
}

impl ArchiveView {
    /// The view of `columns` projected to `projection`. A view of a view refers to the same base.
    pub fn of_projection(columns: &SourceColumns, projection: &[(String, Vec<usize>)]) -> Self {
        Self {
            version: 1,
            source: columns.base_archive.clone().unwrap_or_default(),
            source_identity: columns
                .view
                .as_ref()
                .map_or_else(|| columns.capture_identity.clone(), |v| v.source_identity.clone()),
            projection: projection.to_vec(),
        }
    }

    /// Capture identity of the view: derived from the base identity and the projection, not from values.
    pub fn capture_identity(&self) -> Result<String> {
        serde_json::to_string(&("native-view-v2", &self.source_identity, &self.projection))
            .map_err(StorageIoError::json(&self.source))
    }

    fn read(archive: &Path) -> Result<Self> {
        let path = archive.join(VIEW_FILE);
        let view: Self = read_metadata(&path)?;
        if view.version != 1 || view.source.join(VIEW_FILE).exists() {
            return Err(StorageIoError::archive(&path, "invalid or nested archive view"));
        }
        Ok(view)
    }
}

/// A new lifecycle label `<prefix>-<pid>-<nanos>-<counter>`: unique per preparation, independent of values.
pub fn fresh_lifecycle_version(prefix: &str) -> String {
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    let counter = NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    format!("{prefix}-{}-{nanos}-{counter}", std::process::id())
}

impl SourceColumns {
    /// Persist these columns as a fresh archive directory; an existing directory is refused, so saved evidence is
    /// never replaced. A projection is written as a view (metadata only) and requires a persisted base. Columns read
    /// from an archive re-export its IPC files by copy, refused if the source changed length meanwhile.
    pub fn write_archive(&self, path: &Path) -> Result<()> {
        fs::create_dir(path).map_err(StorageIoError::file(path))?;
        if let Some(view) = &self.view {
            if view.source.as_os_str().is_empty() {
                return Err(StorageIoError::archive(
                    path,
                    "persist base archive before exporting a native view",
                ));
            }
            write_new_file(
                &path.join(VIEW_FILE),
                &serde_json::to_vec(view).map_err(StorageIoError::json(path))?,
            )?;
            return write_new_file(&path.join(CAPTURE_VERSION_FILE), self.capture_identity.as_bytes());
        }
        let mut manifest = self.manifest.clone();
        for (i, (table, archived)) in self.tables.iter().zip(&mut manifest.tables).enumerate() {
            match &self.base_archive {
                Some(source) if !archived.segments.is_empty() => {
                    for segment in &archived.segments {
                        copy_unchanged(
                            &source.join(&segment.file),
                            &path.join(&segment.file),
                            segment.ipc_bytes,
                        )?;
                    }
                }
                Some(source) => {
                    let file = format!("table-{i}.arrow");
                    copy_unchanged(&source.join(&file), &path.join(&file), archived.ipc_bytes)?;
                }
                None => {
                    let file = path.join(format!("table-{i}.arrow"));
                    write_ipc(table, fs::File::create(&file).map_err(StorageIoError::file(&file))?)?;
                    archived.ipc_bytes = fs::metadata(&file).map_err(StorageIoError::file(&file))?.len();
                }
            }
        }
        write_new_file(
            &path.join(MANIFEST_FILE),
            &serde_json::to_vec(&manifest).map_err(StorageIoError::json(path))?,
        )?;
        write_new_file(&path.join(CAPTURE_VERSION_FILE), self.capture_identity.as_bytes())?;
        self.write_column_files(path)
    }

    /// Reconstruct archived columns by decoding their IPC files (logical tables included) and normalizing once.
    /// Execution should use [`SourceColumns::map_archive`], which maps the column files instead. Only canonical
    /// columns are decoded; encoding views of the earlier GenDB version next to them are not read.
    pub fn decode_archive(path: &Path) -> Result<Self> {
        if !path.join(VIEW_FILE).exists() {
            return Self::decode_base_archive(path, None);
        }
        let view = ArchiveView::read(path)?;
        let names = view
            .projection
            .iter()
            .map(|(name, _)| name.clone())
            .collect::<BTreeSet<_>>();
        let base = Self::decode_base_archive(&view.source, Some(&names))?;
        if base.capture_identity != view.source_identity {
            return Err(StorageIoError::archive(
                path,
                "archive view trusted base identity mismatch",
            ));
        }
        let result = base.project(&view.projection)?;
        if read_capture_version(path)? != result.capture_identity {
            return Err(StorageIoError::archive(path, "archive view identity mismatch"));
        }
        Ok(result)
    }

    /// Decode a base archive, only the tables in `names` when given (a view never reopens unrelated tables).
    fn decode_base_archive(path: &Path, names: Option<&BTreeSet<String>>) -> Result<Self> {
        let manifest: ArchiveManifest = read_metadata(&path.join(MANIFEST_FILE))?;
        let capture_identity = read_capture_version(path)?;
        check_manifest_lifecycle(path, &manifest, &capture_identity)?;
        let mut tables = vec![];
        for (i, archived) in manifest.tables.iter().enumerate() {
            if names.is_some_and(|names| !names.contains(&archived.table)) {
                continue;
            }
            let batches = if archived.segments.is_empty() {
                read_ipc_file(
                    &path.join(format!("table-{i}.arrow")),
                    archived.ipc_bytes,
                    &archived.fields,
                )?
            } else {
                read_ipc_segments(
                    path,
                    &archived.segments,
                    &archived.original_indices,
                    &archived.fields,
                    archived.row_count,
                )?
            };
            tables.push(ProjectedTable {
                table: archived.table.clone(),
                original_indices: archived.original_indices.clone(),
                fields: archived.fields.clone(),
                batches,
                row_count: archived.row_count,
            });
        }
        let mut result = Self::normalize(tables, Some(manifest))?;
        result.capture_identity = capture_identity;
        result.base_archive = Some(path.canonicalize().map_err(StorageIoError::file(path))?);
        Ok(result)
    }

    /// Adopt IPC table files already written under `path` by the snapshot layer: write the archive manifest and a new
    /// lifecycle version, normalize `tables` once, then write and map the column files. IPC data is neither copied
    /// nor re-encoded. This is offline preparation, not source-snapshot authority.
    pub fn adopt_ipc_archive(path: &Path, tables: &[ProjectedTable]) -> Result<Self> {
        let mut manifest = ArchiveManifest::fresh(tables);
        for (i, archived) in manifest.tables.iter_mut().enumerate() {
            let file = path.join(format!("table-{i}.arrow"));
            archived.ipc_bytes = fs::metadata(&file).map_err(StorageIoError::file(&file))?.len();
        }
        write_new_file(
            &path.join(MANIFEST_FILE),
            &serde_json::to_vec(&manifest).map_err(StorageIoError::json(path))?,
        )?;
        write_new_file(&path.join(CAPTURE_VERSION_FILE), manifest.lifecycle_version.as_bytes())?;
        let mut result = Self::normalize(tables.to_vec(), Some(manifest))?;
        result.base_archive = Some(path.canonicalize().map_err(StorageIoError::file(path))?);
        result.write_and_map_column_files(path)
    }
}

/// A version-2 manifest must carry the archive's capture version; version 1 predates lifecycle versions.
fn check_manifest_lifecycle(path: &Path, manifest: &ArchiveManifest, capture_identity: &str) -> Result<()> {
    if !matches!(manifest.version, 1 | 2) {
        return Err(StorageIoError::archive(path, "unsupported archive version"));
    }
    if capture_identity.is_empty() || (manifest.version == 2 && manifest.lifecycle_version != capture_identity) {
        return Err(StorageIoError::archive(path, "archive lifecycle version differs"));
    }
    Ok(())
}

/// The archive's capture identity: `capture-version.txt`, or `identity.sha256` in version-1 archives.
pub(super) fn read_capture_version(archive: &Path) -> Result<String> {
    let current = archive.join(CAPTURE_VERSION_FILE);
    let path = if current.exists() {
        current
    } else {
        archive.join(LEGACY_CAPTURE_VERSION_FILE)
    };
    fs::read_to_string(&path).map_err(StorageIoError::file(&path))
}

pub(super) fn refuse_v7_only_archive(archive: &Path) -> Result<()> {
    match V7_ONLY_FILES.into_iter().find(|file| archive.join(file).exists()) {
        Some(file) => Err(StorageIoError::V7Only {
            path: archive.to_path_buf(),
            file,
        }),
        None => Ok(()),
    }
}

pub(super) fn read_metadata<T: serde::de::DeserializeOwned>(path: &Path) -> Result<T> {
    if fs::metadata(path).map_err(StorageIoError::file(path))?.len() > METADATA_LIMIT_BYTES {
        return Err(StorageIoError::archive(path, "archive metadata exceeds limit"));
    }
    serde_json::from_slice(&fs::read(path).map_err(StorageIoError::file(path))?).map_err(StorageIoError::json(path))
}

/// Write a file that must not exist yet.
pub(super) fn write_new_file(path: &Path, contents: &[u8]) -> Result<()> {
    fs::OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(path)
        .and_then(|mut file| file.write_all(contents))
        .map_err(StorageIoError::file(path))
}

/// Copy a saved archive file, refusing it if its length no longer equals the recorded extent.
fn copy_unchanged(from: &Path, to: &Path, expected_bytes: u64) -> Result<()> {
    fs::copy(from, to).map_err(StorageIoError::file(from))?;
    if fs::metadata(to).map_err(StorageIoError::file(to))?.len() != expected_bytes {
        return Err(StorageIoError::archive(
            from,
            "loaded archive source changed during re-export",
        ));
    }
    Ok(())
}
