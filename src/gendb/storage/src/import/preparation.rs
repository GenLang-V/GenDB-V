//! Preparing a workload's source once: resume the workload's own prepared root, reuse a named or registered prepared
//! root that covers the demand, extend a prepared root by only its missing columns, or import the demanded columns
//! from the original files. Every path ends in the same [`PreparedSource::open`].
//!
//! A named prepared root must declare the request's dataset, or a prefix of it: the request may append tables
//! (widening), declaring every base table identically and in the same order. A widening is always an extension, since
//! the new record declares the wider dataset. Automatic reuse of registered roots requires the same dataset.
//!
//! Reuse and extension trust the recorded source versions: lifecycle-stamped sources must still be current (checked,
//! metadata only); a saved legacy label cannot be checked and is trusted as saved. Extension additionally assumes that
//! unchanged files hold the same rows in the same order as when the base was captured, so base and new columns align
//! row by row; equal row counts are checked.

use super::dataset::{DatasetSpec, SourceVersion, all_current, check_current};
use super::demand::ColumnDemand;
use super::error::{ImportError, Result};
use super::facts::{DataFacts, compute_facts};
use super::parquet::{read_projection, stamp_and_check_files};
use super::prepared::{ARCHIVE_DIRECTORY, PreparedRecord, PreparedSource, RECORD_FILE};
use super::snapshot::{SnapshotReceipt, write_capture, write_extension};
use crate::io::{SourceColumns, fresh_lifecycle_version};
use serde::{Deserialize, Serialize};
use std::{
    fs,
    io::Write,
    path::{Path, PathBuf},
};

/// What to prepare and where.
pub struct PreparationRequest<'a> {
    pub dataset: &'a DatasetSpec,
    /// Union of the columns the workload's statements deliver.
    pub demand: &'a ColumnDemand,
    /// A prepared root to reuse (or extend) instead of looking one up or importing.
    pub base: Option<&'a Path>,
    /// Directory of prepared-root registrations: searched for automatic reuse; every new root is registered.
    pub registry: &'a Path,
    /// This workload's prepared root. When it already holds a record, the workload resumes it.
    pub root: &'a Path,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum PreparationMethod {
    /// The demanded columns were read from the original files.
    Imported,
    /// The workload's own prepared root was reopened.
    Resumed,
    /// The named prepared root covers the demand; its capture is shared.
    ReusedNamed,
    /// A registered prepared root covers the demand; its capture is shared.
    ReusedRegistered,
    /// The named prepared root lacked columns or declared fewer tables: missing columns were imported, the base's files
    /// linked.
    Extended,
}

/// How a prepared source was obtained and which files it created or linked. Every byte count is a sum of file lengths
/// from metadata: logical sizes, not device I/O.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PreparationReport {
    pub method: PreparationMethod,
    /// The reused or extended prepared root.
    pub base: Option<PathBuf>,
    /// `(table, ordinal)` of every column read from the original files.
    pub imported_columns: Vec<(String, usize)>,
    /// `(table, ordinal)` of every base column linked into an extension.
    pub linked_columns: Vec<(String, usize)>,
    /// New files: IPC tables or segments, and native column files; `written_bytes` is their sum.
    pub written_ipc_bytes: u64,
    pub written_native_bytes: u64,
    pub written_bytes: u64,
    /// Base files an extension links (symbolic links; nothing is copied or read). Reuse links the whole base archive
    /// and counts nothing here.
    pub linked_ipc_bytes: u64,
    pub linked_native_bytes: u64,
    /// Total native column-file bytes of the capture, linked or written.
    pub column_file_bytes: u64,
    /// Tables an extension's dataset appends to its base's (each with a new source version, captured or not).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub widened_tables: Vec<String>,
}

impl PreparationReport {
    fn new(method: PreparationMethod, base: Option<PathBuf>, archive: &Path) -> Result<Self> {
        Ok(Self {
            method,
            base,
            imported_columns: vec![],
            linked_columns: vec![],
            written_ipc_bytes: 0,
            written_native_bytes: 0,
            written_bytes: 0,
            linked_ipc_bytes: 0,
            linked_native_bytes: 0,
            column_file_bytes: SourceColumns::column_file_bytes(archive)?,
            widened_tables: vec![],
        })
    }

    fn set_written(&mut self, ipc: u64, native: u64) {
        self.written_ipc_bytes = ipc;
        self.written_native_bytes = native;
        self.written_bytes = ipc + native;
    }
}

/// Prepare `request.dataset` for `request.demand` once; see the module documentation for the order of attempts.
pub fn prepare_source(request: &PreparationRequest) -> Result<(PreparedSource, PreparationReport)> {
    let dataset = request.dataset.clone().with_canonical_locations()?;
    dataset.validate()?;
    request.demand.check(&dataset)?;
    fs::create_dir_all(request.registry).map_err(ImportError::file(request.registry))?;
    let lock_path = request.registry.join("preparation.lock");
    let lock = fs::OpenOptions::new()
        .create(true)
        .truncate(false)
        .read(true)
        .write(true)
        .open(&lock_path)
        .map_err(ImportError::file(&lock_path))?;
    lock.lock().map_err(ImportError::file(&lock_path))?;
    // A resumed controller reopens its own root; it never captures again or rewrites saved records.
    if request.root.join(RECORD_FILE).exists() {
        let source = PreparedSource::open(request.root, &dataset)?;
        require_covered(&source, request.demand)?;
        let report = PreparationReport::new(
            PreparationMethod::Resumed,
            source.record().base.clone(),
            source.archive(),
        )?;
        return Ok((source, report));
    }
    let (source, report) = match request.base {
        Some(base) => reuse_or_extend(&dataset, request.demand, base, request.root)?,
        None => match find_registered(request.registry, &dataset, request.demand) {
            Some(base) => {
                let (source, mut report) = reuse(&dataset, request.demand, &base, request.root)?;
                report.method = PreparationMethod::ReusedRegistered;
                (source, report)
            }
            None => import(&dataset, request.demand, request.root)?,
        },
    };
    record_data_facts(&source, &report)?;
    register(request.registry, &source)?;
    Ok((source, report))
}

/// The source data facts of a new prepared root (`facts`): computed over the columns this preparation read from the
/// original files and over every captured column its base has no facts for (a base prepared before facts existed;
/// computed once, then inherited), merged with its base's facts (an extension or a reuse copies them).
fn record_data_facts(source: &PreparedSource, report: &PreparationReport) -> Result<()> {
    let base = match &report.base {
        Some(base) => DataFacts::read(base)?,
        None => None,
    };
    let known = |table: &str, ordinal: usize| base.as_ref().is_some_and(|b| b.columns.iter().any(|c| c.table == table && c.ordinal == ordinal));
    let mut selected = report.imported_columns.clone();
    for (table, ordinals) in source.coverage() {
        for ordinal in ordinals {
            if !known(&table, ordinal) && !selected.contains(&(table.clone(), ordinal)) {
                selected.push((table.clone(), ordinal));
            }
        }
    }
    let added = compute_facts(source.columns(), &selected);
    DataFacts::write(source.root(), base, added)
}

fn require_covered(source: &PreparedSource, demand: &ColumnDemand) -> Result<()> {
    let missing = demand.missing_from(&source.coverage());
    if missing.is_empty() {
        Ok(())
    } else {
        Err(ImportError::NotCaptured { missing })
    }
}

/// Import the demanded columns from the original files into a new prepared root.
fn import(dataset: &DatasetSpec, demand: &ColumnDemand, root: &Path) -> Result<(PreparedSource, PreparationReport)> {
    let versions = stamp_and_check_files(&dataset.tables)?;
    let projection = demand.projection();
    let tables = read_projection(dataset, &versions, &projection)?;
    let root = create_root(root)?;
    let archive = root.join(ARCHIVE_DIRECTORY);
    let source_snapshot = fresh_lifecycle_version("lifecycle-v2");
    let receipt = write_capture(&archive, dataset, &versions, &source_snapshot, &tables)?;
    let written_ipc_bytes = receipt.tables.iter().map(|t| t.ipc_bytes).sum();
    let columns = SourceColumns::adopt_ipc_archive(&archive, &tables)?;
    drop(tables);
    PreparedRecord {
        format_version: PreparedRecord::FORMAT_VERSION,
        dataset: dataset.clone(),
        demand: demand.clone(),
        receipt_version: receipt.lifecycle_version,
        capture_identity: columns.capture_identity().to_string(),
        base: None,
    }
    .write_new(&root)?;
    // The normalized logical tables share the imported buffers; keep them for references instead of decoding the
    // IPC files just written.
    let logical = columns.tables().to_vec();
    drop(columns);
    let source = PreparedSource::open(&root, dataset)?.with_logical_tables(&logical);
    let mut report = PreparationReport::new(PreparationMethod::Imported, None, source.archive())?;
    report.imported_columns = columns_of(&projection);
    // Every IPC and native file of an import is new.
    report.set_written(written_ipc_bytes, report.column_file_bytes);
    Ok((source, report))
}

/// Reuse the named prepared root when it declares the same dataset and covers the demand. Otherwise extend it by the
/// missing columns; a request that appends tables to the base's declaration (a widening) is always extended, so that
/// the new record and receipt declare the wider dataset. Any other declaration change is refused.
fn reuse_or_extend(
    dataset: &DatasetSpec,
    demand: &ColumnDemand,
    base: &Path,
    root: &Path,
) -> Result<(PreparedSource, PreparationReport)> {
    let base = base.canonicalize().map_err(ImportError::file(base))?;
    let base_record = PreparedRecord::read(&base)?;
    let appended = dataset.appended_to(&base_record.dataset).map_err(|reason| {
        ImportError::prepared(
            &base,
            format!("the request must declare the prepared workload's dataset, optionally followed by new tables: {reason}"),
        )
    })?;
    let base_receipt = SnapshotReceipt::read(&canonical_archive(&base)?, &base_record.receipt_version)?;
    if base_receipt.dataset != base_record.dataset {
        return Err(ImportError::prepared(&base, "snapshot dataset differs from the prepared record"));
    }
    check_current(&base_record.dataset, &base_receipt.source_versions)?;
    let missing = demand.missing_from(&base_receipt.coverage());
    if appended.is_empty() && missing.is_empty() {
        reuse(dataset, demand, &base, root)
    } else {
        extend(dataset, demand, &base, &base_record, &base_receipt, &missing, root)
    }
}

/// A new prepared root sharing `base`'s capture: `inputs` links the base archive; only the record is written.
fn reuse(
    dataset: &DatasetSpec,
    demand: &ColumnDemand,
    base: &Path,
    root: &Path,
) -> Result<(PreparedSource, PreparationReport)> {
    let base_source = PreparedSource::open(base, dataset)?;
    require_covered(&base_source, demand)?;
    let root = create_root(root)?;
    let link = root.join(ARCHIVE_DIRECTORY);
    std::os::unix::fs::symlink(base_source.archive(), &link).map_err(ImportError::file(&link))?;
    PreparedRecord {
        format_version: PreparedRecord::FORMAT_VERSION,
        dataset: dataset.clone(),
        demand: demand.clone(),
        receipt_version: base_source.record().receipt_version.clone(),
        capture_identity: base_source.capture_identity().to_string(),
        base: Some(base_source.root().to_path_buf()),
    }
    .write_new(&root)?;
    drop(base_source);
    let source = PreparedSource::open(&root, dataset)?;
    let report = PreparationReport::new(
        PreparationMethod::ReusedNamed,
        source.record().base.clone(),
        source.archive(),
    )?;
    Ok((source, report))
}

/// `extension.json` of an extended prepared root: what was linked and built, and what extension assumes.
#[derive(Serialize)]
struct ExtensionRecord<'a> {
    format_version: u32,
    base_prepared_root: &'a Path,
    base_archive: &'a Path,
    base_receipt_version: &'a str,
    base_capture_identity: &'a str,
    receipt_version: &'a str,
    capture_identity: &'a str,
    source_snapshot: &'a str,
    demand: &'a ColumnDemand,
    built_columns: &'a [(String, usize)],
    linked_base_columns: &'a [(String, usize)],
    /// File lengths from metadata (not device I/O), as in [`PreparationReport`].
    written_ipc_bytes: u64,
    written_native_bytes: u64,
    written_bytes: u64,
    linked_ipc_bytes: u64,
    linked_native_bytes: u64,
    legacy_source_label_tables: &'a [String],
    /// Tables the request's dataset appends to the base's; each has a new source version, captured or not.
    widened_tables: &'a [String],
    scope: &'static str,
    assumptions: [&'static str; 3],
}

/// A new prepared root holding `base`'s capture plus the `missing` columns imported from the current source files,
/// declaring `dataset`: the base's dataset, possibly followed by appended tables (checked by [`reuse_or_extend`]).
/// Every appended table, demanded or not, is checked against its files' footers and stamped, so the new receipt has a
/// source version for every declared table; base tables keep their recorded versions. Every applicability check and
/// the source read precede the first write.
fn extend(
    dataset: &DatasetSpec,
    demand: &ColumnDemand,
    base: &Path,
    base_record: &PreparedRecord,
    base_receipt: &SnapshotReceipt,
    missing: &[(String, Vec<usize>)],
    root: &Path,
) -> Result<(PreparedSource, PreparationReport)> {
    let base_archive = canonical_archive(base)?;
    let appended = &dataset.tables[base_record.dataset.tables.len()..];
    let widened_tables: Vec<String> = appended.iter().map(|t| t.name.clone()).collect();
    let appended_versions = stamp_and_check_files(appended)?;
    let mut legacy_tables = vec![];
    let mut current = vec![];
    for (table, _) in missing {
        if let Some(stamp) = appended_versions.iter().find(|v| v.table == *table) {
            current.push(stamp.clone());
            continue;
        }
        let declared = dataset
            .table(table)
            .ok_or_else(|| ImportError::demand(table, "table is not declared"))?;
        let prior = base_receipt
            .source_versions
            .iter()
            .find(|v| v.table == *table)
            .ok_or_else(|| ImportError::prepared(&base_archive, "prepared base source version absent"))?;
        if prior.locations != declared.locations {
            return Err(ImportError::prepared(
                &base_archive,
                "prepared base source locations differ",
            ));
        }
        let stamp = SourceVersion::stamp(declared)?;
        if prior.is_lifecycle_stamp() {
            if prior.version != stamp.version {
                return Err(ImportError::SourceChanged { table: table.clone() });
            }
        } else {
            legacy_tables.push(table.clone());
        }
        current.push(stamp);
    }
    let added = read_projection(dataset, &current, missing)?;
    let root = create_root(root)?;
    let archive = root.join(ARCHIVE_DIRECTORY);
    let source_versions = base_receipt.source_versions.iter().cloned().chain(appended_versions).collect();
    let (receipt, layout, ipc_bytes) = write_extension(
        &base_archive,
        base_receipt,
        &base_record.capture_identity,
        dataset,
        source_versions,
        &added,
        &archive,
    )?;
    let extension = SourceColumns::adopt_extended_archive(&base_archive, &archive, &layout, added)?;
    // `ArchiveExtension` counts native column-file bytes only (its field names are kept: `crate::io` is part of the
    // runtime identity).
    let (linked_native_bytes, written_native_bytes) = (extension.linked_bytes, extension.written_bytes);
    let record = PreparedRecord {
        format_version: PreparedRecord::FORMAT_VERSION,
        dataset: dataset.clone(),
        demand: demand.clone(),
        receipt_version: receipt.lifecycle_version.clone(),
        capture_identity: extension.capture_identity.clone(),
        base: Some(base.to_path_buf()),
    };
    write_new_json(
        &root.join("extension.json"),
        &ExtensionRecord {
            format_version: 1,
            base_prepared_root: base,
            base_archive: &base_archive,
            base_receipt_version: &base_record.receipt_version,
            base_capture_identity: &base_record.capture_identity,
            receipt_version: &record.receipt_version,
            capture_identity: &record.capture_identity,
            source_snapshot: &receipt.source_snapshot,
            demand,
            built_columns: &extension.built_columns,
            linked_base_columns: &extension.reused_columns,
            written_ipc_bytes: ipc_bytes.written,
            written_native_bytes,
            written_bytes: ipc_bytes.written + written_native_bytes,
            linked_ipc_bytes: ipc_bytes.linked,
            linked_native_bytes,
            legacy_source_label_tables: &legacy_tables,
            widened_tables: &widened_tables,
            scope: "base IPC and native column files are linked unchanged; only built_columns were read from the declared source files, in their file row order",
            assumptions: [
                "Checked: the request declares every base table identically and in the same order (schema with column order, types and nullability, table names, source locations, format), optionally followed by widened_tables whose file footers match their declaration; equal row counts of every extended table; and for lifecycle-stamped base versions equality with the current file stamp (device, inode, size, mtime, ctime). These are metadata checks, not proof of byte equality.",
                "Assumed: the source files hold the same rows in the same order as when the base was captured, so base and built columns align row by row.",
                "Tables in legacy_source_label_tables carry a saved legacy label and no lifecycle stamp; their source was not rescanned or hashed, so equality with the base capture rests on the unchanged declared location and equal row count only.",
            ],
        },
    )?;
    record.write_new(&root)?;
    let source = PreparedSource::open(&root, dataset)?;
    let mut report = PreparationReport::new(PreparationMethod::Extended, Some(base.to_path_buf()), source.archive())?;
    report.imported_columns = extension.built_columns;
    report.linked_columns = extension.reused_columns;
    report.set_written(ipc_bytes.written, written_native_bytes);
    report.linked_ipc_bytes = ipc_bytes.linked;
    report.linked_native_bytes = linked_native_bytes;
    report.widened_tables = widened_tables;
    Ok((source, report))
}

/// `registry/prepared-<pid>-<nanos>.json`: a prepared root offered for automatic reuse. Format 1 (earlier version) also lists the
/// SQL coverage statements the root was prepared for; they are informational and not written any more.
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Registration {
    format_version: u32,
    prepared_root: PathBuf,
    dataset: DatasetSpec,
    sources: Vec<SourceVersion>,
    receipt_version: String,
    #[serde(rename = "native_version")]
    capture_identity: String,
    coverage: Vec<(String, Vec<usize>)>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    queries: Vec<String>,
}

/// The first registered prepared root (by path) for the same dataset whose every source is lifecycle-stamped and
/// current, whose coverage includes the demand, and whose saved record still names the registered versions.
/// Unreadable registrations are skipped.
fn find_registered(registry: &Path, dataset: &DatasetSpec, demand: &ColumnDemand) -> Option<PathBuf> {
    let mut candidates: Vec<Registration> = fs::read_dir(registry)
        .ok()?
        .filter_map(|entry| {
            let path = entry.ok()?.path();
            if path.extension().and_then(|x| x.to_str()) != Some("json") {
                return None;
            }
            serde_json::from_slice(&fs::read(path).ok()?).ok()
        })
        .filter(|r: &Registration| {
            matches!(r.format_version, 1 | 2)
                && r.dataset == *dataset
                && demand.missing_from(&r.coverage).is_empty()
                && all_current(dataset, &r.sources)
        })
        .collect();
    candidates.sort_by(|a, b| a.prepared_root.cmp(&b.prepared_root));
    candidates.into_iter().find_map(|r| {
        let saved = PreparedRecord::read(&r.prepared_root).ok()?;
        (saved.capture_identity == r.capture_identity && saved.receipt_version == r.receipt_version)
            .then_some(r.prepared_root)
    })
}

fn register(registry: &Path, source: &PreparedSource) -> Result<()> {
    let registration = Registration {
        format_version: 2,
        prepared_root: source.root().to_path_buf(),
        dataset: source.dataset().clone(),
        sources: source.source_versions().to_vec(),
        receipt_version: source.record().receipt_version.clone(),
        capture_identity: source.capture_identity().to_string(),
        coverage: source.coverage(),
        queries: vec![],
    };
    let name = format!("prepared-{}-{}.json", std::process::id(), nanos_since_epoch());
    write_new_json(&registry.join(name), &registration)
}

fn nanos_since_epoch() -> u128 {
    std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos()
}

/// Create a new, not yet existing prepared root and return its canonical path.
fn create_root(root: &Path) -> Result<PathBuf> {
    fs::create_dir(root).map_err(ImportError::file(root))?;
    root.canonicalize().map_err(ImportError::file(root))
}

fn canonical_archive(root: &Path) -> Result<PathBuf> {
    let archive = root.join(ARCHIVE_DIRECTORY);
    archive.canonicalize().map_err(ImportError::file(&archive))
}

fn columns_of(projection: &[(String, Vec<usize>)]) -> Vec<(String, usize)> {
    projection
        .iter()
        .flat_map(|(t, o)| o.iter().map(move |&i| (t.clone(), i)))
        .collect()
}

fn write_new_json(path: &Path, value: &impl Serialize) -> Result<()> {
    let bytes = serde_json::to_vec_pretty(value).map_err(ImportError::json(path))?;
    fs::OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(path)
        .and_then(|mut file| file.write_all(&bytes))
        .map_err(ImportError::file(path))
}
