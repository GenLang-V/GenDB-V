//! The `native-buffers/` column files of a base archive: every normalized buffer written once as a read-only file and
//! mapped read-only by every later execution, so isolated workers share one preparation and never decode Arrow.
//! Extended archives link their base's files by name. The format is unchanged from the earlier GenDB version.

use super::archive::{
    ArchiveManifest, ArchiveView, ArchivedTable, fresh_lifecycle_version, read_capture_version, read_metadata,
    refuse_v7_only_archive, write_new_file,
};
use super::column::{
    ColumnBinding, NATIVE_TYPE_CARDINALITY, NativeColumn, ValueLayout, extent, native_type_tag, utf8_offsets_extent,
};
use super::error::{Result, StorageIoError};
use super::ipc::ArchiveTableLayout;
use super::read_only::ReadOnlyBuffer;
use super::source_columns::{ProjectedTable, SourceColumns};
use gendb_artifacts::ColumnSpec;
use serde::{Deserialize, Serialize};
use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    sync::Arc,
};

const COLUMN_FILES_DIRECTORY: &str = "native-buffers";
const COLUMN_FILES_MANIFEST: &str = "manifest.json";

/// One buffer file, local to the column-files directory.
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct BufferFile {
    file: String,
    bytes: usize,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ColumnFiles {
    binding: ColumnBinding,
    type_tag: i32,
    values: Option<BufferFile>,
    offsets: Option<BufferFile>,
    bytes: Option<BufferFile>,
    validity: Option<BufferFile>,
}

impl ColumnFiles {
    fn buffer_bytes(&self) -> u64 {
        [&self.values, &self.offsets, &self.bytes, &self.validity]
            .into_iter()
            .flatten()
            .map(|b| b.bytes as u64)
            .sum()
    }
}

/// `native-buffers/manifest.json`.
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ColumnFilesManifest {
    version: u32,
    /// Host byte order of the buffers; mapping on a host of the other order is refused.
    little_endian: bool,
    /// Capture identity of the archive the files belong to.
    capture: String,
    manifest: ArchiveManifest,
    columns: Vec<ColumnFiles>,
}

impl ColumnFilesManifest {
    fn read(archive: &Path) -> Result<Self> {
        let path = archive.join(COLUMN_FILES_DIRECTORY).join(COLUMN_FILES_MANIFEST);
        let manifest: Self = read_metadata(&path)?;
        if manifest.version != 1
            || manifest.little_endian != cfg!(target_endian = "little")
            || read_capture_version(archive)? != manifest.capture
        {
            return Err(StorageIoError::archive(archive, "column files lifecycle/ABI differs"));
        }
        Ok(manifest)
    }
}

/// Columns of an extended archive: linked from the base or newly written.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ArchiveExtension {
    pub capture_identity: String,
    /// `(table, declared ordinal)` of each column linked from the base.
    pub reused_columns: Vec<(String, usize)>,
    /// `(table, declared ordinal)` of each column normalized and written for the extension.
    pub built_columns: Vec<(String, usize)>,
    pub linked_bytes: u64,
    pub written_bytes: u64,
}

impl SourceColumns {
    /// Write the column files once (when absent), then map them. The mapped columns keep this value's logical tables
    /// for the parent's independent reference checks.
    pub fn write_and_map_column_files(&self, path: &Path) -> Result<Self> {
        self.write_column_files(path)?;
        let mut mapped = Self::map_archive(path)?;
        if mapped.capture_identity != self.capture_identity || mapped.bindings != self.bindings {
            return Err(StorageIoError::archive(
                path,
                "shared native archive lifecycle/interface differs",
            ));
        }
        mapped.tables = self.tables.clone();
        Ok(mapped)
    }

    /// Total bytes of the buffer files listed by an archive's column-files manifest (metadata only).
    pub fn column_file_bytes(path: &Path) -> Result<u64> {
        let manifest: ColumnFilesManifest =
            read_metadata(&path.join(COLUMN_FILES_DIRECTORY).join(COLUMN_FILES_MANIFEST))?;
        Ok(manifest.columns.iter().map(ColumnFiles::buffer_bytes).sum())
    }

    /// Write the base archive's column files unless they exist; views have none.
    pub(super) fn write_column_files(&self, path: &Path) -> Result<()> {
        let directory = path.join(COLUMN_FILES_DIRECTORY);
        if self.view.is_some() || directory.join(COLUMN_FILES_MANIFEST).exists() {
            return Ok(());
        }
        fs::create_dir(&directory).map_err(StorageIoError::file(&directory))?;
        let columns = self
            .descriptors
            .iter()
            .zip(&self.bindings)
            .enumerate()
            .map(|(index, (descriptor, binding))| write_buffer_files(&directory, index, descriptor, binding))
            .collect::<Result<Vec<_>>>()?;
        let manifest = ColumnFilesManifest {
            version: 1,
            little_endian: cfg!(target_endian = "little"),
            capture: self.capture_identity.clone(),
            manifest: self.manifest.clone(),
            columns,
        };
        let manifest_path = directory.join(COLUMN_FILES_MANIFEST);
        write_new_file(
            &manifest_path,
            &serde_json::to_vec(&manifest).map_err(StorageIoError::json(&manifest_path))?,
        )
    }

    /// Open an archive for execution: map its column files read-only (a view: its base's, then project), never
    /// decoding Arrow. An archive without column files is decoded once instead. Logical tables of a mapping have no
    /// batches. Checks cover lifecycle, declared types and file extents, not values.
    pub fn map_archive(path: &Path) -> Result<Self> {
        refuse_v7_only_archive(path)?;
        if path.join("view.json").exists() {
            return Self::map_view_archive(path);
        }
        if !path.join(COLUMN_FILES_DIRECTORY).join(COLUMN_FILES_MANIFEST).exists() {
            return Ok(Self::decode_archive(path)?.read_only()?.0);
        }
        let files = ColumnFilesManifest::read(path)?;
        let directory = path.join(COLUMN_FILES_DIRECTORY);
        let mut buffers = vec![];
        let mut descriptors = vec![];
        let mut bindings = vec![];
        for column in files.columns {
            let (type_tag, rows, nullable) = check_column(path, &files.manifest, &column, descriptors.len())?;
            let binding = column.binding;
            let mut map = |file: &Option<BufferFile>| -> Result<*const u8> {
                let Some(file) = file else { return Ok(std::ptr::null()) };
                if Path::new(&file.file).components().count() != 1 {
                    return Err(StorageIoError::archive(path, "native buffer path is not local"));
                }
                let buffer = Arc::new(ReadOnlyBuffer::map_file(&directory.join(&file.file), file.bytes)?);
                let pointer = buffer.as_ptr();
                buffers.push(buffer);
                Ok(pointer)
            };
            descriptors.push(NativeColumn {
                type_tag,
                nullable: i32::from(nullable),
                len: i64::try_from(rows).map_err(|_| StorageIoError::Overflow("row count"))?,
                values: map(&column.values)?,
                offsets: map(&column.offsets)?.cast(),
                bytes: map(&column.bytes)?,
                validity: map(&column.validity)?,
            });
            bindings.push(binding);
        }
        let tables = files
            .manifest
            .tables
            .iter()
            .map(logical_table_without_batches)
            .collect();
        let mapped = Self {
            tables,
            bindings,
            descriptors,
            heap_columns: Default::default(),
            read_only_buffers: buffers,
            read_only_descriptors: None,
            manifest: files.manifest,
            capture_identity: files.capture,
            base_archive: Some(path.canonicalize().map_err(StorageIoError::file(path))?),
            view: None,
        };
        Ok(mapped.read_only()?.0)
    }

    fn map_view_archive(path: &Path) -> Result<Self> {
        let view: ArchiveView = read_metadata(&path.join("view.json"))?;
        if view.version != 1 || view.source.join("view.json").exists() {
            return Err(StorageIoError::archive(path, "invalid nested execution view"));
        }
        let base = Self::map_archive(&view.source)?;
        if base.capture_identity != view.source_identity {
            return Err(StorageIoError::archive(path, "execution view source version differs"));
        }
        let result = base.project(&view.projection)?.read_only()?.0;
        if read_capture_version(path)? != result.capture_identity {
            return Err(StorageIoError::archive(path, "execution view lifecycle differs"));
        }
        Ok(result)
    }

    /// Derive an extended archive at `path` from a prepared base archive. Base column files are linked by name (never
    /// read, converted or copied); only the `added` columns are normalized and written, once. `layout` comes from the
    /// snapshot layer, which already placed the IPC files under `path`.
    pub fn adopt_extended_archive(
        base: &Path,
        path: &Path,
        layout: &[ArchiveTableLayout],
        added: Vec<ProjectedTable>,
    ) -> Result<ArchiveExtension> {
        let base = base.canonicalize().map_err(StorageIoError::file(base))?;
        let base_directory = base.join(COLUMN_FILES_DIRECTORY);
        let base_files = ColumnFilesManifest::read(&base)?;
        let added = Self::from_projected(added)?;
        let names = layout.iter().map(|t| t.table.as_str()).collect::<BTreeSet<_>>();
        let mut members = base_files
            .manifest
            .tables
            .iter()
            .map(|t| t.table.as_str())
            .chain(added.tables.iter().map(|t| t.table.as_str()));
        if names.len() != layout.len() || members.any(|t| !names.contains(t)) {
            return Err(StorageIoError::Shape("derived archive table membership differs"));
        }
        let directory = path.join(COLUMN_FILES_DIRECTORY);
        fs::create_dir(&directory).map_err(StorageIoError::file(&directory))?;
        let mut extension = ArchiveExtension::default();
        let mut columns = vec![];
        for table in layout {
            let prior = base_files.manifest.tables.iter().find(|t| t.table == table.table);
            let new = added.tables.iter().find(|t| t.table == table.table);
            check_extended_table(table, prior, new)?;
            if table.fields.is_empty() {
                let (binding, _) = ColumnBinding::row_count_only(&table.table, columns.len(), table.row_count)?;
                columns.push(ColumnFiles {
                    binding,
                    type_tag: NATIVE_TYPE_CARDINALITY,
                    values: None,
                    offsets: None,
                    bytes: None,
                    validity: None,
                });
                continue;
            }
            for (ordinal, field) in table.original_indices.iter().zip(&table.fields) {
                let index = columns.len();
                let base_column = base_files
                    .columns
                    .iter()
                    .find(|c| c.binding.table == table.table && c.binding.original_index == Some(*ordinal));
                if let Some(base_column) = base_column {
                    if base_column.binding.field.as_ref() != Some(field)
                        || base_column.binding.row_count != table.row_count
                    {
                        return Err(StorageIoError::archive(&base, "base native column binding differs"));
                    }
                    let mut link = |role: &str, file: &Option<BufferFile>| -> Result<Option<BufferFile>> {
                        let Some(file) = file else { return Ok(None) };
                        let name = format!("column-{index}-{role}.bin");
                        link_base_buffer(&base_directory, file, &directory.join(&name))?;
                        extension.linked_bytes += file.bytes as u64;
                        Ok(Some(BufferFile {
                            file: name,
                            bytes: file.bytes,
                        }))
                    };
                    columns.push(ColumnFiles {
                        binding: ColumnBinding {
                            descriptor_index: index,
                            ..base_column.binding.clone()
                        },
                        type_tag: base_column.type_tag,
                        values: link("values", &base_column.values)?,
                        offsets: link("offsets", &base_column.offsets)?,
                        bytes: link("bytes", &base_column.bytes)?,
                        validity: link("validity", &base_column.validity)?,
                    });
                    extension.reused_columns.push((table.table.clone(), *ordinal));
                } else {
                    let binding = added
                        .bindings
                        .iter()
                        .find(|b| b.table == table.table && b.original_index == Some(*ordinal))
                        .ok_or(StorageIoError::Shape(
                            "derived archive column has no base or added source",
                        ))?;
                    if binding.field.as_ref() != Some(field) {
                        return Err(StorageIoError::Shape("added native column binding differs"));
                    }
                    let files = write_buffer_files(
                        &directory,
                        index,
                        &added.descriptors[binding.descriptor_index],
                        &ColumnBinding {
                            descriptor_index: index,
                            ..binding.clone()
                        },
                    )?;
                    extension.written_bytes += files.buffer_bytes();
                    columns.push(files);
                    extension.built_columns.push((table.table.clone(), *ordinal));
                }
            }
        }
        let manifest = ArchiveManifest {
            version: 2,
            lifecycle_version: fresh_lifecycle_version("native-v2"),
            tables: layout
                .iter()
                .map(|t| ArchivedTable {
                    table: t.table.clone(),
                    original_indices: t.original_indices.clone(),
                    fields: t.fields.clone(),
                    row_count: t.row_count,
                    ipc_bytes: t.ipc_bytes,
                    saved_ipc_sha256: String::new(),
                    segments: t.segments.clone(),
                })
                .collect(),
        };
        extension.capture_identity = manifest.lifecycle_version.clone();
        let files = ColumnFilesManifest {
            version: 1,
            little_endian: cfg!(target_endian = "little"),
            capture: manifest.lifecycle_version.clone(),
            manifest,
            columns,
        };
        write_new_file(
            &path.join("manifest.json"),
            &serde_json::to_vec(&files.manifest).map_err(StorageIoError::json(path))?,
        )?;
        write_new_file(&path.join("capture-version.txt"), files.capture.as_bytes())?;
        let files_path = directory.join(COLUMN_FILES_MANIFEST);
        write_new_file(
            &files_path,
            &serde_json::to_vec(&files).map_err(StorageIoError::json(&files_path))?,
        )?;
        Ok(extension)
    }
}

/// An extended table holds exactly its base columns plus its added columns, all with the same row count.
fn check_extended_table(
    table: &ArchiveTableLayout,
    prior: Option<&ArchivedTable>,
    new: Option<&ProjectedTable>,
) -> Result<()> {
    let mut expected = prior.map_or(vec![], |t| t.original_indices.clone());
    for ordinal in new.map_or(&[][..], |t| &t.original_indices) {
        if expected.contains(ordinal) {
            return Err(StorageIoError::Shape(
                "added column is already prepared in the base archive",
            ));
        }
        expected.push(*ordinal);
    }
    expected.sort_unstable();
    if table.original_indices != expected
        || table.original_indices.len() != table.fields.len()
        || prior.is_some_and(|t| t.row_count != table.row_count)
        || new.is_some_and(|t| t.row_count != table.row_count)
    {
        return Err(StorageIoError::Shape(
            "derived archive ordinals/row extent differ from base and added columns",
        ));
    }
    Ok(())
}

/// The checks a mapping makes of one column of a column-files manifest, without mapping: its table and row count,
/// its descriptor position, its type tag against the declared field, and every buffer extent. Returns the type tag,
/// the row count and whether the column is nullable.
fn check_column(path: &Path, manifest: &ArchiveManifest, column: &ColumnFiles, position: usize) -> Result<(i32, usize, bool)> {
    let binding = &column.binding;
    let table = manifest
        .tables
        .iter()
        .find(|t| t.table == binding.table)
        .ok_or(StorageIoError::archive(path, "native sidecar table absent"))?;
    let rows = binding.row_count;
    if rows != table.row_count {
        return Err(StorageIoError::archive(path, "native sidecar row binding differs"));
    }
    if binding.descriptor_index != position {
        return Err(StorageIoError::archive(path, "native sidecar descriptor binding differs"));
    }
    let type_tag = binding.field.as_ref().map_or(Ok(NATIVE_TYPE_CARDINALITY), |f| native_type_tag(f.ty))?;
    if column.type_tag != type_tag {
        return Err(StorageIoError::archive(path, "native sidecar type tag differs from the declared field"));
    }
    let nullable = binding.field.as_ref().is_some_and(|f| f.nullable);
    let expected_extent = |file: &Option<BufferFile>, bytes: Option<usize>| file.as_ref().map(|f| f.bytes) == bytes;
    let extents_match = match ValueLayout::of_tag(type_tag).expect("canonical tag") {
        ValueLayout::Fixed { width } => expected_extent(&column.values, Some(extent(rows, width)?)),
        ValueLayout::Utf8 => expected_extent(&column.offsets, Some(utf8_offsets_extent(rows)?)),
        ValueLayout::RowCountOnly => true,
    } && (!nullable || expected_extent(&column.validity, Some(rows)));
    if !extents_match {
        return Err(StorageIoError::archive(path, "native sidecar buffer extent differs"));
    }
    Ok((type_tag, rows, nullable))
}

/// One buffer file of a captured column: the file as the archive names it (`<archive>/native-buffers/<file>`; an
/// extended archive's name may be a symbolic link to its base's file) and its byte length from the manifest.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CapturedBuffer {
    pub path: PathBuf,
    pub bytes: u64,
}

/// The canonical buffer files of one captured column: `values` for a fixed-width column, `offsets` (i64, rows + 1) and
/// `bytes` for text, and for a nullable column its `validity` (one byte per row, 1 valid, 0 NULL; the value bytes under
/// a NULL row are unspecified).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CapturedColumn {
    pub table: String,
    /// Ordinal of the column in the declared source table.
    pub ordinal: usize,
    pub field: ColumnSpec,
    pub rows: usize,
    pub values: Option<CapturedBuffer>,
    pub offsets: Option<CapturedBuffer>,
    pub bytes: Option<CapturedBuffer>,
    /// Present exactly for a nullable column (absent from the serialized form otherwise).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub validity: Option<CapturedBuffer>,
}

impl SourceColumns {
    /// The captured columns of the archive `path` with their buffer files (a nullable column with its validity file),
    /// from its column-files manifest only: nothing is mapped, read or hashed. Each column passes the checks a mapping
    /// makes ([`Self::map_archive`]: lifecycle and byte order, declared type tag, row count, buffer extents, the
    /// validity extent of a nullable column); a view and an archive without column files are refused.
    pub fn captured_columns(path: &Path) -> Result<Vec<CapturedColumn>> {
        refuse_v7_only_archive(path)?;
        if path.join("view.json").exists() || !path.join(COLUMN_FILES_DIRECTORY).join(COLUMN_FILES_MANIFEST).exists() {
            return Err(StorageIoError::archive(path, "captured column files need an archive with its own column files"));
        }
        let files = ColumnFilesManifest::read(path)?;
        let directory = path.join(COLUMN_FILES_DIRECTORY);
        let mut columns = vec![];
        for (position, column) in files.columns.iter().enumerate() {
            let (_, rows, nullable) = check_column(path, &files.manifest, column, position)?;
            let (Some(ordinal), Some(field)) = (column.binding.original_index, column.binding.field.clone()) else { continue };
            let buffer = |file: &Option<BufferFile>| -> Result<Option<CapturedBuffer>> {
                let Some(file) = file else { return Ok(None) };
                if Path::new(&file.file).components().count() != 1 {
                    return Err(StorageIoError::archive(path, "native buffer path is not local"));
                }
                Ok(Some(CapturedBuffer { path: directory.join(&file.file), bytes: file.bytes as u64 }))
            };
            columns.push(CapturedColumn {
                table: column.binding.table.clone(),
                ordinal,
                field,
                rows,
                values: buffer(&column.values)?,
                offsets: buffer(&column.offsets)?,
                bytes: buffer(&column.bytes)?,
                validity: if nullable { buffer(&column.validity)? } else { None },
            });
        }
        Ok(columns)
    }
}

/// Symlink `link` to a base buffer file after checking its path is local and its length is the recorded one.
fn link_base_buffer(base_directory: &Path, file: &BufferFile, link: &PathBuf) -> Result<()> {
    if Path::new(&file.file).components().count() != 1 {
        return Err(StorageIoError::archive(
            base_directory,
            "native buffer path is not local",
        ));
    }
    let source = base_directory.join(&file.file);
    let target = source.canonicalize().map_err(StorageIoError::file(&source))?;
    if fs::metadata(&target).map_err(StorageIoError::file(&target))?.len() != file.bytes as u64 {
        return Err(StorageIoError::archive(&target, "base native buffer extent differs"));
    }
    std::os::unix::fs::symlink(&target, link).map_err(StorageIoError::file(link))
}

/// Write one canonical descriptor's buffers as read-only files `column-<index>-<role>.bin`.
fn write_buffer_files(
    directory: &Path,
    index: usize,
    descriptor: &NativeColumn,
    binding: &ColumnBinding,
) -> Result<ColumnFiles> {
    let rows = binding.row_count;
    let write = |role: &str, pointer: *const u8, len: usize| -> Result<Option<BufferFile>> {
        if pointer.is_null() {
            return Ok(None);
        }
        let file = format!("column-{index}-{role}.bin");
        let path = directory.join(&file);
        // SAFETY: `pointer` and `len` come from a canonical descriptor owned by the caller's columns.
        write_new_file(&path, unsafe { std::slice::from_raw_parts(pointer, len) })?;
        let mut permissions = fs::metadata(&path).map_err(StorageIoError::file(&path))?.permissions();
        permissions.set_readonly(true);
        fs::set_permissions(&path, permissions).map_err(StorageIoError::file(&path))?;
        Ok(Some(BufferFile { file, bytes: len }))
    };
    let layout = ValueLayout::of_tag(descriptor.type_tag)
        .ok_or(StorageIoError::Shape("native sidecar requires canonical descriptors"))?;
    let (values, offsets, bytes) = match layout {
        ValueLayout::Fixed { width } => (write("values", descriptor.values, extent(rows, width)?)?, None, None),
        ValueLayout::Utf8 => {
            // SAFETY: a canonical UTF-8 descriptor has `rows + 1` offsets; the last one ends the value bytes.
            let end = unsafe { *descriptor.offsets.add(rows) };
            let value_bytes = usize::try_from(end).map_err(|_| StorageIoError::Overflow("string bytes"))?;
            (
                None,
                write("offsets", descriptor.offsets.cast(), utf8_offsets_extent(rows)?)?,
                write("bytes", descriptor.bytes, value_bytes)?,
            )
        }
        ValueLayout::RowCountOnly => (None, None, None),
    };
    let validity = if descriptor.nullable != 0 {
        write("validity", descriptor.validity, rows)?
    } else {
        None
    };
    Ok(ColumnFiles {
        binding: binding.clone(),
        type_tag: descriptor.type_tag,
        values,
        offsets,
        bytes,
        validity,
    })
}

/// The logical table of a mapped archive: declared shape only, no decoded batches.
fn logical_table_without_batches(table: &ArchivedTable) -> ProjectedTable {
    ProjectedTable {
        table: table.table.clone(),
        original_indices: table.original_indices.clone(),
        fields: table.fields.clone(),
        batches: vec![],
        row_count: table.row_count,
    }
}
