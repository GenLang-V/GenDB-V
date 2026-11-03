//! The asset of a fixed flat storage package (`obligations::flat_storage`, `storage_policy` `fixed_flat`), published
//! from the capture's own canonical column files instead of a run of its builder: the trusted host item
//! [`FLAT_CAPTURE_PARTS`].
//!
//! The flat layout is regenerated from the package's declaration, so a package whose sources are not the generator's
//! output for its declaration is refused (`flat_storage_not_generated`). Every part is matched to one captured column
//! file from the capture's column-files manifest (metadata only) and checked against the asset key: table, ordinal,
//! declared field and element type, row count, element count against the file length, a read-only regular file. A
//! nullable column's validity part is the capture's validity file of that column (one byte per row).
//! Nothing is read for a hard link; a file on another filesystem than the library is copied once, unchanged (free space
//! for the copies is checked first). An earlier flat asset's copy of the same capture file may be named in `reuse` and is
//! then hard-linked instead of copied again.

use super::{AssetBuildSlot, StorageAsset, record_error, store_error};
use crate::admission::AdmissionError;
use crate::obligations::{flat_storage_of, DeclaredColumn, DeclaredSource, DeclaredType, FlatBuffer, FlatElem, FlatStorage};
use gendb_artifacts::{ColType, ColumnSpec};
use gendb_artifacts::asset_directory::remove_build_directory;
use gendb_artifacts::verus::{self as records, BuiltParts, VerusBuildV1, VerusSourceOwnerV1};
use gendb_artifacts::ObjectStore;
use gendb_storage::io::{CapturedBuffer, PartElem, PartFilesWriter, PartPlacement, PartsFormat, SourceColumns, STORAGE_MARGIN_BYTES, free_bytes_at};
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::time::Instant;

/// Record kind of the evidence of a flat storage asset published from the capture's column files.
pub const FLAT_CAPTURE_ASSET_KIND: &str = "gendb.verus.flat-capture-asset.v1";

/// The trusted host item of flat storage assets, `(id, statement)`: in the TCB records of flat storage packages and of
/// query packages over flat assets, and in every flat asset's evidence.
pub const FLAT_CAPTURE_PARTS: (&str, &str) = (
    "flat_capture_parts",
    "gendb_verification::admission::storage::AssetBuildSlot::publish_flat_capture_parts with \
     gendb_storage::io::PartFilesWriter::add_file_part: the asset of a fixed flat storage package (its sources equal to \
     obligations::flat_storage generated from its declaration) for a capture is not built by running its builder. Part i \
     is the capture's canonical column file of generated part i (values; or text offsets and bytes; and after a \
     nullable column's value parts its validity, one byte per row, 0 for a NULL row), named by the \
     capture's column-files manifest: a hard link to the resolved file, or a byte copy when the library lies on another \
     filesystem; matched from metadata only (table, ordinal, declared field, element type, the asset key's row count, \
     element count against the file length, a read-only regular file); never read for a link, hashed or rescanned. \
     Mapped as parts (stored_parts_round_trip), these files are the buffers the binder delivers from the same capture \
     (storage_source_columns: the same files in the same raw little-endian element format), so the parts' view is \
     flat_parts of the delivered source, which the package's verified lemma_delivered_buffers_represent proves to \
     represent the delivered table. The builder is verified and compiled with the package but not executed for such an \
     asset.",
);

/// What the evidence says of the builder of a flat asset.
const BUILDER_NOT_EXECUTED: &str = "the package's builder is verified and compiled with its storage crate but was not executed for this asset: its parts are the capture's column files (flat_capture_parts), connected to the fixed claim by the verified lemma_delivered_buffers_represent";

/// The flat layout of a package's declaration, refused unless the package's author sources are exactly its generation.
pub fn generated_flat_storage(declaration: &Value, author_files: &[(String, String)]) -> Result<FlatStorage, AdmissionError> {
    let declaration: DeclaredSource = serde_json::from_value(declaration.clone()).map_err(AdmissionError::tool)?;
    let flat = flat_storage_of(&declaration).map_err(|e| AdmissionError::refusal(format!("flat_storage_not_generated: {e}")))?;
    let mut expected: Vec<(String, String)> = flat.files.iter().map(|f| (f.path.clone(), f.text.clone())).collect();
    let mut actual = author_files.to_vec();
    expected.sort();
    actual.sort();
    if expected != actual {
        return Err(AdmissionError::refusal(format!(
            "flat_storage_not_generated: the author sources of storage {} are not the flat storage generator's output for its declaration",
            flat.name
        )));
    }
    Ok(flat)
}

/// The flat layout of the storage package with checked build `build` and declaration `declaration`: its author files
/// (the build's agent-owned sources) must be exactly the generator's output for the declaration.
pub fn flat_storage_of_build(store: &ObjectStore, build: &VerusBuildV1, declaration: &Value) -> Result<FlatStorage, AdmissionError> {
    let author_files: Vec<(String, String)> = build
        .source_texts(store)
        .map_err(record_error)?
        .into_iter()
        .filter(|(_, owner, _)| *owner == VerusSourceOwnerV1::Agent)
        .map(|(path, _, text)| (path, text))
        .collect();
    generated_flat_storage(declaration, &author_files)
}

/// One part's source: the captured file and the file actually linked or copied (an earlier flat asset's copy of it).
struct PartSource {
    captured: CapturedBuffer,
    resolved: PathBuf,
    linked_from: PathBuf,
    elem: PartElem,
    len: usize,
}

impl AssetBuildSlot {
    /// Publish this key's asset of the flat storage `flat` (from [`generated_flat_storage`] of this slot's package) from
    /// the capture archive `archive` (with the capture identity `capture`), as [`FLAT_CAPTURE_PARTS`] states. `reuse`
    /// maps a resolved capture file to an earlier flat asset's copy of it. Returns the asset and its evidence record.
    pub fn publish_flat_capture_parts(
        self,
        store: &ObjectStore,
        flat: &FlatStorage,
        archive: &Path,
        capture: &str,
        reuse: &BTreeMap<PathBuf, PathBuf>,
    ) -> Result<(StorageAsset, Value), AdmissionError> {
        let started = Instant::now();
        let sources = self.flat_part_sources(flat, archive, reuse)?;
        let staged = store.fresh_asset_staging_directory(self.lock.asset_name()).map_err(store_error)?;
        check_copy_space(&sources, staged.parent().unwrap_or(&staged))?;
        let written = || -> Result<(gendb_storage::io::PartsManifest, Vec<PartPlacement>), AdmissionError> {
            let mut writer = PartFilesWriter::new(&staged, PartsFormat::LittleEndian).map_err(AdmissionError::tool)?;
            let placements = sources.iter().map(|s| writer.add_file_part(s.elem, s.len, &s.linked_from).map_err(AdmissionError::tool)).collect::<Result<Vec<_>, _>>()?;
            Ok((writer.finish().map_err(AdmissionError::tool)?, placements))
        };
        let (manifest, placements) = match written() {
            Ok(done) => done,
            Err(error) => {
                remove_build_directory(&staged).map_err(store_error)?;
                return Err(error);
            }
        };
        let wall_ns = started.elapsed().as_nanos() as u64;
        let parts: Vec<Value> = flat
            .parts
            .iter()
            .zip(&sources)
            .zip(&placements)
            .enumerate()
            .map(|(index, ((part, source), placement))| {
                json!({"part":index,"constant":part.constant,"column":part.column,"ordinal":part.ordinal,"buffer":buffer_name(part.buffer),
                    "elem":part.elem.variant(),"len":source.len,"bytes":source.captured.bytes,"capture_file":source.captured.path,
                    "resolved":source.resolved,"linked_from":source.linked_from,"placement":placement})
            })
            .collect();
        let copied: u64 = sources.iter().zip(&placements).filter(|(_, p)| **p == PartPlacement::Copy).map(|(s, _)| s.captured.bytes).sum();
        let evidence = json!({"storage_package":self.package_id,"storage":flat.name.as_str(),"table":flat.table,"key":self.key(),
            "capture":{"archive":archive,"capture_identity":capture},"parts":parts,"storage_bytes":manifest.storage_bytes,
            "copied_bytes":copied,"wall_ns":wall_ns,"builder":BUILDER_NOT_EXECUTED,
            "trusted_host_item":{"id":FLAT_CAPTURE_PARTS.0,"statement":FLAT_CAPTURE_PARTS.1}});
        let evidence_id = store.put(1, FLAT_CAPTURE_ASSET_KIND, &evidence).map_err(store_error)?;
        let built = BuiltParts {
            format_version: manifest.format_version,
            byte_order: "little".into(),
            parts: manifest.parts.iter().map(|(elem, len)| Ok((super::element_name(elem)?, *len))).collect::<Result<Vec<_>, AdmissionError>>()?,
            storage_bytes: manifest.storage_bytes,
        };
        let (id, asset) = records::publish_storage_asset(store, &self.lock, &staged, built, wall_ns, evidence_id).map_err(record_error)?;
        let directory = records::storage_asset_directory(store, &asset).map_err(record_error)?;
        Ok((StorageAsset { id, asset, directory, built: true }, evidence))
    }

    /// The capture file of every part of `flat`, checked against this slot's key and the generated layout.
    fn flat_part_sources(&self, flat: &FlatStorage, archive: &Path, reuse: &BTreeMap<PathBuf, PathBuf>) -> Result<Vec<PartSource>, AdmissionError> {
        let refuse = |message: String| Err(AdmissionError::refusal(format!("flat_capture_mismatch: storage {}: {message}", flat.name)));
        let [stored] = self.key().tables.as_slice() else {
            return refuse("a flat asset key holds exactly one table".into());
        };
        if stored.table != flat.table {
            return refuse(format!("the asset key is for table {}, not {}", stored.table, flat.table));
        }
        let columns = SourceColumns::captured_columns(archive).map_err(AdmissionError::tool)?;
        let declared = &flat.declaration.tables[0].columns;
        let mut sources = vec![];
        for part in &flat.parts {
            let Some(column) = columns.iter().find(|c| c.table == flat.table && c.ordinal == part.ordinal) else {
                return refuse(format!("column {} (ordinal {}) is not captured", part.column, part.ordinal));
            };
            let declared = declared.iter().find(|c| c.ordinal == part.ordinal).expect("generated part column");
            if !captured_as_declared(&column.field, declared) || column.rows as u64 != stored.rows {
                return refuse(format!(
                    "captured column {} {:?} (nullable {}, {} rows) is not the declared {} {:?} of the key's {} rows",
                    column.field.name, column.field.ty, column.field.nullable, column.rows, declared.name, declared.ty, stored.rows
                ));
            }
            let (buffer, elem, len) = match part.buffer {
                FlatBuffer::Values => (&column.values, part.elem, column.rows),
                FlatBuffer::Offsets => (&column.offsets, part.elem, column.rows + 1),
                FlatBuffer::Bytes => (&column.bytes, part.elem, column.bytes.as_ref().map_or(0, |b| b.bytes as usize)),
                FlatBuffer::Validity => (&column.validity, part.elem, column.rows),
            };
            let Some(captured) = buffer.clone() else {
                return refuse(format!("captured column {} has no {} file", column.field.name, buffer_name(part.buffer)));
            };
            let elem = part_elem(elem);
            if captured.bytes != (len as u64).saturating_mul(elem.width() as u64) {
                return refuse(format!("captured {} file of {} is not {len} elements of {}", buffer_name(part.buffer), column.field.name, part.elem.variant()));
            }
            let resolved = captured.path.canonicalize().map_err(|e| AdmissionError::tool(format!("{}: {e}", captured.path.display())))?;
            let linked_from = reuse.get(&resolved).cloned().unwrap_or_else(|| resolved.clone());
            sources.push(PartSource { captured, resolved, linked_from, elem, len });
        }
        Ok(sources)
    }
}

/// Whether the captured column `captured` is exactly the declared column `declared`: same name, same nullability, and
/// the captured type the declared SQL type is captured as (integer I32, bigint I64, date Date32, numeric(p,s) Decimal
/// with the same precision and scale, text/varchar/char Utf8). Metadata only.
fn captured_as_declared(captured: &ColumnSpec, declared: &DeclaredColumn) -> bool {
    let expected = match declared.ty {
        DeclaredType::Int4 => ColType::I32,
        DeclaredType::Int8 => ColType::I64,
        DeclaredType::Date => ColType::Date32,
        DeclaredType::Numeric { precision, scale } => match (u8::try_from(precision), i8::try_from(scale)) {
            (Ok(p), Ok(s)) => ColType::Decimal { p, s },
            _ => return false,
        },
        DeclaredType::Text | DeclaredType::Varchar { .. } | DeclaredType::Bpchar { .. } => ColType::Utf8,
    };
    captured.name == declared.name && captured.nullable == declared.nullable && captured.ty == expected
}

/// Free space for the parts that must be copied (their files lie on another filesystem than `library_directory`): their
/// bytes plus the writers' reserve, refused as `insufficient_storage` before anything is written.
fn check_copy_space(sources: &[PartSource], library_directory: &Path) -> Result<(), AdmissionError> {
    let device = std::fs::metadata(library_directory).map_err(|e| AdmissionError::tool(format!("{}: {e}", library_directory.display())))?.dev();
    let mut copied = 0u64;
    for source in sources {
        let metadata = std::fs::metadata(&source.linked_from).map_err(|e| AdmissionError::tool(format!("{}: {e}", source.linked_from.display())))?;
        if metadata.dev() != device {
            copied = copied.saturating_add(source.captured.bytes);
        }
    }
    let free = free_bytes_at(library_directory);
    if copied > 0 && free.is_some_and(|free| free < copied.saturating_add(STORAGE_MARGIN_BYTES)) {
        return Err(AdmissionError::tool(format!(
            "insufficient_storage: the flat asset copies {copied} bytes from another filesystem and keeps {STORAGE_MARGIN_BYTES} bytes free; {} bytes are free",
            free.unwrap_or(0)
        )));
    }
    Ok(())
}

fn part_elem(elem: FlatElem) -> PartElem {
    match elem {
        FlatElem::I32 => PartElem::I32,
        FlatElem::I64 => PartElem::I64,
        FlatElem::I128 => PartElem::I128,
        FlatElem::U8 => PartElem::U8,
    }
}

fn buffer_name(buffer: FlatBuffer) -> &'static str {
    match buffer {
        FlatBuffer::Values => "values",
        FlatBuffer::Offsets => "offsets",
        FlatBuffer::Bytes => "bytes",
        FlatBuffer::Validity => "validity",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A captured column matches its declaration only with the same name, type, decimal precision and scale, and
    /// nullability.
    #[test]
    fn captured_columns_must_have_the_declared_type() {
        let declared = |ty| DeclaredColumn { ordinal: 0, name: "c".into(), ty, row_count_only: false, nullable: false };
        let captured = |ty, nullable| ColumnSpec { name: "c".into(), ty, nullable };
        let numeric = declared(DeclaredType::Numeric { precision: 15, scale: 2 });
        assert!(captured_as_declared(&captured(ColType::Decimal { p: 15, s: 2 }, false), &numeric));
        assert!(!captured_as_declared(&captured(ColType::Decimal { p: 15, s: 3 }, false), &numeric), "another scale");
        assert!(!captured_as_declared(&captured(ColType::Decimal { p: 12, s: 2 }, false), &numeric), "another precision");
        assert!(!captured_as_declared(&captured(ColType::I32, false), &declared(DeclaredType::Date)), "same width, another type");
        assert!(captured_as_declared(&captured(ColType::Date32, false), &declared(DeclaredType::Date)));
        assert!(!captured_as_declared(&captured(ColType::Utf8, true), &declared(DeclaredType::Text)), "nullable, declared NOT NULL");
        let nullable_text = DeclaredColumn { nullable: true, ..declared(DeclaredType::Text) };
        assert!(captured_as_declared(&captured(ColType::Utf8, true), &nullable_text));
        assert!(!captured_as_declared(&captured(ColType::Utf8, false), &nullable_text), "NOT NULL, declared nullable");
        assert!(!captured_as_declared(&ColumnSpec { name: "d".into(), ty: ColType::I64, nullable: false }, &declared(DeclaredType::Int8)), "another name");
    }
}
