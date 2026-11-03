//! The data of a workload folder at one scale (`data/<scale>/`): each table's Parquet files, their check against
//! `schema.sql` (file footers only, no data read), and the data size that is the storage budget.
//!
//! A table's files are `data/<scale>/<table>.parquet`, or every `*.parquet` file of `data/<scale>/<table>/` in name
//! order (the table's rows are the files' rows in that order). The importer refuses any file whose Arrow schema is not
//! the declared one (names, types and nullability, in order); [`check_files`] lists every difference first, each with
//! its fix.
//!
//! The data size ([`DataSize`]), in this order: the `storage_budget_bytes` setting (the user's explicit budget), else
//! `data/<scale>/MANIFEST.json` `original_data_bytes` (the data as `|` text, the measure of the benchmarks), else the
//! Parquet files' uncompressed size from their footers (a different measure; the record names which one was used).

use super::FolderError;
use super::schema::Schema;
use arrow::datatypes::DataType;
use gendb_artifacts::ColType;
use gendb_storage::import::DatasetSpec;
use parquet::arrow::arrow_reader::ParquetRecordBatchReaderBuilder;
use serde::Serialize;
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// The optional record of a scale's original data size.
pub const MANIFEST_FILE: &str = "MANIFEST.json";

/// The data size of one scale and where it comes from.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct DataSize {
    /// Bytes.
    pub original_data_bytes: u64,
    /// `manifest_original_data_bytes`, `setting_storage_budget_bytes` or `parquet_uncompressed_bytes`.
    pub measure: &'static str,
    /// The file that states it (the manifest, the settings file's folder, or the data directory).
    pub source: PathBuf,
}

/// The source files of every table of `schema` under `dir` (`data/<scale>`).
pub fn locations(schema: &Schema, dir: &Path) -> Result<BTreeMap<String, Vec<PathBuf>>, FolderError> {
    if !dir.is_dir() {
        return Err(FolderError::new("data_missing", format!("{} does not exist: write the data there (or add setup_data.sh SCALE, which writes it)", dir.display())));
    }
    let mut out = BTreeMap::new();
    for table in &schema.tables {
        let single = dir.join(format!("{}.parquet", table.name));
        let parts = dir.join(&table.name);
        let files = if single.is_file() {
            vec![single.clone()]
        } else if parts.is_dir() {
            let mut files: Vec<PathBuf> = std::fs::read_dir(&parts)
                .map_err(|e| FolderError::new("data_missing", format!("{}: {e}", parts.display())))?
                .filter_map(|e| e.ok().map(|e| e.path()))
                .filter(|p| p.extension().is_some_and(|x| x == "parquet"))
                .collect();
            files.sort();
            files
        } else {
            vec![]
        };
        if files.is_empty() {
            return Err(FolderError::new("data_missing", format!("table {}: no {} and no {}/*.parquet", table.name, single.display(), parts.display())));
        }
        out.insert(table.name.clone(), files);
    }
    Ok(out)
}

/// The Arrow type the importer requires for a declared column type.
fn arrow_type(ty: ColType) -> DataType {
    match ty {
        ColType::Decimal { p, s } => DataType::Decimal128(p, s),
        ColType::Date32 => DataType::Date32,
        ColType::Bool => DataType::Boolean,
        ColType::I32 => DataType::Int32,
        ColType::I64 => DataType::Int64,
        ColType::U32 => DataType::UInt32,
        ColType::U64 => DataType::UInt64,
        ColType::Utf8 => DataType::Utf8,
        ColType::Binary => DataType::Binary,
    }
}

/// Check every file of `dataset` against its declared columns (footers only); the refusal lists every difference.
pub fn check_files(dataset: &DatasetSpec) -> Result<(), FolderError> {
    let mut differences = vec![];
    for table in &dataset.tables {
        for path in &table.locations {
            let file = std::fs::File::open(path).map_err(|e| FolderError::new("data_missing", format!("{}: {e}", path.display())))?;
            let builder = ParquetRecordBatchReaderBuilder::try_new(file).map_err(|e| FolderError::new("data_schema", format!("{}: not a readable Parquet file: {e}", path.display())))?;
            let found = builder.schema().fields().clone();
            let at = path.display();
            if found.len() != table.fields.len() {
                let names: Vec<&str> = found.iter().map(|f| f.name().as_str()).collect();
                differences.push(format!("{at}: {} columns {names:?}, but table {} declares {}: write exactly the declared columns, in order", found.len(), table.name, table.fields.len()));
                continue;
            }
            for (declared, field) in table.fields.iter().zip(found.iter()) {
                let want = arrow_type(declared.ty);
                if field.name() != &declared.name {
                    differences.push(format!("{at}: column {:?} where {}.{} is declared: write the declared name, in the declared order", field.name(), table.name, declared.name));
                    continue;
                }
                if field.data_type() != &want {
                    let fix = match (field.data_type(), &want) {
                        (DataType::LargeUtf8 | DataType::Utf8View, DataType::Utf8) => "write it as Arrow string (pyarrow pa.string())".to_string(),
                        _ => format!("write it as Arrow {want:?}"),
                    };
                    differences.push(format!("{at}: {}.{} is {:?}; the declared type needs {want:?}: {fix}", table.name, declared.name, field.data_type()));
                }
                if field.is_nullable() != declared.nullable {
                    let fix = if declared.nullable { "add NOT NULL to the column, or write the field as nullable" } else { "remove NOT NULL from the column, or write the field as not nullable" };
                    differences.push(format!("{at}: {}.{} is {} in the file but {} in schema.sql: {fix}", table.name, declared.name, nullability(field.is_nullable()), nullability(declared.nullable)));
                }
            }
        }
    }
    if differences.is_empty() { Ok(()) } else { Err(FolderError::new("data_schema", differences.join("\n"))) }
}

fn nullability(nullable: bool) -> &'static str {
    if nullable { "nullable" } else { "NOT NULL" }
}

/// The data size of the scale at `dir` with source files `dataset` (see the module documentation).
pub fn data_size(dir: &Path, dataset: &DatasetSpec, budget_setting: Option<(u64, &Path)>) -> Result<DataSize, FolderError> {
    if let Some((bytes, folder)) = budget_setting {
        return Ok(DataSize { original_data_bytes: bytes, measure: "setting_storage_budget_bytes", source: folder.to_path_buf() });
    }
    let manifest = dir.join(MANIFEST_FILE);
    if manifest.is_file() {
        let text = std::fs::read_to_string(&manifest).map_err(|e| FolderError::new("data_size", format!("{}: {e}", manifest.display())))?;
        let value: serde_json::Value = serde_json::from_str(&text).map_err(|e| FolderError::new("data_size", format!("{}: {e}", manifest.display())))?;
        // A manifest without the field (an older data script's) states no size: the footers below give it.
        if let Some(field) = value.get("original_data_bytes") {
            let bytes = field.as_u64().filter(|b| *b > 0);
            let bytes = bytes.ok_or_else(|| FolderError::new("data_size", format!("{}: original_data_bytes must be a positive integer", manifest.display())))?;
            return Ok(DataSize { original_data_bytes: bytes, measure: "manifest_original_data_bytes", source: manifest });
        }
    }
    let mut bytes: u64 = 0;
    for path in dataset.tables.iter().flat_map(|t| &t.locations) {
        let file = std::fs::File::open(path).map_err(|e| FolderError::new("data_missing", format!("{}: {e}", path.display())))?;
        let builder = ParquetRecordBatchReaderBuilder::try_new(file).map_err(|e| FolderError::new("data_schema", format!("{}: {e}", path.display())))?;
        bytes += builder.metadata().row_groups().iter().map(|g| g.total_byte_size().max(0) as u64).sum::<u64>();
    }
    if bytes == 0 {
        return Err(FolderError::new("data_size", format!("{}: the Parquet files are empty; set storage_budget_bytes", dir.display())));
    }
    Ok(DataSize { original_data_bytes: bytes, measure: "parquet_uncompressed_bytes", source: dir.to_path_buf() })
}
