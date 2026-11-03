//! The trusted original-data importer. It reads the demanded columns of declared Parquet files, file by file in
//! declared order and batch by batch in file order: that sequence is the canonical row order of the capture, which
//! every later projection, native column and reference shares.
//!
//! Trusted, not verified: that the parquet/Arrow decoders and the filesystem deliver each file's values exactly, and
//! that files whose lifecycle stamp is unchanged hold the same rows. Checked here: every file's Arrow schema equals the
//! declaration exactly (names, types, nullability, order), and every stamp is unchanged across the read.

use super::dataset::{DatasetSpec, SourceVersion, TableSpec, declared_schema};
use super::error::{ImportError, Result};
use crate::io::ProjectedTable;
use arrow::datatypes::SchemaRef;
use parquet::arrow::{ProjectionMask, arrow_reader::ParquetRecordBatchReaderBuilder};
use std::{fs::File, path::Path};

/// Stamp each of `tables` and check each of its files against its declaration (file footers only).
pub(crate) fn stamp_and_check_files(tables: &[TableSpec]) -> Result<Vec<SourceVersion>> {
    tables
        .iter()
        .map(|table| {
            let schema = declared_schema(&table.name, &table.fields)?;
            for path in &table.locations {
                open_declared(path, &schema)?;
            }
            SourceVersion::stamp(table)
        })
        .collect()
}

/// Read `projection` from the current source files. `versions` are the stamps just taken for these files (the versions
/// the capture records); a file whose stamp differs before or after the read is refused, so a capture never mixes two
/// file versions.
pub(crate) fn read_projection(
    dataset: &DatasetSpec,
    versions: &[SourceVersion],
    projection: &[(String, Vec<usize>)],
) -> Result<Vec<ProjectedTable>> {
    let tables = projection
        .iter()
        .map(|(name, _)| {
            dataset
                .table(name)
                .ok_or_else(|| ImportError::demand(name, "table is not declared"))
        })
        .collect::<Result<Vec<_>>>()?;
    let unchanged = || -> Result<()> {
        for table in &tables {
            let recorded = versions.iter().find(|v| v.table == table.name).map(|v| &v.version);
            if recorded != Some(&SourceVersion::stamp(table)?.version) {
                return Err(ImportError::SourceChanged {
                    table: table.name.clone(),
                });
            }
        }
        Ok(())
    };
    unchanged()?;
    let captured = tables
        .iter()
        .zip(projection)
        .map(|(table, (_, ordinals))| read_table(table, ordinals))
        .collect::<Result<Vec<_>>>()?;
    unchanged()?;
    Ok(captured)
}

/// The declared columns `ordinals` (strictly increasing) of every file of `table`, in row order. With no ordinals only
/// the row count is read, from the file footers.
fn read_table(table: &TableSpec, ordinals: &[usize]) -> Result<ProjectedTable> {
    if ordinals.windows(2).any(|w| w[0] >= w[1]) || ordinals.last().is_some_and(|&o| o >= table.fields.len()) {
        return Err(ImportError::demand(
            &table.name,
            "ordinals must be strictly increasing declared ordinals",
        ));
    }
    let schema = declared_schema(&table.name, &table.fields)?;
    let mut batches = vec![];
    let mut row_count = 0usize;
    let mut add_rows = |rows: usize| -> Result<()> {
        row_count = row_count
            .checked_add(rows)
            .ok_or_else(|| ImportError::declaration(&table.name, "row count overflow"))?;
        Ok(())
    };
    for path in &table.locations {
        let builder = open_declared(path, &schema)?;
        if ordinals.is_empty() {
            let rows = usize::try_from(builder.metadata().file_metadata().num_rows())
                .map_err(|_| source_error(path, "invalid Parquet row count"))?;
            add_rows(rows)?;
            continue;
        }
        let mask = ProjectionMask::roots(builder.parquet_schema(), ordinals.iter().copied());
        let reader = builder
            .with_projection(mask)
            .build()
            .map_err(ImportError::parquet(path))?;
        for batch in reader {
            let batch = batch?;
            add_rows(batch.num_rows())?;
            batches.push(batch);
        }
    }
    Ok(ProjectedTable {
        table: table.name.clone(),
        original_indices: ordinals.to_vec(),
        fields: ordinals.iter().map(|&o| table.fields[o].clone()).collect(),
        batches,
        row_count,
    })
}

/// Open one Parquet file, refusing it unless its Arrow schema equals the declared schema.
fn open_declared(path: &Path, declared: &SchemaRef) -> Result<ParquetRecordBatchReaderBuilder<File>> {
    let file = File::open(path).map_err(ImportError::file(path))?;
    let builder = ParquetRecordBatchReaderBuilder::try_new(file).map_err(ImportError::parquet(path))?;
    if builder.schema().fields() != declared.fields() {
        return Err(source_error(
            path,
            &format!("declared/file schema disagreement: file schema {:?}", builder.schema()),
        ));
    }
    Ok(builder)
}

fn source_error(path: &Path, reason: &str) -> ImportError {
    ImportError::Source {
        path: path.to_path_buf(),
        reason: reason.to_string(),
    }
}
