//! Compatibility of the import layer with a saved prepared capture of the earlier GenDB version (ignored: needs saved files). Reads metadata and a
//! few boundary values only: no import, full scan or hash.
//!
//! ```text
//! GENDB_PREPARED_ROOT=<saved prepared root>  GENDB_SAVED_QUERIES=<query dir>,<query dir>,...  TMPDIR=<scratch> \
//!   cargo test -p gendb-storage --test prepared_sf1 -- --ignored --nocapture
//! ```
//!
//! A query directory holds `verus-preflight/statement.json` (its source declaration) and `verus-inputs/` (the view
//! archive that version wrote for it). Checks: the saved root opens with its recorded capture identity; each declaration projects
//! to the saved view's projection and capture identity, and its written view archive equals the saved one byte for
//! byte; native boundary values (first and last row) equal the original
//! Parquet files' first and last rows, in the same units; a small captured table decodes consistently; and reusing the
//! saved root for the union of the declarations imports nothing.

use gendb_frontend::columns::{SourceColumn, SourceDeclaration, SourceTable, SourceType};
use gendb_storage::import::{
    ColumnDemand, DatasetSpec, PreparationMethod, PreparationRequest, PreparedSource, declaration_projection,
    prepare_source,
};
use gendb_storage::io::{NativeColumn, SourceColumns};
use parquet::arrow::{ProjectionMask, arrow_reader::ParquetRecordBatchReaderBuilder};
use serde_json::Value;
use std::{
    fs,
    path::{Path, PathBuf},
};

fn read_json(path: &Path) -> Value {
    serde_json::from_slice(&fs::read(path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))).unwrap()
}

fn source_type(value: &Value) -> SourceType {
    match value {
        Value::String(s) if s == "int64" => SourceType::Int64,
        Value::String(s) if s == "int32" => SourceType::Int32,
        Value::String(s) if s == "date32" => SourceType::Date32,
        Value::String(s) if s == "utf8" => SourceType::Utf8,
        Value::Object(o) if o.contains_key("decimal") => SourceType::Decimal {
            p: o["decimal"]["p"].as_u64().unwrap() as u32,
            s: o["decimal"]["s"].as_u64().unwrap() as u32,
        },
        other => panic!("unexpected source type {other}"),
    }
}

/// The saved source declaration of a query (`SourceDeclaration` is serialize-only; rebuilt field by field).
fn saved_declaration(query: &Path) -> SourceDeclaration {
    let statement = read_json(&query.join("verus-preflight/statement.json"));
    let tables = statement["source_declaration"]["tables"].as_array().unwrap();
    SourceDeclaration {
        tables: tables
            .iter()
            .map(|t| SourceTable {
                index: t["index"].as_u64().unwrap() as usize,
                table_id: t["table_id"].as_u64().unwrap() as usize,
                name: t["name"].as_str().unwrap().into(),
                columns: t["columns"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|c| SourceColumn {
                        ordinal: c["ordinal"].as_u64().unwrap() as usize,
                        name: c["name"].as_str().unwrap().into(),
                        ty: source_type(&c["ty"]),
                        row_count_only: c["row_count_only"].as_bool().unwrap(),
                        nullable: c["nullable"].as_bool().unwrap_or(false),
                    })
                    .collect(),
            })
            .collect(),
    }
}

/// A native value at `row` rendered in its native unit: i64, i32 days since 1970-01-01, i128 decimal coefficient, or
/// UTF-8 text.
fn native_value(column: &NativeColumn, row: usize) -> String {
    // SAFETY: descriptors of a mapped capture point at `len` rows kept alive by the owning `SourceColumns`.
    unsafe {
        match column.type_tag {
            1 => (*column.values.cast::<i32>().add(row)).to_string(),
            2 => (*column.values.cast::<i64>().add(row)).to_string(),
            3 => (*column.values.cast::<i128>().add(row)).to_string(),
            4 => {
                let (start, end) = (*column.offsets.add(row) as usize, *column.offsets.add(row + 1) as usize);
                String::from_utf8(std::slice::from_raw_parts(column.bytes.add(start), end - start).to_vec()).unwrap()
            }
            tag => panic!("unexpected tag {tag}"),
        }
    }
}

/// The same value read from the original file: Arrow's Date32 is days since 1970-01-01 and Decimal128 its coefficient.
fn arrow_value(array: &dyn arrow::array::Array, row: usize) -> String {
    use arrow::array::AsArray;
    use arrow::datatypes::{Date32Type, Decimal128Type, Int32Type, Int64Type};
    match array.data_type() {
        arrow::datatypes::DataType::Int64 => array.as_primitive::<Int64Type>().value(row).to_string(),
        arrow::datatypes::DataType::Int32 => array.as_primitive::<Int32Type>().value(row).to_string(),
        arrow::datatypes::DataType::Date32 => array.as_primitive::<Date32Type>().value(row).to_string(),
        arrow::datatypes::DataType::Decimal128(..) => array.as_primitive::<Decimal128Type>().value(row).to_string(),
        arrow::datatypes::DataType::Utf8 => array.as_string::<i32>().value(row).to_string(),
        other => panic!("unexpected type {other}"),
    }
}

/// First and last row of declared column `ordinal` in the original files, reading only the first row group of the
/// first file and the last row group of the last file.
fn original_boundary(locations: &[PathBuf], ordinal: usize) -> (String, String) {
    let read = |path: &PathBuf, last: bool| {
        let builder = ParquetRecordBatchReaderBuilder::try_new(fs::File::open(path).unwrap()).unwrap();
        let group = if last {
            builder.metadata().num_row_groups() - 1
        } else {
            0
        };
        let mask = ProjectionMask::roots(builder.parquet_schema(), [ordinal]);
        let batches: Vec<_> = builder
            .with_row_groups(vec![group])
            .with_projection(mask)
            .build()
            .unwrap()
            .map(Result::unwrap)
            .collect();
        let batch = if last {
            batches.last().unwrap()
        } else {
            batches.first().unwrap()
        };
        arrow_value(batch.column(0).as_ref(), if last { batch.num_rows() - 1 } else { 0 })
    };
    (
        read(locations.first().unwrap(), false),
        read(locations.last().unwrap(), true),
    )
}

#[test]
#[ignore = "needs a saved prepared root (GENDB_PREPARED_ROOT) and saved query directories (GENDB_SAVED_QUERIES)"]
fn saved_prepared_capture_opens_projects_and_is_reused_without_import() {
    let root = PathBuf::from(std::env::var("GENDB_PREPARED_ROOT").expect("GENDB_PREPARED_ROOT"));
    let queries: Vec<PathBuf> = std::env::var("GENDB_SAVED_QUERIES")
        .expect("GENDB_SAVED_QUERIES")
        .split(',')
        .map(PathBuf::from)
        .collect();
    let lane = PathBuf::from(std::env::var("TMPDIR").expect("a scratch TMPDIR"));
    assert!(!lane.starts_with("/tmp"));
    let record = read_json(&root.join("workload.json"));
    let dataset: DatasetSpec = serde_json::from_value(record["workload"]["dataset"].clone()).unwrap();

    // 1. The saved root opens (metadata and mappings only) with its recorded capture identity.
    let source = PreparedSource::open(&root, &dataset).unwrap();
    assert_eq!(
        source.capture_identity(),
        record["native_capture_identity"].as_str().unwrap()
    );
    println!(
        "opened {} capture {} coverage {:?}",
        root.display(),
        source.capture_identity(),
        source.coverage()
    );

    // 2. Each saved declaration projects to the saved view: projection, capture identity and view-archive bytes.
    let mut demand = ColumnDemand::default();
    for (index, query) in queries.iter().enumerate() {
        let declaration = saved_declaration(query);
        let view = read_json(&query.join("verus-inputs/view.json"));
        let projection = declaration_projection(&dataset, &declaration).unwrap();
        assert_eq!(
            serde_json::to_value(&projection).unwrap(),
            view["projection"],
            "{}",
            query.display()
        );
        let columns = source.project_declaration(&declaration).unwrap();
        let saved_identity = fs::read_to_string(query.join("verus-inputs/capture-version.txt")).unwrap();
        assert_eq!(columns.capture_identity(), saved_identity, "{}", query.display());
        let written = lane.join(format!(
            "gendb-storage-prepared-sf1-view-{}-{index}",
            std::process::id()
        ));
        columns.write_archive(&written).unwrap();
        for file in ["view.json", "capture-version.txt"] {
            assert_eq!(
                fs::read(written.join(file)).unwrap(),
                fs::read(query.join("verus-inputs").join(file)).unwrap()
            );
        }
        demand.add_declaration(&dataset, &declaration).unwrap();

        // 3. Boundary values of every delivered column equal the original files' first/last rows, in native units.
        for (table, ordinals) in &projection {
            let locations = &dataset.table(table).unwrap().locations;
            for ordinal in ordinals {
                let binding = columns
                    .bindings()
                    .iter()
                    .find(|b| b.table == *table && b.original_index == Some(*ordinal))
                    .unwrap();
                let native = &columns.descriptors()[binding.descriptor_index];
                let rows = binding.row_count;
                let (first, last) = original_boundary(locations, *ordinal);
                assert_eq!(
                    (native_value(native, 0), native_value(native, rows - 1)),
                    (first.clone(), last.clone())
                );
                println!(
                    "{} {table}.{ordinal} rows {rows}: first {first} last {last}",
                    query.display()
                );
            }
        }
    }

    // 4. A small captured table decodes from its IPC file consistently with the native columns.
    let small = source
        .coverage()
        .into_iter()
        .min_by_key(|(t, _)| source.row_count(t).unwrap())
        .unwrap();
    let logical = source.logical_table(&small.0).unwrap();
    let native: SourceColumns = source.project(&[(small.0.clone(), vec![small.1[0]])]).unwrap();
    let batch_rows: Vec<usize> = logical.batches.iter().map(|b| b.num_rows()).collect();
    assert_eq!(batch_rows.iter().sum::<usize>(), logical.row_count);
    let last_batch = logical.batches.last().unwrap();
    assert_eq!(
        arrow_value(logical.batches[0].column(0).as_ref(), 0),
        native_value(&native.descriptors()[0], 0)
    );
    assert_eq!(
        arrow_value(last_batch.column(0).as_ref(), last_batch.num_rows() - 1),
        native_value(&native.descriptors()[0], logical.row_count - 1)
    );
    println!(
        "decoded {} ({} rows, {} batches)",
        small.0,
        logical.row_count,
        batch_rows.len()
    );

    // 5. Reusing the saved root for the union of the declarations imports nothing and shares its capture.
    let scratch = lane.join(format!("gendb-storage-prepared-sf1-{}", std::process::id()));
    let (reused, report) = prepare_source(&PreparationRequest {
        dataset: &dataset,
        demand: &demand,
        base: Some(&root),
        registry: &scratch.join("registry"),
        root: &scratch.join("prepared"),
    })
    .unwrap();
    assert_eq!(report.method, PreparationMethod::ReusedNamed);
    assert!(report.imported_columns.is_empty());
    assert_eq!(reused.capture_identity(), source.capture_identity());
    let reopened = PreparedSource::open(&scratch.join("prepared"), &dataset).unwrap();
    assert_eq!(reopened.capture_identity(), source.capture_identity());
    println!("reused: {}", serde_json::to_string(&report).unwrap());
    println!("demand: {}", serde_json::to_string(&demand).unwrap());
}
