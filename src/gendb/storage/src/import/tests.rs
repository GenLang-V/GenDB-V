//! Scoped checks of import, prepared-capture reuse/extension and the reference on tiny Parquet files. Scratch lives
//! under a scratch `TMPDIR`, never `/tmp`. The saved SF1 capture is checked by `tests/prepared_sf1.rs` (ignored).

use super::*;
use crate::io::SourceColumns;
use arrow::{
    array::{Array, ArrayRef, Date32Array, Decimal128Array, Int64Array, StringArray},
    datatypes::{DataType, Field, Schema},
    record_batch::RecordBatch,
};
use datafusion::common::ScalarValue;
use gendb_artifacts::{ColType, ColumnSpec};
use gendb_frontend::columns::{SourceColumn, SourceDeclaration, SourceTable, SourceType};
use std::{
    collections::BTreeSet,
    fs,
    path::{Path, PathBuf},
    sync::Arc,
};

/// A fresh, not yet existing path `$TMPDIR/gendb-storage-import-tests/<pid>-<nanos>-<n>`.
fn scratch() -> PathBuf {
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let lane = PathBuf::from(std::env::var_os("TMPDIR").expect("a scratch TMPDIR is required; /tmp is forbidden"));
    assert!(!lane.starts_with("/tmp"), "TMPDIR must be a scratch directory, not /tmp");
    let root = lane.join("gendb-storage-import-tests");
    fs::create_dir_all(&root).unwrap();
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    root.join(format!(
        "{}-{nanos}-{}",
        std::process::id(),
        NEXT.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    ))
}

fn column(name: &str, ty: ColType, nullable: bool) -> ColumnSpec {
    ColumnSpec {
        name: name.into(),
        ty,
        nullable,
    }
}

fn sales_fields() -> Vec<ColumnSpec> {
    vec![
        column("key", ColType::I64, false),
        column("amount", ColType::Decimal { p: 12, s: 2 }, true),
        column("label", ColType::Utf8, false),
        column("day", ColType::Date32, false),
        column("unused", ColType::Utf8, false),
    ]
}

/// Rows `range` of the `sales` fixture: key 10+i, amount (i*125-50) cents with row 1 NULL, label "l<i%3>",
/// day 9000+i, unused text.
fn sales_batch(range: std::ops::Range<i64>) -> RecordBatch {
    let schema = dataset::declared_schema("sales", &sales_fields()).unwrap();
    let amounts: Vec<Option<i128>> = range
        .clone()
        .map(|i| (i != 1).then_some(i as i128 * 125 - 50))
        .collect();
    let columns: Vec<ArrayRef> = vec![
        Arc::new(Int64Array::from(range.clone().map(|i| 10 + i).collect::<Vec<_>>())),
        Arc::new(Decimal128Array::from(amounts).with_precision_and_scale(12, 2).unwrap()),
        Arc::new(StringArray::from(
            range.clone().map(|i| format!("l{}", i % 3)).collect::<Vec<_>>(),
        )),
        Arc::new(Date32Array::from(
            range.clone().map(|i| 9000 + i as i32).collect::<Vec<_>>(),
        )),
        Arc::new(StringArray::from(
            range.map(|i| format!("unused-{i}")).collect::<Vec<_>>(),
        )),
    ];
    RecordBatch::try_new(schema, columns).unwrap()
}

fn write_parquet(path: &Path, batch: &RecordBatch) {
    let mut writer =
        ::parquet::arrow::ArrowWriter::try_new(fs::File::create(path).unwrap(), batch.schema(), None).unwrap();
    writer.write(batch).unwrap();
    writer.close().unwrap();
}

/// `sales` in two files (rows 0..3 and 3..5) and a one-file `other`, declared in that order.
fn fixture(root: &Path) -> DatasetSpec {
    fs::create_dir_all(root).unwrap();
    let (first, second, other) = (
        root.join("sales-0.parquet"),
        root.join("sales-1.parquet"),
        root.join("other.parquet"),
    );
    write_parquet(&first, &sales_batch(0..3));
    write_parquet(&second, &sales_batch(3..5));
    let other_schema = Arc::new(Schema::new(vec![Field::new("id", DataType::Int64, false)]));
    write_parquet(
        &other,
        &RecordBatch::try_new(other_schema, vec![Arc::new(Int64Array::from(vec![7, 8]))]).unwrap(),
    );
    DatasetSpec {
        tables: vec![
            TableSpec {
                name: "sales".into(),
                fields: sales_fields(),
                locations: vec![first, second],
                format: DataFormat::Parquet,
            },
            TableSpec {
                name: "other".into(),
                fields: vec![column("id", ColType::I64, false)],
                locations: vec![other],
                format: DataFormat::Parquet,
            },
        ],
    }
}

fn demand(dataset: &DatasetSpec, columns: &[(&str, &[usize])]) -> ColumnDemand {
    let mut demand = ColumnDemand::default();
    for (table, ordinals) in columns {
        demand.add_columns(dataset, table, ordinals).unwrap();
    }
    demand
}

fn prepare(
    dataset: &DatasetSpec,
    demand: &ColumnDemand,
    base: Option<&Path>,
    registry: &Path,
    root: &Path,
) -> Result<(PreparedSource, PreparationReport)> {
    prepare_source(&PreparationRequest {
        dataset,
        demand,
        base,
        registry,
        root,
    })
}

/// Values of one native column of `columns`, by descriptor index.
fn native_i64(columns: &SourceColumns, index: usize) -> Vec<i64> {
    let d = columns.descriptors()[index];
    // SAFETY: an I64 descriptor points at `len` values kept alive by `columns`.
    unsafe { std::slice::from_raw_parts(d.values.cast::<i64>(), d.len as usize) }.to_vec()
}

fn native_i128(columns: &SourceColumns, index: usize) -> Vec<i128> {
    let d = columns.descriptors()[index];
    // SAFETY: a decimal descriptor points at `len` i128 coefficients kept alive by `columns`.
    unsafe { std::slice::from_raw_parts(d.values.cast::<i128>(), d.len as usize) }.to_vec()
}

fn native_utf8(columns: &SourceColumns, index: usize) -> Vec<String> {
    let d = columns.descriptors()[index];
    let rows = d.len as usize;
    // SAFETY: a UTF-8 descriptor has rows+1 offsets into its byte buffer, kept alive by `columns`.
    let offsets = unsafe { std::slice::from_raw_parts(d.offsets, rows + 1) };
    let bytes = unsafe { std::slice::from_raw_parts(d.bytes, offsets[rows] as usize) };
    (0..rows)
        .map(|r| String::from_utf8(bytes[offsets[r] as usize..offsets[r + 1] as usize].to_vec()).unwrap())
        .collect()
}

/// Every file under `dir` with its length and symlink flag (metadata only).
fn tree(dir: &Path) -> BTreeSet<(PathBuf, u64, bool)> {
    let mut out = BTreeSet::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        for entry in fs::read_dir(&d).unwrap() {
            let path = entry.unwrap().path();
            let m = fs::symlink_metadata(&path).unwrap();
            if m.is_dir() {
                stack.push(path.clone());
            }
            out.insert((path, m.len(), m.file_type().is_symlink()));
        }
    }
    out
}

/// `(linked, written)` lengths of the IPC files directly in a prepared root's archive (metadata only).
fn ipc_file_bytes(root: &Path) -> (u64, u64) {
    let (mut linked, mut written) = (0, 0);
    for entry in fs::read_dir(root.join("inputs")).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().and_then(|x| x.to_str()) == Some("arrow") {
            let length = fs::metadata(&path).unwrap().len();
            if fs::symlink_metadata(&path).unwrap().file_type().is_symlink() {
                linked += length;
            } else {
                written += length;
            }
        }
    }
    (linked, written)
}

#[tokio::test]
async fn import_reference_reuse_extension_and_changed_source() {
    let root = scratch();
    let dataset = fixture(&root.join("source"));
    let registry = root.join("registry");

    // Import: only the demanded columns, in file order across both files.
    let wanted = demand(&dataset, &[("sales", &[0, 1, 3])]);
    let (imported, report) = prepare(&dataset, &wanted, None, &registry, &root.join("a")).unwrap();
    assert_eq!(report.method, PreparationMethod::Imported);
    assert_eq!(
        report.imported_columns,
        vec![("sales".into(), 0), ("sales".into(), 1), ("sales".into(), 3)]
    );
    assert!(report.column_file_bytes > 0);
    let (_, written_ipc) = ipc_file_bytes(&root.join("a"));
    assert_eq!(
        (report.written_ipc_bytes, report.written_native_bytes, report.written_bytes),
        (written_ipc, report.column_file_bytes, written_ipc + report.column_file_bytes),
        "an import writes every IPC and native file"
    );
    assert_eq!(imported.coverage(), vec![("sales".to_string(), vec![0, 1, 3])]);
    assert_eq!(imported.row_count("sales"), Some(5));
    let stamp: serde_json::Value = serde_json::from_str(imported.source_version("sales").unwrap()).unwrap();
    assert_eq!(stamp.as_array().unwrap().len(), 2, "one stamp per file");
    assert_eq!(
        stamp[0].as_array().unwrap().len(),
        8,
        "(path, dev, ino, size, mtime, mtime_nsec, ctime, ctime_nsec)"
    );
    let view = imported.project(&[("sales".into(), vec![0, 1])]).unwrap();
    assert!(view.is_read_only());
    assert_eq!(native_i64(&view, 0), vec![10, 11, 12, 13, 14]);
    let (amounts, amount) = (native_i128(&view, 1), view.descriptors()[1]);
    assert_eq!(
        [amounts[0], amounts[2], amounts[3], amounts[4]],
        [-50, 200, 325, 450],
        "coefficients at scale 2"
    );
    // SAFETY: a nullable descriptor has one validity byte per row, kept alive by `view`.
    let valid = unsafe { std::slice::from_raw_parts(amount.validity, 5) };
    assert_eq!(valid, [1, 0, 1, 1, 1]);
    assert!(matches!(
        imported.project(&[("sales".into(), vec![2])]),
        Err(ImportError::NotCaptured { missing }) if missing == vec![("sales".to_string(), vec![2])]
    ));

    // Reference over the capture: exact decimals, typed parameters, pinned literal typing, refusals.
    let imported = Arc::new(imported);
    let reference = SqlReference::new(imported.clone()).unwrap();
    let sum = reference
        .execute("SELECT SUM(amount) AS total FROM sales")
        .await
        .unwrap();
    let sum = sum[0].column(0).as_any().downcast_ref::<Decimal128Array>().unwrap();
    assert_eq!(sum.value(0), -50 + 200 + 325 + 450);
    let bound = reference
        .execute_bound(
            "SELECT COUNT(*) FROM sales WHERE key > $1",
            &[("BIGINT".into(), ScalarValue::Int64(Some(11)))],
        )
        .await
        .unwrap();
    assert_eq!(
        bound[0]
            .column(0)
            .as_any()
            .downcast_ref::<Int64Array>()
            .unwrap()
            .value(0),
        3
    );
    let literal = reference.result_columns("SELECT 0.2 AS x", &[]).await.unwrap();
    assert!(matches!(literal[0].ty, ColType::Decimal { .. }), "{literal:?}");
    // Typed placeholders plan without values; the result types follow the declared parameter types.
    let typed = reference
        .result_columns(
            "SELECT key, SUM(amount) AS total FROM sales WHERE key > $1 GROUP BY key",
            &["BIGINT".into()],
        )
        .await
        .unwrap();
    assert_eq!(
        typed.iter().map(|c| c.ty).collect::<Vec<_>>(),
        [ColType::I64, ColType::Decimal { p: 22, s: 2 }],
        "{typed:?}"
    );
    let refusal = reference
        .execute("SELECT label FROM sales")
        .await
        .unwrap_err()
        .to_string();
    assert!(refusal.contains("not captured"), "{refusal}");
    assert!(
        reference
            .execute("SELECT id FROM other")
            .await
            .unwrap_err()
            .to_string()
            .contains("not captured")
    );
    assert!(reference.execute("DROP TABLE sales").await.is_err());
    drop(reference);

    // Reuse by name and by registration: no import, the same capture.
    let (named, report) = prepare(
        &dataset,
        &demand(&dataset, &[("sales", &[0])]),
        Some(&root.join("a")),
        &registry,
        &root.join("b"),
    )
    .unwrap();
    assert_eq!(
        (report.method, report.imported_columns.len()),
        (PreparationMethod::ReusedNamed, 0)
    );
    assert_eq!(named.capture_identity(), imported.capture_identity());
    assert!(
        fs::symlink_metadata(root.join("b/inputs"))
            .unwrap()
            .file_type()
            .is_symlink()
    );
    let (registered, report) = prepare(
        &dataset,
        &demand(&dataset, &[("sales", &[1])]),
        None,
        &registry,
        &root.join("c"),
    )
    .unwrap();
    assert_eq!(report.method, PreparationMethod::ReusedRegistered);
    assert_eq!(registered.capture_identity(), imported.capture_identity());
    let sales_order = imported.row_order_identity("sales").unwrap();
    assert!(sales_order.starts_with("receipt:"), "{sales_order}");
    assert_eq!(named.row_order_identity("sales"), Some(sales_order.clone()), "a reused capture keeps the row order");

    // Extension: only the missing columns are read; the base is linked, not changed.
    let base_before = tree(&root.join("a"));
    let wider = demand(&dataset, &[("sales", &[0, 2]), ("other", &[0])]);
    let (extended, report) = prepare(&dataset, &wider, Some(&root.join("a")), &registry, &root.join("d")).unwrap();
    assert_eq!(report.method, PreparationMethod::Extended);
    let built: BTreeSet<_> = report.imported_columns.iter().cloned().collect();
    assert_eq!(
        built,
        BTreeSet::from([("other".to_string(), 0), ("sales".to_string(), 2)])
    );
    let linked: BTreeSet<_> = report.linked_columns.iter().cloned().collect();
    assert_eq!(
        linked,
        BTreeSet::from([
            ("sales".to_string(), 0),
            ("sales".to_string(), 1),
            ("sales".to_string(), 3)
        ])
    );
    assert_eq!(
        tree(&root.join("a")),
        base_before,
        "the base prepared root is unchanged"
    );
    let (linked_ipc, written_ipc) = ipc_file_bytes(&root.join("d"));
    assert!(linked_ipc > 0 && written_ipc > 0 && report.written_native_bytes > 0);
    assert_eq!(
        (report.linked_ipc_bytes, report.written_ipc_bytes),
        (linked_ipc, written_ipc),
        "IPC files linked and written by the extension"
    );
    assert_eq!(report.written_bytes, written_ipc + report.written_native_bytes);
    assert_eq!(report.linked_native_bytes + report.written_native_bytes, report.column_file_bytes);
    let view = extended
        .project(&[("other".into(), vec![0]), ("sales".into(), vec![0, 2])])
        .unwrap();
    assert_eq!(native_i64(&view, 0), vec![7, 8]);
    assert_eq!(native_i64(&view, 1), vec![10, 11, 12, 13, 14]);
    assert_eq!(native_utf8(&view, 2), vec!["l0", "l1", "l2", "l0", "l1"]);
    assert_ne!(extended.capture_identity(), imported.capture_identity());
    assert_eq!(
        extended.row_order_identity("sales"),
        Some(sales_order.clone()),
        "an extension keeps the row-order identity of a widened, unchanged table"
    );
    let other_order = extended.row_order_identity("other").unwrap();
    assert!(other_order != sales_order && other_order.starts_with("receipt:"), "a newly captured table: {other_order}");
    let logical = extended.logical_table("sales").unwrap();
    assert_eq!(logical.original_indices, vec![0, 1, 2, 3]);
    assert_eq!(logical.batches.iter().map(RecordBatch::num_rows).sum::<usize>(), 5);

    // Cold reopen and resume: nothing captured again.
    let reopened = PreparedSource::open(&root.join("d"), &dataset).unwrap();
    assert_eq!(reopened.capture_identity(), extended.capture_identity());
    let (_, report) = prepare(&dataset, &wider, Some(&root.join("a")), &registry, &root.join("d")).unwrap();
    assert_eq!(report.method, PreparationMethod::Resumed);

    // A changed source file (new lifecycle stamp, same values) refuses reuse before any write.
    drop((imported, named, registered, extended, reopened));
    write_parquet(&dataset.tables[0].locations[0], &sales_batch(0..3));
    let refused = prepare(
        &dataset,
        &demand(&dataset, &[("sales", &[0])]),
        Some(&root.join("a")),
        &registry,
        &root.join("e"),
    );
    assert!(
        matches!(refused, Err(ImportError::SourceChanged { ref table }) if table == "sales"),
        "{refused:?}"
    );
    assert!(!root.join("e").exists());
    assert!(matches!(
        PreparedSource::open(&root.join("a"), &dataset),
        Err(ImportError::SourceChanged { .. })
    ));
    // A capture of the changed source is a new read of its files: a new row-order identity.
    let (fresh, report) = prepare(&dataset, &demand(&dataset, &[("sales", &[0])]), None, &registry, &root.join("f")).unwrap();
    assert_eq!(report.method, PreparationMethod::Imported);
    assert_ne!(fresh.row_order_identity("sales"), Some(sales_order));
}

#[test]
fn declared_dataset_and_declaration_binding_refusals() {
    let root = scratch();
    let dataset = fixture(&root.join("source"));
    let registry = root.join("registry");
    let wanted = demand(&dataset, &[("sales", &[0])]);

    // Files must match the declaration exactly.
    let mut wrong_type = dataset.clone();
    wrong_type.tables[0].fields[1].ty = ColType::Decimal { p: 12, s: 3 };
    let error = prepare(&wrong_type, &wanted, None, &registry, &root.join("a")).unwrap_err();
    assert!(matches!(error, ImportError::Source { .. }), "{error}");
    assert!(!root.join("a").exists());
    let mut duplicate_table = dataset.clone();
    duplicate_table.tables[1].name = "sales".into();
    assert!(matches!(
        duplicate_table.validate(),
        Err(ImportError::Declaration { .. })
    ));
    let mut duplicate_field = dataset.clone();
    duplicate_field.tables[0].fields[1].name = "key".into();
    assert!(matches!(
        duplicate_field.validate(),
        Err(ImportError::Declaration { .. })
    ));
    assert!(demand(&dataset, &[]).add_columns(&dataset, "sales", &[5]).is_err());

    // A statement's declaration binds by name, ordinal, type and nullability, and keeps its table order.
    let source_column = |ordinal, name: &str, ty| SourceColumn {
        ordinal,
        name: name.into(),
        ty,
        row_count_only: false,
        nullable: false,
    };
    let nullable_column = |ordinal, name: &str, ty| SourceColumn {
        nullable: true,
        ..source_column(ordinal, name, ty)
    };
    let declaration = |columns: Vec<SourceColumn>| SourceDeclaration {
        tables: vec![
            SourceTable {
                index: 0,
                table_id: 1,
                name: "other".into(),
                columns: vec![source_column(0, "id", SourceType::Int64)],
            },
            SourceTable {
                index: 1,
                table_id: 0,
                name: "sales".into(),
                columns,
            },
        ],
    };
    let good = declaration(vec![
        source_column(0, "key", SourceType::Int64),
        nullable_column(1, "amount", SourceType::Decimal { p: 12, s: 2 }),
        source_column(3, "day", SourceType::Date32),
    ]);
    assert_eq!(
        declaration_projection(&dataset, &good).unwrap(),
        vec![("other".to_string(), vec![0]), ("sales".to_string(), vec![0, 1, 3])]
    );
    for bad in [
        vec![source_column(0, "day", SourceType::Int64)],
        vec![source_column(3, "day", SourceType::Int32)],
        vec![source_column(1, "amount", SourceType::Decimal { p: 12, s: 2 })],
        vec![nullable_column(0, "key", SourceType::Int64)],
        vec![
            source_column(3, "day", SourceType::Date32),
            source_column(0, "key", SourceType::Int64),
        ],
    ] {
        let error = declaration_projection(&dataset, &declaration(bad)).unwrap_err();
        assert!(matches!(error, ImportError::Demand { .. }), "{error}");
    }
}

#[test]
fn widening_extension_links_base_and_refuses_changed_declarations() {
    let root = scratch();
    let wide = {
        let mut dataset = fixture(&root.join("source"));
        let spare = root.join("source/spare.parquet");
        let schema = Arc::new(Schema::new(vec![Field::new("n", DataType::Int64, false)]));
        write_parquet(&spare, &RecordBatch::try_new(schema, vec![Arc::new(Int64Array::from(vec![1]))]).unwrap());
        dataset.tables.push(TableSpec {
            name: "spare".into(),
            fields: vec![column("n", ColType::I64, false)],
            locations: vec![spare],
            format: DataFormat::Parquet,
        });
        dataset.with_canonical_locations().unwrap()
    };
    let base = DatasetSpec {
        tables: vec![wide.tables[0].clone()],
    };
    let registry = root.join("registry");
    let (imported, _) = prepare(&base, &demand(&base, &[("sales", &[0, 1, 3])]), None, &registry, &root.join("a")).unwrap();
    let sales_order = imported.row_order_identity("sales").unwrap();
    let sales_version = imported.source_version("sales").unwrap().to_string();
    let base_before = tree(&root.join("a"));

    // Widening: base columns linked, only demanded missing columns read, every appended table versioned.
    let wanted = demand(&wide, &[("sales", &[0, 2]), ("other", &[0])]);
    let (widened, report) = prepare(&wide, &wanted, Some(&root.join("a")), &registry, &root.join("w")).unwrap();
    assert_eq!(report.method, PreparationMethod::Extended);
    assert_eq!(report.widened_tables, vec!["other".to_string(), "spare".to_string()]);
    let built: BTreeSet<_> = report.imported_columns.iter().cloned().collect();
    assert_eq!(built, BTreeSet::from([("other".to_string(), 0), ("sales".to_string(), 2)]));
    let linked: BTreeSet<_> = report.linked_columns.iter().cloned().collect();
    assert_eq!(linked, BTreeSet::from([("sales".to_string(), 0), ("sales".to_string(), 1), ("sales".to_string(), 3)]));
    assert_eq!(tree(&root.join("a")), base_before, "the base prepared root is unchanged");
    assert_eq!(widened.dataset(), &wide);
    assert_eq!(widened.source_version("sales"), Some(sales_version.as_str()), "a base table keeps its version");
    assert!(widened.source_version("other").is_some());
    assert!(widened.source_version("spare").is_some(), "an appended table without demand is versioned");
    assert_eq!(widened.row_count("spare"), None, "and not captured");
    assert_eq!(widened.row_order_identity("sales"), Some(sales_order.clone()));
    assert_ne!(widened.row_order_identity("other"), Some(sales_order.clone()));
    let view = widened
        .project(&[("other".into(), vec![0]), ("sales".into(), vec![0, 2])])
        .unwrap();
    assert_eq!(native_i64(&view, 0), vec![7, 8]);
    assert_eq!(native_i64(&view, 1), vec![10, 11, 12, 13, 14]);
    assert_eq!(native_utf8(&view, 2), vec!["l0", "l1", "l2", "l0", "l1"]);
    let record: serde_json::Value = serde_json::from_slice(&fs::read(root.join("w/extension.json")).unwrap()).unwrap();
    assert_eq!(record["widened_tables"], serde_json::json!(["other", "spare"]));

    // Reopen and resume under the wider dataset only.
    let reopened = PreparedSource::open(&root.join("w"), &wide).unwrap();
    assert_eq!(reopened.capture_identity(), widened.capture_identity());
    assert!(matches!(PreparedSource::open(&root.join("w"), &base), Err(ImportError::Prepared { .. })));
    let (_, report) = prepare(&wide, &wanted, Some(&root.join("a")), &registry, &root.join("w")).unwrap();
    assert_eq!(report.method, PreparationMethod::Resumed);

    // A widening without missing columns still extends (a new receipt declares the wider dataset), writing no column.
    let (covered, report) = prepare(&wide, &demand(&wide, &[("sales", &[0])]), Some(&root.join("a")), &registry, &root.join("x")).unwrap();
    assert_eq!((report.method, report.imported_columns.len(), report.written_native_bytes), (PreparationMethod::Extended, 0, 0));
    assert_eq!(covered.row_order_identity("sales"), Some(sales_order));
    // The equal-dataset path is unchanged.
    let (_, report) = prepare(&base, &demand(&base, &[("sales", &[0])]), Some(&root.join("a")), &registry, &root.join("y")).unwrap();
    assert_eq!(report.method, PreparationMethod::ReusedNamed);

    // Any change to a base table's declaration, or to the base's table order, is refused before any write.
    let edits: [fn(&mut TableSpec); 4] = [
        |t: &mut TableSpec| t.locations.reverse(),
        |t: &mut TableSpec| t.fields[1].ty = ColType::Decimal { p: 12, s: 3 },
        |t: &mut TableSpec| t.fields[0].nullable = true,
        |t: &mut TableSpec| t.fields.swap(0, 3),
    ];
    let mut changed = vec![];
    for edit in edits {
        let mut dataset = wide.clone();
        edit(&mut dataset.tables[0]);
        changed.push(dataset);
    }
    let mut reordered = wide.clone();
    reordered.tables.swap(0, 1);
    changed.push(reordered);
    for dataset in changed {
        let refused = prepare(&dataset, &demand(&dataset, &[("other", &[0])]), Some(&root.join("a")), &registry, &root.join("z"));
        assert!(matches!(refused, Err(ImportError::Prepared { .. })), "{refused:?}");
        assert!(!root.join("z").exists());
    }
    // An appended table's files must match its declaration, even when it is not demanded.
    let mut mistyped = wide.clone();
    mistyped.tables[2].fields[0].ty = ColType::I32;
    let refused = prepare(&mistyped, &demand(&mistyped, &[("sales", &[0])]), Some(&root.join("a")), &registry, &root.join("z"));
    assert!(matches!(refused, Err(ImportError::Source { .. })), "{refused:?}");
    assert!(!root.join("z").exists());
}
