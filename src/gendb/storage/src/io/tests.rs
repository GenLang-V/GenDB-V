//! Scoped checks of storage I/O on tiny tables, plus one ignored check against saved prepared archives
//! (`saved_view_archives_map_to_identical_columns`). Scratch lives under a scratch `TMPDIR`, never `/tmp`.

use super::*;
use arrow::{array::*, record_batch::RecordBatch};
use gendb_artifacts::{ColType, ColumnSpec};
use std::{fs, path::PathBuf, sync::Arc};

/// A fresh, not yet existing path `$TMPDIR/gendb-storage-io-tests/<pid>-<nanos>-<n>`.
fn scratch() -> PathBuf {
    static NEXT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let lane = PathBuf::from(std::env::var_os("TMPDIR").expect("a scratch TMPDIR is required; /tmp is forbidden"));
    assert!(!lane.starts_with("/tmp"), "TMPDIR must be a scratch directory, not /tmp");
    let root = lane.join("gendb-storage-io-tests");
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

fn spec(name: &str, ty: ColType, nullable: bool) -> ColumnSpec {
    ColumnSpec {
        name: name.into(),
        ty,
        nullable,
    }
}

fn batch(fields: &[ColumnSpec], arrays: Vec<ArrayRef>) -> RecordBatch {
    RecordBatch::try_new(ipc::arrow_schema(fields).unwrap(), arrays).unwrap()
}

/// Every canonical type, nulls, a wide decimal and multi-byte text: 3 rows, declared ordinals 1,3,4,6,8,9.
fn fixture() -> ProjectedTable {
    let fields = vec![
        spec("n", ColType::I64, true),
        spec("b", ColType::Bool, true),
        spec("d", ColType::Date32, false),
        spec("money", ColType::Decimal { p: 38, s: 4 }, true),
        spec("text", ColType::Utf8, true),
        spec("u", ColType::U64, false),
    ];
    let arrays: Vec<ArrayRef> = vec![
        Arc::new(Int64Array::from(vec![Some(-8), None, Some(17)])),
        Arc::new(BooleanArray::from(vec![Some(true), None, Some(false)])),
        Arc::new(Date32Array::from(vec![-100, 0, 20])),
        Arc::new(
            Decimal128Array::from(vec![Some(i128::MAX / 100), None, Some(-123)])
                .with_precision_and_scale(38, 4)
                .unwrap(),
        ),
        Arc::new(StringArray::from(vec![Some("λ猫"), None, Some("")])),
        Arc::new(UInt64Array::from(vec![u64::MAX, 0, 7])),
    ];
    let batch = batch(&fields, arrays);
    ProjectedTable {
        table: "arbitrary".into(),
        original_indices: vec![1, 3, 4, 6, 8, 9],
        fields,
        batches: vec![batch],
        row_count: 3,
    }
}

#[test]
fn shared_column_files_map_without_ipc_decode_and_reject_stale_version() {
    let base = SourceColumns::from_projected(vec![fixture()]).unwrap();
    let path = scratch();
    base.write_archive(&path).unwrap();
    let mapped = base.write_and_map_column_files(&path).unwrap();
    assert!(mapped.is_read_only());
    assert!(SourceColumns::column_file_bytes(&path).unwrap() > 0);
    let view = mapped.project(&[("arbitrary".into(), vec![1, 8])]).unwrap();
    let (view, copied) = view.read_only().unwrap();
    assert_eq!(
        copied,
        2 * std::mem::size_of::<NativeColumn>() as u64,
        "only the new descriptor array is copied"
    );
    assert_eq!(view.descriptors()[0].values, mapped.descriptors()[0].values);
    let view_path = scratch();
    view.write_archive(&view_path).unwrap();
    assert_eq!(
        fs::read_dir(&view_path).unwrap().count(),
        2,
        "projection stores metadata only"
    );
    fs::rename(path.join("table-0.arrow"), path.join("reference-retained.arrow")).unwrap();
    let execution = SourceColumns::map_archive(&view_path).unwrap();
    assert_eq!(execution.capture_identity(), view.capture_identity());
    assert!(
        execution.tables()[0].batches.is_empty(),
        "execution mapping does not decode IPC"
    );
    assert_eq!(unsafe { *execution.descriptors()[0].values.cast::<i64>() }, -8);
    assert_eq!(execution.read_only().unwrap().1, 0);
    fs::write(path.join("capture-version.txt"), "different-source-version").unwrap();
    assert!(SourceColumns::map_archive(&view_path).is_err());
}

/// The captured columns of an archive are listed from its column-files manifest with a mapping's checks: a non-null
/// date and text column with their buffer files and extents, a nullable column with its validity file (one byte per
/// row, 0 for NULL); a view is refused.
#[test]
fn captured_columns_list_canonical_buffer_files() {
    let fields = vec![spec("d", ColType::Date32, false), spec("t", ColType::Utf8, false)];
    let arrays: Vec<ArrayRef> = vec![Arc::new(Date32Array::from(vec![-100, 0, 20])), Arc::new(StringArray::from(vec!["λ猫", "", "x"]))];
    let table = ProjectedTable { table: "flat".into(), original_indices: vec![0, 2], fields: fields.clone(), batches: vec![batch(&fields, arrays)], row_count: 3 };
    let path = scratch();
    let base = SourceColumns::from_projected(vec![table]).unwrap();
    base.write_archive(&path).unwrap();
    let mapped = base.write_and_map_column_files(&path).unwrap();
    let columns = SourceColumns::captured_columns(&path).unwrap();
    assert_eq!(columns.iter().map(|c| (c.table.as_str(), c.ordinal, c.rows)).collect::<Vec<_>>(), [("flat", 0, 3), ("flat", 2, 3)]);
    assert_eq!((columns[0].values.as_ref().unwrap().bytes, columns[0].offsets.is_none()), (12, true));
    assert_eq!((columns[1].values.is_none(), columns[1].offsets.as_ref().unwrap().bytes), (true, 32));
    for buffer in [&columns[0].values, &columns[1].offsets, &columns[1].bytes] {
        let buffer = buffer.as_ref().unwrap();
        assert_eq!(fs::metadata(&buffer.path).unwrap().len(), buffer.bytes, "the named file has the manifest's extent");
    }
    let view_path = scratch();
    mapped.project(&[("flat".into(), vec![2])]).unwrap().read_only().unwrap().0.write_archive(&view_path).unwrap();
    assert!(SourceColumns::captured_columns(&view_path).is_err(), "a view has no column files of its own");
    let nullable = scratch();
    let with_nulls = SourceColumns::from_projected(vec![fixture()]).unwrap();
    with_nulls.write_archive(&nullable).unwrap();
    with_nulls.write_and_map_column_files(&nullable).unwrap();
    let columns = SourceColumns::captured_columns(&nullable).unwrap();
    let column = |name: &str| columns.iter().find(|c| c.field.name == name).unwrap();
    for (name, values) in [("n", true), ("money", true), ("text", false)] {
        let c = column(name);
        let validity = c.validity.as_ref().unwrap_or_else(|| panic!("{name}: validity"));
        assert_eq!((c.field.nullable, c.values.is_some(), validity.bytes), (true, values, 3), "{name}");
        assert_eq!(fs::read(&validity.path).unwrap(), [1, 0, 1], "{name}: row 1 is NULL");
    }
    assert!(column("d").validity.is_none() && !column("d").field.nullable, "a NOT NULL column has no validity file");
    let listed = serde_json::to_value(column("d")).unwrap();
    assert!(listed.get("validity").is_none(), "nor a validity field: {listed}");
}

#[test]
fn archive_views_preserve_buffers_and_scope_reads() {
    let path = scratch();
    let mut other = fixture();
    other.table = "unneeded".into();
    let base = SourceColumns::from_projected(vec![fixture(), other]).unwrap();
    base.write_archive(&path).unwrap();
    let base = SourceColumns::decode_archive(&path).unwrap();
    let view = base.project(&[("arbitrary".into(), vec![1, 8])]).unwrap();
    assert_eq!(view.descriptors()[0].values, base.descriptors()[0].values);
    assert_eq!(view.descriptors()[1].bytes, base.descriptors()[4].bytes);
    assert_eq!(view.bindings()[1].original_index, Some(8));
    assert_eq!(view.bindings()[1].descriptor_index, 1);
    let count = base.project(&[("arbitrary".into(), vec![])]).unwrap();
    assert_eq!(count.descriptors()[0].len, 3);
    assert_eq!(count.descriptors()[0].type_tag, NATIVE_TYPE_CARDINALITY);
    assert!(
        matches!(
            base.project(&[("arbitrary".into(), vec![2])]),
            Err(StorageIoError::Shape(_))
        ),
        "uncaptured column"
    );
    let view_path = scratch();
    view.write_archive(&view_path).unwrap();
    assert_eq!(fs::read_dir(&view_path).unwrap().count(), 2);
    // A query must not reopen unrelated tables of the base.
    fs::rename(path.join("table-1.arrow"), path.join("table-1.retained")).unwrap();
    let loaded = SourceColumns::decode_archive(&view_path).unwrap();
    assert_eq!(loaded.capture_identity(), view.capture_identity());
    assert_eq!(loaded.tables()[0].original_indices, vec![1, 8]);
    drop(base);
    drop(view);
    assert_eq!(unsafe { *loaded.descriptors()[0].values.cast::<i64>() }, -8);
    let smaller = loaded.project(&[("arbitrary".into(), vec![8])]).unwrap();
    let smaller_path = scratch();
    smaller.write_archive(&smaller_path).unwrap();
    assert_eq!(
        SourceColumns::decode_archive(&smaller_path).unwrap().capture_identity(),
        smaller.capture_identity()
    );
    fs::write(view_path.join("capture-version.txt"), b"forged").unwrap();
    assert!(SourceColumns::decode_archive(&view_path).is_err());
}

#[test]
fn exact_nullable_buffers_archive_and_concurrent_reads() {
    let input = Arc::new(SourceColumns::from_projected(vec![fixture()]).unwrap());
    let d = input.descriptors();
    unsafe {
        assert_eq!(std::slice::from_raw_parts(d[0].values.cast::<i64>(), 3), [-8, 0, 17]);
        assert_eq!(std::slice::from_raw_parts(d[0].validity, 3), [1, 0, 1]);
        assert_eq!(std::slice::from_raw_parts(d[1].values, 3), [1, 0, 0]);
        assert_eq!(std::slice::from_raw_parts(d[2].values.cast::<i32>(), 3), [-100, 0, 20]);
        assert_eq!(*d[3].values.cast::<i128>(), i128::MAX / 100);
        assert_eq!(*d[5].values.cast::<u64>(), u64::MAX);
        let offsets = std::slice::from_raw_parts(d[4].offsets, 4);
        assert_eq!(
            std::str::from_utf8(std::slice::from_raw_parts(d[4].bytes, offsets[1] as usize)).unwrap(),
            "λ猫"
        );
    }
    assert_eq!(
        d.iter().map(|c| c.type_tag).collect::<Vec<_>>(),
        [
            NATIVE_TYPE_I64,
            NATIVE_TYPE_BOOL,
            NATIVE_TYPE_I32,
            NATIVE_TYPE_I128,
            NATIVE_TYPE_UTF8,
            NATIVE_TYPE_U64
        ]
    );
    let path = scratch();
    input.write_archive(&path).unwrap();
    let loaded = SourceColumns::decode_archive(&path).unwrap();
    assert_eq!(loaded.capture_identity(), input.capture_identity());
    assert_eq!(loaded.bindings(), input.bindings());
    assert_eq!(loaded.tables()[0].batches, input.tables()[0].batches);
    std::thread::scope(|scope| {
        for _ in 0..4 {
            let input = input.clone();
            scope.spawn(move || {
                for _ in 0..100 {
                    assert_eq!(
                        unsafe { *input.descriptors()[3].values.cast::<i128>() },
                        i128::MAX / 100
                    );
                }
            });
        }
    });
}

#[test]
fn adopted_multibatch_ipc_reexports_exact_bytes_and_refuses_changed_source() {
    let mut table = fixture();
    let whole = table.batches[0].clone();
    table.batches = vec![whole.slice(0, 1), whole.slice(1, 2)];
    let path = scratch();
    fs::create_dir(&path).unwrap();
    ipc::write_ipc(&table, fs::File::create(path.join("table-0.arrow")).unwrap()).unwrap();
    let input = SourceColumns::adopt_ipc_archive(&path, &[table]).unwrap();
    assert!(input.is_read_only());
    let copied = scratch();
    input.write_archive(&copied).unwrap();
    let reopened = SourceColumns::decode_archive(&copied).unwrap();
    assert_eq!(reopened.capture_identity(), input.capture_identity());
    assert_eq!(
        fs::read(path.join("table-0.arrow")).unwrap(),
        fs::read(copied.join("table-0.arrow")).unwrap()
    );
    fs::write(path.join("table-0.arrow"), b"changed archive").unwrap();
    assert!(
        input
            .write_archive(&scratch())
            .unwrap_err()
            .to_string()
            .contains("changed during re-export")
    );
}

#[test]
fn sliced_multibatch_empty_and_row_count_only_inputs() {
    let mut f = fixture();
    let whole = f.batches[0].clone();
    f.batches = vec![whole.slice(1, 1), whole.slice(2, 1)];
    f.row_count = 2;
    let x = SourceColumns::from_projected(vec![f]).unwrap();
    assert_eq!(unsafe { *x.descriptors()[0].validity }, 0);
    let p = scratch();
    x.write_archive(&p).unwrap();
    assert_eq!(
        SourceColumns::decode_archive(&p).unwrap().capture_identity(),
        x.capture_identity()
    );
    let mut empty = fixture();
    empty.batches.clear();
    empty.row_count = 0;
    let count = ProjectedTable {
        table: "count".into(),
        original_indices: vec![],
        fields: vec![],
        batches: vec![],
        row_count: 125,
    };
    let x = SourceColumns::from_projected(vec![empty, count]).unwrap();
    assert_eq!(x.descriptors()[0].len, 0);
    assert_eq!(x.descriptors()[6].len, 125);
    assert_eq!(x.descriptors()[6].type_tag, NATIVE_TYPE_CARDINALITY);
    assert!(x.descriptors()[6].values.is_null());
    let p = scratch();
    x.write_archive(&p).unwrap();
    assert_eq!(
        SourceColumns::decode_archive(&p).unwrap().capture_identity(),
        x.capture_identity()
    );
    let mapped = SourceColumns::map_archive(&p).unwrap();
    assert_eq!(mapped.bindings(), x.bindings());
    assert_eq!(mapped.descriptors()[6].len, 125);
}

#[test]
fn utf8_single_slice_keeps_wide_absolute_offsets_and_shared_logical_bytes() {
    let field = spec("s", ColType::Utf8, true);
    let full = StringArray::from(vec![Some("prefix"), Some("λ猫"), None, Some(""), Some("tail")]);
    let array = Arc::new(full.slice(1, 3)) as ArrayRef;
    let batch = batch(std::slice::from_ref(&field), vec![array]);
    let input = SourceColumns::from_projected(vec![ProjectedTable {
        table: "slices".into(),
        original_indices: vec![0],
        fields: vec![field],
        batches: vec![batch],
        row_count: 3,
    }])
    .unwrap();
    let d = input.descriptors()[0];
    assert_eq!(std::mem::size_of::<NativeColumn>(), 48);
    unsafe {
        assert_eq!(std::slice::from_raw_parts(d.offsets, 4), [6_i64, 11, 11, 11]);
        assert_eq!(std::slice::from_raw_parts(d.validity, 3), [1, 0, 1]);
        assert_eq!(std::slice::from_raw_parts(d.bytes.add(6), 5), "λ猫".as_bytes());
    }
    let logical = input.tables()[0].batches[0]
        .column(0)
        .as_any()
        .downcast_ref::<StringArray>()
        .unwrap();
    assert_eq!(logical.value(0), "λ猫");
    assert!(logical.is_null(1));
    assert_eq!(logical.value(2), "");
    assert_eq!(logical.values().as_ptr(), unsafe { d.bytes.add(6) });
    let path = scratch();
    input.write_archive(&path).unwrap();
    let reopened = SourceColumns::decode_archive(&path).unwrap();
    assert_eq!(reopened.capture_identity(), input.capture_identity());
    assert_eq!(reopened.tables()[0].batches, input.tables()[0].batches);
    // The mapped column files deliver the same absolute offsets and bytes.
    let mapped = SourceColumns::map_archive(&path).unwrap();
    unsafe {
        assert_eq!(
            std::slice::from_raw_parts(mapped.descriptors()[0].offsets, 4),
            [6_i64, 11, 11, 11]
        )
    };
}

#[test]
fn normalization_rejects_schema_rows_nulls_and_ordinal_disagreement() {
    let mut f = fixture();
    f.row_count += 1;
    assert!(matches!(
        SourceColumns::from_projected(vec![f]),
        Err(StorageIoError::Shape(_))
    ));
    let mut f = fixture();
    f.fields[0].ty = ColType::I32;
    assert!(SourceColumns::from_projected(vec![f]).is_err());
    let mut f = fixture();
    f.original_indices[1] = 1;
    assert!(SourceColumns::from_projected(vec![f]).is_err());
    let mut f = fixture();
    f.fields[0].nullable = false;
    assert!(
        SourceColumns::from_projected(vec![f]).is_err(),
        "NULL in a non-nullable column"
    );
    let mut f = fixture();
    f.fields[0].ty = ColType::Binary;
    assert!(matches!(
        SourceColumns::from_projected(vec![f]),
        Err(StorageIoError::UnsupportedType(ColType::Binary))
    ));
    assert!(
        SourceColumns::from_projected(vec![fixture(), fixture()]).is_err(),
        "duplicate table"
    );
    let mut changed = fixture();
    changed.table = "changed".into();
    assert_ne!(
        SourceColumns::from_projected(vec![fixture()])
            .unwrap()
            .capture_identity(),
        SourceColumns::from_projected(vec![changed]).unwrap().capture_identity()
    );
}

#[test]
fn remaining_integer_widths_and_nonzero_null_payloads_roundtrip() {
    let fields = vec![spec("i", ColType::I32, true), spec("u", ColType::U32, false)];
    let signed = Int32Array::new(
        vec![i32::MIN, 12345].into(),
        Some(arrow::buffer::NullBuffer::from(vec![true, false])),
    );
    let batch = batch(
        &fields,
        vec![Arc::new(signed), Arc::new(UInt32Array::from(vec![u32::MAX, 0]))],
    );
    let x = SourceColumns::from_projected(vec![ProjectedTable {
        table: "widths".into(),
        original_indices: vec![0, 1],
        fields,
        batches: vec![batch],
        row_count: 2,
    }])
    .unwrap();
    let p = scratch();
    x.write_archive(&p).unwrap();
    let y = SourceColumns::decode_archive(&p).unwrap();
    assert_eq!(y.capture_identity(), x.capture_identity());
    unsafe {
        assert_eq!(
            std::slice::from_raw_parts(y.descriptors()[0].values.cast::<i32>(), 2),
            [i32::MIN, 12345]
        );
        assert_eq!(*y.descriptors()[1].values.cast::<u32>(), u32::MAX);
    }
}

/// Controls: encoding views of the earlier GenDB version, a column-file type tag contradicting its declared field, and a sidecar binding
/// with a (legacy) non-canonical `encoding` field are refused by execution mapping.
#[test]
fn execution_mapping_refuses_v7_encodings_and_contradicting_metadata() {
    let path = scratch();
    SourceColumns::from_projected(vec![fixture()])
        .unwrap()
        .write_archive(&path)
        .unwrap();
    SourceColumns::map_archive(&path).unwrap();
    fs::write(path.join("decimal-views.json"), b"{}").unwrap();
    assert!(matches!(
        SourceColumns::map_archive(&path),
        Err(StorageIoError::V7Only {
            file: "decimal-views.json",
            ..
        })
    ));
    fs::remove_file(path.join("decimal-views.json")).unwrap();

    let manifest_path = path.join("native-buffers/manifest.json");
    let saved = fs::read(&manifest_path).unwrap();
    let rewrite = |edit: &dyn Fn(&mut serde_json::Value)| {
        let mut manifest: serde_json::Value = serde_json::from_slice(&saved).unwrap();
        edit(&mut manifest);
        let mut permissions = fs::metadata(&manifest_path).unwrap().permissions();
        #[allow(clippy::permissions_set_readonly_false)]
        permissions.set_readonly(false);
        fs::set_permissions(&manifest_path, permissions).unwrap();
        fs::write(&manifest_path, serde_json::to_vec(&manifest).unwrap()).unwrap();
    };
    rewrite(&|m| m["columns"][2]["type_tag"] = NATIVE_TYPE_I64.into());
    assert!(matches!(
        SourceColumns::map_archive(&path),
        Err(StorageIoError::Archive { .. })
    ));
    rewrite(&|m| m["columns"][3]["binding"]["encoding"] = "DecimalCoefficientI64V1".into());
    assert!(matches!(
        SourceColumns::map_archive(&path),
        Err(StorageIoError::Json { .. })
    ));
    rewrite(&|_| {});
    SourceColumns::map_archive(&path).unwrap();
}

/// An extension links every base column file and writes only the added column, with a fresh lifecycle version.
#[test]
fn extended_archive_links_base_files_and_writes_only_added_columns() {
    let base_path = scratch();
    let base = SourceColumns::from_projected(vec![fixture()]).unwrap();
    base.write_archive(&base_path).unwrap();
    let added_field = spec("extra", ColType::I32, false);
    let added = ProjectedTable {
        table: "arbitrary".into(),
        original_indices: vec![2],
        fields: vec![added_field.clone()],
        batches: vec![batch(
            std::slice::from_ref(&added_field),
            vec![Arc::new(Int32Array::from(vec![5, 6, 7]))],
        )],
        row_count: 3,
    };
    let mut ordinals = fixture().original_indices;
    ordinals.push(2);
    ordinals.sort_unstable();
    let mut fields = fixture().fields;
    fields.insert(1, added_field);
    let layout = [ArchiveTableLayout {
        table: "arbitrary".into(),
        original_indices: ordinals,
        fields,
        row_count: 3,
        ipc_bytes: 0,
        segments: vec![],
    }];
    let path = scratch();
    fs::create_dir(&path).unwrap();
    let extension = SourceColumns::adopt_extended_archive(&base_path, &path, &layout, vec![added.clone()]).unwrap();
    assert_eq!(extension.built_columns, vec![("arbitrary".to_string(), 2)]);
    assert_eq!(extension.reused_columns.len(), 6);
    assert_eq!(extension.written_bytes, 12);
    assert_eq!(
        extension.linked_bytes,
        SourceColumns::column_file_bytes(&base_path).unwrap()
    );
    let mapped = SourceColumns::map_archive(&path).unwrap();
    assert_eq!(mapped.capture_identity(), extension.capture_identity);
    assert_ne!(mapped.capture_identity(), base.capture_identity());
    let extra = mapped.descriptors()[1];
    assert_eq!(
        unsafe { std::slice::from_raw_parts(extra.values.cast::<i32>(), 3) },
        [5, 6, 7]
    );
    assert_eq!(unsafe { *mapped.descriptors()[0].values.cast::<i64>() }, -8);
    let again = scratch();
    fs::create_dir(&again).unwrap();
    assert!(
        SourceColumns::adopt_extended_archive(&base_path, &again, &layout, vec![fixture(), added]).is_err(),
        "base column added again"
    );
}

/// Saved-data check (run explicitly; reads no whole column). For each saved view archive in `GENDB_SAVED_VIEWS`
/// (comma-separated), mapped through the new reader:
/// - the view identity equals the saved `capture-version.txt` and a re-exported view is byte-identical;
/// - bindings equal the earlier-version-written column-file bindings of the base (descriptor positions renumbered);
/// - rows 0, 1, n-2, n-1 of every column equal the base column files read with `pread`, and rows 0, 1 equal the first
///   Arrow IPC batch of the base table file;
/// - projecting an uncaptured column is refused.
///
/// A JSON report is written to `GENDB_SAVED_VIEWS_REPORT`.
#[test]
#[ignore = "reads saved prepared archives; set GENDB_SAVED_VIEWS and GENDB_SAVED_VIEWS_REPORT"]
fn saved_view_archives_map_to_identical_columns() {
    use std::os::unix::fs::FileExt;
    let views = std::env::var("GENDB_SAVED_VIEWS").expect("GENDB_SAVED_VIEWS");
    let report_path = PathBuf::from(std::env::var("GENDB_SAVED_VIEWS_REPORT").expect("GENDB_SAVED_VIEWS_REPORT"));
    let mut report = vec![];
    for view_dir in views.split(',').map(PathBuf::from) {
        let started = std::time::Instant::now();
        let columns = SourceColumns::map_archive(&view_dir).unwrap();
        let map_ns = started.elapsed().as_nanos();
        let saved_identity = fs::read_to_string(view_dir.join("capture-version.txt")).unwrap();
        assert_eq!(columns.capture_identity(), saved_identity);
        let exported = scratch();
        columns.write_archive(&exported).unwrap();
        for file in ["view.json", "capture-version.txt"] {
            assert_eq!(
                fs::read(exported.join(file)).unwrap(),
                fs::read(view_dir.join(file)).unwrap(),
                "{file}"
            );
        }
        let view: serde_json::Value = serde_json::from_slice(&fs::read(view_dir.join("view.json")).unwrap()).unwrap();
        let base = PathBuf::from(view["source"].as_str().unwrap());
        let base_files: serde_json::Value =
            serde_json::from_slice(&fs::read(base.join("native-buffers/manifest.json")).unwrap()).unwrap();
        let base_manifest: serde_json::Value =
            serde_json::from_slice(&fs::read(base.join("manifest.json")).unwrap()).unwrap();
        let mut checked = vec![];
        for (binding, descriptor) in columns.bindings().iter().zip(columns.descriptors()) {
            let saved = base_files["columns"]
                .as_array()
                .unwrap()
                .iter()
                .find(|c| {
                    c["binding"]["table"] == binding.table.as_str()
                        && c["binding"]["original_index"] == serde_json::json!(binding.original_index)
                })
                .expect("column in base column files");
            let mut expected = saved["binding"].clone();
            expected["descriptor_index"] = binding.descriptor_index.into();
            assert_eq!(serde_json::to_value(binding).unwrap(), expected);
            assert_eq!(descriptor.type_tag, saved["type_tag"].as_i64().unwrap() as i32);
            let rows = binding.row_count;
            let file = |role: &str| {
                fs::File::open(base.join("native-buffers").join(saved[role]["file"].as_str().unwrap())).unwrap()
            };
            let boundary = [0, 1, rows - 2, rows - 1];
            let (mapped_cells, file_cells): (Vec<String>, Vec<String>) = boundary
                .iter()
                .map(|&row| match descriptor.type_tag {
                    NATIVE_TYPE_UTF8 => {
                        let offsets = file("offsets");
                        let mut pair = [0u8; 16];
                        offsets.read_exact_at(&mut pair, row as u64 * 8).unwrap();
                        let start = i64::from_le_bytes(pair[..8].try_into().unwrap());
                        let end = i64::from_le_bytes(pair[8..].try_into().unwrap());
                        let mut text = vec![0u8; (end - start) as usize];
                        file("bytes").read_exact_at(&mut text, start as u64).unwrap();
                        (mapped_cell(descriptor, row), String::from_utf8(text).unwrap())
                    }
                    tag => {
                        let width = match tag {
                            NATIVE_TYPE_I32 => 4,
                            NATIVE_TYPE_I64 => 8,
                            NATIVE_TYPE_I128 => 16,
                            other => panic!("unexpected tag {other} in saved Q6/Q4 inputs"),
                        };
                        let mut bytes = vec![0u8; width];
                        file("values").read_exact_at(&mut bytes, (row * width) as u64).unwrap();
                        let mut wide = [if bytes[width - 1] & 0x80 != 0 { 0xff } else { 0 }; 16];
                        wide[..width].copy_from_slice(&bytes);
                        (mapped_cell(descriptor, row), i128::from_le_bytes(wide).to_string())
                    }
                })
                .unzip();
            assert_eq!(
                mapped_cells, file_cells,
                "{} ordinal {:?}",
                binding.table, binding.original_index
            );
            let ipc_cells = first_ipc_rows(&base, &base_manifest, &binding.table, binding.original_index.unwrap());
            assert_eq!(mapped_cells[..2], ipc_cells[..], "first IPC batch of {}", binding.table);
            checked.push(
                serde_json::json!({"table": binding.table, "ordinal": binding.original_index, "field": binding.field,
                "rows": rows, "type_tag": descriptor.type_tag, "boundary_rows": boundary, "values": mapped_cells}),
            );
        }
        let table = columns.tables()[0].table.clone();
        let captured = base_manifest["tables"]
            .as_array()
            .unwrap()
            .iter()
            .find(|t| t["table"] == table.as_str())
            .unwrap()["original_indices"]
            .clone();
        let uncaptured = (0..64)
            .find(|o| !captured.as_array().unwrap().contains(&(*o).into()))
            .unwrap();
        let refusal = SourceColumns::map_archive(&base)
            .unwrap()
            .project(&[(table.clone(), vec![uncaptured])])
            .err()
            .unwrap()
            .to_string();
        report.push(serde_json::json!({"view": view_dir, "base": base, "capture_identity": saved_identity, "map_archive_ns": map_ns,
            "base_column_file_bytes": SourceColumns::column_file_bytes(&base).unwrap(), "reexported_view_identical": true,
            "columns": checked, "uncaptured_projection": {"table": table, "ordinal": uncaptured, "refusal": refusal}}));
    }
    fs::write(&report_path, serde_json::to_vec_pretty(&report).unwrap()).unwrap();
}

/// A mapped cell as text: integers in decimal (decimal coefficients unscaled), strings verbatim.
fn mapped_cell(column: &NativeColumn, row: usize) -> String {
    unsafe {
        match column.type_tag {
            NATIVE_TYPE_I32 => (*column.values.cast::<i32>().add(row)).to_string(),
            NATIVE_TYPE_I64 => (*column.values.cast::<i64>().add(row)).to_string(),
            NATIVE_TYPE_I128 => std::ptr::read_unaligned(column.values.cast::<i128>().add(row)).to_string(),
            NATIVE_TYPE_UTF8 => {
                let start = *column.offsets.add(row) as usize;
                let end = *column.offsets.add(row + 1) as usize;
                String::from_utf8(std::slice::from_raw_parts(column.bytes.add(start), end - start).to_vec()).unwrap()
            }
            other => panic!("unexpected tag {other}"),
        }
    }
}

/// Rows 0 and 1 of one column, decoded from the first batch of the base archive's IPC table file.
fn first_ipc_rows(base: &std::path::Path, manifest: &serde_json::Value, table: &str, ordinal: usize) -> Vec<String> {
    let tables = manifest["tables"].as_array().unwrap();
    let index = tables.iter().position(|t| t["table"] == table).unwrap();
    let position = tables[index]["original_indices"]
        .as_array()
        .unwrap()
        .iter()
        .position(|o| o.as_u64() == Some(ordinal as u64))
        .unwrap();
    let file = fs::File::open(base.join(format!("table-{index}.arrow"))).unwrap();
    let batch = arrow::ipc::reader::StreamReader::try_new(file, None)
        .unwrap()
        .next()
        .unwrap()
        .unwrap();
    let column = batch.column(position);
    (0..2)
        .map(|row| {
            if let Some(a) = column.as_any().downcast_ref::<Decimal128Array>() {
                a.value(row).to_string()
            } else if let Some(a) = column.as_any().downcast_ref::<Date32Array>() {
                a.value(row).to_string()
            } else if let Some(a) = column.as_any().downcast_ref::<Int64Array>() {
                a.value(row).to_string()
            } else if let Some(a) = column.as_any().downcast_ref::<Int32Array>() {
                a.value(row).to_string()
            } else if let Some(a) = column.as_any().downcast_ref::<StringArray>() {
                a.value(row).to_string()
            } else {
                panic!("unexpected IPC type {:?}", column.data_type())
            }
        })
        .collect()
}
