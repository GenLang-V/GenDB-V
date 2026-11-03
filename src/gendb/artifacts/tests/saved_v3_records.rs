//! Compatibility with saved v3 libraries written by the earlier GenDB version. Ignored by default because it reads
//! saved libraries outside the crate; run it with `--ignored` and
//! `GENDB_SAVED_V3_CASES=<library>=<qualification.json>[,<library>=<qualification.json>...]`, where the qualification
//! is that version's controller record of the admission in that library.
//!
//! The saved libraries are opened read-only. The check reads only the records of each admitted package (never the
//! stored library or data parts) and copies only append records and their subjects for the index comparison.

mod common;

use gendb_artifacts::verus::*;
use gendb_artifacts::{
    APPEND_RECORD_KIND, AppendRecord, ContentId, ObjectStore, RecordIndex, canonical_envelope, lookup_record_head,
    rebuild_indexes,
};
use serde::Serialize;
use std::path::Path;

/// Decoding the stored record and encoding it again gives the stored bytes, hence the same content identity.
/// Returns the stored byte count.
fn assert_byte_identical<T: Serialize>(store: &ObjectStore, id: ContentId, kind: &str, record: &T) -> usize {
    let stored = std::fs::read(store.object_path(id)).unwrap();
    let encoded = canonical_envelope(1, kind, record).unwrap();
    assert_eq!(encoded.as_bytes(), stored.as_slice(), "{kind} {id} re-encodes differently");
    assert_eq!(gendb_artifacts::content_id(1, kind, record).unwrap(), id);
    stored.len()
}

fn reported_id(qualification: &serde_json::Value, field: &str) -> ContentId {
    let result = qualification.get("result").unwrap_or(qualification);
    serde_json::from_value(result[field].clone()).unwrap_or_else(|_| panic!("qualification lacks {field}"))
}

fn check_library(root: &Path, qualification: &Path) -> serde_json::Value {
    let store = ObjectStore::open_existing(root).unwrap();
    let qualification: serde_json::Value = serde_json::from_slice(&std::fs::read(qualification).unwrap()).unwrap();
    let statement = reported_id(&qualification, "statement");
    let resolved = resolve_package_v3(&store, statement).unwrap().expect("the saved statement resolves to its admitted package");
    let package = &resolved.package;
    assert_eq!(resolved.key.identity().unwrap(), statement, "statement key identity");
    assert_eq!(resolved.key.stream().unwrap(), statement_stream(statement));
    for (field, id) in [
        ("admission", resolved.admission_id),
        ("package", resolved.admission.package),
        ("claim", package.claim),
        ("build", package.build),
        ("tcb", package.tcb),
        ("representation", package.representation),
    ] {
        assert_eq!(reported_id(&qualification, field), id, "{field} differs from the saved qualification");
    }
    assert_eq!(resolved.admission.assets, vec![reported_id(&qualification, "asset")]);
    assert_eq!(resolved.admission.qualification_evidence, vec![reported_id(&qualification, "qualification_evidence")]);

    let mut compared = vec![
        assert_byte_identical(&store, resolved.admission_id, VERUS_PACKAGE_ADMISSION_KIND, &resolved.admission),
        assert_byte_identical(&store, resolved.admission.package, VERUS_QUERY_PACKAGE_V2_KIND, package),
        assert_byte_identical(&store, package.claim, VERUS_SQL_CLAIM_KIND, &resolved.claim),
        assert_byte_identical(&store, statement, VERUS_STATEMENT_KEY_KIND, &resolved.key),
        assert_byte_identical(&store, package.build, VERUS_BUILD_KIND, &resolved.build),
    ];
    let tcb: VerusTcbV1 = store.read(package.tcb).unwrap().decode().unwrap();
    compared.push(assert_byte_identical(&store, package.tcb, VERUS_TCB_KIND, &tcb));
    for id in &package.implementations {
        let implementation: VerusImplementationV1 = store.read(*id).unwrap().decode().unwrap();
        compared.push(assert_byte_identical(&store, *id, VERUS_IMPLEMENTATION_KIND, &implementation));
    }
    let representation: VerusRepresentationV2 = store.read(package.representation).unwrap().decode().unwrap();
    compared.push(assert_byte_identical(&store, package.representation, VERUS_REPRESENTATION_V2_KIND, &representation));

    let mut asset_streams = vec![];
    for asset in &resolved.admission.assets {
        let manifest: VerusAssetManifestV2 = store.read(*asset).unwrap().decode().unwrap();
        compared.push(assert_byte_identical(&store, *asset, VERUS_ASSET_V2_KIND, &manifest));
        assert_eq!(resolve_asset_v2(&store, &manifest.key).unwrap().map(|(id, _)| id), Some(*asset), "asset key resolves");
        let stream = manifest.key.stream().unwrap();
        assert!(RecordIndex::path(&store, &stream).is_file(), "saved index names asset stream {stream}");
        let head = lookup_record_head(&store, &stream).unwrap().unwrap();
        let append: AppendRecord = store.read(head).unwrap().decode().unwrap();
        compared.push(assert_byte_identical(&store, head, APPEND_RECORD_KIND, &append));
        let promotion: VerusAssetPromotionV1 = store.read(append.subject).unwrap().decode().unwrap();
        compared.push(assert_byte_identical(&store, append.subject, VERUS_ASSET_PROMOTION_KIND, &promotion));
        let rebuilt_key = VerusAssetKeyV2::current(package.representation, &representation, &|table: &str| {
            let source = manifest.key.sources.iter().find(|s| s.table == table).ok_or("table absent")?;
            Ok((source.source_version.clone(), source.rows))
        })
        .unwrap();
        assert_eq!(rebuilt_key, manifest.key, "asset key rebuilt from the representation and current versions");
        asset_streams.push(stream);
    }
    let statement_head = lookup_record_head(&store, &statement_stream(statement)).unwrap().unwrap();
    let statement_append: AppendRecord = store.read(statement_head).unwrap().decode().unwrap();
    compared.push(assert_byte_identical(&store, statement_head, APPEND_RECORD_KIND, &statement_append));

    let build = check_build_evidence(&store, package.build).unwrap();
    let library = library_path(&store, &build).unwrap();
    let meaning = statement_meaning(&build.framework_text(&store, "query.rs").unwrap());
    assert_eq!(meaning, resolved.key.meaning, "stored query.rs has the key's meaning");

    serde_json::json!({
        "library": root, "statement": statement, "admission": resolved.admission_id, "package": resolved.admission.package,
        "claim": package.claim, "build": package.build, "representation": package.representation,
        "assets": resolved.admission.assets, "asset_streams": asset_streams, "implementations": package.implementations,
        "records_compared": compared.len(), "record_bytes_compared": compared.iter().sum::<usize>(), "library_file": library, "library_bytes": build.library_bytes,
    })
}

/// Rebuild the record index of a scratch copy holding only the saved append records and their subjects; every index
/// file must equal the saved one byte for byte.
fn check_index_rebuild(root: &Path) -> serde_json::Value {
    let saved = ObjectStore::open_existing(root).unwrap();
    let copy = ObjectStore::open(common::scratch_dir("saved-index-copy")).unwrap();
    let appends = saved.list_kind(APPEND_RECORD_KIND).unwrap();
    for object in &appends {
        let record: AppendRecord = object.decode().unwrap();
        for id in [object.id, record.subject] {
            std::fs::copy(saved.object_path(id), copy.object_path(id)).unwrap();
        }
    }
    let rebuilt = rebuild_indexes(&copy).unwrap();
    let mut saved_files: Vec<_> = std::fs::read_dir(saved.index_root().join("records")).unwrap().map(|e| e.unwrap().file_name()).collect();
    saved_files.sort();
    let mut rebuilt_files: Vec<_> = rebuilt.iter().map(|p| p.file_name().unwrap().to_owned()).collect();
    rebuilt_files.sort();
    assert_eq!(rebuilt_files, saved_files);
    for name in &saved_files {
        let saved_bytes = std::fs::read(saved.index_root().join("records").join(name)).unwrap();
        assert_eq!(std::fs::read(copy.index_root().join("records").join(name)).unwrap(), saved_bytes, "{name:?}");
    }
    serde_json::json!({"library": root, "append_records": appends.len(), "index_files_equal": saved_files.len(), "copy": copy.root()})
}

#[test]
#[ignore = "reads saved libraries named by GENDB_SAVED_V3_CASES"]
fn saved_v3_packages_resolve_with_identical_content_ids() {
    let cases = std::env::var("GENDB_SAVED_V3_CASES").expect("GENDB_SAVED_V3_CASES=<library>=<qualification.json>,...");
    for case in cases.split(',') {
        let (library, qualification) = case.split_once('=').expect("<library>=<qualification.json>");
        println!("SAVED_V3_PACKAGE {}", check_library(Path::new(library), Path::new(qualification)));
        println!("SAVED_V3_INDEX {}", check_index_rebuild(Path::new(library)));
    }
}
