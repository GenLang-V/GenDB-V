//! Object store and append-only record invariants.

mod common;

use gendb_artifacts::{AppendOnlyError, ContentId, ObjectStore, StoreError, append_record, lookup_record_head, rebuild_indexes};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct Fixture {
    name: String,
    ports: Vec<String>,
    lower_bound: i128,
}

fn fixture() -> Fixture {
    Fixture { name: "scan-filter-sum".into(), ports: vec!["rows".into(), "predicate".into()], lower_bound: i128::MIN }
}

fn store(name: &str) -> ObjectStore {
    ObjectStore::open(common::scratch_dir(name)).unwrap()
}

#[test]
fn sealing_twice_is_idempotent_and_typed() {
    let store = store("seal-reseal");
    let first = store.put(1, "gendb.contract", &fixture()).unwrap();
    assert_eq!(store.put(1, "gendb.contract", &fixture()).unwrap(), first);
    let object = store.read(first).unwrap();
    assert_eq!((object.kind.as_str(), object.format_version), ("gendb.contract", 1));
    assert_eq!(object.decode::<Fixture>().unwrap(), fixture());
    let mut reversed = fixture();
    reversed.ports.reverse();
    assert_ne!(store.put(1, "gendb.contract", &reversed).unwrap(), first, "array order is content");
}

#[test]
fn blobs_are_named_by_their_bytes_and_checked_on_read() {
    let store = store("blob");
    let bytes = b"plain binary bytes\0without an envelope";
    let id = store.put_blob(bytes).unwrap();
    assert_eq!(store.put_blob(bytes).unwrap(), id);
    assert_eq!(store.read_blob(id, Some(bytes.len() as u64)).unwrap(), bytes);
    assert!(matches!(store.read_blob(id, Some(1)), Err(StoreError::BlobLengthMismatch { .. })));
}

#[test]
fn tampered_object_is_refused_before_decode() {
    let store = store("tamper");
    let id = store.put(1, "gendb.contract", &fixture()).unwrap();
    let path = store.object_path(id);
    let mut bytes = std::fs::read(&path).unwrap();
    let at = bytes.iter().position(|byte| *byte == b's').unwrap();
    bytes[at] = b'x';
    std::fs::write(&path, bytes).unwrap();
    assert!(matches!(store.read(id), Err(StoreError::DigestMismatch { expected, .. }) if expected == id));
}

#[test]
fn kind_discovery_selects_only_the_canonical_envelope_header() {
    let store = store("kind-discovery");
    let wanted = store.put(1, "gendb.record", &fixture()).unwrap();
    let decoy_payload = format!(r#",\"kind\":\"gendb.record\",\"payload\":{}"#, "x".repeat(4096));
    let decoy = store.put(1, "gendb.blob", &decoy_payload).unwrap();
    let found: Vec<ContentId> = store.list_kind("gendb.record").unwrap().iter().map(|o| o.id).collect();
    assert_eq!(found, [wanted]);
    assert_eq!(store.list_kind("gendb.blob").unwrap()[0].id, decoy);
}

#[test]
fn streams_append_and_their_index_rebuilds_from_objects_alone() {
    let store = store("index-rebuild");
    let subject_a = store.put(1, "gendb.evidence", &fixture()).unwrap();
    let subject_b = store.put(1, "gendb.evidence", &Fixture { name: "later".into(), ..fixture() }).unwrap();
    let record_a = append_record(&store, "promotion", subject_a).unwrap();
    let record_b = append_record(&store, "promotion", subject_b).unwrap();
    assert_ne!(record_a, record_b);
    assert_eq!(lookup_record_head(&store, "promotion").unwrap(), Some(record_b));
    assert!(matches!(append_record(&store, "bad/stream", subject_a), Err(AppendOnlyError::InvalidStream(_))));

    let index_path = store.index_root().join("records/promotion.json");
    let written_by_append = std::fs::read(&index_path).unwrap();
    std::fs::remove_dir_all(store.index_root()).unwrap();
    assert_eq!(rebuild_indexes(&store).unwrap(), vec![index_path.clone()]);
    assert_eq!(std::fs::read(&index_path).unwrap(), written_by_append);
    assert_eq!(lookup_record_head(&store, "promotion").unwrap(), Some(record_b));
}

#[test]
fn an_index_entry_alone_never_names_a_head() {
    let store = store("index-only");
    let records = store.index_root().join("records");
    std::fs::create_dir_all(&records).unwrap();
    let missing = ContentId::from_bytes([7; 32]);
    let fake = format!(r#"{{"format_version":1,"head":"{missing}","sequence":0,"stream":"promotion"}}"#);
    std::fs::write(records.join("promotion.json"), format!("{fake}\n")).unwrap();
    assert!(matches!(lookup_record_head(&store, "promotion"), Err(AppendOnlyError::IndexOnlyAuthorityRefused { .. })));
}

#[test]
fn an_existing_library_opens_without_creating_anything() {
    let root = common::scratch_dir("open-existing");
    assert!(ObjectStore::open_existing(&root).is_err());
    assert!(!root.join("objects").exists(), "open_existing created objects/");
    ObjectStore::open(&root).unwrap();
    ObjectStore::open_existing(&root).unwrap();
}
