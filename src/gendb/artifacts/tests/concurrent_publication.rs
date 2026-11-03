//! Publication atomicity across independent processes: no partial object after an abandoned write, one object for
//! duplicate content, and no forked stream heads under concurrent appends.

mod common;

use gendb_artifacts::{APPEND_RECORD_KIND, AppendRecord, ObjectStore, append_record, lookup_record_head, rebuild_indexes};
use std::fs;
use std::path::PathBuf;
use std::process::{Command, Stdio};

const ROOT_VARIABLE: &str = "GENDB_STORE_PROCESS_CONTROL_ROOT";
const ROLE_VARIABLE: &str = "GENDB_STORE_PROCESS_CONTROL_ROLE";
const WRITER_APPENDS: u64 = 10;

/// Child-process body; a no-op unless spawned by the test below.
#[test]
fn process_worker() {
    let Ok(root) = std::env::var(ROOT_VARIABLE) else {
        return;
    };
    let role = std::env::var(ROLE_VARIABLE).unwrap();
    let root = PathBuf::from(root);
    let store = ObjectStore::open(&root).unwrap();
    if role == "abandon_stage" {
        // A process that exits after a staging write but before the no-replace link.
        fs::create_dir_all(root.join(".staging")).unwrap();
        fs::write(root.join(".staging/abandoned"), b"partial unpublished bytes").unwrap();
        std::process::exit(73);
    }
    while !root.join("start").exists() {
        std::thread::yield_now();
    }
    if role == "reader" {
        for i in 0..50 {
            lookup_record_head(&store, "shared").unwrap();
            if i % 5 == 0 {
                rebuild_indexes(&store).unwrap();
            }
        }
        return;
    }
    for i in 0..WRITER_APPENDS {
        let blob = store.put_blob(&vec![41u8; 256 * 1024]).unwrap();
        assert_eq!(store.read_blob(blob, Some(256 * 1024)).unwrap().len(), 256 * 1024);
        let duplicate = store.put(1, "duplicate", &serde_json::json!({"shared": true})).unwrap();
        assert_eq!(store.read(duplicate).unwrap().kind, "duplicate");
        let subject = store.put(1, "subject", &serde_json::json!({"role": role, "index": i})).unwrap();
        append_record(&store, "shared", subject).unwrap();
        append_record(&store, &format!("writer.{role}"), subject).unwrap();
        lookup_record_head(&store, "shared").unwrap();
    }
}

#[test]
fn independent_processes_publish_and_resolve_without_partial_objects_or_forked_heads() {
    let root = common::scratch_dir("store-process-control");
    let store = ObjectStore::open(&root).unwrap();
    let spawn = |role: &str| {
        Command::new(std::env::current_exe().unwrap())
            .args(["--exact", "process_worker", "--nocapture"])
            .env(ROOT_VARIABLE, &root)
            .env(ROLE_VARIABLE, role)
            .stdout(Stdio::from(fs::File::create(root.join(format!("{role}.stdout"))).unwrap()))
            .stderr(Stdio::from(fs::File::create(root.join(format!("{role}.stderr"))).unwrap()))
            .spawn()
            .unwrap()
    };
    assert_eq!(spawn("abandon_stage").wait().unwrap().code(), Some(73));
    assert_eq!(fs::read_dir(store.objects_root()).unwrap().count(), 0, "an abandoned staging write became an object");

    let writers = ["a", "b", "c"];
    let mut children: Vec<_> = writers.iter().chain(["reader"].iter()).map(|role| spawn(role)).collect();
    fs::write(root.join("start"), b"start").unwrap();
    for child in &mut children {
        assert!(child.wait().unwrap().success(), "child evidence {}", root.display());
    }

    rebuild_indexes(&store).unwrap();
    let sequence_of = |stream: &str| -> u64 {
        let head = lookup_record_head(&store, stream).unwrap().unwrap();
        store.read(head).unwrap().decode::<AppendRecord>().unwrap().sequence
    };
    assert_eq!(sequence_of("shared"), writers.len() as u64 * WRITER_APPENDS - 1);
    for role in writers {
        assert_eq!(sequence_of(&format!("writer.{role}")), WRITER_APPENDS - 1);
    }
    assert_eq!(store.list_kind("duplicate").unwrap().len(), 1);
    assert_eq!(store.list_kind("subject").unwrap().len(), 30);
    assert_eq!(store.list_kind(APPEND_RECORD_KIND).unwrap().len(), 60);
    let entries_before = fs::read_dir(&root).unwrap().count();
    lookup_record_head(&ObjectStore::open(&root).unwrap(), "shared").unwrap();
    assert_eq!(fs::read_dir(&root).unwrap().count(), entries_before, "a read-only lookup added lock files");
}
