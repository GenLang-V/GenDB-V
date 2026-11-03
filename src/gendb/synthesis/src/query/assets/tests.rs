//! The session trial-asset policy over synthetic trials (tiny directories, a stand-in package record; no build).

use super::*;
use gendb_artifacts::verus::{VERUS_STORAGE_PACKAGE_KIND, VerusCheckConfigurationV1, VerusStorageAssetTableV1, VerusStorageAssetV1};

/// A fresh scratch directory under `TMPDIR` (a scratch directory, never `/tmp`).
fn scratch_root(name: &str) -> PathBuf {
    let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
    PathBuf::from(std::env::var_os("TMPDIR").expect("TMPDIR must name a scratch directory")).join(format!("trial-assets-{name}-{}-{nanos}", std::process::id()))
}

/// A session directory with its controller lock file and a library holding one (unadmitted) package record.
fn session(name: &str) -> (PathBuf, ObjectStore, ContentId) {
    let root = scratch_root(name);
    let session = root.join("session");
    std::fs::create_dir_all(&session).unwrap();
    std::fs::write(session.join("controller.lock"), b"").unwrap();
    let store = ObjectStore::open(root.join("library")).unwrap();
    let package = put_package(&store, "e");
    (session, store, package)
}

/// A stand-in record of a package of storage `s` in `store`; `entry` tells packages apart.
fn put_package(store: &ObjectStore, entry: &str) -> ContentId {
    let zero = ContentId::from_bytes([0; 32]);
    let package = VerusStoragePackageV1 {
        name: "s".into(), build: zero, entry_identity: entry.into(), assumed_constraints: None, tables: vec![], declaration: json!(null), schema_ddl: zero,
        frontend: json!(null), closure: vec![],
        configuration: VerusCheckConfigurationV1 { provider_identity: "p".into(), options: vec![], environment: BTreeMap::new() },
        readers: vec![], theorems: vec![], workers: (1, 1), tcb: zero, derived_from: None,
    };
    store.put(1, VERUS_STORAGE_PACKAGE_KIND, &package).unwrap()
}

/// A present trial of `package` for row order `order` with `bytes` stored bytes, recorded in `trials`.
fn trial(trials: &mut TrialAssets, package: ContentId, order: &str, bytes: u64) -> TrialAsset {
    let key = VerusStorageAssetKeyV1 {
        storage_package: package,
        tables: vec![VerusStorageAssetTableV1 { table: "t".into(), source_version: "v".into(), row_order: order.into(), rows: 3 }],
    };
    let directory = trials.root().join(key.identity().unwrap().to_hex());
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(directory.join("part-0000.bin"), vec![0u8; bytes as usize]).unwrap();
    std::fs::write(directory.join("parts.json"), b"{}").unwrap();
    let asset = VerusStorageAssetV1 {
        directory: format!("assets/{}", key.identity().unwrap().to_hex()), key, parts_format: 2, byte_order: "little".into(),
        parts: vec![("i32".into(), 3)], storage_bytes: bytes, build_wall_ns: 1, evidence: package,
    };
    let trial = TrialAsset { id: records::storage_asset_id(&asset).unwrap(), asset, directory };
    trials.record_built(package, "s", &trial).unwrap();
    trial
}

/// More than any filesystem has free: reclaim removes every disposable trial.
fn pressure() -> SpaceNeed {
    SpaceNeed::new(Some(u64::MAX / 4), None, None)
}

fn ids(record: &Value, field: &str) -> Vec<String> {
    record[field].as_array().unwrap().iter().map(|r| r["asset"].as_str().unwrap().to_string()).collect()
}

/// The estimate's basis follows the documented order; the guard names its facts before anything is built.
#[test]
fn space_need_uses_the_best_measured_estimate() {
    let canonical = SpaceNeed::new(None, None, Some(7));
    assert_eq!((canonical.basis, canonical.required_bytes()), ("canonical_columns", STORAGE_MARGIN_BYTES + 7));
    let measured = SpaceNeed::new(None, Some(3), Some(7));
    assert_eq!((measured.basis, measured.required_bytes()), ("same_storage_measured", STORAGE_MARGIN_BYTES + 3));
    let prior = SpaceNeed::new(Some(10), Some(3), Some(1));
    assert_eq!((prior.basis, prior.required_bytes()), ("prior_same_key", STORAGE_MARGIN_BYTES + 10));
    assert_eq!(SpaceNeed::new(None, None, None).basis, "unknown");
    let root = scratch_root("space-need");
    std::fs::create_dir_all(&root).unwrap();
    assert!(check_free_storage(&root, &canonical, &json!(null)).is_ok());
    let refused = check_free_storage(&root, &pressure(), &json!({"reclaimed":[]})).unwrap_err();
    assert_eq!(refused.class, gendb_verification::admission::FailureClass::ToolFailure);
    assert!(refused.message.starts_with("insufficient_storage:") && refused.message.contains("prior_same_key"));
}

/// Pressure removes disposable trials least recently used first and holds protected ones, ones a durable eligible
/// evaluation names, the asking job's and published ones; the ledger survives reopening; a removed trial's bytes
/// become its key's estimate and its absence is noticed.
#[test]
fn pressure_reclaims_only_disposable_trials() {
    let (session, store, package) = session("trial-pressure");
    let mut trials = TrialAssets::open(&session).unwrap();
    let old = trial(&mut trials, package, "old", 3);
    let protected = trial(&mut trials, package, "protected", 3);
    let durable = trial(&mut trials, package, "durable", 3);
    let kept = trial(&mut trials, package, "kept", 3);
    let recent = trial(&mut trials, package, "recent", 5);
    assert_eq!(trials.present(&old.asset.key).unwrap(), Some(old.clone()), "use makes `old` the most recent");
    trials.protect(&BTreeSet::from([protected.id]), "eligible evaluation").unwrap();
    let evaluation = session.join("iterations/0001/frozen/evaluation-0");
    std::fs::create_dir_all(&evaluation).unwrap();
    std::fs::write(evaluation.join("verus-evaluation.json"), json!({"eligible":true,"storage":[{"asset":durable.id}]}).to_string()).unwrap();

    let mut trials = TrialAssets::open(&session).unwrap();
    let record = trials.reclaim_for(&store, &pressure(), &BTreeSet::from([kept.id])).unwrap();
    assert_eq!(ids(&record, "reclaimed"), vec![old.id.to_hex()], "only superseded builds: {record}");
    assert_eq!(ids(&record, "held").len(), 4, "the newest build of the storage is the current candidate's: {record}");
    assert!(!old.directory.exists() && recent.directory.join("parts.json").is_file());
    assert!([&protected, &durable, &kept].iter().all(|t| t.directory.join("parts.json").is_file()));
    assert_eq!(trials.prior_bytes(&old.asset.key), Some(3));
    assert_eq!(trials.newest_bytes_of(&store, "s"), Some(5));
    assert_eq!(trials.present(&old.asset.key).unwrap(), None);

    remove_build_directory(&kept.directory).unwrap();
    assert_eq!(trials.present(&kept.asset.key).unwrap(), None, "an absent directory is noticed");
    let stray_key = VerusStorageAssetKeyV1 { storage_package: package, tables: vec![] };
    let stray = trials.root().join(stray_key.identity().unwrap().to_hex());
    std::fs::create_dir_all(&stray).unwrap();
    assert_eq!(trials.present(&stray_key).unwrap(), None);
    assert!(!stray.exists(), "a directory the ledger never named was never used, and is removed");
}

/// An unreadable session record reclaims nothing (fail closed).
#[test]
fn unreadable_evidence_reclaims_nothing() {
    let (session, store, package) = session("trial-unreadable");
    let mut trials = TrialAssets::open(&session).unwrap();
    let only = trial(&mut trials, package, "only", 3);
    std::fs::create_dir_all(session.join("iterations/0001")).unwrap();
    std::fs::write(session.join("iterations/0001/evaluation.json"), b"{ torn").unwrap();
    let record = trials.reclaim_for(&store, &pressure(), &BTreeSet::new()).unwrap();
    assert!(record["refused"].as_str().unwrap().contains("unreadable session record") && ids(&record, "reclaimed").is_empty());
    assert!(only.directory.is_dir());
}

/// Close keeps the named trials and those the library holds; everything else of the session goes.
#[test]
fn close_releases_all_but_kept_and_registered() {
    let (session, store, package) = session("trial-close");
    let mut trials = TrialAssets::open(&session).unwrap();
    let best = trial(&mut trials, package, "best", 3);
    let other = trial(&mut trials, package, "other", 3);
    let registered = trial(&mut trials, package, "registered", 3);
    trials.protect(&BTreeSet::from([other.id]), "eligible evaluation").unwrap();
    trials.record_promoted(registered.id).unwrap();
    let record = trials.release_at_close(&store, &BTreeSet::from([best.id])).unwrap();
    assert_eq!(ids(&record, "reclaimed"), vec![other.id.to_hex()], "{record}");
    assert_eq!(ids(&record, "kept"), vec![best.id.to_hex()]);
    assert!(best.directory.is_dir() && !other.directory.exists() && registered.directory.is_dir(), "a promoted entry is not the session's to remove");
}

/// The ended-session command: refused without a session or while its controller runs; a dry run lists; `--apply`
/// removes disposable trials and interrupted builds, never an eligible one.
#[test]
fn ended_session_command_is_explicit_and_locked() {
    let (session, store, package) = session("trial-command");
    let library = store.root().to_path_buf();
    let mut trials = TrialAssets::open(&session).unwrap();
    let disposable = trial(&mut trials, package, "disposable", 3);
    let eligible = trial(&mut trials, package, "eligible", 3);
    trials.protect(&BTreeSet::from([eligible.id]), "eligible evaluation").unwrap();
    let building = trials.root().join(format!("{}.building", "a".repeat(64)));
    std::fs::create_dir_all(&building).unwrap();
    drop(trials);

    assert_eq!(reclaim_ended_session(&session.join("absent"), &library, &BTreeSet::new(), true).unwrap_err().class, gendb_verification::admission::FailureClass::MissingInput);
    let running = FileLock::acquire(std::fs::File::open(session.join("controller.lock")).unwrap(), libc::LOCK_EX | libc::LOCK_NB).unwrap();
    assert!(reclaim_ended_session(&session, &library, &BTreeSet::new(), true).unwrap_err().message.contains("controller is running"));
    drop(running);

    let listed = reclaim_ended_session(&session, &library, &BTreeSet::new(), false).unwrap();
    assert_eq!(ids(&listed, "disposable"), vec![disposable.id.to_hex()]);
    assert!(disposable.directory.is_dir() && building.is_dir(), "a dry run removes nothing");
    let applied = reclaim_ended_session(&session, &library, &BTreeSet::new(), true).unwrap();
    assert_eq!(applied["removed"].as_array().unwrap().len(), 2, "{applied}");
    assert!(!disposable.directory.exists() && !building.exists() && eligible.directory.is_dir());
}


/// One session's trials of one storage name in two libraries (a run of several workloads, where a storage family's
/// instance has the family's name in every library): every lookup by name sees only the library it is asked for, so
/// library B's build is never given library A's package (B's store cannot read it), its estimate is B's
/// own build, and pressure from library A keeps A's newest build and leaves B's trial alone.
#[test]
fn name_lookups_see_only_one_librarys_trials() {
    let (session, store_a, package_a) = session("trial-libraries");
    let store_b = ObjectStore::open(session.parent().unwrap().join("library-b")).unwrap();
    let package_b = put_package(&store_b, "e-b");
    let mut trials = TrialAssets::open(&session).unwrap();
    let a = trial(&mut trials, package_a, "a", 3);
    let b = trial(&mut trials, package_b, "b", 5);
    assert_eq!(trials.present_of_name(&store_a, "s"), vec![(package_a, a.clone())]);
    assert_eq!(trials.present_of_name(&store_b, "s"), vec![(package_b, b.clone())]);
    assert_eq!((trials.newest_bytes_of(&store_a, "s"), trials.newest_bytes_of(&store_b, "s")), (Some(3), Some(5)));
    let record = trials.reclaim_for(&store_a, &pressure(), &BTreeSet::new()).unwrap();
    assert!(ids(&record, "reclaimed").is_empty(), "A's trial is A's newest build of s; B's is not A's: {record}");
    let held: BTreeMap<String, String> = record["held"].as_array().unwrap().iter().map(|h| (h["asset"].as_str().unwrap().into(), h["held"].as_str().unwrap().into())).collect();
    assert!(held[&a.id.to_hex()].starts_with("the newest build of storage s"), "{record}");
    assert!(held[&b.id.to_hex()].starts_with("a trial of another library"), "{record}");
    assert!(a.directory.join("parts.json").is_file() && b.directory.join("parts.json").is_file());
}
