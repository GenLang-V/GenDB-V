//! The general line's storage assets over a fixture engine library (`storage::engine_library::tests::Fixture`: fixture
//! builds and tiny assets, no Verus run, no data): what a release keeps and removes, a lookup after a release, the
//! floor, and the promotion of a session's first-scale build of an admitted storage.

use super::*;
use crate::query::assets::{STORAGE_MARGIN_BYTES, TrialAssets};
use crate::storage::engine_library::tests::{Fixture, capture, capture_at, payload, remove_scratch};
use gendb_artifacts::verus::{
    BuiltParts, EngineVersion, VERUS_STORAGE_ASSET_RELEASE_KIND, VerusEngineLineageV1, VerusEngineSelectionV1, VerusStorageAssetKeyV1, VerusStorageAssetTableV1,
    VerusStoragePackageV1, released_storage_asset, select_engine_version, storage_asset_id, storage_asset_record,
};
use gendb_storage::versions::CurrentCapture;
use gendb_verification::admission::storage::{AssetLookup, TrialAsset, lookup_storage_asset};
use std::path::PathBuf;

/// A line of three versions over a fixture library, every storage with an asset at the first scale and at `sf10`:
/// v000 reads the plain storage `flat_lineitem` (built from source columns); v001 also the derived `narrow`, an
/// extension whose assets link flat_lineitem's two part files before their own one; v002, the head, the derived
/// `narrow2` (three own part files) instead.
pub(crate) struct Line {
    pub(crate) library: Fixture,
    pub(crate) flat: ContentId,
    pub(crate) old: ContentId,
    pub(crate) new: ContentId,
    pub(crate) versions: Vec<EngineVersion>,
}

pub(crate) fn captures() -> [CurrentCapture; 2] {
    [capture(), capture_at("sf10")]
}

pub(crate) fn line(root: &Path) -> Line {
    let mut library = Fixture::new(root, "engine");
    let flat = library.storage("flat_lineitem", &[(0, &[0, 1])], payload("lineitem", &["l_a", "l_b"]), None, 2);
    library.publish_asset(flat, &capture_at("sf10"), None, 2);
    let old = library.derived("narrow", &[(0, &[0, 1])], &[("flat_lineitem", flat)], Some(0), 1, &captures());
    let new = library.derived("narrow2", &[(0, &[0, 1])], &[("flat_lineitem", flat)], None, 3, &captures());
    let lineage = |branch: &str, kind: &str, parents: Vec<ContentId>| Some(VerusEngineLineageV1 { branch: branch.into(), kind: kind.into(), parents });
    let v0 = library.engine_with_lineage(&[("flat_lineitem", flat)], lineage("main", "framework_generated", vec![]));
    let v1 = library.engine_with_lineage(&[("narrow", old), ("flat_lineitem", flat)], lineage("b1", "branch", vec![v0.package_id]));
    let v2 = library.engine_with_lineage(&[("narrow2", new), ("flat_lineitem", flat)], lineage("b1", "branch", vec![v1.package_id]));
    for version in [&v0, &v1, &v2] {
        let selection = VerusEngineSelectionV1 { package: version.package_id, admission: version.admission_id, reason: "race".into(), evidence: vec![] };
        select_engine_version(&library.store, &selection).unwrap();
    }
    Line { library, flat, old, new, versions: vec![v0, v1, v2] }
}

/// The key of `package`'s asset for `capture`.
fn key(store: &ObjectStore, package: ContentId, capture: &CurrentCapture) -> VerusStorageAssetKeyV1 {
    let record: VerusStoragePackageV1 = store.read(package).unwrap().decode().unwrap();
    capture.asset_key(package, &record).unwrap()
}

/// v002 as the one head.
fn head_v002(line: &Line) -> Vec<KeptHead> {
    vec![KeptHead { version: "v002".into(), uses: line.versions[2].package.storage_uses.clone() }]
}

fn inode(path: &Path) -> (u64, u64, u64) {
    let meta = std::fs::metadata(path).unwrap();
    (meta.dev(), meta.ino(), meta.nlink())
}

fn released_names(record: &Value) -> BTreeSet<String> {
    record["released"].as_array().unwrap().iter().map(|r| r["storage"].as_str().unwrap().to_string()).collect()
}

/// A session directory with its controller lock file.
fn session(root: &Path) -> PathBuf {
    let session = root.join("session");
    std::fs::create_dir_all(&session).unwrap();
    std::fs::write(session.join("controller.lock"), b"").unwrap();
    session
}

/// A sealed trial of `package` for `key` in `trials` (one part file of `bytes` bytes), its record computed as a build
/// computes it, with the library's fixture evidence.
fn trial_for(trials: &mut TrialAssets, package: ContentId, name: &str, key: VerusStorageAssetKeyV1, bytes: usize, evidence: ContentId) -> TrialAsset {
    let directory = trials.root().join(key.identity().unwrap().to_hex());
    std::fs::create_dir_all(&directory).unwrap();
    std::fs::write(directory.join("part-0000.bin"), vec![7u8; bytes]).unwrap();
    std::fs::write(directory.join("parts.json"), b"{}").unwrap();
    let built = BuiltParts { format_version: 2, byte_order: "little".into(), parts: vec![("u8".into(), bytes as u64)], storage_bytes: bytes as u64 };
    let asset = storage_asset_record(key, built, 1, evidence).unwrap();
    let trial = TrialAsset { id: storage_asset_id(&asset).unwrap(), asset, directory };
    trials.record_built(package, name, &trial).unwrap();
    trial
}

/// Done-check 1: a release after v002's admission keeps the head's derived assets (narrow2) at both scales and the plain
/// storage's, and releases the superseded narrow at both: its directories are removed, its keys have no asset (the
/// stream ends with a release record naming the asset, its bytes and why), and the two flat part files each of its
/// assets linked stay on disk with their inode (one name fewer). The pass's record counts the bytes; a second pass
/// releases nothing. The head's derived bytes (the facts' number) count narrow2's files once, at both scales.
#[test]
fn a_release_keeps_the_heads_assets_and_releases_a_superseded_derived_one() {
    let root = crate::controller::test_support::scratch_root("asset-release-keep");
    let line = line(&root);
    let store = &line.library.store;
    let old_dirs: Vec<PathBuf> = captures().iter().map(|c| line.library.asset_dir_at(line.old, c)).collect();
    let flat_part = line.library.asset_dir(line.flat).join("part-0000.bin");
    let (dev, ino, links) = inode(&flat_part);
    let record = release_superseded_assets(store, &head_v002(&line), "admission of v002").unwrap();
    assert_eq!((record["released_assets"].as_u64(), released_names(&record)), (Some(2), BTreeSet::from(["narrow".to_string()])), "{record:#}");
    assert_eq!(record["file_bytes"].as_u64(), Some(2 * (3 * 64 + 2)), "each directory: 2 linked parts, 1 own part, parts.json");
    assert_eq!(record["freed_bytes"].as_u64(), Some(2 * (64 + 2)), "only the files whose last link was removed");
    for (capture, dir) in captures().iter().zip(&old_dirs) {
        assert!(!dir.exists(), "{}", dir.display());
        let released = key(store, line.old, capture);
        assert!(resolve_storage_asset(store, &released).unwrap().is_none(), "the key has no asset");
        let (_, release) = released_storage_asset(store, &released).unwrap().unwrap();
        assert!(release.reason.starts_with("superseded (admission of v002): derived storage narrow, read by v001, is read by no head (v002)"), "{}", release.reason);
        assert_eq!((release.storage_bytes, release.directory.starts_with("assets/")), (3 * 64, true));
        for kept in [line.new, line.flat] {
            assert!(line.library.asset_dir_at(kept, capture).join("parts.json").is_file(), "the head's and the plain storage's assets stay");
        }
    }
    assert_eq!(store.list_kind(VERUS_STORAGE_ASSET_RELEASE_KIND).unwrap().len(), 2, "one release record per released asset");
    assert_eq!(links, 2, "flat_lineitem's first-scale part and narrow's link to it");
    assert_eq!(inode(&flat_part), (dev, ino, 1), "the flat part stays, its inode untouched, one name fewer");
    let again = release_superseded_assets(store, &head_v002(&line), "controller start").unwrap();
    assert_eq!(again["released_assets"].as_u64(), Some(0), "{again:#}");
    let head = head_assets(store).unwrap();
    assert_eq!((head.head.as_deref(), head.derived_storages.clone(), head.assets, head.bytes), (Some("v002"), vec!["narrow2".to_string()], 2, 2 * (3 * 64 + 2)));
    remove_scratch(&root);
}

/// Done-check 3: flat storages (and every storage built from source columns) are never released, even when no head
/// reads anything; and the head's bytes leave out the flat part files an extension links.
#[test]
fn only_derived_assets_are_released_never_flat_ones() {
    let root = crate::controller::test_support::scratch_root("asset-release-flat");
    let line = line(&root);
    let store = &line.library.store;
    let flat_dirs: Vec<PathBuf> = captures().iter().map(|c| line.library.asset_dir_at(line.flat, c)).collect();
    // v001 as the head: narrow's own files count, the two flat parts it links do not.
    let v001 = [KeptHead { version: "v001".into(), uses: line.versions[1].package.storage_uses.clone() }];
    let selection = VerusEngineSelectionV1 { package: line.versions[1].package_id, admission: line.versions[1].admission_id, reason: "fixture".into(), evidence: vec![] };
    select_engine_version(store, &selection).unwrap();
    assert_eq!(head_assets(store).unwrap().bytes, 2 * (64 + 2), "narrow's own part and manifest at both scales");
    let record = release_superseded_assets(store, &v001, "fixture").unwrap();
    assert_eq!(released_names(&record), BTreeSet::from(["narrow2".to_string()]));
    let record = release_superseded_assets(store, &[], "no head").unwrap();
    assert_eq!(released_names(&record), BTreeSet::from(["narrow".to_string()]), "{record:#}");
    for (capture, dir) in captures().iter().zip(&flat_dirs) {
        assert!(dir.join("parts.json").is_file() && resolve_storage_asset(store, &key(store, line.flat, capture)).unwrap().is_some(), "flat_lineitem stays");
    }
    remove_scratch(&root);
}

/// Done-check 2: a lookup of a released asset finds none and hands out the key's build slot (the caller builds it again
/// by the package's stored builder; here a fixture build stands in for that run), and the rebuilt asset is published
/// after the release record and found again. A published asset whose directory was removed outside GenDB is refused by
/// name before any worker reads it, and the next release pass releases its record, so its next lookup builds it.
#[test]
fn a_released_asset_is_built_again_and_a_missing_directory_is_refused_by_name() {
    let root = crate::controller::test_support::scratch_root("asset-release-rebuild");
    let mut line = line(&root);
    release_superseded_assets(&line.library.store, &head_v002(&line), "admission of v002").unwrap();
    let released = key(&line.library.store, line.old, &capture());
    match lookup_storage_asset(&line.library.store, line.old, &capture(), None).unwrap() {
        AssetLookup::Absent(slot) => assert_eq!(slot.key(), &released),
        AssetLookup::Published(asset) => panic!("a released asset was found: {}", asset.id),
    }
    let flat_dir = line.library.asset_dir(line.flat);
    let rebuilt = line.library.publish_asset(line.old, &capture(), Some(&flat_dir), 1);
    let store = &line.library.store;
    assert_eq!(resolve_storage_asset(store, &released).unwrap().map(|(id, _)| id), Some(rebuilt));
    assert!(released_storage_asset(store, &released).unwrap().is_none(), "the stream ends with the rebuilt asset");
    match lookup_storage_asset(store, line.old, &capture(), None).unwrap() {
        AssetLookup::Published(asset) => assert!(asset.id == rebuilt && asset.directory.join("parts.json").is_file()),
        AssetLookup::Absent(_) => panic!("the rebuilt asset is published"),
    }
    // The head's asset at the first scale loses its directory outside GenDB.
    let gone = line.library.asset_dir(line.new);
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(&gone, std::fs::Permissions::from_mode(0o755)).unwrap();
    std::fs::remove_dir_all(&gone).unwrap();
    let refused = lookup_storage_asset(store, line.new, &capture(), None).err().expect("refused");
    assert!(refused.message.starts_with("asset_directory_missing: the published asset") && refused.message.contains("narrow2"), "{refused}");
    let record = release_superseded_assets(store, &head_v002(&line), "controller start").unwrap();
    let reasons: Vec<&str> = record["released"].as_array().unwrap().iter().map(|r| r["reason"].as_str().unwrap()).collect();
    assert_eq!(reasons.len(), 2, "the dangling head asset and the rebuilt superseded one: {record:#}");
    assert!(reasons.iter().any(|r| r.starts_with("directory missing (controller start): derived storage narrow2")), "{reasons:?}");
    assert!(matches!(lookup_storage_asset(store, line.new, &capture(), None).unwrap(), AssetLookup::Absent(_)), "its next use builds it");
    assert!(line.library.asset_dir_at(line.new, &capture_at("sf10")).join("parts.json").is_file(), "the head's asset at sf10 stays");
    remove_scratch(&root);
}

/// Done-check 4: under the floor a build is refused after the session's disposable trials are reclaimed: the older,
/// superseded build of a storage is removed, the newest kept, and the refusal (`insufficient_storage`) states the free
/// space, the floor, the reclaim and what the library keeps (the head's derived bytes) with the rule. The general
/// line's floor replaces the 4 GiB margin; a floor below the margin keeps the margin.
#[test]
fn the_floor_refuses_a_build_that_would_cross_it_after_reclaiming_trials() {
    let root = crate::controller::test_support::scratch_root("asset-release-floor");
    let mut line = line(&root);
    // Two builds of the unadmitted storage `scratch` for keys the library does not hold: the older is disposable.
    let package = line.library.publish_package("scratch", &[(1, &[0])], None);
    let store = &line.library.store;
    let mut trials = TrialAssets::open(&session(&root)).unwrap();
    let key_of = |order: &str| VerusStorageAssetKeyV1 {
        storage_package: package,
        tables: vec![VerusStorageAssetTableV1 { table: "orders".into(), source_version: "orders-v1".into(), row_order: order.into(), rows: 2 }],
    };
    let older = trial_for(&mut trials, package, "scratch", key_of("r-old"), 64, line.library.evidence);
    let newer = trial_for(&mut trials, package, "scratch", key_of("r-new"), 64, line.library.evidence);
    let upkeep = AssetUpkeep { floor_bytes: u64::MAX / 4 };
    let need = SpaceNeed::new(Some(7), None, None).with_floor(Some(upkeep.floor_bytes));
    let reclaim = trials.reclaim_for(store, &need, &BTreeSet::new()).unwrap();
    let removed: Vec<&str> = reclaim["reclaimed"].as_array().unwrap().iter().map(|r| r["asset"].as_str().unwrap()).collect();
    assert_eq!(removed, [older.id.to_hex()], "{reclaim:#}");
    assert!(!older.directory.exists() && newer.directory.exists());
    let refused = check_free_space(Some(&upkeep), &root.join("engine"), &trials.root(), &need, &reclaim).unwrap_err();
    let message = refused.message;
    assert!(message.starts_with("insufficient_storage: ") && message.contains(&format!("the shared host's floor {}", u64::MAX / 4)), "{message}");
    assert!(message.contains(&older.id.to_hex()), "the reclaim is stated: {message}");
    assert!(message.contains(&format!("GenDB keeps {} bytes ({} GiB) free on this shared host besides each build's estimate", u64::MAX / 4, (u64::MAX / 4) >> 30)), "{message}");
    assert!(message.contains("the library holds 388 bytes of the head v002's derived storage assets (2 assets, every scale)") && message.ends_with(KEEP_RULE), "{message}");
    // The general line's floor and the margin elsewhere.
    assert_eq!(SpaceNeed::new(None, None, Some(7)).with_floor(Some(AssetUpkeep::GENERAL_LINE.floor_bytes)).required_bytes(), (20u64 << 30) + 7);
    assert_eq!(SpaceNeed::new(None, None, Some(7)).required_bytes(), STORAGE_MARGIN_BYTES + 7);
    assert_eq!(SpaceNeed::new(None, None, Some(7)).with_floor(Some(1)).required_bytes(), STORAGE_MARGIN_BYTES + 7);
    let room = SpaceNeed::new(Some(1), None, None).with_floor(Some(1));
    check_free_space(Some(&AssetUpkeep { floor_bytes: 1 }), &root.join("engine"), &trials.root(), &room, &json!({})).unwrap();
    remove_scratch(&root);
}

/// Done-check 5 (the first-scale leak): a session at a later scale built a new storage's trial at the first scale for
/// its variants; once the storage is admitted (its asset at sf10 published), that trial is promoted into the library as
/// its first-scale asset, with the same id, instead of staying in the session forever; a trial for a key the library
/// already holds is removed; nothing is left to keep at the session's close.
#[test]
fn a_first_scale_trial_of_an_admitted_storage_is_promoted_into_the_library() {
    let root = crate::controller::test_support::scratch_root("asset-release-first-scale");
    let mut line = line(&root);
    let package = line.library.derived("wide", &[(1, &[0])], &[("flat_lineitem", line.flat)], None, 1, &[capture_at("sf10")]);
    let store = line.library.store.clone();
    let mut trials = TrialAssets::open(&session(&root)).unwrap();
    let first = trial_for(&mut trials, package, "wide", key(&store, package, &capture()), 64, line.library.evidence);
    let duplicate = trial_for(&mut trials, package, "wide", key(&store, package, &capture_at("sf10")), 32, line.library.evidence);
    let result = trials.promote_admitted(&store, &BTreeSet::from([package])).unwrap();
    let ids = |field: &str| -> Vec<String> { result[field].as_array().unwrap().iter().map(|r| r["asset"].as_str().unwrap().to_string()).collect() };
    assert_eq!((ids("promoted"), ids("removed")), (vec![first.id.to_hex()], vec![duplicate.id.to_hex()]), "{result:#}");
    let (id, asset) = resolve_storage_asset(&store, &first.asset.key).unwrap().unwrap();
    assert_eq!(id, first.id, "the same asset id");
    assert!(storage_asset_directory(&store, &asset).unwrap().join("parts.json").is_file() && !first.directory.exists() && !duplicate.directory.exists());
    let closed = trials.release_at_close(&store, &BTreeSet::new()).unwrap();
    assert!(closed["kept"].as_array().unwrap().is_empty() && closed["reclaimed"].as_array().unwrap().is_empty(), "{closed:#}");
    remove_scratch(&root);
}
