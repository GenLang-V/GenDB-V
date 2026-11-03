//! Seeding an engine library: admitted storage packages of a source library, with their
//! records and stored assets, become admitted storage packages of a new engine library, without any query package.
//!
//! What is carried, and how:
//! - **objects**: every object the seeded records reach (the storage admission with its evidence, the package, its
//!   build with sources, Verus output, compiled library and TCB, the asset records with their build evidence), found by
//!   following the 64-hex identities in the typed records' payloads to objects of the source. Each object file is
//!   hard-linked under its own name (its content identity): no byte is read, copied or hashed except the typed records
//!   walked, which are small. A record of a query package, its admission, key or claim, of an engine, or of an
//!   append-only stream is never carried (`seed_reaches_query_record`);
//! - **assets**: every published asset of a seeded package, its part files hard-linked into a new asset directory of
//!   the same library-relative name (`assets/<key id>`), placed and sealed as a fresh build is, then its record appended
//!   to its key's stream. Part payload is never read, copied or hashed, and nothing is built; the shared inodes make the
//!   seeded assets count exactly as the source's in an inode-counted budget;
//! - **admissions**: each seeded package's admission record appended to its name's stream of the target, after its
//!   objects and assets are in place. The target's streams start at the seed.
//!
//! The source must be on the target's filesystem (`seed_other_filesystem`: nothing is copied instead). A seed is
//! idempotent: what the target already holds identically is kept, and a restarted seed completes an interrupted one (an
//! asset directory placed without its appended record is completed by `locked_storage_asset`). A target that already
//! holds query packages or engine versions, or another admitted version of a seeded name, is refused. Nothing in the
//! source is changed, and nothing is ever removed.

use super::super::package::{
    VERUS_PACKAGE_ADMISSION_KIND, VERUS_QUERY_PACKAGE_V2_KIND, VERUS_SQL_CLAIM_KIND, VERUS_STATEMENT_KEY_KIND, VERUS_STATEMENT_KEY_V2_KIND,
};
use super::super::query_v4::{VERUS_PACKAGE_ADMISSION_V2_KIND, VERUS_QUERY_PACKAGE_V3_KIND, VERUS_SQL_CLAIM_V2_KIND};
use super::super::storage::{
    VERUS_STORAGE_ASSET_KIND, VerusStorageAssetV1, VerusStoragePackageV1, lock_storage_asset, locked_storage_asset, resolve_admitted_storage,
    resolve_storage_asset, storage_asset_directory, storage_stream, storage_versions,
};
use super::super::{RecordError, rejected};
use super::{VERUS_ENGINE_ADMISSION_KIND, VERUS_ENGINE_PACKAGE_KIND, engine_versions, refuse_query_packages};
use crate::append_only::{APPEND_RECORD_KIND, append_record};
use crate::content_id::ContentId;
use crate::object_store::ObjectStore;
use serde::Serialize;
use serde_json::Value;
use std::collections::BTreeSet;
use std::io::Read;
use std::os::unix::fs::MetadataExt;
use std::path::Path;

/// Record kinds a seed never carries: query packages and everything that names one, engine records, stream records.
const NOT_SEEDED: [&str; 12] = [
    APPEND_RECORD_KIND,
    VERUS_PACKAGE_ADMISSION_KIND,
    VERUS_PACKAGE_ADMISSION_V2_KIND,
    VERUS_QUERY_PACKAGE_V2_KIND,
    VERUS_QUERY_PACKAGE_V3_KIND,
    VERUS_STATEMENT_KEY_KIND,
    VERUS_STATEMENT_KEY_V2_KIND,
    VERUS_SQL_CLAIM_KIND,
    VERUS_SQL_CLAIM_V2_KIND,
    VERUS_ENGINE_PACKAGE_KIND,
    VERUS_ENGINE_ADMISSION_KIND,
    "gendb.verus.qualification-evidence.v2",
];

/// Leading bytes of every typed record (the canonical envelope); any other object is a blob.
const RECORD_PREFIX: &[u8] = b"{\"format_version\":";

/// One storage package to seed: its admission in the source and its published assets.
#[derive(Clone, Debug, Serialize)]
pub struct SeedStorage {
    pub name: String,
    pub package: ContentId,
    /// The source admission of the package (its name's newest admission naming it).
    pub admission: ContentId,
    /// Every published asset of the package: `(asset id, record)`.
    pub assets: Vec<(ContentId, VerusStorageAssetV1)>,
}

/// What a seed carries ([`plan_seed`]).
#[derive(Clone, Debug, Serialize)]
pub struct SeedPlan {
    pub storages: Vec<SeedStorage>,
    /// Every object the seeded admissions and assets reach (records and blobs), each once.
    pub objects: BTreeSet<ContentId>,
    /// The seeded assets' part files: count, and bytes counted once per filesystem identity (device, inode), as the
    /// storage budget counts them. File metadata only.
    pub part_files: u64,
    pub part_bytes_by_inode: u64,
}

/// What [`apply_seed`] did (the rest the target already held identically).
#[derive(Clone, Debug, Default, Serialize)]
pub struct SeedOutcome {
    pub objects_linked: u64,
    pub objects_present: u64,
    pub assets_linked: u64,
    pub assets_present: u64,
    pub admissions_appended: u64,
    pub admissions_present: u64,
}

/// The seed of the admitted storage packages `packages` of `source`: distinct packages of distinct names, each admitted,
/// every source of a derived package seeded too; the reachable objects, refusing any query, engine or stream record;
/// every published asset of each package, with its part files counted by inode. Reads records and file metadata only.
pub fn plan_seed(source: &ObjectStore, packages: &[ContentId]) -> Result<SeedPlan, RecordError> {
    if packages.is_empty() || packages.iter().collect::<BTreeSet<_>>().len() != packages.len() {
        return Err(rejected("seed_packages: name at least one storage package, each once"));
    }
    let mut storages = vec![];
    let mut records: Vec<VerusStoragePackageV1> = vec![];
    for id in packages {
        let package = resolve_admitted_storage(source, *id)?;
        if records.iter().any(|r| r.name == package.name) {
            return Err(rejected(format!("seed_packages: two seeded packages are versions of storage {}; an engine library seeds one version per name", package.name)));
        }
        let admission = storage_versions(source, &package.name)?
            .into_iter()
            .find(|(_, admission)| admission.package == *id)
            .map(|(admission_id, _)| admission_id)
            .ok_or_else(|| rejected(format!("storage package {id} has no admission")))?;
        storages.push(SeedStorage { name: package.name.clone(), package: *id, admission, assets: vec![] });
        records.push(package);
    }
    for package in &records {
        for derived in package.derived_from.iter().flat_map(|d| &d.sources) {
            if !packages.contains(&derived.package) {
                return Err(rejected(format!(
                    "seed_source_not_seeded: storage {} is built from {} ({}), which is not among the seeded packages",
                    package.name, derived.name, derived.package
                )));
            }
        }
    }
    for object in source.list_kind(VERUS_STORAGE_ASSET_KIND)? {
        let asset: VerusStorageAssetV1 = object.decode()?;
        let Some(storage) = storages.iter_mut().find(|s| s.package == asset.key.storage_package) else { continue };
        if resolve_storage_asset(source, &asset.key)?.map(|(published, _)| published) == Some(object.id) {
            storage.assets.push((object.id, asset));
        }
    }
    let roots: Vec<ContentId> = storages.iter().flat_map(|s| std::iter::once(s.admission).chain(s.assets.iter().map(|(id, _)| *id))).collect();
    let objects = reachable_objects(source, roots)?;
    let (mut part_files, mut part_bytes_by_inode, mut counted) = (0, 0, BTreeSet::new());
    for (_, asset) in storages.iter().flat_map(|s| &s.assets) {
        for (identity, bytes) in asset_part_files(&storage_asset_directory(source, asset)?)? {
            part_files += 1;
            if counted.insert(identity) {
                part_bytes_by_inode += bytes;
            }
        }
    }
    Ok(SeedPlan { storages, objects, part_files, part_bytes_by_inode })
}

/// Every object reachable from `roots` through the 64-hex identities in typed records' payloads that name objects of
/// `source`. A record of a kind in [`NOT_SEEDED`] refuses the seed.
fn reachable_objects(source: &ObjectStore, roots: Vec<ContentId>) -> Result<BTreeSet<ContentId>, RecordError> {
    let mut reached = BTreeSet::new();
    let mut pending = roots;
    while let Some(id) = pending.pop() {
        if !reached.insert(id) || !is_record(source, id)? {
            continue;
        }
        let object = source.read(id)?;
        if NOT_SEEDED.contains(&object.kind.as_str()) {
            return Err(rejected(format!(
                "seed_reaches_query_record: the seeded storages' records reach {} record {id}; an engine library holds storages only",
                object.kind
            )));
        }
        let payload: Value = object.decode()?;
        collect_identities(&payload, &mut |text| {
            if let Ok(next) = ContentId::parse_hex(text)
                && source.object_path(next).is_file()
            {
                pending.push(next);
            }
        });
    }
    Ok(reached)
}

/// Whether object `id` of `store` is a typed record (its file starts with the canonical envelope), from its first bytes.
fn is_record(store: &ObjectStore, id: ContentId) -> Result<bool, RecordError> {
    let path = store.object_path(id);
    let mut head = Vec::with_capacity(RECORD_PREFIX.len());
    std::fs::File::open(&path)
        .and_then(|file| file.take(RECORD_PREFIX.len() as u64).read_to_end(&mut head))
        .map_err(|error| RecordError::io(&path, error))?;
    Ok(head == RECORD_PREFIX)
}

/// Call `found` with every string of `value` that is 64 characters long (candidate identities).
fn collect_identities(value: &Value, found: &mut impl FnMut(&str)) {
    match value {
        Value::String(text) if text.len() == 64 => found(text),
        Value::Array(items) => items.iter().for_each(|item| collect_identities(item, found)),
        Value::Object(fields) => fields.values().for_each(|item| collect_identities(item, found)),
        _ => {}
    }
}

/// One part file: its filesystem identity `(device, inode)` and its length in bytes.
pub type PartFile = ((u64, u64), u64);

/// Every part file of an asset directory (`part-NNNN.bin`, in part order). Metadata only.
pub fn asset_part_files(directory: &Path) -> Result<Vec<PartFile>, RecordError> {
    let mut files = vec![];
    for index in 0.. {
        let path = directory.join(format!("part-{index:04}.bin"));
        match std::fs::metadata(&path) {
            Ok(meta) => files.push(((meta.dev(), meta.ino()), meta.len())),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => break,
            Err(error) => return Err(RecordError::io(&path, error)),
        }
    }
    Ok(files)
}

/// Carry `plan` from `source` into `target` (see the module documentation): objects by hard link, assets by hard-linked
/// part files placed as asset directories with their records appended, then each storage admission appended. Refused
/// before anything is written when the target holds query packages or engine versions, or another admitted version of
/// a seeded name.
pub fn apply_seed(source: &ObjectStore, target: &ObjectStore, plan: &SeedPlan) -> Result<SeedOutcome, RecordError> {
    refuse_query_packages(target)?;
    if !engine_versions(target)?.is_empty() {
        return Err(rejected("seed_after_engine: the target library already holds engine versions; a seed precedes every engine version"));
    }
    for storage in &plan.storages {
        if let Some((_, other)) = storage_versions(target, &storage.name)?.into_iter().find(|(_, a)| a.package != storage.package) {
            return Err(rejected(format!(
                "seed_target_differs: the target already admits package {} of storage {}, not the seeded {}",
                other.package, storage.name, storage.package
            )));
        }
    }
    let mut outcome = SeedOutcome::default();
    for id in &plan.objects {
        if link_file(&source.object_path(*id), &target.object_path(*id))? {
            outcome.objects_linked += 1;
        } else {
            outcome.objects_present += 1;
        }
    }
    let objects = target.objects_root();
    std::fs::File::open(&objects).and_then(|directory| directory.sync_all()).map_err(|error| RecordError::io(&objects, error))?;
    for (id, asset) in plan.storages.iter().flat_map(|s| &s.assets) {
        if link_asset(source, target, *id, asset)? {
            outcome.assets_linked += 1;
        } else {
            outcome.assets_present += 1;
        }
    }
    for storage in &plan.storages {
        if storage_versions(target, &storage.name)?.iter().any(|(_, a)| a.package == storage.package) {
            outcome.admissions_present += 1;
        } else {
            append_record(target, &storage_stream(&storage.name), storage.admission)?;
            outcome.admissions_appended += 1;
        }
    }
    Ok(outcome)
}

/// Hard-link `from` to the new name `to`; `false` when `to` already exists (an object of that identity is that content).
fn link_file(from: &Path, to: &Path) -> Result<bool, RecordError> {
    match std::fs::hard_link(from, to) {
        Ok(()) => Ok(true),
        Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => Ok(false),
        Err(error) if error.kind() == std::io::ErrorKind::CrossesDevices => Err(rejected(format!(
            "seed_other_filesystem: {} and {} are on different filesystems; a seed links, it never copies",
            from.display(),
            to.display()
        ))),
        Err(error) => Err(RecordError::io(to, error)),
    }
}

/// Seed one published asset under its key's lock: kept when the target already publishes it, else its part files are
/// hard-linked into a fresh staging directory, placed as `assets/<key id>` and its record appended. `true` when linked
/// now.
fn link_asset(source: &ObjectStore, target: &ObjectStore, id: ContentId, asset: &VerusStorageAssetV1) -> Result<bool, RecordError> {
    let lock = lock_storage_asset(target, asset.key.clone())?;
    if let Some((published, _)) = locked_storage_asset(target, &lock)? {
        return if published == id { Ok(false) } else { Err(rejected(format!("seed_target_differs: the target publishes asset {published} for the key of seeded asset {id}"))) };
    }
    let from = storage_asset_directory(source, asset)?;
    let staged = target.fresh_asset_staging_directory(lock.asset_name())?;
    std::fs::create_dir(&staged).map_err(|error| RecordError::io(&staged, error))?;
    for entry in std::fs::read_dir(&from).map_err(|error| RecordError::io(&from, error))? {
        let entry = entry.map_err(|error| RecordError::io(&from, error))?;
        if !entry.file_type().map_err(|error| RecordError::io(&entry.path(), error))?.is_file() {
            return Err(rejected(format!("seed_asset_not_flat: {} is not a part file", entry.path().display())));
        }
        link_file(&entry.path(), &staged.join(entry.file_name()))?;
    }
    if target.place_asset_directory(&staged, lock.asset_name().name())? != asset.directory {
        return Err(rejected("the seeded asset directory differs from its record"));
    }
    append_record(target, &asset.key.stream()?, id)?;
    Ok(true)
}
