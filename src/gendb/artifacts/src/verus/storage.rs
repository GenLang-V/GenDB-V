//! Storage packages (fixed storage entry `gendb-verus-storage-entry-v1`, or `gendb-verus-storage-entry-v2` for a
//! builder that assumes the declared integrity constraints) and their stored assets.
//!
//! A storage package is one checked storage build: the declaration of the columns it stores, the author's interface
//! (`represents`, readers) and builder, verified and compiled as one whole crate. A package of the storage entry v2
//! records the exact declaration set its builder assumes (`assumed_constraints`); it may be built, offered or composed
//! only in a run that declares exactly that set ([`VerusStoragePackageV1::check_declared_constraints`]), and its assets
//! are keyed by the package, so they never serve another set. Its record names the build, the
//! dependency closure of its interface (the files every query build that reads it must carry byte for byte) and the
//! build's check configuration. Admission appends the package to the stream `verus-storage.<name>`: the stream's
//! versions are the admitted packages of that name, the head is the current one, and query packages pin the exact
//! package they were checked against, so an older version stays resolvable.
//!
//! A stored asset is the parts the package's builder wrote for exactly one key: the package plus, per stored table,
//! its source version, row-order identity and row count (see [`VerusStorageAssetKeyV1`]). It lives in the library
//! (`assets/<key id>/`, named by its library-relative path) and is published once per key on
//! `verus-storage-asset.<key id>`, by the one holder of the key's lock ([`lock_storage_asset`]). Nothing on the serving path reads, hashes or validates part payload.
//!
//! The asset of a storage that is not admitted yet is built outside the library, in its session's trial directory,
//! with its record computed then ([`storage_asset_record`], [`storage_asset_id`]); it is published with exactly that
//! record, by renaming the trial build into the library, when the storage is registered
//! ([`publish_trial_storage_asset`]). No record is stored before that placement, so recovery never finds one.
//!
//! An asset can be **released** ([`release_storage_asset`]; the general engine line releases the derived assets no head
//! reads): its key's stream gets a release record ([`VerusStorageAssetReleaseV1`]) as its head, so the key has no
//! published asset again ([`resolve_storage_asset`] is `None`), and its directory is removed. The store is
//! append-only: the asset record itself stays, unnamed by the head. The package, its build and every other record stay,
//! so a later use of the key builds the asset again with the package's stored builder and publishes it after the
//! release record.

use super::build::{VERUS_BUILD_KIND, VerusBuildV1, VerusCheckConfigurationV1, VerusItemV1, VerusSourceOwnerV1, check_build_evidence};
use super::package::{VERUS_STORAGE_ENTRY_DERIVED_IDENTITY, VERUS_STORAGE_ENTRY_V1_IDENTITY, VERUS_STORAGE_ENTRY_V2_IDENTITY};
use super::{CONSTRAINTS_MODULE_PATH, RecordError, check_entry_theorems, check_framework_files, current_subject, read_record, rejected};
use crate::append_only::{AppendRecord, append_record, lookup_record_head};
use crate::canonical_json::{CanonError, content_id};
use crate::content_id::ContentId;
use crate::asset_directory::{ASSETS_DIRECTORY, AssetNameLock};
use crate::object_store::ObjectStore;
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

pub const VERUS_STORAGE_PACKAGE_KIND: &str = "gendb.verus.storage-package.v1";
pub const VERUS_STORAGE_ADMISSION_KIND: &str = "gendb.verus.storage-admission.v1";
pub const VERUS_STORAGE_ASSET_KIND: &str = "gendb.verus.storage-asset.v1";
/// Record kind of the release of a published asset ([`VerusStorageAssetReleaseV1`]).
pub const VERUS_STORAGE_ASSET_RELEASE_KIND: &str = "gendb.verus.storage-asset-release.v1";
const VERUS_STORAGE_ASSET_KEY_KIND: &str = "gendb.verus.storage-asset-key.v1";

/// One stored table of a storage declaration: the dataset table, its id in the schema and the ordinals the storage
/// delivers to its builder (ascending; a row-count carrier included).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusStoredTableV1 {
    pub table: String,
    pub table_id: usize,
    pub ordinals: Vec<usize>,
}

/// One file of a storage's dependency closure, as stored with its build.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusClosureFileV1 {
    /// Relative to the crate's `src/`.
    pub path: String,
    pub blob: ContentId,
    pub bytes: u64,
}

/// A checked storage build and what query builds must share with it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusStoragePackageV1 {
    /// The storage's name: its module `crate::stores::<name>` in storage and query crates.
    pub name: String,
    pub build: ContentId,
    pub entry_identity: String,
    /// The declared integrity constraints the builder assumes (storage entry v2): the identity
    /// (`declared_constraints_digest`, the blob id) of the build's generated `gendb_constraints.rs`. Absent (and not
    /// serialized) for the storage entry v1, so every existing package keeps its identity.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub assumed_constraints: Option<ContentId>,
    /// The stored tables (declaration order), the typed summary of `declaration`.
    pub tables: Vec<VerusStoredTableV1>,
    /// The storage declaration the framework files were generated from
    /// (`gendb_verification::obligations::DeclaredSource`, serialized).
    pub declaration: serde_json::Value,
    /// The dataset DDL the schema module was translated from (blob) and the frontend that translated it.
    pub schema_ddl: ContentId,
    pub frontend: serde_json::Value,
    /// The dependency closure of the interface (the registry's shared files of this storage), from the build.
    pub closure: Vec<VerusClosureFileV1>,
    pub configuration: VerusCheckConfigurationV1,
    /// Interface readers with the `requires`/`ensures` text Verus checked (descriptive).
    pub readers: Vec<VerusItemV1>,
    /// Theorem paths of the fixed storage entry the build proved (`gendb_entry::theorem_storage_built`, ...).
    pub theorems: Vec<String>,
    /// Inclusive worker-count domain of the builder.
    pub workers: (u32, u32),
    pub tcb: ContentId,
    /// The admitted storages this storage is built from (derived storage entry); absent (and not serialized) for a
    /// storage built from source columns, so every existing package keeps its identity.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub derived_from: Option<VerusDerivationV1>,
}

/// The admitted sources of a storage built from admitted storages.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusDerivationV1 {
    /// Per source, in the builder's use order.
    pub sources: Vec<VerusDerivationSourceV1>,
    /// The source whose whole part list the new storage inherits unchanged, before its builder's parts (an index into
    /// `sources`; its part files are shared by hard link).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub extends: Option<usize>,
}

/// One admitted source of a derived storage.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusDerivationSourceV1 {
    pub name: String,
    pub package: ContentId,
}

impl VerusStoragePackageV1 {
    /// The stream of the admitted versions of this storage name.
    pub fn stream(&self) -> String {
        storage_stream(&self.name)
    }

    /// The closure file at `path`, if the closure has one.
    pub fn closure_file(&self, path: &str) -> Option<&VerusClosureFileV1> {
        self.closure.iter().find(|file| file.path == path)
    }

    /// The fixed storage entry the package is proved with: the derived entry when it is built from admitted storages,
    /// else v2 exactly when it assumes declared constraints.
    pub fn storage_entry_identity(&self) -> &'static str {
        match self.derived_from {
            Some(_) => VERUS_STORAGE_ENTRY_DERIVED_IDENTITY,
            None => storage_entry_identity(self.assumed_constraints.is_some()),
        }
    }

    /// The one exact-set rule of constraint-dependent storages, for building, offering, evaluating and composing: `Ok`
    /// when the package assumes no declared constraint (storage entry v1: usable in every run), or exactly the run's
    /// declarations, `declared` being the run's `declared_constraints_digest` (`None`: the run declares none).
    /// Otherwise the named refusal `storage_assumes_declared_constraints`. No subset or reordering is accepted.
    pub fn check_declared_constraints(&self, declared: Option<ContentId>) -> Result<(), RecordError> {
        match (self.assumed_constraints, declared) {
            (None, _) => Ok(()),
            (Some(assumed), Some(run)) if assumed == run => Ok(()),
            (Some(assumed), run) => Err(rejected(format!(
                "storage_assumes_declared_constraints: storage {} assumes the declared integrity constraints {assumed}; this run declares {}",
                self.name,
                run.map_or("none".to_string(), |d| format!("other constraints {d}"))
            ))),
        }
    }
}

/// The fixed storage entry identity of a package that assumes declared constraints (v2) or not (v1).
pub fn storage_entry_identity(assumes_declared_constraints: bool) -> &'static str {
    if assumes_declared_constraints { VERUS_STORAGE_ENTRY_V2_IDENTITY } else { VERUS_STORAGE_ENTRY_V1_IDENTITY }
}

pub fn storage_stream(name: &str) -> String {
    format!("verus-storage.{name}")
}

/// Admission of one storage package on its name's stream.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusStorageAdmissionV1 {
    pub package: ContentId,
    pub gate_identity: String,
    /// The storage checks that preceded admission (tiny cases, source-domain probes, asset build records).
    pub evidence: Vec<ContentId>,
}

/// Store a storage package record after checking it against its build: the build is admissible evidence
/// ([`check_build_evidence`]) of the package's fixed storage entry (v2 exactly when it records `assumed_constraints`),
/// defining every named theorem; the build carries `gendb_constraints.rs` exactly for entry v2, as a framework file
/// with the recorded identity; the package and build name the same TCB; the stored framework files are exactly `expected_framework` (the fresh generation of the storage crate's
/// framework files), byte for byte and complete; author files lie only under `stores/<name>/interface/` and
/// `builder/`; the closure is a set of framework-owned files of the build with their stored blobs, and includes the
/// interface root `stores/<name>/interface/mod.rs`, `schema.rs` and the declaration; the configuration is the build's;
/// the stored tables are distinct with ascending ordinals; the worker domain starts at 1.
pub fn publish_storage_package(
    store: &ObjectStore,
    package: &VerusStoragePackageV1,
    expected_framework: &[(&str, &str)],
) -> Result<ContentId, RecordError> {
    let build = check_build_evidence(store, package.build)?;
    let entry_identity = package.storage_entry_identity();
    if build.tcb != package.tcb || package.entry_identity != entry_identity {
        return Err(rejected("storage package names another TCB or entry than its build"));
    }
    let entry = build.framework_text(store, "gendb_entry.rs")?;
    check_entry_theorems(&entry, entry_identity, &package.theorems, "gendb_entry::theorem_storage_built")?;
    check_assumed_constraints(package, &build)?;
    check_framework_files(store, &build, expected_framework)?;
    let interface = format!("stores/{}/interface/", package.name);
    if let Some(source) = build
        .sources
        .iter()
        .find(|s| s.owner == VerusSourceOwnerV1::Agent && !(s.path.starts_with(&interface) || s.path.starts_with("builder/")))
    {
        return Err(rejected(format!("storage build author file {} lies outside {interface} and builder/", source.path)));
    }
    let mut paths = BTreeSet::new();
    for file in &package.closure {
        let stored = build.sources.iter().find(|s| s.path == file.path);
        let own = stored.is_some_and(|s| s.blob == file.blob && s.bytes == file.bytes && !s.path.starts_with("builder/"));
        if !own || !paths.insert(file.path.as_str()) {
            return Err(rejected(format!("closure file {} is not a stored, shared file of the storage build", file.path)));
        }
    }
    for required in [format!("{interface}mod.rs"), "schema.rs".into(), format!("stores/{}/declaration.rs", package.name)] {
        if !paths.contains(required.as_str()) {
            return Err(rejected(format!("the storage closure lacks {required}")));
        }
    }
    if build.check_configuration()? != package.configuration {
        return Err(rejected("storage package configuration differs from its build's"));
    }
    check_stored_tables(&package.tables)?;
    check_derivation(store, package)?;
    if !(1..=package.workers.1).contains(&package.workers.0) {
        return Err(rejected("storage package worker domain is empty"));
    }
    store.read_blob(package.schema_ddl, None)?;
    Ok(store.put(1, VERUS_STORAGE_PACKAGE_KIND, package)?)
}

/// A derived package names at least one source, each an admitted storage package of its recorded name with another
/// name than the new storage's, all distinct, and an extended source among them.
fn check_derivation(store: &ObjectStore, package: &VerusStoragePackageV1) -> Result<(), RecordError> {
    let Some(derivation) = &package.derived_from else { return Ok(()) };
    let mut names = BTreeSet::new();
    for source in &derivation.sources {
        let admitted = resolve_admitted_storage(store, source.package)?;
        if admitted.name != source.name || source.name == package.name || !names.insert(source.name.as_str()) {
            return Err(rejected(format!("derived storage {}: source {} is not a distinct admitted storage of another name", package.name, source.name)));
        }
    }
    if derivation.sources.is_empty() || derivation.extends.is_some_and(|k| k >= derivation.sources.len()) {
        return Err(rejected(format!("derived storage {} names no source, or extends none of its sources", package.name)));
    }
    Ok(())
}

/// The build's `gendb_constraints.rs` is a framework file whose blob is the package's `assumed_constraints`, and is
/// absent exactly when the package assumes none.
fn check_assumed_constraints(package: &VerusStoragePackageV1, build: &VerusBuildV1) -> Result<(), RecordError> {
    let module = build.sources.iter().find(|s| s.path == CONSTRAINTS_MODULE_PATH);
    match (package.assumed_constraints, module) {
        (None, None) => Ok(()),
        (Some(assumed), Some(source)) if source.owner == VerusSourceOwnerV1::Framework && source.blob == assumed => Ok(()),
        (None, Some(_)) => Err(rejected(
            "declared_constraints_unexpected: the storage build has gendb_constraints.rs but its package assumes no declared constraints",
        )),
        (Some(_), None) => Err(rejected(
            "declared_constraints_missing: the storage package assumes declared constraints but its build has no gendb_constraints.rs",
        )),
        (Some(_), Some(_)) => Err(rejected("gendb_constraints.rs of the storage build is not the package's assumed constraints")),
    }
}

/// Admit a published storage package: append it to its name's stream. The admission names at least one readable
/// evidence record.
pub fn admit_storage_package(store: &ObjectStore, admission: &VerusStorageAdmissionV1) -> Result<ContentId, RecordError> {
    let package: VerusStoragePackageV1 = read_record(store, admission.package, VERUS_STORAGE_PACKAGE_KIND)?;
    check_build_evidence(store, package.build)?;
    if admission.evidence.is_empty() {
        return Err(rejected("storage admission requires evidence"));
    }
    for id in &admission.evidence {
        store.read(*id)?;
    }
    if storage_versions(store, &package.name)?.iter().any(|(_, admitted)| admitted.package == admission.package) {
        return Err(rejected("this storage package is already admitted"));
    }
    let id = store.put(1, VERUS_STORAGE_ADMISSION_KIND, admission)?;
    append_record(store, &package.stream(), id)?;
    Ok(id)
}

/// Every admitted version of storage `name`, newest first: `(admission id, admission)`.
pub fn storage_versions(store: &ObjectStore, name: &str) -> Result<Vec<(ContentId, VerusStorageAdmissionV1)>, RecordError> {
    let mut versions = vec![];
    let mut next = lookup_record_head(store, &storage_stream(name))?;
    while let Some(record_id) = next {
        let record: AppendRecord = store.read(record_id)?.decode()?;
        let admission: VerusStorageAdmissionV1 = read_record(store, record.subject, VERUS_STORAGE_ADMISSION_KIND)?;
        versions.push((record.subject, admission));
        next = record.previous;
    }
    Ok(versions)
}

/// The admitted storage package `id`: its record, provided some admission of its name names it.
pub fn resolve_admitted_storage(store: &ObjectStore, id: ContentId) -> Result<VerusStoragePackageV1, RecordError> {
    let package: VerusStoragePackageV1 = read_record(store, id, VERUS_STORAGE_PACKAGE_KIND)?;
    if !storage_versions(store, &package.name)?.iter().any(|(_, admission)| admission.package == id) {
        return Err(rejected(format!("storage package {id} ({}) is not admitted", package.name)));
    }
    Ok(package)
}

/// Every storage name with an admission in the library, sorted.
fn admitted_names(store: &ObjectStore) -> Result<BTreeSet<String>, RecordError> {
    let mut names = BTreeSet::new();
    for object in store.list_kind(VERUS_STORAGE_ADMISSION_KIND)? {
        let admission: VerusStorageAdmissionV1 = object.decode()?;
        let package: VerusStoragePackageV1 = read_record(store, admission.package, VERUS_STORAGE_PACKAGE_KIND)?;
        names.insert(package.name);
    }
    Ok(names)
}

/// The current (head) admitted package of every storage name in the library: `(package id, package)`, by name.
pub fn current_storages(store: &ObjectStore) -> Result<Vec<(ContentId, VerusStoragePackageV1)>, RecordError> {
    let mut current = vec![];
    for name in admitted_names(store)? {
        if let Some(admission_id) = current_subject(store, &storage_stream(&name))? {
            let admission: VerusStorageAdmissionV1 = read_record(store, admission_id, VERUS_STORAGE_ADMISSION_KIND)?;
            current.push((admission.package, read_record(store, admission.package, VERUS_STORAGE_PACKAGE_KIND)?));
        }
    }
    Ok(current)
}

/// One admitted storage version: its package, and whether it is its name's current (head) version.
#[derive(Clone, Debug)]
pub struct AdmittedStorage {
    pub package_id: ContentId,
    pub package: VerusStoragePackageV1,
    pub current: bool,
}

/// Every distinct admitted storage package in the library (for author discovery): by name, then newest first within a
/// name; the first of each name is its current version. Older versions of a name stay usable by exact package id.
pub fn admitted_storages(store: &ObjectStore) -> Result<Vec<AdmittedStorage>, RecordError> {
    let mut admitted = vec![];
    for name in admitted_names(store)? {
        let mut seen = BTreeSet::new();
        for (position, (_, admission)) in storage_versions(store, &name)?.into_iter().enumerate() {
            if seen.insert(admission.package) {
                let package = read_record(store, admission.package, VERUS_STORAGE_PACKAGE_KIND)?;
                admitted.push(AdmittedStorage { package_id: admission.package, package, current: position == 0 });
            }
        }
    }
    Ok(admitted)
}

/// One stored table of an asset key: its current source version, its row-order identity (the capture's label of one
/// read of its source files in file row order) and its row count.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusStorageAssetTableV1 {
    pub table: String,
    pub source_version: String,
    pub row_order: String,
    pub rows: u64,
}

/// Applicability key of one stored asset: the storage package and every stored table's source version, row-order
/// identity and row count, in declaration order. Two assets of one table with equal (source version, row order) relate
/// to one row sequence, so storages of one table can be read together (`same_capture`); a changed source or a new
/// read of it is another key, so a stale asset is never returned. Adding columns to an unchanged table's capture keeps
/// its key.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusStorageAssetKeyV1 {
    pub storage_package: ContentId,
    pub tables: Vec<VerusStorageAssetTableV1>,
}

impl VerusStorageAssetKeyV1 {
    pub fn identity(&self) -> Result<ContentId, CanonError> {
        content_id(1, VERUS_STORAGE_ASSET_KEY_KIND, self)
    }

    pub fn stream(&self) -> Result<String, CanonError> {
        Ok(format!("verus-storage-asset.{}", self.identity()?.to_hex()))
    }
}

/// A stored asset: the parts the package's builder wrote for exactly the key, in the library.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusStorageAssetV1 {
    pub key: VerusStorageAssetKeyV1,
    /// Library-relative directory (`assets/<key id>`).
    pub directory: String,
    /// `parts.json` of the directory: format, byte order, `(element type, element count)` per part, stored bytes.
    pub parts_format: u32,
    pub byte_order: String,
    pub parts: Vec<(String, u64)>,
    pub storage_bytes: u64,
    pub build_wall_ns: u64,
    /// The build record: which stored library ran over which input capture, its call record and column rows.
    pub evidence: ContentId,
}

/// The release of one published asset ([`release_storage_asset`]): the head of its key's stream from then on, so the
/// key has no published asset until it is built and published again.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusStorageAssetReleaseV1 {
    /// The released asset's key (its package and, per stored table, the capture it was built for).
    pub key: VerusStorageAssetKeyV1,
    /// The released asset record and its library-relative directory (removed).
    pub asset: ContentId,
    pub directory: String,
    /// The asset's stored bytes (its parts as recorded; part files it shared by hard link are counted here too).
    pub storage_bytes: u64,
    /// Why it was released (the caller's rule) and when (Unix ms).
    pub reason: String,
    pub released_unix_ms: u64,
}

/// What one release did: the release record, its id, and the bytes of the removed directory's files (`file_bytes`) of
/// which `freed_bytes` held their last link (a part file shared by hard link with another asset or a capture stays on
/// disk under its other names, untouched).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReleasedAsset {
    pub release: ContentId,
    pub record: VerusStorageAssetReleaseV1,
    pub file_bytes: u64,
    pub freed_bytes: u64,
}

/// The manifest facts of a built parts directory, as the builder's host reported them.
pub struct BuiltParts {
    pub format_version: u32,
    pub byte_order: String,
    pub parts: Vec<(String, u64)>,
    pub storage_bytes: u64,
}

/// The exclusive build/publication lock of one asset key ([`lock_storage_asset`]). Holding it from the lookup until
/// the publication makes one builder per key across processes; other keys are not blocked.
#[derive(Debug)]
pub struct StorageAssetLock {
    key: VerusStorageAssetKeyV1,
    name: AssetNameLock,
}

impl StorageAssetLock {
    pub fn key(&self) -> &VerusStorageAssetKeyV1 {
        &self.key
    }

    /// The held lock of the key's asset directory name (for its staging directories).
    pub fn asset_name(&self) -> &AssetNameLock {
        &self.name
    }
}

/// Wait for, then hold, the lock of `key` (its asset directory name, `assets/.locks/<key id>.lock`).
pub fn lock_storage_asset(store: &ObjectStore, key: VerusStorageAssetKeyV1) -> Result<StorageAssetLock, RecordError> {
    let name = store.lock_asset_name(key.identity()?)?;
    Ok(StorageAssetLock { key, name })
}

/// Under the key's lock, the asset of the key if one exists or can be completed; `None` when the key needs a build.
///
/// Crash and retry, precisely (nothing here claims more durability than this):
/// - a build that died before placement leaves only a staging directory (never placed, never served; left for the
///   cleanup), and the key has no directory: `None`, build again;
/// - a publication that died after the rename and after storing its record but before appending it: the stored record
///   of exactly this key and directory is found (a bounded scan of record headers of this kind, only on this path) and
///   appended, completing that publication without a build;
/// - a directory with no stored record (died between the rename and the record): refused with
///   `unrecorded_asset_directory`; it is never overwritten or adopted without its build evidence, and removing it is
///   a user decision;
/// - after a release ([`release_storage_asset`]) the key's earlier asset records are on its stream already, so the
///   search above skips them: only a record never appended completes a publication.
pub fn locked_storage_asset(store: &ObjectStore, lock: &StorageAssetLock) -> Result<Option<(ContentId, VerusStorageAssetV1)>, RecordError> {
    if let Some(published) = resolve_storage_asset(store, &lock.key)? {
        return Ok(Some(published));
    }
    if !store.asset_directory_exists(lock.name.name()) {
        return Ok(None);
    }
    let directory = format!("{}/{}", ASSETS_DIRECTORY, lock.name.name().to_hex());
    let appended = stream_subjects(store, &lock.key.stream()?)?;
    for object in store.list_kind(VERUS_STORAGE_ASSET_KIND)? {
        let asset: VerusStorageAssetV1 = object.decode()?;
        if asset.key == lock.key && asset.directory == directory && !appended.contains(&object.id) {
            append_record(store, &lock.key.stream()?, object.id)?;
            return Ok(Some((object.id, asset)));
        }
    }
    Err(rejected(format!(
        "unrecorded_asset_directory: {directory} exists without a stored asset record (an interrupted publication); it is not overwritten"
    )))
}

/// Publish the stored asset of the locked key from the complete staged build `staged` (see
/// `ObjectStore::place_asset_directory`): the key's package is a published storage package with admissible build
/// evidence; the key lists exactly the package's stored tables in order, each with a source version, row-order
/// identity and row count; the key has no asset and no directory ([`locked_storage_asset`] returned `None` under this
/// lock). The directory is placed as `assets/<key id>` (a rename, no copy; an existing directory is refused, never
/// replaced), then the record is stored and appended. Returns `(asset id, asset)`.
pub fn publish_storage_asset(
    store: &ObjectStore,
    lock: &StorageAssetLock,
    staged: &Path,
    built: BuiltParts,
    build_wall_ns: u64,
    evidence: ContentId,
) -> Result<(ContentId, VerusStorageAssetV1), RecordError> {
    let asset = storage_asset_record(lock.key.clone(), built, build_wall_ns, evidence)?;
    publish_asset_record(store, lock, asset, |name| store.place_asset_directory(staged, name))
}

/// Publish the stored asset of the locked key from the sealed trial build `trial` (an unadmitted storage's
/// run-local build, `ObjectStore::place_trial_asset_directory`) with exactly the record `asset` computed when it was
/// built ([`storage_asset_record`]), so the published asset id is the one its trials and evaluations recorded. The
/// checks and order are those of [`publish_storage_asset`].
pub fn publish_trial_storage_asset(
    store: &ObjectStore,
    lock: &StorageAssetLock,
    trial: &Path,
    asset: VerusStorageAssetV1,
) -> Result<(ContentId, VerusStorageAssetV1), RecordError> {
    if asset.key != lock.key || asset.directory != storage_asset_relative_directory(&lock.key)? {
        return Err(rejected("the trial asset record names another key or directory than the locked key's"));
    }
    publish_asset_record(store, lock, asset, |name| store.place_trial_asset_directory(trial, name))
}

/// The record of the asset of `key` built as `built` (library-relative directory `assets/<key id>`): what
/// publication stores, computable before placement.
pub fn storage_asset_record(key: VerusStorageAssetKeyV1, built: BuiltParts, build_wall_ns: u64, evidence: ContentId) -> Result<VerusStorageAssetV1, RecordError> {
    Ok(VerusStorageAssetV1 {
        directory: storage_asset_relative_directory(&key)?,
        key,
        parts_format: built.format_version,
        byte_order: built.byte_order,
        parts: built.parts,
        storage_bytes: built.storage_bytes,
        build_wall_ns,
        evidence,
    })
}

/// The identity publication gives the asset record `asset`.
pub fn storage_asset_id(asset: &VerusStorageAssetV1) -> Result<ContentId, RecordError> {
    Ok(content_id(1, VERUS_STORAGE_ASSET_KIND, asset)?)
}

fn storage_asset_relative_directory(key: &VerusStorageAssetKeyV1) -> Result<String, RecordError> {
    Ok(format!("{ASSETS_DIRECTORY}/{}", key.identity()?.to_hex()))
}

/// The checks of an asset publication, then `place` (the rename to `assets/<key id>`), the record and the append.
fn publish_asset_record(
    store: &ObjectStore,
    lock: &StorageAssetLock,
    asset: VerusStorageAssetV1,
    place: impl FnOnce(ContentId) -> Result<String, crate::object_store::StoreError>,
) -> Result<(ContentId, VerusStorageAssetV1), RecordError> {
    let key = &asset.key;
    let package: VerusStoragePackageV1 = read_record(store, key.storage_package, VERUS_STORAGE_PACKAGE_KIND)?;
    check_build_evidence(store, package.build)?;
    let covers = key.tables.len() == package.tables.len()
        && key.tables.iter().zip(&package.tables).all(|(keyed, stored)| {
            keyed.table == stored.table && !keyed.source_version.is_empty() && !keyed.row_order.is_empty()
        });
    if !covers {
        return Err(rejected("asset key differs from its storage package's stored tables or lacks a source version or row order"));
    }
    store.read(asset.evidence)?;
    if resolve_storage_asset(store, key)?.is_some() {
        return Err(rejected("an asset of this storage package for these source versions is already published"));
    }
    if place(lock.name.name())? != asset.directory {
        return Err(rejected("the placed asset directory differs from its record"));
    }
    let id = store.put(1, VERUS_STORAGE_ASSET_KIND, &asset)?;
    append_record(store, &key.stream()?, id)?;
    Ok((id, asset))
}

/// The published asset of exactly this key, if any: `(asset id, asset)`. A key whose stream ends with a release
/// ([`release_storage_asset`]) has none.
pub fn resolve_storage_asset(
    store: &ObjectStore,
    key: &VerusStorageAssetKeyV1,
) -> Result<Option<(ContentId, VerusStorageAssetV1)>, RecordError> {
    let Some(id) = current_subject(store, &key.stream()?)? else {
        return Ok(None);
    };
    if store.read(id)?.kind == VERUS_STORAGE_ASSET_RELEASE_KIND {
        return Ok(None);
    }
    let asset: VerusStorageAssetV1 = read_record(store, id, VERUS_STORAGE_ASSET_KIND)?;
    if &asset.key != key {
        return Err(rejected("published storage asset key differs from its stream"));
    }
    Ok(Some((id, asset)))
}

/// The release that ends this key's stream, if its head is one: `(release id, release)` (the released asset's exact
/// stored bytes are the estimate of its rebuild).
pub fn released_storage_asset(store: &ObjectStore, key: &VerusStorageAssetKeyV1) -> Result<Option<(ContentId, VerusStorageAssetReleaseV1)>, RecordError> {
    let Some(id) = current_subject(store, &key.stream()?)? else {
        return Ok(None);
    };
    if store.read(id)?.kind != VERUS_STORAGE_ASSET_RELEASE_KIND {
        return Ok(None);
    }
    let release: VerusStorageAssetReleaseV1 = read_record(store, id, VERUS_STORAGE_ASSET_RELEASE_KIND)?;
    if &release.key != key {
        return Err(rejected("a storage asset release names another key than its stream"));
    }
    Ok(Some((id, release)))
}

/// Release the published asset `asset` of the locked key (module documentation), for `reason` at `at_unix_ms`: its
/// directory is renamed into the library's asset staging directory (one rename: from then on nothing can read it under
/// its name), the release record is stored and appended to the key's stream (from then on the key has no published
/// asset), and the renamed directory is removed. `Ok(None)` when `asset` is not the key's published asset any more
/// (released or replaced by another caller): nothing is done. Only the directory and the stream head change: the asset
/// record, the package, its build and evidence stay. Part files shared by hard link (an extension's inherited parts, a
/// reused build, a capture's files) lose only this directory's name for them.
///
/// Crash and retry: an interruption after the rename and before the record leaves a published asset without its
/// directory, which a lookup refuses by name (`asset_directory_missing`) until it is released again; one after the
/// record leaves a staged leftover of the key's name, removed at the key's next lookup
/// (`ObjectStore::remove_stale_asset_staging`).
pub fn release_storage_asset(store: &ObjectStore, lock: &StorageAssetLock, asset: ContentId, reason: &str, at_unix_ms: u64) -> Result<Option<ReleasedAsset>, RecordError> {
    let Some((published, record)) = resolve_storage_asset(store, &lock.key)? else {
        return Ok(None);
    };
    if published != asset {
        return Ok(None);
    }
    let retired = store.retire_asset_directory(&lock.name)?;
    let release = VerusStorageAssetReleaseV1 {
        key: lock.key.clone(),
        asset,
        directory: record.directory.clone(),
        storage_bytes: record.storage_bytes,
        reason: reason.to_string(),
        released_unix_ms: at_unix_ms,
    };
    let id = store.put(1, VERUS_STORAGE_ASSET_RELEASE_KIND, &release)?;
    append_record(store, &lock.key.stream()?, id)?;
    let (file_bytes, freed_bytes) = match retired {
        Some(staged) => store.remove_retired_asset_directory(&staged)?,
        None => (0, 0),
    };
    Ok(Some(ReleasedAsset { release: id, record: release, file_bytes, freed_bytes }))
}

/// Every subject ever appended to `stream` (published and released records alike).
fn stream_subjects(store: &ObjectStore, stream: &str) -> Result<BTreeSet<ContentId>, RecordError> {
    let mut subjects = BTreeSet::new();
    let mut next = lookup_record_head(store, stream)?;
    while let Some(record_id) = next {
        let record: AppendRecord = store.read(record_id)?.decode()?;
        subjects.insert(record.subject);
        next = record.previous;
    }
    Ok(subjects)
}

/// The absolute parts directory of a published asset in `store` (checked to be a library-relative asset path).
pub fn storage_asset_directory(store: &ObjectStore, asset: &VerusStorageAssetV1) -> Result<PathBuf, RecordError> {
    Ok(store.asset_directory(&asset.directory)?)
}

/// The build record of a storage package (not re-checked: serving and lookup trust admission).
pub fn storage_build(store: &ObjectStore, package: &VerusStoragePackageV1) -> Result<VerusBuildV1, RecordError> {
    read_record(store, package.build, VERUS_BUILD_KIND)
}

/// At least one stored table; tables distinct; ordinals non-empty and strictly ascending.
fn check_stored_tables(tables: &[VerusStoredTableV1]) -> Result<(), RecordError> {
    if tables.is_empty() {
        return Err(rejected("a storage stores at least one table"));
    }
    let mut seen = BTreeSet::new();
    for table in tables {
        let ordered = !table.ordinals.is_empty() && table.ordinals.windows(2).all(|pair| pair[0] < pair[1]);
        if !seen.insert(&table.table) || !ordered {
            return Err(rejected(format!("stored table {} is repeated or its ordinals are empty or unordered", table.table)));
        }
    }
    Ok(())
}
