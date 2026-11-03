//! Engine packages (fixed engine entry `gendb-verus-engine-entry-v1`): one verified engine for a whole schema, the
//! append-only stream of its admitted versions in an engine library, and the selected version.
//!
//! An **engine library** is one engine run's library: it is seeded with admitted storage
//! packages and their assets ([`seed`]) and holds no query package. Its engine versions are admitted on the one stream
//! [`ENGINE_STREAM`] in order: version `N` is the stream's record at sequence `N - 1`. The **selected** version is the
//! one serving answers by default, and the only one whose storage uses pin payload (the serving set of
//! `synthesis::storage::budget` in an engine library). Older versions stay recorded and resolvable by package id, with
//! their builds and storage packages; they pin nothing. Nothing is ever removed.
//!
//! Which version is selected:
//! - a library with no selection record (a schema-engine run): the newest admitted version, so admitting selects;
//! - a library with selection records (a general-engine run, with versions of several
//!   branches): the version the newest record of [`ENGINE_SELECTION_STREAM`] names ([`select_engine_version`]: each
//!   record is one change of the main-line head). Admitting a version then selects nothing.
//!
//! A version admitted on a branch carries its lineage as admission evidence ([`VerusEngineLineageV1`]: branch, kind and
//! parent versions); admission checks that every parent is an admitted version of the same library.
//!
//! A package names its checked build (one whole-crate `--no-cheating` verify-and-compile run over the frozen engine
//! crate), the exact admitted storage packages it reads (`storage_uses`, in the order of the entry's `uses`), the
//! dataset DDL and the declared integrity constraints its claim assumes, and the inputs of its framework generation
//! (the generation identity and the toolkit files). Publication ([`publish_engine_package`]) compares the build's
//! framework files byte for byte with the caller's fresh generation; admission ([`admit_engine_version`]) checks, for
//! every storage use, the same check configuration, the storage's dependency closure carried byte for byte and the
//! caller's full composition rule, as for query packages over stored data (`query_v4`).

pub mod seed;

use super::build::{VERUS_BUILD_KIND, VERUS_IMPLEMENTATION_KIND, VERUS_TCB_KIND};
use super::build::{VerusBuildV1, VerusCheckConfigurationV1, VerusImplementationV1, VerusSourceOwnerV1, VerusTcbV1, check_build_evidence};
use super::package::{VERUS_PACKAGE_ADMISSION_KIND, VERUS_QUERY_PACKAGE_V2_KIND};
use super::query_v4::{CompositionRule, StorageComposition, VERUS_PACKAGE_ADMISSION_V2_KIND, VerusStorageUseV1};
use super::storage::{
    VERUS_STORAGE_ASSET_KIND, VerusClosureFileV1, VerusStorageAssetV1, VerusStoragePackageV1, resolve_admitted_storage, resolve_storage_asset,
    storage_build,
};
use super::{CONSTRAINTS_MODULE_PATH, RecordError, check_entry_theorems, check_framework_files, read_record, rejected};
use crate::append_only::{AppendRecord, append_record, lookup_record_head};
use crate::content_id::ContentId;
use crate::object_store::ObjectStore;
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

/// Identity of the fixed engine entry (`verification/obligations/engine_entry.rs`).
pub const VERUS_ENGINE_ENTRY_V1_IDENTITY: &str = "gendb-verus-engine-entry-v1";
pub const VERUS_ENGINE_PACKAGE_KIND: &str = "gendb.verus.engine-package.v1";
pub const VERUS_ENGINE_ADMISSION_KIND: &str = "gendb.verus.engine-admission.v1";
/// The stream of an engine library's admitted engine versions (oldest first; without selection records the head is
/// the selected version).
pub const ENGINE_STREAM: &str = "verus-engine";
/// The stream of an engine library's selection changes (oldest first; the head names the selected version).
pub const ENGINE_SELECTION_STREAM: &str = "verus-engine-selection";
pub const VERUS_ENGINE_SELECTION_KIND: &str = "gendb.verus.engine-selection.v1";
/// Admission evidence of a version admitted with its lineage (at most one per admission).
pub const VERUS_ENGINE_LINEAGE_KIND: &str = "gendb.verus.engine-lineage.v1";
/// Engine ABI version of every engine package (the engine symbols and inputs, `gendb_runtime::abi::ENGINE_ABI_VERSION`).
pub const ENGINE_PACKAGE_ABI_VERSION: u64 = 1;
/// The theorem every engine package must name.
const END_TO_END_THEOREM: &str = "gendb_entry::theorem_engine_end_to_end";
/// Where the engine-only proof toolkit lies in engine crates.
const TOOLKIT_DIRECTORY: &str = "engine_link/";

/// One checked engine build and what it reads.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusEnginePackageV1 {
    pub entry_identity: String,
    pub build: ContentId,
    /// Theorem paths of the fixed engine entry the build proved (`gendb_entry::theorem_engine_end_to_end`, ...).
    pub theorems: Vec<String>,
    /// The dataset DDL (with the declared integrity constraints) the crate's schema modules were generated from (blob);
    /// serving translates statements against exactly this text.
    pub schema_ddl: ContentId,
    /// The frontend that translated it (descriptive).
    pub frontend: serde_json::Value,
    /// The declared integrity constraints the claim assumes: the blob id of the build's `gendb_constraints.rs`
    /// (`declared_constraints_digest`).
    pub constraints: ContentId,
    /// The identity the generated headers name (`engine_crate_files(.., identity)`): needed for a fresh generation.
    pub generation_identity: String,
    /// The admitted storages the engine reads, in the order of the entry's `uses`.
    pub storage_uses: Vec<VerusStorageUseV1>,
    /// The engine-only proof toolkit files the crate carried (`engine_link/**`, as stored with the build).
    pub toolkit: Vec<VerusClosureFileV1>,
    pub implementations: Vec<ContentId>,
    pub abi_version: u64,
    /// Inclusive worker-count domain of the checked theorem.
    pub workers: (u32, u32),
    pub tcb: ContentId,
}

/// Admission of one engine version on [`ENGINE_STREAM`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusEngineAdmissionV1 {
    pub package: ContentId,
    pub gate_identity: String,
    /// The admission evidence (static checks, storage policy, qualification, and timing when the caller timed before
    /// admitting): readable records.
    pub evidence: Vec<ContentId>,
    /// The stored assets qualification ran over (descriptive; serving resolves assets for the current capture).
    pub assets: Vec<ContentId>,
}

/// Where an engine version comes from (admission evidence of kind [`VERUS_ENGINE_LINEAGE_KIND`]): the branch it was
/// admitted on, how it was made, and the admitted versions its code derives from.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusEngineLineageV1 {
    /// `main` (the framework's version 0 and merges) or a branch name (`b1`, `b2`, ...).
    pub branch: String,
    /// `framework_generated` (version 0, no parent), `branch` (one parent) or `merge` (two or more parents).
    pub kind: String,
    /// The engine package ids of its parent versions, each admitted in the same library before it.
    pub parents: Vec<ContentId>,
}

/// The lineage kinds and their parent counts.
const LINEAGE_KINDS: [(&str, usize, usize); 3] = [("framework_generated", 0, 0), ("branch", 1, 1), ("merge", 2, usize::MAX)];

/// One change of the selected engine version (a record of [`ENGINE_SELECTION_STREAM`]).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusEngineSelectionV1 {
    /// The admitted engine package selected from now on.
    pub package: ContentId,
    /// Its admission record on [`ENGINE_STREAM`].
    pub admission: ContentId,
    /// Why (for example `framework_generated version 0`, `interleaved timing against the previous selection`).
    pub reason: String,
    /// Readable records that decided it (for example the interleaved timing); may be empty for version 0.
    pub evidence: Vec<ContentId>,
}

/// Store an engine package record after checking it against its build: admissible build evidence of the fixed engine
/// entry, whose text defines every named theorem including `theorem_engine_end_to_end`; the same TCB; the build's
/// framework files exactly `expected_framework` (the caller's fresh generation of the engine crate with its shim), byte
/// for byte and complete; author files only under `agent/`; `gendb_constraints.rs` a framework file whose blob is the
/// package's `constraints`; the toolkit list exactly the build's `engine_link/**` framework files; distinct admitted
/// storage uses whose assumed declared constraints, if any, are exactly the package's; a worker domain starting at 1;
/// implementations of the same build; a readable DDL blob.
pub fn publish_engine_package(store: &ObjectStore, package: &VerusEnginePackageV1, expected_framework: &[(&str, &str)]) -> Result<ContentId, RecordError> {
    let build = check_build_evidence(store, package.build)?;
    if package.entry_identity != VERUS_ENGINE_ENTRY_V1_IDENTITY || package.abi_version != ENGINE_PACKAGE_ABI_VERSION || build.tcb != package.tcb {
        return Err(rejected(format!(
            "engine package entry {} / ABI v{} / TCB is not its build's fixed engine entry {VERUS_ENGINE_ENTRY_V1_IDENTITY}, ABI v{ENGINE_PACKAGE_ABI_VERSION} and TCB",
            package.entry_identity, package.abi_version
        )));
    }
    read_record::<VerusTcbV1>(store, package.tcb, VERUS_TCB_KIND)?;
    check_entry_theorems(&build.framework_text(store, "gendb_entry.rs")?, VERUS_ENGINE_ENTRY_V1_IDENTITY, &package.theorems, END_TO_END_THEOREM)?;
    check_framework_files(store, &build, expected_framework)?;
    if let Some(source) = build.sources.iter().find(|s| s.owner == VerusSourceOwnerV1::Agent && !s.path.starts_with("agent/")) {
        return Err(rejected(format!("engine build author file {} lies outside agent/", source.path)));
    }
    let constraints = build.sources.iter().find(|s| s.path == CONSTRAINTS_MODULE_PATH && s.owner == VerusSourceOwnerV1::Framework);
    if constraints.map(|s| s.blob) != Some(package.constraints) {
        return Err(rejected("engine_requires_declared_constraints: the engine build's gendb_constraints.rs is absent or not the package's declared constraints"));
    }
    check_toolkit(&build, &package.toolkit)?;
    for storage in resolve_engine_storages(store, &package.storage_uses)? {
        storage.check_declared_constraints(Some(package.constraints))?;
    }
    if !(1..=package.workers.1).contains(&package.workers.0) {
        return Err(rejected("engine package worker domain is empty"));
    }
    for id in &package.implementations {
        let implementation: VerusImplementationV1 = read_record(store, *id, VERUS_IMPLEMENTATION_KIND)?;
        if implementation.build != package.build {
            return Err(rejected("engine package implementation belongs to another build"));
        }
    }
    store.read_blob(package.schema_ddl, None)?;
    Ok(store.put(1, VERUS_ENGINE_PACKAGE_KIND, package)?)
}

/// The toolkit list is exactly the build's framework files under `engine_link/`, with their stored blobs.
fn check_toolkit(build: &VerusBuildV1, toolkit: &[VerusClosureFileV1]) -> Result<(), RecordError> {
    let carried: Vec<&super::build::VerusSourceFileV1> = build.sources.iter().filter(|s| s.path.starts_with(TOOLKIT_DIRECTORY)).collect();
    let same = carried.len() == toolkit.len()
        && toolkit.iter().all(|t| carried.iter().any(|s| s.owner == VerusSourceOwnerV1::Framework && s.path == t.path && s.blob == t.blob && s.bytes == t.bytes));
    if same { Ok(()) } else { Err(rejected("the engine package's toolkit list is not the build's engine_link/ framework files")) }
}

/// Admit a published engine package as the next version of the library's engine (append it to [`ENGINE_STREAM`]; in a
/// library without selection records this selects it). Rules: the library is an engine library (it holds no query
/// package admission); the package is not admitted yet; non-empty, readable evidence, with at most one lineage record
/// whose parents are admitted versions ([`VerusEngineLineageV1`]); for every storage use, an admitted storage package
/// of that name checked with the engine build's check configuration, every closure file carried by the engine build as
/// a framework file with the storage build's stored blob, and `composition` accepting it; every named asset is a
/// published asset of a used storage package. Returns `(admission id, version)`.
pub fn admit_engine_version(store: &ObjectStore, admission: &VerusEngineAdmissionV1, composition: CompositionRule<'_>) -> Result<(ContentId, u64), RecordError> {
    let package: VerusEnginePackageV1 = read_record(store, admission.package, VERUS_ENGINE_PACKAGE_KIND)?;
    let build = check_build_evidence(store, package.build)?;
    refuse_query_packages(store)?;
    let versions = engine_versions(store)?;
    if versions.iter().any(|v| v.package_id == admission.package) {
        return Err(rejected(format!("engine package {} is already admitted", admission.package)));
    }
    if admission.evidence.is_empty() {
        return Err(rejected("engine admission requires evidence"));
    }
    for id in &admission.evidence {
        store.read(*id)?;
    }
    if let Some(lineage) = lineage_of(store, &admission.evidence)? {
        check_lineage(&lineage, &versions)?;
    }
    let configuration = build.check_configuration()?;
    let storages = resolve_engine_storages(store, &package.storage_uses)?;
    for (storage_use, storage) in package.storage_uses.iter().zip(&storages) {
        check_storage_use(store, storage_use, storage, &build, &configuration, composition)?;
    }
    for id in &admission.assets {
        let asset: VerusStorageAssetV1 = read_record(store, *id, VERUS_STORAGE_ASSET_KIND)?;
        let published = resolve_storage_asset(store, &asset.key)?.map(|(published, _)| published);
        if published != Some(*id) || !package.storage_uses.iter().any(|u| u.package == asset.key.storage_package) {
            return Err(rejected("a named asset is not a published asset of a storage the engine reads"));
        }
    }
    let id = store.put(1, VERUS_ENGINE_ADMISSION_KIND, admission)?;
    append_record(store, ENGINE_STREAM, id)?;
    Ok((id, versions.len() as u64 + 1))
}

/// The lineage record among `evidence` (`None`: the admission states none); two lineage records are refused.
fn lineage_of(store: &ObjectStore, evidence: &[ContentId]) -> Result<Option<VerusEngineLineageV1>, RecordError> {
    let mut found = None;
    for id in evidence {
        let object = store.read(*id)?;
        if object.kind != VERUS_ENGINE_LINEAGE_KIND {
            continue;
        }
        if found.is_some() {
            return Err(rejected("engine admission evidence holds two lineage records"));
        }
        found = Some(read_record::<VerusEngineLineageV1>(store, *id, VERUS_ENGINE_LINEAGE_KIND)?);
    }
    Ok(found)
}

/// A lineage names a branch, a known kind with its number of parents, and only distinct admitted parent versions.
fn check_lineage(lineage: &VerusEngineLineageV1, versions: &[EngineVersion]) -> Result<(), RecordError> {
    let branch_ok = !lineage.branch.is_empty() && lineage.branch.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_' || b == b'-');
    if !branch_ok {
        return Err(rejected(format!("engine lineage branch {:?} is not a name", lineage.branch)));
    }
    let Some((_, least, most)) = LINEAGE_KINDS.iter().find(|(kind, _, _)| *kind == lineage.kind) else {
        return Err(rejected(format!("engine lineage kind {:?} is not one of framework_generated, branch, merge", lineage.kind)));
    };
    if !(*least..=*most).contains(&lineage.parents.len()) || lineage.parents.iter().collect::<BTreeSet<_>>().len() != lineage.parents.len() {
        return Err(rejected(format!("engine lineage of kind {} names {} parents (distinct, {least} to {most})", lineage.kind, lineage.parents.len())));
    }
    if let Some(unknown) = lineage.parents.iter().find(|parent| !versions.iter().any(|v| v.package_id == **parent)) {
        return Err(rejected(format!("engine lineage parent {unknown} is not an admitted engine version of this library")));
    }
    Ok(())
}

/// The lineage of an admitted version (`None`: admitted without one, as every schema-engine version).
pub fn engine_lineage(store: &ObjectStore, version: &EngineVersion) -> Result<Option<VerusEngineLineageV1>, RecordError> {
    lineage_of(store, &version.admission.evidence)
}

/// Record a change of the selected version (append `selection` to [`ENGINE_SELECTION_STREAM`]). Rules: the package is
/// an admitted version of this library and `admission` is its admission record; it is not the selected version already;
/// the reason is stated and every evidence record is readable. Returns `(selection record id, its 1-based position)`.
pub fn select_engine_version(store: &ObjectStore, selection: &VerusEngineSelectionV1) -> Result<(ContentId, u64), RecordError> {
    let versions = engine_versions(store)?;
    let Some(version) = versions.iter().find(|v| v.package_id == selection.package) else {
        return Err(rejected(format!("engine package {} is not an admitted version of this library", selection.package)));
    };
    if version.admission_id != selection.admission {
        return Err(rejected(format!("selection names admission {} of engine package {}, admitted as {}", selection.admission, selection.package, version.admission_id)));
    }
    if selection.reason.trim().is_empty() {
        return Err(rejected("a selection states its reason"));
    }
    for id in &selection.evidence {
        store.read(*id)?;
    }
    let selections = engine_selections(store)?;
    if selections.last().is_some_and(|(_, last)| last.package == selection.package) {
        return Err(rejected(format!("engine package {} is the selected version already", selection.package)));
    }
    let id = store.put(1, VERUS_ENGINE_SELECTION_KIND, selection)?;
    append_record(store, ENGINE_SELECTION_STREAM, id)?;
    Ok((id, selections.len() as u64 + 1))
}

/// Every selection record of the library, oldest first: `(record id, selection)` (empty: admission selects).
pub fn engine_selections(store: &ObjectStore) -> Result<Vec<(ContentId, VerusEngineSelectionV1)>, RecordError> {
    let mut selections = vec![];
    let mut next = lookup_record_head(store, ENGINE_SELECTION_STREAM)?;
    while let Some(record_id) = next {
        let record: AppendRecord = store.read(record_id)?.decode()?;
        selections.push((record.subject, read_record(store, record.subject, VERUS_ENGINE_SELECTION_KIND)?));
        next = record.previous;
    }
    selections.reverse();
    Ok(selections)
}

/// An engine library holds no query package: its serving set is decided by the selected engine version alone.
fn refuse_query_packages(store: &ObjectStore) -> Result<(), RecordError> {
    for kind in [VERUS_PACKAGE_ADMISSION_V2_KIND, VERUS_PACKAGE_ADMISSION_KIND, VERUS_QUERY_PACKAGE_V2_KIND] {
        if let Some(object) = store.list_kind(kind)?.first() {
            return Err(rejected(format!(
                "engine_library_holds_query_packages: this library holds {kind} record {}; an engine is admitted only into an engine library (seeded with storages, no query package)",
                object.id
            )));
        }
    }
    Ok(())
}

/// One use's composition: equal check configurations, every closure file carried by the engine build as a framework
/// file with the storage build's stored blob, then the full rule.
fn check_storage_use(
    store: &ObjectStore,
    storage_use: &VerusStorageUseV1,
    storage: &VerusStoragePackageV1,
    engine_build: &VerusBuildV1,
    engine_configuration: &VerusCheckConfigurationV1,
    composition: CompositionRule<'_>,
) -> Result<(), RecordError> {
    let name = &storage_use.name;
    if &storage.configuration != engine_configuration {
        return Err(rejected(format!("storage_spec_identity: storage {name} was checked with another toolchain or configuration than the engine build")));
    }
    for file in &storage.closure {
        let carried = engine_build.sources.iter().find(|s| s.path == file.path);
        if !carried.is_some_and(|s| s.owner == VerusSourceOwnerV1::Framework && s.blob == file.blob && s.bytes == file.bytes) {
            return Err(rejected(format!("storage_spec_identity: {} of storage {name} is missing from the engine build or differs", file.path)));
        }
    }
    let storage_build = storage_build(store, storage)?;
    composition(&StorageComposition { name, storage, storage_build: &storage_build, query_build: engine_build })
        .map_err(|reason| rejected(format!("storage_spec_identity: storage {name}: {reason}")))
}

/// The storage packages of `uses`, in order: at least one, distinct names, each an admitted package of that name.
fn resolve_engine_storages(store: &ObjectStore, uses: &[VerusStorageUseV1]) -> Result<Vec<VerusStoragePackageV1>, RecordError> {
    if uses.is_empty() {
        return Err(rejected("an engine reads at least one storage"));
    }
    if uses.iter().map(|u| u.name.as_str()).collect::<BTreeSet<_>>().len() != uses.len() {
        return Err(rejected("a storage is used twice"));
    }
    uses.iter()
        .map(|storage_use| {
            let package = resolve_admitted_storage(store, storage_use.package)?;
            if package.name != storage_use.name {
                return Err(rejected(format!("storage use {} names package {} of storage {}", storage_use.name, storage_use.package, package.name)));
            }
            Ok(package)
        })
        .collect()
}

/// One admitted engine version.
#[derive(Clone, Debug)]
pub struct EngineVersion {
    /// 1-based position on [`ENGINE_STREAM`] (`v1` is the first admitted version).
    pub version: u64,
    pub admission_id: ContentId,
    pub admission: VerusEngineAdmissionV1,
    pub package_id: ContentId,
    pub package: VerusEnginePackageV1,
}

/// Every admitted engine version of the library, oldest first (empty for a library without an engine).
pub fn engine_versions(store: &ObjectStore) -> Result<Vec<EngineVersion>, RecordError> {
    let mut versions = vec![];
    let mut next = lookup_record_head(store, ENGINE_STREAM)?;
    while let Some(record_id) = next {
        let record: AppendRecord = store.read(record_id)?.decode()?;
        let admission: VerusEngineAdmissionV1 = read_record(store, record.subject, VERUS_ENGINE_ADMISSION_KIND)?;
        let package = read_record(store, admission.package, VERUS_ENGINE_PACKAGE_KIND)?;
        versions.push(EngineVersion { version: record.sequence + 1, admission_id: record.subject, package_id: admission.package, admission, package });
        next = record.previous;
    }
    versions.reverse();
    Ok(versions)
}

/// The selected engine version (module documentation): the one the newest selection record names, else the newest
/// admitted one (`None` before the first admission).
pub fn selected_engine(store: &ObjectStore) -> Result<Option<EngineVersion>, RecordError> {
    let mut versions = engine_versions(store)?;
    match engine_selections(store)?.pop() {
        Some((_, selection)) => versions
            .into_iter()
            .find(|v| v.package_id == selection.package)
            .map(Some)
            .ok_or_else(|| rejected(format!("the selected engine package {} is not an admitted version", selection.package))),
        None => Ok(versions.pop()),
    }
}

/// An admitted engine version as serving uses it: its records, its build and the admitted storage package of every use
/// (in use order). Nothing is re-verified.
#[derive(Clone, Debug)]
pub struct ResolvedEngine {
    pub version: EngineVersion,
    /// Whether this is the selected version ([`selected_engine`]).
    pub selected: bool,
    pub build: VerusBuildV1,
    pub storages: Vec<VerusStoragePackageV1>,
}

/// The engine version to serve: the admitted version of package `package`, or the selected one (`None`). `Ok(None)`:
/// the library has no admitted engine version (or none of that package).
pub fn resolve_engine(store: &ObjectStore, package: Option<ContentId>) -> Result<Option<ResolvedEngine>, RecordError> {
    let selected = selected_engine(store)?.map(|v| v.package_id);
    let wanted = package.or(selected);
    let Some(version) = engine_versions(store)?.into_iter().find(|v| Some(v.package_id) == wanted) else {
        return Ok(None);
    };
    let build: VerusBuildV1 = read_record(store, version.package.build, VERUS_BUILD_KIND)?;
    let storages = resolve_engine_storages(store, &version.package.storage_uses)?;
    Ok(Some(ResolvedEngine { selected: Some(version.package_id) == selected, version, build, storages }))
}
