//! Library records of Verus-checked packages.
//!
//! * [`build`]: one Verus invocation that verified and compiled a frozen crate (sources, raw output, library, check
//!   configuration), the TCB record, and reusable implementation records;
//! * [`representation`] and [`package`]: the saved route (ABI 3, entry v3): representations with their assets keyed by
//!   source versions, statement keys v1, SQL claims, query packages, admission and serving lookup;
//! * [`storage`]: storage packages (storage entry v1, or v2 when the builder assumes the declared integrity
//!   constraints, with the exact-set rule), their admitted versions per name, and their stored assets in the library,
//!   keyed by per-table source version and row-order identity, and their release (the general engine line);
//! * [`query_v4`]: query packages over stored data (ABI 4, entry v4, or entry v5 for a key with declared integrity
//!   constraints): statement keys v2, claims v2, admission with the storage composition rule, serving lookup;
//! * [`engine`]: engine packages (engine entry v1: one verified engine for a whole schema), the append-only stream of an
//!   engine library's admitted versions and its selected version, and the seeding of an engine library with admitted
//!   storages ([`engine::seed`]).
//!
//! Records use the typed object store, its identities and append-only streams; no other identity or data-hashing
//! scheme exists. Admission decides from stored evidence (never from a flag) and serving resolves admitted records
//! without re-checking them. Record formats and kind strings are those of the saved libraries; saved ABI v1/v2
//! records (`VerusRepresentationV1`, `VerusQueryPackageV1`, SQL links, registered views) are read only
//! by the earlier GenDB version (not part of this repository).

pub mod build;
pub mod engine;
pub mod package;
pub mod query_v4;
pub mod representation;
pub mod storage;

pub use build::{
    VERUS_BUILD_KIND, VERUS_IMPLEMENTATION_KIND, VERUS_PARTIAL_OPTIONS, VERUS_TCB_KIND, VerusBuildInput,
    VerusBuildPurposeV1, VerusBuildV1, VerusCheckConfigurationV1, VerusImplementationV1, VerusItemV1, VerusSourceFileV1, VerusSourceOwnerV1,
    VerusTcbV1, VerusTrustedItemV1, check_build_evidence, library_path, publish_build,
};
pub use engine::{
    ENGINE_PACKAGE_ABI_VERSION, ENGINE_SELECTION_STREAM, ENGINE_STREAM, EngineVersion, ResolvedEngine, VERUS_ENGINE_ADMISSION_KIND,
    VERUS_ENGINE_ENTRY_V1_IDENTITY, VERUS_ENGINE_LINEAGE_KIND, VERUS_ENGINE_PACKAGE_KIND, VERUS_ENGINE_SELECTION_KIND, VerusEngineAdmissionV1,
    VerusEngineLineageV1, VerusEnginePackageV1, VerusEngineSelectionV1, admit_engine_version, engine_lineage, engine_selections, engine_versions,
    publish_engine_package, resolve_engine, select_engine_version, selected_engine,
};
pub use package::{
    ADMITTED_ABI_V3_VERSION, ResolvedVerusPackageV3, VERUS_ENTRY_V3_IDENTITY, VERUS_ENTRY_V4_IDENTITY, VERUS_ENTRY_V5_IDENTITY,
    VERUS_PACKAGE_ADMISSION_KIND, VERUS_QUERY_PACKAGE_V2_KIND, VERUS_SQL_CLAIM_KIND, VERUS_STATEMENT_KEY_KIND,
    VERUS_STATEMENT_KEY_V2_KIND, VERUS_STORAGE_ENTRY_DERIVED_IDENTITY, VERUS_STORAGE_ENTRY_V1_IDENTITY, VERUS_STORAGE_ENTRY_V2_IDENTITY, VERUS_V3_REQUIRED_FRAMEWORK, VerusFreeParamV1,
    VerusPackageAdmissionV1, VerusParamBindingV1, VerusParamDeclV1, VerusQueryPackageV2, VerusSqlClaimInput,
    VerusSqlClaimV1, VerusStatementKeyV1, VerusStatementKeyV2, admit_package_v3, declared_constraints_digest, publish_claim, publish_statement_key,
    resolve_package_v3, statement_meaning, statement_stream,
};
pub use query_v4::{
    ADMITTED_ABI_V4_VERSION, CompositionRule, ResolvedVerusPackageV4, StorageComposition, VERUS_PACKAGE_ADMISSION_V2_KIND,
    VERUS_QUERY_PACKAGE_V3_KIND, VERUS_SQL_CLAIM_V2_KIND, VerusPackageAdmissionV2, VerusQueryPackageV3, VerusSqlClaimV2,
    VerusSqlClaimV2Input, VerusStorageUseV1, admit_package_v4, publish_claim_v2, publish_statement_key_v2, query_entry_identity,
    resolve_package_v4,
};
pub use storage::{
    BuiltParts, VerusDerivationSourceV1, VerusDerivationV1, VERUS_STORAGE_ADMISSION_KIND, VERUS_STORAGE_ASSET_KIND, VERUS_STORAGE_ASSET_RELEASE_KIND,
    VERUS_STORAGE_PACKAGE_KIND, VerusClosureFileV1, ReleasedAsset, VerusStorageAssetReleaseV1,
    VerusStorageAdmissionV1, VerusStorageAssetKeyV1, VerusStorageAssetTableV1, VerusStorageAssetV1, VerusStoragePackageV1,
    VerusStoredTableV1, AdmittedStorage, StorageAssetLock, admit_storage_package, admitted_storages, current_storages, lock_storage_asset, locked_storage_asset, publish_storage_asset, publish_storage_package,
    publish_trial_storage_asset, release_storage_asset, released_storage_asset, storage_asset_id, storage_asset_record,
    resolve_admitted_storage, resolve_storage_asset, storage_asset_directory, storage_build, storage_entry_identity, storage_stream, storage_versions,
};
pub use representation::{
    CurrentSource, VERUS_ASSET_GATE, VERUS_ASSET_PROMOTION_KIND, VERUS_ASSET_V2_KIND, VERUS_REPRESENTATION_V2_KIND,
    VerusAssetKeyV2, VerusAssetManifestV2, VerusAssetPromotionV1, VerusAssetSourceV2, VerusRepresentationV2,
    VerusSourceTableV2, publish_asset_v2, publish_representation_v2, resolve_asset_v2,
};

use crate::append_only::{AppendOnlyError, AppendRecord, lookup_record_head};
use crate::canonical_json::CanonError;
use crate::content_id::ContentId;
use crate::object_store::{ObjectStore, StoreError};
use std::fmt;
use std::path::{Path, PathBuf};

/// Why a Verus record could not be stored, admitted or resolved. Display texts are the recorded refusal reasons.
#[derive(Debug)]
pub enum RecordError {
    Store(StoreError),
    AppendOnly(AppendOnlyError),
    Canonical(CanonError),
    /// Reading a frozen source or the compiled library failed.
    Io { path: PathBuf, message: String },
    /// The object is not a format-version-1 record of the expected kind.
    WrongKind { id: ContentId, expected: &'static str },
    /// The build's stored evidence is not one complete, successful whole-crate verification and compilation.
    BuildEvidence(String),
    /// The caller could not give a source table's current version or row count.
    CurrentSource(String),
    /// A record or its inputs break a publication or admission rule (the reason says which).
    Rejected(String),
}

impl RecordError {
    fn io(path: &Path, error: std::io::Error) -> Self {
        Self::Io { path: path.to_path_buf(), message: error.to_string() }
    }
}

impl From<StoreError> for RecordError {
    fn from(error: StoreError) -> Self {
        Self::Store(error)
    }
}

impl From<AppendOnlyError> for RecordError {
    fn from(error: AppendOnlyError) -> Self {
        Self::AppendOnly(error)
    }
}

impl From<CanonError> for RecordError {
    fn from(error: CanonError) -> Self {
        Self::Canonical(error)
    }
}

impl fmt::Display for RecordError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Store(error) => error.fmt(f),
            Self::AppendOnly(error) => error.fmt(f),
            Self::Canonical(error) => error.fmt(f),
            Self::Io { path, message } => write!(f, "{}: {message}", path.display()),
            Self::WrongKind { id, expected } => write!(f, "{id} is not a {expected} record"),
            Self::BuildEvidence(reason) | Self::CurrentSource(reason) | Self::Rejected(reason) => f.write_str(reason),
        }
    }
}

impl std::error::Error for RecordError {}

/// The generated module of the declared integrity constraints in query and storage crates (relative to `src/`).
pub const CONSTRAINTS_MODULE_PATH: &str = "gendb_constraints.rs";

fn rejected(reason: impl Into<String>) -> RecordError {
    RecordError::Rejected(reason.into())
}

/// Read and decode a format-version-1 record of `kind`.
fn read_record<T: serde::de::DeserializeOwned>(
    store: &ObjectStore,
    id: ContentId,
    kind: &'static str,
) -> Result<T, RecordError> {
    let object = store.read(id)?;
    if object.format_version != 1 || object.kind != kind {
        return Err(RecordError::WrongKind { id, expected: kind });
    }
    Ok(object.decode()?)
}

/// The subject of `stream`'s head record: the stream's current publication, if any.
fn current_subject(store: &ObjectStore, stream: &str) -> Result<Option<ContentId>, RecordError> {
    let Some(head) = lookup_record_head(store, stream)? else {
        return Ok(None);
    };
    let record: AppendRecord = store.read(head)?.decode()?;
    Ok(Some(record.subject))
}

/// The entry text is the fixed entry `identity`, names `required`, and defines every named `gendb_entry::` theorem.
fn check_entry_theorems(entry: &str, identity: &str, theorems: &[String], required: &str) -> Result<(), RecordError> {
    if !entry.contains(identity) {
        return Err(rejected(format!("the build's gendb_entry.rs is not the fixed entry {identity}")));
    }
    if !theorems.iter().any(|t| t == required) {
        return Err(rejected(format!("a claim names {required}")));
    }
    for theorem in theorems {
        let name = theorem.strip_prefix("gendb_entry::").ok_or_else(|| rejected(format!("theorem {theorem} is not a gendb_entry item")))?;
        if name.is_empty() || name.contains("::") || !entry.contains(&format!("pub proof fn {name}(")) {
            return Err(rejected(format!("the build's gendb_entry.rs does not define theorem {theorem}")));
        }
    }
    Ok(())
}

/// The build's framework files are exactly `expected_framework`, byte for byte (the same count, every path equal).
fn check_framework_files(store: &ObjectStore, build: &VerusBuildV1, expected_framework: &[(&str, &str)]) -> Result<(), RecordError> {
    let framework_count = build.sources.iter().filter(|s| s.owner == VerusSourceOwnerV1::Framework).count();
    if framework_count != expected_framework.len() {
        return Err(rejected("build framework file set differs from the expected framework files"));
    }
    for (path, text) in expected_framework {
        if build.framework_bytes(store, path)? != text.as_bytes() {
            return Err(rejected(format!("frozen framework file {path} differs from the framework generation")));
        }
    }
    Ok(())
}
