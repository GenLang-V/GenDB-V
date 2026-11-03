//! Query packages over stored data (fixed query entry v4, ABI 4): statement keys v2, SQL claims v2, packages v3,
//! their admission and serving lookup.
//!
//! A package is found by its [`VerusStatementKeyV2`] (the generated schema and statement texts as separate fields,
//! free parameters, output columns, and the generated `gendb_constraints.rs` when the request declares integrity
//! constraints); keys v1 and v2 are different kinds, so they never share an identity or a stream. A key with
//! `constraints` is proved with the fixed query entry v5 (entry v4 plus the declared constraints as hypothesis) and its
//! build carries that module byte for byte; a key without is proved with entry v4 and its build carries no such module
//! ([`query_entry_identity`]). The declarations are part of the key, so a constrained package is only on its own
//! statement stream and is never found by a request with another (or no) declaration list.
//! It pins the exact admitted storage packages it reads (`storage_uses`, in the order of the entry's `uses`). Admission
//! requires, for every use, that the query build carries the storage build's dependency closure with the same check
//! configuration: [`admit_package_v4`] compares configurations and closure blobs on the records and runs the caller's
//! full composition rule (`gendb_verification::obligations::check_storage_composition`) over both builds' stored
//! sources. Admitted packages are appended to `verus-statement.<key v2 id>`; the head is the served version.

use super::build::{VERUS_BUILD_KIND, VERUS_IMPLEMENTATION_KIND, VERUS_TCB_KIND};
use super::build::{VerusBuildV1, VerusImplementationV1, VerusSourceOwnerV1, VerusTcbV1, check_build_evidence};
use super::package::{
    VERUS_ENTRY_V4_IDENTITY, VERUS_ENTRY_V5_IDENTITY, VERUS_STATEMENT_KEY_V2_KIND, VerusParamDeclV1, VerusStatementKeyV2, check_free_parameters,
    statement_meaning, statement_stream,
};
use super::storage::{
    VERUS_STORAGE_ASSET_KIND, VerusStorageAssetV1, VerusStoragePackageV1, resolve_admitted_storage, resolve_storage_asset,
    storage_build,
};
use super::{CONSTRAINTS_MODULE_PATH, RecordError, check_entry_theorems, check_framework_files, current_subject, read_record, rejected};
use crate::append_only::append_record;
use crate::content_id::ContentId;
use crate::object_store::ObjectStore;
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

pub const VERUS_SQL_CLAIM_V2_KIND: &str = "gendb.verus.sql-claim.v2";
pub const VERUS_QUERY_PACKAGE_V3_KIND: &str = "gendb.verus.query-package.v3";
pub const VERUS_PACKAGE_ADMISSION_V2_KIND: &str = "gendb.verus.package-admission.v2";
/// ABI version of every package of the query entry v4.
pub const ADMITTED_ABI_V4_VERSION: u64 = 4;
/// The theorem every v4 claim must name.
const END_TO_END_THEOREM: &str = "gendb_entry::theorem_end_to_end";

/// The fixed query entry a statement key v2 is proved with: entry v5 exactly when the key carries declared integrity
/// constraints, entry v4 otherwise.
pub fn query_entry_identity(key: &VerusStatementKeyV2) -> &'static str {
    if key.constraints.is_some() { VERUS_ENTRY_V5_IDENTITY } else { VERUS_ENTRY_V4_IDENTITY }
}

/// One storage a query package reads: the storage's name (its module and `Stores` field) and the exact admitted
/// storage package.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusStorageUseV1 {
    pub name: String,
    pub package: ContentId,
}

/// The checked SQL claim of a query build over stored data: the final theorems of the fixed entry v4 (v5 under declared
/// integrity constraints), proved by the build's one whole-crate `--no-cheating` verification over the generated schema
/// and statement (the key's texts), the parameter module, the copied storage interfaces and the author's code. The
/// theorems hold for every database of the schema whose stored relations the stored parts of every use represent (under
/// v5 also satisfying the declared constraints); each use's storage package proves that for the database its source
/// columns come from. The theorems state what each outcome means (partial correctness); termination, the other part of
/// the claim, is checked by Verus on the same crate and is no theorem, so this record does not name it
/// (`gendb_verification::obligations::PROVED_PROPERTIES`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusSqlClaimV2 {
    pub statement: ContentId,
    pub entry_identity: String,
    pub build: ContentId,
    pub theorems: Vec<String>,
    pub sql: String,
    pub frontend: serde_json::Value,
    pub schema_ddl: ContentId,
    pub parameters: Vec<VerusParamDeclV1>,
    /// The statement's column demand (declared source, reviewable; the storages cover it).
    pub demand: serde_json::Value,
    pub storage_uses: Vec<VerusStorageUseV1>,
}

/// A query package over stored data: the statement key v2, its claim, the checked build, the storages it reads, ABI 4.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusQueryPackageV3 {
    pub statement: ContentId,
    pub claim: ContentId,
    pub entry_identity: String,
    pub build: ContentId,
    pub storage_uses: Vec<VerusStorageUseV1>,
    pub implementations: Vec<ContentId>,
    pub abi_version: u64,
    /// Inclusive worker-count domain of the checked theorem.
    pub workers: (u32, u32),
    pub tcb: ContentId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusPackageAdmissionV2 {
    pub package: ContentId,
    pub gate_identity: String,
    /// Offline qualification evidence (exact reference checks, request and dispatch records).
    pub qualification_evidence: Vec<ContentId>,
    /// The stored assets the qualification ran over (descriptive; serving resolves assets for the current capture).
    pub assets: Vec<ContentId>,
}

/// Store a statement key v2; its identity is [`VerusStatementKeyV2::identity`].
pub fn publish_statement_key_v2(store: &ObjectStore, key: &VerusStatementKeyV2) -> Result<ContentId, RecordError> {
    let id = store.put(1, VERUS_STATEMENT_KEY_V2_KIND, key)?;
    if id != key.identity()? {
        return Err(rejected("stored statement key identity differs from its content identity"));
    }
    Ok(id)
}

/// Inputs of [`publish_claim_v2`].
pub struct VerusSqlClaimV2Input<'a> {
    pub statement: ContentId,
    pub build: ContentId,
    pub theorems: Vec<String>,
    pub sql: String,
    pub frontend: serde_json::Value,
    pub schema_ddl: &'a str,
    pub parameters: Vec<VerusParamDeclV1>,
    pub demand: serde_json::Value,
    pub storage_uses: Vec<VerusStorageUseV1>,
}

/// Store the SQL claim of a checked query build: the build passes [`check_build_evidence`]; its stored `schema.rs` is
/// the key's schema, its `query.rs` has the key's statement meaning and its `gendb_constraints.rs` is the key's
/// constraints module (absent exactly when the key has none); its `gendb_entry.rs` is the key's fixed entry
/// ([`query_entry_identity`]) and defines every named theorem, including `theorem_end_to_end`; the declaration's free
/// parameters are the key's; the storage uses are distinct admitted storage packages.
pub fn publish_claim_v2(store: &ObjectStore, input: VerusSqlClaimV2Input<'_>) -> Result<ContentId, RecordError> {
    let key: VerusStatementKeyV2 = read_record(store, input.statement, VERUS_STATEMENT_KEY_V2_KIND)?;
    let build = check_build_evidence(store, input.build)?;
    let entry_identity = query_entry_identity(&key);
    let constraints = build_constraints_text(store, &build)?;
    check_statement_texts(&key, &build.framework_text(store, "schema.rs")?, &build.framework_text(store, "query.rs")?, constraints.as_deref())?;
    check_entry_theorems(&build.framework_text(store, "gendb_entry.rs")?, entry_identity, &input.theorems, END_TO_END_THEOREM)?;
    check_free_parameters(&input.parameters, &key.free)?;
    resolve_storage_uses(store, &input.storage_uses)?;
    let claim = VerusSqlClaimV2 {
        statement: input.statement,
        entry_identity: entry_identity.into(),
        build: input.build,
        theorems: input.theorems,
        sql: input.sql,
        frontend: input.frontend,
        schema_ddl: store.put_blob(input.schema_ddl.as_bytes())?,
        parameters: input.parameters,
        demand: input.demand,
        storage_uses: input.storage_uses,
    };
    Ok(store.put(1, VERUS_SQL_CLAIM_V2_KIND, &claim)?)
}

/// One storage use of a query build under admission: the storage package, its build and the query build.
pub struct StorageComposition<'a> {
    pub name: &'a str,
    pub storage: &'a VerusStoragePackageV1,
    pub storage_build: &'a VerusBuildV1,
    pub query_build: &'a VerusBuildV1,
}

/// The full composition rule of one storage use (for example `check_storage_composition` over both builds' stored
/// sources): `Err` names why the query build may not use the storage build.
pub type CompositionRule<'a> = &'a dyn Fn(&StorageComposition<'_>) -> Result<(), String>;

/// Admit a query package over stored data and append it to its statement's stream. Rules:
/// - ABI 4 and the key's fixed entry ([`query_entry_identity`]: v5 exactly when the key declares constraints, else
///   v4), whose text the build's `gendb_entry.rs` is and which defines the claim's theorems; the claim is a claim of
///   the same build, statement and storage uses;
/// - the fresh generation `expected_framework` (from a fresh translation, with the storages' interface texts taken from
///   their stored closures) has `schema.rs`/`query.rs` of the key's texts and `gendb_constraints.rs` exactly when the
///   key has constraints, with the key's text, and the build's framework files are exactly it, byte for byte; build
///   evidence, TCB, a worker domain starting at 1, implementations of the same build, non-empty readable
///   qualification evidence;
/// - every use: an admitted storage package of that name whose assumed declared constraints, if any, are exactly the
///   key's (`storage_assumes_declared_constraints`: a key without declarations never reads a storage of the storage
///   entry v2), with the query build's check configuration, every closure file present in the query build as a
///   framework file with the same stored blob, and `composition` accepting it;
/// - every named asset is a published asset of one of the used packages.
pub fn admit_package_v4(
    store: &ObjectStore,
    admission: &VerusPackageAdmissionV2,
    expected_framework: &[(&str, &str)],
    composition: CompositionRule<'_>,
) -> Result<ContentId, RecordError> {
    let package: VerusQueryPackageV3 = read_record(store, admission.package, VERUS_QUERY_PACKAGE_V3_KIND)?;
    let key: VerusStatementKeyV2 = read_record(store, package.statement, VERUS_STATEMENT_KEY_V2_KIND)?;
    let entry_identity = query_entry_identity(&key);
    if package.abi_version != ADMITTED_ABI_V4_VERSION || package.entry_identity != entry_identity {
        return Err(rejected(format!(
            "package ABI v{} / entry {} is not the admitted format of its statement key (ABI {ADMITTED_ABI_V4_VERSION}, entry {entry_identity})",
            package.abi_version, package.entry_identity
        )));
    }
    let claim: VerusSqlClaimV2 = read_record(store, package.claim, VERUS_SQL_CLAIM_V2_KIND)?;
    let same_claim = claim.build == package.build
        && claim.statement == package.statement
        && claim.entry_identity == package.entry_identity
        && claim.storage_uses == package.storage_uses;
    if !same_claim {
        return Err(rejected("the package claim is not a claim of this build, statement and storage uses"));
    }
    let fresh = |path: &str| expected_framework.iter().find(|(p, _)| *p == path).map(|(_, text)| *text);
    let (Some(schema), Some(query)) = (fresh("schema.rs"), fresh("query.rs")) else {
        return Err(rejected("the expected framework files lack schema.rs or query.rs"));
    };
    check_statement_texts(&key, schema, query, fresh(CONSTRAINTS_MODULE_PATH))?;
    let build = check_build_evidence(store, package.build)?;
    check_entry_theorems(&build.framework_text(store, "gendb_entry.rs")?, entry_identity, &claim.theorems, END_TO_END_THEOREM)?;
    read_record::<VerusTcbV1>(store, package.tcb, VERUS_TCB_KIND)?;
    if build.tcb != package.tcb {
        return Err(rejected("package and build TCB records differ"));
    }
    check_framework_files(store, &build, expected_framework)?;
    if !(1..=package.workers.1).contains(&package.workers.0) {
        return Err(rejected("package worker domain is empty"));
    }
    for id in &package.implementations {
        let implementation: VerusImplementationV1 = read_record(store, *id, VERUS_IMPLEMENTATION_KIND)?;
        if implementation.build != package.build {
            return Err(rejected("package implementation belongs to another build"));
        }
    }
    if admission.qualification_evidence.is_empty() {
        return Err(rejected("package admission requires qualification evidence"));
    }
    for id in &admission.qualification_evidence {
        store.read(*id)?;
    }
    let storages = resolve_storage_uses(store, &package.storage_uses)?;
    let configuration = build.check_configuration()?;
    for (storage_use, storage) in package.storage_uses.iter().zip(&storages) {
        storage.check_declared_constraints(key.constraints_digest())?;
        check_storage_use(store, storage_use, storage, &build, &configuration, composition)?;
    }
    for id in &admission.assets {
        let asset: VerusStorageAssetV1 = read_record(store, *id, VERUS_STORAGE_ASSET_KIND)?;
        let published = resolve_storage_asset(store, &asset.key)?.map(|(published, _)| published);
        if published != Some(*id) || !package.storage_uses.iter().any(|u| u.package == asset.key.storage_package) {
            return Err(rejected("a named asset is not a published asset of a storage the package reads"));
        }
    }
    let id = store.put(1, VERUS_PACKAGE_ADMISSION_V2_KIND, admission)?;
    append_record(store, &statement_stream(package.statement), id)?;
    Ok(id)
}

/// The schema text is the key's, the statement text has the key's meaning, and the constraints module is the key's:
/// present with the key's text exactly when the key declares constraints.
fn check_statement_texts(key: &VerusStatementKeyV2, schema: &str, query: &str, constraints: Option<&str>) -> Result<(), RecordError> {
    if schema != key.schema {
        return Err(rejected("schema.rs is not the statement key's schema"));
    }
    if statement_meaning(query) != key.statement {
        return Err(rejected("query.rs is not the statement key's statement meaning"));
    }
    if constraints != key.constraints.as_deref() {
        return Err(rejected(match (constraints, &key.constraints) {
            (None, Some(_)) => "declared_constraints_missing: the statement key declares integrity constraints but the crate has no gendb_constraints.rs",
            (Some(_), None) => "declared_constraints_unexpected: the crate has gendb_constraints.rs but the statement key declares no integrity constraints",
            _ => "gendb_constraints.rs is not the statement key's declared constraints",
        }));
    }
    Ok(())
}

/// The build's framework `gendb_constraints.rs`, `None` when the build carries no file of that path.
fn build_constraints_text(store: &ObjectStore, build: &VerusBuildV1) -> Result<Option<String>, RecordError> {
    if build.sources.iter().any(|s| s.path == CONSTRAINTS_MODULE_PATH) { Ok(Some(build.framework_text(store, CONSTRAINTS_MODULE_PATH)?)) } else { Ok(None) }
}

/// The storage packages of `uses`, in order: distinct names, each an admitted package of that name.
fn resolve_storage_uses(store: &ObjectStore, uses: &[VerusStorageUseV1]) -> Result<Vec<VerusStoragePackageV1>, RecordError> {
    if uses.is_empty() {
        return Err(rejected("a query package reads at least one storage"));
    }
    let names: BTreeSet<&str> = uses.iter().map(|u| u.name.as_str()).collect();
    if names.len() != uses.len() {
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

/// One use's composition: equal check configurations, every closure file carried by the query build as a framework
/// file with the storage build's stored blob, then the full rule.
fn check_storage_use(
    store: &ObjectStore,
    storage_use: &VerusStorageUseV1,
    storage: &VerusStoragePackageV1,
    query_build: &VerusBuildV1,
    query_configuration: &super::build::VerusCheckConfigurationV1,
    composition: CompositionRule<'_>,
) -> Result<(), RecordError> {
    if &storage.configuration != query_configuration {
        return Err(rejected(format!(
            "storage_spec_identity: storage {} was checked with another toolchain or configuration than the query build",
            storage_use.name
        )));
    }
    for file in &storage.closure {
        let carried = query_build.sources.iter().find(|s| s.path == file.path);
        if !carried.is_some_and(|s| s.owner == VerusSourceOwnerV1::Framework && s.blob == file.blob && s.bytes == file.bytes) {
            return Err(rejected(format!(
                "storage_spec_identity: {} of storage {} is missing from the query build or differs",
                file.path, storage_use.name
            )));
        }
    }
    let storage_build = storage_build(store, storage)?;
    composition(&StorageComposition { name: &storage_use.name, storage, storage_build: &storage_build, query_build })
        .map_err(|reason| rejected(format!("storage_spec_identity: storage {}: {reason}", storage_use.name)))
}

/// An admitted query package over stored data, as serving uses it.
pub struct ResolvedVerusPackageV4 {
    pub admission_id: ContentId,
    pub admission: VerusPackageAdmissionV2,
    pub package: VerusQueryPackageV3,
    pub claim: VerusSqlClaimV2,
    pub key: VerusStatementKeyV2,
    pub build: VerusBuildV1,
    /// The admitted storage package of every use, in use order.
    pub storages: Vec<VerusStoragePackageV1>,
}

/// The latest admitted v4 package of a statement key v2 (serving lookup). The package, its claim and the stored key
/// must all name `statement`; nothing is re-verified.
pub fn resolve_package_v4(store: &ObjectStore, statement: ContentId) -> Result<Option<ResolvedVerusPackageV4>, RecordError> {
    let Some(admission_id) = current_subject(store, &statement_stream(statement))? else {
        return Ok(None);
    };
    let admission: VerusPackageAdmissionV2 = read_record(store, admission_id, VERUS_PACKAGE_ADMISSION_V2_KIND)?;
    let package: VerusQueryPackageV3 = read_record(store, admission.package, VERUS_QUERY_PACKAGE_V3_KIND)?;
    let claim: VerusSqlClaimV2 = read_record(store, package.claim, VERUS_SQL_CLAIM_V2_KIND)?;
    let key: VerusStatementKeyV2 = read_record(store, package.statement, VERUS_STATEMENT_KEY_V2_KIND)?;
    if package.statement != statement || claim.statement != statement || key.identity()? != statement {
        return Err(rejected("the admitted package on this statement stream names another statement"));
    }
    let build: VerusBuildV1 = read_record(store, package.build, VERUS_BUILD_KIND)?;
    let storages = resolve_storage_uses(store, &package.storage_uses)?;
    Ok(Some(ResolvedVerusPackageV4 { admission_id, admission, package, claim, key, build, storages }))
}
