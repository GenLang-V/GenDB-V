//! ABI v3 query packages: statement keys, SQL claims, admission and serving lookup.
//!
//! The final SQL claim is proved inside the candidate crate by the fixed entry (`gendb-verus-entry-v3`), so a
//! package needs no separate link crate. A package is found by its statement key: the emitted meaning of the
//! statement instance, its free-parameter declaration and its output columns. Every allowed binding is served by
//! the same package, library and assets; a different fixed value, domain, schema or statement is a different key and
//! never a hit. Admitted packages are appended to `verus-statement.<statement id>`.

use super::build::{VerusBuildV1, VerusImplementationV1, VerusTcbV1, check_build_evidence};
use super::build::{VERUS_BUILD_KIND, VERUS_IMPLEMENTATION_KIND, VERUS_TCB_KIND};
use super::representation::{
    VERUS_ASSET_V2_KIND, VERUS_REPRESENTATION_V2_KIND, VerusAssetManifestV2, VerusRepresentationV2, resolve_asset_v2,
};
use super::{RecordError, check_entry_theorems, check_framework_files, current_subject, read_record, rejected};
use crate::append_only::append_record;
use crate::canonical_json::{CanonError, content_id, sha256};
use crate::content_id::ContentId;
use crate::object_store::ObjectStore;
use serde::{Deserialize, Serialize};

pub const VERUS_STATEMENT_KEY_KIND: &str = "gendb.verus.statement-key.v1";
pub const VERUS_SQL_CLAIM_KIND: &str = "gendb.verus.sql-claim.v1";
pub const VERUS_QUERY_PACKAGE_V2_KIND: &str = "gendb.verus.query-package.v2";
pub const VERUS_PACKAGE_ADMISSION_KIND: &str = "gendb.verus.package-admission.v1";
/// ABI version of every admitted package (the runtime's ABI v3).
pub const ADMITTED_ABI_V3_VERSION: u64 = 3;
/// Identity of the fixed entry a claim is stated with (the obligations generator's entry v3 identity).
pub const VERUS_ENTRY_V3_IDENTITY: &str = "gendb-verus-entry-v3";
/// Identity of the fixed query entry v4 over stored parts of admitted storages.
pub const VERUS_ENTRY_V4_IDENTITY: &str = "gendb-verus-entry-v4";
/// Identity of the fixed query entry v5: entry v4 with the declared integrity constraints as one more hypothesis, used
/// exactly by statements whose key v2 carries `constraints`.
pub const VERUS_ENTRY_V5_IDENTITY: &str = "gendb-verus-entry-v5";
/// Identity of the fixed storage entry (storage builds whose parts query entry v4 crates read).
pub const VERUS_STORAGE_ENTRY_V1_IDENTITY: &str = "gendb-verus-storage-entry-v1";
/// Identity of the fixed storage entry v2: storage entry v1 whose builder may also assume that its delivered source
/// comes from a full database satisfying the declared integrity constraints. Used exactly by storage packages that
/// record `assumed_constraints`.
pub const VERUS_STORAGE_ENTRY_V2_IDENTITY: &str = "gendb-verus-storage-entry-v2";
/// Identity of the fixed storage entry of a storage built from admitted storages
/// (`verification/obligations/storage_entry_derived.rs`).
pub const VERUS_STORAGE_ENTRY_DERIVED_IDENTITY: &str = "gendb-verus-storage-entry-derived-v1";
/// Record kind of [`VerusStatementKeyV2`].
pub const VERUS_STATEMENT_KEY_V2_KIND: &str = "gendb.verus.statement-key.v2";
/// Framework files every build must contain (compared byte-for-byte with the rest of the fresh generation).
pub const VERUS_V3_REQUIRED_FRAMEWORK: &[&str] =
    &["query.rs", "gendb_source.rs", "gendb_params.rs", "gendb_entry.rs", "gendb_entry/binder.rs", "gendb_abi.rs", "gendb_shim.rs"];
/// The theorem every claim must name.
const END_TO_END_THEOREM: &str = "gendb_entry::theorem_end_to_end";

/// One free parameter: `$index` is `ps[slot]` of `query_spec_at(ps)` and ABI argument `slot`; SQL type and inclusive
/// bounds as canonical texts of the declared type. A `text` parameter has no bounds (its domain is every text value
/// without a NUL byte); absent bounds are not serialized, so every key with bounds keeps its identity.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusFreeParamV1 {
    pub index: u32,
    pub slot: usize,
    pub sql_type: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub min: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max: Option<String>,
}

/// Lookup key of an admitted package. `meaning` is the emitted `query.rs` of the statement instance (fixed
/// parameters substituted) without its leading `//!` lines, which quote the SQL text: the schema, the statement
/// `query_spec_at`, `param_typed`/`param_domain` and their lemmas, exactly as the build verified them. Two requests
/// share a key only if they denote the same checked meaning over the same parameter domain with the same output
/// columns; a fully fixed template and the same SQL written with literals share it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusStatementKeyV1 {
    pub frontend_identity: String,
    pub meaning: String,
    pub free: Vec<VerusFreeParamV1>,
    /// Output columns: (name, PostgreSQL type) in order.
    pub output: Vec<(String, String)>,
}

impl VerusStatementKeyV1 {
    pub fn identity(&self) -> Result<ContentId, CanonError> {
        content_id(1, VERUS_STATEMENT_KEY_KIND, self)
    }

    pub fn stream(&self) -> Result<String, CanonError> {
        Ok(statement_stream(self.identity()?))
    }
}

/// Lookup key of a statement in the storage-aware layout (entry v4), where the column schema is its own generated
/// module (`schema.rs`) and `query.rs` imports `schema_spec` from it. The key holds both texts as separate fields, so
/// equal statement text over different schemas (tables, types, table ids) never shares a key; with the free parameters,
/// the output columns and the declared constraints it is exactly what the v1 key's `meaning` covers. A different kind,
/// so a v1 and a v2 key never share an identity or a stream.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusStatementKeyV2 {
    pub frontend_identity: String,
    /// The generated `schema.rs` text, complete (the column schema: no declared constraint).
    pub schema: String,
    /// The generated `query.rs` without its leading `//!` lines ([`statement_meaning`]).
    pub statement: String,
    pub free: Vec<VerusFreeParamV1>,
    /// Output columns: (name, PostgreSQL type) in order.
    pub output: Vec<(String, String)>,
    /// The generated `gendb_constraints.rs` text, complete, when the request declares integrity constraints (the
    /// statement's proof assumes them). Absent (and not serialized) without declarations, so every unconstrained key
    /// keeps its identity, and a constrained statement never shares a key with the unconstrained one or with another
    /// declaration list.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub constraints: Option<String>,
}

impl VerusStatementKeyV2 {
    pub fn identity(&self) -> Result<ContentId, CanonError> {
        content_id(1, VERUS_STATEMENT_KEY_V2_KIND, self)
    }

    /// The content identity of the `constraints` text: the blob identity `ObjectStore::put_blob` gives those bytes, and
    /// the `constraints_digest` every record of a constrained statement reports. `None` without declarations.
    pub fn constraints_digest(&self) -> Option<ContentId> {
        self.constraints.as_deref().map(declared_constraints_digest)
    }

    pub fn stream(&self) -> Result<String, CanonError> {
        Ok(statement_stream(self.identity()?))
    }
}

/// The content identity of a generated `gendb_constraints.rs` text: the blob identity `ObjectStore::put_blob` gives its
/// bytes. Statement keys report it as `constraints_digest`; storage packages record it as `assumed_constraints`.
pub fn declared_constraints_digest(text: &str) -> ContentId {
    sha256(text.as_bytes())
}

pub fn statement_stream(statement: ContentId) -> String {
    format!("verus-statement.{}", statement.to_hex())
}

/// The emitted meaning of a `query.rs` text: the text without its leading `//!` lines (the quoted SQL).
pub fn statement_meaning(query_rs: &str) -> String {
    let mut rest = query_rs;
    while rest.starts_with("//!") {
        rest = rest.split_once('\n').map_or("", |(_, tail)| tail);
    }
    rest.to_string()
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum VerusParamBindingV1 {
    Fixed { value: String },
    /// Inclusive bounds; absent (and not serialized) for a `text` parameter, as in [`VerusFreeParamV1`].
    Free {
        #[serde(default, skip_serializing_if = "Option::is_none")]
        min: Option<String>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        max: Option<String>,
    },
}

/// One placeholder of the request as declared (canonical texts).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusParamDeclV1 {
    pub index: u32,
    pub sql_type: String,
    pub binding: VerusParamBindingV1,
}

/// The checked SQL claim of a build: the final theorems of the fixed entry, proved by the build's single whole-crate
/// `--no-cheating` verification over the emitted statement (`query.rs`, whose meaning is the key's), the generated
/// source and parameter modules and the author's code. Reviewable inputs: SQL, frontend identity, schema DDL, the
/// full parameter declaration (fixed values and free domains) and the source declaration.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusSqlClaimV1 {
    pub statement: ContentId,
    pub entry_identity: String,
    pub build: ContentId,
    /// Theorem paths in the crate (`gendb_entry::theorem_end_to_end`, ...), each a `pub proof fn` of the build's
    /// stored `gendb_entry.rs`.
    pub theorems: Vec<String>,
    pub sql: String,
    pub frontend: serde_json::Value,
    pub schema_ddl: ContentId,
    pub parameters: Vec<VerusParamDeclV1>,
    /// The source declaration (tables, delivered columns, declared types) the binder and `gendb_source.rs` came from.
    pub source: serde_json::Value,
}

/// A query package: the statement key, its claim, the checked build and representation, ABI 3.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusQueryPackageV2 {
    pub statement: ContentId,
    pub claim: ContentId,
    pub entry_identity: String,
    pub build: ContentId,
    pub representation: ContentId,
    pub implementations: Vec<ContentId>,
    pub abi_version: u64,
    /// Inclusive worker-count domain of the checked theorem.
    pub workers: (u32, u32),
    pub tcb: ContentId,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VerusPackageAdmissionV1 {
    pub package: ContentId,
    pub gate_identity: String,
    /// Offline qualification evidence (exact reference checks, dispatch records).
    pub qualification_evidence: Vec<ContentId>,
    /// Published assets of the package's representation (`VerusAssetManifestV2`).
    pub assets: Vec<ContentId>,
}

/// Store a statement key; its identity is [`VerusStatementKeyV1::identity`].
pub fn publish_statement_key(store: &ObjectStore, key: &VerusStatementKeyV1) -> Result<ContentId, RecordError> {
    let id = store.put(1, VERUS_STATEMENT_KEY_KIND, key)?;
    if id != key.identity()? {
        return Err(rejected("stored statement key identity differs from its content identity"));
    }
    Ok(id)
}

/// Inputs of [`publish_claim`].
pub struct VerusSqlClaimInput<'a> {
    pub statement: ContentId,
    pub build: ContentId,
    pub theorems: Vec<String>,
    pub sql: String,
    pub frontend: serde_json::Value,
    pub schema_ddl: &'a str,
    pub parameters: Vec<VerusParamDeclV1>,
    pub source: serde_json::Value,
}

/// Store the SQL claim of a checked build: the build passes [`check_build_evidence`]; its stored `query.rs` has the
/// key's meaning; its stored `gendb_entry.rs` is the fixed entry [`VERUS_ENTRY_V3_IDENTITY`] and defines every named
/// theorem (`pub proof fn <name>(`), including `theorem_end_to_end`; the declaration's free parameters are the key's.
pub fn publish_claim(store: &ObjectStore, input: VerusSqlClaimInput<'_>) -> Result<ContentId, RecordError> {
    let key: VerusStatementKeyV1 = read_record(store, input.statement, VERUS_STATEMENT_KEY_KIND)?;
    let build = check_build_evidence(store, input.build)?;
    if statement_meaning(&build.framework_text(store, "query.rs")?) != key.meaning {
        return Err(rejected("the build's query.rs is not the statement key's meaning"));
    }
    check_entry_theorems(&build.framework_text(store, "gendb_entry.rs")?, VERUS_ENTRY_V3_IDENTITY, &input.theorems, END_TO_END_THEOREM)?;
    check_free_parameters(&input.parameters, &key.free)?;
    let claim = VerusSqlClaimV1 {
        statement: input.statement,
        entry_identity: VERUS_ENTRY_V3_IDENTITY.into(),
        build: input.build,
        theorems: input.theorems,
        sql: input.sql,
        frontend: input.frontend,
        schema_ddl: store.put_blob(input.schema_ddl.as_bytes())?,
        parameters: input.parameters,
        source: input.source,
    };
    Ok(store.put(1, VERUS_SQL_CLAIM_KIND, &claim)?)
}

/// The declaration's free parameters, in ascending placeholder order with dense slots, must be exactly the key's;
/// placeholder indices are distinct.
pub(super) fn check_free_parameters(parameters: &[VerusParamDeclV1], free: &[VerusFreeParamV1]) -> Result<(), RecordError> {
    let mut indices: Vec<u32> = parameters.iter().map(|p| p.index).collect();
    indices.sort_unstable();
    if indices.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err(rejected("a placeholder is declared twice"));
    }
    let mut declared_free: Vec<(u32, &str, &Option<String>, &Option<String>)> = parameters
        .iter()
        .filter_map(|p| match &p.binding {
            VerusParamBindingV1::Free { min, max } => Some((p.index, p.sql_type.as_str(), min, max)),
            VerusParamBindingV1::Fixed { .. } => None,
        })
        .collect();
    declared_free.sort_by_key(|(index, ..)| *index);
    let expected: Vec<VerusFreeParamV1> = declared_free
        .into_iter()
        .enumerate()
        .map(|(slot, (index, sql_type, min, max))| VerusFreeParamV1 {
            index,
            slot,
            sql_type: sql_type.into(),
            min: min.clone(),
            max: max.clone(),
        })
        .collect();
    if expected != free {
        return Err(rejected("the free parameters of the declaration differ from the statement key"));
    }
    Ok(())
}

/// Admit a package and append it to its statement's stream. Rules: ABI 3 and the fixed entry; the claim is a claim of
/// the same build and statement; the fresh generation `expected_framework` contains every
/// [`VERUS_V3_REQUIRED_FRAMEWORK`] file and its `query.rs` has the key's meaning (so a stale key for another fixed
/// value, domain or statement cannot be attached to this build); then [`check_package_parts`].
pub fn admit_package_v3(
    store: &ObjectStore,
    admission: &VerusPackageAdmissionV1,
    expected_framework: &[(&str, &str)],
) -> Result<ContentId, RecordError> {
    let package: VerusQueryPackageV2 = read_record(store, admission.package, VERUS_QUERY_PACKAGE_V2_KIND)?;
    if package.abi_version != ADMITTED_ABI_V3_VERSION || package.entry_identity != VERUS_ENTRY_V3_IDENTITY {
        return Err(rejected(format!(
            "package ABI v{} / entry {} is not the admitted v3 format",
            package.abi_version, package.entry_identity
        )));
    }
    let claim: VerusSqlClaimV1 = read_record(store, package.claim, VERUS_SQL_CLAIM_KIND)?;
    if claim.build != package.build || claim.statement != package.statement || claim.entry_identity != package.entry_identity {
        return Err(rejected("the package claim is not a claim of this build and statement"));
    }
    let key: VerusStatementKeyV1 = read_record(store, package.statement, VERUS_STATEMENT_KEY_KIND)?;
    if let Some(missing) = VERUS_V3_REQUIRED_FRAMEWORK.iter().find(|path| !expected_framework.iter().any(|(p, _)| p == *path)) {
        return Err(rejected(format!("the expected framework files lack {missing}")));
    }
    let fresh_query = expected_framework.iter().find(|(path, _)| *path == "query.rs").map(|(_, text)| *text).unwrap_or_default();
    if statement_meaning(fresh_query) != key.meaning {
        return Err(rejected("the statement key's meaning differs from the fresh generation's query.rs"));
    }
    check_package_parts(store, admission, &package, expected_framework)?;
    let id = store.put(1, VERUS_PACKAGE_ADMISSION_KIND, admission)?;
    append_record(store, &statement_stream(package.statement), id)?;
    Ok(id)
}

/// Rules on the parts of a package: build evidence ([`check_build_evidence`]); package and build name the same TCB
/// record; the build's framework files are exactly `expected_framework`, byte for byte; a non-empty worker domain
/// starting at 1; implementations of the same build; non-empty readable qualification evidence; a V2 representation
/// of the same build with at least one published asset of it.
fn check_package_parts(
    store: &ObjectStore,
    admission: &VerusPackageAdmissionV1,
    package: &VerusQueryPackageV2,
    expected_framework: &[(&str, &str)],
) -> Result<VerusBuildV1, RecordError> {
    let build = check_build_evidence(store, package.build)?;
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
    check_published_assets(store, admission, package)?;
    Ok(build)
}

fn check_published_assets(
    store: &ObjectStore,
    admission: &VerusPackageAdmissionV1,
    package: &VerusQueryPackageV2,
) -> Result<(), RecordError> {
    let representation: VerusRepresentationV2 =
        read_record(store, package.representation, VERUS_REPRESENTATION_V2_KIND).map_err(|error| {
            rejected(format!("package representation is not a V2 representation (old formats are not admitted): {error}"))
        })?;
    if representation.build != package.build {
        return Err(rejected("package representation belongs to another build"));
    }
    if admission.assets.is_empty() {
        return Err(rejected("package representation has no published asset"));
    }
    for id in &admission.assets {
        let manifest: VerusAssetManifestV2 = read_record(store, *id, VERUS_ASSET_V2_KIND)?;
        let published = resolve_asset_v2(store, &manifest.key)?.map(|(published, _)| published);
        if manifest.key.representation != package.representation || published != Some(*id) {
            return Err(rejected("package asset is not a published asset of its representation"));
        }
    }
    Ok(())
}

pub struct ResolvedVerusPackageV3 {
    pub admission_id: ContentId,
    pub admission: VerusPackageAdmissionV1,
    pub package: VerusQueryPackageV2,
    pub claim: VerusSqlClaimV1,
    pub key: VerusStatementKeyV1,
    pub build: VerusBuildV1,
}

/// The latest admitted package of a statement (serving lookup). The package, its claim and the stored key must all
/// name `statement`; nothing is re-verified.
pub fn resolve_package_v3(store: &ObjectStore, statement: ContentId) -> Result<Option<ResolvedVerusPackageV3>, RecordError> {
    let Some(admission_id) = current_subject(store, &statement_stream(statement))? else {
        return Ok(None);
    };
    let admission: VerusPackageAdmissionV1 = read_record(store, admission_id, VERUS_PACKAGE_ADMISSION_KIND)?;
    let package: VerusQueryPackageV2 = read_record(store, admission.package, VERUS_QUERY_PACKAGE_V2_KIND)?;
    let claim: VerusSqlClaimV1 = read_record(store, package.claim, VERUS_SQL_CLAIM_KIND)?;
    let key: VerusStatementKeyV1 = read_record(store, package.statement, VERUS_STATEMENT_KEY_KIND)?;
    if package.statement != statement || claim.statement != statement || key.identity()? != statement {
        return Err(rejected("the admitted package on this statement stream names another statement"));
    }
    let build: VerusBuildV1 = read_record(store, package.build, VERUS_BUILD_KIND)?;
    Ok(Some(ResolvedVerusPackageV3 { admission_id, admission, package, claim, key, build }))
}
