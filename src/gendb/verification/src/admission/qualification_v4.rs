//! Qualification of a query crate over stored data (fixed query entry v4, ABI 4): library records and admission.
//! A statement translated with declared integrity constraints is qualified the same way with the query entry v5
//! (`obligations::query_entry`): its TCB adds `declared_integrity_constraints`, and the fresh translation repeats the
//! request's declarations, so the key, the generated `gendb_constraints.rs` and the entry are compared too.
//!
//! In order: the TCB record; the build record of the candidate's one whole-crate verify-and-compile run (admissible
//! evidence; author files only under `agent/`); the implementation records (the fixed entry and each author module);
//! then a fresh translation of the SQL must reproduce the statement key v2, and its fresh generation of the query
//! crate (`query_crate_files`, with every storage's interface text taken from the storage package's stored closure,
//! and the v4 query shim) is what admission compares byte for byte with the build's framework files; finally the
//! statement key v2, the SQL claim v2, the package v3 and its admission. Admission runs the storage composition rule
//! (`obligations::check_storage_composition`: closure identity and implementation ownership) over both builds'
//! stored sources for every storage use, after comparing their check configurations and closure blobs. Every author
//! file of the query build and of every storage build is scanned again with the central refusal list
//! (`verus::scan_source`) from the stored records.

use super::qualification::{ClauseText, CandidateModule, entry_assumptions, framework_trusted_items, publish_checked_build, record_error, store_error};
use super::records::now_unix_ms;
use super::statement::{Statement, prepare_statement};
use super::storage::{build_files, crate_sources, refuse_unscanned_author_sources, v4_host_items, FLAT_CAPTURE_ASSET_KIND, FLAT_CAPTURE_PARTS};
use super::{AdmissionError, Refused};
use crate::obligations::{
    check_storage_composition, query_crate_files, query_entry, with_trusted_shim, DeclaredSource, QueryEntry, StorageName, StorageUse,
    CANDIDATE_CRATE_NAME, QUERY_ENTRY_V5, QUERY_THEOREMS,
};
use crate::verus::{FrameworkSource, VerusToolchain, VERUS_REFUSAL_RULES};
use gendb_artifacts::verus::{
    self as records, StorageComposition, VerusImplementationV1, VerusItemV1, VerusPackageAdmissionV2, VerusQueryPackageV3,
    VerusSqlClaimV2Input, VerusStoragePackageV1, VerusStorageUseV1, VerusTcbV1, ADMITTED_ABI_V4_VERSION,
};
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_frontend::parser::SqlParser;
use gendb_runtime::abi::{GENDB_QUERY_SHIM_V4_SOURCE, MAX_WORKERS};
use gendb_runtime::serve::{DECLARED_CONSTRAINTS_LOOKUP, TRUSTED_ITEMS_V4 as SERVING_TRUSTED_ITEMS_V4, parameter_declaration};
use gendb_storage::import::DatasetSpec;
use serde::Serialize;
use serde_json::{Value, json};
use std::path::Path;

/// Gate identity of every v4 package admission written here.
pub const GATE_IDENTITY_V4: &str = "gendb.verus.integrated-qualification.v4";
/// Entry items recorded with their `requires`/`ensures` text in the entry's implementation record.
const RECORDED_ENTRY_ITEMS: [&str; 3] = ["abi_query", "theorem_end_to_end", "corollary_inside_capacity"];

/// Where a query over stored data is qualified: the library, the statement, the dataset it was translated against
/// (for the fresh translation), the frontend and the caller's lexical clause extractor.
pub struct QueryV4Context<'a> {
    pub library: &'a Path,
    pub statement: &'a Statement,
    pub dataset: &'a DatasetSpec,
    pub parser: &'a SqlParser,
    pub clause_text: ClauseText<'a>,
}

/// One evaluated query crate over stored data.
pub struct QueryV4Candidate<'a> {
    /// The frozen crate (`<root>/src/`) its one whole-crate verify-and-compile run checked.
    pub frozen_root: &'a Path,
    /// The run record (`VerusRun::record`).
    pub verus_run: &'a Value,
    /// The storages it reads, in the order of the entry's `uses` (the order its crate was assembled with).
    pub storage_uses: Vec<VerusStorageUseV1>,
    pub modules: Vec<CandidateModule>,
    /// The evaluation record (stored as qualification evidence).
    pub evaluation: &'a Value,
    /// The stored assets the evaluation ran over.
    pub assets: Vec<ContentId>,
}

/// Every record id of an admitted v4 package.
#[derive(Clone, Debug, Serialize)]
pub struct QualificationV4 {
    pub admission: ContentId,
    pub package: ContentId,
    pub statement: ContentId,
    pub claim: ContentId,
    pub build: ContentId,
    pub tcb: ContentId,
    pub implementations: Vec<ContentId>,
    pub storage_uses: Vec<VerusStorageUseV1>,
    pub assets: Vec<ContentId>,
    pub qualification_evidence: ContentId,
    pub statement_key: String,
    /// The fixed entry the package was proved with (v4, or v5 under declared constraints).
    #[serde(skip)]
    pub entry: QueryEntry,
}

impl QualificationV4 {
    pub fn record(&self) -> Value {
        json!({"qualified":true,"kind":"verus","abi_version":ADMITTED_ABI_V4_VERSION,"entry_identity":self.entry.identity,
            "admission":self.admission,"package":self.package,"statement":self.statement,"claim":self.claim,"build":self.build,
            "tcb":self.tcb,"implementations":self.implementations,"storage_uses":self.storage_uses,"assets":self.assets,
            "qualification_evidence":self.qualification_evidence,"statement_key":self.statement_key,
            "proof_link":format!("the build record stores the frozen sources, the raw Verus JSON (0 errors, entire crate, including gendb_entry::theorem_end_to_end of the {} over the actual entry, the copied storage interfaces and the agent code) and the library compiled by that same invocation; admission compared every framework file byte for byte with a fresh generation from a fresh translation of the SQL, with each storage's interface taken from its admitted storage package, and checked for every storage use the same check configuration, the storage's dependency closure byte for byte and implementation ownership", self.entry.name)})
    }
}

/// Publish every record of an evaluated query crate over stored data and admit its package.
pub fn qualify_v4(context: &QueryV4Context<'_>, candidate: QueryV4Candidate<'_>) -> Result<QualificationV4, AdmissionError> {
    let statement = context.statement;
    let entry = query_entry(&statement.instance);
    let store = ObjectStore::open(context.library).map_err(store_error)?;
    let storages = candidate
        .storage_uses
        .iter()
        .map(|u| records::resolve_admitted_storage(&store, u.package).map_err(record_error))
        .collect::<Result<Vec<_>, _>>()?;
    let toolchain = VerusToolchain::from_env().map_err(AdmissionError::tool)?;
    let tcb = store.put(1, records::VERUS_TCB_KIND, &query_v4_tcb_record(entry, reads_flat_assets(&store, &candidate.assets)?)?).map_err(store_error)?;
    let sources = crate_sources(candidate.frozen_root, &|path| path.starts_with("agent/"))?;
    let build = publish_checked_build(&store, &toolchain, tcb, candidate.frozen_root, sources, candidate.verus_run)?;
    let build_record = store.read(build).and_then(|o| o.decode()).map_err(store_error)?;
    refuse_unscanned_author_sources(&store, &build_record)?;
    for storage in &storages {
        refuse_unscanned_author_sources(&store, &records::storage_build(&store, storage).map_err(record_error)?)?;
    }
    let implementations = publish_implementations(&store, build, context, entry, &candidate.modules)?;
    let fresh = fresh_framework(context, &store, &candidate.storage_uses, &storages)?;
    let statement_id = records::publish_statement_key_v2(&store, &statement.key_v4).map_err(record_error)?;
    let claim = records::publish_claim_v2(&store, VerusSqlClaimV2Input {
        statement: statement_id,
        build,
        theorems: QUERY_THEOREMS.iter().map(|t| t.to_string()).collect(),
        sql: statement.sql.clone(),
        frontend: statement.instance.doc.frontend.clone(),
        schema_ddl: &statement.schema_ddl,
        parameters: parameter_declaration(&statement.declarations),
        demand: serde_json::to_value(DeclaredSource::of_statement(&statement.instance.doc, &statement.source).map_err(AdmissionError::tool)?)
            .map_err(AdmissionError::tool)?,
        storage_uses: candidate.storage_uses.clone(),
    })
    .map_err(record_error)?;
    let package = store
        .put(1, records::VERUS_QUERY_PACKAGE_V3_KIND, &VerusQueryPackageV3 {
            statement: statement_id,
            claim,
            entry_identity: entry.identity.into(),
            build,
            storage_uses: candidate.storage_uses.clone(),
            implementations: implementations.clone(),
            abi_version: ADMITTED_ABI_V4_VERSION,
            workers: (1, MAX_WORKERS as u32),
            tcb,
        })
        .map_err(store_error)?;
    let evaluation = candidate.evaluation;
    let qualification_evidence = store
        .put(1, "gendb.verus.qualification-evidence.v2", &json!({"evaluation":evaluation,"assets":candidate.assets,
            "statement":statement.directory.join("statement.json")}))
        .map_err(store_error)?;
    let expected: Vec<(&str, &str)> = fresh.iter().map(|f| (f.path.as_str(), f.text.as_str())).collect();
    let composition = |use_: &StorageComposition<'_>| -> Result<(), String> {
        let name = StorageName::new(use_.name).map_err(|e| e.to_string())?;
        let storage_files = build_files(&store, use_.storage_build).map_err(|e| e.to_string())?;
        let query_files = build_files(&store, use_.query_build).map_err(|e| e.to_string())?;
        check_storage_composition(&storage_files, &query_files, &name).map_err(|e| e.to_string())
    };
    let admission = records::admit_package_v4(
        &store,
        &VerusPackageAdmissionV2 {
            package,
            gate_identity: GATE_IDENTITY_V4.into(),
            qualification_evidence: vec![qualification_evidence],
            assets: candidate.assets.clone(),
        },
        &expected,
        &composition,
    )
    .map_err(record_error)?;
    Ok(QualificationV4 {
        admission,
        package,
        statement: statement_id,
        claim,
        build,
        tcb,
        implementations,
        storage_uses: candidate.storage_uses,
        assets: candidate.assets,
        qualification_evidence,
        statement_key: statement.key_v4_id.clone(),
        entry,
    })
}

/// The fixed entry's implementation record and one per author module.
fn publish_implementations(
    store: &ObjectStore,
    build: ContentId,
    context: &QueryV4Context<'_>,
    entry: QueryEntry,
    modules: &[CandidateModule],
) -> Result<Vec<ContentId>, AdmissionError> {
    let entry_items = RECORDED_ENTRY_ITEMS
        .iter()
        .map(|name| {
            let (requires, ensures) = (context.clause_text)(entry.source, name).ok_or_else(|| AdmissionError::tool("entry clause text absent"))?;
            Ok(VerusItemV1 { path: format!("{CANDIDATE_CRATE_NAME}::gendb_entry::{name}"), requires, ensures })
        })
        .collect::<Result<Vec<_>, AdmissionError>>()?;
    let entry = VerusImplementationV1 { build, module: "gendb_entry".into(), operations: vec![], items: entry_items };
    let mut implementations = vec![store.put(1, records::VERUS_IMPLEMENTATION_KIND, &entry).map_err(store_error)?];
    for module in modules {
        let record = VerusImplementationV1 { build, module: format!("agent/{} ({})", module.file, module.role), operations: vec![], items: module.items.clone() };
        implementations.push(store.put(1, records::VERUS_IMPLEMENTATION_KIND, &record).map_err(store_error)?);
    }
    Ok(implementations)
}

/// The SQL translated again now: the fresh instance must have the same statement key v2; its query crate generation,
/// with the storages' interfaces from their admitted packages, is what admission compares with the build.
fn fresh_framework(
    context: &QueryV4Context<'_>,
    store: &ObjectStore,
    uses: &[VerusStorageUseV1],
    storages: &[VerusStoragePackageV1],
) -> Result<Vec<FrameworkSource>, AdmissionError> {
    let statement = context.statement;
    let directory = statement.directory.join(format!("admission-{}", now_unix_ms()));
    let constraints = statement.integrity_constraints.as_ref();
    let fresh = prepare_statement(context.parser, context.dataset, constraints, &statement.sql, &statement.parameters, &[], &[], &directory)
        .map_err(|Refused { error, .. }| AdmissionError::refusal(format!("the SQL no longer translates at admission: {error}")))?;
    if fresh.key_v4 != statement.key_v4 {
        return Err(AdmissionError::refusal("the SQL no longer translates to the checked statement instance"));
    }
    let mut names = vec![];
    let mut declarations = vec![];
    let mut interfaces = vec![];
    for (storage_use, storage) in uses.iter().zip(storages) {
        names.push(StorageName::new(&storage_use.name).map_err(AdmissionError::refusal)?);
        declarations.push(serde_json::from_value::<DeclaredSource>(storage.declaration.clone()).map_err(AdmissionError::tool)?);
        interfaces.push(interface_files(store, storage)?);
    }
    let storage_uses: Vec<StorageUse<'_>> = (0..uses.len())
        .map(|i| StorageUse { name: &names[i], declaration: &declarations[i], interface: &interfaces[i] })
        .collect();
    let files = query_crate_files(&fresh.instance, &fresh.source, &storage_uses, &fresh.identity()).map_err(|e| match e.failure_class() {
        "missing_input" => AdmissionError::missing_input(e),
        _ => AdmissionError::tool(e),
    })?;
    Ok(with_trusted_shim(files, GENDB_QUERY_SHIM_V4_SOURCE))
}

/// The interface files of an admitted storage (`stores/<name>/interface/**`), from its stored closure.
fn interface_files(store: &ObjectStore, storage: &VerusStoragePackageV1) -> Result<Vec<FrameworkSource>, AdmissionError> {
    let prefix = format!("stores/{}/interface/", storage.name);
    storage
        .closure
        .iter()
        .filter(|file| file.path.starts_with(&prefix))
        .map(|file| {
            let bytes = store.read_blob(file.blob, Some(file.bytes)).map_err(store_error)?;
            let text = String::from_utf8(bytes).map_err(AdmissionError::tool)?;
            Ok(FrameworkSource { path: file.path.clone(), text })
        })
        .collect()
}

/// The TCB record of query packages over stored data proved with `entry`: the shared items, the v4 runtime, stored
/// assets, serving lookup (under declared constraints also the lookup by the declaration list), the flat asset host item
/// `flat_capture_parts` when the package reads a flat asset (`flat`), and the entry's assumptions. For entry v4 over
/// built assets it is the record written before constraints could be declared.
pub fn query_v4_tcb_record(entry: QueryEntry, flat: bool) -> Result<VerusTcbV1, AdmissionError> {
    let mut serving = SERVING_TRUSTED_ITEMS_V4.to_vec();
    if entry == QUERY_ENTRY_V5 {
        serving.push(DECLARED_CONSTRAINTS_LOOKUP);
    }
    if flat {
        serving.push(FLAT_CAPTURE_PARTS);
    }
    let mut items = framework_trusted_items();
    items.extend(v4_host_items(&serving));
    items.extend(entry_assumptions(entry.trusted_assumptions, entry.identity));
    Ok(VerusTcbV1 { items, refusal_rules: serde_json::to_value(VERUS_REFUSAL_RULES).map_err(AdmissionError::tool)? })
}

/// Whether any of `assets` was published from a capture's column files (`flat_capture_parts`), by its evidence kind.
fn reads_flat_assets(store: &ObjectStore, assets: &[ContentId]) -> Result<bool, AdmissionError> {
    for id in assets {
        let asset: records::VerusStorageAssetV1 = store.read(*id).and_then(|o| o.decode()).map_err(store_error)?;
        if store.read(asset.evidence).map_err(store_error)?.kind == FLAT_CAPTURE_ASSET_KIND {
            return Ok(true);
        }
    }
    Ok(false)
}
