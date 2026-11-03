//! The admitted storages as an author sees them: every admitted version, head marked `current` (`storage_versions_for`), whether
//! it applies to the current capture and schema (and why not), its asset for the current capture when built, its
//! declaration, interface files, readers, part labels, layout explanation, recorded storage policy (kind and revision)
//! and data_policy declaration, the declared integrity constraints its builder assumes (`assumed_constraints`, storage entry v2 only),
//! and measured sizes and build time. The
//! library records are the authority; this module only reads and renders them.

use crate::controller::records::write_json_atomic;
use gendb_artifacts::verus::{self as records, VerusStorageAssetV1, VerusStoragePackageV1};
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_frontend::ast::TableDef;
use gendb_frontend::translator::{EmitOptions, emit_column_schema_module};
use super::reverify::{ClosureState, closure_state, content_matches};
use gendb_storage::versions::{CurrentCapture, storage_versions_for};
use gendb_verification::admission::AdmissionError;
use gendb_verification::admission::storage::run_constraints_digest;
use gendb_verification::obligations::{DeclaredSource, check_storage_coverage, StorageName, StorageUse};
use gendb_verification::verus::FrameworkSource;
use serde_json::{Value, json};
use std::fs;
use std::path::Path;

/// Record kind of the author's description of a storage (descriptive admission evidence; never interpreted).
pub const STORAGE_DESCRIPTION_KIND: &str = "gendb.verus.storage-description.v1";

/// One admitted storage version.
#[derive(Clone, Debug)]
pub struct AdmittedStorage {
    pub package_id: ContentId,
    pub package: VerusStoragePackageV1,
    pub declaration: DeclaredSource,
    /// Whether this version is its name's head (newest admission); older versions stay usable by package id.
    pub current: bool,
    /// `Ok` when it applies to the current capture and represents the same content over the run's schema, else the
    /// named reason (`storage::reverify`).
    pub applicability: Result<(), String>,
    /// For an applicable storage: whether its framework closure is the current one or it is re-verified on first use.
    pub closure: Option<ClosureState>,
    /// Its asset for the current capture, if built.
    pub asset: Option<(ContentId, VerusStorageAssetV1)>,
    /// The author's description recorded at registration (parts, layout, who registered it), if any.
    pub description: Value,
}

/// The dataset's column schema text every storage and query crate carries (`schema.rs`).
pub fn schema_text(schema: &[TableDef]) -> Result<String, AdmissionError> {
    emit_column_schema_module(schema, &EmitOptions::candidate()).map_err(|e| AdmissionError::tool(format!("schema module: {e}")))
}

/// Every admitted storage version of the library (newest first per name, heads marked), with its applicability to
/// `capture` over `schema` (the dataset tables, with the run's declared constraints): a storage that assumes another
/// declaration set is listed as not applicable (`storage_assumes_declared_constraints`) and counted, never offered.
pub fn admitted_storages(store: &ObjectStore, capture: &CurrentCapture, schema: &[TableDef]) -> Result<Vec<AdmittedStorage>, AdmissionError> {
    let declared = run_constraints_digest(schema)?;
    let versions = storage_versions_for(store, capture, declared, None).map_err(AdmissionError::tool)?;
    versions
        .into_iter()
        .map(|version| {
            let declaration: DeclaredSource =
                serde_json::from_value(version.package.declaration.clone()).map_err(|e| AdmissionError::tool(format!("storage declaration: {e}")))?;
            let description = description_of(store, version.package_id, &version.package.name)?;
            // Applicability by content: the same tables and columns with the same types; the framework text may differ.
            let (applicability, closure) = match version.applicability.and_then(|()| content_matches(schema, &version.package)) {
                Ok(fresh) => (Ok(()), Some(closure_state(schema, &version.package, &fresh)?)),
                Err(reason) => (Err(reason), None),
            };
            Ok(AdmittedStorage {
                package_id: version.package_id,
                package: version.package,
                declaration,
                current: version.current,
                applicability,
                closure,
                asset: version.asset,
                description,
            })
        })
        .collect()
}

/// The admitted storage package `id` (refused unless admitted), with its declaration.
pub fn admitted_storage(store: &ObjectStore, id: ContentId) -> Result<(VerusStoragePackageV1, DeclaredSource), AdmissionError> {
    let package = records::resolve_admitted_storage(store, id).map_err(|e| AdmissionError::missing_input(format!("storage package {id}: {e}")))?;
    let declaration = serde_json::from_value(package.declaration.clone()).map_err(|e| AdmissionError::tool(format!("storage declaration: {e}")))?;
    Ok((package, declaration))
}

/// The interface files of a storage package (`stores/<name>/interface/**`), from its stored closure: exactly the bytes
/// its checked build had.
pub fn interface_files(store: &ObjectStore, package: &VerusStoragePackageV1) -> Result<Vec<FrameworkSource>, AdmissionError> {
    let prefix = format!("stores/{}/interface/", package.name);
    package
        .closure
        .iter()
        .filter(|file| file.path.starts_with(&prefix))
        .map(|file| {
            let bytes = store.read_blob(file.blob, Some(file.bytes)).map_err(AdmissionError::tool)?;
            Ok(FrameworkSource { path: file.path.clone(), text: String::from_utf8(bytes).map_err(AdmissionError::tool)? })
        })
        .collect()
}

/// The description evidence of the admission of `package` (null when none was recorded).
pub fn description_of(store: &ObjectStore, package: ContentId, name: &str) -> Result<Value, AdmissionError> {
    for (_, admission) in records::storage_versions(store, name).map_err(AdmissionError::tool)? {
        if admission.package != package {
            continue;
        }
        for evidence in admission.evidence {
            let object = store.read(evidence).map_err(AdmissionError::tool)?;
            if object.kind == STORAGE_DESCRIPTION_KIND {
                let record: Value = object.decode().map_err(AdmissionError::tool)?;
                return Ok(record["description"].clone());
            }
        }
    }
    Ok(Value::Null)
}

/// Which part of a statement's demand one storage stores: `covers` (every demanded column and table) or the demanded
/// tables and columns it lacks (`missing`; a query may read several storages together, so another storage, or an
/// extension of this one, can supply them), with the first gap named as freeze reports it.
pub fn coverage_of(demand: &DeclaredSource, name: &StorageName, declaration: &DeclaredSource) -> Value {
    let interface: [FrameworkSource; 0] = [];
    let alone = [StorageUse { name, declaration, interface: &interface }];
    match check_storage_coverage(demand, &alone) {
        Ok(()) => json!({"covers":true}),
        Err(gap) => {
            let stored = |table: usize, ordinal: Option<usize>| {
                declaration.tables.iter().any(|t| t.table_id == table && ordinal.is_none_or(|o| t.columns.iter().any(|c| !c.row_count_only && c.ordinal == o)))
            };
            let missing: Vec<String> = demand
                .tables
                .iter()
                .flat_map(|t| {
                    let table = (!stored(t.table_id, None)).then(|| format!("{} (table)", t.name));
                    let columns = t.columns.iter().filter(|c| !c.row_count_only && !stored(t.table_id, Some(c.ordinal))).map(|c| format!("{}.{}", t.name, c.name));
                    table.into_iter().chain(columns)
                })
                .collect();
            json!({"covers":false,"missing":missing,"gap":gap.to_string()})
        }
    }
}

/// The author-facing record of one admitted storage. Its interface files are written read-only under `view_dir`
/// (`<view_dir>/stores/<name>/interface/**`) for reading; queries copy them through the framework, never by hand.
pub fn storage_view(store: &ObjectStore, storage: &AdmittedStorage, view_dir: &Path, demands: &[(String, DeclaredSource)]) -> Result<Value, AdmissionError> {
    let files = interface_files(store, &storage.package)?;
    for f in &files {
        write_read_only(&view_dir.join(&f.path), &f.text)?;
    }
    let name = StorageName::new(&storage.package.name).map_err(AdmissionError::tool)?;
    let coverage: Vec<Value> = demands.iter().map(|(statement, demand)| json!({"statement":statement,"coverage":coverage_of(demand, &name, &storage.declaration)})).collect();
    let tables: Vec<Value> = storage
        .declaration
        .tables
        .iter()
        .map(|t| json!({"table":t.name,"columns":t.columns.iter().filter(|c| !c.row_count_only).map(|c| &c.name).collect::<Vec<_>>(),
            "row_count_carrier":t.columns.iter().any(|c| c.row_count_only)}))
        .collect();
    let asset = storage.asset.as_ref().map(|(id, asset)| {
        json!({"asset":id,"storage_bytes":asset.storage_bytes,"build_wall_ns":asset.build_wall_ns,"parts":asset.parts,"key":asset.key})
    });
    let mut view = json!({"name":storage.package.name,"package":storage.package_id,"use_as":{"name":storage.package.name,"admitted":storage.package_id},"current":storage.current,
        "applicable":storage.applicability.is_ok(),"not_applicable_reason":storage.applicability.as_ref().err(),
        "tables":tables,"interface_files":files.iter().map(|f| view_dir.join(&f.path)).collect::<Vec<_>>(),
        "readers":storage.package.readers,"theorems":storage.package.theorems,
        "parts":storage.description["parts"],"layout":storage.description["layout"],"registered_by":storage.description["registered_by"],
        "storage_policy":storage.description["storage_policy"],"storage_policy_revision":storage.description["storage_policy_revision"],"data_policy":storage.description["data_policy"],
        "closure":match &storage.closure {
            Some(ClosureState::Current) => json!("current"),
            Some(ClosureState::Stale(reason)) => json!({"stale":reason,"use":"name it as usual (use_as): GenDB re-verifies its unchanged interface and builder against the current framework once, as a new version of the same name, and reuses its asset by hard links when the builder's code is unchanged"}),
            None => Value::Null,
        },
        "derived_from":storage.package.derived_from,
        "asset_for_current_data":asset,
        "asset_note":if storage.asset.is_some() { "built for the current capture: using it builds nothing" } else { "no asset for the current capture yet: the first evaluation that uses it builds it once with the admitted library" },
        "statement_coverage":coverage});
    if let Some(assumed) = storage.package.assumed_constraints {
        // Storage entry v2: the builder assumes exactly this declaration set (the digest of its gendb_constraints.rs).
        view["assumed_constraints"] = json!(assumed);
    }
    Ok(view)
}

/// Write a read-only copy of `text` (rewritten only when its bytes differ).
pub fn write_read_only(path: &Path, text: &str) -> Result<(), AdmissionError> {
    use std::os::unix::fs::PermissionsExt;
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(AdmissionError::tool)?;
    }
    if fs::read(path).ok().as_deref() != Some(text.as_bytes()) {
        if path.exists() {
            fs::set_permissions(path, fs::Permissions::from_mode(0o644)).map_err(AdmissionError::tool)?;
        }
        fs::write(path, text).map_err(AdmissionError::tool)?;
    }
    fs::set_permissions(path, fs::Permissions::from_mode(0o444)).map_err(AdmissionError::tool)
}

/// Record a value as JSON (for catalogs written into workspaces).
pub fn write_record(path: &Path, value: &Value) -> Result<(), AdmissionError> {
    write_json_atomic(path, value).map_err(AdmissionError::tool)
}
