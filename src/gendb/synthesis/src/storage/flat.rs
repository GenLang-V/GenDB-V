//! Fixed flat storage (`storage_policy` `fixed_flat`): the storage side of the plain-array storage ablation.
//!
//! Every table of the dataset is stored once by one framework-generated storage `flat_<table>`
//! (`gendb_verification::obligations::flat_storage`): every column as a plain typed array in source row order, the
//! element type fixed by the declared SQL type. It is an ordinary storage package of the fixed storage entry v1 (the
//! generated interface and builder are verified and compiled whole like any storage), prepared once by
//! `gendb prepare-flat-storage` ([`prepare_flat_storages`]) and never designed, built or changed by an author. Its asset
//! is the capture's own column files (`AssetBuildSlot::publish_flat_capture_parts`, trusted host item
//! `flat_capture_parts`): hard links, and one byte copy of a file that lies on another filesystem.
//!
//! What enforces the mode (none of it is only a prompt):
//! - the request: `fixed_flat` takes no workload storage and no storage budget (`controller::request`);
//! - eligibility ([`flat_ineligibility`], through `StoredDataPolicy::ineligible`, so catalogs, evaluation,
//!   qualification and serving apply it): an admitted package is usable only when its sources are exactly the
//!   generator's output for its declaration, from source columns, assuming no declared constraint, under storage
//!   entry v1. A registration's recorded words are not trusted;
//! - assets ([`check_flat_asset`]): a flat use reads only an asset published from the capture's column files; a
//!   missing one is refused (`flat_storage_not_prepared`), never built;
//! - the tools: storage tools are neither offered nor run, workspace storages are refused at freeze, a stale flat
//!   storage is refused instead of re-verified (`tools::bench`, `query::candidate`);
//! - synthesis starts only when every table's current flat storage and asset are prepared ([`flat_readiness`]);
//! - query author files under `fixed_flat` may not declare `static` items (`gendb_verification::verus::scan_static_items`):
//!   Verus admits an `exec static` atomic, which could carry state from one measured call to the next.
//!
//! The authors' shell is not a sandbox against reading files; what the claims rest on is the query code, which reads
//! data only through its `StoredParts` handles.

use super::catalog::{STORAGE_DESCRIPTION_KIND, admitted_storage};
use super::freeze::freeze_storage;
use super::manifest::{STORAGE_MANIFEST_FILE, StorageLayout, StorageManifest, StoredTable};
use super::registration::register_storage;
use super::reverify::{ClosureState, closure_state};
use crate::controller::records::write_new_json;
use crate::query::compile::{self, declared_items, item_record};
use crate::query::host_locks::HostLocks;
use crate::query::source_items::requires_ensures;
use gendb_artifacts::verus::{self as records, VerusStorageAssetV1, VerusStoragePackageV1};
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_frontend::ast::TableDef;
use gendb_registry::CrateKind;
use gendb_storage::import::PreparedSource;
use gendb_storage::versions::CurrentCapture;
use gendb_verification::admission::AdmissionError;
use gendb_verification::admission::storage::{
    AssetLookup, FLAT_CAPTURE_ASSET_KIND, FLAT_CAPTURE_PARTS, StorageCandidate, StorageSchema, flat_storage_of_build, lookup_storage_asset,
    publish_storage, run_constraints_digest,
};
use gendb_verification::obligations::{FLAT_STORAGE_GENERATOR, FlatStorage, STORAGE_ENTRY_IDENTITY, flat_storage};
use gendb_verification::verus::{STATIC_ITEM_RULE, scan_static_items};
use gendb_runtime::serve::AdmittedPackage;
use super::policy::StoredDataPolicy;
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::Instant;

/// `kind` of the fixed flat policy, recorded with every flat storage registration.
pub const FIXED_FLAT: &str = "fixed_flat";

/// [`author_view`] for a dataset schema with a nullable column (`nullable`): it adds the validity part of a nullable
/// column to the representation and readers. Without one it is `author_view`, byte for byte.
pub fn author_view_for(nullable: bool) -> Value {
    let mut view = author_view();
    if nullable {
        let representation = &mut view["representation"];
        representation["nullable"] = json!("a nullable column has one more part after its value part(s): <COLUMN>_VALIDITY, U8, one byte per row (0: the row is NULL; its value bytes mean nothing)");
        let rule = format!("{}; and one validity part per nullable column", representation["rule"].as_str().unwrap_or_default());
        representation["rule"] = json!(rule);
        let readers = format!(
            "{}; read_<column>_validity(s, lo, hi, Ghost(rels)) for a nullable column, whose value readers state every row that is not NULL",
            view["readers"].as_str().unwrap_or_default()
        );
        view["readers"] = json!(readers);
    }
    view
}

/// The policy as both roles read it (prompt facts, `stored-data.json`, summaries).
pub fn author_view() -> Value {
    json!({"kind":FIXED_FLAT,"generator":FLAT_STORAGE_GENERATOR,
        "meaning":"our flat-storage definition: every table is stored once, by GenDB, as plain typed arrays, one per column, in the original source row order. Nobody designs storage in this run: there is no sorting, partitioning, index, permutation, compression, dictionary, data-dependent encoding or skip metadata, and no storage can be added or changed",
        "storages":"one storage per table, named flat_<table>, holding every column of the table (storages.json; interface copies under admitted-storages/)",
        "representation":{"bigint":"I64 value","integer":"I32 value","date":"I32 days since 1970-01-01","numeric(p,s)":"I128 coefficient, value = coefficient * 10^-s",
            "text, varchar, char":"I64 offsets (rows + 1, positions in the bytes part; the first need not be 0) and U8 UTF-8 bytes; value i = bytes[offsets[i] .. offsets[i + 1]]",
            "rule":"the element type follows the declared SQL type only, never observed values; one part per column, two for text, in column order; stored row i is source row i"},
        "readers":"each flat interface (stores/flat_<table>/interface/mod.rs) states represents(parts, rels) (row i of the table is row_at(parts, i)) and verified readers: stored_rows, read_<column>(s, lo, hi, Ghost(rels)) for fixed-width columns, read_<column>_at(s, i, Ghost(rels)) and read_<column>_range(s, lo, hi, Ghost(rels)) for text, text_rows; you may also call StoredParts extents with the part constants and prove from represents yourself",
        "runtime":"hash tables, sorting, grouping, joins, filters and any other temporary structure are built inside each measured call, timed, and discarded; nothing computed in one call may be kept for a later call (static items are refused in query code under fixed_flat)",
        "tools":"the storage tools (storage_check, storage_verify, storage_compile, storage_build, storage_register) are not available; a query manifest names only the admitted flat packages (workspace storages are refused, fixed_flat_workspace_storage)",
        "trust":FLAT_CAPTURE_PARTS.0,
        "not_a_proof":"the flat representation is fixed by GenDB's generator and checked at every use (sources equal to the generator's output, assets published from the capture's column files); Verus proves what your code computes over it"})
}

/// Why the admitted storage `package` named `name` is not a usable fixed flat storage (`None`: it is). Decided from
/// the package's records, never from a registration's words: the generator's output for its declaration, built from
/// source columns under storage entry v1, assuming no declared constraint.
pub fn flat_ineligibility(store: &ObjectStore, package: ContentId, name: &str) -> Result<Option<String>, AdmissionError> {
    let ineligible = |why: String| Ok(Some(format!("storage_policy_ineligible: admitted storage {name} ({package}) is not a fixed flat storage: {why}")));
    let record = match records::resolve_admitted_storage(store, package) {
        Ok(record) => record,
        Err(e) => return ineligible(e.to_string()),
    };
    if record.name != name {
        return ineligible(format!("the package is named {}", record.name));
    }
    if record.derived_from.is_some() || record.assumed_constraints.is_some() || record.entry_identity != STORAGE_ENTRY_IDENTITY {
        return ineligible("a flat storage is built from source columns under storage entry v1 and assumes no declared constraint".into());
    }
    let build = records::storage_build(store, &record).map_err(AdmissionError::tool)?;
    match flat_storage_of_build(store, &build, &record.declaration) {
        Ok(flat) if flat.name.as_str() == name => Ok(None),
        Ok(flat) => ineligible(format!("its declaration generates storage {}", flat.name)),
        Err(e) => ineligible(e.message),
    }
}

/// Refuse the asset `asset` of the flat storage `name` unless it was published from the capture's column files.
pub fn check_flat_asset(store: &ObjectStore, name: &str, asset: &VerusStorageAssetV1) -> Result<(), AdmissionError> {
    let kind = store.read(asset.evidence).map_err(AdmissionError::tool)?.kind;
    if kind != FLAT_CAPTURE_ASSET_KIND {
        return Err(AdmissionError::refusal(format!(
            "flat_storage_asset_not_fixed: the asset of flat storage {name} ({}) was not published from the capture's column files (its evidence is {kind})",
            asset.directory
        )));
    }
    Ok(())
}

/// The refusal of a flat storage use without an asset for the current capture: flat assets are prepared, never built.
pub fn not_prepared(name: &str) -> AdmissionError {
    AdmissionError::refusal(format!(
        "flat_storage_not_prepared: flat storage {name} has no asset for the current capture; it is prepared once by gendb prepare-flat-storage, never built during synthesis"
    ))
}

/// Under `fixed_flat`, a `static` item (`STATIC_ITEM_RULE`) in the agent files among `files` (`(path, text)`, paths
/// relative to the crate's `src/`), as its named refusal.
pub fn static_item_refusal<'a>(files: impl IntoIterator<Item = (&'a str, &'a str)>) -> Option<String> {
    files
        .into_iter()
        .filter(|(path, _)| path.starts_with("agent/"))
        .flat_map(|(path, text)| scan_static_items(path, text))
        .next()
        .map(|found| format!("{}: {}:{}: {} ({})", STATIC_ITEM_RULE.id, found.file, found.line, STATIC_ITEM_RULE.refuses, STATIC_ITEM_RULE.reason))
}

/// Under `fixed_flat`, why the admitted query package `admitted` may not be served or measured over `capture` (`None`:
/// it may): a saved ABI v3 package (it reads delivered columns, not the flat storages), a storage use that is not an
/// eligible flat storage, a use without its prepared flat asset, or a `static` item in the agent sources of its checked
/// build (it may have been admitted under another policy). Library records and source blobs only; no proof is re-run.
pub fn served_package_refusal(store: &ObjectStore, capture: &CurrentCapture, admitted: &AdmittedPackage) -> Result<Option<String>, AdmissionError> {
    let AdmittedPackage::StoredDataV4 { resolved, .. } = admitted else {
        return Ok(Some(
            "fixed_flat_package_not_flat: a saved ABI v3 package reads delivered columns, not the flat storages; under storage_policy fixed_flat only packages over the flat storages are served".into(),
        ));
    };
    let uses = &resolved.package.storage_uses;
    let policy = StoredDataPolicy::FixedFlat {};
    if let Some(reason) = policy.ineligible_use(store, uses.iter().map(|u| (u.name.as_str(), u.package)))? {
        return Ok(Some(reason));
    }
    for storage_use in uses {
        let record = records::resolve_admitted_storage(store, storage_use.package).map_err(AdmissionError::tool)?;
        let key = capture.asset_key(storage_use.package, &record).map_err(AdmissionError::missing_input)?;
        match records::resolve_storage_asset(store, &key).map_err(AdmissionError::tool)? {
            Some((_, asset)) => {
                if let Err(refused) = check_flat_asset(store, &storage_use.name, &asset) {
                    return Ok(Some(refused.message));
                }
            }
            None => return Ok(Some(not_prepared(&storage_use.name).message)),
        }
    }
    let sources = resolved.build.source_texts(store).map_err(AdmissionError::tool)?;
    let agent = sources.iter().filter(|(_, owner, _)| *owner == records::VerusSourceOwnerV1::Agent).map(|(path, _, text)| (path.as_str(), text.as_str()));
    Ok(static_item_refusal(agent))
}

/// One table's prepared flat storage.
struct PreparedFlat {
    package: ContentId,
    record: VerusStoragePackageV1,
    asset: Option<(ContentId, VerusStorageAssetV1)>,
}

/// The newest admitted version of `flat` that is a current flat storage (eligible, the generator's declaration for the
/// run's schema, framework closure current), with its flat asset for `capture` when one is published.
fn current_flat(store: &ObjectStore, schema: &[TableDef], capture: &CurrentCapture, flat: &FlatStorage) -> Result<Option<PreparedFlat>, AdmissionError> {
    let name = flat.name.as_str();
    for (_, admission) in records::storage_versions(store, name).map_err(AdmissionError::tool)? {
        let package = admission.package;
        if flat_ineligibility(store, package, name)?.is_some() {
            continue;
        }
        let (record, declaration) = admitted_storage(store, package)?;
        if declaration != flat.declaration || closure_state(schema, &record, &declaration)? != ClosureState::Current {
            continue;
        }
        let key = capture.asset_key(package, &record).map_err(AdmissionError::missing_input)?;
        let asset = records::resolve_storage_asset(store, &key).map_err(AdmissionError::tool)?;
        return Ok(Some(PreparedFlat { package, record, asset }));
    }
    Ok(None)
}

/// Every table's current flat storage with its flat asset for `capture`: `(table, storage, package, asset)` records,
/// or the reasons some table is not prepared (`flat_storage_not_prepared`). Records only; nothing is built.
pub fn flat_readiness(store: &ObjectStore, schema: &[TableDef], capture: &CurrentCapture) -> Result<Result<Vec<Value>, Vec<String>>, AdmissionError> {
    let (mut ready, mut missing) = (vec![], vec![]);
    for table_id in 0..schema.len() {
        let flat = flat_storage(schema, table_id).map_err(|e| AdmissionError::refusal(e.to_string()))?;
        match current_flat(store, schema, capture, &flat)? {
            Some(PreparedFlat { package, asset: Some((asset_id, asset)), .. }) => {
                check_flat_asset(store, flat.name.as_str(), &asset)?;
                ready.push(json!({"table":flat.table,"storage":flat.name.as_str(),"package":package,"asset":asset_id,"storage_bytes":asset.storage_bytes}));
            }
            Some(_) => missing.push(format!("{}: no flat asset for the current capture", flat.name)),
            None => missing.push(format!("{}: no current flat storage package", flat.name)),
        }
    }
    Ok(if missing.is_empty() { Ok(ready) } else { Err(missing) })
}

/// What the one-time preparation needs.
pub struct FlatPreparation<'a> {
    pub library: &'a Path,
    pub locks: &'a HostLocks,
    /// The dataset schema, its DDL and frontend (the statements').
    pub schema: StorageSchema<'a>,
    /// The run's prepared capture (every column of every table).
    pub source: &'a PreparedSource,
    /// Evidence directory (`<run>/flat-storage`).
    pub out: &'a Path,
    /// Recorded with each registration (who prepared it).
    pub registered_by: Value,
}

/// Prepare the fixed flat storage of every table of the schema once: a current admitted flat package with its flat
/// asset is reused; otherwise the generated storage crate is frozen, verified and compiled whole, published (sources
/// checked against the generator), its asset published from the capture's column files, and the package registered
/// under `fixed_flat`. Returns the preparation record (per table: package, asset, parts, bytes, times).
pub fn prepare_flat_storages(preparation: &FlatPreparation<'_>) -> Result<Value, AdmissionError> {
    let store = ObjectStore::open(preparation.library).map_err(AdmissionError::tool)?;
    let capture = CurrentCapture::of(preparation.source).map_err(AdmissionError::tool)?;
    let schema = preparation.schema.tables;
    let mut tables = vec![];
    for table_id in 0..schema.len() {
        let flat = flat_storage(schema, table_id).map_err(|e| AdmissionError::refusal(e.to_string()))?;
        tables.push(prepare_table(preparation, &store, &capture, &flat)?);
    }
    let logical: u64 = tables.iter().filter_map(|t| t["asset"]["storage_bytes"].as_u64()).sum();
    let copied: u64 = tables.iter().filter_map(|t| t["asset"]["copied_bytes"].as_u64()).sum();
    let nullable = schema.iter().any(|t| t.columns.iter().any(|c| c.nullable));
    Ok(json!({"format_version":1,"storage_policy":author_view_for(nullable),"capture":{"archive":preparation.source.archive(),"capture_identity":preparation.source.capture_identity()},
        "tables":tables,"storage_bytes":logical,"copied_bytes":copied,
        "scope":"one framework-generated flat storage per table: verified and compiled whole, assets published from the capture's column files (hard links; byte copies only across filesystems); no author, no builder run on the full data"}))
}

/// One table: reuse its current flat storage and asset, or create what is missing.
fn prepare_table(preparation: &FlatPreparation<'_>, store: &ObjectStore, capture: &CurrentCapture, flat: &FlatStorage) -> Result<Value, AdmissionError> {
    let started = Instant::now();
    let name = flat.name.as_str();
    let (package, record, created) = match current_flat(store, preparation.schema.tables, capture, flat)? {
        Some(current) => (current.package, current.record, None),
        None => {
            let (package, record, verus) = publish_flat_package(preparation, store, flat)?;
            (package, record, Some(verus))
        }
    };
    let key = capture.asset_key(package, &record).map_err(AdmissionError::missing_input)?;
    let (asset, evidence) = match lookup_storage_asset(store, package, capture, run_constraints_digest(preparation.schema.tables)?)? {
        AssetLookup::Published(asset) => {
            check_flat_asset(store, name, &asset.asset)?;
            let evidence: Value = store.read(asset.asset.evidence).and_then(|o| o.decode()).map_err(AdmissionError::tool)?;
            (asset, evidence)
        }
        AssetLookup::Absent(slot) => {
            let reuse = earlier_copies(store, capture, name)?;
            slot.publish_flat_capture_parts(store, flat, preparation.source.archive(), preparation.source.capture_identity(), &reuse)?
        }
    };
    let manifest = flat_manifest(flat);
    let mut description = json!({"layout":manifest.layout,"parts":manifest.parts,"registered_by":preparation.registered_by});
    let standing = StoredDataPolicy::FixedFlat {}.standing();
    for (field, value) in standing.as_object().into_iter().flatten() {
        description[field] = value.clone();
    }
    let registration = register_storage(store, name, package, asset.id, &[asset.asset.evidence], &description)?;
    Ok(json!({"table":flat.table,"storage":name,"package":package,"admission":registration.admission,"admitted_now":registration.admitted_now,
        "created":created,"key":key,"asset":{"id":asset.id,"directory":asset.directory,"storage_bytes":asset.asset.storage_bytes,
            "copied_bytes":evidence["copied_bytes"],"published_now":asset.built,"evidence":asset.asset.evidence},
        "parts":flat.parts.len(),"wall_ns":started.elapsed().as_nanos() as u64,"description_kind":STORAGE_DESCRIPTION_KIND}))
}

/// The manifest of a flat storage (`verus-storage.json` of its generated workspace).
fn flat_manifest(flat: &FlatStorage) -> StorageManifest {
    let columns = flat.declaration.tables[0].columns.iter().map(|c| c.name.clone()).collect();
    StorageManifest {
        format_version: 1,
        name: flat.name.to_string(),
        crate_dir: "crate".into(),
        tables: vec![StoredTable { table: flat.table.clone(), columns }],
        parts: flat.parts.iter().map(|p| format!("{} {} of {}", p.constant, p.elem.variant(), p.column)).collect(),
        layout: StorageLayout {
            summary: format!("fixed flat storage of {}: every column as a plain typed array in source row order, one part per column, two (offsets, bytes) per text column", flat.table),
            units: "bigint I64, integer I32, date I32 days since 1970-01-01, numeric I128 coefficient at the declared scale, text I64 offsets into U8 UTF-8 bytes".into(),
            choice: format!("fixed by storage_policy fixed_flat ({FLAT_STORAGE_GENERATOR}); not chosen for any workload"),
        },
        data_policy: Default::default(),
        modules: vec![],
        compiler: None,
        notes: "generated by GenDB; no author".into(),
        uses_declared_constraints: false,
        built_from: None,
    }
}

/// Generate, freeze, verify and compile the flat storage crate of `flat` once, and publish its package (sources checked
/// against the generator). Returns `(package, record, Verus run summary)`.
fn publish_flat_package(preparation: &FlatPreparation<'_>, store: &ObjectStore, flat: &FlatStorage) -> Result<(ContentId, VerusStoragePackageV1, Value), AdmissionError> {
    let dir = preparation.out.join(format!("{}-{}", flat.name, crate::controller::records::now_unix_ms()));
    let workspace = dir.join("workspace");
    for file in &flat.files {
        let path = workspace.join("crate/src").join(&file.path);
        std::fs::create_dir_all(path.parent().expect("a file path")).map_err(AdmissionError::tool)?;
        std::fs::write(&path, &file.text).map_err(AdmissionError::tool)?;
    }
    write_new_json(&workspace.join(STORAGE_MANIFEST_FILE), &flat_manifest(flat)).map_err(AdmissionError::tool)?;
    let frozen_dir = dir.join("frozen");
    let frozen = freeze_storage(&workspace, Path::new(STORAGE_MANIFEST_FILE), &frozen_dir, preparation.schema.tables, Some(store), &BTreeMap::new())?;
    let krate = frozen.frozen_crate(&frozen_dir);
    let (run, _) = compile::compile(preparation.locks, &krate, CrateKind::Storage, &frozen.compiler, &dir.join("verus"))?;
    let stdout = run["stdout"].as_str().unwrap_or_default();
    let items = declared_items(&frozen.declared_modules(stdout)?, &krate, CrateKind::Storage, stdout)?;
    let readers = items.iter().filter(|item| item["module_role"] != json!("builder")).map(item_record).collect();
    let name = frozen.name()?;
    let candidate = StorageCandidate {
        name: &name,
        declaration: &frozen.declaration,
        uses_declared_constraints: false,
        derivation: None,
        frozen_root: &krate.root,
        verus_run: &run,
        readers,
        flat: true,
    };
    let clause_text = |text: &str, item: &str| requires_ensures(text, item);
    let published = publish_storage(store, preparation.schema, &candidate, &clause_text)?;
    let verus = json!({"evidence":dir,"verification":run.get("verification"),"wall_ns":run.get("wall_ns")});
    Ok((published.package, published.record, verus))
}

/// The copies earlier flat assets of storage `name` over the same capture made of capture files on another
/// filesystem: resolved capture file -> that copy (a part file in the library), so a new flat asset links it.
fn earlier_copies(store: &ObjectStore, capture: &CurrentCapture, name: &str) -> Result<BTreeMap<PathBuf, PathBuf>, AdmissionError> {
    let mut copies = BTreeMap::new();
    for (_, admission) in records::storage_versions(store, name).map_err(AdmissionError::tool)? {
        let record = records::resolve_admitted_storage(store, admission.package).map_err(AdmissionError::tool)?;
        let Ok(key) = capture.asset_key(admission.package, &record) else { continue };
        let Some((_, asset)) = records::resolve_storage_asset(store, &key).map_err(AdmissionError::tool)? else { continue };
        let object = store.read(asset.evidence).map_err(AdmissionError::tool)?;
        if object.kind != FLAT_CAPTURE_ASSET_KIND {
            continue;
        }
        let evidence: Value = object.decode().map_err(AdmissionError::tool)?;
        let directory = records::storage_asset_directory(store, &asset).map_err(AdmissionError::tool)?;
        for part in evidence["parts"].as_array().into_iter().flatten().filter(|p| p["placement"] == "copy") {
            let (Some(resolved), Some(index)) = (part["resolved"].as_str(), part["part"].as_u64()) else { continue };
            copies.entry(PathBuf::from(resolved)).or_insert_with(|| directory.join(format!("part-{index:04}.bin")));
        }
    }
    Ok(copies)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Only agent files are scanned, and a `static` item there is refused by name; `'static` and `const` are not items.
    #[test]
    fn static_items_in_agent_files_are_refused() {
        let item = "use vstd::prelude::*;\nverus! {\nexec static CALLS: u64 ensures true { 0 }\n}\n";
        let refused = static_item_refusal([("agent/mod.rs", item)]).unwrap();
        assert!(refused.starts_with(STATIC_ITEM_RULE.id) && refused.contains("agent/mod.rs:3"), "{refused}");
        assert_eq!(static_item_refusal([("stores/flat_t/interface/mod.rs", item)]), None, "only agent files");
        assert_eq!(static_item_refusal([("agent/mod.rs", "verus! { const N: usize = 1; fn f(s: &'static [u8]) {} }")]), None);
    }
}
