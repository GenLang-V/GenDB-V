//! Check and build one storage candidate once: the whole-crate verify-and-compile run of its frozen crate, the checked
//! build recorded in the library (with the library object Verus compiled), its asset over the current capture built
//! by that stored library (never by a run-directory library), and builds over the workload's tiny inputs (none under the validation policy `formal_proofs`).
//!
//! This is the one path of `storage_build`, `storage_register`, the workload role's evaluation and a query's workspace
//! storages. A checked storage is cached per session by its source key. Its asset is a **trial asset**
//! (`query::assets`): built once into the session's trial directory, outside the library, and published only when
//! the storage is registered (`tools::bench`, promotion by rename with the same asset id). A reused checked storage
//! re-resolves its asset ([`refresh_storage_asset`]): the library's once registered, the trial while present, a
//! rebuild by the same stored library after its session removed the trial. Qualification and registration never
//! build. When the storage stores a column the capture lacks, the capture is extended by exactly that column first
//! (`storage::capture`). An admitted storage's asset for a capture that has none (a new scale, or after its release on
//! the general line) is built straight into the library by its stored builder ([`build_library_asset`]; on the general
//! line its derivation sources first, [`ensure_source_assets`]). A package the user excluded under the run's storage
//! policy (`storage::exclusion`) is refused as soon as its package id is known, before any asset is built or
//! re-resolved.

use super::asset_release::{AssetUpkeep, check_free_space};
use super::budget::StorageBudget;
use super::capture::SharedCapture;
use super::identity::builder_identity;
use super::freeze::FrozenStorage;
use super::policy::StoredDataPolicy;
use crate::query::QuerySession;
use crate::query::assets::{SpaceNeed, TrialAssets};
use crate::query::compile::{self, declared_items, item_record};
use crate::query::host_locks::HostLocks;
use crate::query::source_items::requires_ensures;
use gendb_artifacts::verus as records;
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_registry::CrateKind;
use gendb_storage::versions::CurrentCapture;
use gendb_verification::admission::AdmissionError;
use gendb_verification::admission::execution::CandidateRunner;
use gendb_verification::admission::storage::{
    AssetBuildSlot, AssetLookup, StorageAsset, StorageCandidate, StorageSchema, TrialAsset, build_trial_asset, derived_storage_input, link_trial_asset,
    lookup_storage_asset, publish_storage, run_constraints_digest, storage_input,
};
use gendb_verification::admission::stored_execution::{TinyBuilder, TinySource, check_storage_tiny_builds};
use gendb_verification::obligations::{ColumnKind, DeclaredSource};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// Record kind of the tiny-input build evidence of a storage package.
pub const STORAGE_TINY_BUILDS_KIND: &str = "gendb.verus.storage-tiny-builds.v1";

/// What building a storage needs from its session.
pub struct StorageBuildContext<'a> {
    pub library: &'a Path,
    pub locks: &'a HostLocks,
    pub runner: &'a CandidateRunner,
    pub capture: &'a SharedCapture,
    /// The workload statements (their schema, and their tiny cases for the tiny-input builds).
    pub statements: &'a [Arc<QuerySession>],
    /// Worker count of asset builds (the largest configured).
    pub build_workers: u32,
    /// The session's trial assets.
    pub trials: &'a mut TrialAssets,
    /// Assets the asking job uses: never removed to make room for its builds.
    pub keep: &'a BTreeSet<ContentId>,
    /// The run's stored-data policy: an excluded package is refused before its asset is built.
    pub policy: &'a StoredDataPolicy,
    /// The user's storage budget (`storage::budget`; `None`: no limit).
    pub allowance: Option<u64>,
    /// The general line's upkeep of storage assets on the shared host (`storage::asset_release`): the floor every build
    /// leaves free, and a derived storage's sources built first when their assets were released; `None` elsewhere.
    pub asset_upkeep: Option<AssetUpkeep>,
}

impl StorageBuildContext<'_> {
    /// The dataset schema of the workload's statements (`doc.tables`, with the run's declared constraints).
    fn schema(&self) -> Result<&[gendb_frontend::ast::TableDef], AdmissionError> {
        let statement = self.statements.first().ok_or_else(|| AdmissionError::tool("a storage is checked for a workload with statements"))?;
        Ok(&statement.statement().instance.doc.tables)
    }
}

/// A checked storage candidate with its checked build, its package record and its asset for the current capture.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CheckedStorage {
    pub name: String,
    /// The frozen storage (`<frozen dir>/storage.json`).
    pub frozen_dir: PathBuf,
    pub package: ContentId,
    pub build: ContentId,
    /// The stored library object of the checked build (it built the asset; it builds tiny-case assets).
    pub library: PathBuf,
    pub asset: ContentId,
    /// The asset's parts: its trial directory, or its library directory once registered.
    pub asset_directory: PathBuf,
    /// The unregistered trial asset (`None` once the asset is the library's).
    pub trial: Option<TrialAsset>,
    /// Whether this call built the asset (false: the key already had it).
    pub asset_built_now: bool,
    /// Admission evidence: the asset build record and the tiny-input build record.
    pub evidence: Vec<ContentId>,
    /// The descriptive record returned to the author (sizes, times, parts, items, capture extension).
    pub record: Value,
}

/// Verify and compile the frozen storage `frozen` (evidence under `out`), record its checked build, refuse it if the
/// user excluded its package, build its trial asset for the current capture once, and build every tiny input of the
/// statements that read a stored table.
pub fn check_storage(ctx: &mut StorageBuildContext<'_>, frozen: &FrozenStorage, frozen_dir: &Path, out: &Path) -> Result<CheckedStorage, AdmissionError> {
    let name = frozen.name()?;
    let krate = frozen.frozen_crate(frozen_dir);
    let (run, _) = compile::compile(ctx.locks, &krate, CrateKind::Storage, &frozen.compiler, &out.join("verus"))?;
    let stdout = run["stdout"].as_str().unwrap_or_default();
    let items = declared_items(&frozen.declared_modules(stdout)?, &krate, CrateKind::Storage, stdout)?;
    let readers = items.iter().filter(|item| item["module_role"] != json!("builder")).map(item_record).collect();
    let store = ObjectStore::open(ctx.library).map_err(AdmissionError::tool)?;
    let statement = ctx.statements.first().ok_or_else(|| AdmissionError::tool("a storage is checked for a workload with statements"))?.statement();
    let schema = StorageSchema { tables: &statement.instance.doc.tables, ddl: &statement.schema_ddl, frontend: &statement.instance.doc.frontend };
    let derivation = frozen.candidate_derivation(&store)?;
    let candidate = StorageCandidate {
        name: &name,
        declaration: &frozen.declaration,
        uses_declared_constraints: frozen.manifest.uses_declared_constraints,
        derivation: derivation.as_ref(),
        frozen_root: &krate.root,
        verus_run: &run,
        readers,
        flat: false,
    };
    let clause_text = |text: &str, item: &str| requires_ensures(text, item);
    let published = publish_storage(&store, schema, &candidate, &clause_text)?;
    ctx.policy.refuse_excluded(&store, published.package)?;
    // A storage built from source columns extends the capture by any column it stores; one built from admitted
    // storages reads no source column.
    let extension = match frozen.derivation {
        None => ctx.capture.covering(&frozen.declaration)?.1,
        Some(_) => None,
    };
    let asset = workspace_asset(ctx, &store, published.package, &frozen.declaration, out)?;
    let build = records::check_build_evidence(&store, published.build).map_err(AdmissionError::tool)?;
    let library = records::library_path(&store, &build).map_err(AdmissionError::tool)?;
    let preflights: Vec<_> = ctx.statements.iter().map(|s| &s.preflight).collect();
    let tiny = match &frozen.derivation {
        None => check_storage_tiny_builds(
            ctx.runner,
            &library,
            &frozen.declaration,
            frozen.manifest.uses_declared_constraints,
            &preflights,
            &out.join("tiny-builds"),
            ctx.build_workers,
        )?,
        // Its tiny inputs are its sources' tiny assets: built and tested with every query that reads it.
        Some(derivation) if preflights.iter().any(|p| p.validation.formal) => {
            json!({"status":"not_run","reason":gendb_verification::admission::stored_execution::TINY_NOT_RUN,"derived_from":derivation})
        }
        Some(derivation) => json!({"status":"not_run","reason":"built from admitted storages: its builder's tiny inputs are its sources' tiny assets, built for the tiny cases of every query that reads it","derived_from":derivation}),
    };
    let tiny_record = store.put(1, STORAGE_TINY_BUILDS_KIND, &json!({"package":published.package,"builds":tiny})).map_err(AdmissionError::tool)?;
    let record = json!({"status":"built","name":name.as_str(),"package":published.package,"build":published.build,
        "verification":run["verification"],"verus_wall_ns":run["wall_ns"],"verus_record":out.join("verus/run.json"),
        "asset":asset.record(),
        "part_labels":frozen.manifest.parts,"layout":frozen.manifest.layout,"items":items,"tiny_builds":tiny,
        "capture_extension":extension,
        "reuse":"the checked build and its asset are reused for unchanged sources in this session and by every query that names this package; admission builds nothing"});
    Ok(CheckedStorage {
        name: name.to_string(),
        frozen_dir: frozen_dir.to_path_buf(),
        package: published.package,
        build: published.build,
        library,
        asset: asset.id,
        asset_directory: asset.directory.clone(),
        trial: asset.trial.clone(),
        asset_built_now: asset.built_now,
        evidence: vec![asset.build_evidence, tiny_record],
        record,
    })
}

/// Re-resolve the asset of a reused checked storage (`declaration`: its storage declaration; evidence of a rebuild
/// under `out`), refused if the user excluded its package since it was checked: nothing changes while it is present; a rebuild after its session removed the trial updates the
/// asset, its directory and record (`asset.rebuilt_after_reclaim`).
pub fn refresh_storage_asset(ctx: &mut StorageBuildContext<'_>, checked: &mut CheckedStorage, declaration: &DeclaredSource, out: &Path) -> Result<(), AdmissionError> {
    let store = ObjectStore::open(ctx.library).map_err(AdmissionError::tool)?;
    ctx.policy.refuse_excluded(&store, checked.package)?;
    let asset = workspace_asset(ctx, &store, checked.package, declaration, out)?;
    // The asset's own build record, also when it was found rather than built: a bench that viewed another capture
    // (`Workbench::at_capture`) leaves the record of that capture's asset here.
    checked.evidence[0] = asset.build_evidence;
    checked.asset = asset.id;
    checked.asset_directory = asset.directory.clone();
    checked.trial = asset.trial.clone();
    checked.asset_built_now = asset.built_now;
    checked.record["asset"] = asset.record();
    Ok(())
}

/// The asset of a workspace storage package for the current capture, as resolved or built now.
struct WorkspaceAsset {
    id: ContentId,
    directory: PathBuf,
    trial: Option<TrialAsset>,
    built_now: bool,
    /// The asset build record (admission evidence).
    build_evidence: ContentId,
    asset: records::VerusStorageAssetV1,
    canonical_column_bytes: u64,
    /// Free-space facts of a build: the need and what the session freed first.
    space: Value,
}

impl WorkspaceAsset {
    fn record(&self) -> Value {
        let asset = &self.asset;
        let mut record = json!({"asset":self.id,"built_now":self.built_now,"directory":self.directory,"parts":asset.parts,
            "storage_bytes":asset.storage_bytes,"build_wall_ns":asset.build_wall_ns,"key":asset.key,
            "registered":self.trial.is_none(),
            "canonical_column_bytes":self.canonical_column_bytes,
            "sizes":"storage_bytes: the stored parts; canonical_column_bytes: the stored columns at their fixed ABI widths (text: offsets only), for comparison; both descriptive"});
        if !self.space.is_null() {
            record["space"] = self.space.clone();
        }
        record
    }
}

/// The library's asset of the key once registered, else the present trial, else a new trial build: the free-space
/// guard (after freeing disposable trials of the session) and one build by the package's stored library.
fn workspace_asset(ctx: &mut StorageBuildContext<'_>, store: &ObjectStore, package_id: ContentId, declaration: &DeclaredSource, out: &Path) -> Result<WorkspaceAsset, AdmissionError> {
    let package: records::VerusStoragePackageV1 = store.read(package_id).and_then(|o| o.decode()).map_err(AdmissionError::tool)?;
    let capture = CurrentCapture::of(&ctx.capture.current()).map_err(AdmissionError::tool)?;
    let key = capture.asset_key(package_id, &package).map_err(AdmissionError::missing_input)?;
    let canonical = canonical_column_bytes(declaration, &key.tables.iter().map(|t| t.rows).collect::<Vec<_>>());
    let resolved = |id, asset: records::VerusStorageAssetV1, directory, trial: Option<TrialAsset>| WorkspaceAsset {
        id, directory, trial, built_now: false, build_evidence: asset.evidence, asset, canonical_column_bytes: canonical, space: Value::Null,
    };
    if let Some((id, asset)) = records::resolve_storage_asset(store, &key).map_err(AdmissionError::tool)? {
        let directory = records::storage_asset_directory(store, &asset).map_err(AdmissionError::tool)?;
        return Ok(resolved(id, asset, directory, None));
    }
    if let Some(trial) = ctx.trials.present(&key)? {
        return Ok(resolved(trial.id, trial.asset.clone(), trial.directory.clone(), Some(trial)));
    }
    if let Some(reused) = reuse_equal_builder(ctx, store, package_id, &package, &capture, canonical)? {
        return Ok(reused);
    }
    if ctx.asset_upkeep.is_some()
        && let Some(derivation) = package.derived_from.as_ref()
    {
        ensure_source_assets(ctx, store, derivation, &capture, out)?;
    }
    let prior = ctx.trials.prior_bytes(&key);
    let same_storage = ctx.trials.newest_bytes_of(store, &package.name).or(library_bytes_of(store, &package.name, &capture)?);
    let need = SpaceNeed::new(prior, same_storage, Some(canonical)).with_floor(ctx.asset_upkeep.map(|u| u.floor_bytes));
    // A new version of the name replaces its current version (unless an admitted query reads that one).
    let replacing = std::collections::BTreeSet::from([package.name.clone()]);
    let budget = StorageBudget::of_library_replacing(store, &capture, ctx.schema()?, ctx.policy, ctx.allowance, &replacing)?;
    check_budget_before_build(&budget, &need, &package.name)?;
    let reclaim = ctx.trials.reclaim_for(store, &need, ctx.keep)?;
    check_free_space(ctx.asset_upkeep.as_ref(), ctx.library, &ctx.trials.root(), &need, &reclaim)?;
    // A reused checked storage rebuilds here without having compiled under `out`, so `out` may not exist yet.
    std::fs::create_dir_all(out).map_err(AdmissionError::tool)?;
    let input = asset_input(store, ctx.capture, &package, declaration, &capture, out)?;
    let declared = run_constraints_digest(ctx.schema()?)?;
    let trial = build_trial_asset(store, ctx.runner, package_id, &capture, declared, input, ctx.build_workers, &ctx.trials.root(), &out.join("asset-build"))?;
    ctx.trials.record_built(package_id, &package.name, &trial)?;
    let mut built = resolved(trial.id, trial.asset.clone(), trial.directory.clone(), Some(trial));
    built.built_now = true;
    built.space = json!({"need":need,"session_reclaim":reclaim,"rebuilt_after_reclaim":prior.is_some()});
    Ok(built)
}

/// Build the asset of the admitted storage `record` (declared as `declaration`) for `capture` straight into the
/// library by its stored builder, through the held build `slot` (evidence under `out`, created before the build): the
/// storage budget's guard (a measured estimate), then the free-space guard after the session's disposable trials are
/// reclaimed. The estimate: on the general line a released asset's exact stored bytes first, then the newest measured
/// build of the same storage name, then the declared columns. On the general line (`ctx.asset_upkeep`) the build leaves
/// the shared-host floor free and a derived storage's sources get their assets for `capture` first
/// ([`ensure_source_assets`]). The one path of an admitted storage's asset for a new capture or after its release
/// (`tools::bench::Workbench::resolve_uses_as`).
#[allow(clippy::too_many_arguments)]
pub fn build_library_asset(
    ctx: &mut StorageBuildContext<'_>,
    store: &ObjectStore,
    slot: AssetBuildSlot,
    record: &records::VerusStoragePackageV1,
    declaration: &DeclaredSource,
    capture: &CurrentCapture,
    out: &Path,
) -> Result<StorageAsset, AdmissionError> {
    let upkeep = ctx.asset_upkeep;
    if upkeep.is_some()
        && let Some(derivation) = record.derived_from.as_ref()
    {
        ensure_source_assets(ctx, store, derivation, capture, out)?;
    }
    let rows: Vec<u64> = slot.key().tables.iter().map(|t| t.rows).collect();
    let released = match upkeep {
        Some(_) => records::released_storage_asset(store, slot.key()).map_err(AdmissionError::tool)?.map(|(_, release)| release.storage_bytes),
        None => None,
    };
    let same_storage = library_bytes_of(store, &record.name, capture)?;
    let need = SpaceNeed::new(released, same_storage, Some(canonical_column_bytes(declaration, &rows))).with_floor(upkeep.map(|u| u.floor_bytes));
    let budget = StorageBudget::of_library(store, capture, ctx.schema()?, ctx.policy, ctx.allowance)?;
    check_budget_before_build(&budget, &need, &record.name)?;
    let reclaim = ctx.trials.reclaim_for(store, &need, ctx.keep)?;
    check_free_space(upkeep.as_ref(), ctx.library, ctx.library, &need, &reclaim)?;
    std::fs::create_dir_all(out).map_err(AdmissionError::tool)?;
    let input = asset_input(store, ctx.capture, record, declaration, capture, out)?;
    slot.build(store, ctx.runner, input, ctx.build_workers, &out.join("asset-build"))
}

/// The general line: every derivation source of a storage (`derivation`) with its published asset for `capture`
/// before the storage is built from them. A source whose asset was released, or was never built for this capture, is
/// built first by its stored builder ([`build_library_asset`], its own sources first; evidence under
/// `<out>/source-<name>`). A flat source without an asset is refused by name: its asset comes only from
/// `gendb prepare-flat-storage`.
pub fn ensure_source_assets(ctx: &mut StorageBuildContext<'_>, store: &ObjectStore, derivation: &records::VerusDerivationV1, capture: &CurrentCapture, out: &Path) -> Result<(), AdmissionError> {
    for source in &derivation.sources {
        let declared = run_constraints_digest(ctx.schema()?)?;
        match lookup_storage_asset(store, source.package, capture, declared)? {
            AssetLookup::Published(_) => {}
            AssetLookup::Absent(_) if super::flat::flat_ineligibility(store, source.package, &source.name)?.is_none() => return Err(super::flat::not_prepared(&source.name)),
            AssetLookup::Absent(slot) => {
                let (record, declaration) = super::catalog::admitted_storage(store, source.package)?;
                build_library_asset(ctx, store, slot, &record, &declaration, capture, &out.join(format!("source-{}", source.name)))?;
            }
        }
    }
    Ok(())
}

/// The builder input of one asset build of `package` for `capture` (evidence under `out`): the published assets of its
/// admitted sources when it is built from admitted storages (no source column is read), else its declared columns
/// from the capture, extended first by any column it stores that is not captured yet.
pub fn asset_input(
    store: &ObjectStore,
    shared: &SharedCapture,
    package: &records::VerusStoragePackageV1,
    declaration: &DeclaredSource,
    capture: &CurrentCapture,
    out: &Path,
) -> Result<gendb_runtime::worker::WorkerInput, AdmissionError> {
    if package.derived_from.is_some() {
        return derived_storage_input(store, package, capture);
    }
    let (source, _) = shared.covering(declaration)?;
    storage_input(&source, package, &out.join("storage-input"))
}

/// How the tiny-case assets of a storage with the checked library `library` are built: from columns, or (built from
/// admitted storages, `derivation`) from its sources' tiny assets, each source's own builder resolved from the library.
pub fn tiny_builder(store: &ObjectStore, library: &Path, derivation: Option<&records::VerusDerivationV1>) -> Result<TinyBuilder, AdmissionError> {
    let Some(derivation) = derivation else { return Ok(TinyBuilder::Columns { library: library.to_path_buf() }) };
    let mut sources = vec![];
    for source in &derivation.sources {
        let record = records::resolve_admitted_storage(store, source.package).map_err(AdmissionError::tool)?;
        let build = records::check_build_evidence(store, record.build).map_err(AdmissionError::tool)?;
        let source_library = records::library_path(store, &build).map_err(AdmissionError::tool)?;
        sources.push(TinySource {
            name: source.name.clone(),
            declaration: serde_json::from_value(record.declaration.clone()).map_err(AdmissionError::tool)?,
            builder: tiny_builder(store, &source_library, record.derived_from.as_ref())?,
            assumes_declared_constraints: record.assumed_constraints.is_some(),
        });
    }
    Ok(TinyBuilder::Derived { library: library.to_path_buf(), sources, extends: derivation.extends })
}

/// Refuse a build whose measured size estimate (an earlier build of the same key or storage name) already exceeds what
/// the storage budget leaves (`storage_budget_exceeded`, before anything is built). A canonical-width estimate refuses
/// nothing here: the measured bytes decide at registration.
pub fn check_budget_before_build(budget: &StorageBudget, need: &SpaceNeed, name: &str) -> Result<(), AdmissionError> {
    match (need.basis, need.estimate_bytes) {
        ("prior_same_key" | "same_storage_measured", Some(estimate)) => {
            budget.check_room(estimate, &format!("building storage {name} (measured estimate, basis {})", need.basis))
        }
        _ => Ok(()),
    }
}

/// Measured stored bytes of the newest admitted version (newest first) of storage `name` with an asset for `capture` (a size
/// estimate for a new version of the same storage).
pub fn library_bytes_of(store: &ObjectStore, name: &str, capture: &CurrentCapture) -> Result<Option<u64>, AdmissionError> {
    for (_, admission) in records::storage_versions(store, name).map_err(AdmissionError::tool)? {
        let package: records::VerusStoragePackageV1 = store.read(admission.package).and_then(|o| o.decode()).map_err(AdmissionError::tool)?;
        if let Ok(key) = capture.asset_key(admission.package, &package)
            && let Some((_, asset)) = records::resolve_storage_asset(store, &key).map_err(AdmissionError::tool)?
        {
            return Ok(Some(asset.storage_bytes));
        }
    }
    Ok(None)
}

/// The trial asset of `package_id` made by hard links from an asset of another package of the same storage name with
/// the same builder identity (`storage::identity`): a published library asset for this capture, or a present trial of
/// this session of a package in this library (newest first; `query::assets`, "Libraries"). `None` when there is none:
/// the caller builds.
fn reuse_equal_builder(
    ctx: &mut StorageBuildContext<'_>,
    store: &ObjectStore,
    package_id: ContentId,
    package: &records::VerusStoragePackageV1,
    capture: &CurrentCapture,
    canonical: u64,
) -> Result<Option<WorkspaceAsset>, AdmissionError> {
    let identity = builder_identity(store, package)?;
    let mut candidates: Vec<(ContentId, ContentId, PathBuf, u64)> = vec![];
    for (_, admission) in records::storage_versions(store, &package.name).map_err(AdmissionError::tool)? {
        let other: records::VerusStoragePackageV1 = store.read(admission.package).and_then(|o| o.decode()).map_err(AdmissionError::tool)?;
        if admission.package == package_id {
            continue;
        }
        if let Ok(key) = capture.asset_key(admission.package, &other)
            && let Some((asset_id, asset)) = records::resolve_storage_asset(store, &key).map_err(AdmissionError::tool)?
        {
            let directory = records::storage_asset_directory(store, &asset).map_err(AdmissionError::tool)?;
            candidates.push((admission.package, asset_id, directory, asset.build_wall_ns));
        }
    }
    for (other, trial) in ctx.trials.present_of_name(store, &package.name) {
        if other != package_id && capture.asset_key(other, &store.read(other).and_then(|o| o.decode()).map_err(AdmissionError::tool)?).ok().as_ref() == Some(&trial.asset.key) {
            candidates.push((other, trial.id, trial.directory.clone(), trial.asset.build_wall_ns));
        }
    }
    for (other, asset_id, directory, wall_ns) in candidates {
        let record: records::VerusStoragePackageV1 = store.read(other).and_then(|o| o.decode()).map_err(AdmissionError::tool)?;
        if builder_identity(store, &record)? != identity {
            continue;
        }
        let reuse = json!({"builder_identity":identity,"from_package":other,"from_asset":asset_id,
            "basis":"equal builder identity: byte-identical source files compiled with the same toolchain, configuration and codegen options, over the same input (storage::identity); the parts are shared by hard links"});
        let declared = run_constraints_digest(ctx.schema()?)?;
        let trial = link_trial_asset(store, package_id, capture, declared, &directory, wall_ns, reuse.clone(), &ctx.trials.root())?;
        ctx.trials.record_built(package_id, &package.name, &trial)?;
        return Ok(Some(WorkspaceAsset {
            id: trial.id,
            directory: trial.directory.clone(),
            build_evidence: trial.asset.evidence,
            asset: trial.asset.clone(),
            trial: Some(trial),
            built_now: false,
            canonical_column_bytes: canonical,
            space: json!({"reused_by_hard_links":reuse}),
        }));
    }
    Ok(None)
}

/// Bytes of the stored columns at their fixed ABI widths (`rows[j]`: stored table `j`'s rows); text counts its
/// offsets only. Descriptive.
pub fn canonical_column_bytes(declaration: &DeclaredSource, rows: &[u64]) -> u64 {
    let width = |kind: ColumnKind| -> u64 {
        match kind {
            ColumnKind::I32 => 4,
            ColumnKind::I64 | ColumnKind::Utf8 => 8,
            ColumnKind::I128 => 16,
        }
    };
    declaration
        .tables
        .iter()
        .zip(rows)
        .map(|(t, rows)| t.columns.iter().filter(|c| !c.row_count_only).map(|c| width(c.ty.kind())).sum::<u64>() * rows)
        .sum()
}
