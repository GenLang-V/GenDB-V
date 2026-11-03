//! Unverified diagnostic storage builds ("measure first, prove later"): `storage_build` with
//! `verification: "not_run"`, and the workspace storages of a `not_run` trial.
//!
//! The storage crate is frozen exactly as for a verified build (manifest, source rules, framework files), then compiled
//! with `rust_verify --no-verify`; its builder runs once over the current data in the worker child and writes its parts
//! into the session's `diagnostic-assets/<name>/`, apart from the library and from trial assets. Nothing is recorded
//! in the library: no build, package or asset record exists, so such parts can never be registered, admitted,
//! submitted or served, and they are not counted in the storage budget. Every result says `diagnostic_unverified`.
//!
//! Disk: one diagnostic build per storage name per session; a newer build of the name replaces the older one (it is
//! removed first), the same sources reuse it, and the session removes them all at close. Before a build the free space
//! must hold the margin plus a size estimate (`query::assets::SpaceNeed`); on the general engine line the shared-host
//! floor instead of the margin, after the session's disposable trials are reclaimed (`storage::asset_release`).

use super::freeze::FrozenStorage;
use super::asset_release::{AssetUpkeep, check_free_space};
use crate::query::assets::SpaceNeed;
use crate::query::compile;
use crate::query::host_locks::HostLocks;
use super::capture::SharedCapture;
use super::build::canonical_column_bytes;
use gendb_artifacts::asset_directory::remove_build_directory;
use gendb_artifacts::{ContentId, ObjectStore, content_id};
use gendb_storage::versions::CurrentCapture;
use gendb_registry::CrateKind;
use gendb_verification::admission::AdmissionError;
use gendb_verification::admission::execution::CandidateRunner;
use gendb_verification::admission::storage::{build_diagnostic_parts, declared_storage_input, derivation_input};
use gendb_verification::obligations::DeclaredSource;
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

/// The session directory of diagnostic builds.
pub const DIAGNOSTIC_ASSETS_DIRECTORY: &str = "diagnostic-assets";
/// The label of every diagnostic storage result.
pub const DIAGNOSTIC_LABEL: &str = "diagnostic_unverified";
const NOTE: &str = "UNVERIFIED diagnostic storage build: compiled with rust_verify --no-verify (no proof obligation checked); its parts are real and measured, but they are no asset: never registered, admitted, submitted or served, and not counted in the storage budget. Prove the chosen design with storage_build (verified) before submitting";

/// One diagnostic build.
#[derive(Clone, Debug)]
pub struct DiagnosticStorage {
    pub name: String,
    /// Identity of the frozen sources it was built from (also its pseudo package id in trial records).
    pub sources: ContentId,
    pub declaration: DeclaredSource,
    /// The unverified library (it also builds tiny-case parts in trials).
    pub library: PathBuf,
    pub directory: PathBuf,
    pub storage_bytes: u64,
    pub build_wall_ns: u64,
    pub record: Value,
}

/// What a diagnostic build needs from its session.
pub struct DiagnosticContext<'a> {
    /// The library holding the admitted sources of a storage built from admitted storages.
    pub library: &'a Path,
    pub locks: &'a HostLocks,
    pub runner: &'a CandidateRunner,
    pub capture: &'a SharedCapture,
    pub build_workers: u32,
    /// The general line's upkeep (`storage::asset_release`): the build leaves the shared-host floor free, after
    /// `reclaim` frees the session's disposable trials; `None` elsewhere (the margin, nothing reclaimed).
    pub asset_upkeep: Option<AssetUpkeep>,
    /// The session's trial reclaim for a need (`query::assets::TrialAssets::reclaim_for`), used only with an upkeep.
    pub reclaim: &'a mut dyn FnMut(&SpaceNeed) -> Result<Value, AdmissionError>,
}

/// The diagnostic builds of one session (see the module documentation).
pub struct DiagnosticStorages {
    root: PathBuf,
    by_name: BTreeMap<String, DiagnosticStorage>,
}

impl DiagnosticStorages {
    /// The session's diagnostic builds under `<session>/diagnostic-assets`; leftovers of an earlier process are removed
    /// (they are disposable and nothing refers to them).
    pub fn open(session: &Path) -> Result<Self, AdmissionError> {
        let root = session.join(DIAGNOSTIC_ASSETS_DIRECTORY);
        remove_build_directory(&root).map_err(AdmissionError::tool)?;
        Ok(Self { root, by_name: BTreeMap::new() })
    }

    /// The diagnostic build of `frozen` (frozen under `frozen_dir`; evidence under `out`): the session's build of equal
    /// sources, or a new unverified compile and build replacing the name's older one. `(build, reused)`.
    pub fn build(&mut self, ctx: &mut DiagnosticContext<'_>, frozen: &FrozenStorage, frozen_dir: &Path, out: &Path) -> Result<(DiagnosticStorage, bool), AdmissionError> {
        let name = frozen.manifest.name.clone();
        let sources = content_id(1, "gendb.diagnostic-storage-sources.v1", &frozen.source_key(frozen_dir)?).map_err(AdmissionError::tool)?;
        if let Some(existing) = self.by_name.get(&name).filter(|d| d.sources == sources && d.directory.join("parts.json").is_file()) {
            return Ok((existing.clone(), true));
        }
        let previous_bytes = self.by_name.get(&name).map(|d| d.storage_bytes);
        self.remove(&name)?;
        std::fs::create_dir_all(out).map_err(AdmissionError::tool)?;
        let krate = frozen.frozen_crate(frozen_dir);
        let (run, library) = compile::compile_unverified(ctx.locks, &krate, CrateKind::Storage, &frozen.compiler, &out.join("verus"))?;
        // A storage built from admitted storages reads their published assets (as its verified build does); any other
        // reads the declared source columns, extending the capture when needed.
        let (input, extension, rows) = match &frozen.derivation {
            Some(derivation) => {
                let store = ObjectStore::open_existing(ctx.library).map_err(AdmissionError::tool)?;
                let current = CurrentCapture::of(&ctx.capture.current()).map_err(AdmissionError::tool)?;
                let source = ctx.capture.current();
                let rows: Vec<u64> = frozen.declaration.tables.iter().map(|t| source.row_count(&t.name).unwrap_or(0) as u64).collect();
                (derivation_input(&store, &name, derivation, &current)?, None, rows)
            }
            None => {
                let (source, extension) = ctx.capture.covering(&frozen.declaration)?;
                let input = declared_storage_input(&source, &frozen.declaration, &out.join("storage-input"))?;
                let rows: Vec<u64> = frozen.declaration.tables.iter().map(|t| source.row_count(&t.name).unwrap_or(0) as u64).collect();
                (input, extension, rows)
            }
        };
        let need = SpaceNeed::new(None, previous_bytes, Some(canonical_column_bytes(&frozen.declaration, &rows))).with_floor(ctx.asset_upkeep.map(|u| u.floor_bytes));
        let reclaim = match ctx.asset_upkeep {
            Some(_) => json!({"diagnostic_builds":"not reclaimed for space; a newer build of the same name replaced the older","session_trials":(ctx.reclaim)(&need)?}),
            None => json!("diagnostic builds are not reclaimed for space; a newer build of the same name replaced the older"),
        };
        check_free_space(ctx.asset_upkeep.as_ref(), ctx.library, &self.root, &need, &reclaim)?;
        let directory = self.root.join(&name);
        let built = build_diagnostic_parts(ctx.runner, &library, input, ctx.build_workers, &directory, &out.join("asset-build"))?;
        let record = json!({"status":DIAGNOSTIC_LABEL,"verification":"verification_not_run","name":name,"sources":sources,
            "parts":built.parts.parts,"storage_bytes":built.parts.storage_bytes,"build_wall_ns":built.build_wall_ns,"column_rows":built.column_rows,
            "canonical_column_bytes":need.estimate_bytes.filter(|_| need.basis == "canonical_columns"),"directory":directory,"library":library,
            "compile":{"wall_ns":run["wall_ns"],"argv":run["argv"],"record":out.join("verus/run.json")},"space":need,"capture_extension":extension,"note":NOTE});
        let storage = DiagnosticStorage {
            name: name.clone(),
            sources,
            declaration: frozen.declaration.clone(),
            library,
            directory,
            storage_bytes: built.parts.storage_bytes,
            build_wall_ns: built.build_wall_ns,
            record,
        };
        self.by_name.insert(name, storage.clone());
        Ok((storage, false))
    }

    /// Remove the diagnostic build of `name`, if any.
    fn remove(&mut self, name: &str) -> Result<(), AdmissionError> {
        if let Some(old) = self.by_name.remove(name) {
            remove_build_directory(&old.directory).map_err(AdmissionError::tool)?;
        }
        Ok(())
    }

    /// At session close: remove every diagnostic build; what was removed.
    pub fn release(&mut self) -> Result<Value, AdmissionError> {
        let names: Vec<String> = self.by_name.keys().cloned().collect();
        let removed: Vec<Value> = names.iter().map(|n| json!({"name":n,"bytes":self.by_name[n].storage_bytes})).collect();
        for name in names {
            self.remove(&name)?;
        }
        Ok(json!({"removed_diagnostic_builds":removed}))
    }
}
