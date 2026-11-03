//! The work bench of one author session: the state its local jobs and its controller stages share on the retained
//! owner thread, and the one implementation of every tool action for both roles.
//!
//! It holds the session's statements (one for a query author, every workload statement for the storage author), the
//! run's shared capture, the library, the host locks and two session caches: checked storages by source key (each
//! verified, recorded and built once) and compiled query libraries by build mode and source key (a verified build is
//! never answered with an unverified diagnostic library). The roles call the same methods for
//! their submissions (`check_storage`, `resolve_storages`, `register`), so a tool run and an official evaluation of
//! unchanged sources never build a storage twice.

use super::{AuthorRole, LocalJobArguments, LocalToolContext, ToolAction, ToolStatement, TrialVerification, CONTEXT_FORMAT};
use crate::controller::author::{CandidateSubmission, resolve_candidate_manifest};
use crate::controller::records::write_new_json;
use crate::controller::session::LocalSessionEndpoint;
use crate::prompts::brief;
use crate::query::QuerySession;
use crate::query::candidate::{self, FrozenCandidate, QueryFreeze, StorageSource, crate_version};
use crate::query::compile::{self, declared_items};
use crate::query::evaluation::{ResolvedStorage, TrialKind};
use crate::query::host_locks::HostLocks;
use crate::query::assets::TrialAssets;
use crate::storage::asset_release::AssetUpkeep;
use crate::storage::build::{CheckedStorage, StorageBuildContext, build_library_asset, check_storage, ensure_source_assets, refresh_storage_asset};
use crate::storage::capture::SharedCapture;
use crate::storage::budget::{StorageBudget, serving_storages};
use crate::storage::library_lock::{BUDGET_LOCK, LibraryLock, reverification_lock};
use crate::storage::catalog::{self, coverage_of};
use crate::storage::coverage::{check_lossless_coverage, coverage_report};
use crate::storage::diagnostic::{DiagnosticContext, DiagnosticStorage, DiagnosticStorages};
use crate::storage::reverify::{ClosureState, REVERIFICATION_KIND, closure_state, content_matches, materialize, recorded_reverification};
use crate::storage::freeze::{self, FrozenStorage, freeze_storage, read_manifest, storage_framework, write_workspace_framework};
use crate::storage::payload::{PayloadHolder, added_to, check_single_copy, column_report, payload_holders, payload_of_serving, recorded_storages, serving_payload};
use crate::storage::flat;
use crate::storage::policy::{StoredDataPolicy, recorded_standing};
use crate::storage::registration::{Registration, register_storage};
use gendb_artifacts::verus as records;
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_frontend::parser::SqlParser;
use gendb_registry::CrateKind;
use gendb_storage::versions::CurrentCapture;
use gendb_verification::admission::AdmissionError;
use gendb_verification::admission::execution::CandidateRunner;
use gendb_verification::admission::storage::{
    AssetLookup, check_storage_assumptions, lookup_storage_asset, promote_trial_asset, run_constraints_digest,
};
use gendb_verification::obligations::{DeclaredSource, StorageName};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;

/// Where a session works and what it may use.
pub struct BenchConfig {
    /// The admitted library (read for catalogs; storages and queries are recorded and admitted into it).
    pub library: PathBuf,
    pub locks: HostLocks,
    pub parser: SqlParser,
    /// The user's hard limit on the serving bytes of all usable admitted storages together (request
    /// `data_allowance.live_bytes`; `storage::budget`); `None`: no limit.
    pub live_bytes_allowance: Option<u64>,
    /// The user's stored-data policy: required declarations, the kind recorded at registration, usable admitted storages.
    pub storage_policy: StoredDataPolicy,
    /// The general engine line's upkeep of storage assets on the shared host (`storage::asset_release`): every asset
    /// build leaves the shared-host floor free (diagnostic builds reclaim the session's disposable trials first, as
    /// the others do), a released asset's derivation sources are built first, and a refusal states what the library
    /// keeps. `None` on the schema and per-query lines (the 4 GiB margin).
    pub asset_upkeep: Option<AssetUpkeep>,
}

/// One session's bench (see the module documentation).
pub struct Workbench {
    pub config: BenchConfig,
    pub capture: SharedCapture,
    pub statements: Vec<Arc<QuerySession>>,
    endpoint: Option<LocalSessionEndpoint>,
    workspace: Option<PathBuf>,
    storages: BTreeMap<Vec<u8>, CheckedStorage>,
    /// Compiled query libraries by (build mode, source key).
    query_builds: BTreeMap<(TrialVerification, Vec<u8>), (PathBuf, Value)>,
    /// Whole-crate verifications that passed, by source key (a verify of identical content is not run again).
    verified_queries: BTreeMap<Vec<u8>, Value>,
    /// Tiny-case runs that passed, by (build mode, query source key, storage assets): identical code over identical
    /// assets is not tested again.
    /// Tiny cases passed per (verification, crate source key, storage assets, worker count of the trial: `None` = every
    /// configured count).
    tiny_cases_passed: BTreeSet<(TrialVerification, Vec<u8>, Vec<ContentId>, Option<usize>)>,
    /// The session's trial assets (opened with the workspace).
    trials: Option<TrialAssets>,
    /// The session's unverified diagnostic storage builds (opened with the workspace).
    diagnostics: Option<DiagnosticStorages>,
    /// The role this bench serves (set with its tool context): a query author's new storages are built from admitted
    /// storages.
    role: Option<AuthorRole>,
    /// Stale admitted storages re-verified in this session: old package -> its current version.
    reverified: BTreeMap<ContentId, ContentId>,
}

/// What a refreshed budget and catalog mean (CURRENT FACTS, Storage and the `catalog` tool).
pub const SHARED_FACTS_MEANING: &str = "a snapshot of the library when it was read (before this call, or when you ran catalog), not a reservation: other sessions may admit storages at any time, and registration enforces the actual budget then (storage_budget_exceeded). Newly admitted versions are listed in storages.json with their interface copies under admitted-storages/; the search index stays as prepared for this session";

/// The label of every result of an unverified diagnostic build (`verification: "not_run"`).
pub const UNVERIFIED_LABEL: &str = "verification_not_run";

/// What an unverified trial or profile result means (in every such result).
const UNVERIFIED_NOTE: &str = "diagnostic_unverified: this library was compiled with rust_verify --no-verify, so no proof obligation of the query crate was checked; the run and comparison are real, but the result is never a submission, proof, official measurement or early-stop input. A submission of the same code is verified whole and tested from scratch";


/// A frozen query candidate with its statement.
pub struct FrozenQuery {
    pub statement: usize,
    pub candidate: FrozenCandidate,
    pub frozen_dir: PathBuf,
}

/// The storage uses of a frozen crate, checked and not yet registered ([`Workbench::check_workspace_uses`]).
pub struct CheckedUses {
    /// `(name, package, registration)` in use order; a workspace storage's registration is set once it is registered.
    pub uses: Vec<(String, ContentId, Option<Registration>)>,
    /// Each workspace storage: its index in `uses`, its checked storage and its frozen storage.
    pub workspace: Vec<(usize, CheckedStorage, FrozenStorage)>,
}

impl CheckedUses {
    /// The uses with the registrations of the workspace storages (in `workspace` order).
    pub fn registered(self, registrations: Vec<Registration>) -> Vec<(String, ContentId, Option<Registration>)> {
        let mut uses = self.uses;
        for ((index, _, _), registration) in self.workspace.iter().zip(registrations) {
            uses[*index].1 = registration.package;
            uses[*index].2 = Some(registration);
        }
        uses
    }
}

impl Workbench {
    pub fn new(config: BenchConfig, capture: SharedCapture, statements: Vec<Arc<QuerySession>>) -> Self {
        Self { config, capture, statements, endpoint: None, workspace: None, storages: BTreeMap::new(), query_builds: BTreeMap::new(), verified_queries: BTreeMap::new(), tiny_cases_passed: BTreeSet::new(), trials: None, diagnostics: None, role: None, reverified: BTreeMap::new() }
    }

    pub fn attach(&mut self, endpoint: &LocalSessionEndpoint) {
        self.endpoint = Some(endpoint.clone());
    }

    /// Create the workspace, remember its canonical path and open the session's trial assets.
    pub fn open_workspace(&mut self, workspace: &Path) -> Result<PathBuf, AdmissionError> {
        fs::create_dir_all(workspace).map_err(AdmissionError::tool)?;
        let workspace = workspace.canonicalize().map_err(AdmissionError::tool)?;
        self.workspace = Some(workspace.clone());
        self.trials = Some(TrialAssets::open(&self.session_root()?)?);
        self.diagnostics = Some(DiagnosticStorages::open(&self.session_root()?)?);
        Ok(workspace)
    }

    /// Run `work` with this bench viewing another capture of the run's data (`capture`, with that capture's prepared
    /// `statements`), then restore its own capture and statements whatever `work` returns. Storages resolve there with
    /// the session's checked storages (`refresh_storage_asset`: a workspace storage's asset for that capture is found or
    /// built by its verified builder, the asset of this bench's capture kept), and admitted storages as at a scale move.
    /// The general line's development evaluation checks variants this way at the ladder's first scale
    /// (`engine::acceptance`).
    pub fn at_capture<T>(&mut self, capture: SharedCapture, statements: Vec<Arc<QuerySession>>, work: impl FnOnce(&mut Self) -> T) -> T {
        let own_capture = std::mem::replace(&mut self.capture, capture);
        let own_statements = std::mem::replace(&mut self.statements, statements);
        let outcome = work(self);
        self.capture = own_capture;
        self.statements = own_statements;
        outcome
    }

    pub fn workspace(&self) -> Result<&Path, AdmissionError> {
        self.workspace.as_deref().ok_or_else(|| AdmissionError::missing_input("the author workspace is not prepared"))
    }

    /// The session's run directory (the parent of the author workspace).
    pub fn session_root(&self) -> Result<PathBuf, AdmissionError> {
        self.workspace()?.parent().map(Path::to_path_buf).ok_or_else(|| AdmissionError::tool("author workspace without a session directory"))
    }

    pub fn store(&self) -> Result<ObjectStore, AdmissionError> {
        ObjectStore::open(&self.config.library).map_err(AdmissionError::tool)
    }

    pub fn runner(&self) -> &CandidateRunner {
        &self.statements[0].runner
    }

    pub fn worker_counts(&self) -> &[usize] {
        &self.statements[0].worker_counts
    }

    fn build_workers(&self) -> Result<u32, AdmissionError> {
        self.statements[0].build_workers()
    }

    /// The dataset schema (`doc.tables`), shared by every statement of the workload.
    pub fn schema(&self) -> &[gendb_frontend::ast::TableDef] {
        &self.statements[0].statement().instance.doc.tables
    }

    /// `local-tool.json` of this session.
    pub fn tool_context(&mut self, role: AuthorRole, author_contract: PathBuf) -> Result<LocalToolContext, AdmissionError> {
        self.role = Some(role);
        let endpoint = self.endpoint.clone().ok_or_else(|| AdmissionError::tool("the retained local session is not attached"))?;
        let statements = self
            .statements
            .iter()
            .enumerate()
            .map(|(index, s)| ToolStatement { index, statement_key: s.statement().key_v4_id.clone(), sql: s.statement().sql.clone(), name: None })
            .collect();
        Ok(LocalToolContext {
            format_version: CONTEXT_FORMAT,
            role,
            author_workspace: self.workspace()?.to_path_buf(),
            session_service: endpoint,
            worker_counts: self.worker_counts().to_vec(),
            statements,
            author_contract,
            fixed_flat: self.config.storage_policy.is_fixed_flat(),
            engine_bindings: vec![],
            workloads: vec![],
        })
    }

    // ------------------------------------------------------------------------------------------------ storages

    /// The checked storage of `frozen` (frozen under `frozen_dir`): the session's earlier result for equal sources
    /// (its asset re-resolved, rebuilt if the session removed its trial), or a new check and build with evidence under
    /// `out`. `keep`: assets the asking job uses, never removed to make room. `(checked, reused)`. A storage without the
    /// declaration the storage policy requires, or declaring a column another serving storage already stores, is
    /// refused before anything is built ([`Workbench::check_policy_before_build`]); one whose package the user
    /// excluded is refused before its asset is built (`storage::build`).
    pub fn check_storage(&mut self, frozen: &FrozenStorage, frozen_dir: &Path, out: &Path, keep: &BTreeSet<ContentId>) -> Result<(CheckedStorage, bool), AdmissionError> {
        self.check_storage_as(frozen, frozen_dir, out, keep, false)
    }

    /// [`Workbench::check_storage`]; `reverification`: the re-verification of an admitted storage (its sources are its
    /// own, so a query session may re-verify a storage built from source columns; it has the re-verified package's
    /// policy standing, so the current declaration rules and the one-copy check do not apply to it).
    fn check_storage_as(&mut self, frozen: &FrozenStorage, frozen_dir: &Path, out: &Path, keep: &BTreeSet<ContentId>, reverification: bool) -> Result<(CheckedStorage, bool), AdmissionError> {
        if !reverification {
            self.check_policy_before_build(&[frozen])?;
        }
        self.refuse_query_storage_from_source(frozen, reverification)?;
        let key = frozen.source_key(frozen_dir)?;
        let build_workers = self.build_workers()?;
        let mut context = StorageBuildContext {
            library: &self.config.library,
            locks: &self.config.locks,
            runner: &self.statements[0].runner,
            capture: &self.capture,
            statements: &self.statements,
            build_workers,
            trials: self.trials.as_mut().ok_or_else(|| AdmissionError::missing_input("the author workspace is not prepared"))?,
            keep,
            policy: &self.config.storage_policy,
            allowance: self.config.live_bytes_allowance,
            asset_upkeep: self.config.asset_upkeep,
        };
        if let Some(mut checked) = self.storages.get(&key).cloned() {
            refresh_storage_asset(&mut context, &mut checked, &frozen.declaration, out)?;
            self.storages.insert(key, checked.clone());
            return Ok((checked, true));
        }
        let checked = check_storage(&mut context, frozen, frozen_dir, out)?;
        self.storages.insert(key, checked.clone());
        Ok((checked, false))
    }

    /// The assets of the session's checked storages among `storages` (`(frozen dir, storage)`): what a job over them
    /// keeps while it builds the others.
    pub fn checked_assets<'a>(&self, storages: impl IntoIterator<Item = (&'a Path, &'a FrozenStorage)>) -> BTreeSet<ContentId> {
        storages
            .into_iter()
            .filter_map(|(dir, storage)| storage.source_key(dir).ok())
            .filter_map(|key| self.storages.get(&key).map(|checked| checked.asset))
            .collect()
    }

    /// Admit one checked storage ([`Workbench::register_all`]).
    pub fn register(&mut self, checked: &mut CheckedStorage, frozen: &FrozenStorage, registered_by: Value) -> Result<Registration, AdmissionError> {
        let mut registrations = self.register_all(vec![(checked, frozen)], registered_by)?;
        registrations.pop().ok_or_else(|| AdmissionError::tool("one storage registered nothing"))
    }

    /// Admit the checked storages of one submission (the one registration path; builds nothing). Under the library's
    /// budget lock, their new assets together are first checked against the storage budget
    /// ([`Workbench::check_new_storage_bytes`]); none is registered when they do not fit. Each trial asset is then
    /// published by promotion (its sealed directory renamed into the library, same asset id; `checked` and the session
    /// cache then name the library directory), and the run's storage policy standing (kind and revision) is recorded
    /// with the author's description. Under the same lock the storages must also keep one copy of each column
    /// ([`Workbench::check_new_storage_payload`]). A re-verification (`registered_by.reverification_of`) records the
    /// standing of the package it re-verifies and is not a new copy.
    pub fn register_all(&mut self, storages: Vec<(&mut CheckedStorage, &FrozenStorage)>, registered_by: Value) -> Result<Vec<Registration>, AdmissionError> {
        let store = self.store()?;
        let budget_lock = LibraryLock::acquire(&store, BUDGET_LOCK)?;
        let new: Vec<(String, ContentId, PathBuf)> = storages.iter().map(|(c, _)| (c.name.clone(), c.package, c.asset_directory.clone())).collect();
        self.check_new_storage_bytes(&store, &new, "registering")?;
        let reverifies: Option<ContentId> = serde_json::from_value(registered_by["reverification_of"].clone()).ok();
        let standing = match (reverifies, storages.first()) {
            (Some(original), Some((checked, _))) => recorded_standing(&catalog::description_of(&store, original, &checked.name)?),
            _ => {
                self.check_new_storage_payload(&store, &storages.iter().map(|(c, f)| (*f, c.package)).collect::<Vec<_>>())?;
                self.config.storage_policy.standing()
            }
        };
        self.register_checked(&store, &budget_lock, storages, &registered_by, &standing)
    }

    /// Publish and admit checked storages whose budget and storage policy the caller has already checked while holding
    /// the library's budget lock `_budget_lock` (still held): each trial asset promoted into the library, then its
    /// admission with `standing` and the author's description. [`Workbench::register_all`] checks with this library's
    /// serving rule; an engine submission checks with the engine rule (`storage::engine_library::
    /// check_engine_storage_uses`: the serving storage as it stands once its version is selected) and registers here.
    pub fn register_checked(
        &mut self,
        store: &ObjectStore,
        _budget_lock: &LibraryLock,
        storages: Vec<(&mut CheckedStorage, &FrozenStorage)>,
        registered_by: &Value,
        standing: &Value,
    ) -> Result<Vec<Registration>, AdmissionError> {
        let mut registrations = vec![];
        for (checked, frozen) in storages {
            if let Some(trial) = checked.trial.clone() {
                let promoted = promote_trial_asset(store, &trial)?;
                self.trials.as_mut().ok_or_else(|| AdmissionError::tool("trial assets are not open"))?.record_promoted(trial.id)?;
                checked.trial = None;
                checked.asset_directory = promoted.directory.clone();
                checked.record["asset"]["directory"] = json!(promoted.directory);
                checked.record["asset"]["registered"] = json!(true);
                for cached in self.storages.values_mut().filter(|c| c.package == checked.package) {
                    cached.trial = None;
                    cached.asset_directory = checked.asset_directory.clone();
                    cached.record["asset"] = checked.record["asset"].clone();
                }
            }
            let mut description = freeze::description(frozen, registered_by.clone());
            for (field, value) in standing.as_object().into_iter().flatten() {
                description[field] = value.clone();
            }
            registrations.push(register_storage(store, &checked.name, checked.package, checked.asset, &checked.evidence, &description)?);
        }
        Ok(registrations)
    }

    /// Refuse (`storage_budget_exceeded`) when the new storages `new` (`(name, package, asset parts directory)`; one
    /// already admitted adds nothing) would take the serving storage over the user's budget: their part files not
    /// counted yet, each once, against the budget as it stands after they are registered (each replaces its name's
    /// current version unless an admitted query reads that version). `what` names the step. Returns the check's facts.
    pub fn check_new_storage_bytes(&self, store: &ObjectStore, new: &[(String, ContentId, PathBuf)], what: &str) -> Result<Value, AdmissionError> {
        let mut fresh = vec![];
        for (name, package, directory) in new {
            let admitted = records::storage_versions(store, name).map_err(AdmissionError::tool)?.iter().any(|(_, a)| a.package == *package);
            if !admitted {
                fresh.push((name, directory));
            }
        }
        let replacing: BTreeSet<String> = fresh.iter().map(|(name, _)| (*name).clone()).collect();
        let capture = CurrentCapture::of(&self.capture.current()).map_err(AdmissionError::tool)?;
        let mut budget = StorageBudget::of_library_replacing(store, &capture, self.schema(), &self.config.storage_policy, self.config.live_bytes_allowance, &replacing)?;
        let used_after_replacement = budget.used_bytes;
        let mut new_bytes = 0u64;
        for (_, directory) in &fresh {
            new_bytes = new_bytes.saturating_add(budget.add_new(directory)?);
        }
        let names: Vec<&String> = fresh.iter().map(|(name, _)| *name).collect();
        budget.check_room(new_bytes, &format!("{what} the new storages {names:?} (their assets' part files not yet counted)"))?;
        Ok(json!({"new_storages":names,"new_bytes":new_bytes,"used_bytes_after_replacement":used_after_replacement,"allowance_bytes":budget.allowance,
            "left_bytes_after":budget.allowance.map(|a| a.saturating_sub(used_after_replacement.saturating_add(new_bytes)))}))
    }

    /// The run's storage policy before a storage candidate is verified or built (`storage_check`, `storage_build`,
    /// every check of a submission's storages): each candidate's `data_policy` declaration
    /// (`StoredDataPolicy::check_declaration`), and under `physical_only` one copy of each column
    /// (`storage::payload`) among `candidates` and against the serving storages of other names. Versions of a
    /// candidate's own name are decided once its package is known ([`Workbench::check_new_storage_payload`]).
    ///
    /// In an engine session the serving storage once a version is selected is exactly the storages that version reads,
    /// so a storage is checked here only among `candidates`; against the other storages of its engine submission it is
    /// checked when the submission is evaluated and, under the budget lock, when it is admitted
    /// (`storage::engine_library::check_engine_storage_uses`). A re-layout of columns the current version reads is
    /// therefore not refused here.
    pub fn check_policy_before_build(&self, candidates: &[&FrozenStorage]) -> Result<(), AdmissionError> {
        for candidate in candidates {
            self.config.storage_policy.check_declaration(&candidate.manifest)?;
        }
        if !self.config.storage_policy.stores_columns_once() {
            return Ok(());
        }
        let holders: Vec<PayloadHolder> = candidates.iter().map(|c| PayloadHolder::of_manifest(&c.manifest, None)).collect::<Result<_, _>>()?;
        let names: BTreeSet<String> = holders.iter().map(|h| h.name.clone()).collect();
        let serving = if self.role == Some(AuthorRole::Engine) { vec![] } else { self.serving_payload(&self.store()?, &names)? };
        check_single_copy(&holders, &serving)
    }

    /// Under `physical_only`, refuse (`storage_payload_duplicate`) new storages `new` (`(frozen storage, package)`; one
    /// already admitted is not new) that store a column twice among themselves or that a serving storage already
    /// stores, as the serving storage will stand once they are registered (`storage::payload`). Called by every
    /// evaluation of a submission's storages and, under the library's budget lock, by registration.
    pub fn check_new_storage_payload(&self, store: &ObjectStore, new: &[(&FrozenStorage, ContentId)]) -> Result<(), AdmissionError> {
        if !self.config.storage_policy.stores_columns_once() {
            return Ok(());
        }
        let mut holders = vec![];
        for (frozen, package) in new {
            let admitted = records::storage_versions(store, &frozen.manifest.name).map_err(AdmissionError::tool)?.iter().any(|(_, a)| a.package == *package);
            if !admitted {
                holders.push(PayloadHolder::of_manifest(&frozen.manifest, Some(*package))?);
            }
        }
        if holders.is_empty() {
            return Ok(());
        }
        let replacing: BTreeSet<String> = holders.iter().map(|h| h.name.clone()).collect();
        check_single_copy(&holders, &self.serving_payload(store, &replacing)?)
    }

    /// The serving storage as it will stand once a query package reading `uses` (`(name, package)`) is admitted: its
    /// uses that are not serving storage yet (an older version of a name it pins; its new storages are registered
    /// before) join it. Refused when, under `physical_only`, the serving storage would then hold a column twice
    /// (`storage_payload_duplicate`; user-listed packages included, so a query-only run cannot pass two listed copies)
    /// or when the joining assets exceed the storage budget (`storage_budget_exceeded`). Both use the one inventory
    /// definition, `storage::budget::serving_storages`. Qualification calls it under the library budget lock and keeps
    /// the lock through the package's admission (record publication only), so no storage registration races it;
    /// evaluation calls it earlier for feedback. Metadata only.
    pub fn check_query_storage_uses(&self, store: &ObjectStore, uses: &[(String, ContentId)]) -> Result<Value, AdmissionError> {
        let capture = CurrentCapture::of(&self.capture.current()).map_err(AdmissionError::tool)?;
        let (serving, superseded) = serving_storages(store, &capture, self.schema(), &self.config.storage_policy, &BTreeSet::new())?;
        if self.config.storage_policy.stores_columns_once() {
            let serving_holders = payload_of_serving(store, &serving)?;
            let use_holders = payload_holders(&recorded_storages(store, uses.to_vec())?);
            check_single_copy(&added_to(use_holders, &serving_holders), &serving_holders)?;
        }
        let joining: Vec<&(String, ContentId)> = uses.iter().filter(|(_, package)| serving.iter().all(|s| s.package_id != *package)).collect();
        let mut budget = StorageBudget::of_serving(store, &serving, &superseded, self.config.live_bytes_allowance)?;
        let mut joining_bytes = 0u64;
        for (_, package) in &joining {
            if let Some((_, asset)) = superseded.iter().find(|s| s.package_id == *package).and_then(|s| s.asset.as_ref()) {
                let directory = records::storage_asset_directory(store, asset).map_err(AdmissionError::tool)?;
                joining_bytes = joining_bytes.saturating_add(budget.add_new(&directory)?);
            }
        }
        let names: Vec<&String> = joining.iter().map(|(name, _)| name).collect();
        budget.check_room(joining_bytes, &format!("admitting a query package that reads the storages {names:?}, which are not serving storage yet"))?;
        Ok(json!({"joining_storages":names,"joining_bytes":joining_bytes,"used_bytes":budget.used_bytes,"allowance_bytes":budget.allowance,
            "single_copy":if self.config.storage_policy.is_unrestricted() { "not applicable (unrestricted)" } else if self.config.storage_policy.is_fixed_flat() { "not applicable (fixed_flat: one generated flat storage per table)" } else { "checked: the serving storage with this package's uses holds each column once" }}))
    }

    fn serving_payload(&self, store: &ObjectStore, replacing: &BTreeSet<String>) -> Result<Vec<PayloadHolder>, AdmissionError> {
        let capture = CurrentCapture::of(&self.capture.current()).map_err(AdmissionError::tool)?;
        serving_payload(store, &capture, self.schema(), &self.config.storage_policy, replacing)
    }

    /// The storage budget of the library for the current capture (`storage::budget`).
    pub fn budget(&self, store: &ObjectStore) -> Result<StorageBudget, AdmissionError> {
        let capture = CurrentCapture::of(&self.capture.current()).map_err(AdmissionError::tool)?;
        StorageBudget::of_library(store, &capture, self.schema(), &self.config.storage_policy, self.config.live_bytes_allowance)
    }

    /// Recompute the facts other sessions change while this one runs, from the library as it stands now: the admitted
    /// storage catalog (`storages.json` of the role's contract, with read-only interface copies of newly admitted versions
    /// under `admitted-storages/<name>@<package8>/`; earlier copies stay) and the storage budget (`storage-budget.json`).
    /// Prepared code, proofs and data are not touched; nothing is reserved. Used before every author call and by the
    /// `catalog` tool.
    pub fn refresh_shared_facts(&self) -> Result<Value, AdmissionError> {
        let role = self.role.ok_or_else(|| AdmissionError::tool("the shared facts are refreshed for an author workspace with its role"))?;
        let root = self.workspace()?.to_path_buf();
        let (contract, statements) = match role {
            AuthorRole::Query => (root.join(brief::CONTRACT_DIRECTORY), &self.statements[..1]),
            AuthorRole::WorkloadStorage => (root.join(brief::storage::CONTRACT_DIRECTORY), &self.statements[..]),
            AuthorRole::Engine => (root.join(crate::prompts::engine_contract::CONTRACT_DIRECTORY), &self.statements[..]),
        };
        let demands: Vec<(String, DeclaredSource)> = statements.iter().map(|s| Ok((s.statement().key_v4_id.clone(), s.demand()?))).collect::<Result<_, AdmissionError>>()?;
        let store = self.store()?;
        let capture = self.capture.current();
        let storages = brief::common::storages_catalog(&store, &capture, self.schema(), &root, &demands, &self.config.storage_policy)?;
        brief::common::write(&contract.join("storages.json"), &storages)?;
        let budget = brief::common::storage_budget(&store, &capture, self.schema(), &self.config.storage_policy, self.config.live_bytes_allowance, &contract.join("storage-budget.json"))?;
        let listed: Vec<Value> = storages["storages"]
            .as_array()
            .into_iter()
            .flatten()
            .map(|s| json!({"name":s["name"],"package":s["package"],"current":s["current"],"applicable":s["applicable"],"storage_bytes":s["asset_for_current_data"]["storage_bytes"]}))
            .collect();
        Ok(json!({"storage_budget":budget,"catalog":{"storages":listed,"file":contract.join("storages.json")},
            "refreshed_unix_ms":crate::controller::records::now_unix_ms(),"meaning":SHARED_FACTS_MEANING}))
    }

    /// The storage budget as it stands now, compact (in every storage tool result); a snapshot, not a reservation.
    fn budget_now(&self) -> Value {
        match self.store().and_then(|store| self.budget(&store)) {
            Ok(budget) => json!({"budget_bytes":budget.allowance,"used_bytes":budget.used_bytes,"left_bytes":budget.left_bytes(),
                "read_unix_ms":crate::controller::records::now_unix_ms(),"meaning":SHARED_FACTS_MEANING}),
            Err(error) => json!({"error":error.to_string()}),
        }
    }

    /// The declarations of every usable admitted storage (applicable to the current data and allowed by the storage
    /// policy), with their names.
    pub fn usable_admitted_declarations(&self, store: &ObjectStore) -> Result<Vec<(String, DeclaredSource)>, AdmissionError> {
        let capture = CurrentCapture::of(&self.capture.current()).map_err(AdmissionError::tool)?;
        let mut usable = vec![];
        for storage in catalog::admitted_storages(store, &capture, self.schema())? {
            if storage.applicability.is_ok() && self.config.storage_policy.ineligible(store, storage.package_id, &storage.package.name)?.is_none() {
                usable.push((storage.package.name.clone(), storage.declaration.clone()));
            }
        }
        Ok(usable)
    }

    /// Complete lossless coverage of a workload submission (`storage::coverage`): its storages together with every
    /// usable admitted storage store every column of every table; otherwise `storage_coverage_incomplete`.
    pub fn check_workload_coverage(&self, submitted: &[&DeclaredSource]) -> Result<Value, AdmissionError> {
        let store = self.store()?;
        let admitted = self.usable_admitted_declarations(&store)?;
        let all: Vec<&DeclaredSource> = submitted.iter().copied().chain(admitted.iter().map(|(_, d)| d)).collect();
        check_lossless_coverage(self.schema(), all.iter().copied(), "the submitted storages and the usable admitted storages")?;
        Ok(coverage_report(self.schema(), all.iter().copied()))
    }

    /// Protect the session's trials among `assets` (an eligible evaluation used them; qualification needs exactly
    /// those): durable before the caller records the evaluation.
    pub fn protect_assets(&mut self, assets: &BTreeSet<ContentId>, reason: &str) -> Result<(), AdmissionError> {
        self.trials.as_mut().ok_or_else(|| AdmissionError::tool("trial assets are not open"))?.protect(assets, reason)
    }

    /// At session close: remove the session's remaining trial assets except `keep`; the record of what was removed
    /// and kept.
    pub fn release_trial_assets(&mut self, keep: &BTreeSet<ContentId>) -> Result<Value, AdmissionError> {
        let store = self.store()?;
        let mut released = self.trials.as_mut().ok_or_else(|| AdmissionError::tool("trial assets are not open"))?.release_at_close(&store, keep)?;
        if let Some(diagnostics) = self.diagnostics.as_mut() {
            released["diagnostic_builds"] = diagnostics.release()?;
        }
        Ok(released)
    }

    /// Refuse a query or engine author's storage that reads source columns (`storage_not_built_from_admitted`),
    /// for verified and unverified builds alike; the re-verification of an admitted storage is exempt.
    fn refuse_query_storage_from_source(&self, frozen: &FrozenStorage, reverification: bool) -> Result<(), AdmissionError> {
        if matches!(self.role, Some(AuthorRole::Query | AuthorRole::Engine)) && frozen.derivation.is_none() && !reverification {
            return Err(AdmissionError::refusal(format!(
                "storage_not_built_from_admitted: storage {} reads source columns; a query author's new storage is built from admitted storages (manifest built_from: their parts through their readers), since the original input may be deleted",
                frozen.manifest.name
            )));
        }
        Ok(())
    }

    /// The unverified diagnostic build of a frozen storage (`storage::diagnostic`): `(build, reused)`.
    /// Verification is skipped; the run's storage policy is not ([`Workbench::check_policy_before_build`]). On the
    /// general line a derived storage's sources get their assets first (a released one rebuilt by its stored builder),
    /// and the build leaves the shared-host floor free after the session's disposable trials are reclaimed.
    pub fn diagnostic_storage(&mut self, frozen: &FrozenStorage, frozen_dir: &Path, out: &Path) -> Result<(DiagnosticStorage, bool), AdmissionError> {
        self.refuse_query_storage_from_source(frozen, false)?;
        self.check_policy_before_build(&[frozen])?;
        let store = self.store()?;
        if self.config.asset_upkeep.is_some()
            && let Some(derivation) = frozen.derivation.as_ref()
        {
            let capture = CurrentCapture::of(&self.capture.current()).map_err(AdmissionError::tool)?;
            let keep = BTreeSet::new();
            let mut context = self.build_context(&keep)?;
            ensure_source_assets(&mut context, &store, derivation, &capture, out)?;
        }
        let build_workers = self.build_workers()?;
        let keep = BTreeSet::new();
        let trials = self.trials.as_mut().ok_or_else(|| AdmissionError::missing_input("the author workspace is not prepared"))?;
        let mut reclaim = |need: &crate::query::assets::SpaceNeed| trials.reclaim_for(&store, need, &keep);
        let mut context = DiagnosticContext {
            library: &self.config.library,
            locks: &self.config.locks,
            runner: &self.statements[0].runner,
            capture: &self.capture,
            build_workers,
            asset_upkeep: self.config.asset_upkeep,
            reclaim: &mut reclaim,
        };
        self.diagnostics.as_mut().ok_or_else(|| AdmissionError::missing_input("the author workspace is not prepared"))?.build(&mut context, frozen, frozen_dir, out)
    }

    /// The storage build context of this bench at its capture, keeping `keep` (the asking job's assets) from reclaim.
    fn build_context<'a>(&'a mut self, keep: &'a BTreeSet<ContentId>) -> Result<StorageBuildContext<'a>, AdmissionError> {
        let build_workers = self.build_workers()?;
        Ok(StorageBuildContext {
            library: &self.config.library,
            locks: &self.config.locks,
            runner: &self.statements[0].runner,
            capture: &self.capture,
            statements: &self.statements,
            build_workers,
            trials: self.trials.as_mut().ok_or_else(|| AdmissionError::missing_input("the author workspace is not prepared"))?,
            keep,
            policy: &self.config.storage_policy,
            allowance: self.config.live_bytes_allowance,
            asset_upkeep: self.config.asset_upkeep,
        })
    }

    /// Publish this session's builds of the admitted storages `packages` at other captures into the library (the
    /// general line's admission, `query::assets::TrialAssets::promote_admitted`). Returns what was promoted and removed.
    pub fn promote_session_trials(&mut self, store: &ObjectStore, packages: &BTreeSet<ContentId>) -> Result<Value, AdmissionError> {
        self.trials.as_mut().ok_or_else(|| AdmissionError::tool("trial assets are not open"))?.promote_admitted(store, packages)
    }

    /// Every storage use of a frozen query candidate with its asset for the current capture: an admitted package's
    /// asset (built once by its admitted library when this capture has none; refused when the storage policy excludes
    /// the package), or a workspace storage checked and built through [`Workbench::check_storage`]. Evidence of new
    /// builds goes under `out`.
    pub fn resolve_storages(&mut self, frozen: &FrozenQuery, out: &Path) -> Result<Vec<ResolvedStorage>, AdmissionError> {
        self.resolve_storages_as(frozen, out, TrialVerification::WholeCrate)
    }

    /// [`Workbench::resolve_storages`] for a trial built as `verification`: under `NotRun` the candidate's workspace
    /// storages are unverified diagnostic builds (`storage::diagnostic`; admitted storages stay as admitted). Only
    /// `not_run` trials, which are labelled diagnostic and never evidence, may resolve that way.
    pub fn resolve_storages_as(&mut self, frozen: &FrozenQuery, out: &Path, verification: TrialVerification) -> Result<Vec<ResolvedStorage>, AdmissionError> {
        self.resolve_uses_as(&frozen.candidate.storage_uses, &frozen.frozen_dir, out, verification)
    }

    /// [`Workbench::resolve_storages_as`] for the storage `uses` of any frozen crate (a query's or an engine's) frozen
    /// under `frozen_dir` (its workspace storages under `<frozen_dir>/storages/<name>`).
    pub fn resolve_uses_as(&mut self, uses: &[candidate::FrozenUse], frozen_dir: &Path, out: &Path, verification: TrialVerification) -> Result<Vec<ResolvedStorage>, AdmissionError> {
        if self.config.storage_policy.is_fixed_flat() {
            candidate::refuse_workspace_storages(uses)?;
        }
        let workspace_storage = |name: &str| -> Result<(PathBuf, FrozenStorage), AdmissionError> {
            let dir = frozen_dir.join("storages").join(name);
            Ok((dir.clone(), freeze::read_frozen_storage(&dir)?))
        };
        let workspace: Vec<(PathBuf, FrozenStorage)> =
            uses.iter().filter(|u| matches!(u.source, StorageSource::Workspace { .. })).map(|u| workspace_storage(&u.name)).collect::<Result<_, _>>()?;
        let mut keep = self.checked_assets(workspace.iter().map(|(dir, storage)| (dir.as_path(), storage)));
        let mut resolved = vec![];
        for storage_use in uses {
            let name = StorageName::new(&storage_use.name).map_err(AdmissionError::refusal)?;
            let use_out = out.join(format!("storage-{}", storage_use.name));
            match &storage_use.source {
                StorageSource::Admitted { package } => {
                    let store = self.store()?;
                    let (record, declaration) = self.usable_admitted_storage(&store, *package)?;
                    // The key names the tables' rows only: a published asset is found without capturing its columns.
                    let capture = CurrentCapture::of(&self.capture.current()).map_err(AdmissionError::tool)?;
                    let asset = match lookup_storage_asset(&store, *package, &capture, run_constraints_digest(self.schema())?)? {
                        AssetLookup::Published(asset) => {
                            if self.config.storage_policy.is_fixed_flat() {
                                flat::check_flat_asset(&store, &record.name, &asset.asset)?;
                            }
                            asset
                        }
                        AssetLookup::Absent(_) if self.config.storage_policy.is_fixed_flat() => return Err(flat::not_prepared(&record.name)),
                        AssetLookup::Absent(slot) => {
                            // An admitted storage's asset for a new capture (or after its release on the general line) is
                            // built straight into the library.
                            let mut context = self.build_context(&keep)?;
                            build_library_asset(&mut context, &store, slot, &record, &declaration, &capture, &use_out)?
                        }
                    };
                    let build = records::check_build_evidence(&store, record.build).map_err(AdmissionError::tool)?;
                    let library = records::library_path(&store, &build).map_err(AdmissionError::tool)?;
                    resolved.push(ResolvedStorage {
                        name,
                        declaration,
                        package: *package,
                        admitted: true,
                        tiny: crate::storage::build::tiny_builder(&store, &library, record.derived_from.as_ref())?,
                        library,
                        asset: asset.id,
                        parts: asset.directory,
                        storage_bytes: asset.asset.storage_bytes,
                        build_wall_ns: asset.asset.build_wall_ns,
                        asset_built_now: asset.built,
                        assumes_declared_constraints: record.assumed_constraints.is_some(),
                    });
                }
                StorageSource::Workspace { .. } if verification == TrialVerification::NotRun => {
                    let (dir, storage) = workspace_storage(&storage_use.name)?;
                    let (built, _) = self.diagnostic_storage(&storage, &dir, &use_out)?;
                    resolved.push(ResolvedStorage {
                        name,
                        declaration: storage.declaration.clone(),
                        package: built.sources,
                        admitted: false,
                        tiny: crate::storage::build::tiny_builder(&self.store()?, &built.library, storage.derivation.as_ref())?,
                        library: built.library.clone(),
                        asset: built.sources,
                        parts: built.directory.clone(),
                        storage_bytes: built.storage_bytes,
                        build_wall_ns: built.build_wall_ns,
                        asset_built_now: false,
                        assumes_declared_constraints: storage.manifest.uses_declared_constraints,
                    });
                }
                StorageSource::Workspace { .. } => {
                    let (dir, storage) = workspace_storage(&storage_use.name)?;
                    let (checked, _) = self.check_storage(&storage, &dir, &use_out, &keep)?;
                    keep.insert(checked.asset);
                    resolved.push(ResolvedStorage {
                        name,
                        declaration: storage.declaration.clone(),
                        package: checked.package,
                        admitted: false,
                        tiny: crate::storage::build::tiny_builder(&self.store()?, &checked.library, storage.derivation.as_ref())?,
                        library: checked.library.clone(),
                        asset: checked.asset,
                        parts: checked.asset_directory.clone(),
                        storage_bytes: checked.record.pointer("/asset/storage_bytes").and_then(Value::as_u64).unwrap_or(0),
                        build_wall_ns: checked.record.pointer("/asset/build_wall_ns").and_then(Value::as_u64).unwrap_or(0),
                        asset_built_now: checked.asset_built_now,
                        assumes_declared_constraints: storage.manifest.uses_declared_constraints,
                    });
                }
            }
        }
        Ok(resolved)
    }

    /// The admitted storage `package` with its declaration, refused when the run's storage policy does not allow it
    /// (a user exclusion, or no `physical_only` registration or listing) or when it assumes declared integrity
    /// constraints other than the run's (`storage_assumes_declared_constraints`).
    fn usable_admitted_storage(&self, store: &ObjectStore, package: ContentId) -> Result<(records::VerusStoragePackageV1, DeclaredSource), AdmissionError> {
        let (record, declaration) = catalog::admitted_storage(store, package)?;
        check_storage_assumptions(&record, run_constraints_digest(self.schema())?)?;
        if let Some(reason) = self.config.storage_policy.ineligible(store, package, &record.name)? {
            return Err(AdmissionError::refusal(reason));
        }
        Ok((record, declaration))
    }

    /// Register every workspace storage of a frozen query candidate (checked through the session cache, so an
    /// evaluated candidate builds nothing here): the uses as admitted package pins, in use order. Admitted uses are
    /// checked against the storage policy again, so an exclusion recorded after the evaluation still refuses them.
    pub fn register_workspace_storages(&mut self, frozen: &FrozenQuery, out: &Path, registered_by: &Value) -> Result<Vec<(String, gendb_artifacts::ContentId, Option<Registration>)>, AdmissionError> {
        self.register_workspace_uses(&frozen.candidate.storage_uses, &frozen.frozen_dir, out, registered_by)
    }

    /// [`Workbench::register_workspace_storages`] for the storage `uses` of any frozen crate frozen under `frozen_dir`.
    pub fn register_workspace_uses(&mut self, storage_uses: &[candidate::FrozenUse], frozen_dir: &Path, out: &Path, registered_by: &Value) -> Result<Vec<(String, gendb_artifacts::ContentId, Option<Registration>)>, AdmissionError> {
        let mut checked = self.check_workspace_uses(storage_uses, frozen_dir, out)?;
        // All of the submission's new storages are registered together (one budget check).
        let registrations = self.register_all(checked.workspace.iter_mut().map(|(_, c, f)| (c, &*f)).collect(), registered_by.clone())?;
        Ok(checked.registered(registrations))
    }

    /// The storage uses of a crate frozen under `frozen_dir`, checked and not yet registered: each admitted use usable
    /// under the run's storage policy (an exclusion recorded after the evaluation still refuses it), each workspace
    /// storage checked through the session cache (an evaluated candidate builds nothing here).
    pub fn check_workspace_uses(&mut self, storage_uses: &[candidate::FrozenUse], frozen_dir: &Path, out: &Path) -> Result<CheckedUses, AdmissionError> {
        let mut uses = vec![];
        let mut workspace: Vec<(usize, CheckedStorage, FrozenStorage)> = vec![];
        for storage_use in storage_uses {
            match &storage_use.source {
                StorageSource::Admitted { package } => {
                    self.usable_admitted_storage(&self.store()?, *package)?;
                    uses.push((storage_use.name.clone(), *package, None));
                }
                StorageSource::Workspace { .. } => {
                    let dir = frozen_dir.join("storages").join(&storage_use.name);
                    let storage = freeze::read_frozen_storage(&dir)?;
                    let keep = self.checked_assets([(dir.as_path(), &storage)]);
                    let (checked, _) = self.check_storage(&storage, &dir, &out.join(format!("storage-{}", storage_use.name)), &keep)?;
                    let package = checked.package;
                    workspace.push((uses.len(), checked, storage));
                    uses.push((storage_use.name.clone(), package, None));
                }
            }
        }
        Ok(CheckedUses { uses, workspace })
    }

    /// The current version of every admitted storage a query submission names (its admitted uses and the `built_from`
    /// sources of its workspace storages), as substitutes for the stale ones.
    fn current_versions_named_by(&mut self, submission: &CandidateSubmission) -> Result<BTreeMap<ContentId, ContentId>, AdmissionError> {
        let workspace = self.workspace()?.to_path_buf();
        let Ok((path, _)) = resolve_candidate_manifest(&workspace, &submission.candidate_manifest) else { return Ok(BTreeMap::new()) };
        let Ok(manifest) = serde_json::from_slice::<candidate::QueryManifest>(&fs::read(&path).unwrap_or_default()) else { return Ok(BTreeMap::new()) };
        let mut named: Vec<ContentId> = manifest.storage_uses.iter().filter_map(|u| u.admitted).collect();
        let base = path.parent().map(Path::to_path_buf).unwrap_or_default();
        for storage in manifest.storage_uses.iter().filter_map(|u| u.workspace.as_ref()) {
            if let Ok((storage, _)) = read_manifest(&workspace, &base.join(storage))
                && let Some(built_from) = storage.built_from
            {
                named.extend(built_from.sources.iter().map(|s| s.admitted));
            }
        }
        let mut substitutes = BTreeMap::new();
        for package in named {
            // An unknown, inapplicable or failed re-verification is refused here by name.
            let (current, _) = self.current_version(package)?;
            if current != package {
                substitutes.insert(package, current);
            }
        }
        Ok(substitutes)
    }

    /// The current version of admitted storage `package` (`storage::reverify`): itself when its closure is the current
    /// framework's; else its recorded re-verification; else a re-verification now: its unchanged interface and builder
    /// with fresh framework files (the sources of a storage built from admitted storages first), verified, compiled and
    /// checked as any storage (its asset reused by hard links when its builder identity is unchanged), and registered
    /// as a new version of its name with the re-verification evidence. `(package, re-verification record if made now)`.
    pub fn current_version(&mut self, package: ContentId) -> Result<(ContentId, Option<Value>), AdmissionError> {
        let store = self.store()?;
        let (record, _) = catalog::admitted_storage(&store, package)?;
        let fresh = content_matches(self.schema(), &record).map_err(AdmissionError::refusal)?;
        let ClosureState::Stale(reason) = closure_state(self.schema(), &record, &fresh)? else { return Ok((package, None)) };
        if self.config.storage_policy.is_fixed_flat() {
            // A flat storage is prepared once, with its asset; re-verifying it here would rebuild that asset by its builder.
            return Err(AdmissionError::refusal(format!(
                "flat_storage_stale: flat storage {} ({package}) was prepared with other framework files ({reason}); run gendb prepare-flat-storage with this GenDB first",
                record.name
            )));
        }
        if let Some(current) = self.reverified.get(&package) {
            return Ok((*current, None));
        }
        // One re-verification per storage at a time across the sessions of this library; a session that waited finds
        // the other's recorded result.
        let _reverifying = LibraryLock::acquire(&store, &reverification_lock(&record.name))?;
        if let Some(current) = recorded_reverification(&store, self.schema(), package, &record.name)? {
            self.reverified.insert(package, current);
            return Ok((current, None));
        }
        let sources = match &record.derived_from {
            Some(derivation) => Some(derivation.sources.iter().map(|s| self.current_version(s.package).map(|(id, _)| id)).collect::<Result<Vec<_>, _>>()?),
            None => None,
        };
        let dir = self.session_root()?.join("reverification").join(format!("{}-{}", record.name, crate::controller::records::now_unix_ms()));
        let description = catalog::description_of(&store, package, &record.name)?;
        let (frozen, frozen_dir) = materialize(&store, self.schema(), &record, &description, sources, &dir)?;
        let (mut checked, _) = self.check_storage_as(&frozen, &frozen_dir, &dir, &BTreeSet::new(), true)?;
        let evidence = json!({"reverifies":package,"name":record.name,"reason":reason,"evidence":dir,
            "meaning":"the same interface and builder sources as the re-verified package, verified and compiled whole with the current framework files"});
        checked.evidence.push(store.put(1, REVERIFICATION_KIND, &evidence).map_err(AdmissionError::tool)?);
        let registration = self.register(&mut checked, &frozen, json!({"reverification_of":package,"session":self.session_root()?}))?;
        self.reverified.insert(package, registration.package);
        Ok((registration.package, Some(json!({"reverified":package,"as":registration.package,"asset":checked.record["asset"],"reason":reason}))))
    }

    // ------------------------------------------------------------------------------------------------ queries

    /// Freeze a query submission for statement `statement` into `frozen_dir`. Every admitted storage it names (as a
    /// use, or as a source of one of its workspace storages) is first replaced by its current version
    /// ([`Workbench::current_version`]: re-verified against the current framework when stale).
    pub fn freeze_query(&mut self, statement: usize, frozen_dir: &Path, submission: &CandidateSubmission) -> Result<(FrozenQuery, candidate::Frozen), AdmissionError> {
        let substitutes = self.current_versions_named_by(submission)?;
        let session = self.statements.get(statement).ok_or_else(|| AdmissionError::missing_input(format!("statement {statement} is not a workload statement")))?;
        let context = QueryFreeze { workspace: self.workspace()?, session, library: &self.config.library, substitutes: &substitutes, policy: &self.config.storage_policy };
        let frozen = candidate::freeze(&context, frozen_dir, submission)?;
        Ok((FrozenQuery { statement, candidate: frozen.candidate.clone(), frozen_dir: frozen_dir.to_path_buf() }, frozen))
    }

    /// The whole-crate verify-and-compile run of a frozen query crate, reused for equal sources unless `fresh`:
    /// `(library, build record, reused)`.
    pub fn compile_query(&mut self, frozen: &FrozenQuery, out: &Path, fresh: bool) -> Result<(PathBuf, Value, bool), AdmissionError> {
        let krate = frozen.candidate.crate_in(&frozen.frozen_dir);
        let key = (TrialVerification::WholeCrate, frozen.candidate.source_key(&krate)?);
        if !fresh && let Some((library, record)) = self.query_builds.get(&key) {
            return Ok((library.clone(), record.clone(), true));
        }
        let (run, library) = compile::compile(&self.config.locks, &krate, CrateKind::Query, &frozen.candidate.compiler, out)?;
        let items = declared_items(&frozen.candidate.agent_modules(), &krate, CrateKind::Query, run["stdout"].as_str().unwrap_or_default())?;
        let record = json!({"verification":run["verification"],"wall_ns":run["wall_ns"],"argv":run["argv"],"library":library,"items":items,"record":out.join("run.json"),
            "outcome":run["outcome"],"detail":run["detail"]});
        self.query_builds.insert(key, (library.clone(), record.clone()));
        Ok((library, record, false))
    }

    /// The unverified diagnostic build (`rust_verify --no-verify`) of a frozen query crate, reused for equal sources
    /// within this mode only: `(library, build record, reused)`. No declared-item check (items are what verification
    /// reports); the record says `verification_not_run`.
    fn compile_query_unverified(&mut self, frozen: &FrozenQuery, out: &Path) -> Result<(PathBuf, Value, bool), AdmissionError> {
        let krate = frozen.candidate.crate_in(&frozen.frozen_dir);
        let key = (TrialVerification::NotRun, frozen.candidate.source_key(&krate)?);
        if let Some((library, record)) = self.query_builds.get(&key) {
            return Ok((library.clone(), record.clone(), true));
        }
        let (run, library) = compile::compile_unverified(&self.config.locks, &krate, CrateKind::Query, &frozen.candidate.compiler, out)?;
        let record = json!({"verification":UNVERIFIED_LABEL,"verus_summary":run["verification"],"wall_ns":run["wall_ns"],"argv":run["argv"],"library":library,
            "record":out.join("run.json"),"outcome":run["outcome"],"detail":run["detail"]});
        self.query_builds.insert(key, (library.clone(), record.clone()));
        Ok((library, record, false))
    }

    // ------------------------------------------------------------------------------------------------ local jobs

    /// One local job of a session of `role`; `Err` refuses the request itself (the job directory may not exist). A
    /// query author's query tools run its one statement; the workload author's name one (`statement`).
    pub fn local_job(&mut self, role: AuthorRole, evidence_root: &Path, action: &str, arguments: Value, job_id: u64) -> Result<Value, AdmissionError> {
        let parsed: LocalJobArguments = serde_json::from_value(arguments.clone()).map_err(|e| AdmissionError::missing_input(format!("invalid tool arguments: {e}")))?;
        let statement = match (role, parsed.statement) {
            _ if action == ToolAction::Catalog.name() => 0,
            (AuthorRole::Query, None) => 0,
            (AuthorRole::Query, Some(_)) => return Err(AdmissionError::missing_input("a query author's tools run the session's statement; statement is a workload-role argument")),
            (AuthorRole::WorkloadStorage, Some(index)) if index < self.statements.len() => index,
            (AuthorRole::WorkloadStorage, other) if !ToolAction::parse(action)?.is_storage() => {
                return Err(AdmissionError::missing_input(format!("statement must name a workload statement (0..{}), got {other:?}", self.statements.len())));
            }
            (AuthorRole::WorkloadStorage, _) => 0,
            (AuthorRole::Engine, _) => return Err(AdmissionError::tool("an engine session's jobs run through Workbench::job with the engine tools")),
        };
        if parsed.engine_arguments_given() {
            return Err(AdmissionError::missing_input("templates, binding and sql are engine-tool arguments"));
        }
        self.job(role, evidence_root, action, arguments, job_id, |bench, workspace, job, action, arguments| bench.query_job(workspace, job, statement, action, arguments))
    }

    /// The record of one local job of a session of `role`: the job directory `<evidence_root>/<NNNN>-<job_name>` with
    /// `request.json` and `result.json`, the outcome (completed or refused with its failure class) and the unverified
    /// label. Catalog and the storage tools run here; every other action runs `query_tool` (the query tools of the
    /// query and workload roles, the engine tools of the engine role). `Err` refuses the request itself.
    pub fn job(
        &mut self,
        role: AuthorRole,
        evidence_root: &Path,
        action: &str,
        arguments: Value,
        job_id: u64,
        query_tool: impl FnOnce(&mut Workbench, &Path, &Path, ToolAction, &LocalJobArguments) -> Result<Value, AdmissionError>,
    ) -> Result<Value, AdmissionError> {
        let action = ToolAction::parse(action)?;
        let arguments: LocalJobArguments = serde_json::from_value(arguments).map_err(|e| AdmissionError::missing_input(format!("invalid tool arguments: {e}")))?;
        arguments.check(action)?;
        let workspace = self.workspace()?.to_path_buf();
        let job = evidence_root.join(format!("{job_id:04}-{}", arguments.job_name));
        fs::create_dir(&job).map_err(|e| AdmissionError::missing_input(format!("fresh local job required: {e}")))?;
        write_new_json(&job.join("request.json"), &json!({"format_version":1,"job_id":job_id,"action":action.name(),"arguments":&arguments,
            "author_workspace":workspace,"diagnostic_only":true,"official_measurement":false}))
        .map_err(AdmissionError::tool)?;
        let started = Instant::now();
        let unverified = action.takes_verification() && arguments.verification() == TrialVerification::NotRun;
        let outcome = if action == ToolAction::Catalog {
            self.refresh_shared_facts().map(|mut facts| {
                facts["status"] = json!("refreshed");
                facts
            })
        } else if action.is_storage() && self.config.storage_policy.is_fixed_flat() {
            Err(AdmissionError::refusal(format!(
                "fixed_flat_storage_tools_unavailable: {} is not available under storage_policy fixed_flat; queries read the prepared flat storages listed in storages.json",
                action.name()
            )))
        } else if action.is_storage() {
            // Storage results carry the budget as it stands now, so sizes are judged against current facts while measuring.
            self.storage_job(role, &workspace, &job, action, &arguments).map(|mut result| {
                result["storage_budget_now"] = self.budget_now();
                result
            })
        } else {
            query_tool(self, &workspace, &job, action, &arguments)
        };
        let frozen_record = ["frozen/candidate.json", "frozen/storage.json"].iter().map(|r| job.join(r)).find(|p| p.is_file());
        let mut record = match outcome {
            Ok(result) => json!({"format_version":1,"job_id":job_id,"action":action.name(),"status":"completed","stage":action.name(),
                "elapsed_ns":started.elapsed().as_nanos(),"result":result,"error":Value::Null,"result_record":job.join("result.json"),
                "diagnostic_only":true,"official_measurement":false,
                "paths":{"request":job.join("request.json"),"result":job.join("result.json"),"frozen":frozen_record}}),
            Err(error) => {
                let verus_record = job.join("verus/run.json");
                json!({"format_version":1,"job_id":job_id,"action":action.name(),"status":"refused","failure_class":error.class,"stage":action.name(),
                    "elapsed_ns":started.elapsed().as_nanos(),"result":Value::Null,"error":error.to_string(),"result_record":job.join("result.json"),
                    "diagnostic_only":true,"official_measurement":false,
                    "paths":{"request":job.join("request.json"),"result":job.join("result.json"),"frozen":frozen_record,
                        "verus_record":verus_record.is_file().then_some(verus_record)}})
            }
        };
        if unverified {
            // Labelled whatever the outcome, including a refusal before any timing.
            record["verification"] = json!(UNVERIFIED_LABEL);
            record["diagnostic_unverified"] = json!(true);
        }
        write_new_json(&job.join("result.json"), &record).map_err(AdmissionError::tool)?;
        Ok(record)
    }

    /// A storage tool: freeze the named storage candidate into the job, then the action.
    fn storage_job(&mut self, role: AuthorRole, workspace: &Path, job: &Path, action: ToolAction, arguments: &LocalJobArguments) -> Result<Value, AdmissionError> {
        let manifest = arguments.storage.as_ref().expect("checked: storage tools carry a storage manifest");
        let (_, relative) = resolve_candidate_manifest(workspace, manifest).map_err(AdmissionError::missing_input)?;
        if action == ToolAction::StorageCheck {
            // Generate the crate's framework files (and empty author roots) first, so a new storage can start from them.
            let (src, complete) = freeze::scaffold_storage_crate(workspace, &relative, self.schema(), Some(&self.store()?))?;
            if !complete {
                return Ok(json!({"status":"scaffolded","workspace_framework":src,
                    "next":"write the author roots' mod.rs files (interface: represents and readers; builder: build), then run storage_check again"}));
            }
        }
        let frozen_dir = job.join("frozen");
        let store = self.store()?;
        let mut substitutes = BTreeMap::new();
        if let Ok((manifest, _)) = read_manifest(workspace, &relative)
            && let Some(built_from) = manifest.built_from
        {
            for source in built_from.sources {
                let (current, _) = self.current_version(source.admitted)?;
                if current != source.admitted {
                    substitutes.insert(source.admitted, current);
                }
            }
        }
        let frozen = freeze_storage(workspace, &relative, &frozen_dir, self.schema(), Some(&store), &substitutes)?;
        let krate = frozen.frozen_crate(&frozen_dir);
        let verus_dir = job.join("verus");
        match action {
            ToolAction::StorageCheck => {
                let (_, crate_dir) = read_manifest(workspace, &relative)?;
                let name = frozen.name()?;
                let rewritten = write_workspace_framework(
                    &crate_dir,
                    &storage_framework(self.schema(), &name, &frozen.declaration, frozen.manifest.uses_declared_constraints, frozen.candidate_derivation(&store)?.as_ref())?,
                )?;
                let coverage: Vec<Value> = self
                    .statements
                    .iter()
                    .enumerate()
                    .map(|(index, s)| Ok(json!({"statement":index,"statement_key":s.statement().key_v4_id,"coverage":coverage_of(&s.demand()?, &name, &frozen.declaration)})))
                    .collect::<Result<_, AdmissionError>>()?;
                self.check_policy_before_build(&[&frozen])?;
                let part_sources = crate::storage::policy::part_sources(&frozen.manifest)?;
                Ok(json!({"status":"accepted","storage":frozen.manifest.name,"declaration":frozen.declaration,"coverage":coverage,
                    "parts":part_sources,"columns":column_report(&frozen.manifest)?,"modules":frozen.modules.iter().map(|m| json!({"file":m.file,"role":m.role,"items_from_verus":m.items_from_verus})).collect::<Vec<_>>(),
                    "workspace_framework_rewritten":rewritten,"workspace_framework":crate_dir.join("src"),
                    "checks":if self.role == Some(AuthorRole::Engine) {
                        "manifest, author file set, central source rule over both author roots, framework files, the data_policy declaration of every part under the run's storage policy; under physical_only, that it holds each column once (against the other storages of an engine submission at evaluation and admission); items are checked against Verus output by storage_compile/storage_build"
                    } else {
                        "manifest, author file set, central source rule over both author roots, framework files, the data_policy declaration of every part under the run's storage policy and, under physical_only, that no column it declares as base_payload is already stored by a serving storage of another name (again with its package at evaluation and registration); items are checked against Verus output by storage_compile/storage_build"
                    }}))
            }
            ToolAction::StorageVerify if !arguments.modules.is_empty() => {
                let run = compile::verify_modules(&self.config.locks, &krate, CrateKind::Storage, &frozen.compiler, &arguments.modules, &verus_dir)?;
                Ok(json!({"status":"verified_modules","scope":arguments.modules,"verification":run["verification"],"detail":run["detail"],"wall_ns":run["wall_ns"],
                    "argv":run["argv"],"record":verus_dir.join("run.json"),"note":"module-scoped diagnostic run: NOT a whole-crate verification"}))
            }
            ToolAction::StorageVerify => {
                let run = compile::verify(&self.config.locks, &krate, CrateKind::Storage, &frozen.compiler, &verus_dir)?;
                Ok(json!({"status":"verified","verification":run["verification"],"wall_ns":run["wall_ns"],"argv":run["argv"],"record":verus_dir.join("run.json")}))
            }
            ToolAction::StorageCompile => {
                let (run, library) = compile::compile(&self.config.locks, &krate, CrateKind::Storage, &frozen.compiler, &verus_dir)?;
                let stdout = run["stdout"].as_str().unwrap_or_default();
                let items = declared_items(&frozen.declared_modules(stdout)?, &krate, CrateKind::Storage, stdout)?;
                Ok(json!({"status":"compiled","verification":run["verification"],"wall_ns":run["wall_ns"],"argv":run["argv"],"library":library,"items":items,"record":verus_dir.join("run.json")}))
            }
            ToolAction::StorageBuild if arguments.verification() == TrialVerification::NotRun => {
                let (built, reused) = self.diagnostic_storage(&frozen, &frozen_dir, job)?;
                let mut result = built.record.clone();
                result["reused"] = json!(reused);
                Ok(result)
            }
            ToolAction::StorageBuild | ToolAction::StorageRegister => {
                let (mut checked, reused) = self.check_storage(&frozen, &frozen_dir, job, &BTreeSet::new())?;
                let mut result = checked.record.clone();
                result["build"] = json!({"reused":reused,"note":"a checked storage of equal sources is reused within the session; its asset is built at most once per capture"});
                if action == ToolAction::StorageRegister {
                    let by = json!({"role":role,"session":self.session_root()?,"job":job});
                    let registration = self.register(&mut checked, &frozen, by)?;
                    result["asset"] = checked.record["asset"].clone();
                    let store = self.store()?;
                    let (package, _) = catalog::admitted_storage(&store, registration.package)?;
                    let capture = CurrentCapture::of(&self.capture.current()).map_err(AdmissionError::tool)?;
                    let reopened = gendb_storage::versions::resolve_storage_assets(&store, [(package.name.as_str(), registration.package, &package)], &capture)
                        .map_err(AdmissionError::tool)?;
                    result["status"] = json!("registered");
                    result["registration"] = json!({"registration":registration,"reopened_from_library":reopened.iter().map(|r| json!({"asset":r.asset_id,"directory":r.directory})).collect::<Vec<_>>(),
                        "use_as":{"name":package.name,"admitted":registration.package}});
                }
                Ok(result)
            }
            _ => unreachable!("storage_job runs storage actions only"),
        }
    }

    /// A query tool: freeze the named query candidate for `statement` into the job, then the action.
    fn query_job(&mut self, workspace: &Path, job: &Path, statement: usize, action: ToolAction, arguments: &LocalJobArguments) -> Result<Value, AdmissionError> {
        let input = arguments.candidate.as_ref().expect("checked: query tools carry a candidate");
        let (_, relative) = resolve_candidate_manifest(workspace, input).map_err(AdmissionError::missing_input)?;
        let submission = CandidateSubmission { candidate_manifest: relative, rationale: "local job".into(), data_access_analysis: "diagnostic snapshot".into() };
        let frozen_dir = job.join("frozen");
        let (frozen, written) = self.freeze_query(statement, &frozen_dir, &submission)?;
        let krate = frozen.candidate.crate_in(&frozen_dir);
        let artifacts = json!({"frozen_candidate":frozen_dir.join("candidate.json"),"frozen_crate":krate.root,"author_files":krate.author_files,
            "storage_uses":frozen.candidate.storage_uses});
        let verus_dir = job.join("verus");
        let locks = &self.config.locks;
        match action {
            ToolAction::Check => {
                let rewritten = write_workspace_framework(&written.workspace_crate, &written.framework)?;
                return Ok(json!({"status":"accepted","artifacts":artifacts,"workspace_framework_rewritten":rewritten,"workspace_framework":written.workspace_crate.join("src"),
                    "checks":"manifest, storage uses, coverage of the statement's demand, storage composition, central source rule, framework files; items are checked against Verus output by verify/compile"}));
            }
            ToolAction::Verify if !arguments.modules.is_empty() => {
                let run = compile::verify_modules(locks, &krate, CrateKind::Query, &frozen.candidate.compiler, &arguments.modules, &verus_dir)?;
                return Ok(json!({"status":"verified_modules","scope":arguments.modules,"verification":run["verification"],"detail":run["detail"],"wall_ns":run["wall_ns"],
                    "argv":run["argv"],"record":verus_dir.join("run.json"),"artifacts":artifacts,
                    "note":"module-scoped diagnostic run: NOT a whole-crate verification; submissions are always verified whole"}));
            }
            ToolAction::Verify => {
                // Identical crate content verified before (a passing verify or whole-crate compile) is not checked again.
                let key = frozen.candidate.source_key(&krate)?;
                let cached = self.verified_queries.get(&key).cloned()
                    .or_else(|| self.query_builds.get(&(TrialVerification::WholeCrate, key.clone())).map(|(_, record)| record.clone()));
                if let Some(record) = cached {
                    return Ok(json!({"status":"verified","reused":true,"verification":record["verification"],"record":record["record"],"artifacts":artifacts,"crate_version":crate_version(&key),
                        "note":"identical crate content was verified whole before in this session; not run again"}));
                }
                let run = compile::verify(locks, &krate, CrateKind::Query, &frozen.candidate.compiler, &verus_dir)?;
                let record = json!({"verification":run["verification"],"record":verus_dir.join("run.json")});
                self.verified_queries.insert(key.clone(), record);
                return Ok(json!({"status":"verified","reused":false,"verification":run["verification"],"wall_ns":run["wall_ns"],"argv":run["argv"],"record":verus_dir.join("run.json"),"artifacts":artifacts,"crate_version":crate_version(&key)}));
            }
            ToolAction::Compile | ToolAction::Trial | ToolAction::Profile => {}
            _ => unreachable!("query_job runs query actions only"),
        }
        let verification = arguments.verification();
        let (library, build, reused) = match verification {
            TrialVerification::WholeCrate => self.compile_query(&frozen, &verus_dir, false)?,
            TrialVerification::NotRun => self.compile_query_unverified(&frozen, &verus_dir)?,
        };
        let build = json!({"reused":reused,"record":build});
        if action == ToolAction::Compile {
            return Ok(json!({"status":"compiled","build":build,"artifacts":artifacts}));
        }
        let storages = self.resolve_storages_as(&frozen, job, verification)?;
        let kind = if action == ToolAction::Trial { TrialKind::Trial } else { TrialKind::Profile };
        let source_key = frozen.candidate.source_key(&krate)?;
        let tiny_key = (verification, source_key.clone(), storages.iter().map(|s| s.asset).collect::<Vec<_>>(), arguments.workers);
        let session = self.statements[statement].clone();
        let locks = self.config.locks.clone();
        let mut result = session.trial(job, &library, &storages, kind, arguments.workers, arguments.hot_calls, arguments.timeout_seconds, arguments.arguments.as_deref(),
            self.tiny_cases_passed.contains(&tiny_key) || self.tiny_cases_passed.contains(&(tiny_key.0, tiny_key.1.clone(), tiny_key.2.clone(), None)), || locks.timing())?;
        // Only tiny cases that actually ran and passed are remembered (never a `not_run` record of the validation policy).
        if result.pointer("/boundary/status") == Some(&json!("allowed")) {
            self.tiny_cases_passed.insert(tiny_key);
        }
        result["crate_version"] = json!(crate_version(&source_key));
        if verification == TrialVerification::NotRun {
            result["status"] = json!("diagnostic_unverified");
            result["verification"] = json!(UNVERIFIED_LABEL);
            result["note"] = json!(UNVERIFIED_NOTE);
        }
        result["build"] = build;
        result["artifacts"] = artifacts;
        Ok(result)
    }
}
