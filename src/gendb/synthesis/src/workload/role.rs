//! The workload storage role: one author session that designs, proves and builds storages for every statement of the
//! workload before any query session starts.
//!
//! Stages (`SynthesisRole`): `prepare` writes the workspace, the workload contract bundle and the tool context;
//! `freeze` snapshots a workload submission (`verus-storages.json`); `evaluate` checks and builds every submitted
//! storage (the whole-crate verify-and-compile, the checked build recorded, its asset over the current capture built
//! once by the stored library, builds over the statements' tiny inputs unless the validation policy is
//! `formal_proofs`), after checking that the submitted storages
//! with the usable admitted ones store every column of every table (`storage::coverage`, `storage_coverage_incomplete`);
//! `qualify` checks coverage again and registers every storage (admission; nothing is rebuilt; each registration within
//! the storage budget, `storage::budget`); `close` records the admitted storages. The objective admits the first verified, built
//! submission; the author compares layouts with the tools before submitting. Local jobs run through the same
//! [`Workbench`] as the query role's.

use super::submission::{FrozenWorkloadCandidate, freeze_workload};
use crate::controller::author::CandidateSubmission;
use crate::controller::records::{write_json_atomic, write_new_json};
use crate::controller::session::{LocalJobs, LocalSessionEndpoint};
use crate::controller::{QualificationAttempt, RunRequest, SynthesisRole, Trial};
use crate::prompts::StoragePolicy;
use crate::prompts::policy::RuntimeTarget;
use crate::prompts::brief::storage::{self as storage_brief, StorageBriefInputs};
use crate::query::role::{fresh_evaluation_dir, protect_eligible_assets, release_trial_assets};
use crate::storage::freeze::FrozenStorage;
use crate::tools::bench::Workbench;
use crate::tools::{self, AuthorRole};
use gendb_verification::admission::AdmissionError;
use gendb_artifacts::ContentId;
use serde_json::{Value, json};
use std::path::{Path, PathBuf};
use std::time::Instant;

/// The claim of an eligible storage evaluation.
const VERIFIED_BUILT_CLAIM: &str = "Verus checked every submitted storage crate whole (fixed storage entry + author interface and builder) with 0 errors under the recorded TCB; the stored library of each checked build built its asset over the current capture and every tiny input of the statements that read its tables with status Ok (tests; the fixed storage entry's claim, checked by Verus, is the correctness claim)";
/// [`VERIFIED_BUILT_CLAIM`] under the validation policy `formal_proofs` (no tiny-input builds).
const VERIFIED_BUILT_CLAIM_FORMAL: &str = "Verus checked every submitted storage crate whole (fixed storage entry + author interface and builder) with 0 errors under the recorded TCB (the fixed storage entry's claim is the correctness claim); the stored library of each checked build built its asset over the full current capture with status Ok; the submitted storages together store every column of every table; validation policy formal_proofs: no tiny-input builds were run";

/// What the workload role adds to its bench: the author's view of the user's request.
pub struct StorageRoleConfig {
    pub hardware: Value,
    pub observed_hardware: Value,
    /// Per bench statement (same index), the user's runtime targets of its query objective (empty: none).
    pub runtime_targets: Vec<Vec<RuntimeTarget>>,
}

/// The workload storage role of one author session.
pub struct StorageAuthorRole {
    bench: Workbench,
    config: StorageRoleConfig,
}

impl StorageAuthorRole {
    /// The role over `bench`, whose statements are every ready statement of the workload.
    pub fn new(bench: Workbench, config: StorageRoleConfig) -> Self {
        Self { bench, config }
    }

    fn prepare_workspace(&mut self, request: &RunRequest, workspace: &Path) -> Result<Value, AdmissionError> {
        let workspace = self.bench.open_workspace(workspace)?;
        let store = self.bench.store()?;
        let inputs = StorageBriefInputs {
            statements: &self.bench.statements,
            task: &request.task,
            limits: &request.limits,
            store: &store,
            capture: &self.bench.capture.current(),
            hardware: &self.config.hardware,
            observed_hardware: &self.config.observed_hardware,
            runtime_targets: &self.config.runtime_targets,
            free_bytes: crate::query::assets::free_bytes_at(&workspace),
            data_allowance: self.bench.config.live_bytes_allowance,
            storage_policy: &self.bench.config.storage_policy,
        };
        let context = storage_brief::write_workload_contract(&workspace, &inputs)?;
        let tool_context = self.bench.tool_context(AuthorRole::WorkloadStorage, workspace.join(storage_brief::CONTRACT_DIRECTORY).join("index.json"))?;
        write_json_atomic(&workspace.join(tools::CONTEXT_FILE), &tool_context).map_err(AdmissionError::tool)?;
        Ok(context)
    }

    /// Check and build every storage of a frozen submission (cached per source key within the session).
    fn evaluate_frozen(&mut self, dir: &Path, frozen_dir: &Path, candidate: &FrozenWorkloadCandidate) -> Result<Value, AdmissionError> {
        let mut storages = vec![];
        let mut checked = vec![];
        let candidate_storages = candidate.storages(frozen_dir)?;
        // Complete lossless coverage is decided from declarations, before anything is built.
        let coverage = self.bench.check_workload_coverage(&candidate_storages.iter().map(|(_, s)| &s.declaration).collect::<Vec<_>>())?;
        // So is one stored copy of each column among them and against other names' serving storages (storage policy).
        self.bench.check_policy_before_build(&candidate_storages.iter().map(|(_, s)| s).collect::<Vec<_>>())?;
        let mut keep = self.bench.checked_assets(candidate_storages.iter().map(|(dir, storage)| (dir.as_path(), storage)));
        for (storage_dir, storage) in &candidate_storages {
            let (checked_storage, reused) = self.bench.check_storage(storage, storage_dir, &dir.join(&storage.manifest.name), &keep)?;
            keep.insert(checked_storage.asset);
            let mut record = checked_storage.record.clone();
            record["reused_session_check"] = json!(reused);
            storages.push(record);
            checked.push(checked_storage);
        }
        // The storage budget is part of the verdict: the new assets together must fit once registered.
        let store = self.bench.store()?;
        let new: Vec<(String, ContentId, PathBuf)> = checked.iter().map(|c| (c.name.clone(), c.package, c.asset_directory.clone())).collect();
        let budget = self.bench.check_new_storage_bytes(&store, &new, "admitting")?;
        let packages: Vec<(&FrozenStorage, ContentId)> = candidate_storages.iter().map(|(_, s)| s).zip(checked.iter().map(|c| c.package)).collect();
        self.bench.check_new_storage_payload(&store, &packages)?;
        Ok(json!({"storages":storages,"coverage":coverage,"storage_budget":budget}))
    }

    fn qualify_evaluated(&mut self, frozen_dir: &Path, evaluation: &Value) -> Result<Value, AdmissionError> {
        if evaluation["eligible"] != true {
            return Err(AdmissionError::refusal("only a verified, built storage submission is qualified"));
        }
        let candidate: FrozenWorkloadCandidate = crate::controller::records::read_json(&frozen_dir.join("candidate.json")).map_err(AdmissionError::tool)?;
        let registered_by = json!({"role":AuthorRole::WorkloadStorage,"session":self.bench.session_root()?,"qualification":frozen_dir});
        let submitted = candidate.storages(frozen_dir)?;
        self.bench.check_workload_coverage(&submitted.iter().map(|(_, s)| &s.declaration).collect::<Vec<_>>())?;
        let mut checked = vec![];
        for (storage_dir, storage) in submitted {
            let keep = self.bench.checked_assets([(storage_dir.as_path(), &storage)]);
            let (storage_checked, _) = self.bench.check_storage(&storage, &storage_dir, &frozen_dir.join("qualification").join(&storage.manifest.name), &keep)?;
            checked.push((storage_checked, storage));
        }
        // Every storage of the submission is registered together, after one budget check (none when they do not fit).
        let admitted = self.bench.register_all(checked.iter_mut().map(|(c, s)| (c, &*s)).collect(), registered_by)?;
        let registrations: Vec<Value> =
            admitted.into_iter().zip(&checked).map(|(registration, (c, _))| json!({"registration":registration,"record":c.record})).collect();
        Ok(json!({"qualified":true,"kind":"verus_storages","admission":registrations.iter().map(|r| r["registration"]["admission"].clone()).collect::<Vec<_>>(),
            "registrations":registrations}))
    }
}

impl SynthesisRole for StorageAuthorRole {
    type Policy = StoragePolicy;

    fn policy(&self) -> StoragePolicy {
        StoragePolicy
    }

    async fn prepare(&mut self, request: &RunRequest, workspace: &Path) -> Result<Value, String> {
        self.prepare_workspace(request, workspace).map_err(|e| e.to_string())
    }

    /// The storage budget as it stands now (the catalog and budget files of the contract are rewritten too).
    async fn refresh_shared_facts(&mut self) -> Result<Value, String> {
        self.bench.refresh_shared_facts().map(|facts| json!({"storage_budget":facts["storage_budget"]})).map_err(|e| e.to_string())
    }

    async fn freeze(&mut self, workspace: &Path, frozen_dir: &Path, submission: &CandidateSubmission) -> Result<Value, String> {
        let store = self.bench.store().map_err(|e| e.to_string())?;
        freeze_workload(workspace, frozen_dir, submission, self.bench.schema(), Some(&store)).map(|c| json!(c)).map_err(|e| e.to_string())
    }

    async fn evaluate(&mut self, frozen_dir: &Path, candidate: &Value) -> Result<Value, String> {
        let started = Instant::now();
        let dir = fresh_evaluation_dir(frozen_dir).map_err(|e| e.to_string())?;
        let outcome = serde_json::from_value::<FrozenWorkloadCandidate>(candidate.clone())
            .map_err(AdmissionError::tool)
            .and_then(|candidate| self.evaluate_frozen(&dir, frozen_dir, &candidate));
        let mut result = match outcome {
            Ok(mut value) => {
                value["kind"] = json!("verus_storages");
                value["eligible"] = json!(true);
                value["status"] = json!("verified_built");
                let formal = self.bench.statements.first().is_some_and(|s| s.preflight.validation.formal);
                value["claim"] = json!(if formal { VERIFIED_BUILT_CLAIM_FORMAL } else { VERIFIED_BUILT_CLAIM });
                value
            }
            Err(error) => json!({"kind":"verus_storages","eligible":false,"status":error.class,"failure_class":error.class,"error":error.to_string()}),
        };
        result["framework_evaluation_ns"] = json!(started.elapsed().as_nanos());
        result["evaluation_record"] = json!(dir.join("storage-evaluation.json"));
        protect_eligible_assets(&mut self.bench, &mut result, &dir);
        write_new_json(&dir.join("storage-evaluation.json"), &result).map_err(|e| e.to_string())?;
        Ok(result)
    }

    async fn qualify(&mut self, frozen_dir: &Path, evaluation: &Value) -> Result<Value, String> {
        self.qualify_evaluated(frozen_dir, evaluation).map_err(|e| e.to_string())
    }

    /// The admitted storages of the session (no build, no author call).
    async fn close(&mut self, trials: &[Trial], qualification: &[QualificationAttempt]) -> Result<Value, String> {
        let admitted: Vec<Value> = qualification
            .iter()
            .filter(|q| q.qualified())
            .flat_map(|q| q.result["registrations"].as_array().cloned().unwrap_or_default())
            .map(|r| {
                let asset = &r["record"]["asset"];
                json!({"name":r["registration"]["name"],"package":r["registration"]["package"],"admission":r["registration"]["admission"],
                    "asset":asset["asset"],"storage_bytes":asset["storage_bytes"],"build_wall_ns":asset["build_wall_ns"],
                    "canonical_column_bytes":asset["canonical_column_bytes"],"parts":asset["parts"],"layout":r["record"]["layout"]})
            })
            .collect();
        let status = if admitted.is_empty() { "no_admitted_storage" } else { "storages_admitted" };
        let trial_assets = release_trial_assets(&mut self.bench, trials, qualification.iter().any(|q| q.qualified()));
        Ok(json!({"status":status,"storages":admitted,"trial_assets":trial_assets,
            "use":"query sessions list these (with every other admitted storage) in their contract storages.json and may reuse, extend or replace them"}))
    }
}

impl LocalJobs for StorageAuthorRole {
    fn attach_local_session(&mut self, endpoint: &LocalSessionEndpoint) {
        self.bench.attach(endpoint);
    }

    async fn run_local_job(&mut self, evidence_root: &Path, action: &str, arguments: Value, job_id: u64) -> Result<Value, String> {
        self.bench.local_job(AuthorRole::WorkloadStorage, evidence_root, action, arguments, job_id).map_err(|e| e.to_string())
    }
}
