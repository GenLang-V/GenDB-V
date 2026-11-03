//! The query role: one author session writes Rust with Verus proofs for one SQL statement over stored data (fixed
//! entry v4, or v5 under declared integrity constraints).
//!
//! Stages (`SynthesisRole`): `prepare` writes the workspace, the contract bundle (with the admitted storages) and the
//! tool context; `freeze` snapshots a submission over its declared storage uses; `evaluate` runs the one whole-crate
//! verify-and-compile and then the framework's tests of that library over the storage assets; `qualify` registers the
//! candidate's new storages and admits the package; `close` serves it again from the library. For a reselection
//! without an author, `policy_exclusion` judges a recorded evaluation's storage uses against the run's storage policy
//! and the library's exclusions, and `import_frozen` copies another session's frozen candidate (`query::import`). For a
//! session that continues from an earlier session's admitted candidate, `seed_incumbent` writes that candidate into
//! the workspace (`query::incumbent`).
//! The author's local jobs
//! (`LocalJobs`) run the same freeze, Verus runs, storage builds and tests as diagnostics through the session's
//! [`Workbench`]. Everything runs on the retained owner thread of the session (`controller::session::RetainedRole`),
//! so compiled libraries and checked storages are reused across jobs and stages.
//!
//! The statement, preflight and prepared-data references are established before the role exists (a refusal there
//! precedes any author call): the caller opens the [`QuerySession`] and gives it to the bench.

use super::QuerySession;
use super::compile::agent_modules;
use super::library::library_inventory;
use super::source_items::requires_ensures;
use crate::controller::author::CandidateSubmission;
use crate::controller::records::{now_unix_ms, read_json, write_json_atomic, write_new_json};
use crate::controller::session::{LocalJobs, LocalSessionEndpoint};
use crate::controller::{QualificationAttempt, RunRequest, SeededIncumbent, SynthesisRole, Trial};
use crate::prompts::{EarlyStop, RuntimeTarget};
use crate::prompts::VerifiedQueryPolicy;
use crate::prompts::brief::{self, BriefInputs};
use crate::query::candidate::FrozenCandidate;
use crate::tools::bench::{FrozenQuery, Workbench};
use crate::tools::{self, AuthorRole};
use crate::storage::freeze::FrozenStorage;
use crate::storage::library_lock::{BUDGET_LOCK, LibraryLock};
use crate::storage::policy::StoredDataPolicy;
use gendb_artifacts::verus::VerusStorageUseV1;
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_verification::admission::AdmissionError;
use gendb_verification::admission::qualification_v4::{QueryV4Candidate, QueryV4Context, qualify_v4};
use serde_json::{Value, json};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;

/// The claim of an exact verified evaluation (recorded with it).
const VERIFIED_EXACT_CLAIM: &str = "Verus checked the whole frozen query crate (framework + copied storage interfaces + agent) with 0 errors under the recorded TCB; the compiled library of that same directory returned allowed results (ordered_ok: value, scale, order, ties) over the storage assets on the prepared data and over tiny storage assets of the generated tiny cases (tests)";
/// The claim of a verified evaluation under the validation policy `formal_proofs`.
const VERIFIED_FORMAL_CLAIM: &str = "Verus checked the whole frozen query crate (framework + copied storage interfaces + agent) with 0 errors under the recorded TCB: the fixed final SQL claim is the correctness claim. The compiled library of that same directory ran over the storage assets on the full prepared data at every benchmark binding and worker count; its results agree with the saved answers of other engines where given (real_data cells saved_answers_agree: every engine, or saved_answers_agree_partly with the other engines' differences recorded; agreement, not proof) and are not_compared elsewhere. Validation policy formal_proofs: no tiny cases or reference engine";

/// What the query role adds to its bench: the author's view of the user's request.
pub struct QueryRoleConfig {
    /// The request's hardware record (configured worker counts).
    pub hardware: Value,
    /// What the host exposes (CPUs, caches), recorded for the author.
    pub observed_hardware: Value,
    /// User-supplied runtime targets of the execution-time objective (`QuerySession::performance`): search guidance
    /// with provenance, shown to the author and in the objective status; empty for correctness or without targets.
    pub runtime_targets: Vec<RuntimeTarget>,
    /// The user's early stop of the execution-time objective (`EarlyStop`), if set. A query author gets only its own
    /// statement's facts: no other statement of the workload.
    pub early_stop: Option<EarlyStop>,
}

/// The query role of one author session.
pub struct QueryAuthorRole {
    bench: Workbench,
    config: QueryRoleConfig,
}

impl QueryAuthorRole {
    /// The role over `bench`, whose one statement is this session's.
    pub fn new(bench: Workbench, config: QueryRoleConfig) -> Self {
        Self { bench, config }
    }

    fn session(&self) -> Arc<QuerySession> {
        self.bench.statements[0].clone()
    }

    fn prepare_workspace(&mut self, request: &RunRequest, workspace: &Path) -> Result<Value, AdmissionError> {
        let workspace = self.bench.open_workspace(workspace)?;
        let store = self.bench.store()?;
        let library = library_inventory(&store, &workspace.join("prior-verus-code"), &self.bench.config.storage_policy)?;
        let session = self.session();
        let inputs = BriefInputs {
            session: &session,
            task: &request.task,
            limits: &request.limits,
            library: &library,
            store: &store,
            capture: &self.bench.capture.current(),
            hardware: &self.config.hardware,
            observed_hardware: &self.config.observed_hardware,
            free_bytes: super::assets::free_bytes_at(&workspace),
            runtime_targets: &self.config.runtime_targets,
            early_stop: self.config.early_stop,
            data_allowance: self.bench.config.live_bytes_allowance,
            storage_policy: &self.bench.config.storage_policy,
        };
        let context = brief::write_author_contract(&workspace, &inputs)?;
        let tool_context = self.bench.tool_context(AuthorRole::Query, workspace.join(brief::CONTRACT_DIRECTORY).join("index.json"))?;
        write_json_atomic(&workspace.join(tools::CONTEXT_FILE), &tool_context).map_err(AdmissionError::tool)?;
        Ok(context)
    }

    fn frozen(frozen_dir: &Path, candidate: &Value) -> Result<FrozenQuery, AdmissionError> {
        let candidate: FrozenCandidate = serde_json::from_value(candidate.clone()).map_err(AdmissionError::tool)?;
        Ok(FrozenQuery { statement: 0, candidate, frozen_dir: frozen_dir.to_path_buf() })
    }

    /// Verify and compile a frozen candidate once (evaluation evidence) and test its library over its storages.
    fn evaluate_frozen(&mut self, dir: &Path, frozen: &FrozenQuery) -> Result<Value, AdmissionError> {
        let build_dir = dir.join("verus-build");
        let (library, build, _) = self.bench.compile_query(frozen, &build_dir, true)?;
        let storages = self.bench.resolve_storages(frozen, dir)?;
        // The storage budget is part of the verdict: the submission's new storages together must fit.
        let new: Vec<(String, ContentId, PathBuf)> =
            storages.iter().filter(|s| !s.admitted).map(|s| (s.name.to_string(), s.package, s.parts.clone())).collect();
        let budget = self.bench.check_new_storage_bytes(&self.bench.store()?, &new, "admitting")?;
        // One stored copy of each column (storage policy): the new storages against each other and the serving storage.
        let workspace: Vec<(PathBuf, FrozenStorage)> =
            storages.iter().filter(|s| !s.admitted).map(|s| frozen.candidate.workspace_storage(&frozen.frozen_dir, s.name.as_str())).collect::<Result<_, _>>()?;
        let packages: Vec<(&FrozenStorage, ContentId)> = workspace.iter().map(|(_, f)| f).zip(storages.iter().filter(|s| !s.admitted).map(|s| s.package)).collect();
        self.bench.check_new_storage_payload(&self.bench.store()?, &packages)?;
        // Its admitted uses join the serving storage when it is admitted: one copy of each column, within the budget.
        let admitted: Vec<(String, ContentId)> = storages.iter().filter(|s| s.admitted).map(|s| (s.name.to_string(), s.package)).collect();
        let storage_uses = self.bench.check_query_storage_uses(&self.bench.store()?, &admitted)?;
        let session = self.session();
        let locks = &self.bench.config.locks;
        let mut evaluation = session.evaluate_submission(dir, &library, &storages, || locks.timing())?;
        evaluation["verus"] = json!({"outcome":build["outcome"],"detail":build["detail"],"verification":build["verification"],"wall_ns":build["wall_ns"],"record":build["record"]});
        evaluation["items"] = build["items"].clone();
        evaluation["storage_budget"] = budget;
        evaluation["storage_uses_at_admission"] = storage_uses;
        Ok(evaluation)
    }

    /// Register the candidate's new storages, then admit the package (`qualify_v4`) with the evaluation.
    fn qualify_evaluated(&mut self, frozen_dir: &Path, evaluation: &Value) -> Result<Value, AdmissionError> {
        if evaluation["eligible"] != true {
            return Err(AdmissionError::refusal("only an exact verified evaluation is qualified"));
        }
        let candidate: Value = read_json(&frozen_dir.join("candidate.json")).map_err(AdmissionError::tool)?;
        let frozen = Self::frozen(frozen_dir, &candidate)?;
        if self.bench.config.storage_policy.is_fixed_flat() {
            // Also for a candidate imported from another session (reselection), which was frozen elsewhere.
            let files = crate::query::candidate::crate_files(&frozen.candidate.crate_in(frozen_dir))?;
            if let Some(reason) = crate::storage::flat::static_item_refusal(files.iter().map(|f| (f.path.as_str(), f.text.as_str()))) {
                return Err(AdmissionError::refusal(reason));
            }
        }
        let record = evaluation["verus"]["record"].as_str().ok_or_else(|| AdmissionError::tool("evaluation lacks its Verus record"))?;
        let verus_run: Value = read_json(Path::new(record)).map_err(AdmissionError::tool)?;
        let registered_by = json!({"role":AuthorRole::Query,"session":self.bench.session_root()?,"qualification":frozen_dir});
        let uses = self.bench.register_workspace_storages(&frozen, &frozen_dir.join(format!("qualification-{}", now_unix_ms())), &registered_by)?;
        // From the prospective serving-storage check through the package's admission (record publication only, no
        // proof, build or timing), hold the library budget lock that storage registration takes, so no replacement of a
        // storage it reads can interleave (taken after its own storages are registered under the same lock).
        let store = self.bench.store()?;
        let _inventory_lock = LibraryLock::acquire(&store, BUDGET_LOCK)?;
        self.bench.check_query_storage_uses(&store, &uses.iter().map(|(name, package, _)| (name.clone(), *package)).collect::<Vec<_>>())?;
        let items: Vec<Value> = serde_json::from_value(evaluation["items"].clone()).map_err(AdmissionError::tool)?;
        let assets = evaluation["storage"].as_array().into_iter().flatten().filter_map(|s| serde_json::from_value(s["asset"].clone()).ok()).collect();
        let session = self.session();
        let clause_text = |text: &str, name: &str| requires_ensures(text, name);
        let context = QueryV4Context {
            library: &self.bench.config.library,
            statement: session.statement(),
            dataset: self.bench.capture.dataset(),
            parser: &self.bench.config.parser,
            clause_text: &clause_text,
        };
        let candidate = QueryV4Candidate {
            frozen_root: &frozen.candidate.crate_in(frozen_dir).root,
            verus_run: &verus_run,
            storage_uses: uses.iter().map(|(name, package, _)| VerusStorageUseV1 { name: name.clone(), package: *package }).collect(),
            modules: agent_modules(&frozen.candidate.agent_modules(), &items),
            evaluation,
            assets,
        };
        let mut record = qualify_v4(&context, candidate)?.record();
        record["registered_storages"] = json!(uses.iter().filter_map(|(_, _, registration)| registration.as_ref()).collect::<Vec<_>>());
        Ok(record)
    }
}

/// Why `policy` no longer admits the storage uses a recorded query evaluation names (`storage[]`): an admitted use as
/// qualification would judge it (user exclusion, registration kind, listing), a workspace use by the user's
/// exclusion of its package only (its registration under the run's policy happens at qualification). `None`: every
/// use is admitted. Reads only library records.
pub fn recorded_policy_exclusion(policy: &StoredDataPolicy, store: &ObjectStore, evaluation: &Value) -> Result<Option<String>, AdmissionError> {
    if policy.is_unrestricted() {
        return Ok(None);
    }
    for used in evaluation["storage"].as_array().into_iter().flatten() {
        let package = used["package"]
            .as_str()
            .and_then(|text| ContentId::parse_hex(text).ok())
            .ok_or_else(|| AdmissionError::tool(format!("recorded storage use without a package id: {used}")))?;
        let reason = if used["admitted"] == true {
            policy.ineligible(store, package, used["name"].as_str().unwrap_or_default())?
        } else {
            policy.excluded(store, package)?
        };
        if reason.is_some() {
            return Ok(reason);
        }
    }
    Ok(None)
}

/// Protect the session's trial assets an eligible evaluation used, before its record is written (qualification
/// publishes exactly those). A failure to record protection is noted on the evaluation, which stays as it is: the
/// session's durable evaluation records protect it as well (`query::assets`).
pub fn protect_eligible_assets(bench: &mut Workbench, evaluation: &mut Value, dir: &Path) {
    if evaluation["eligible"] != true {
        return;
    }
    let assets = super::assets::evaluation_assets(evaluation);
    if let Err(error) = bench.protect_assets(&assets, &format!("eligible evaluation {}", dir.display())) {
        evaluation["trial_asset_protection_error"] = json!(error.to_string());
    }
}

/// At close: remove the session's remaining trial assets, keeping the best eligible candidate's when nothing
/// qualified; the record of what was removed and kept (an error is recorded, never fails the close).
pub fn release_trial_assets(bench: &mut Workbench, trials: &[Trial], qualified: bool) -> Value {
    let keep = super::assets::close_keep(trials, qualified);
    bench.release_trial_assets(&keep).unwrap_or_else(|error| json!({"error":error.to_string(),"note":"nothing further removed; `gendb reclaim-trial-assets` lists what remains"}))
}

/// A fresh evaluation directory of a frozen submission: a resumed controller may evaluate the same frozen submission
/// again, and the frozen crate itself is never rewritten.
pub fn fresh_evaluation_dir(frozen_dir: &Path) -> Result<PathBuf, AdmissionError> {
    for ordinal in 0.. {
        let dir = frozen_dir.join(format!("evaluation-{ordinal}"));
        if fs::create_dir(&dir).is_ok() {
            return Ok(dir);
        }
        if !dir.exists() {
            return Err(AdmissionError::tool(format!("cannot create {}", dir.display())));
        }
    }
    unreachable!("an unbounded ordinal range")
}

impl SynthesisRole for QueryAuthorRole {
    type Policy = VerifiedQueryPolicy;

    fn policy(&self) -> VerifiedQueryPolicy {
        VerifiedQueryPolicy
    }

    async fn prepare(&mut self, request: &RunRequest, workspace: &Path) -> Result<Value, String> {
        self.prepare_workspace(request, workspace).map_err(|e| e.to_string())
    }

    /// The storage budget as it stands now (the catalog and budget files of the contract are rewritten too).
    async fn refresh_shared_facts(&mut self) -> Result<Value, String> {
        self.bench.refresh_shared_facts().map(|facts| json!({"storage_budget":facts["storage_budget"]})).map_err(|e| e.to_string())
    }

    async fn freeze(&mut self, _workspace: &Path, frozen_dir: &Path, submission: &CandidateSubmission) -> Result<Value, String> {
        self.bench.freeze_query(0, frozen_dir, submission).map(|(frozen, _)| json!(frozen.candidate)).map_err(|e| e.to_string())
    }

    /// The complete offline check of a frozen submission (tests after the proof; never proof). Its record is
    /// `<frozen>/evaluation-<k>/verus-evaluation.json`.
    async fn evaluate(&mut self, frozen_dir: &Path, candidate: &Value) -> Result<Value, String> {
        let started = Instant::now();
        let dir = fresh_evaluation_dir(frozen_dir).map_err(|e| e.to_string())?;
        let outcome = Self::frozen(frozen_dir, candidate).and_then(|frozen| self.evaluate_frozen(&dir, &frozen));
        let mut result = match outcome {
            Ok(mut value) => {
                value["kind"] = json!("verus_stored");
                value["eligible"] = json!(true);
                let formal = self.bench.statements[0].preflight.validation.formal;
                value["status"] = json!(if formal { "verified" } else { "verified_exact" });
                value["claim"] = json!(if formal { VERIFIED_FORMAL_CLAIM } else { VERIFIED_EXACT_CLAIM });
                value
            }
            Err(error) => {
                let record = dir.join("verus-build/run.json");
                json!({"kind":"verus_stored","eligible":false,"status":error.class,"failure_class":error.class,"error":error.to_string(),
                    "verus_record":record.is_file().then_some(record)})
            }
        };
        result["framework_evaluation_ns"] = json!(started.elapsed().as_nanos());
        result["evaluation_record"] = json!(dir.join("verus-evaluation.json"));
        protect_eligible_assets(&mut self.bench, &mut result, &dir);
        write_new_json(&dir.join("verus-evaluation.json"), &result).map_err(|e| e.to_string())?;
        Ok(result)
    }

    async fn qualify(&mut self, frozen_dir: &Path, evaluation: &Value) -> Result<Value, String> {
        self.qualify_evaluated(frozen_dir, evaluation).map_err(|e| e.to_string())
    }

    /// Serve the admitted package again from library records and compare with the reference; no author call.
    async fn close(&mut self, trials: &[Trial], qualification: &[QualificationAttempt]) -> Result<Value, String> {
        let admissions: Vec<Value> = qualification.iter().filter(|q| q.qualified()).map(|q| q.result["admission"].clone()).collect();
        let mut closed = if admissions.is_empty() {
            json!({"status":"no_qualified_verus_package","served":[]})
        } else {
            let session = self.session();
            let work = self.bench.session_root().map_err(|e| e.to_string())?.join(format!("verus-serving-{}", now_unix_ms()));
            let locks = &self.bench.config.locks;
            session.close(&self.bench.config.library, self.bench.capture.current(), &work, admissions.clone(), || locks.timing()).map_err(|e| e.to_string())?
        };
        closed["trial_assets"] = release_trial_assets(&mut self.bench, trials, !admissions.is_empty());
        Ok(closed)
    }

    async fn policy_exclusion(&mut self, evaluation: &Value) -> Result<Option<String>, String> {
        let store = self.bench.store().map_err(|e| e.to_string())?;
        recorded_policy_exclusion(&self.bench.config.storage_policy, &store, evaluation).map_err(|e| e.to_string())
    }

    async fn import_frozen(&mut self, source: &Path, frozen_dir: &Path) -> Result<Value, String> {
        super::import::import_frozen(source, frozen_dir).map(|candidate| json!(candidate)).map_err(|e| e.to_string())
    }

    async fn seed_incumbent(&mut self, source: &Path, workspace: &Path) -> Result<SeededIncumbent, String> {
        super::incumbent::seed_workspace(source, workspace).map_err(|e| e.to_string())
    }
}

impl LocalJobs for QueryAuthorRole {
    fn attach_local_session(&mut self, endpoint: &LocalSessionEndpoint) {
        self.bench.attach(endpoint);
    }

    async fn run_local_job(&mut self, evidence_root: &Path, action: &str, arguments: Value, job_id: u64) -> Result<Value, String> {
        self.bench.local_job(AuthorRole::Query, evidence_root, action, arguments, job_id).map_err(|e| e.to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::storage::exclusion::record_exclusion;
    use gendb_artifacts::verus::VERUS_STORAGE_PACKAGE_KIND;

    /// A recorded evaluation is judged on its storage uses alone: the user's exclusion of a workspace or admitted
    /// package excludes it; an unregistered workspace package is not excluded (registration happens at
    /// qualification); `unrestricted` reads nothing.
    #[test]
    fn recorded_evaluations_are_judged_by_the_library_exclusions_of_their_storage_uses() {
        let root = crate::controller::test_support::scratch_root("recorded-policy-exclusion");
        let store = ObjectStore::open(&root.join("library")).unwrap();
        let excluded = store.put(1, VERUS_STORAGE_PACKAGE_KIND, &json!({"name":"s_locators"})).unwrap();
        let kept = store.put(1, VERUS_STORAGE_PACKAGE_KIND, &json!({"name":"s_own"})).unwrap();
        record_exclusion(&store, "physical_only", excluded, "review: stores another table's row ranges").unwrap();
        let physical: StoredDataPolicy = serde_json::from_value(json!({"kind":"physical_only"})).unwrap();
        let uses = |package: ContentId, admitted: bool| json!({"eligible":true,"storage":[{"name":"s","package":package,"admitted":admitted}]});
        let judged = |policy: &StoredDataPolicy, evaluation: Value| recorded_policy_exclusion(policy, &store, &evaluation).unwrap();
        assert!(judged(&physical, uses(excluded, false)).unwrap().starts_with("storage_policy_excluded"), "a workspace use of an excluded package");
        assert!(judged(&physical, uses(excluded, true)).unwrap().starts_with("storage_policy_excluded"), "an admitted use of an excluded package");
        assert_eq!(judged(&physical, uses(kept, false)), None, "an unregistered workspace package is judged at qualification");
        assert_eq!(judged(&StoredDataPolicy::Unrestricted, uses(excluded, false)), None);
        assert!(recorded_policy_exclusion(&physical, &store, &json!({"storage":[{"name":"s"}]})).is_err(), "a use without its package id");
        std::fs::remove_dir_all(root).unwrap();
    }
}
