//! A query session without an author that admits a published package (`gendb import`, run by
//! `controller::workload_run::import`). The package's author files (its `agent/**`) are written into the session's
//! workspace with a manifest that reads the storages this import admitted, then frozen, evaluated, qualified and closed
//! by the query role exactly as an author's submission would be: the freeze generates every framework file for this
//! run's statement and storages (nothing of the published crate but its author files is used) and applies the source
//! rules; the evaluation verifies and compiles the whole crate with Verus and runs it over the stored data under the
//! run's validation policy; qualification admits the package into the run's library; the close serves it again.
//!
//! Phases (each durable before the next, so a rerun repeats no completed seed, freeze, evaluation, qualification or
//! closure):
//! 1. open the session's ledger (its resume identity names the published crate) and return an existing closure;
//! 2. prepare the role context (as `run` does; no author is configured or called);
//! 3. seed and freeze, once: the published author files and manifest written into the workspace
//!    (`published::seed_query_workspace`), frozen by the role into `iterations/0001`; `source.json` (provenance and
//!    the freeze outcome), written last, marks both done; an interrupted seed or freeze is started again;
//! 4. evaluate the frozen candidate (`evaluation.json`); a framework failure (not the candidate's) is evaluated once
//!    more, and a second one stops the session resumably;
//! 5. qualify an eligible candidate (`qualification.json`);
//! 6. close: the role's resolution (`resolution.json`) and the summary, which states that no author was called.
//!
//! A freeze refusal, an ineligible evaluation or a refused qualification is the session's recorded outcome: it closes
//! with no package and nothing else is tried.

use super::ControllerError;
use super::layout::RunLayout;
use super::ledger::{Ledger, Trial, TrialStatus, attribute_repeated_checker_failure, framework_failure};
use super::records::{self, RecordError};
use super::reselect::SOURCE_FILE;
use super::role::{RolePolicy, SynthesisRole};
use super::run::{RunRequest, evaluation_digest, evaluation_error, prepare_context, qualification_digest, qualify_recorded, role_error};
use super::schedule::{CloseHook, in_parallel, record_framework_error, record_results};
use crate::published::{PublishedQuery, seed_query_workspace};
use gendb_artifacts::ContentId;
use serde_json::{Value, json};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

/// The summary `reason` of an import session.
pub const IMPORTED: &str = "imported_from_published_package";

/// The iteration of the imported candidate (the session's only one).
pub const IMPORT_ITERATION: u32 = 1;

/// What one import session admits: a published query package over admitted storages.
#[derive(Clone, Debug)]
pub struct ImportCandidate {
    /// The published folder it comes from.
    pub published_run: PathBuf,
    pub query: PublishedQuery,
    /// The storages it reads, in use order: each name with the admitted package of this run's library.
    pub uses: Vec<(String, ContentId)>,
}

/// One import session to run (see [`run_import_sessions`]).
pub struct ImportSession<R> {
    /// The session's run directory.
    pub directory: PathBuf,
    pub request: RunRequest,
    pub role: R,
    pub candidate: ImportCandidate,
    /// Called once with the summary when the session closes without a framework error.
    pub on_close: Option<CloseHook>,
}

/// Run `sessions` in order, at most `max_concurrent` at a time, each on its own thread with its own single-threaded
/// async runtime (the scheduler's pool, `schedule::in_parallel`). One result per session, in order: its summary, or a
/// resumable `framework_error` record (also written in its directory). The results are recorded in `summary_dir` as a
/// new `workload-summary[-N].json`.
pub fn run_import_sessions<R: SynthesisRole + Send>(sessions: Vec<ImportSession<R>>, summary_dir: &Path, max_concurrent: usize) -> Result<Vec<Value>, ControllerError> {
    let results = in_parallel(sessions, max_concurrent, |mut session| {
        let outcome = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .map_err(|e| e.to_string())
            .and_then(|runtime| runtime.block_on(import_session(&session.request, &session.directory, &session.candidate, &mut session.role)).map_err(|e| e.to_string()));
        match outcome {
            Ok(summary) => {
                if let Some(hook) = session.on_close.take() {
                    hook(&summary);
                }
                summary
            }
            Err(error) => record_framework_error(&session.directory, error).unwrap_or_else(|error| json!({"status":"framework_error","error":error})),
        }
    })?;
    record_results(summary_dir, &results)?;
    Ok(results)
}

/// Run the import session of `candidate` in `root` with `role` (see the module documentation). Returns the session
/// summary (also written to `summary.json`).
pub async fn import_session<R: SynthesisRole>(request: &RunRequest, root: &Path, candidate: &ImportCandidate, role: &mut R) -> Result<Value, ControllerError> {
    request.validate()?;
    records::create_dir(root)?;
    let root = root.canonicalize().map_err(|e| RecordError::new(root, e))?;
    let layout = RunLayout::new(&root);
    let identity = json!({"request":request,"import_from":{"published_run":candidate.published_run,"query":candidate.query.name,"crate":candidate.query.crate_src}});
    let mut ledger = Ledger::open(&root, identity, request.limits.clone())?;
    if let Some(closed) = &ledger.state.closed {
        return Ok(closed.clone());
    }
    for directory in [layout.workspace(), layout.iterations()] {
        records::create_dir(&directory)?;
    }
    let reason = if layout.context().exists() { "controller_process_resume" } else { "initial_run" };
    let context = prepare_context(role, request, &layout, reason).await?;
    let source = seed_and_freeze(role, &layout, candidate).await?;
    let trial = evaluate(role, &layout, &source).await?;
    let mut qualification = vec![];
    if trial.eligible() {
        qualification.push(qualify_recorded(role, &layout, IMPORT_ITERATION, &trial.evaluation).await?);
    }
    let resolution = if layout.resolution().exists() {
        records::read_json(&layout.resolution())?
    } else {
        let resolution = role.close(std::slice::from_ref(&trial), &qualification).await.map_err(role_error("close"))?;
        records::write_json_atomic(&layout.resolution(), &resolution)?;
        resolution
    };
    let totals = ledger.totals()?;
    let summary = json!({"status":"closed","reason":IMPORTED,"inference_dispatched":false,
        "objective":role.policy().objective_status(&context, std::slice::from_ref(&trial)),
        "session_id":ledger.state.session_id,"limits":request.limits,"iterations":0,"calls":ledger.state.calls.len(),
        "reported_cost_usd":totals.spent,"known_reported_cost_usd":totals.spent,"outstanding_reservation_usd":totals.reserved,
        "cost_complete":!totals.usage_unknown,"cost_kind":"provider_reported","accounting":ledger.accounting(None)?,"author_elapsed_ms":0,
        "import":{"published_run":candidate.published_run,"query":candidate.query.name,"crate":candidate.query.crate_src,
            "storage_uses":candidate.uses.iter().map(|(name, package)| json!({"name":name,"package":package})).collect::<Vec<_>>(),
            "source":layout.iteration(IMPORT_ITERATION).join(SOURCE_FILE),"freeze":source["freeze"]},
        "trajectory":[{"iteration":IMPORT_ITERATION,"directory":layout.iteration(IMPORT_ITERATION),"evaluation":evaluation_digest(&trial.evaluation),
            "evaluation_record":layout.evaluation(IMPORT_ITERATION),"framework_elapsed_ms":trial.framework_elapsed_ms}],
        "qualification":qualification_digest(&layout, &qualification),
        "resolution":resolution,"resolution_record":layout.resolution(),"ledger":layout.ledger(),
        "scope":"no author call and no synthesis submission: a published package's author files, frozen with this run's framework files, evaluated, qualified and closed by the query role"});
    ledger.state.closed = Some(summary.clone());
    ledger.save()?;
    records::write_json_atomic(&layout.summary(), &summary)?;
    Ok(summary)
}

/// Phase 3: the provenance record of the seeded and frozen candidate (`iterations/0001/source.json`), written now
/// unless an earlier process completed it. A partial earlier attempt (no provenance) is removed first: only this
/// session writes there and nothing was evaluated before the provenance record.
async fn seed_and_freeze<R: SynthesisRole>(role: &mut R, layout: &RunLayout, candidate: &ImportCandidate) -> Result<Value, ControllerError> {
    let directory = layout.iteration(IMPORT_ITERATION);
    let provenance = directory.join(SOURCE_FILE);
    if provenance.exists() {
        return Ok(records::read_json(&provenance)?);
    }
    if directory.exists() {
        fs::remove_dir_all(&directory).map_err(|e| RecordError::new(&directory, e))?;
    }
    records::create_dir(&directory)?;
    let started = Instant::now();
    let workspace = layout.workspace();
    let submission = seed_query_workspace(&candidate.query, &candidate.uses, &workspace).map_err(|detail| ControllerError::Role { stage: "seed", detail })?;
    let freeze = match role.freeze(&workspace, &layout.frozen(IMPORT_ITERATION), &submission).await {
        Ok(frozen) => {
            records::write_new_json(&layout.frozen_candidate(IMPORT_ITERATION), &frozen)?;
            json!({"status":"frozen","candidate":layout.frozen_candidate(IMPORT_ITERATION)})
        }
        Err(error) => json!({"status":"freeze_error","error":error}),
    };
    let record = json!({"format_version":1,"published_run":candidate.published_run,"query":candidate.query.name,"crate":candidate.query.crate_src,
        "template":candidate.query.sql,"submission":submission,
        "storage_uses":candidate.uses.iter().map(|(name, package)| json!({"name":name,"package":package})).collect::<Vec<_>>(),
        "freeze":freeze,"framework_elapsed_ms":started.elapsed().as_millis() as u64,
        "copied":"the published crate's src/agent/** only, with a manifest naming the admitted storages; every framework file was generated by this run's freeze"});
    records::write_new_json(&provenance, &record)?;
    Ok(record)
}

/// Phase 4: the candidate's evaluation (`evaluation.json`), recorded once. A freeze refusal is the recorded outcome; a
/// framework failure is evaluated once more, and a second framework failure stops the session resumably (nothing is
/// recorded as its outcome, so a rerun evaluates again).
async fn evaluate<R: SynthesisRole>(role: &mut R, layout: &RunLayout, source: &Value) -> Result<Trial, ControllerError> {
    let iteration = IMPORT_ITERATION;
    let path = layout.evaluation(iteration);
    let (evaluation, framework_elapsed_ms) = if path.exists() {
        (records::read_json(&path)?, None)
    } else if source["freeze"]["status"] != "frozen" {
        let refusal = json!({"eligible":false,"status":"freeze_error","error":source["freeze"]["error"]});
        records::write_new_json(&path, &refusal)?;
        (refusal, None)
    } else {
        let started = Instant::now();
        let candidate: Value = records::read_json(&layout.frozen_candidate(iteration))?;
        let mut evaluation = role.evaluate(&layout.frozen(iteration), &candidate).await.unwrap_or_else(evaluation_error);
        if framework_failure(&evaluation) {
            let first = layout.iteration(iteration).join(format!("framework-failure-{}.json", records::now_unix_ms()));
            records::write_new_json(&first, &evaluation)?;
            let mut again = role.evaluate(&layout.frozen(iteration), &candidate).await.unwrap_or_else(evaluation_error);
            attribute_repeated_checker_failure(&evaluation, &mut again);
            if framework_failure(&again) {
                return Err(ControllerError::Role {
                    stage: "evaluate",
                    detail: format!("the imported candidate failed in the framework on two evaluations ({}); rerun the import after the framework is fixed", again["error"]),
                });
            }
            again["earlier_framework_failure"] = json!({"record":first,"status":evaluation["status"],"error":evaluation["error"]});
            evaluation = again;
        }
        records::write_new_json(&path, &evaluation)?;
        (evaluation, Some(started.elapsed().as_millis() as u64))
    };
    Ok(Trial {
        iteration,
        call_id: 0,
        candidate: source["submission"].clone(),
        status: TrialStatus::Evaluated,
        evaluation,
        framework_elapsed_ms,
        directory: Some(layout.iteration(iteration)),
        recovery_records: vec![],
        evaluation_record: None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::controller::limits::tests::limits;
    use crate::controller::test_support::{FixtureRole, scratch_root};

    fn request() -> RunRequest {
        RunRequest { format_version: 1, task: json!({"sql":"fixture"}), limits: limits(), continue_from: None }
    }

    /// A published query crate with one agent file, read through `PublishedRun`.
    fn candidate(root: &Path) -> ImportCandidate {
        let folder = root.join("published");
        for (path, text) in [("query.sql", "SELECT 1"), ("crates/example/src/agent/mod.rs", "pub fn query() {}\n"), ("crates/example/src/stores.rs", "pub mod flat_t;\n")] {
            fs::create_dir_all(folder.join(path).parent().unwrap()).unwrap();
            fs::write(folder.join(path), text).unwrap();
        }
        let run = crate::published::PublishedRun::read(&folder).unwrap();
        ImportCandidate { published_run: run.root.clone(), query: run.queries[0].clone(), uses: vec![("flat_t".into(), ContentId::from_bytes([3; 32]))] }
    }

    /// The published author files are seeded, frozen, evaluated, qualified and closed with no author call; a rerun
    /// returns the closure and repeats nothing.
    #[tokio::test]
    async fn an_import_session_admits_once_and_a_rerun_repeats_nothing() {
        let root = scratch_root("import-session");
        let candidate = candidate(&root);
        let session = root.join("run/queries/query-0000");
        let mut role = FixtureRole::default();
        let summary = import_session(&request(), &session, &candidate, &mut role).await.unwrap();
        assert_eq!((summary["status"].as_str(), summary["reason"].as_str(), summary["calls"].as_u64()), (Some("closed"), Some(IMPORTED), Some(0)));
        assert_eq!((role.prepared, role.evaluated, role.qualified), (1, 1, 1));
        assert_eq!(summary["resolution"]["selected"], true);
        assert!(session.join("author/import/crate/src/agent/mod.rs").is_file(), "the agent file is seeded");
        let provenance: Value = records::read_json(&session.join("iterations/0001").join(SOURCE_FILE)).unwrap();
        assert_eq!(provenance["freeze"]["status"], "frozen");
        let mut again = FixtureRole::default();
        assert_eq!(import_session(&request(), &session, &candidate, &mut again).await.unwrap(), summary);
        assert_eq!((again.prepared, again.evaluated, again.qualified), (0, 0, 0), "a closed import repeats nothing");
        fs::remove_dir_all(root).unwrap();
    }

    /// A freeze refusal closes the session with no package and no evaluation; a framework failure is evaluated once
    /// more, and two stop the session resumably, so a rerun evaluates again.
    #[tokio::test]
    async fn refusals_close_and_framework_failures_stay_resumable() {
        let root = scratch_root("import-session-outcomes");
        let candidate = candidate(&root);
        let mut refusing = FixtureRole { fail_freeze: true, ..FixtureRole::default() };
        let refused = import_session(&request(), &root.join("a"), &candidate, &mut refusing).await.unwrap();
        assert_eq!((refused["trajectory"][0]["evaluation"]["status"].as_str(), refusing.evaluated, refusing.qualified), (Some("freeze_error"), 0, 0));
        assert_eq!(refused["resolution"]["selected"], false);
        let mut flaky = FixtureRole { framework_failures: 2, ..FixtureRole::default() };
        let error = import_session(&request(), &root.join("b"), &candidate, &mut flaky).await.unwrap_err();
        assert!(error.to_string().contains("two evaluations"), "{error}");
        assert!(!root.join("b/iterations/0001/evaluation.json").exists(), "no outcome is recorded");
        let mut resumed = FixtureRole::default();
        let summary = import_session(&request(), &root.join("b"), &candidate, &mut resumed).await.unwrap();
        assert_eq!((resumed.evaluated, resumed.qualified, summary["resolution"]["selected"].as_bool()), (1, 1, Some(true)));
        fs::remove_dir_all(root).unwrap();
    }
}
