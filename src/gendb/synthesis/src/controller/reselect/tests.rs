use super::*;
use crate::controller::author::AuthorTransport;
use crate::controller::limits::tests::limits;
use crate::controller::records::read_json;
use crate::controller::run::run;
use crate::controller::schedule::{ScheduledSession, run_sessions};
use crate::controller::test_support::{FixtureAuthor, FixtureRole, scratch_root};
use std::path::PathBuf;

fn request() -> RunRequest {
    RunRequest { format_version: 1, task: json!({"sql":"fixture"}), limits: limits(), continue_from: None }
}

/// A closed author session of two paid submissions: iteration 1 scores 100 ns, iteration 2 scores 50 ns (so the
/// source's own order is 2, then 1); iteration 2 was qualified.
async fn closed_source_session(root: &Path) -> (PathBuf, Value) {
    let source = root.join("source/queries/query-0000");
    let closed = run(&request(), &source, &mut FixtureAuthor::default(), &mut FixtureRole::default()).await.unwrap();
    assert_eq!((closed["iterations"].as_u64(), closed["reported_cost_usd"].as_str()), (Some(2), Some("0.2")));
    (source, closed)
}

/// Every file under `root` with its bytes.
fn snapshot(root: &Path) -> Vec<(PathBuf, Vec<u8>)> {
    let mut files = vec![];
    let mut pending = vec![root.to_path_buf()];
    while let Some(dir) = pending.pop() {
        for entry in fs::read_dir(&dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                pending.push(path);
            } else if path.file_name().is_some_and(|name| name != "controller.lock") {
                files.push((path.clone(), fs::read(&path).unwrap()));
            }
        }
    }
    files.sort();
    files
}

/// The best candidate the policy excludes is passed over before any copy or evaluation; the next one in the source's
/// own order is imported, evaluated afresh, qualified and closed with zero author calls and cost; the source's cost
/// is referenced, never added; the source session is only read; a rerun returns the closure.
#[tokio::test]
async fn reselection_takes_the_best_admitted_candidate_without_an_author() {
    let root = scratch_root("reselect");
    let (source, source_closed) = closed_source_session(&root).await;
    let before = snapshot(&source);
    let target = root.join("recovery/queries/query-0000");
    let author = FixtureAuthor::default();
    let mut role = FixtureRole { excluded_scores: vec![50], ..FixtureRole::default() };
    let summary = reselect(&request(), &target, &source, &author, &mut role).await.unwrap();
    assert_eq!((summary["status"].as_str(), summary["reason"].as_str()), (Some("closed"), Some(RESELECTED)));
    assert_eq!((summary["calls"].as_u64(), summary["iterations"].as_u64(), summary["reported_cost_usd"].as_str()), (Some(0), Some(0), Some("0")));
    assert_eq!((summary["cost_complete"].as_bool(), summary["inference_dispatched"].as_bool()), (Some(true), Some(false)));
    assert_eq!((author.calls, author.prompts.len()), (0, 0), "no author is invoked");
    assert_eq!((role.imports, role.evaluated, role.qualified), (1, 1, 1));
    let decisions: Vec<(u64, &str)> =
        summary["reselection"]["candidates"].as_array().unwrap().iter().map(|c| (c["iteration"].as_u64().unwrap(), c["decision"].as_str().unwrap())).collect();
    assert_eq!(decisions, [(2, "policy_excluded"), (1, "selected")]);
    assert_eq!(summary["qualification"][0]["iteration"], 1);
    assert_eq!(summary["resolution"]["selected"], true);
    assert_eq!(summary["source_accounting"]["reported_cost_usd"], source_closed["reported_cost_usd"]);
    let provenance: Value = read_json(&target.join("iterations/0001").join(SOURCE_FILE)).unwrap();
    assert_eq!(provenance["source_frozen"], json!(source.canonicalize().unwrap().join("iterations/0001/frozen")));
    assert!(!target.join("iterations/0002").exists(), "the excluded candidate is never copied");
    assert_eq!(snapshot(&source), before, "the source session is only read");
    let mut restarted = FixtureRole::default();
    assert_eq!(reselect(&request(), &target, &source, &author, &mut restarted).await.unwrap(), summary);
    assert_eq!((restarted.prepared, restarted.imports, restarted.evaluated, restarted.qualified), (0, 0, 0, 0), "a closed reselection repeats nothing");
}

/// A controller stopped after evaluation and qualification resumes from the records: it repeats no import,
/// evaluation or qualification. An import interrupted before its provenance record is started again.
#[tokio::test]
async fn a_restarted_reselection_repeats_no_completed_stage() {
    let root = scratch_root("reselect-restart");
    let (source, _) = closed_source_session(&root).await;
    let target = root.join("recovery/queries/query-0000");
    let partial = target.join("iterations/0002/frozen/partial-copy");
    fs::create_dir_all(&partial).unwrap();
    let author = FixtureAuthor::default();
    let mut stopped = FixtureRole { fail_close: true, ..FixtureRole::default() };
    let error = reselect(&request(), &target, &source, &author, &mut stopped).await.unwrap_err();
    assert!(error.to_string().contains("fixture close failed"), "{error}");
    assert_eq!((stopped.imports, stopped.evaluated, stopped.qualified), (1, 1, 1));
    assert!(!partial.exists() && target.join("iterations/0002").join(SOURCE_FILE).is_file(), "the partial copy was replaced");
    let mut resumed = FixtureRole::default();
    let summary = reselect(&request(), &target, &source, &author, &mut resumed).await.unwrap();
    assert_eq!((resumed.imports, resumed.evaluated, resumed.qualified), (0, 0, 0));
    assert_eq!(summary["reselection"]["selected_iteration"], 2);
    assert_eq!(summary["qualification"][0]["result"]["qualified"], true);
    assert_eq!(author.calls, 0);
}

/// An open, missing or different-task source is refused by name before preparation; no closure is recorded.
#[tokio::test]
async fn open_missing_and_mismatched_sources_are_refused() {
    let root = scratch_root("reselect-refusals");
    let (source, _) = closed_source_session(&root).await;
    let author = FixtureAuthor::default();
    let refused = |error: ControllerError| {
        let text = error.to_string();
        assert!(text.starts_with(SOURCE_REFUSAL), "{text}");
        text
    };
    let mut role = FixtureRole::default();
    let other_task = RunRequest { task: json!({"sql":"other"}), ..request() };
    assert!(refused(reselect(&other_task, &root.join("a"), &source, &author, &mut role).await.unwrap_err()).contains("another task"));
    refused(reselect(&request(), &root.join("b"), &root.join("missing"), &author, &mut role).await.unwrap_err());
    let open = root.join("open");
    drop(Ledger::open(&open, json!({"request":request(),"author":author.capability()}), limits()).unwrap());
    assert!(refused(reselect(&request(), &root.join("c"), &open, &author, &mut role).await.unwrap_err()).contains("is open"));
    assert_eq!(role.prepared, 0, "refused before preparation");
    let ledger: LedgerState = read_json(&root.join("a/ledger.json")).unwrap();
    assert!(ledger.closed.is_none());
}

/// The scheduler runs a session that names a source as a reselection.
#[tokio::test]
async fn the_scheduler_dispatches_a_named_source_to_the_reselection() {
    let root = scratch_root("reselect-schedule");
    let (source, _) = closed_source_session(&root).await;
    let session = ScheduledSession {
        directory: root.join("recovery/queries/query-0000"),
        request: request(),
        author: FixtureAuthor::default(),
        role: FixtureRole::default(),
        reselect_from: Some(source),
        on_close: None,
    };
    let results = tokio::task::spawn_blocking(move || run_sessions(vec![session], &root.join("recovery/queries"), 1)).await.unwrap().unwrap();
    assert_eq!((results[0]["reason"].as_str(), results[0]["calls"].as_u64()), (Some(RESELECTED), Some(0)));
    assert_eq!(results[0]["reselection"]["selected_iteration"], 2);
}
