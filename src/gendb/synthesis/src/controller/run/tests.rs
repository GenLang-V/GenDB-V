use super::*;
use crate::controller::ledger::{Tokens, Trial};
use crate::controller::limits::tests::limits;
use crate::controller::records::{read_json, write_json_atomic};
use crate::controller::schedule::{ScheduledSession, run_sessions};
use crate::controller::test_support::{FixtureAuthor, FixturePolicy, FixtureRole, scratch_root};
use std::fs;

fn request() -> RunRequest {
    RunRequest { format_version: 1, task: json!({"sql":"fixture"}), limits: limits(), continue_from: None }
}

/// Five submissions and ten dollars: room for the continuation rules to act before a guard does.
fn roomy_request() -> RunRequest {
    RunRequest {
        limits: Limits { max_iterations: 5, max_cost_usd: Money::parse("10").unwrap(), ..limits() },
        ..request()
    }
}

fn open_ledger(root: &Path, request: &RunRequest, author: &FixtureAuthor) -> Ledger {
    Ledger::open(root, run_identity(request, &author.capability()), request.limits.clone()).unwrap()
}

fn load(path: &Path) -> Value {
    read_json(path).unwrap()
}

/// Invoke the fixture author for `call` outside the controller (to build an interrupted run).
fn invoke(author: &mut FixtureAuthor, call: &Call, session: &str, root: &Path) -> Receipt {
    author.invoke(&AuthorCall {
        call,
        session_id: session,
        resume: false,
        prompt: "fixture",
        workspace: root,
        call_dir: root,
        limits: &limits(),
    })
}

/// Recreate two settled pre-dispatch refusals and their retry-limit closure through the ordinary controller.
async fn closed_by_setup_refusals(root: &Path, author: &mut FixtureAuthor) -> (Value, Value) {
    author.refuse = true;
    let closed = run(&request(), root, author, &mut FixtureRole::default()).await.unwrap();
    assert_eq!((closed["reason"].as_str(), closed["calls"].as_u64()), (Some("retry_limit"), Some(2)));
    assert_eq!(closed["reported_cost_usd"], "0");
    assert_eq!(author.calls, 0);
    (closed, load(&root.join("ledger.json")))
}

#[tokio::test]
async fn predispatch_recovery_retains_closure_and_initializes_then_resumes() {
    let root = scratch_root("predispatch");
    let mut author = FixtureAuthor::default();
    let (closed, before) = closed_by_setup_refusals(&root, &mut author).await;
    let layout = RunLayout::new(&root.canonicalize().unwrap());
    let receipts: Vec<Vec<u8>> = (1..=2).map(|id| fs::read(layout.receipt(id)).unwrap()).collect();
    author.prove = true;
    assert!(predispatch_recovery_available(layout.root(), &author, None).unwrap());
    author.ready = false;
    let mut role = FixtureRole::default();
    let error = run(&request(), &root, &mut author, &mut role).await.unwrap_err();
    assert!(error.to_string().contains("unavailable"), "{error}");
    assert_eq!(role.prepared, 0);
    assert_eq!(load(&root.join("ledger.json")), before, "a failed readiness check does not reopen the closure");
    author.ready = true;
    author.refuse = false;
    let result = run(&request(), &root, &mut author, &mut role).await.unwrap();
    assert_eq!((author.calls, author.resumes.clone()), (2, vec![false, false]), "each attempt is a fresh provider session");
    assert_eq!((result["reason"].as_str(), result["calls"].as_u64()), (Some("iteration_limit"), Some(4)));
    assert_eq!(result["reported_cost_usd"], "0.2");
    assert_eq!(result["session_id"], before["session_id"]);
    let after = load(&root.join("ledger.json"));
    assert_eq!((&after["request"], &after["limits"]), (&before["request"], &before["limits"]));
    assert_eq!(&after["calls"].as_array().unwrap()[..2], before["calls"].as_array().unwrap());
    assert_eq!((after["calls"][2]["attempt"].as_u64(), after["calls"][3]["attempt"].as_u64()), (Some(1), Some(1)));
    let recoveries = after["predispatch_recoveries"].as_array().unwrap();
    assert_eq!(recoveries.len(), 1);
    assert_eq!((&recoveries[0]["prior_closed"], &recoveries[0]["prior_summary"]), (&closed, &closed));
    assert_eq!(recoveries[0]["call_ids"], json!([1, 2]));
    for id in 1..=2 {
        assert_eq!(fs::read(layout.receipt(id)).unwrap(), receipts[id as usize - 1]);
    }
    assert!(!predispatch_recovery_available(layout.root(), &author, None).unwrap());
    assert!(predispatch_recovery_available(layout.root(), &author, Some(&closed)).unwrap());
    assert!(!predispatch_recovery_available(layout.root(), &author, Some(&result)).unwrap());
    assert_eq!(run(&request(), &root, &mut author, &mut role).await.unwrap(), result);
    assert_eq!(author.calls, 2);
}

#[tokio::test]
async fn predispatch_recovery_refuses_paid_unknown_exhausted_and_normal_closed() {
    let root = scratch_root("predispatch-refused");
    let mut author = FixtureAuthor::default();
    let (_, before) = closed_by_setup_refusals(&root, &mut author).await;
    let base: LedgerState = serde_json::from_value(before).unwrap();
    for mode in ["paid", "unknown", "raw_result", "elapsed", "tokens", "trial", "iterations", "budget", "completed", "prior_recovery"] {
        let mut state = base.clone();
        let first = state.calls[0].receipt.as_mut().unwrap();
        match mode {
            "paid" => first.reported_cost_usd = Some(Money::parse("0.1").unwrap()),
            "unknown" => first.reported_cost_usd = None,
            "raw_result" => first.raw_result = Some(json!({"total_cost_usd":0})),
            "elapsed" => first.elapsed_ms = 1,
            "tokens" => first.tokens = Some(Tokens { input: 1, ..Tokens::default() }),
            "trial" => state.trials.push(Trial {
                iteration: 1,
                call_id: 1,
                candidate: json!({}),
                status: TrialStatus::Submitted,
                evaluation: Value::Null,
                framework_elapsed_ms: None,
                directory: None,
                recovery_records: vec![],
                evaluation_record: None,
            }),
            "iterations" => {
                state.iterations = state.limits.max_iterations;
                state.closed.as_mut().unwrap()["reason"] = json!("iteration_limit");
            }
            "budget" => state.closed.as_mut().unwrap()["reason"] = json!("budget_limit"),
            "completed" => state.closed.as_mut().unwrap()["reason"] = json!("first_eligible_candidate"),
            "prior_recovery" => state.predispatch_recoveries.push(json!({"call_ids":[1,2]})),
            _ => unreachable!(),
        }
        assert!(!state.predispatch_recovery_candidate(), "{mode}");
    }
    assert!(!predispatch_recovery_available(&root, &author, None).unwrap(), "no transport proof");
    author.prove = true;
    write_json_atomic(&root.join("calls/0001/invocation.json"), &json!({"launched":"uncertain"})).unwrap();
    assert!(!predispatch_recovery_available(&root, &author, None).unwrap(), "an uncertain launch is not proof");
    let mut role = FixtureRole::default();
    run(&request(), &root, &mut author, &mut role).await.unwrap();
    assert_eq!((role.prepared, author.calls), (0, 0));
}

#[tokio::test]
async fn predispatch_recovery_survives_prepare_crash_and_preserves_provider_identity() {
    let root = scratch_root("predispatch-prepare");
    let mut author = FixtureAuthor::default();
    let (_, before) = closed_by_setup_refusals(&root, &mut author).await;
    author.prove = true;
    author.refuse = false;
    let mut role = FixtureRole { fail_prepare: true, ..Default::default() };
    assert!(run(&request(), &root, &mut author, &mut role).await.is_err());
    assert!(predispatch_recovery_available(&root, &author, None).unwrap());
    let after = load(&root.join("ledger.json"));
    assert!(after["closed"].is_null());
    assert_eq!(after["predispatch_recoveries"].as_array().unwrap().len(), 1);
    assert_eq!(load(&root.join("summary.json")), before["closed"]);
    let mut changed = after["request"].clone();
    changed["author"]["version"] = json!("different");
    assert!(Ledger::open(&root, changed, request().limits).is_err());
    role.fail_prepare = false;
    let result = run(&request(), &root, &mut author, &mut role).await.unwrap();
    assert_eq!(result["calls"], 4);
    assert_eq!(author.resumes, vec![false, false], "each attempt is a fresh provider session");
    assert_eq!(load(&root.join("ledger.json"))["predispatch_recoveries"].as_array().unwrap().len(), 1);
}

#[tokio::test]
async fn predispatch_recovery_is_bounded_when_refusal_recurs() {
    let root = scratch_root("predispatch-bounded");
    let mut author = FixtureAuthor { refuse: true, prove: true, ..Default::default() };
    let mut role = FixtureRole::default();
    let first = run(&request(), &root, &mut author, &mut role).await.unwrap();
    assert_eq!((first["calls"].as_u64(), first["reason"].as_str()), (Some(1), Some("author_readiness_refusal")));
    let second = run(&request(), &root, &mut author, &mut role).await.unwrap();
    assert_eq!((second["calls"].as_u64(), second["reason"].as_str()), (Some(2), Some("author_readiness_refusal")));
    assert_eq!(run(&request(), &root, &mut author, &mut role).await.unwrap(), second);
    assert_eq!((role.prepared, author.calls), (2, 0));
}

#[test]
fn session_prepare_failure_is_durable_and_resume_preserves_closed_session() {
    let root = scratch_root("sessions");
    let sessions = |failing: usize| {
        (0..2)
            .map(|index| ScheduledSession {
                directory: root.join(format!("query-{index:04}")),
                request: request(),
                author: FixtureAuthor::default(),
                role: FixtureRole { fail_prepare: index == failing, ..Default::default() },
                reselect_from: None,
                on_close: None,
            })
            .collect::<Vec<_>>()
    };
    let first = run_sessions(sessions(0), &root, 2).unwrap();
    assert_eq!((first[0]["status"].as_str(), first[0]["resumable"].as_bool()), (Some("framework_error"), Some(true)));
    let error_record = PathBuf::from(first[0]["error_record"].as_str().unwrap());
    let original_error = fs::read(&error_record).unwrap();
    assert_eq!(load(&error_record), first[0]);
    assert!(first[0]["error"].as_str().unwrap().contains("role prepare: fixture preparation failed"));
    let before = load(&root.join("query-0000/ledger.json"));
    assert_eq!(before["calls"], json!([]));
    let completed = fs::read(root.join("query-0001/ledger.json")).unwrap();
    let original_summary = fs::read(root.join("workload-summary.json")).unwrap();
    let next = run_sessions(sessions(1), &root, 2).unwrap();
    assert_eq!(next[0]["status"], "closed");
    assert_eq!(next[0]["session_id"], before["session_id"]);
    assert_eq!((next[0]["calls"].as_u64(), next[0]["iterations"].as_u64()), (Some(2), Some(2)));
    assert_eq!(next[1], first[1], "a closed session returns its closure without preparing");
    assert_eq!(fs::read(root.join("query-0001/ledger.json")).unwrap(), completed);
    assert_eq!(fs::read(error_record).unwrap(), original_error);
    assert_eq!(fs::read(root.join("workload-summary.json")).unwrap(), original_summary);
    assert_eq!(load(&root.join("workload-summary-1.json")), json!(next));
    assert_eq!(load(&root.join("workload-summary-latest.json"))["record"], "workload-summary-1.json");
}

/// Session slots as the scheduled sessions use them: a session takes one when its controller checks the author's
/// readiness (`AuthorTransport::preflight`, once per `run`, after it opened the session's ledger) and frees it in its
/// close hook, after which the scheduler's thread takes the next session.
#[derive(Default)]
struct Slots {
    busy: usize,
    most_busy: usize,
    closed: usize,
    /// Per started session, in start order: its index and how many sessions had closed before it started.
    started: Vec<(usize, usize)>,
}

/// The fixture author of session `index`, taking a slot in [`Slots`] when its controller checks its readiness.
struct SlotAuthor {
    inner: FixtureAuthor,
    index: usize,
    slots: std::sync::Arc<std::sync::Mutex<Slots>>,
}

impl AuthorTransport for SlotAuthor {
    fn capability(&self) -> Capability {
        self.inner.capability()
    }

    fn preflight(&mut self) -> Result<(), String> {
        let mut slots = self.slots.lock().unwrap();
        slots.busy += 1;
        slots.most_busy = slots.most_busy.max(slots.busy);
        let closed = slots.closed;
        slots.started.push((self.index, closed));
        drop(slots);
        self.inner.preflight()
    }

    fn provider_session_exists(&self, call_dir: &Path) -> bool {
        self.inner.provider_session_exists(call_dir)
    }

    fn invoke(&mut self, call: &AuthorCall) -> Receipt {
        self.inner.invoke(call)
    }

    fn recover_receipt(&self, call: &Call, session_id: &str, call_dir: &Path, workspace: &Path) -> Result<Option<Receipt>, String> {
        self.inner.recover_receipt(call, session_id, call_dir, workspace)
    }
}

/// A paused workload relaunched with fewer query slots than open sessions (`max_concurrent_queries` lowered, a
/// scheduling control): every session had its incumbent evaluated and its first author call running when the
/// controller stopped. At most that many sessions run at once, each later one only after an earlier one closed; a
/// waiting session's stopped call is settled from the transport's terminal result when its turn comes (paid once, its
/// output not accepted, no submission counted), its next attempt resumes that provider session, and its recorded
/// incumbent is neither seeded nor evaluated again.
#[test]
fn a_relaunch_with_fewer_slots_resumes_stopped_sessions_at_most_that_many_at_once() {
    let root = scratch_root("fewer-slots");
    let request = continuing_request(&root.join("earlier-session"), 1);
    let (sessions, allowed) = (4, 2);
    let directory = |index: usize| root.join(format!("queries/query-{index:04}"));
    let incumbent_evaluation = json!({"eligible":true,"score_ns":10,"status":"diagnostic_exact"});
    for index in 0..sessions {
        // The records a stopped controller leaves: the incumbent evaluated, call 1 dispatched, its terminal result.
        let layout = RunLayout::new(&directory(index));
        let mut ledger = open_ledger(layout.root(), &request, &FixtureAuthor::default());
        fs::create_dir_all(layout.iteration(INCUMBENT_ITERATION)).unwrap();
        write_json_atomic(&layout.evaluation(INCUMBENT_ITERATION), &incumbent_evaluation).unwrap();
        ledger.state.incumbent = Some(Trial {
            iteration: INCUMBENT_ITERATION,
            call_id: 0,
            candidate: json!({"candidate_manifest":"incumbent-manifest.json","incumbent":{"record":layout.incumbent()}}),
            status: TrialStatus::Evaluated,
            evaluation: incumbent_evaluation.clone(),
            framework_elapsed_ms: None,
            directory: Some(layout.iteration(INCUMBENT_ITERATION)),
            recovery_records: vec![],
            evaluation_record: None,
        });
        let call = ledger.begin_call().unwrap();
        fs::create_dir_all(layout.call(call.id)).unwrap();
        write_json_atomic(&layout.call(call.id).join("fixture-terminal-result.json"), &json!({"type":"result","subtype":"error_during_execution",
            "session_id":ledger.state.session_id,"total_cost_usd":"0.25","duration_ms":1_000u64,"usage_scope":"session"}))
        .unwrap();
    }
    let slots = std::sync::Arc::new(std::sync::Mutex::new(Slots::default()));
    let scheduled = (0..sessions)
        .map(|index| {
            let freed = slots.clone();
            ScheduledSession {
                directory: directory(index),
                request: request.clone(),
                author: SlotAuthor { inner: FixtureAuthor::default(), index, slots: slots.clone() },
                role: FixtureRole::default(),
                reselect_from: None,
                on_close: Some(Box::new(move |_: &Value| {
                    let mut slots = freed.lock().unwrap();
                    slots.busy -= 1;
                    slots.closed += 1;
                })),
            }
        })
        .collect::<Vec<_>>();
    let results = run_sessions(scheduled, &root.join("queries"), allowed).unwrap();

    let slots = slots.lock().unwrap();
    assert!(slots.most_busy <= allowed, "{} sessions ran at once", slots.most_busy);
    assert_eq!((slots.started.len(), slots.closed), (sessions, sessions), "every session ran once");
    for &(index, closed_before) in &slots.started {
        assert!(index < allowed || closed_before + allowed > index, "session {index} started after only {closed_before} closed");
    }
    for (index, result) in results.iter().enumerate() {
        let directory = directory(index);
        assert_eq!((result["status"].as_str(), result["reason"].as_str()), (Some("closed"), Some("iteration_limit")), "{result}");
        assert_eq!((result["calls"].as_u64(), result["iterations"].as_u64()), (Some(2), Some(1)), "the stopped call counted no submission");
        assert_eq!(result["reported_cost_usd"], "0.35", "the stopped call is paid once");
        assert_eq!(load(&directory.join("calls/0001/receipt.json"))["outcome"], "controller_loss_recovery: error_during_execution");
        let ledger = load(&directory.join("ledger.json"));
        let next = &ledger["calls"][1];
        assert_eq!((next["attempt"].as_u64(), next["resumes_provider_session"].as_bool()), (Some(2), Some(true)));
        assert_eq!(next["provider_session"], ledger["session_id"], "the next attempt resumes the stopped call's provider session");
        assert_eq!(load(&directory.join("iterations/0000/evaluation.json")), incumbent_evaluation);
        assert!(!directory.join("author/incumbent-manifest.json").exists(), "the recorded incumbent is not seeded again");
        assert_eq!((result["incumbent"]["evaluation"]["score_ns"].as_u64(), result["qualification"][0]["iteration"].as_u64()), (Some(10), Some(0)));
    }
}

#[tokio::test]
async fn repaired_frozen_refusal_keeps_paid_call_iteration_and_original_evidence() {
    let root = scratch_root("repair");
    fs::create_dir_all(&root).unwrap();
    let root = root.canonicalize().unwrap();
    let layout = RunLayout::new(&root);
    let request = RunRequest { limits: Limits { max_iterations: 1, ..limits() }, ..request() };
    let mut author = FixtureAuthor::default();
    let original = json!({"eligible":false,"status":"evaluation_error","error":"fixture archive transport refused"});
    let session = {
        let mut ledger = open_ledger(&root, &request, &author);
        let call = ledger.begin_call().unwrap();
        let session = ledger.state.session_id.clone();
        let settled = invoke(&mut author, &call, &session, &root);
        let output = settled.output.clone().unwrap();
        ledger.settle(settled).unwrap();
        ledger.submit(call.id, output).unwrap();
        fs::create_dir_all(layout.frozen(1)).unwrap();
        write_json_atomic(&layout.frozen_candidate(1), &json!({"frozen":true})).unwrap();
        write_json_atomic(&layout.evaluation(1), &original).unwrap();
        ledger.state.trials[0].status = TrialStatus::Evaluated;
        ledger.state.trials[0].evaluation = original.clone();
        ledger.save().unwrap();
        session
    };
    let mut role = FixtureRole { policy: FixturePolicy { repair: true, ..Default::default() }, ..Default::default() };
    let result = run(&request, &root, &mut author, &mut role).await.unwrap();
    assert_eq!((author.calls, role.evaluated), (1, 1));
    assert_eq!((result["calls"].as_u64(), result["iterations"].as_u64()), (Some(1), Some(1)));
    assert_eq!(result["session_id"], json!(session));
    assert_eq!(result["reported_cost_usd"], "0.1");
    assert_eq!(load(&layout.evaluation(1)), original, "the original evaluation record stays");
    let repair = load(Path::new(result["trajectory"][0]["evaluation_record"].as_str().unwrap()));
    assert_eq!(repair["prior_evaluation"], original);
    assert_eq!(repair["author_dispatched"], false);
    assert_eq!(repair["evaluation"]["eligible"], true);
    assert_eq!(result["trajectory"][0]["recovery_records"][0]["revision"], "fixture-transport-v2");
    assert_eq!(run(&request, &root, &mut author, &mut role).await.unwrap(), result);
    assert_eq!((author.calls, role.evaluated), (1, 1));
}

#[tokio::test]
async fn proven_undispatched_reservation_uses_same_call_without_zero_receipt_or_retry() {
    let root = scratch_root("undispatched");
    let request = RunRequest { limits: Limits { max_iterations: 1, max_retries_per_iteration: 0, ..limits() }, ..request() };
    let mut author = FixtureAuthor { prove: true, ..Default::default() };
    let session = {
        let mut ledger = open_ledger(&root, &request, &author);
        assert_eq!(ledger.begin_call().unwrap().id, 1);
        ledger.state.session_id.clone()
    };
    let result = run(&request, &root, &mut author, &mut FixtureRole::default()).await.unwrap();
    assert_eq!((author.calls, author.resumes.clone()), (1, vec![false]));
    assert_eq!((result["calls"].as_u64(), result["iterations"].as_u64()), (Some(1), Some(1)));
    assert_eq!(result["session_id"], json!(session));
    assert_eq!((&result["reported_cost_usd"], &result["cost_complete"]), (&json!("0.1"), &json!(true)));
    assert_eq!(load(&root.join("calls/0001/receipt.json"))["provider_reported_cost_usd"], "0.1");
    assert_eq!(load(&root.join("ledger.json"))["calls"][0]["attempt"], 1);
}

#[tokio::test]
async fn two_candidates_one_session_close_without_extra_author_and_resume() {
    let root = scratch_root("two-candidates");
    let mut author = FixtureAuthor::default();
    let mut role = FixtureRole::default();
    let result = run(&request(), &root, &mut author, &mut role).await.unwrap();
    assert_eq!((result["iterations"].as_u64(), result["reported_cost_usd"].as_str()), (Some(2), Some("0.2")));
    assert_eq!(author.resumes, vec![false, false], "each attempt is a fresh provider session");
    assert_eq!((role.prepared, role.evaluated, role.qualified), (1, 2, 1));
    assert_eq!(result["qualification"][0]["iteration"], 2, "the better score qualifies first");
    assert_eq!(run(&request(), &root, &mut author, &mut role).await.unwrap(), result);
    assert_eq!(author.calls, 2);
}

#[tokio::test]
async fn cost_paid_failure_resume_retry_overshoot_and_unknown() {
    let request = request();
    let root = scratch_root("paid-failure");
    let mut author = FixtureAuthor { raw_cost_only: Some(Some("0.75")), ..Default::default() };
    // A paid failure whose controller stopped before settling: only the transport's record of the result remains.
    let (call_dir, record) = {
        let mut ledger = open_ledger(&root, &request, &author);
        let call = ledger.begin_call().unwrap();
        let call_dir = root.join("calls/0001");
        fs::create_dir_all(&call_dir).unwrap();
        let record = json!({"type":"result","session_id":ledger.state.session_id,"subtype":"error_during_execution",
            "total_cost_usd":"0.4","duration_ms":10});
        write_json_atomic(&call_dir.join("fixture-terminal-result.json"), &record).unwrap();
        assert_eq!(call.id, 1);
        (call_dir, record)
    };
    let result = run(&request, &root, &mut author, &mut FixtureRole::default()).await.unwrap();
    assert_eq!((author.calls, author.resumes.clone()), (1, vec![true]), "the recovered call started the provider session");
    assert_eq!((result["calls"].as_u64(), result["iterations"].as_u64()), (Some(2), Some(1)));
    assert_eq!(result["reason"], "budget_limit");
    assert_eq!(result["reported_cost_usd"], "1.15");
    assert_eq!((result["cost_kind"].as_str(), result["budget_enforcement"].as_str()), (Some("provider_reported"), Some("stop_guard")));
    assert_eq!((&result["known_budget_overshoot_usd"], &result["budget_overshoot_complete"]), (&json!("0.15"), &json!(true)));
    assert_eq!(result["accounting"]["provider_reported_cost_usd"], "1.15");
    assert!(result["accounting"]["tokens"].is_null());
    assert_eq!(result["iteration_accounting"][0]["accounting"]["call_ids"], json!([1, 2]));
    let receipt = load(&call_dir.join("receipt.json"));
    assert_eq!(receipt["outcome"], "controller_loss_recovery: error_during_execution");
    let before = fs::read(root.join("ledger.json")).unwrap();
    assert_eq!(run(&request, &root, &mut author, &mut FixtureRole::default()).await.unwrap(), result);
    assert_eq!(author.calls, 1);
    assert_eq!(fs::read(root.join("ledger.json")).unwrap(), before);
    assert_eq!(load(&call_dir.join("fixture-terminal-result.json")), record);

    let mut unknown = FixtureAuthor { raw_cost_only: Some(None), ..Default::default() };
    let root = scratch_root("paid-unknown");
    let result = run(&request, &root, &mut unknown, &mut FixtureRole::default()).await.unwrap();
    assert_eq!(unknown.calls, 1);
    assert_eq!((result["status"].as_str(), result["reason"].as_str()), (Some("accounting_unresolved"), Some("usage_unknown")));
    assert!(result["reported_cost_usd"].is_null());
    assert_eq!(result["known_reported_cost_usd"], "0");
    assert_eq!((&result["cost_complete"], &result["budget_overshoot_complete"]), (&json!(false), &json!(false)));
    assert_eq!(result["outstanding_reservation_usd"], "1");
    assert!(load(&root.join("ledger.json"))["closed"].is_null(), "unknown usage keeps the session open");
}

#[tokio::test]
async fn strict_cap_refuses_before_preparation_or_dispatch() {
    let request = RunRequest { limits: Limits { spend_policy: SpendPolicy::StrictUsd, ..limits() }, ..request() };
    let mut author = FixtureAuthor::default();
    let mut role = FixtureRole::default();
    let result = run(&request, &scratch_root("strict"), &mut author, &mut role).await.unwrap();
    assert_eq!(result["status"], "unsupported_capability");
    assert_eq!((author.calls, role.prepared), (0, 0));
}

#[tokio::test]
async fn policy_stop_after_first_eligible_without_extra_call() {
    let request = RunRequest { limits: Limits { max_iterations: 3, ..limits() }, ..request() };
    let mut author = FixtureAuthor::default();
    let policy = FixturePolicy { stop_at_first_eligible: true, ..Default::default() };
    let mut role = FixtureRole { policy, reject_evaluations: 1, ..Default::default() };
    let result = run(&request, &scratch_root("first-eligible"), &mut author, &mut role).await.unwrap();
    assert_eq!((result["reason"].as_str(), result["iterations"].as_u64()), (Some("first_eligible_candidate"), Some(2)));
    assert_eq!(result["accounting"]["provider_reported_cost_usd"], "0.2");
    assert_eq!((author.calls, role.evaluated, role.qualified), (2, 2, 1));
    assert_eq!(author.resumes, vec![false, false], "each attempt is a fresh provider session");
}

#[tokio::test]
async fn failed_submissions_consume_iterations_and_retain_cost() {
    let mut author = FixtureAuthor::default();
    let mut role = FixtureRole { fail_freeze: true, ..Default::default() };
    let result = run(&request(), &scratch_root("failed-freeze"), &mut author, &mut role).await.unwrap();
    assert_eq!((result["reason"].as_str(), result["iterations"].as_u64()), (Some("iteration_limit"), Some(2)));
    assert_eq!(result["accounting"]["provider_reported_cost_usd"], "0.2");
    assert_eq!(result["iteration_accounting"][0]["accounting"]["provider_reported_cost_usd"], "0.1");
    assert_eq!(result["trajectory"][0]["evaluation"]["status"], "freeze_error");
    assert_eq!((author.calls, role.evaluated, role.qualified), (2, 0, 0));
}

#[tokio::test]
async fn unresolved_dispatch_resumes_without_preparation_or_paid_replay() {
    let root = scratch_root("unresolved");
    let request = request();
    let mut author = FixtureAuthor::default();
    open_ledger(&root, &request, &author).begin_call().unwrap();
    let mut role = FixtureRole::default();
    let result = run(&request, &root, &mut author, &mut role).await.unwrap();
    assert_eq!(result["status"], "accounting_unresolved");
    assert_eq!(result["outstanding_reservation_usd"], "1");
    assert_eq!((author.calls, role.prepared), (0, 0));
}

#[tokio::test]
async fn crash_after_submission_counts_failed_capture_before_next_candidate() {
    let root = scratch_root("crash-submitted");
    let request = request();
    let mut author = FixtureAuthor::default();
    {
        let mut ledger = open_ledger(&root, &request, &author);
        let call = ledger.begin_call().unwrap();
        let session = ledger.state.session_id.clone();
        let settled = invoke(&mut author, &call, &session, &root);
        let output = settled.output.clone().unwrap();
        ledger.settle(settled).unwrap();
        ledger.submit(call.id, output).unwrap();
    }
    let mut role = FixtureRole::default();
    let result = run(&request, &root, &mut author, &mut role).await.unwrap();
    assert_eq!(result["trajectory"][0]["evaluation"]["status"], "interrupted_source_capture");
    assert_eq!(result["iterations"], 2);
    assert_eq!((author.calls, role.evaluated), (2, 1));
    assert_eq!(author.resumes, vec![false, false], "each attempt is a fresh provider session");
}

#[tokio::test]
async fn unchanged_effective_candidate_reuses_result_and_stops_before_remeasurement() {
    let root = scratch_root("unchanged");
    let mut author = FixtureAuthor::default();
    let mut role = FixtureRole { unchanged_module: true, ..Default::default() };
    let result = run(&request(), &root, &mut author, &mut role).await.unwrap();
    assert_eq!(result["reason"], "unchanged_effective_candidate");
    assert_eq!((result["iterations"].as_u64(), result["calls"].as_u64()), (Some(2), Some(2)));
    assert_eq!(result["reported_cost_usd"], "0.2");
    assert_eq!((role.evaluated, role.qualified), (1, 1));
    let counters = &result["trajectory_accounting"];
    assert_eq!((counters["candidate_submissions"].as_u64(), counters["duplicate_submissions"].as_u64()), (Some(2), Some(1)));
    assert_eq!(counters["distinct_code_versions"], 1);
    assert_eq!(result["trajectory"][1]["evaluation"]["status"], "unchanged_effective_candidate");
    let duplicate = load(&root.join("iterations/0002/evaluation.json"));
    assert_eq!(duplicate["duplicate_of_iteration"], 1);
    assert_eq!((duplicate["qualification_runs"].as_u64(), duplicate["timed_measurements"].as_u64()), (Some(0), Some(0)));
}

#[tokio::test]
async fn unchanged_resubmission_after_a_framework_failure_is_evaluated() {
    let root = scratch_root("unchanged-after-tool-failure");
    let mut author = FixtureAuthor::default();
    let mut role = FixtureRole { unchanged_module: true, framework_failures: 1, ..Default::default() };
    let result = run(&request(), &root, &mut author, &mut role).await.unwrap();
    assert_ne!(result["trajectory"][0]["evaluation"]["status"], "tool_failure", "a framework failure is evaluated once more");
    assert_eq!(role.evaluated, 2, "the tool failure judged nothing, so the same frozen candidate is evaluated again");
    assert!(root.join("iterations/0001/framework-failure-1.json").is_file());
    assert!(load(&root.join("iterations/0001/evaluation.json"))["earlier_framework_failure"]["record"].is_string());
    assert_eq!(result["trajectory"][1]["evaluation"]["status"], "unchanged_effective_candidate", "the second evaluation is a real verdict");
}

#[tokio::test]
async fn a_repeated_framework_failure_stops_resumably_and_is_not_counted() {
    let root = scratch_root("repeated-framework-failure");
    let mut author = FixtureAuthor::default();
    let mut role = FixtureRole { framework_failures: 2, ..Default::default() };
    let error = run(&request(), &root, &mut author, &mut role).await.unwrap_err();
    assert!(error.to_string().contains("not counted"), "{error}");
    let ledger: LedgerState = read_json(&root.join("ledger.json")).unwrap();
    assert!(ledger.closed.is_none(), "the session stays open for a resume after the framework is fixed");
    assert_eq!((ledger.iterations, ledger.counted_submissions()), (1, 0));
    assert_eq!(ledger.uncounted_framework_failures(), vec![1]);
}

#[test]
fn unchanged_resubmission_stop_rule() {
    let trial = |iteration: u32, unchanged: bool| Trial {
        iteration,
        call_id: iteration as u64,
        candidate: json!({}),
        status: TrialStatus::Evaluated,
        evaluation: json!({"duplicate_effective_candidate":unchanged}),
        framework_elapsed_ms: None,
        directory: None,
        recovery_records: vec![],
        evaluation_record: None,
    };
    let unmet = json!({"status":"unmet"});
    let once = [trial(1, false), trial(2, true)];
    let twice = [trial(1, false), trial(2, true), trial(3, true)];
    assert_eq!(unchanged_resubmission_stop(&json!({"status":"not_configured"}), &once), Some(StopReason::UnchangedEffectiveCandidate));
    assert_eq!(unchanged_resubmission_stop(&json!({"status":"met"}), &once), Some(StopReason::UnchangedEffectiveCandidate));
    assert_eq!(unchanged_resubmission_stop(&unmet, &once), None);
    assert_eq!(unchanged_resubmission_stop(&unmet, &twice), Some(StopReason::UnchangedAfterContinueObjectiveUnmet));
}

fn prompt(author: &FixtureAuthor, index: usize) -> Value {
    serde_json::from_str(&author.prompts[index]).unwrap()
}

/// Unmet objective: one unchanged resubmission continues, the second stops the run unmet; every call's actual cost
/// is counted and the author sees counted costs, remaining guards and the reused result.
#[tokio::test]
async fn unmet_objective_continues_once_then_unchanged_repeat_stops_unmet_with_costs() {
    let mut author = FixtureAuthor { cost: "1.25", ..Default::default() };
    let policy = FixturePolicy { objective_below_ns: Some(40), ..Default::default() };
    let mut role = FixtureRole { policy, unchanged_module: true, median_ns: Some(45), ..Default::default() };
    let result = run(&roomy_request(), &scratch_root("unmet"), &mut author, &mut role).await.unwrap();
    assert_eq!(result["reason"], "unchanged_after_continue_objective_unmet");
    assert_eq!(result["objective"]["status"], "unmet");
    assert_eq!((result["calls"].as_u64(), result["iterations"].as_u64()), (Some(3), Some(3)));
    assert_eq!(role.evaluated, 1, "unchanged candidates are never remeasured");
    assert_eq!(result["reported_cost_usd"], "3.75");
    assert_eq!(result["trajectory_accounting"]["duplicate_submissions"], 2);
    let first = prompt(&author, 0);
    assert_eq!(first["ledger"]["spent_usd"], "0");
    assert_eq!(first["ledger"]["submissions"]["remaining_including_this_call"], 5);
    assert_eq!(first["context"]["contract"], "fixture");
    let third = prompt(&author, 2);
    assert_eq!((&third["ledger"]["spent_usd"], &third["ledger"]["remaining_usd"]), (&json!("2.5"), &json!("7.5")));
    assert_eq!(third["ledger"]["earlier_calls"], 2);
    assert_eq!(third["ledger"]["this_call"]["call"], 3);
    let feedback = third["feedback"].as_array().unwrap();
    let unchanged = feedback.iter().rev().find(|event| event["iteration"] == 2 && event["evaluation"].is_object()).unwrap();
    assert_eq!(unchanged["evaluation"]["duplicate_of_iteration"], 1);
    let call = feedback.iter().rev().find(|event| event["author_outcome"].is_string()).unwrap();
    assert_eq!(call["provider_reported_cost_usd"], "1.25");
}

#[tokio::test]
async fn met_objective_unchanged_candidate_closes_and_guards_still_bound_unmet_runs() {
    let policy = FixturePolicy { objective_below_ns: Some(40), ..Default::default() };
    let mut author = FixtureAuthor { cost: "0.5", ..Default::default() };
    let mut met = FixtureRole { policy: policy.clone(), unchanged_module: true, median_ns: Some(30), ..Default::default() };
    let result = run(&roomy_request(), &scratch_root("met"), &mut author, &mut met).await.unwrap();
    assert_eq!((result["reason"].as_str(), result["objective"]["status"].as_str()), (Some("unchanged_effective_candidate"), Some("met")));
    assert_eq!(result["calls"], 2);

    let mut author = FixtureAuthor { cost: "0.5", ..Default::default() };
    let mut unmet = FixtureRole { policy, unchanged_module: true, median_ns: Some(45), ..Default::default() };
    let request = RunRequest { limits: Limits { max_iterations: 2, ..roomy_request().limits }, ..request() };
    let result = run(&request, &scratch_root("guard"), &mut author, &mut unmet).await.unwrap();
    assert_eq!((result["reason"].as_str(), result["objective"]["status"].as_str()), (Some("iteration_limit"), Some("unmet")));
    assert_eq!((result["calls"].as_u64(), unmet.evaluated), (Some(2), 1));
    assert_eq!(result["remaining_limits"]["candidate_submissions"], 0);
}

/// Controller loss after dispatch: the transport's durable terminal result settles the call once (its paid cost
/// counted, its output not accepted) and the run continues; without such evidence usage stays unknown and no author
/// is called.
#[tokio::test]
async fn ordinary_resume_settles_lost_controller_call_once_then_continues() {
    for terminal in [true, false] {
        let root = scratch_root(if terminal { "resume-lost" } else { "resume-incomplete" });
        let request = roomy_request();
        let mut author = FixtureAuthor { cost: "1.25", ..Default::default() };
        let call_dir = root.join("calls/0001");
        {
            let mut ledger = open_ledger(&root, &request, &author);
            ledger.begin_call().unwrap();
            fs::create_dir_all(&call_dir).unwrap();
            if terminal {
                write_json_atomic(&call_dir.join("fixture-terminal-result.json"), &json!({"type":"result",
                    "subtype":"error_during_execution","session_id":ledger.state.session_id,"total_cost_usd":"7.25",
                    "duration_ms":1_071_344u64,"usage_scope":"session"}))
                .unwrap();
            }
        }
        let policy = FixturePolicy { objective_below_ns: Some(40), ..Default::default() };
        let mut role = FixtureRole { policy, unchanged_module: true, median_ns: Some(45), ..Default::default() };
        let result = run(&request, &root, &mut author, &mut role).await.unwrap();
        if terminal {
            let receipt: Receipt = read_json(&call_dir.join("receipt.json")).unwrap();
            assert_eq!(receipt.outcome, "controller_loss_recovery: error_during_execution");
            assert_eq!((receipt.elapsed_ms, receipt.output.is_none()), (1_071_344, true));
            assert_eq!(result["reason"], "unchanged_after_continue_objective_unmet");
            assert_eq!(result["calls"], 4);
            assert_eq!(result["reported_cost_usd"], "11");
            assert_eq!(author.prompts.len(), 3);
            assert_eq!(load(&root.join("ledger.json"))["calls"][1]["attempt"], 2, "the lost call consumed attempt 1 only");
        } else {
            assert!(!call_dir.join("receipt.json").exists());
            assert_eq!((result["status"].as_str(), result["reason"].as_str()), (Some("accounting_unresolved"), Some("usage_unknown")));
            assert!(author.prompts.is_empty());
        }
    }
}

#[test]
fn trajectory_counters_separate_calls_submissions_versions_jobs_and_improvements() {
    let root = scratch_root("trajectory");
    let layout = RunLayout::new(&root);
    let job = |path: &str, record: Value| {
        let path = root.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        write_json_atomic(&path, &record).unwrap();
    };
    job("calls/0001/local-jobs/0001-profile-a/result.json", json!({"status":"completed","action":"profile","job_id":1}));
    job("calls/0002/local-jobs/refused-0002.json", json!({"status":"refused","action":"trial","job_id":2,"error":"fixture"}));
    job("calls/0002/local-jobs/0003-check/result.json", json!({"status":"completed","action":"check","job_id":3,"result":{"status":"accepted"}}));
    job("calls/0002/local-jobs/service.json", json!({"status":"ready"}));
    let (source_a, source_b) = (root.join("a.rs"), root.join("b.rs"));
    fs::write(&source_a, "module fixture").unwrap();
    fs::write(&source_b, "module fixture, revised").unwrap();
    for (iteration, source) in [(1, &source_a), (2, &source_a), (3, &source_b)] {
        fs::create_dir_all(layout.iteration(iteration)).unwrap();
        write_json_atomic(&layout.frozen_candidate(iteration), &json!({"format_version":1,"modules":[{"source":source}]})).unwrap();
    }
    let settled = |id: u64, outcome: &str, output: bool| {
        let call = Call { id, iteration: id as u32, attempt: 1, started_unix_ms: 0, reservation_usd: Money::parse("1").unwrap(), receipt: None, provider_session: None, resumes_provider_session: false, usage_in_resumed_session: false };
        let mut receipt = crate::controller::test_support::receipt(&call, "s", Some("0.1"));
        receipt.outcome = outcome.into();
        receipt.output = output.then(|| json!({"candidate_manifest":"candidate.json"}));
        Call { receipt: Some(receipt), ..call }
    };
    let trial = |iteration: u32, evaluation: Value| Trial {
        iteration,
        call_id: 1,
        candidate: json!({}),
        status: TrialStatus::Evaluated,
        evaluation,
        framework_elapsed_ms: None,
        directory: None,
        recovery_records: vec![],
        evaluation_record: None,
    };
    let state = LedgerState {
        format_version: 1,
        request: json!({}),
        session_id: "s".into(),
        limits: limits(),
        iterations: 3,
        calls: vec![settled(1, "success", true), settled(2, "transport_error", false)],
        receipt_reconciliations: vec![],
        predispatch_recoveries: vec![],
        preparation_context_revisions: vec![],
        trials: vec![
            trial(1, json!({"eligible":true,"measurements":[{"workers":1,"median_ns":100}]})),
            trial(2, json!({"eligible":false})),
            trial(3, json!({"eligible":true,"measurements":[{"workers":1,"median_ns":80}]})),
        ],
        incumbent: None,
        closed: None,
    };
    let counters = json!(trajectory::trajectory_accounting(&layout, &state).unwrap());
    assert_eq!((counters["author_calls"].as_u64(), counters["failed_author_calls"].as_u64()), (Some(2), Some(1)));
    assert_eq!((counters["candidate_submissions"].as_u64(), counters["failed_submissions"].as_u64()), (Some(3), Some(1)));
    assert_eq!((counters["duplicate_submissions"].as_u64(), counters["distinct_code_versions"].as_u64()), (Some(1), Some(2)));
    assert_eq!((counters["timed_submitted_trials"].as_u64(), counters["improvements"].as_u64()), (Some(2), Some(1)));
    let local = &counters["local"];
    assert_eq!((local["jobs"].as_u64(), local["local_trials"].as_u64(), local["failed_jobs"].as_u64()), (Some(3), Some(2), Some(1)));
    assert_eq!(local["by_action"], json!({"check":1,"profile":1,"trial":1}));
    assert_eq!((local["latest"]["job_id"].as_u64(), local["latest"]["result_status"].as_str()), (Some(3), Some("accepted")));
}

/// One submission, no dollar or retry guard: provider conditions alone decide what follows a failed call.
fn unguarded_request() -> RunRequest {
    RunRequest {
        limits: Limits { max_iterations: 1, max_cost_usd: Money::UNSET, max_retries_per_iteration: crate::controller::limits::UNSET_COUNT, ..limits() },
        ..request()
    }
}

#[tokio::test]
async fn provider_limits_wait_then_continue_the_same_session_with_one_short_message_each() {
    use crate::controller::author::ProviderCondition;
    use crate::controller::provider_wait::PROVIDER_WAIT_FILE;
    let root = scratch_root("provider-wait");
    let reset = records::now_unix_ms() + 3_600_000;
    let mut author = FixtureAuthor {
        cost: "0.5",
        script: vec![
            Some(ProviderCondition::RateLimited { status: Some(429), resets_at_unix_ms: Some(reset) }),
            Some(ProviderCondition::ApiError { status: Some(529) }),
            None,
        ],
        ..Default::default()
    };
    let result = run(&unguarded_request(), &root, &mut author, &mut FixtureRole::default()).await.unwrap();
    assert_eq!((author.calls, author.resumes.clone()), (3, vec![false, true, true]));
    assert!(author.sessions.iter().all(|session| *session == author.sessions[0]), "one provider session throughout");
    let ledger = load(&root.join("ledger.json"));
    let second_ended = ledger["calls"][1]["receipt"]["ended_unix_ms"].as_u64().unwrap();
    // The provider's reset time, then the backoff of the second consecutive failure from the end of that call.
    assert_eq!(author.waits, vec![reset, second_ended + 120_000]);
    for (call, basis) in [("0001", "provider_reset"), ("0002", "exponential_backoff")] {
        let record = load(&root.join("calls").join(call).join(PROVIDER_WAIT_FILE));
        assert_eq!((record["status"].as_str(), record["wait"]["basis"].as_str()), (Some("elapsed"), Some(basis)));
    }
    assert!(author.prompts[0].starts_with('{'), "the first call sends the full prompt");
    for continuation in &author.prompts[1..] {
        assert!(continuation.starts_with("# Continue after a provider interruption") && continuation.len() < 1_000, "{continuation}");
    }
    // Session totals 0.5, 1.0, 1.5 count once, by increment; the submission is the third call's.
    assert_eq!((result["iterations"].as_u64(), result["reported_cost_usd"].as_str()), (Some(1), Some("1.5")));
    assert_eq!(ledger["trials"][0]["call_id"], 3);
}

#[tokio::test]
async fn an_exhausted_session_is_replaced_and_unrecoverable_provider_refusals_stop_resumably() {
    use crate::controller::author::ProviderCondition;
    let root = scratch_root("provider-exhausted");
    let mut author = FixtureAuthor {
        cost: "0.5",
        script: vec![
            Some(ProviderCondition::RateLimited { status: Some(429), resets_at_unix_ms: None }),
            Some(ProviderCondition::ContextExhausted),
            None,
        ],
        ..Default::default()
    };
    let result = run(&unguarded_request(), &root, &mut author, &mut FixtureRole::default()).await.unwrap();
    assert_eq!((author.calls, author.resumes.clone()), (3, vec![false, true, false]));
    assert_eq!(author.sessions[1], author.sessions[0]);
    assert_ne!(author.sessions[2], author.sessions[0], "the exhausted session is not resumed");
    assert_eq!(author.waits.len(), 1, "only the rate limit waits");
    let fresh: Value = serde_json::from_str(&author.prompts[2]).unwrap();
    assert!(fresh["handoff"].is_object(), "the fresh session gets the attempt handoff");
    // Old session total 1.0 plus the fresh session's 0.5.
    assert_eq!((result["iterations"].as_u64(), result["reported_cost_usd"].as_str()), (Some(1), Some("1.5")));

    for (name, condition) in [("fresh-exhausted", ProviderCondition::ContextExhausted), ("login", ProviderCondition::AccountRefused { reason: "authentication_failed".into() })] {
        let root = scratch_root(name);
        let mut author = FixtureAuthor { script: vec![Some(condition)], ..Default::default() };
        for _ in 0..2 {
            let error = run(&unguarded_request(), &root, &mut author, &mut FixtureRole::default()).await.unwrap_err();
            assert!(matches!(error, ControllerError::Author { stage: "provider_refusal", .. }), "{name}: {error}");
        }
        assert_eq!((author.calls, author.waits.len()), (1, 0), "{name}: never retried");
        assert!(load(&root.join("ledger.json"))["closed"].is_null(), "{name}: the session stays resumable");
    }
}

/// A session continuing from `source` with `max_iterations` submissions.
fn continuing_request(source: &Path, max_iterations: u32) -> RunRequest {
    RunRequest { limits: Limits { max_iterations, ..limits() }, continue_from: Some(source.to_path_buf()), ..request() }
}

/// The incumbent is seeded, frozen and evaluated once before the first author call (iteration 0, never counted); the
/// author sees it first in its feedback; slower submissions do not replace it, so it is the candidate qualified; a
/// restarted controller returns the closure without evaluating anything again. An ordinary session's ledger and summary
/// carry no incumbent.
#[tokio::test]
async fn a_continuing_session_keeps_a_faster_incumbent_and_qualifies_it() {
    let root = scratch_root("incumbent-kept");
    let source = root.join("earlier-session");
    let mut author = FixtureAuthor::default();
    let mut role = FixtureRole { scores: vec![10, 50, 40], ..FixtureRole::default() };
    let result = run(&continuing_request(&source, 2), &root.join("session"), &mut author, &mut role).await.unwrap();
    assert_eq!((role.seeded, role.evaluated, author.calls), (1, 3, 2));
    assert_eq!((result["reason"].as_str(), result["iterations"].as_u64()), (Some("iteration_limit"), Some(2)), "two counted submissions");
    assert_eq!(result["qualification"][0]["iteration"], 0, "the faster incumbent is qualified");
    assert_eq!(result["incumbent"]["evaluation"]["score_ns"], 10);
    let first: Value = serde_json::from_str(&author.prompts[0]).unwrap();
    assert_eq!((first["feedback"][0]["iteration"].as_u64(), first["feedback"][0]["call_id"].as_u64()), (Some(0), Some(0)));
    assert_eq!(first["feedback"][0]["candidate"]["incumbent"]["source_session"], json!(source));
    let ledger = load(&root.join("session/ledger.json"));
    assert_eq!((ledger["trials"].as_array().unwrap().len(), ledger["incumbent"]["iteration"].as_u64()), (2, Some(0)));
    assert!(root.join("session/iterations/0000/incumbent.json").is_file() && root.join("session/author/incumbent-manifest.json").is_file());
    assert_eq!(run(&continuing_request(&source, 2), &root.join("session"), &mut author, &mut role).await.unwrap(), result);
    assert_eq!((role.seeded, role.evaluated), (1, 3));

    let plain_root = scratch_root("incumbent-absent");
    let plain = run(&request(), &plain_root, &mut FixtureAuthor::default(), &mut FixtureRole::default()).await.unwrap();
    assert!(plain.get("incumbent").is_none() && load(&plain_root.join("ledger.json")).get("incumbent").is_none());
}

/// A faster submission replaces the incumbent; an incumbent that already meets the role's stop ends the session before
/// any author call and is qualified.
#[tokio::test]
async fn a_faster_submission_replaces_the_incumbent_and_a_sufficient_incumbent_calls_no_author() {
    let root = scratch_root("incumbent-replaced");
    let mut author = FixtureAuthor::default();
    let mut role = FixtureRole { scores: vec![100, 10], ..FixtureRole::default() };
    let result = run(&continuing_request(&root.join("earlier"), 1), &root.join("session"), &mut author, &mut role).await.unwrap();
    assert_eq!((author.calls, result["qualification"][0]["iteration"].as_u64()), (1, Some(1)));

    let root = scratch_root("incumbent-sufficient");
    let mut author = FixtureAuthor::default();
    let mut role = FixtureRole { scores: vec![10], policy: FixturePolicy { stop_at_first_eligible: true, ..FixturePolicy::default() }, ..FixtureRole::default() };
    let result = run(&continuing_request(&root.join("earlier"), 2), &root.join("session"), &mut author, &mut role).await.unwrap();
    assert_eq!((author.calls, result["reason"].as_str(), result["iterations"].as_u64()), (0, Some("first_eligible_candidate"), Some(0)));
    assert_eq!((result["qualification"][0]["iteration"].as_u64(), role.qualified), (Some(0), 1));
}

/// Under a render-only author the source's recorded evaluation stands in for the incumbent's (marked, nothing
/// evaluated) and is never qualified.
#[tokio::test]
async fn a_render_only_author_shows_the_recorded_incumbent_and_never_qualifies_it() {
    let root = scratch_root("incumbent-render");
    let source = root.join("earlier");
    fs::create_dir_all(&source).unwrap();
    write_json_atomic(&source.join("evaluation.json"), &json!({"eligible":true,"score_ns":5,"status":"verified"})).unwrap();
    let mut author = FixtureAuthor { render_only: true, ..FixtureAuthor::default() };
    let mut role = FixtureRole { scores: vec![50], ..FixtureRole::default() };
    let result = run(&continuing_request(&source, 1), &root.join("session"), &mut author, &mut role).await.unwrap();
    assert_eq!((role.evaluated, author.calls), (1, 1), "only the submission is evaluated");
    let incumbent = &result["incumbent"]["evaluation"];
    assert_eq!(incumbent["score_ns"], 5);
    let recorded = load(&root.join("session/iterations/0000/evaluation.json"));
    assert_eq!(recorded[RENDER_ONLY_FIELD]["recorded_evaluation"], json!(source.join("evaluation.json")));
    let qualified: Vec<u64> = result["qualification"].as_array().unwrap().iter().filter_map(|q| q["iteration"].as_u64()).collect();
    assert_eq!(qualified, vec![1], "the faster recorded incumbent is never qualified");
}

/// The operator's stop: recorded once (a second request returns the first record), refused without a reason or for a
/// closed session; a session with the record calls no further author, still establishes and qualifies its incumbent,
/// and closes with `operator_stop`.
#[tokio::test]
async fn an_operator_stop_closes_the_session_before_its_next_call() {
    let root = scratch_root("operator-stop");
    let session = root.join("session");
    let mut author = FixtureAuthor::default();
    let mut role = FixtureRole { scores: vec![10, 50], ..FixtureRole::default() };
    let request = continuing_request(&root.join("earlier"), 2);
    assert!(record_operator_stop(&session, "too early").is_err(), "no session yet");
    // The session's ledger exists (as once its controller started), then the operator records the stop.
    Ledger::open(&session, run_identity(&request, &author.capability()), request.limits.clone()).unwrap();
    assert!(record_operator_stop(&session, " ").unwrap_err().contains("needs a reason"));
    let first = record_operator_stop(&session, "user: enough").unwrap();
    assert_eq!(record_operator_stop(&session, "again").unwrap(), first, "written once");
    let result = run(&request, &session, &mut author, &mut role).await.unwrap();
    assert_eq!((author.calls, result["reason"].as_str(), result["iterations"].as_u64()), (0, Some("operator_stop"), Some(0)));
    assert_eq!((result["qualification"][0]["iteration"].as_u64(), role.evaluated), (Some(0), 1), "the incumbent is still established and qualified");
    assert!(record_operator_stop(&session, "late").unwrap_err().contains("is closed"));
}

/// An incumbent directory without its provenance record is this session's own partial work: kept aside under another
/// name (its files may be read-only) and the incumbent is seeded, frozen and evaluated again.
#[tokio::test]
async fn a_partial_incumbent_is_set_aside_and_redone() {
    let root = scratch_root("incumbent-partial");
    let partial = root.join("session/iterations/0000");
    fs::create_dir_all(&partial).unwrap();
    fs::write(partial.join("frozen-candidate.json"), "{}").unwrap();
    let mut role = FixtureRole { scores: vec![10], ..FixtureRole::default() };
    let result = run(&continuing_request(&root.join("earlier"), 1), &root.join("session"), &mut FixtureAuthor::default(), &mut role).await.unwrap();
    assert_eq!((role.seeded, result["incumbent"]["evaluation"]["score_ns"].as_u64()), (1, Some(10)));
    let aside: Vec<String> = fs::read_dir(root.join("session/iterations")).unwrap().map(|e| e.unwrap().file_name().into_string().unwrap()).filter(|n| n.starts_with("0000-partial-")).collect();
    assert_eq!(aside.len(), 1, "the partial directory is kept aside");
    assert!(root.join("session/iterations/0000/incumbent.json").is_file());
}
