//! Run R: the user's stop during a live call of the real Claude Code CLI. PAID: every call
//! is a real provider call of the request's author model (the default, `claude-opus-5-5`) within the run's budget
//! (`GENDB_LIVE_BUDGET` dollars, default [`DEFAULT_LIVE_BUDGET`]; the CLI also receives the budget left as
//! `--max-budget-usd`). FRAMEWORK TEST ONLY: the trial fixture (tiny data, one scale, one branch, the slowed root) and
//! the public general-line controller (`branches::run_general_engine`) with the author `gendb engine synthesize` builds
//! (`rounds::claude_code_author`: the CLI at `GENDB_LIVE_AUTHOR`, inspected, with GenDB's local tool server). Only the
//! prompt differs: [`live_stop_prompt`], a framework check that keeps the call busy in one long Bash command (Claude
//! Code 2.1.286 refuses a standalone `sleep` in its Bash tool, so the command waits in Python). Run with `-- --ignored`
//! and the trial environment (`TMPDIR`, `GENDB_WORKER`, `GENDB_BUILD_LOCK`, `GENDB_TRIAL_DIR`).
//!
//! Every launch is a trial child (`trial_child`, mode `live`) that installs the user's stop as the commands do:
//! 1. b1's first call. Once the author's Bash tool call is in flight (GenDB's Bash guardian or its command runs;
//!    [`live_call`]), the
//!    controller gets SIGTERM. If the call ends first, the controller gets SIGTERM at once, so no further paid call
//!    starts (the test then fails: the stop was not during a live call). Checked by `stops::stop_by_term`: it ends by SIGTERM, every process seen just before has
//!    ended, their process groups are empty, the stop record has no survivor and `leftovers` lists nothing; here also:
//!    the provider's group got SIGINT, its transcript ends with its one terminal result, which reports a cost, and the
//!    supervising thread settled nothing (no `process-exit.json`).
//! 2. Relaunch. The stopped call is recovered from that result (`controller-loss-recovery.json`); the next call
//!    continues the provider session (`--resume` with the first call's session, which the provider's init event names
//!    again). It is stopped the same way.
//! 3. Relaunch. The second call is recovered too. The request allows one retry per submission
//!    (`max_retries_per_iteration` 1), so the session ends without a third call and the run pauses after it
//!    (`every_session`). Checked: both calls carry their provider-reported cost in the ledger, the cost is complete (no
//!    `accounting_unresolved`), nothing is left.

use super::stops::{Seen, stop_by_term};
use super::*;
use crate::controller::PromptInput;
use crate::controller::layout::RunLayout;
use crate::controller::ledger::LedgerState;
use crate::controller::workload_run::WorkloadError;
use gendb_runtime::process_stop::leftovers;
use std::time::Duration;

/// The run's budget when `GENDB_LIVE_BUDGET` is not set, in dollars.
const DEFAULT_LIVE_BUDGET: &str = "0.6";
/// How long the author's Bash command waits, long enough to be live when the stop comes.
const LIVE_WAIT_SECONDS: u32 = 240;
/// How long after a call started the stop comes when no Bash tool call is in flight (the call is live, generating).
const LIVE_WAIT: Duration = Duration::from_secs(120);

/// The prompt of every call of run R: a framework check, not an engine task. One Read of the prompt itself, then one
/// long Bash command that keeps the call live until the stop.
fn live_stop_prompt(input: &PromptInput) -> String {
    format!(
        "This call is a check of GenDB's controller (how it stops and resumes an author call while a tool runs), not an engine task. The test stops this call from outside while step 2 runs. Do exactly these steps and nothing else:\n\n\
         1. Use the Read tool once to read the file {} (this prompt).\n\
         2. Use the Bash tool once, in the foreground, with a timeout of 600000 ms, to run exactly this command: python3 -c \"import time; time.sleep({LIVE_WAIT_SECONDS})\"\n\
         3. Reply with the single word DONE. If the command was refused, do not retry it.\n\n\
         Do not write, edit or create any file. Do not call any other tool, including GenDB's local tools.\n",
        input.prompt_file.display()
    )
}

/// The `live` trial child: the public general-line controller with the author of `gendb engine synthesize` and
/// [`live_stop_prompt`].
pub(super) async fn run_live(request: &WorkloadRequest, run: &Path) -> Result<Value, WorkloadError> {
    let framework = worker();
    let authors = |_: &str, evidence: &Path| super::super::rounds::claude_code_author(request, &framework, evidence);
    let options = GeneralRunOptions { prompt: live_stop_prompt, render_only: false };
    run_general_engine(request, run, authors, &framework, options).await
}

/// Ready to stop the call recorded in `call_dir`: its invocation is recorded, and a Bash tool call is in flight
/// ([`bash_tool_in_flight`]), or [`LIVE_WAIT`] has passed since the invocation, or the call has ended (its transcript
/// holds its result: stop at once, before another paid call starts).
fn live_call(seen: &[Seen], call_dir: &Path) -> bool {
    let Ok(invoked) = fs::metadata(call_dir.join("invocation.json")).and_then(|m| m.modified()) else { return false };
    let ended = fs::read_to_string(call_dir.join("stdout.jsonl")).is_ok_and(|t| t.lines().any(|l| l.contains("\"type\":\"result\"")));
    ended || bash_tool_in_flight(seen.iter().map(|p| p.name.as_str())) || invoked.elapsed().unwrap_or_default() >= LIVE_WAIT
}

/// Whether a Bash tool call is in flight among processes named `names`: GenDB's Bash guardian (`gendb-author-bash`, its
/// command name cut to `gendb-author-ba`; it may still wait for the host's activity lease) or the command it runs
/// (`python3`).
fn bash_tool_in_flight<'a>(mut names: impl Iterator<Item = &'a str>) -> bool {
    names.any(|name| name.starts_with("gendb-author-ba") || name.starts_with("python"))
}

/// The events of a provider transcript.
fn transcript_events(call_dir: &Path) -> Vec<Value> {
    let text = fs::read_to_string(call_dir.join("stdout.jsonl")).unwrap();
    text.lines().filter(|l| !l.trim().is_empty()).map(|l| serde_json::from_str(l).unwrap()).collect()
}

/// What a stopped call's transcript shows: its provider session (init event), whether its Bash tool ran, and its
/// terminal result, which must be the transcript's one result and its last event.
fn stopped_call(call_dir: &Path) -> Value {
    let events = transcript_events(call_dir);
    let init = events.iter().find(|e| e["type"] == "system" && e["subtype"] == "init").expect("the provider's init event");
    let results: Vec<&Value> = events.iter().filter(|e| e["type"] == "result").collect();
    let last = events.last().unwrap();
    assert_eq!((results.len(), last["type"].as_str()), (1, Some("result")), "{}: the provider wrote its one terminal result last", call_dir.display());
    assert!(last["total_cost_usd"].is_number() && last["duration_ms"].is_number(), "the terminal result reports the call's cost: {last}");
    let tools: Vec<&str> = events
        .iter()
        .filter(|e| e["type"] == "assistant")
        .flat_map(|e| e["message"]["content"].as_array().into_iter().flatten())
        .filter(|c| c["type"] == "tool_use")
        .filter_map(|c| c["name"].as_str())
        .collect();
    assert!(!call_dir.join("process-exit.json").exists(), "the supervising thread parked: the stopped call was not settled");
    json!({"session_id":init["session_id"],"model":init["model"],"claude_code_version":init["claude_code_version"],"tools_used":tools,
        "result":{"subtype":last["subtype"],"is_error":last["is_error"],"total_cost_usd":last["total_cost_usd"],"duration_ms":last["duration_ms"],
            "num_turns":last["num_turns"],"terminal_reason":last["terminal_reason"]}})
}

#[test]
#[ignore = "PAID: real Claude Code calls within GENDB_LIVE_BUDGET dollars (GENDB_LIVE_AUTHOR); the pinned frontend, Verus and the gendb worker on tiny data; TMPDIR, GENDB_WORKER, GENDB_BUILD_LOCK, GENDB_TRIAL_DIR; -- --ignored"]
fn real_author_stop_and_resume() {
    let author = PathBuf::from(std::env::var_os("GENDB_LIVE_AUTHOR").expect("GENDB_LIVE_AUTHOR names the author CLI"));
    let budget = std::env::var("GENDB_LIVE_BUDGET").unwrap_or_else(|_| DEFAULT_LIVE_BUDGET.into());
    let fixture = TrialFixture::prepare();
    let dir = run_folder("R");
    let library = dir.join("library");
    fixture.seed_library(&library);
    let shape = RunShape { branches: 1, budget: &budget, cadence: "every_session", author_executable: &author };
    let scales = [TrialScale { name: "s1", data: 0, capture: &fixture.s1_capture, original_data_bytes: fixture.s1_flat_bytes * 10 }];
    let request_path = fixture.request_with(&dir.join("request.json"), &library, &dir.join("home"), &scales, &shape);
    let request = WorkloadRequest::read(&request_path).unwrap();
    assert_eq!(request.engine().unwrap().limits.max_retries_per_iteration, 1, "one retry per submission ends the session after the second call");
    let run = dir.join("run");
    seed_slowed_root(&request, &run, &dir);
    let engine_dir = engine_directory(&run.canonicalize().unwrap());
    let session = super::super::sessions::session_directory(&engine_dir, "b1", 1);
    let call_dir = |n: u64| RunLayout::new(&session).call(n);
    let order = json!({"mode":"live","request":request_path,"run":run});

    // 1. b1's first call, stopped by SIGTERM while it runs.
    let name = "1-live-call-stopped";
    let first = stop_by_term(name, &dir, child_command(name, &dir, &order), &run, &|seen: &[Seen], _: &Path| live_call(seen, &call_dir(1)));
    let groups = first.stop["owned_groups"].as_array().unwrap();
    assert!(groups.iter().any(|g| g["what"].as_str().unwrap().starts_with("author provider") && g["signal"] == "SIGINT"), "{groups:?}");
    let call_one = stopped_call(&call_dir(1));
    let session_id = call_one["session_id"].as_str().unwrap().to_string();

    // 2. Relaunch: the first call is recovered; the second continues its provider session and is stopped the same way.
    let name = "2-relaunch-resumed-call-stopped";
    let second = stop_by_term(name, &dir, child_command(name, &dir, &order), &run, &|seen: &[Seen], _: &Path| live_call(seen, &call_dir(2)));
    let recovery: Value = read_json(&call_dir(1).join("controller-loss-recovery.json")).unwrap();
    assert_eq!((recovery["kind"].as_str(), recovery["provider_reported_cost_usd"].is_null()), (Some("controller_loss_receipt_recovery"), false), "{recovery}");
    let invocation: Value = read_json(&call_dir(2).join("invocation.json")).unwrap();
    let argv: Vec<&str> = invocation["argv"].as_array().unwrap().iter().filter_map(Value::as_str).collect();
    let resumed = argv.iter().position(|a| *a == "--resume").map(|at| argv[at + 1]);
    assert_eq!(resumed, Some(session_id.as_str()), "the second call continues the first call's provider session: {argv:?}");
    let call_two = stopped_call(&call_dir(2));
    assert_eq!(call_two["session_id"].as_str(), Some(session_id.as_str()), "the provider resumed the same session");

    // 3. Relaunch: the second call is recovered; one retry per submission ends the session without a third call.
    let third = launch_child("3-relaunch-recovers-and-pauses", &dir, &order, None);
    assert_eq!(third.code, Some(0), "{third:?}");
    let summary = latest_summary(&run);
    assert_eq!(summary["status"], PAUSED, "{summary}");
    assert!(!call_dir(3).exists(), "no third call");
    let ledger: LedgerState = read_json(&RunLayout::new(&session).ledger()).unwrap();
    assert_eq!(ledger.calls.len(), 2, "two calls");
    let counted = ledger.counted_usage();
    let calls: Vec<Value> = ledger
        .calls
        .iter()
        .zip(&counted)
        .map(|(call, counted)| {
            let receipt = call.receipt.as_ref().unwrap_or_else(|| panic!("call {} has no receipt", call.id));
            assert!(receipt.reported_cost_usd.is_some() && counted.cost.is_some(), "call {}: its provider-reported cost is in the ledger", call.id);
            json!({"call":call.id,"provider_session":ledger.provider_session_of(call),"resumes_provider_session":call.resumes_provider_session,
                "reported_cost_usd":receipt.reported_cost_usd,"usage_scope":receipt.usage_scope,"counted_cost_usd":counted.cost,"basis":format!("{:?}", counted.basis),
                "outcome":receipt.outcome})
        })
        .collect();
    assert_eq!(summary["spend"]["complete"], true, "the run's cost is complete: {}", summary["spend"]);
    let left = leftovers(&run).unwrap();
    assert_eq!(left.processes, Vec::<Value>::new(), "{left:?}");
    // Whether a Bash tool call was in flight at each stop (among the processes seen just before it).
    let in_flight = |stop: &super::stops::TermStop| bash_tool_in_flight(stop.stopped_names.iter().map(String::as_str));
    let evidence = json!({"fixture":fixture.dir,"run":run,"library":library,"request":request_path,"author":author,"budget_usd":budget,
        "bash_tool_in_flight_at_stop":[in_flight(&first),in_flight(&second)],"stops":[first.evidence(),second.evidence()],"calls":{"stopped":[call_one,call_two],"ledger":calls},"recovery":recovery,
        "second_call_argv":argv,"relaunch":format!("{third:?}"),"summary":summary,"leftovers":left.processes});
    write_json_atomic(&dir.join("evidence.json"), &evidence).unwrap();
    eprintln!("run R: {}", dir.display());
}
