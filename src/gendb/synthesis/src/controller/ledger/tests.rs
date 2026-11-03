use super::*;
use crate::controller::limits::tests::limits;
use crate::controller::limits::{SpendPolicy, UNSET_COUNT, UNSET_SECONDS};
use crate::controller::records::{read_json, write_json_atomic};
use crate::controller::test_support::{receipt, scratch_root};
use std::fs;

fn open(root: &Path, identity: Value) -> Ledger {
    Ledger::open(root, identity, limits()).unwrap()
}

fn push_settled(ledger: &mut Ledger, session: &str, scope: Option<UsageScope>, cost: &str, tokens: [u64; 4]) {
    let call = Call {
        id: ledger.state.calls.len() as u64 + 1,
        iteration: 1,
        attempt: 1,
        started_unix_ms: 0,
        reservation_usd: Money::default(),
        receipt: None,
        provider_session: None,
        resumes_provider_session: false,
        usage_in_resumed_session: false,
    };
    let mut settled = receipt(&call, session, Some(cost));
    let [input, output, cache_read, cache_creation] = tokens;
    settled.tokens = Some(Tokens { input, output, cache_read, cache_creation });
    settled.usage_scope = scope;
    ledger.state.calls.push(Call { receipt: Some(settled), ..call });
}

/// Counting follows each receipt's declared scope, never magnitudes. Session totals (Stage C Q19 run-01's actual
/// receipts, Claude Code 2.1.280, one session) count once; invocation totals are summed; unknown scope counts raw,
/// flagged; a session total that decreases is a conflict (usage unknown), not a reset.
#[test]
fn usage_is_counted_by_declared_receipt_scope() {
    let mut ledger = open(&scratch_root("scope"), Value::Null);
    let session = Some(UsageScope::Session);
    let invocation = Some(UsageScope::Invocation);
    push_settled(&mut ledger, "a", session, "4.696694599999999", [72, 88212, 4869033, 244795]);
    push_settled(&mut ledger, "a", session, "5.017076399999999", [78, 90190, 5632582, 260806]);
    push_settled(&mut ledger, "a", session, "5.268066599999998", [82, 91854, 6167253, 274651]);
    push_settled(&mut ledger, "b", invocation, "1", [10, 100, 1000, 10]);
    push_settled(&mut ledger, "b", invocation, "2", [20, 200, 2000, 20]);
    push_settled(&mut ledger, "c", None, "0.5", [1, 1, 1, 1]);
    push_settled(&mut ledger, "c", None, "0.75", [2, 2, 2, 2]);
    let bases: Vec<CountingBasis> = ledger.state.counted_usage().iter().map(|counted| counted.basis).collect();
    use CountingBasis::*;
    assert_eq!(bases, [SessionFirst, SessionIncrement, SessionIncrement, Invocation, Invocation, ScopeUnknown, ScopeUnknown]);
    assert_eq!(ledger.state.counted_usage()[1].cost.unwrap().decimal(), "0.3203818");
    let accounting = json!(ledger.accounting(None).unwrap());
    assert_eq!(accounting["provider_reported_cost_usd"], "9.518066599999998", "{accounting}");
    assert_eq!(accounting["raw_receipt_sum_usd"], "19.231837599999996");
    assert_eq!(accounting["scope_complete"], false);
    assert_eq!(accounting["tokens"], json!({"input":115,"output":92157,"cache_read":6170256,"cache_creation":274684}));
    assert_eq!(ledger.totals().unwrap().spent.decimal(), "9.518066599999998");
    // The author prompt's LEDGER counts the same way (a resumed session total once), not the raw receipt sum.
    let shown = ledger.author_view(99).unwrap();
    assert_eq!(shown["spent_usd"], "9.518066599999998", "{shown}");
    assert_eq!(shown["earlier_calls"], 7);
    // A lower session total without a declared reset: that call and later ones of its session are unknown.
    push_settled(&mut ledger, "a", session, "1", [1, 1, 1, 1]);
    push_settled(&mut ledger, "a", session, "6", [90, 95000, 6200000, 280000]);
    let tail: Vec<_> = ledger.state.counted_usage()[7..].iter().map(|counted| (counted.basis, counted.cost)).collect();
    assert_eq!(tail, [(ScopeConflict, None), (ScopeConflict, None)]);
    assert_eq!(ledger.accounting(None).unwrap().cost_complete, false);
    assert_eq!(ledger.stop_reason().unwrap(), Some(LedgerStop::UsageUnknown));
}

/// Consecutive calls of one iteration that ended without a candidate and share an outcome class (for example
/// session-limit retries, whose texts differ in the reported conversation size) take one LEDGER run with its range,
/// count and last outcome; a call with a candidate, another class or another iteration ends the run. The view stays
/// the same size however many such calls repeat; every call stays in ledger.json.
#[test]
fn author_view_bounds_repeated_calls_without_a_candidate() {
    let root = scratch_root("repeats");
    let mut ledger = open(&root, Value::Null);
    let session = Some(UsageScope::Session);
    for total in ["47.3", "47.3", "47.3", "47.3", "47.3", "47.5", "47.5"] {
        push_settled(&mut ledger, "a", session, total, [1, 1, 1, 1]);
    }
    let outcomes = ["provider_error: limit", "provider_error: 58.8MB", "provider_error: 177.1MB", "schema_error: x", "success"];
    for (call, outcome) in ledger.state.calls[1..6].iter_mut().zip(outcomes) {
        call.receipt.as_mut().unwrap().outcome = outcome.into();
    }
    ledger.state.calls[0].receipt.as_mut().unwrap().output = Some(json!({}));
    ledger.state.calls[5].receipt.as_mut().unwrap().output = Some(json!({}));
    ledger.state.calls[6].iteration = 2;
    let shown = ledger.author_view(99).unwrap();
    let runs: Vec<_> = shown["runs_without_candidate"].as_array().unwrap().iter()
        .map(|run| (run["first_call"].clone(), run["last_call"].clone(), run["calls"].clone(), run["last_outcome"].clone())).collect();
    assert_eq!(runs, [
        (json!(2), json!(4), json!(3), json!("provider_error: 177.1MB")),
        (json!(5), json!(5), json!(1), json!("schema_error: x")),
        (json!(7), json!(7), json!(1), json!("error")),
    ], "{shown}");
    assert_eq!((shown["earlier_calls"].as_u64(), shown["spent_usd"].as_str()), (Some(7), Some("47.5")));
    assert_eq!(shown["file"], json!(root.join("ledger.json")));
}

/// The two terminal results (observed numbers) of one Claude Code 2.1.280 session (the first invocation, then
/// the same session resumed). `total_cost_usd`, `modelUsage` and `duration_api_ms` are session
/// totals; `duration_ms` and the top-level `usage` cover one invocation. Counted once: the final cumulative cost and
/// token totals; wall time is summed per invocation; raw results stay unchanged.
#[test]
fn resumed_claude_session_counts_final_cumulative_cost_once_and_wall_per_invocation() {
    let mut ledger = open(&scratch_root("r1a-receipts"), Value::Null);
    let session = "00000000-0000-4000-8000-0000000000a1";
    let results = [
        json!({"type":"result","subtype":"success","session_id":session,"total_cost_usd":10.9926742,
            "duration_ms":1359007,"duration_api_ms":1333010,
            "usage":{"input_tokens":178,"output_tokens":169589,"cache_read_input_tokens":22164751,"cache_creation_input_tokens":395904},
            "modelUsage":{"claude-opus-5-5":{"inputTokens":178,"outputTokens":169589,"cacheReadInputTokens":22164751,"cacheCreationInputTokens":395904,"costUSD":10.9926742}}}),
        json!({"type":"result","subtype":"success","session_id":session,"total_cost_usd":12.292872199999998,
            "duration_ms":93811,"duration_api_ms":1420250,
            "usage":{"input_tokens":20,"output_tokens":9699,"cache_read_input_tokens":4261890,"cache_creation_input_tokens":31720},
            "modelUsage":{"claude-opus-5-5":{"inputTokens":198,"outputTokens":179288,"cacheReadInputTokens":26426641,"cacheCreationInputTokens":427624,"costUSD":12.292872199999998}}}),
    ];
    for raw in &results {
        // As the provider adapter settles it: cost from the raw result, tokens from modelUsage, wall per invocation.
        let usage = &raw["modelUsage"]["claude-opus-5-5"];
        let token = |key: &str| usage[key].as_u64().unwrap();
        push_settled(&mut ledger, session, Some(UsageScope::Session), "0", [0; 4]);
        let settled = ledger.state.calls.last_mut().unwrap().receipt.as_mut().unwrap();
        settled.reported_cost_usd = reported_total_cost(raw);
        settled.tokens = Some(Tokens {
            input: token("inputTokens"),
            output: token("outputTokens"),
            cache_read: token("cacheReadInputTokens"),
            cache_creation: token("cacheCreationInputTokens"),
        });
        settled.elapsed_ms = raw["duration_ms"].as_u64().unwrap();
        settled.raw_result = Some(raw.clone());
    }
    let counted = ledger.state.counted_usage();
    assert_eq!(counted[0].cost.unwrap().decimal(), "10.9926742");
    assert_eq!(counted[1].cost.unwrap().decimal(), "1.300197999999998");
    assert_eq!(counted[1].tokens.as_ref().unwrap().output, 9699, "the increment equals the invocation's own usage");
    let accounting = ledger.accounting(None).unwrap();
    assert_eq!(accounting.provider_reported_cost_usd.unwrap().decimal(), "12.292872199999998");
    assert_eq!(accounting.raw_receipt_sum_usd.decimal(), "23.285546399999998", "summing raw totals would double count");
    assert_eq!(accounting.tokens, Some(Tokens { input: 198, output: 179288, cache_read: 26426641, cache_creation: 427624 }));
    assert_eq!(accounting.author_elapsed_ms, 1359007 + 93811);
    assert!(accounting.scope_complete);
    assert_eq!(ledger.state.calls[1].receipt.as_ref().unwrap().raw_result.as_ref(), Some(&results[1]));
}

#[test]
fn crash_resume_reservation_and_duplicate_receipts() {
    let root = scratch_root("crash-resume");
    let mut ledger = open(&root, Value::Null);
    let call = ledger.begin_call().unwrap();
    let session = ledger.state.session_id.clone();
    drop(ledger);
    let mut ledger = open(&root, Value::Null);
    assert_eq!(ledger.stop_reason().unwrap(), Some(LedgerStop::UsageUnknown));
    let settled = receipt(&call, &session, Some("0.25"));
    ledger.settle(settled.clone()).unwrap();
    ledger.settle(settled.clone()).unwrap();
    assert_eq!(ledger.totals().unwrap().spent.decimal(), "0.25");
    let mut conflict = settled;
    conflict.outcome = "changed".into();
    assert_eq!(ledger.settle(conflict), Err(LedgerError::ConflictingDuplicateReceipt(1)));
    assert!(ledger.begin_call().is_ok());
    assert_eq!(Ledger::open(&root, Value::Null, limits()).err(), Some(LedgerError::AlreadyOwned));
}

/// A dropped ledger frees its run lock at once, even while a child that another thread is spawning still shares the
/// lock's open file description (between the child's fork and exec). Closing the descriptor alone left the lock held
/// for that window, and a resume in it was refused as `AlreadyOwned` (the flaky parallel ledger/run tests).
#[test]
fn dropped_ledger_releases_its_lock_while_a_spawning_child_shares_it() {
    use std::os::unix::process::CommandExt;
    let root = scratch_root("spawn-window");
    let ledger = open(&root, Value::Null);
    let mut pipe = [0; 2];
    // SAFETY: pipe fills the two descriptors of a fresh pipe; both are closed below.
    assert_eq!(unsafe { libc::pipe(pipe.as_mut_ptr()) }, 0);
    let [forked, signal] = pipe;
    let spawner = std::thread::spawn(move || {
        let mut command = std::process::Command::new("/bin/true");
        // SAFETY: between fork and exec the child only calls the async-signal-safe write and nanosleep.
        unsafe {
            command.pre_exec(move || {
                libc::write(signal, b"f".as_ptr().cast(), 1);
                let hold = libc::timespec { tv_sec: 0, tv_nsec: 300_000_000 };
                libc::nanosleep(&hold, std::ptr::null_mut());
                Ok(())
            })
        };
        command.status().unwrap()
    });
    let mut byte = 0u8;
    // SAFETY: reads one byte into a local; returns once the forked child has written it.
    assert_eq!(unsafe { libc::read(forked, (&mut byte as *mut u8).cast(), 1) }, 1);
    // The child now shares every descriptor of this process, the run lock's included, until its exec.
    drop(ledger);
    assert!(Ledger::open(&root, Value::Null, limits()).is_ok());
    assert!(spawner.join().unwrap().success());
    // SAFETY: closes the two pipe descriptors this test created.
    unsafe { libc::close(forked) };
    unsafe { libc::close(signal) };
}

#[test]
fn failures_retry_finitely_and_unknown_is_not_zero() {
    let mut ledger = open(&scratch_root("retry"), Value::Null);
    for _ in 0..2 {
        let call = ledger.begin_call().unwrap();
        let session = ledger.state.session_id.clone();
        ledger.settle(receipt(&call, &session, Some("0"))).unwrap();
    }
    assert_eq!(ledger.stop_reason().unwrap(), Some(LedgerStop::RetryLimit));
    let mut ledger = open(&scratch_root("unknown"), Value::Null);
    let call = ledger.begin_call().unwrap();
    let session = ledger.state.session_id.clone();
    ledger.settle(receipt(&call, &session, None)).unwrap();
    assert_eq!(ledger.totals().unwrap().reserved.decimal(), "1");
    assert_eq!(ledger.begin_call().err(), Some(LedgerError::Stopped(LedgerStop::UsageUnknown)));
    let evidence = json!({"source":"fixture provider receipt"});
    ledger.reconcile_usage(call.id, Some(Money::parse("0.25").unwrap()), None, None, evidence).unwrap();
    let totals = ledger.totals().unwrap();
    assert_eq!((totals.spent.decimal(), totals.reserved.decimal()), ("0.25".into(), "0".into()));
    assert_eq!(ledger.state.receipt_reconciliations.len(), 1);
    let conflicting = json!({"source":"conflicting receipt"});
    assert!(ledger.reconcile_usage(call.id, Some(Money::parse("0.1").unwrap()), None, None, conflicting).is_err());
}

#[test]
fn provider_cost_legacy_receipts_partial_totals_and_policy_independence() {
    for policy in [SpendPolicy::EstimatedUsd, SpendPolicy::StrictUsd] {
        let limits = Limits { spend_policy: policy, ..limits() };
        let root = scratch_root("legacy-cost");
        let mut ledger = Ledger::open(&root, Value::Null, limits.clone()).unwrap();
        let call = ledger.begin_call().unwrap();
        let session = ledger.state.session_id.clone();
        let mut settled = receipt(&call, &session, None);
        settled.raw_result = Some(json!({"total_cost_usd":"0.4","subtype":"error_during_execution"}));
        // Historical spelling of the recorded cost field.
        let mut legacy = serde_json::to_value(&settled).unwrap();
        legacy.as_object_mut().unwrap().remove("provider_reported_cost_usd");
        legacy["estimated_cost_usd"] = Value::Null;
        let settled: Receipt = serde_json::from_value(legacy).unwrap();
        ledger.settle(settled.clone()).unwrap();
        ledger.settle(settled).unwrap();
        let totals = ledger.totals().unwrap();
        assert_eq!((totals.spent, totals.reserved, totals.usage_unknown), (Money::parse("0.4").unwrap(), Money::default(), false));
        assert!(ledger.reconcile_usage(call.id, Some(Money::parse("0.3").unwrap()), None, None, json!({"source":"fixture"})).is_err());
        let second = ledger.begin_call().unwrap();
        ledger.settle(receipt(&second, &session, None)).unwrap();
        let accounting = json!(ledger.accounting(None).unwrap());
        assert!(accounting["provider_reported_cost_usd"].is_null());
        assert_eq!(accounting["known_provider_reported_cost_usd"], "0.4");
        assert_eq!(accounting["cost_complete"], false);
        assert!(accounting["tokens"].is_null());
        assert_eq!(ledger.totals().unwrap().reserved.decimal(), "0.6");
        drop(ledger);
        let ledger = Ledger::open(&root, Value::Null, limits).unwrap();
        assert_eq!(json!(ledger.accounting(None).unwrap()), accounting);
        assert_eq!(ledger.stop_reason().unwrap(), Some(LedgerStop::UsageUnknown));
    }
    let call = Call { id: 1, iteration: 1, attempt: 1, started_unix_ms: 0, reservation_usd: Money::parse("1").unwrap(), receipt: None, provider_session: None, resumes_provider_session: false, usage_in_resumed_session: false };
    let mut legacy = serde_json::to_value(receipt(&call, "s", Some("0.25"))).unwrap();
    legacy.as_object_mut().unwrap().remove("provider_reported_cost_usd");
    legacy["estimated_cost_usd"] = json!("0.25");
    legacy["billed_cost_usd"] = json!("0.25");
    assert_eq!(serde_json::from_value::<Receipt>(legacy.clone()).unwrap().provider_cost().unwrap().decimal(), "0.25");
    legacy["estimated_cost_usd"] = Value::Null;
    assert_eq!(serde_json::from_value::<Receipt>(legacy).unwrap().provider_cost().unwrap().decimal(), "0.25");
}

#[test]
fn unset_guards_reserve_unset_and_still_stop_on_unknown_usage() {
    let unset = Limits {
        max_iterations: UNSET_COUNT,
        max_cost_usd: Money::UNSET,
        spend_policy: SpendPolicy::EstimatedUsd,
        max_retries_per_iteration: UNSET_COUNT,
        max_author_tool_turns: 0,
        author_timeout_seconds: UNSET_SECONDS,
    };
    let root = scratch_root("unset");
    let mut ledger = Ledger::open(&root, Value::Null, unset.clone()).unwrap();
    assert!(ledger.begin_call().unwrap().reservation_usd.is_unset());
    assert_eq!(ledger.stop_reason().unwrap(), Some(LedgerStop::UsageUnknown));
    drop(ledger);
    assert!(Ledger::open(&root, Value::Null, unset).is_ok());
}

#[test]
fn retired_turn_cap_resume_preserves_history_and_all_active_guards() {
    for mode in ["active", "pending", "budget", "iterations", "retries"] {
        let root = scratch_root("retired-turns");
        let old_limits = Limits { max_author_tool_turns: 100, ..limits() };
        let old_request = json!({"request":{"task":{"sql":"fixture"},"limits":old_limits}});
        let mut ledger = Ledger::open(&root, old_request.clone(), old_limits.clone()).unwrap();
        let session = ledger.state.session_id.clone();
        let call = ledger.begin_call().unwrap();
        if mode != "pending" {
            let mut settled = receipt(&call, &session, Some(if mode == "budget" { "1.25" } else { "0.25" }));
            settled.outcome = "error_max_turns".into();
            ledger.settle(settled).unwrap();
        }
        if mode == "iterations" {
            ledger.state.iterations = old_limits.max_iterations;
        }
        if mode == "retries" {
            let call = ledger.begin_call().unwrap();
            ledger.settle(receipt(&call, &session, Some("0.125"))).unwrap();
        }
        if matches!(mode, "budget" | "iterations" | "retries") {
            ledger.state.closed = Some(json!({"reason":mode,"historical":true}));
        }
        ledger.save().unwrap();
        let prior = json!(ledger.state);
        let totals = ledger.totals().unwrap();
        let stop = ledger.stop_reason().unwrap();
        drop(ledger);
        let original_bytes = fs::read(root.join("ledger.json")).unwrap();
        let new_limits = old_limits.active();
        let new_request = json!({"request":{"task":{"sql":"fixture"},"limits":new_limits}});
        for field in ["max_cost_usd", "max_iterations", "spend_policy", "max_retries_per_iteration", "author_timeout_seconds"] {
            let mut changed = json!(new_limits);
            changed[field] = match field {
                "max_cost_usd" => json!("2"),
                "spend_policy" => json!("strict_usd"),
                _ => json!(9),
            };
            let changed: Limits = serde_json::from_value(changed).unwrap();
            assert!(Ledger::open(&root, new_request.clone(), changed).is_err(), "{field}");
            let mut changed_request = new_request.clone();
            changed_request["request"]["limits"][field] = Value::Null;
            assert!(Ledger::open(&root, changed_request, new_limits.clone()).is_err(), "request {field}");
        }
        let mut resumed = Ledger::open(&root, new_request, new_limits).unwrap();
        assert_eq!(json!(resumed.state), prior, "{mode}");
        assert_eq!(resumed.totals().unwrap(), totals);
        assert_eq!(resumed.stop_reason().unwrap(), stop);
        assert_eq!(fs::read(root.join("ledger.json")).unwrap(), original_bytes);
        if mode == "active" {
            let next = resumed.begin_call().unwrap();
            assert_eq!((next.id, next.attempt, next.reservation_usd.decimal()), (2, 2, "0.75".to_string()));
            assert_eq!(resumed.state.request, old_request);
            assert_eq!(resumed.state.limits.max_author_tool_turns, 100);
            assert_eq!(json!(resumed.state.calls[0]), prior["calls"][0]);
        } else {
            assert!(resumed.begin_call().is_err(), "{mode}");
        }
    }
}

/// Resume ignores only provider cost wording; request, provider version/model and active limits are fixed, and a
/// closed legacy ledger is not rewritten.
#[test]
fn resume_identity_ignores_only_cost_wording_and_does_not_rewrite_closed_ledger() {
    let root = scratch_root("resume-identity");
    let old = json!({"author":{"cost_semantics":"old estimate wording","model":"fixture","version":"2.1.280"},
        "request":{"task":{"sql":"fixture","shared_design":{"status":"not_applicable"}}}});
    let mut ledger = open(&root, old.clone());
    let call = ledger.begin_call().unwrap();
    let session = ledger.state.session_id.clone();
    ledger.settle(receipt(&call, &session, Some("1.25"))).unwrap();
    ledger.state.closed = Some(json!({"historical":true}));
    ledger.save().unwrap();
    drop(ledger);
    // Materialize the historical spelling of the recorded cost in this test-only ledger.
    let mut state: Value = read_json(&root.join("ledger.json")).unwrap();
    let recorded = state["calls"][0]["receipt"].as_object_mut().unwrap();
    let cost = recorded.remove("provider_reported_cost_usd").unwrap();
    recorded.insert("estimated_cost_usd".into(), cost);
    write_json_atomic(&root.join("ledger.json"), &state).unwrap();
    let before = fs::read(root.join("ledger.json")).unwrap();
    let mut reworded = old.clone();
    reworded["author"]["cost_semantics"] = json!("provider-reported");
    let ledger = open(&root, reworded.clone());
    assert_eq!(ledger.totals().unwrap().spent.decimal(), "1.25");
    assert_eq!(ledger.stop_reason().unwrap(), Some(LedgerStop::BudgetLimit));
    assert_eq!(ledger.state.request, old);
    drop(ledger);
    assert_eq!(fs::read(root.join("ledger.json")).unwrap(), before);
    for (pointer, value) in [
        ("/author/model", json!("changed")),
        ("/author/version", json!("2.1.281")),
        ("/request/task/sql", json!("other")),
        // The archived shared-design context refresh no longer applies.
        ("/request/task/shared_design", json!({"portfolio_available":true})),
    ] {
        let mut changed = reworded.clone();
        *changed.pointer_mut(pointer).unwrap() = value;
        assert_eq!(Ledger::open(&root, changed, limits()).err(), Some(LedgerError::ResumeIdentityDiffers), "{pointer}");
    }
    let doubled = Limits { max_cost_usd: Money::parse("2").unwrap(), ..limits() };
    assert!(Ledger::open(&root, old, doubled).is_err());
}

/// A historical ledger that carries archived fields still loads and keeps them.
#[test]
fn historical_ledger_fields_are_read_and_preserved() {
    let root = scratch_root("historical");
    let ledger = open(&root, Value::Null);
    drop(ledger);
    let mut state: Value = read_json(&root.join("ledger.json")).unwrap();
    assert!(state.get("preparation_context_revisions").is_none(), "new ledgers do not write the archived field");
    state["preparation_context_revisions"] = json!([{"reason":"historical shared-design refresh"}]);
    state["trials"] = json!([{"iteration":1,"call_id":1,"candidate":{"candidate_manifest":"c.json"},"status":"evaluated",
        "evaluation":{"eligible":true,"score_ns":5},"framework_elapsed_ms":7,"directory":"/d"}]);
    write_json_atomic(&root.join("ledger.json"), &state).unwrap();
    let ledger = open(&root, Value::Null);
    assert_eq!(ledger.state.preparation_context_revisions.len(), 1);
    assert!(ledger.state.trials[0].eligible() && ledger.state.trials[0].score_ns() == 5.0);
    ledger.save().unwrap();
    let saved: Value = read_json(&root.join("ledger.json")).unwrap();
    assert_eq!(saved["preparation_context_revisions"], state["preparation_context_revisions"]);
    assert_eq!(saved["trials"], state["trials"]);
}

/// An interrupted call awaiting its session's resumption does not stop the run, and once the resuming call settles a
/// session total, the interrupted call counts zero (the resuming call's total includes it).
#[test]
fn an_interrupted_call_is_settled_by_its_resumed_session_total() {
    let root = scratch_root("ledger-resumed-session");
    let mut ledger = open(&root, json!({"run":"resumed"}));
    let session = ledger.state.session_id.clone();
    let interrupted = Call {
        id: 1,
        iteration: 1,
        attempt: 1,
        started_unix_ms: 0,
        reservation_usd: Money::default(),
        receipt: None,
        provider_session: Some(session.clone()),
        resumes_provider_session: false,
        usage_in_resumed_session: true,
    };
    ledger.state.calls.push(interrupted);
    assert!(!ledger.totals().unwrap().usage_unknown, "awaiting resumption is not unknown usage");
    assert_eq!(ledger.state.counted_usage()[0].basis, CountingBasis::NoReceipt);
    push_settled(&mut ledger, &session, Some(UsageScope::Session), "2.5", [1, 2, 3, 4]);
    let counted = ledger.state.counted_usage();
    assert_eq!(counted[0].basis, CountingBasis::InResumedSessionTotal);
    assert_eq!(counted[1].cost, Some(Money::parse("2.5").unwrap()));
}
