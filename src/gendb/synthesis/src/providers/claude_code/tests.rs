//! Scoped tests of transcript parsing and receipt completion on fixed transcripts and the saved receipts of a real
//! session. No process is spawned here: tests that run fake provider executables live in the separate test binary
//! `synthesis/tests/claude_code_transport.rs`, so their child processes never share this binary's file descriptors
//! (for example a just-dropped `controller.lock`) with the controller's resume tests. No paid call is made.

use super::transcript::{OutputPolicy, ToolCapabilities, parse_transcript, provider_condition, terminal_result};
use super::*;
use crate::controller::author::{CANDIDATE_MANIFEST_RULE, CandidateSubmission};
use crate::controller::ledger::{Ledger, Tokens};
use crate::controller::limits::{Limits, Money, SpendPolicy};

fn scratch(name: &str) -> PathBuf {
    let tmp = std::env::var_os("TMPDIR").expect("TMPDIR must name a scratch directory");
    let root = PathBuf::from(tmp).join(format!("r12-{name}-{}", records::random_uuid().unwrap()));
    fs::create_dir_all(&root).unwrap();
    root.canonicalize().unwrap()
}

fn call() -> Call {
    Call { id: 1, iteration: 1, attempt: 1, started_unix_ms: 0, reservation_usd: Money::parse("1").unwrap(), receipt: None, provider_session: None, resumes_provider_session: false, usage_in_resumed_session: false }
}

fn limits(timeout_seconds: u64) -> Limits {
    Limits {
        max_iterations: 2,
        max_cost_usd: Money::parse("1").unwrap(),
        spend_policy: SpendPolicy::EstimatedUsd,
        max_retries_per_iteration: 1,
        max_author_tool_turns: 0,
        author_timeout_seconds: timeout_seconds,
    }
}

fn local_tool_names() -> Vec<String> {
    ["check", "verify", "compile", "trial", "profile"].map(|tool| format!("mcp__gendb_local__{tool}")).into()
}

fn transcript(subtype: &str, output: Value) -> String {
    format!(
        "{}\n{}\n",
        json!({"type":"system","subtype":"init","session_id":"s","model":DEFAULT_MODEL}),
        json!({"type":"result","subtype":subtype,"session_id":"s","total_cost_usd":0.125,"modelUsage":{DEFAULT_MODEL:{"inputTokens":10,"outputTokens":20,"cacheReadInputTokens":30,"cacheCreationInputTokens":40,"costBasis":"list"}},"structured_output":output})
    )
}

fn parse(transcript: &str, success: bool, workspace: &Path) -> Receipt {
    let output = if success { OutputPolicy::AcceptAfterSuccessfulExit { workspace } } else { OutputPolicy::Refuse };
    parse_transcript(&call(), "s", AuthorModel::default(), transcript, output).unwrap()
}

#[test]
fn paid_schema_failure_and_error_costs_survive() {
    let workspace = scratch("paid-schema");
    let r = parse(&transcript("success", json!({"action":"final"})), true, &workspace);
    assert!(r.output.is_none());
    assert!(r.outcome.starts_with("schema_error: structured output"), "{}", r.outcome);
    assert_eq!(r.provider_cost().unwrap().decimal(), "0.125");
    for subtype in ["error_max_budget_usd", "error_during_execution"] {
        let r = parse(&transcript(subtype, Value::Null), false, &workspace);
        assert_eq!((r.tokens.as_ref().unwrap().output, r.provider_cost().unwrap().decimal()), (20, "0.125".into()));
        assert_eq!(r.outcome, subtype);
    }
}

#[test]
fn cost_parser_is_exact_and_independent_of_token_metadata() {
    let workspace = scratch("cost-parser");
    for success in [false, true] {
        for subtype in ["success", "error_during_execution", "error_max_turns"] {
            for metadata in [
                Value::Null,
                json!({}),
                json!({DEFAULT_MODEL:{"inputTokens":10}}),
                json!({DEFAULT_MODEL:{"inputTokens":10,"outputTokens":20,"cacheReadInputTokens":30,"cacheCreationInputTokens":40,"costBasis":"unknown"}}),
            ] {
                let mut event = json!({"type":"result","session_id":"s","subtype":subtype,"modelUsage":metadata});
                // A numeric literal must survive JSON parsing without f64 rounding.
                event["total_cost_usd"] = serde_json::from_str("0.123456789012345678").unwrap();
                let r = parse(&event.to_string(), success, &workspace);
                assert_eq!(r.provider_cost().unwrap().decimal(), "0.123456789012345678");
                assert_eq!(r.raw_result, Some(event));
                assert!(r.output.is_none());
                let encoded = json!(r);
                assert_eq!(encoded["provider_reported_cost_usd"], "0.123456789012345678");
                assert!(encoded.get("estimated_cost_usd").is_none());
            }
        }
    }
    for dollars in [Value::Null, json!(-1), json!("NaN"), json!("nonsense")] {
        let event = json!({"type":"result","session_id":"s","total_cost_usd":dollars});
        assert!(parse(&event.to_string(), false, &workspace).provider_cost().is_none());
    }
    assert!(parse(r#"{"type":"result","session_id":"s"}"#, false, &workspace).provider_cost().is_none());
    let zero = r#"{"type":"result","session_id":"s","subtype":"error_during_execution","total_cost_usd":0}"#;
    assert_eq!(parse(zero, false, &workspace).provider_cost(), Some(Money::default()));
    assert!(parse_transcript(&call(), "s", AuthorModel::default(), "", OutputPolicy::Refuse).unwrap_err().contains("result missing"));
}

#[test]
fn cost_parser_does_not_sum_results_or_discard_cost_on_token_overflow() {
    let usage = json!({"inputTokens":u64::MAX,"outputTokens":2,"cacheReadInputTokens":3,"cacheCreationInputTokens":4});
    let result = json!({"type":"result","session_id":"s","subtype":"success","total_cost_usd":"0.3",
        "usage":{"input_tokens":u64::MAX},"modelUsage":{"a":usage,"b":usage}});
    let text = format!("{result}\n{result}\nmalformed trailing event\n");
    let r = parse(&text, true, &scratch("overflow"));
    assert_eq!(r.provider_cost().unwrap().decimal(), "0.3");
    assert!(r.tokens.is_none());
    assert!(r.outcome.starts_with("protocol_error"));
    assert!(r.output.is_none());
    assert_eq!(r.raw_result, Some(result));
}

#[test]
fn schema_example_and_session_identity_are_exact() {
    let workspace = scratch("schema");
    fs::write(workspace.join("candidate.json"), "{}").unwrap();
    let candidate = CandidateSubmission {
        candidate_manifest: "candidate.json".into(),
        rationale: "reason".into(),
        data_access_analysis: "analysis".into(),
    };
    let r = parse(&transcript("success", json!(candidate)), true, &workspace);
    assert_eq!((r.outcome.as_str(), r.output), ("success", Some(json!(candidate))));
    let mismatch = parse_transcript(
        &call(),
        "different",
        AuthorModel::default(),
        &transcript("success", json!(candidate)),
        OutputPolicy::AcceptAfterSuccessfulExit { workspace: &workspace },
    )
    .unwrap();
    assert!(mismatch.output.is_none());
    assert_eq!(mismatch.provider_cost().unwrap().decimal(), "0.125");
    assert!(mismatch.outcome.starts_with("protocol_error"));
    let wrong_model = transcript("success", json!(candidate)).replace(DEFAULT_MODEL, "claude-sonnet-5");
    let r = parse(&wrong_model, true, &workspace);
    assert_eq!(r.outcome, "protocol_error: Claude did not select the requested model");
    assert!(r.output.is_none());
    // A session of another selected model accepts only that model's init; the default is then another model.
    let accept = || OutputPolicy::AcceptAfterSuccessfulExit { workspace: &workspace };
    let sonnet = transcript("success", json!(candidate)).replace(DEFAULT_MODEL, AuthorModel::Sonnet55.id());
    let r = parse_transcript(&call(), "s", AuthorModel::Sonnet55, &sonnet, accept()).unwrap();
    assert_eq!(r.outcome, "success");
    let usage = model_usage_record(r.raw_result.as_ref().unwrap(), AuthorModel::Sonnet55);
    assert_eq!((usage["pinned_model"].clone(), usage["other_models"].clone()), (json!("claude-sonnet-5-5"), json!([])));
    let r = parse_transcript(&call(), "s", AuthorModel::Sonnet55, &transcript("success", json!(candidate)), accept()).unwrap();
    assert_eq!(r.outcome, "protocol_error: Claude did not select the requested model");
}

/// the author passed absolute in-workspace paths to every local tool and to the final
/// submission, which was refused.
#[test]
fn final_manifest_uses_local_tool_path_rule_with_field_specific_errors() {
    let base = scratch("manifest-contract");
    let workspace = base.join("query-0000/author");
    fs::create_dir_all(workspace.join("c2")).unwrap();
    fs::write(workspace.join("c2/candidate.json"), "{}").unwrap();
    fs::create_dir_all(base.join("saved/frozen")).unwrap();
    fs::write(base.join("saved/frozen/candidate.json"), "{}").unwrap();
    let workspace = workspace.canonicalize().unwrap();
    let submit = |manifest: &str, rationale: &str| {
        let output = json!({"candidate_manifest":manifest,"rationale":rationale,"data_access_analysis":"columns"});
        parse(&transcript("success", output), true, &workspace)
    };
    let absolute = workspace.join("c2/candidate.json");
    for manifest in [absolute.to_str().unwrap(), "c2/candidate.json", "c2/../c2/candidate.json"] {
        let r = submit(manifest, "reason");
        assert_eq!(r.outcome, "success", "{manifest}");
        assert_eq!(r.output.unwrap()["candidate_manifest"], "c2/candidate.json");
    }
    let outside = base.join("saved/frozen/candidate.json");
    for (manifest, reason) in [
        (outside.to_str().unwrap(), "inside the author workspace"),
        ("../../saved/frozen/candidate.json", "inside the author workspace"),
        ("c9/candidate.json", "No such file"),
    ] {
        let r = submit(manifest, "reason");
        assert!(r.output.is_none());
        assert!(r.outcome.starts_with(&format!("schema_error: candidate_manifest: {manifest} refused: ")), "{}", r.outcome);
        assert!(r.outcome.contains(reason) && r.outcome.contains(CANDIDATE_MANIFEST_RULE));
        assert!(!r.outcome.contains("rationale:"));
    }
    assert_eq!(submit("c2/candidate.json", " ").outcome, "schema_error: rationale: empty");
    let r = parse(&transcript("success", json!({"candidate_manifest":"c2/candidate.json"})), true, &workspace);
    assert!(r.outcome.starts_with("schema_error: structured output: missing field `rationale`"), "{}", r.outcome);
    assert_eq!(CandidateSubmission::schema()["properties"]["candidate_manifest"]["description"], CANDIDATE_MANIFEST_RULE);
}

#[test]
fn provider_init_capabilities_are_recorded_and_paid_missing_tools_refuse_output() {
    let workspace = scratch("init-capabilities");
    fs::write(workspace.join("candidate.json"), "{}").unwrap();
    let candidate = json!({"candidate_manifest":"candidate.json","rationale":"r","data_access_analysis":"a"});
    let text = transcript("success", candidate);
    let capabilities = ToolCapabilities::observe(&text, &local_tool_names());
    let recorded = json!(capabilities);
    assert_eq!((recorded["init_event_ordinal"].clone(), recorded["missing_required_tools"].as_array().unwrap().len()), (json!(1), 5));
    let mut receipt = parse(&text, true, &workspace);
    assert_eq!(receipt.outcome, "success");
    capabilities.refuse_output_without_required_tools(&mut receipt);
    assert!(receipt.output.is_none());
    assert!(receipt.outcome.contains("call was dispatched"));
    assert_eq!(receipt.provider_cost().unwrap().decimal(), "0.125");
    assert_eq!(receipt.tokens.unwrap().output, 20);
}

/// The terminal results of one resumed Claude Code 2.1.280 session (the first invocation, then the same session
/// resumed), with the observed field structure and numbers; session text, ids and tool lists are synthetic. The first call settles live, the second after its
/// process exit and, separately, after controller loss: every path declares the session scope, so the ledger counts
/// the final cumulative cost once and each invocation's own wall time.
#[test]
fn saved_resumed_session_receipts_declare_session_scope_on_every_settle_path() {
    let saved: Vec<&str> = include_str!("testdata/r1a-resumed-session.jsonl").lines().collect();
    let [first, resumed] = [&saved[0..2], &saved[2..4]].map(|lines| format!("{}\n", lines.join("\n")));
    let session = "00000000-0000-4000-8000-0000000000a1";
    let version = "2.1.280 (Claude Code)";
    let root = scratch("r1a-receipts");
    let workspace = root.join("author");
    fs::create_dir_all(&workspace).unwrap();
    let mut ledger = Ledger::open(&root, json!({"fixture":"r1a"}), Limits { max_cost_usd: Money::parse("30").unwrap(), ..limits(3600) }).unwrap();
    // The saved receipts belong to this provider session.
    ledger.state.session_id = session.into();
    let mut settled = vec![];
    for (text, path) in [(&first, "live"), (&resumed, "process-exit"), (&resumed, "controller-loss")] {
        // The controller-loss copy of the resumed invocation is rebuilt beside the ledger, not settled a second time.
        let call = match path {
            "controller-loss" => Call { id: 3, iteration: 1, attempt: 3, started_unix_ms: 0, reservation_usd: Money::parse("1").unwrap(), receipt: None, provider_session: None, resumes_provider_session: false, usage_in_resumed_session: false },
            _ => ledger.begin_call().unwrap(),
        };
        let call_dir = root.join(format!("calls/{:04}", call.id));
        fs::create_dir_all(&call_dir).unwrap();
        fs::write(call_dir.join("stdout.jsonl"), text).unwrap();
        let invocation = json!({"call":call,"argv":[],"capability":{"transport":"claude_code_cli","executable":"claude","version":version,
            "model":DEFAULT_MODEL,"effort":EFFORT,"persistent_sessions":true,"hard_usd_cap":false,"cost_semantics":COST_SEMANTICS}});
        fs::write(call_dir.join("invocation.json"), invocation.to_string()).unwrap();
        let raw_line: Value = serde_json::from_str(text.lines().nth(1).unwrap()).unwrap();
        let receipt = match path {
            "live" => {
                let mut receipt = parse_transcript(&call, session, AuthorModel::default(), text, OutputPolicy::Refuse).unwrap();
                complete_receipt(&call_dir, &mut receipt, AuthorModel::default(), &[], Some(version), Value::Null);
                // Stands in for the controller-observed wall time of the live invocation.
                receipt.elapsed_ms = raw_line["duration_ms"].as_u64().unwrap();
                receipt
            }
            "process-exit" => {
                fs::write(call_dir.join("process-exit.json"), json!({"success":true,"code":1,"ended_unix_ms":records::now_unix_ms(),
                    "elapsed_ms":raw_line["duration_ms"],"init_capability_abort":null}).to_string()).unwrap();
                recovery::recover_receipt(&call, session, AuthorModel::default(), &call_dir, &workspace).unwrap().unwrap()
            }
            _ => {
                let receipt = recovery::recover_receipt(&call, session, AuthorModel::default(), &call_dir, &workspace).unwrap().unwrap();
                assert_eq!(records::read_json::<Value>(&call_dir.join("controller-loss-recovery.json")).unwrap()["usage_scope"], "session");
                receipt
            }
        };
        assert_eq!(receipt.usage_scope, Some(UsageScope::Session), "{path}");
        assert_eq!(receipt.raw_result.as_ref(), Some(&raw_line), "{path}: raw result unchanged");
        assert_eq!(receipt.elapsed_ms, raw_line["duration_ms"].as_u64().unwrap(), "{path}: per-invocation wall time");
        assert!(call_dir.join("model-usage.json").is_file() && call_dir.join("tool-capabilities.json").is_file());
        settled.push(receipt.clone());
        if path != "controller-loss" {
            ledger.settle(receipt).unwrap();
        }
    }
    let accounting = ledger.accounting(None).unwrap();
    assert_eq!(accounting.provider_reported_cost_usd.unwrap().decimal(), "12.292872199999998");
    assert_eq!(accounting.raw_receipt_sum_usd.decimal(), "23.285546399999998", "summing session totals would double count");
    assert_eq!(accounting.tokens, Some(Tokens { input: 198, output: 179288, cache_read: 26426641, cache_creation: 427624 }));
    assert_eq!(accounting.author_elapsed_ms, 1_359_007 + 93_811);
    assert!(accounting.scope_complete);
    // After a successful exit the output is validated: this worker's result text is prose, not a submission.
    assert_eq!(settled[1].outcome, "schema_error: structured output absent");
    assert_eq!(settled[2].outcome, "controller_loss_recovery: transport_error: successful result without model/init or successful exit");
    // A provider-reported version other than the inspected one voids the declaration.
    assert_eq!(transcript::receipt_usage_scope("2.1.281 (Claude Code)", &first), None);
    assert_eq!(transcript::receipt_usage_scope(version, &first.replace("\"claude_code_version\":\"2.1.280\"", "\"claude_code_version\":\"2.1.281\"")), None);
    // Inspected 2.1.283 declares the same session scope and shell dispatch.
    assert_eq!(transcript::declared_usage_scope("2.1.283 (Claude Code)"), Some(UsageScope::Session));
    assert!(activity::check_shell_version("2.1.283 (Claude Code)").is_ok() && activity::check_shell_version("2.1.282 (Claude Code)").is_err());
    assert_eq!(transcript::declared_usage_scope("2.1.286 (Claude Code)"), Some(UsageScope::Session));
    assert!(activity::check_shell_version("2.1.286 (Claude Code)").is_ok());
}

/// The terminal result of an interrupted worker (Claude Code 2.1.280, with its init event; observed field structure
/// and numbers, synthetic ids and tool lists): `subtype: "success"` with `is_error: true` and an authentication failure text, after
/// which the process exited 1. The provider's `is_error` decides: whichever exit is recorded, the outcome is the
/// provider error with its reason, no submission is accepted, and the reported cost and tokens are kept.
#[test]
fn saved_provider_error_with_success_subtype_is_a_provider_error() {
    let saved = include_str!("testdata/r9-authentication-expired.jsonl");
    let session = "00000000-0000-4000-8000-0000000000b9";
    let workspace = scratch("r9-provider-error");
    for output in [OutputPolicy::Refuse, OutputPolicy::AcceptAfterSuccessfulExit { workspace: &workspace }] {
        let r = parse_transcript(&call(), session, AuthorModel::default(), saved, output).unwrap();
        assert_eq!(
            r.outcome,
            "provider_error: success result with is_error: Failed to authenticate: OAuth session expired and could not be refreshed"
        );
        assert!(r.output.is_none());
        assert_eq!(r.provider_cost().unwrap().decimal(), "5.1297896000000005");
        assert!(r.tokens.is_some_and(|tokens| tokens.output > 0));
        assert_eq!(r.raw_result.as_ref().unwrap()["is_error"], true);
    }
    // Without its token counts the provider error also names the incomplete usage; no counts are invented.
    let without_tokens = saved.replace("\"modelUsage\"", "\"modelUsageRemoved\"");
    let r = parse_transcript(&call(), session, AuthorModel::default(), &without_tokens, OutputPolicy::Refuse).unwrap();
    assert!(r.tokens.is_none() && r.outcome.ends_with("could not be refreshed; incomplete token usage"), "{}", r.outcome);
}

/// A resumed 2.1.286 session first reports a stopped background task as a zero-turn result, then starts a new init for
/// the call's prompt (an observed shape): that earlier result is not a second result of this call; a second result
/// after the last init still is.
#[test]
fn a_zero_turn_result_before_the_resumed_init_is_not_a_second_result() {
    let workspace = scratch("resume-flush");
    let flush = json!({"type":"result","subtype":"success","session_id":"s","num_turns":0,"total_cost_usd":0.1});
    let resumed = format!("{}\n{}\n{}", json!({"type":"system","subtype":"init","session_id":"s","model":DEFAULT_MODEL}), flush, transcript("error_during_execution", Value::Null));
    let r = parse(&resumed, false, &workspace);
    assert!(!r.outcome.starts_with("protocol_error"), "{}", r.outcome);
    assert_eq!(r.provider_cost().unwrap().decimal(), "0.125");
    let twice = format!("{}{}\n", transcript("error_during_execution", Value::Null), flush);
    assert!(parse(&twice, false, &workspace).outcome.starts_with("protocol_error"));
}

/// The actual shape of an observed author call (Claude Code 2.1.286), trimmed: the author started 3
/// sub-agents in the background, its turn ended with a first structured result, their notifications continued the
/// session (a second init), and a second result carried the final submission, both with the same cumulative cost.
/// Live, after the process exit and after controller loss, the call settles with the last result: its submission,
/// its session totals counted once, and the earlier result kept in `superseded-results.json`.
#[test]
fn background_subagent_results_settle_with_the_last_result_on_every_path() {
    let saved = include_str!("testdata/b1-s2-c2-background-subagents.jsonl");
    let [first, last]: [Value; 2] = saved.lines().map(|line| serde_json::from_str::<Value>(line).unwrap()).filter(|event| event["type"] == "result").collect::<Vec<_>>().try_into().unwrap();
    let session = "de7eca39-d247-477a-97e8-d860e084fe59";
    let version = "2.1.286 (Claude Code)";
    let root = scratch("b1-background-subagents");
    let workspace = root.join("author");
    fs::create_dir_all(&workspace).unwrap();
    fs::write(workspace.join("verus-engine.json"), "{}").unwrap();
    let terminal = terminal_result(saved).unwrap();
    assert_eq!((terminal.event.clone(), terminal.superseded.clone(), terminal.refusal), (last.clone(), vec![first.clone()], None));
    let mut ledger = Ledger::open(&root, json!({"fixture":"b1-s2-c2"}), Limits { max_cost_usd: Money::parse("100").unwrap(), ..limits(3600) }).unwrap();
    ledger.state.session_id = session.into();
    for path in ["live", "process-exit", "controller-loss"] {
        let call = match path {
            "live" => ledger.begin_call().unwrap(),
            // The recovered copies are rebuilt beside the ledger, not settled a second time.
            _ => Call { id: if path == "process-exit" { 2 } else { 3 }, ..call() },
        };
        let call_dir = root.join(format!("calls/{:04}", call.id));
        fs::create_dir_all(&call_dir).unwrap();
        fs::write(call_dir.join("stdout.jsonl"), saved).unwrap();
        let invocation = json!({"call":call,"argv":[],"capability":{"transport":"claude_code_cli","executable":"claude","version":version,
            "model":DEFAULT_MODEL,"effort":EFFORT,"persistent_sessions":true,"hard_usd_cap":false,"cost_semantics":COST_SEMANTICS}});
        fs::write(call_dir.join("invocation.json"), invocation.to_string()).unwrap();
        let receipt = match path {
            "live" => {
                let accept = OutputPolicy::AcceptAfterSuccessfulExit { workspace: &workspace };
                let mut receipt = parse_transcript(&call, session, AuthorModel::default(), saved, accept).unwrap();
                complete_receipt(&call_dir, &mut receipt, AuthorModel::default(), &[], Some(version), Value::Null);
                receipt
            }
            "process-exit" => {
                fs::write(call_dir.join("process-exit.json"), json!({"success":true,"code":0,"ended_unix_ms":records::now_unix_ms(),
                    "elapsed_ms":2_764_857,"init_capability_abort":null}).to_string()).unwrap();
                recovery::recover_receipt(&call, session, AuthorModel::default(), &call_dir, &workspace).unwrap().unwrap()
            }
            _ => recovery::recover_receipt(&call, session, AuthorModel::default(), &call_dir, &workspace).unwrap().unwrap(),
        };
        assert_eq!(receipt.raw_result.as_ref(), Some(&last), "{path}: the last result is the terminal one");
        assert_eq!(receipt.provider_cost().unwrap().decimal(), "32.84193659999998", "{path}");
        assert_eq!(receipt.tokens.as_ref().unwrap().output, 438_154, "{path}");
        assert_eq!(receipt.usage_scope, Some(UsageScope::Session), "{path}");
        if path == "controller-loss" {
            assert_eq!(receipt.outcome, "controller_loss_recovery: transport_error: successful result without model/init or successful exit");
            assert!(receipt.output.is_none());
        } else {
            assert_eq!(receipt.outcome, "success", "{path}");
            let rationale = receipt.output.as_ref().unwrap()["rationale"].as_str().unwrap().to_owned();
            assert!(rationale.starts_with("Every training template now runs on the engine path"), "{path}: {rationale}");
        }
        let record: Value = records::read_json(&call_dir.join("superseded-results.json")).unwrap();
        assert_eq!((record["superseded_count"].clone(), record["superseded_results"].clone()), (json!(1), json!([first])), "{path}");
        assert_eq!(record["terminal_result_uuid"], last["uuid"]);
        if path == "live" {
            ledger.settle(receipt).unwrap();
        }
    }
    let accounting = ledger.accounting(None).unwrap();
    assert_eq!(accounting.provider_reported_cost_usd.unwrap().decimal(), "32.84193659999998", "counted once, not per result");
    assert_eq!(accounting.raw_receipt_sum_usd.decimal(), "32.84193659999998");
}

/// Several results stay a protocol error without sub-agents, and a superseded result may not report more cumulative
/// cost than the terminal one. Sub-agents are recognised from the terminal result's `subagent_stats` or from a
/// sub-agent `task_started` event alone.
#[test]
fn several_results_without_subagents_are_still_refused() {
    let saved = include_str!("testdata/b1-s2-c2-background-subagents.jsonl");
    let session = "de7eca39-d247-477a-97e8-d860e084fe59";
    let root = scratch("several-results");
    let workspace = root.join("author");
    fs::create_dir_all(&workspace).unwrap();
    fs::write(workspace.join("verus-engine.json"), "{}").unwrap();
    let rewrite = |keep_task_event: bool, keep_stats: bool, first_cost: Option<&str>| -> String {
        let mut result_index = 0;
        let lines: Vec<String> = saved
            .lines()
            .map(|line| serde_json::from_str::<Value>(line).unwrap())
            .filter(|event| keep_task_event || event["subtype"] != "task_started")
            .map(|mut event| {
                if event["type"] == "result" {
                    if !keep_stats {
                        event.as_object_mut().unwrap().remove("subagent_stats");
                    }
                    if let (0, Some(cost)) = (result_index, first_cost) {
                        event["total_cost_usd"] = serde_json::from_str(cost).unwrap();
                    }
                    result_index += 1;
                }
                event.to_string()
            })
            .collect();
        format!("{}\n", lines.join("\n"))
    };
    let accept = || OutputPolicy::AcceptAfterSuccessfulExit { workspace: &workspace };
    let settle = |text: &str| parse_transcript(&call(), session, AuthorModel::default(), text, accept()).unwrap();
    for (keep_task_event, keep_stats) in [(true, false), (false, true)] {
        assert_eq!(settle(&rewrite(keep_task_event, keep_stats, None)).outcome, "success", "task event {keep_task_event}, stats {keep_stats}");
    }
    let without = rewrite(false, false, None);
    let refused = settle(&without);
    assert_eq!(refused.outcome, "protocol_error: unexpected multiple results in single-input call; final per-invocation totals retained");
    assert!(refused.output.is_none());
    assert_eq!(refused.provider_cost().unwrap().decimal(), "32.84193659999998", "the last result's usage is kept");
    let call_dir = root.join("calls/0001");
    fs::create_dir_all(&call_dir).unwrap();
    fs::write(call_dir.join("stdout.jsonl"), &without).unwrap();
    let mut receipt = refused.clone();
    complete_receipt(&call_dir, &mut receipt, AuthorModel::default(), &[], Some("2.1.286 (Claude Code)"), Value::Null);
    assert!(!call_dir.join("superseded-results.json").exists(), "nothing is superseded");
    fs::write(call_dir.join("invocation.json"), json!({"call":call()}).to_string()).unwrap();
    assert!(recovery::recover_receipt(&call(), session, AuthorModel::default(), &call_dir, &workspace).unwrap().is_none());
    let reason = records::read_json::<Value>(&call_dir.join("controller-loss-recovery-refused.json")).unwrap()["reason"].as_str().unwrap().to_owned();
    assert!(reason.contains("exactly one terminal result event") && reason.contains("found 2 results"), "{reason}");
    let costlier_first = settle(&rewrite(true, true, Some("40.5")));
    assert!(costlier_first.outcome.starts_with("protocol_error: a superseded result reports cumulative cost 40.5"), "{}", costlier_first.outcome);
    assert!(costlier_first.output.is_none());
}

/// Provider conditions come from structural fields of the observed 2.1.286 shapes (a session limit; small
/// synthetic events with the real field structure, redacted text), not from full transcripts.
#[test]
fn provider_conditions_are_classified_from_structural_transcript_fields() {
    use crate::controller::author::ProviderCondition::*;
    let rejected = r#"{"type":"rate_limit_event","rate_limit_info":{"status":"rejected","resetsAt":1791042000,"rateLimitType":"five_hour"}}"#;
    let warning = r#"{"type":"rate_limit_event","rate_limit_info":{"status":"allowed_warning","resetsAt":1791042000,"utilization":0.9}}"#;
    let api_error = |error: &str| format!(r#"{{"type":"assistant","error":"{error}","is_api_error_message":true,"message":{{"content":[]}}}}"#);
    let compaction = |error: &str| format!(r#"{{"type":"system","subtype":"status","status":null,"compact_result":"failed","compact_error":"{error}"}}"#);
    let too_large = compaction("Request too large for the API's 32MB request limit: this conversation is about 58.8MB [redacted]");
    let result = |status: Value, terminal: &str| {
        json!({"type":"result","subtype":"success","is_error":true,"api_error_status":status,"terminal_reason":terminal,"result":"[redacted]"})
    };
    let reset = Some(1_791_042_000_000);
    let limited = format!("{warning}\n{rejected}\n{}\n", api_error("rate_limit"));
    assert_eq!(provider_condition(&result(json!(429), "api_error"), &limited), Some(RateLimited { status: Some(429), resets_at_unix_ms: reset }));
    assert_eq!(provider_condition(&result(json!(429), "api_error"), ""), Some(RateLimited { status: Some(429), resets_at_unix_ms: None }));
    // The limit made automatic compaction fail: still a rate limit with its reset, even beside an invalid_request.
    let compaction_limited = format!("{rejected}\n{}\n{}\n", compaction("You've hit your session limit [redacted]"), api_error("invalid_request"));
    assert_eq!(provider_condition(&result(Value::Null, "blocking_limit"), &compaction_limited), Some(RateLimited { status: None, resets_at_unix_ms: reset }));
    // Exhausted only with the request-size refusal of the compaction and invalid_request.
    let exhausted = format!("{warning}\n{too_large}\n{}\n", api_error("invalid_request"));
    assert_eq!(provider_condition(&result(Value::Null, "blocking_limit"), &exhausted), Some(ContextExhausted));
    // Any other blocking_limit is a retried API error, never a session replacement.
    for other in [api_error("invalid_request"), format!("{}\n{}", compaction("Internal server error"), api_error("invalid_request")), too_large.clone()] {
        assert_eq!(provider_condition(&result(Value::Null, "blocking_limit"), &other), Some(ApiError { status: None }), "{other}");
    }
    assert_eq!(provider_condition(&result(json!(401), "api_error"), ""), Some(AccountRefused { reason: "HTTP 401".into() }));
    let login = api_error("authentication_failed");
    assert_eq!(provider_condition(&result(Value::Null, "api_error"), &login), Some(AccountRefused { reason: "authentication_failed".into() }));
    assert_eq!(provider_condition(&result(json!(529), "api_error"), ""), Some(ApiError { status: Some(529) }));
    // The saved 2.1.280 expired login has no status and no error message: an unclassified API error (backoff).
    let saved = include_str!("testdata/r9-authentication-expired.jsonl");
    let saved_result = saved.lines().map(|line| serde_json::from_str::<Value>(line).unwrap()).find(|event| event["type"] == "result").unwrap();
    assert_eq!(provider_condition(&saved_result, saved), Some(ApiError { status: None }));
    // Not provider conditions: no error, or an author-run error without any API-error evidence.
    let mut not_error = result(json!(429), "api_error");
    not_error["is_error"] = json!(false);
    assert_eq!(provider_condition(&not_error, &limited), None);
    let author_run = json!({"type":"result","subtype":"error_max_structured_output_retries","is_error":true,"terminal_reason":"completed"});
    assert_eq!(provider_condition(&author_run, warning), None);
}
