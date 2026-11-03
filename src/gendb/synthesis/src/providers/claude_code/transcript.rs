//! Reading one invocation's Claude Code `stream-json` transcript (`stdout.jsonl`): the provider's `system/init`
//! event and its terminal `result` event, turned into the controller's [`Receipt`].
//!
//! One prompt yields one result, except after background sub-agents: their completion notifications can continue the
//! session after its first result, and the CLI then emits a further result (observed with 2.1.286:
//! two `success` results with structured output and the same cumulative
//! `total_cost_usd`). The last result is then the
//! terminal one and supersedes the earlier ones ([`terminal_result`]); they stay in `superseded-results.json`.
//!
//! Field scopes of a Claude Code 2.1.280 terminal result (observed in an actual resumed
//! session): `total_cost_usd`, `modelUsage` (tokens and `costUSD`) and `duration_api_ms` are totals of the session so far;
//! `duration_ms` and the top-level `usage` cover this invocation. A receipt's cost is `total_cost_usd` and its tokens
//! are summed over `modelUsage`, so both counted fields share one declared scope ([`declared_usage_scope`]). The raw
//! result is retained unchanged, per-invocation fields included.

use super::{AuthorModel, EFFORT};
use crate::controller::author::{CandidateSubmission, ProviderCondition};
use crate::controller::ledger::{Call, Receipt, Tokens, UsageScope, reported_total_cost};
use crate::controller::records;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::BTreeSet;
use std::path::Path;

/// The declared scope of `total_cost_usd` and `modelUsage` for an inspected Claude Code version; `None` (unknown) for
/// any other version. 2.1.280 reports the session's totals so far, also after `--resume` (observed:
/// 10.9926742 then 12.2928722 dollars in one resumed session; earlier 4.6966946, 5.0170764, 5.2680666 dollars and
/// 88,212, 90,190, 91,854 output tokens after processes of 46, 4 and 3 turns). Scope is never inferred from
/// magnitudes: 2.1.273 once restarted its total across a resume and was not inspected further, so it stays unknown.
/// 2.1.283 also reports session totals after `--resume` (observed: a resumed call's `modelUsage` output tokens 263 =
/// 83 of the first call + its own `usage` 180; cost 0.0695082 then 0.0782842 dollars). 2.1.286 likewise (observed:
/// 247 = 83 + 164; cost 0.0702544 then 0.0789442 dollars).
pub fn declared_usage_scope(version: &str) -> Option<UsageScope> {
    match version.split_whitespace().next() {
        Some("2.1.280" | "2.1.283" | "2.1.286") => Some(UsageScope::Session),
        _ => None,
    }
}

/// The scope a receipt of this transcript declares: the scope of the inspected version that launched it, unless the
/// provider's own init event reports another Claude Code version (the declaration then does not apply: unknown).
pub(super) fn receipt_usage_scope(inspected_version: &str, transcript: &str) -> Option<UsageScope> {
    let reported = init_event(transcript).and_then(|(_, init)| init["claude_code_version"].as_str().map(str::to_owned));
    match reported {
        Some(reported) if Some(reported.as_str()) != inspected_version.split_whitespace().next() => None,
        _ => declared_usage_scope(inspected_version),
    }
}

fn events(transcript: &str) -> impl Iterator<Item = &str> {
    transcript.lines().filter(|line| !line.trim().is_empty())
}

/// The first `system/init` event: its 1-based position among the transcript's events, and the event.
pub(super) fn init_event(transcript: &str) -> Option<(usize, Value)> {
    events(transcript).enumerate().find_map(|(index, line)| {
        let event: Value = serde_json::from_str(line).ok()?;
        is_init(&event).then_some((index + 1, event))
    })
}

fn missing_tools(init: &Value, required: &[String]) -> Vec<String> {
    let visible: BTreeSet<&str> = init["tools"].as_array().into_iter().flatten().filter_map(Value::as_str).collect();
    required.iter().filter(|name| !visible.contains(name.as_str())).cloned().collect()
}

/// Why an init event disqualifies the call before its paid work: another model, another session, or required local
/// tools the provider does not offer. `None`: the call may proceed.
pub(super) fn init_refusal(init: &Value, session_id: &str, model: AuthorModel, required_tools: &[String]) -> Option<String> {
    if init["model"].as_str() != Some(model.id()) {
        return Some(format!("provider init selected model {}, not the pinned author model {}", init["model"], model.id()));
    }
    if init["session_id"].as_str() != Some(session_id) {
        return Some(format!("provider init names session {}, not {session_id}", init["session_id"]));
    }
    let missing = missing_tools(init, required_tools);
    (!missing.is_empty()).then(|| format!("provider init missing required local tools [{}]", missing.join(",")))
}

/// What the provider's init event offered one call against the local tools it requires (`tool-capabilities.json`,
/// format 1). A connected MCP server that offers none of its tools has been observed.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub(super) struct ToolCapabilities {
    format_version: u32,
    source: String,
    init_event_ordinal: Option<usize>,
    visible_tools: Vec<Value>,
    required_tools: Vec<String>,
    missing_required_tools: Vec<String>,
    mcp_servers: Value,
    capabilities_complete: bool,
    /// The supervision's stop at a disqualifying init event, or null.
    #[serde(default)]
    pub init_capability_abort: Value,
}

impl ToolCapabilities {
    pub fn observe(transcript: &str, required_tools: &[String]) -> Self {
        let init = init_event(transcript);
        let event = init.as_ref().map(|(_, event)| event);
        let missing = match event {
            Some(event) => missing_tools(event, required_tools),
            None => required_tools.to_vec(),
        };
        Self {
            format_version: 1,
            source: "provider_system_init".into(),
            init_event_ordinal: init.as_ref().map(|(ordinal, _)| *ordinal),
            visible_tools: event.and_then(|event| event["tools"].as_array().cloned()).unwrap_or_default(),
            required_tools: required_tools.to_vec(),
            capabilities_complete: missing.is_empty() && init.is_some(),
            missing_required_tools: missing,
            mcp_servers: event.map(|event| event["mcp_servers"].clone()).unwrap_or(Value::Null),
            init_capability_abort: Value::Null,
        }
    }

    /// A paid call whose provider lacked a required local tool yields no submission; its usage stays counted.
    pub fn refuse_output_without_required_tools(&self, receipt: &mut Receipt) {
        if self.missing_required_tools.is_empty() {
            return;
        }
        receipt.output = None;
        receipt.outcome = format!(
            "unsupported_capability: provider init missing required local tools [{}]; call was dispatched and provider usage is retained",
            self.missing_required_tools.join(",")
        );
    }
}

/// Whether a terminal result's structured output may become a submission.
pub(super) enum OutputPolicy<'a> {
    /// The provider process exited successfully: validate the output, resolving its manifest inside `workspace`.
    AcceptAfterSuccessfulExit { workspace: &'a Path },
    /// The exit failed or is unknown: the result's usage is kept, its output is never accepted.
    Refuse,
}

/// The terminal result of one invocation's transcript and the earlier results it supersedes.
pub(super) struct TerminalResult {
    /// The last result of this invocation: its usage settles the call and its output may become the submission.
    pub event: Value,
    /// Earlier results of this invocation, in transcript order, unchanged.
    pub superseded: Vec<Value>,
    /// Why the earlier results may not be superseded (a protocol error), or `None`.
    pub refusal: Option<String>,
}

/// The terminal result of the transcript's well-formed events (`None`: no result). On `--resume` after a session that
/// ended with a stopped background task, Claude Code 2.1.286 first reports that notification as a result with zero
/// turns, then starts a new init for this call's prompt (observed): such a zero-turn
/// result before a later init closes the earlier segment and is not a result of this prompt.
pub(super) fn terminal_result(transcript: &str) -> Option<TerminalResult> {
    let parsed: Vec<Value> = events(transcript).filter_map(|line| serde_json::from_str(line).ok()).collect();
    select_terminal_result(&parsed)
}

fn is_init(event: &Value) -> bool {
    event["type"] == "system" && event["subtype"] == "init"
}

fn select_terminal_result(events: &[Value]) -> Option<TerminalResult> {
    let last_init = events.iter().rposition(is_init);
    let mut results: Vec<Value> = events
        .iter()
        .enumerate()
        .filter(|(index, event)| event["type"] == "result" && !(event["num_turns"] == 0 && last_init.is_some_and(|last| *index < last)))
        .map(|(_, event)| event.clone())
        .collect();
    let event = results.pop()?;
    let refusal = if results.is_empty() { None } else { supersession_refusal(&results, &event, events) };
    Some(TerminalResult { event, superseded: results, refusal })
}

/// Why the `earlier` results of an invocation may not be superseded by its `terminal` result, or `None` when they may.
/// They may only after the invocation ran sub-agents (see the module doc), when every earlier result names the same
/// session and none reports a larger cumulative cost than the terminal result: the receipt counts the terminal
/// result's session totals once, so nothing an earlier result reported is lost or counted twice. Without sub-agents a
/// second result stays a protocol error.
fn supersession_refusal(earlier: &[Value], terminal: &Value, events: &[Value]) -> Option<String> {
    if !ran_subagents(terminal, events) {
        return Some("unexpected multiple results in single-input call; final per-invocation totals retained".into());
    }
    let terminal_cost = reported_total_cost(terminal);
    earlier.iter().find_map(|result| {
        if result["session_id"] != terminal["session_id"] {
            return Some("a superseded result names another session".into());
        }
        match (reported_total_cost(result), terminal_cost) {
            (Some(earlier), Some(last)) if earlier > last => Some(format!(
                "a superseded result reports cumulative cost {} above the terminal result's {}",
                earlier.decimal(),
                last.decimal()
            )),
            _ => None,
        }
    })
}

/// Whether the invocation ran sub-agents: its terminal result counts spawned ones (`subagent_stats.spawned`), or the
/// transcript shows one starting (`system/task_started` with `task_type: "local_agent"`).
fn ran_subagents(terminal: &Value, events: &[Value]) -> bool {
    terminal["subagent_stats"]["spawned"].as_u64().is_some_and(|spawned| spawned > 0)
        || events.iter().any(|event| event["type"] == "system" && event["subtype"] == "task_started" && event["task_type"] == "local_agent")
}

/// `superseded-results.json` (format 1) of a transcript whose terminal result superseded earlier ones; `None` when it
/// has a single result or the earlier ones were refused.
pub(super) fn superseded_results_record(transcript: &str) -> Option<Value> {
    let terminal = terminal_result(transcript).filter(|terminal| !terminal.superseded.is_empty() && terminal.refusal.is_none())?;
    Some(json!({"format_version":1,"superseded_count":terminal.superseded.len(),
        "terminal_result_uuid":terminal.event["uuid"],"terminal_result_index":terminal.event["result_index"],
        "rule":"the call ran sub-agents and their notifications continued the session after an earlier result: the last result is the terminal one (its structured output is the submission, its cumulative session totals the call's usage); the earlier results below are retained unchanged and not counted",
        "superseded_results":terminal.superseded}))
}

/// The receipt of one invocation's transcript, launched with `model`: the terminal result's reported cost, `modelUsage`
/// tokens and subtype,
/// its raw event, and a validated submission when `output` allows one. The caller sets wall time and the declared
/// usage scope. `Err` only when the transcript has no terminal result: usage then cannot be established from it.
///
/// The terminal result is the last result of this prompt ([`terminal_result`]). A malformed event, a second result
/// that may not be superseded, or an init or result naming another session or model is a `protocol_error` outcome; a
/// result the provider marks `is_error` is a `provider_error` outcome with its reason; the last result's usage is
/// still kept either way.
pub(super) fn parse_transcript(
    call: &Call,
    session_id: &str,
    model: AuthorModel,
    transcript: &str,
    output: OutputPolicy,
) -> Result<Receipt, String> {
    let mut init_seen = false;
    let mut protocol_error = None;
    let mut parsed = Vec::new();
    for line in events(transcript) {
        match serde_json::from_str::<Value>(line) {
            Ok(event) => parsed.push(event),
            Err(e) => protocol_error = Some(format!("invalid Claude event: {e}")),
        }
    }
    for init in parsed.iter().filter(|event| is_init(event)) {
        if init["session_id"].as_str() != Some(session_id) {
            protocol_error = Some("Claude changed session identity".into());
        }
        if init["model"].as_str() != Some(model.id()) {
            protocol_error = Some("Claude did not select the requested model".into());
        }
        init_seen = true;
    }
    let terminal = select_terminal_result(&parsed).ok_or("Claude final usage/result missing")?;
    if let Some(refusal) = terminal.refusal {
        protocol_error = Some(refusal);
    }
    let result = terminal.event;
    if result["session_id"].as_str() != Some(session_id) {
        protocol_error = Some("Claude result session mismatch".into());
    }
    let subtype = result["subtype"].as_str().unwrap_or("unknown_result");
    let tokens = model_usage_tokens(&result);
    let mut receipt = Receipt {
        call_id: call.id,
        session_id: session_id.into(),
        ended_unix_ms: records::now_unix_ms(),
        elapsed_ms: 0,
        reported_cost_usd: reported_total_cost(&result),
        billed_cost_usd: None,
        tokens: tokens.clone(),
        outcome: String::new(),
        raw_result: Some(result.clone()),
        output: None,
        usage_scope: None,
    };
    receipt.outcome = match (protocol_error, provider_error(&result)) {
        (Some(error), _) => format!("protocol_error: {error}"),
        (None, Some(reason)) => format!("provider_error: {reason}"),
        (None, None) => match output {
            OutputPolicy::AcceptAfterSuccessfulExit { workspace } if subtype == "success" && init_seen => {
                match validated_submission(&result, workspace) {
                    Ok(submission) => {
                        receipt.output = Some(json!(submission));
                        "success".into()
                    }
                    Err(e) => format!("schema_error: {e}"),
                }
            }
            _ if subtype == "success" => "transport_error: successful result without model/init or successful exit".into(),
            _ => subtype.into(),
        },
    };
    // An accepted submission keeps the outcome `success`; its missing token counts stay visible as `tokens: None`,
    // which the ledger reports as incomplete token accounting. Every other outcome names it.
    if tokens.is_none() && receipt.output.is_none() {
        receipt.outcome.push_str("; incomplete token usage");
    }
    Ok(receipt)
}

/// The provider's own failure verdict: a terminal result with `is_error: true`, whatever its `subtype` (Claude Code
/// 2.1.280 reported an expired login as `subtype: "success"`, `is_error: true`, with exit code 1). Its text is the
/// provider's reason; such a result is never a submission.
fn provider_error(result: &Value) -> Option<String> {
    if result["is_error"].as_bool() != Some(true) {
        return None;
    }
    let subtype = result["subtype"].as_str().unwrap_or("unknown_result");
    Some(match result["result"].as_str() {
        Some(reason) if !reason.trim().is_empty() => format!("{subtype} result with is_error: {reason}"),
        _ => format!("{subtype} result with is_error"),
    })
}

/// The provider condition behind a terminal result marked `is_error`, from this invocation's transcript: the result's
/// `api_error_status` and `terminal_reason`, the last `rate_limit_event`, the `error` of the provider's synthetic
/// API-error message (`is_api_error_message`; the Agent SDK declares `authentication_failed`, `billing_error`,
/// `rate_limit`, `invalid_request`, `server_error`, `unknown`, `max_output_tokens`; `rate_limit` and `invalid_request`
/// are observed here) and the last automatic-compaction status (`system/status` with `compact_result`).
///
/// In order:
/// - a rejected rate-limit event, HTTP 429 or error `rate_limit` is a rate limit, with the event's `resetsAt` (unix
///   seconds). This includes a compaction that failed because of the limit (observed with 2.1.286:
///   `terminal_reason: "blocking_limit"`, `api_error_status: null` after the rejected event): after the reset
///   compaction can work;
/// - HTTP 401/403, `authentication_failed` or `billing_error` is a refused account;
/// - the context is exhausted only on direct evidence that the conversation can never be sent again:
///   `terminal_reason: "blocking_limit"`, error `invalid_request`, and a failed compaction whose `compact_error` is the
///   provider's request-size refusal ("Request too large ...", observed at 58.8 MB to 179 MB against the 32 MB limit);
/// - every other provider API error (an HTTP status, a synthetic API-error message, or `terminal_reason` `api_error` or
///   `blocking_limit`: 5xx, `server_error`, any other `blocking_limit`, an unclassified API error such as the 2.1.280
///   expired login saved without its error message) is an API error, retried after a backoff, never in a tight loop.
///
/// Other `is_error` results (for example the author's run ending in a structured-output error) are not provider
/// conditions: the next call gets the full prompt with their feedback, as before.
pub(super) fn provider_condition(raw_result: &Value, transcript: &str) -> Option<ProviderCondition> {
    if raw_result["is_error"].as_bool() != Some(true) {
        return None;
    }
    let status = raw_result["api_error_status"].as_u64().and_then(|status| u16::try_from(status).ok());
    let mut last_rate_limit = None;
    let mut api_error = None;
    let mut last_compaction = None;
    let candidates =
        events(transcript).filter(|line| ["rate_limit_event", "is_api_error_message", "compact_result"].iter().any(|key| line.contains(key)));
    for event in candidates.filter_map(|line| serde_json::from_str::<Value>(line).ok()) {
        if event["type"] == "rate_limit_event" {
            last_rate_limit = Some(event);
        } else if event["type"] == "assistant" && event["is_api_error_message"] == true {
            api_error = event["error"].as_str().map(str::to_owned);
        } else if event["type"] == "system" && event["compact_result"].is_string() {
            last_compaction = Some(event);
        }
    }
    let rejected = last_rate_limit.filter(|event| event["rate_limit_info"]["status"] == "rejected");
    if rejected.is_some() || status == Some(429) || api_error.as_deref() == Some("rate_limit") {
        let resets_at_unix_ms = rejected.and_then(|event| event["rate_limit_info"]["resetsAt"].as_u64()).and_then(|seconds| seconds.checked_mul(1000));
        return Some(ProviderCondition::RateLimited { status, resets_at_unix_ms });
    }
    let request_too_large = last_compaction.is_some_and(|event| {
        event["compact_result"] == "failed" && event["compact_error"].as_str().is_some_and(|error| error.starts_with("Request too large"))
    });
    match (status, api_error.as_deref()) {
        (Some(status @ (401 | 403)), _) => Some(ProviderCondition::AccountRefused { reason: format!("HTTP {status}") }),
        (_, Some(reason @ ("authentication_failed" | "billing_error"))) => Some(ProviderCondition::AccountRefused { reason: reason.into() }),
        (_, Some("invalid_request")) if raw_result["terminal_reason"] == "blocking_limit" && request_too_large => {
            Some(ProviderCondition::ContextExhausted)
        }
        _ if status.is_some() || api_error.is_some() || matches!(raw_result["terminal_reason"].as_str(), Some("api_error" | "blocking_limit")) => {
            Some(ProviderCondition::ApiError { status })
        }
        _ => None,
    }
}

/// Token totals over every model of `modelUsage`; `None` when it is absent, empty, lacks a counter or overflows.
fn model_usage_tokens(result: &Value) -> Option<Tokens> {
    let models = result["modelUsage"].as_object().filter(|models| !models.is_empty())?;
    let mut tokens = Tokens::default();
    let mut complete = true;
    for usage in models.values() {
        let counters = ["inputTokens", "outputTokens", "cacheReadInputTokens", "cacheCreationInputTokens"]
            .map(|key| usage[key].as_u64());
        let [Some(input), Some(output), Some(cache_read), Some(cache_creation)] = counters else {
            complete = false;
            continue;
        };
        for (total, value) in [
            (&mut tokens.input, input),
            (&mut tokens.output, output),
            (&mut tokens.cache_read, cache_read),
            (&mut tokens.cache_creation, cache_creation),
        ] {
            match total.checked_add(value) {
                Some(sum) => *total = sum,
                None => complete = false,
            }
        }
    }
    complete.then_some(tokens)
}

/// The result's structured output (or its `result` text as JSON) as a validated submission whose manifest is
/// normalized inside the workspace. Errors name every failed field.
fn validated_submission(result: &Value, workspace: &Path) -> Result<CandidateSubmission, String> {
    let output = result
        .get("structured_output")
        .cloned()
        .or_else(|| result["result"].as_str().and_then(|text| serde_json::from_str(text).ok()))
        .ok_or("structured output absent")?;
    let mut submission: CandidateSubmission =
        serde_json::from_value(output).map_err(|e| format!("structured output: {e}"))?;
    submission.normalize_manifest(workspace)?;
    submission.validate()?;
    Ok(submission)
}

/// Per-model usage of one terminal result exactly as reported (`model-usage.json`, format 1), with any model other
/// than the session's pinned author `model` named as a finding. Claude Code makes small internal calls (for example session
/// titles); their usage is part of `total_cost_usd` and stays in the receipt's totals: nothing is dropped or
/// re-attributed, and another model is never a synthesis fallback.
pub fn model_usage_record(raw_result: &Value, model: AuthorModel) -> Value {
    let pinned = model.id();
    let usage_by_model = raw_result["modelUsage"].as_object();
    let models: Vec<Value> = usage_by_model
        .into_iter()
        .flatten()
        .map(|(model, usage)| json!({"model":model,"pinned":model == pinned,"usage":usage}))
        .collect();
    let other: Vec<&str> =
        usage_by_model.into_iter().flatten().map(|(model, _)| model.as_str()).filter(|model| *model != pinned).collect();
    json!({"format_version":1,"pinned_model":pinned,"effort":EFFORT,"session_id":raw_result["session_id"],
        "total_cost_usd":raw_result["total_cost_usd"],"models":models,"other_models":other,
        "finding":(!other.is_empty()).then(|| format!("provider receipt lists model(s) {other:?} besides the pinned author model {pinned}: Claude Code internal calls, not a synthesis fallback; their usage is part of total_cost_usd and is retained here per model")),
        "cost_scope":"terminal result of this process as reported by the provider; its scope is the receipt's declared usage_scope"})
}
