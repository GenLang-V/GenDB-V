//! Receipts of calls the controller dispatched but did not settle, rebuilt from this transport's durable call records
//! (`AuthorTransport::recover_receipt`). Every rebuilt receipt is completed exactly like a live one
//! (`complete_receipt`): it declares the usage scope of the CLI version recorded in `invocation.json`, so a resumed
//! session's cumulative total is counted once, by increment, on every settle path.
//!
//! - After the process exit (`process-exit.json` exists, no receipt): the transcript is parsed as the live call would
//!   have been (a submission is accepted only after a successful exit), with the exit record's wall time.
//! - After controller loss (`invocation.json` and `stdout.jsonl`, no exit record): the terminal result of this call's
//!   session (the live call's, `transcript::terminal_result`), when it is the stream's last event, settles the call
//!   only when no process of the invocation is alive. Its output is never accepted, because the exit status is
//!   unknown; its wall time is the result's per-invocation `duration_ms`; no exit record is invented.
//!
//! When usage cannot be established, the reason is recorded beside the call and the call stays unresolved (`Ok(None)`):
//! a zero-cost receipt is never inferred. `Err` is reserved for failing to write that evidence.

use super::transcript::{self, OutputPolicy};
use super::{AuthorModel, ProcessExitRecord, complete_receipt, launch, read_transcript};
use crate::controller::author::Capability;
use crate::controller::ledger::{Call, Receipt};
use crate::controller::records;
use serde::Deserialize;
use serde_json::{Value, json};
use std::fs;
use std::os::unix::fs::MetadataExt;
use std::path::Path;

/// Rebuild the receipt of a call of `model`'s session (see the module doc).
pub(super) fn recover_receipt(
    call: &Call,
    session_id: &str,
    model: AuthorModel,
    call_dir: &Path,
    workspace: &Path,
) -> Result<Option<Receipt>, String> {
    if call_dir.join("process-exit.json").exists() {
        let rebuilt = receipt_after_process_exit(call, session_id, model, call_dir, workspace);
        return settle_or_record_refusal(call, call_dir, "process-exit-recovery-refused.json", rebuilt.map(|receipt| (receipt, None)));
    }
    if call_dir.join("invocation.json").exists() && call_dir.join("stdout.jsonl").exists() {
        let rebuilt = receipt_after_controller_loss(call, session_id, model, call_dir);
        return settle_or_record_refusal(call, call_dir, "controller-loss-recovery-refused.json", rebuilt.map(|(receipt, evidence)| (receipt, Some(evidence))));
    }
    Ok(None)
}

fn settle_or_record_refusal(
    call: &Call,
    call_dir: &Path,
    refusal_record: &str,
    rebuilt: Result<(Receipt, Option<Value>), String>,
) -> Result<Option<Receipt>, String> {
    match rebuilt {
        Ok((receipt, evidence)) => {
            if let Some(evidence) = evidence {
                records::write_json_atomic(&call_dir.join(super::CONTROLLER_LOSS_RECOVERY_FILE), &evidence).map_err(|e| e.to_string())?;
            }
            Ok(Some(receipt))
        }
        Err(reason) => {
            records::write_json_atomic(
                &call_dir.join(refusal_record),
                &json!({"call_id":call.id,"reason":reason,"observed_unix_ms":records::now_unix_ms(),
                    "action":"usage stays unresolved; no receipt inferred"}),
            )
            .map_err(|e| e.to_string())?;
            Ok(None)
        }
    }
}

/// The parts of `invocation.json` a recovery needs. Records of every GenDB version carry `call`; `argv` and
/// `capability` may be absent from minimal historical records (no local tools, unknown scope).
#[derive(Deserialize)]
struct RecordedInvocation {
    call: Call,
    #[serde(default)]
    argv: Vec<String>,
    #[serde(default)]
    capability: Option<Capability>,
}

impl RecordedInvocation {
    fn read(call_dir: &Path, call: &Call) -> Result<Self, String> {
        let invocation: Self =
            records::read_json(&call_dir.join("invocation.json")).map_err(|e| format!("invocation record: {}", e.detail))?;
        if invocation.call.id != call.id || invocation.call.iteration != call.iteration {
            return Err("invocation record names a different call".into());
        }
        Ok(invocation)
    }

    fn version(&self) -> Option<&str> {
        self.capability.as_ref().map(|capability| capability.version.as_str())
    }
}

fn receipt_after_process_exit(call: &Call, session_id: &str, model: AuthorModel, call_dir: &Path, workspace: &Path) -> Result<Receipt, String> {
    let exit: ProcessExitRecord = records::read_json(&call_dir.join("process-exit.json")).map_err(|e| e.to_string())?;
    let invocation = RecordedInvocation::read(call_dir, call)?;
    let transcript = read_transcript(call_dir)?;
    let output = if exit.success { OutputPolicy::AcceptAfterSuccessfulExit { workspace } } else { OutputPolicy::Refuse };
    let mut receipt = transcript::parse_transcript(call, session_id, model, &transcript, output)?;
    receipt.elapsed_ms = exit.elapsed_ms;
    receipt.ended_unix_ms = exit.ended_unix_ms;
    let required_tools = launch::allowed_local_tools(&invocation.argv);
    complete_receipt(call_dir, &mut receipt, model, &required_tools, invocation.version(), exit.init_capability_abort);
    Ok(receipt)
}

/// The receipt and `controller-loss-recovery.json` evidence of a call whose controller was lost before the exit record.
fn receipt_after_controller_loss(call: &Call, session_id: &str, model: AuthorModel, call_dir: &Path) -> Result<(Receipt, Value), String> {
    if call_dir.join("receipt.json").exists() || call_dir.join("process-exit.json").exists() {
        return Err("call already has a receipt or exit record".into());
    }
    let invocation = RecordedInvocation::read(call_dir, call)?;
    let stdout = call_dir.join("stdout.jsonl");
    let transcript = fs::read_to_string(&stdout).map_err(|e| format!("provider stream: {e}"))?;
    let terminal = single_terminal_result(&transcript)?;
    if terminal["session_id"].as_str() != Some(session_id) {
        return Err("terminal result belongs to a different session".into());
    }
    let duration_ms = terminal["duration_ms"].as_u64().ok_or("terminal result duration_ms absent")?;
    let holders = invocation_processes(call_dir)?;
    if !holders.is_empty() {
        return Err(format!("invocation processes still alive: {}", json!(holders)));
    }
    let mut receipt = transcript::parse_transcript(call, session_id, model, &transcript, OutputPolicy::Refuse)?;
    if receipt.outcome.starts_with("protocol_error") {
        return Err(format!("provider stream refused: {}", receipt.outcome));
    }
    let cost = receipt.provider_cost().ok_or("terminal result has no provider-reported cost")?;
    let ended_unix_ms = fs::metadata(&stdout)
        .and_then(|metadata| metadata.modified())
        .map_err(|e| e.to_string())?
        .duration_since(std::time::UNIX_EPOCH)
        .map_err(|e| e.to_string())?
        .as_millis() as u64;
    receipt.elapsed_ms = duration_ms;
    receipt.ended_unix_ms = ended_unix_ms;
    let required_tools = launch::allowed_local_tools(&invocation.argv);
    complete_receipt(call_dir, &mut receipt, model, &required_tools, invocation.version(), Value::Null);
    receipt.outcome = format!("controller_loss_recovery: {}", receipt.outcome);
    let evidence = json!({"format_version":1,"kind":"controller_loss_receipt_recovery","call_id":call.id,
        "iteration":call.iteration,"attempt":call.attempt,"session_id":session_id,
        "result_subtype":terminal["subtype"],"terminal_reason":terminal["terminal_reason"],
        "provider_reported_cost_usd":cost,"usage_scope":receipt.usage_scope,"elapsed_ms_source":"terminal result duration_ms",
        "ended_unix_ms":ended_unix_ms,"ended_unix_ms_source":"stdout.jsonl filesystem modification time",
        "liveness":"no process of this user holds stdout.jsonl open or has TMPDIR equal to the call directory",
        "process_exit_record":"absent; controller was lost before writing it and none is fabricated",
        "output_accepted":false,"recorded_unix_ms":records::now_unix_ms()});
    Ok((receipt, evidence))
}

/// The transcript's terminal result (`transcript::terminal_result`, the one the live call settles with), required to
/// be its last event: a stream that continues after its last result, or has none, is incomplete. Earlier results are
/// allowed only as results the terminal one supersedes (after sub-agents); otherwise a second result is refused here.
fn single_terminal_result(transcript: &str) -> Result<Value, String> {
    let last: Option<Value> = transcript.lines().filter(|line| !line.trim().is_empty()).last().and_then(|line| serde_json::from_str(line).ok());
    let terminal = transcript::terminal_result(transcript);
    let results = terminal.as_ref().map_or(0, |terminal| terminal.superseded.len() + 1);
    match (terminal, last) {
        (Some(terminal), Some(last)) if last["type"] == "result" && terminal.refusal.is_none() => Ok(terminal.event),
        (_, last) => Err(format!(
            "provider stream needs exactly one terminal result event, its last event (found {results} results, last type {})",
            last.as_ref().map_or(Value::Null, |last| last["type"].clone())
        )),
    }
}

/// Live processes of this user that belong to the invocation: they hold the call's `stdout.jsonl` open or run with the
/// call directory as `TMPDIR` (both set by `ClaudeCode::invoke` and inherited by every descendant). Reads `/proc`
/// metadata only.
fn invocation_processes(call_dir: &Path) -> Result<Vec<Value>, String> {
    let call_dir = call_dir.canonicalize().map_err(|e| e.to_string())?;
    let stdout = call_dir.join("stdout.jsonl");
    let tmpdir = format!("TMPDIR={}", call_dir.display()).into_bytes();
    // SAFETY: getuid has no preconditions and cannot fail.
    let own_uid = unsafe { libc::getuid() };
    let mut holders = vec![];
    for entry in fs::read_dir("/proc").map_err(|e| format!("process table unavailable: {e}"))? {
        let proc_dir = entry.map_err(|e| e.to_string())?.path();
        let Some(pid) = proc_dir.file_name().and_then(|name| name.to_str()).and_then(|name| name.parse::<u32>().ok()) else {
            continue;
        };
        if !fs::metadata(&proc_dir).is_ok_and(|metadata| metadata.uid() == own_uid) {
            continue;
        }
        if fs::read(proc_dir.join("environ")).is_ok_and(|environ| environ.split(|byte| *byte == 0).any(|variable| variable == tmpdir)) {
            holders.push(json!({"pid":pid,"evidence":"TMPDIR is the call directory"}));
            continue;
        }
        let holds_stdout = fs::read_dir(proc_dir.join("fd"))
            .into_iter()
            .flatten()
            .flatten()
            .any(|descriptor| fs::read_link(descriptor.path()).is_ok_and(|target| target == stdout));
        if holds_stdout {
            holders.push(json!({"pid":pid,"evidence":"holds stdout.jsonl open"}));
        }
    }
    Ok(holders)
}
