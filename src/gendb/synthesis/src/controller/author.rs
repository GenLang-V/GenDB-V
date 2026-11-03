//! The controller's port to an author provider, and the author's submission contract.
//!
//! A transport (the Claude Code session adapter in `synthesis::providers`, or a test fixture) implements
//! [`AuthorTransport`]. The controller owns the ledger and every accounting decision; the transport owns provider
//! processes and its own per-call records, and reports what the provider returned as a [`Receipt`].

use super::ledger::{Call, Receipt};
use super::limits::Limits;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::path::{Component, Path, PathBuf};

/// What a transport can do, recorded in the ledger identity (a resumed run must present the same capability, except
/// for the free-text `cost_semantics`).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Capability {
    pub transport: String,
    pub executable: PathBuf,
    pub version: String,
    pub model: String,
    pub effort: String,
    /// The transport can create a provider session and continue it in later calls (`--session-id`/`--resume`);
    /// required: the controller starts a fresh session per attempt and resumes it after an interruption.
    pub persistent_sessions: bool,
    /// The transport can enforce a hard dollar cap (required by `SpendPolicy::StrictUsd`).
    pub hard_usd_cap: bool,
    /// Human-readable description of the reported cost.
    pub cost_semantics: String,
}

/// Everything one author call needs.
pub struct AuthorCall<'a> {
    pub call: &'a Call,
    /// The call's provider session id (`Ledger::assign_provider_session`).
    pub session_id: &'a str,
    /// Continue the existing provider session (an interrupted call of the same attempt started it) instead of creating it.
    pub resume: bool,
    pub prompt: &'a str,
    pub workspace: &'a Path,
    /// This call's record directory (`RunLayout::call`).
    pub call_dir: &'a Path,
    /// Controls of this session; the transport applies `author_timeout_seconds` to the call.
    pub limits: &'a Limits,
}

pub trait AuthorTransport {
    fn capability(&self) -> Capability;

    /// Cheap local readiness only; never starts an inference process.
    fn preflight(&mut self) -> Result<(), String> {
        Ok(())
    }

    /// The transport only renders each call's inputs for review and never dispatches a provider
    /// (`workload_run::render`). A session with such an author times nothing it would otherwise time before the first
    /// call: a continuing session's incumbent shows its source session's recorded evaluation instead of a fresh one,
    /// marked as such, and that evaluation is never qualified (`controller::run`). Default: a real author.
    fn render_only(&self) -> bool {
        false
    }

    /// True only when the transport's durable ordering proves that no provider process was launched for the call in
    /// `call_dir`. Uncertain partial invocations must answer false so their usage stays unknown.
    fn definitely_not_dispatched(&self, _call_dir: &Path) -> Result<bool, String> {
        Ok(false)
    }

    /// Opt in only when every shell tool has its own activity lease; otherwise the caller keeps a conservative
    /// whole-invocation lease.
    fn tool_activity_lock(&mut self, _path: &Path) -> Result<bool, String> {
        Ok(false)
    }

    /// Configure framework-owned structured tools from the prepared role context. No inference starts and no prompt
    /// text is parsed.
    fn configure_context(&mut self, _context: &Value) -> Result<(), String> {
        Ok(())
    }

    /// Whether the provider session of the call recorded in `call_dir` exists, so a later call can continue it (for
    /// Claude Code: the call's transcript holds the provider's init event). Default: never.
    /// The usage scope of this transport's receipts (`Session`: a resumed session reports its totals so far).
    fn usage_scope(&self) -> Option<crate::controller::ledger::UsageScope> {
        None
    }

    fn provider_session_exists(&self, _call_dir: &Path) -> bool {
        false
    }

    /// Run one provider invocation. Every outcome (including failures after the provider charged) is a receipt; the
    /// receipt carries the provider's reported cost, tokens and their declared `usage_scope`.
    fn invoke(&mut self, call: &AuthorCall) -> Receipt;

    /// Reconstruct the receipt of a call that was dispatched but never settled (the controller stopped), from the
    /// transport's own durable records in `call_dir`. The receipt must declare the same `usage_scope` as a live
    /// invocation of that provider version would. `Ok(None)`: usage cannot be established from durable evidence (the
    /// transport records why); a zero-cost receipt is never inferred.
    fn recover_receipt(&self, _call: &Call, _session_id: &str, _call_dir: &Path, _workspace: &Path) -> Result<Option<Receipt>, String> {
        Ok(None)
    }

    /// The provider condition that ended the settled call recorded in `call_dir` without output, read from the
    /// transport's durable records (so historical receipts classify too). `None`: no recognized provider condition.
    fn provider_condition(&self, _call_dir: &Path, _receipt: &Receipt) -> Option<ProviderCondition> {
        None
    }

    /// Block until the wall clock reaches `until_unix_ms` before the next provider call. It sleeps in slices of at
    /// most a minute against the clock, so a stopped and continued controller does not oversleep and a terminating
    /// signal still ends the process (the wait's record stays durable).
    fn wait_for_provider(&mut self, until_unix_ms: u64) {
        loop {
            let now = super::records::now_unix_ms();
            if now >= until_unix_ms {
                return;
            }
            std::thread::sleep(std::time::Duration::from_millis((until_unix_ms - now).min(60_000)));
        }
    }
}

/// Why the provider ended a call without output, as far as its records say structurally. The controller decides
/// from it whether to wait, to start a fresh provider session, or to stop (`controller::provider_wait`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum ProviderCondition {
    /// A usage or rate limit refused the request (HTTP 429, or the provider's rejected rate-limit event). The
    /// provider's reset time, when it reported one.
    RateLimited { status: Option<u16>, resets_at_unix_ms: Option<u64> },
    /// Any other provider error: HTTP 5xx (including 529 overloaded), a server error, or an error the provider did
    /// not classify further. Retried after a backoff, never in a tight loop.
    ApiError { status: Option<u16> },
    /// The session's conversation can never be sent again (direct evidence: the provider refused its size and
    /// compaction could not reduce it); resuming it fails the same way.
    ContextExhausted,
    /// The provider refused the account (authentication, permission or billing; `reason` names which); retrying
    /// cannot help until the user fixes it.
    AccountRefused { reason: String },
}

/// The rule for `candidate_manifest`, shared by submissions and the author's local tools.
pub const CANDIDATE_MANIFEST_RULE: &str = "candidate_manifest names an existing manifest file inside the author workspace, either workspace-relative (for example c2/verus-query.json, or verus-storages.json for a workload storage submission) or absolute inside that workspace; this is the same rule as the local tools' candidate argument, and GenDB records the normalized workspace-relative path";

/// The author's structured submission. The field names are the provider output schema of saved runs.
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq)]
#[serde(deny_unknown_fields)]
pub struct CandidateSubmission {
    /// Workspace-relative manifest path after `normalize_manifest`.
    pub candidate_manifest: PathBuf,
    pub rationale: String,
    /// The author's analysis of data access and measured bottlenecks; descriptive, not authority.
    pub data_access_analysis: String,
}

impl CandidateSubmission {
    /// JSON schema of the provider's structured output.
    pub fn schema() -> Value {
        json!({"type":"object","additionalProperties":false,"required":["candidate_manifest","rationale","data_access_analysis"],"properties":{
            "candidate_manifest":{"type":"string","minLength":1,"description":CANDIDATE_MANIFEST_RULE},
            "rationale":{"type":"string","minLength":1,"description":"nonempty"},
            "data_access_analysis":{"type":"string","minLength":1,"description":"nonempty"}}})
    }

    /// Syntax of a normalized submission; every failed field is named.
    pub fn validate(&self) -> Result<(), String> {
        let mut failed = vec![];
        let manifest = &self.candidate_manifest;
        if manifest.as_os_str().is_empty() {
            failed.push("candidate_manifest: empty".to_string());
        } else if !is_normal_relative(manifest) {
            failed.push(format!(
                "candidate_manifest: {} is not a normalized workspace-relative path; {CANDIDATE_MANIFEST_RULE}",
                manifest.display()
            ));
        }
        if self.rationale.trim().is_empty() {
            failed.push("rationale: empty".into());
        }
        if self.data_access_analysis.trim().is_empty() {
            failed.push("data_access_analysis: empty".into());
        }
        if failed.is_empty() { Ok(()) } else { Err(failed.join("; ")) }
    }

    /// Resolve the manifest with the workspace containment rule and store its workspace-relative form.
    pub fn normalize_manifest(&mut self, workspace: &Path) -> Result<(), String> {
        let workspace = workspace.canonicalize().map_err(|e| format!("author workspace unavailable: {e}"))?;
        let (_, relative) = resolve_candidate_manifest(&workspace, &self.candidate_manifest).map_err(|e| {
            format!("candidate_manifest: {} refused: {e}; {CANDIDATE_MANIFEST_RULE}", self.candidate_manifest.display())
        })?;
        self.candidate_manifest = relative;
        Ok(())
    }
}

fn is_normal_relative(path: &Path) -> bool {
    !path.is_absolute() && path.components().all(|part| matches!(part, Component::Normal(_)))
}

/// Resolve `input` (workspace-relative or absolute) to an existing file strictly inside the canonical `workspace`:
/// `(absolute path, normalized workspace-relative path)`.
pub fn resolve_candidate_manifest(workspace: &Path, input: &Path) -> Result<(PathBuf, PathBuf), String> {
    let joined = if input.is_absolute() { input.to_path_buf() } else { workspace.join(input) };
    let candidate = joined.canonicalize().map_err(|e| e.to_string())?;
    if !candidate.starts_with(workspace) || candidate == workspace {
        return Err("candidate must be inside the author workspace".into());
    }
    let relative = candidate.strip_prefix(workspace).map_err(|e| e.to_string())?.to_path_buf();
    if !is_normal_relative(&relative) {
        return Err("candidate path must be a normal workspace-relative path".into());
    }
    Ok((candidate, relative))
}
