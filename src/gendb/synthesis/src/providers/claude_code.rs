//! The Claude Code author transport: one fresh CLI session per attempt (resumed only after an interruption), pinned to one [`AuthorModel`]
//! (the request's `author_model`, default [`DEFAULT_MODEL`]) at [`EFFORT`], with full permissions, the built-in tools, the role's structured local tools (MCP) and per-tool Bash
//! activity leases. The controller chooses each call's provider session (`Ledger::assign_provider_session`): a new
//! attempt creates one (`--session-id`), a retry of an interrupted attempt continues it (`--resume`).
//!
//! One call (`AuthorTransport::invoke`) goes through these steps, each leaving a durable record in the call directory
//! (names are part of the saved-evidence format):
//! 1. `prompt.txt`, empty `stdout.jsonl`/`stderr.txt`, `local-jobs/`, `mcp-config.json`, `author-shell/` (the Bash
//!    guardian, when an activity lock is configured) and `invocation.json` (argv, capability, declared usage scope,
//!    environment policy) are written before the process starts;
//! 2. the CLI runs with the prompt on stdin, its structured event stream in `stdout.jsonl` (the visible transcript of
//!    every model message and tool call) and `TMPDIR` set to the call directory; it is supervised until it exits
//!    (`supervision`);
//! 3. `process-exit.json` records the exit;
//! 4. the transcript's terminal result becomes the receipt (`transcript`); `tool-capabilities.json` and
//!    `model-usage.json` record what the provider offered and reported, and `superseded-results.json` the earlier
//!    results a terminal result superseded after sub-agents.
//!
//! A controller that stops between these steps rebuilds the receipt from the same records (`recovery`). The same
//! records tell the controller why the provider ended a call without output (`AuthorTransport::provider_condition`:
//! rate limit with its reset time, other API error, exhausted context, refused account); waiting is the controller's.
//!
//! Accounting: provider receipts are authoritative. Each receipt keeps the raw terminal result and declares the scope of
//! its cost and tokens from the inspected CLI version (2.1.280, 2.1.283, 2.1.286: session totals, which the ledger counts once, by
//! increment); its wall time is this invocation's. The CLI budget flag is the call's stop-guard reservation, not a hard
//! cap. No dollar price is inferred.

mod activity;
mod inspection;
mod launch;
mod recovery;
mod supervision;
mod transcript;

#[cfg(test)]
mod tests;

pub use inspection::InspectionError;
pub use launch::{LAUNCH_FLAGS, author_session_environment};
pub use transcript::{declared_usage_scope, model_usage_record};

use crate::controller::author::{AuthorCall, AuthorTransport, Capability, ProviderCondition};
use crate::controller::layout::PROMPT_FILE;
use crate::controller::ledger::{Call, Receipt, UsageScope};
use crate::controller::records;
use activity::ActivityShell;
use launch::Launch;
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::fmt;
use std::fs::{self, File, OpenOptions};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus};
use std::time::{Duration, Instant};
use supervision::{InitStop, ProcessEnd, Watch};
use transcript::{OutputPolicy, ToolCapabilities};

/// The default author model (a request without `author_model`).
pub const DEFAULT_MODEL: &str = AuthorModel::Opus55.id();
pub const EFFORT: &str = "high";

/// The author models this transport can pin, selected per run by the request's `author_model` (absent: Opus 5.5).
/// The model is launched by its exact id at [`EFFORT`], serves as the session's helper model, and must be the model the
/// provider's init event names; it is part of the transport capability, so a session never resumes under another
/// model. There is no fallback model. JSON: the model id; any other text is refused when the request is read.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub enum AuthorModel {
    #[default]
    #[serde(rename = "claude-opus-5-5")]
    Opus55,
    #[serde(rename = "claude-sonnet-5-5")]
    Sonnet55,
}

impl AuthorModel {
    /// The provider model id (`--model`, `ANTHROPIC_SMALL_FAST_MODEL`, init event, `Capability::model`).
    pub const fn id(self) -> &'static str {
        match self {
            AuthorModel::Opus55 => "claude-opus-5-5",
            AuthorModel::Sonnet55 => "claude-sonnet-5-5",
        }
    }

    pub fn is_default(&self) -> bool {
        *self == AuthorModel::default()
    }
}

/// `Capability::cost_semantics` of this transport.
pub const COST_SEMANTICS: &str = "Claude Code total_cost_usd and modelUsage: provider-reported actual synthesis cost and tokens of the terminal result; their scope (this invocation or the session so far; 2.1.280, 2.1.283 and 2.1.286: the session so far) is declared per receipt as usage_scope from the inspected CLI version, unknown otherwise; duration_ms and the receipt's elapsed time cover one invocation; the CLI budget is a stop guard, not a strict cap";

/// The record a call directory gets when its receipt is rebuilt after the controller was lost before the call's exit
/// record (`recovery`): the call was stopped from outside, its output is never accepted, and a retry of its attempt
/// resumes its provider session.
pub const CONTROLLER_LOSS_RECOVERY_FILE: &str = "controller-loss-recovery.json";

/// Records of a call directory that exist only once this transport has started working on the call.
const DISPATCH_RECORDS: [&str; 6] =
    ["invocation.json", "stdout.jsonl", "stderr.txt", PROMPT_FILE, "process-exit.json", "author-shell"];

/// How the provider starts the framework's structured local-tool server (stdio MCP) of a call: `program` with
/// `arguments`, followed by the role's tool context and the call's `local-jobs` evidence directory. The composition root
/// supplies it (earlier version: the running binary with `integrated-modular-mcp`).
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct LocalToolServer {
    pub program: PathBuf,
    pub arguments: Vec<String>,
}

/// The local tools a prepared role context declares (`context.local_tools`; other keys there are for the author).
#[derive(Clone, Debug, Deserialize)]
struct LocalTools {
    /// The tool context file the server reads.
    mcp_context: PathBuf,
    /// Full MCP tool names (`mcp__gendb_local__<tool>`) the provider must offer at init.
    required_tools: Vec<String>,
}

/// The Claude Code transport of one author session.
pub struct ClaudeCode {
    executable: PathBuf,
    model: AuthorModel,
    /// `--version` text of the inspected executable.
    version: String,
    inspection: Value,
    local_tool_server: LocalToolServer,
    /// The run's activity lock when every Bash tool call takes its own lease.
    activity_lock: Option<PathBuf>,
    /// Declared by the prepared role context (`configure_context`); `None` = no local tools.
    local_tools: Option<LocalTools>,
    /// The most sub-agents the role allows at once (`context.author_subagents.max_concurrent`); `None` = no sub-agents.
    subagents: Option<u32>,
    /// SHA-256 of the executable's bytes at inspection: the pin every preflight and call checks (no auto-update, no
    /// replaced or removed binary during a run).
    executable_sha256: String,
}

/// SHA-256 (hex) of the file `path` (the author executable, a few hundred MB: read in chunks).
fn file_sha256(path: &Path) -> Result<String, String> {
    use sha2::{Digest, Sha256};
    use std::io::Read;
    let mut file = File::open(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut hasher = Sha256::new();
    let mut buffer = vec![0u8; 1 << 20];
    loop {
        let read = file.read(&mut buffer).map_err(|e| format!("{}: {e}", path.display()))?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    Ok(hasher.finalize().iter().map(|b| format!("{b:02x}")).collect())
}

impl ClaudeCode {
    /// Inspect `executable` read-only (evidence under `evidence_dir`) and create the transport of `model`. No inference
    /// starts.
    pub fn inspect(
        executable: PathBuf,
        model: AuthorModel,
        evidence_dir: &Path,
        local_tool_server: LocalToolServer,
    ) -> Result<Self, InspectionError> {
        let inspected = inspection::inspect(&executable, evidence_dir)?;
        let executable_sha256 = file_sha256(&executable).map_err(|detail| InspectionError::Evidence { path: executable.clone(), detail })?;
        Ok(Self {
            executable,
            model,
            version: inspected.version,
            inspection: inspected.record,
            local_tool_server,
            activity_lock: None,
            local_tools: None,
            subagents: None,
            executable_sha256,
        })
    }

    /// The executable still has the bytes it had at inspection.
    fn check_pinned_executable(&self) -> Result<(), String> {
        let now = file_sha256(&self.executable)?;
        if now != self.executable_sha256 {
            return Err(format!("author executable {} changed since inspection (sha256 {} -> {now}); the pinned CLI must not change during a run", self.executable.display(), self.executable_sha256));
        }
        Ok(())
    }

    fn required_tools(&self) -> &[String] {
        self.local_tools.as_ref().map_or(&[], |tools| tools.required_tools.as_slice())
    }

    /// Write every record the call needs before launch, then start the provider in its own process group.
    fn launch(&self, request: &AuthorCall, call_dir: &Path) -> Result<std::process::Child, InvocationFailure> {
        let prompt = call_dir.join(PROMPT_FILE);
        fs::write(&prompt, request.prompt).map_err(io_failure(&prompt))?;
        let create_output = |name: &str| {
            let path = call_dir.join(name);
            OpenOptions::new().write(true).create_new(true).open(&path).map_err(io_failure(&path))
        };
        let stdout = create_output("stdout.jsonl")?;
        let stderr = create_output("stderr.txt")?;
        let local_jobs = call_dir.join("local-jobs");
        fs::create_dir(&local_jobs).map_err(io_failure(&local_jobs))?;
        let mcp_config = call_dir.join("mcp-config.json");
        let server = self.local_tools.as_ref().map(|tools| (&self.local_tool_server, tools.mcp_context.as_path()));
        records::write_json_atomic(&mcp_config, &launch::mcp_config(server, &local_jobs)).map_err(record_failure)?;
        let subagent_environment = self.subagents.map(|max| launch::subagent_environment(self.model, max)).unwrap_or_default();
        let argv = launch::arguments(&Launch {
            model: self.model,
            subagents: self.subagents.is_some(),
            session_id: request.session_id,
            resume: request.resume,
            stop_guard_usd: request.call.reservation_usd,
            mcp_config: &mcp_config,
            local_tools: self.required_tools(),
        });
        let shell = match &self.activity_lock {
            Some(lock) => Some(
                ActivityShell::install(call_dir, lock, request.limits.author_timeout_seconds).map_err(InvocationFailure::Launch)?,
            ),
            None => None,
        };
        records::write_json_atomic(&call_dir.join("invocation.json"), &InvocationRecord {
            argv: &argv,
            capability: self.capability(),
            capability_inspection: &self.inspection,
            call: request.call,
            usage_scope: declared_usage_scope(&self.version),
            tool_activity: shell.as_ref(),
            session_environment: json!({
                "variables":author_session_environment(self.model).iter().map(|(name, value)| (name.to_string(), json!(value)))
                    .chain(subagent_environment.iter().map(|(name, value)| (name.to_string(), json!(value)))).collect::<serde_json::Map<_, _>>(),
                "policy":"fresh task session: Claude Code auto-memory and auto-updater disabled; inherited authentication and permissions unchanged",
                "executable_sha256":self.executable_sha256}),
        })
        .map_err(record_failure)?;
        let mut command = Command::new(&self.executable);
        command
            .args(&argv)
            .current_dir(request.workspace)
            .stdin(File::open(&prompt).map_err(io_failure(&prompt))?)
            .stdout(stdout)
            .stderr(stderr)
            .env("TMPDIR", call_dir)
            .envs(author_session_environment(self.model))
            .envs(subagent_environment.iter().map(|(name, value)| (*name, value.as_str())))
            .process_group(0);
        if let Some(shell) = &shell {
            command.envs(shell.environment()).env_remove("CLAUDE_CODE_SHELL_PREFIX");
        }
        // The user's stop (`gendb_runtime::process_stop`): SIGINT ends the provider with its terminal result (so the
        // stopped call's usage is recovered on relaunch), whether the controller stops or dies.
        gendb_runtime::process_stop::park_if_stopping();
        gendb_runtime::process_stop::die_with_controller(&mut command, libc::SIGINT);
        command.spawn().map_err(|error| InvocationFailure::Launch(error.to_string()))
    }

    /// Launch, supervise and settle one call. `Err` when the call ended without an exit record and a parsed terminal
    /// result; the caller then keeps whatever usage the transcript shows.
    fn dispatch(&self, request: &AuthorCall, call_dir: &Path, started: Instant) -> Dispatched {
        let mut child = match self.launch(request, call_dir) {
            Ok(child) => child,
            Err(failure) => return Dispatched { result: Err(failure), init_stop: None },
        };
        let owned = gendb_runtime::process_stop::own_group(child.id(), libc::SIGINT, "author provider (its process group)");
        let transcript_path = call_dir.join("stdout.jsonl");
        let supervised = supervision::supervise(&mut child, &Watch {
            transcript: &transcript_path,
            session_id: request.session_id,
            model: self.model,
            required_tools: self.required_tools(),
            wall_guard: Duration::from_secs(request.limits.author_timeout_seconds),
            started,
        });
        // The provider is reaped: its pid is no longer the controller's to signal.
        drop(owned);
        let init_evidence = supervised.init_stop.as_ref().map_or(Value::Null, |stop| stop.evidence.clone());
        let result = match supervised.end {
            ProcessEnd::WallGuardElapsed => Err(InvocationFailure::WallGuardElapsed),
            ProcessEnd::WaitFailed(error) => Err(InvocationFailure::Launch(error.to_string())),
            ProcessEnd::Exited(status) => settle_exit(request, self.model, call_dir, status, started, init_evidence),
        };
        Dispatched { result, init_stop: supervised.init_stop }
    }
}

/// The receipt of a call refused before any provider launch: zero cost, no tokens, no result, no time.
fn predispatch_refusal(request: &AuthorCall, error: &str) -> Receipt {
    Receipt {
        call_id: request.call.id,
        session_id: request.session_id.into(),
        ended_unix_ms: records::now_unix_ms(),
        elapsed_ms: 0,
        reported_cost_usd: Some(crate::controller::limits::Money::default()),
        billed_cost_usd: None,
        tokens: None,
        outcome: format!("{}{error}", crate::controller::ledger::PREDISPATCH_REFUSAL_PREFIX),
        raw_result: None,
        output: None,
        usage_scope: None,
    }
}

/// Record the exit (`process-exit.json`) and parse the transcript's terminal result; a submission is accepted only
/// after a successful exit.
fn settle_exit(
    request: &AuthorCall,
    model: AuthorModel,
    call_dir: &Path,
    status: ExitStatus,
    started: Instant,
    init_capability_abort: Value,
) -> Result<Receipt, InvocationFailure> {
    let exit = ProcessExitRecord {
        success: status.success(),
        code: status.code(),
        ended_unix_ms: records::now_unix_ms(),
        elapsed_ms: started.elapsed().as_millis() as u64,
        init_capability_abort,
    };
    records::write_json_atomic(&call_dir.join("process-exit.json"), &exit)
        .map_err(|error| InvocationFailure::Settle(error.to_string()))?;
    let transcript = read_transcript(call_dir).map_err(InvocationFailure::Settle)?;
    let output = if exit.success {
        OutputPolicy::AcceptAfterSuccessfulExit { workspace: request.workspace }
    } else {
        OutputPolicy::Refuse
    };
    transcript::parse_transcript(request.call, request.session_id, model, &transcript, output).map_err(InvocationFailure::Settle)
}

/// `invocation.json`: what was launched, recorded before launch.
#[derive(Serialize)]
struct InvocationRecord<'a> {
    argv: &'a [String],
    capability: Capability,
    capability_inspection: &'a Value,
    call: &'a Call,
    /// The scope this CLI version declares for its receipts' cost and tokens.
    usage_scope: Option<UsageScope>,
    tool_activity: Option<&'a ActivityShell>,
    session_environment: Value,
}

/// `process-exit.json`: the provider process's exit, as the supervising controller observed it.
#[derive(Serialize, Deserialize)]
struct ProcessExitRecord {
    success: bool,
    code: Option<i32>,
    ended_unix_ms: u64,
    /// Controller-observed wall time of the invocation.
    elapsed_ms: u64,
    #[serde(default)]
    init_capability_abort: Value,
}

/// Why a call ended without a settled terminal result. Display texts are receipt outcomes of saved runs.
#[derive(Debug)]
enum InvocationFailure {
    /// Preparing the call's records, launching or waiting on the process failed.
    Launch(String),
    /// The call's wall guard elapsed; its process group was killed.
    WallGuardElapsed,
    /// The process exited, but its exit record or terminal result could not be settled.
    Settle(String),
}

impl fmt::Display for InvocationFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            InvocationFailure::Launch(detail) | InvocationFailure::Settle(detail) => f.write_str(detail),
            InvocationFailure::WallGuardElapsed => f.write_str("author_timeout; usage remains unknown until reconciled"),
        }
    }
}

fn io_failure(path: &Path) -> impl Fn(std::io::Error) -> InvocationFailure + '_ {
    move |error| InvocationFailure::Launch(format!("{}: {error}", path.display()))
}

fn record_failure(error: records::RecordError) -> InvocationFailure {
    InvocationFailure::Launch(error.to_string())
}

struct Dispatched {
    result: Result<Receipt, InvocationFailure>,
    init_stop: Option<InitStop>,
}

fn read_transcript(call_dir: &Path) -> Result<String, String> {
    let path = call_dir.join("stdout.jsonl");
    fs::read_to_string(&path).map_err(|error| format!("{}: {error}", path.display()))
}

/// The receipt of a call that failed after launch: the transcript's usage when it has a terminal result (its output
/// is never accepted), otherwise a transport error with unknown usage.
fn failed_call_receipt(
    request: &AuthorCall,
    model: AuthorModel,
    call_dir: &Path,
    failure: &InvocationFailure,
    init_stop: Option<&InitStop>,
) -> Receipt {
    let observed = read_transcript(call_dir)
        .ok()
        .and_then(|transcript| transcript::parse_transcript(request.call, request.session_id, model, &transcript, OutputPolicy::Refuse).ok());
    let mut receipt = observed.unwrap_or_else(|| Receipt {
        call_id: request.call.id,
        session_id: request.session_id.into(),
        ended_unix_ms: records::now_unix_ms(),
        elapsed_ms: 0,
        reported_cost_usd: None,
        billed_cost_usd: None,
        tokens: None,
        outcome: String::new(),
        raw_result: None,
        output: None,
        usage_scope: None,
    });
    receipt.outcome = match init_stop {
        // The stream can end without a terminal result after the stop.
        Some(stop) => format!("unsupported_capability: {}; stopped at the provider init event ({failure})", stop.reason),
        None => failure.to_string(),
    };
    receipt.output = None;
    receipt
}

/// Complete a receipt parsed from the call's transcript, identically for live calls and every recovery path: record
/// the provider's tool capabilities (unless already recorded), refuse the output of a call whose provider lacked a
/// required local tool, write `model-usage.json` against the call's pinned `model` (and `superseded-results.json` when
/// the terminal result superseded earlier ones), and declare the usage scope of the CLI `version` that ran the call.
/// These records are evidence beside the receipt, which retains the raw result; a failed evidence write does not change
/// the receipt.
fn complete_receipt(
    call_dir: &Path,
    receipt: &mut Receipt,
    model: AuthorModel,
    required_tools: &[String],
    version: Option<&str>,
    init_stop_evidence: Value,
) {
    let transcript = read_transcript(call_dir).unwrap_or_default();
    let record = call_dir.join("tool-capabilities.json");
    let capabilities = match records::read_json::<ToolCapabilities>(&record) {
        Ok(recorded) => recorded,
        Err(_) => {
            let mut observed = ToolCapabilities::observe(&transcript, required_tools);
            observed.init_capability_abort = init_stop_evidence;
            let _ = records::write_json_atomic(&record, &observed);
            observed
        }
    };
    let Some(raw_result) = &receipt.raw_result else {
        return;
    };
    let _ = records::write_json_atomic(&call_dir.join("model-usage.json"), &model_usage_record(raw_result, model));
    if let Some(superseded) = transcript::superseded_results_record(&transcript) {
        let _ = records::write_json_atomic(&call_dir.join("superseded-results.json"), &superseded);
    }
    receipt.usage_scope = version.and_then(|version| transcript::receipt_usage_scope(version, &transcript));
    capabilities.refuse_output_without_required_tools(receipt);
}

impl AuthorTransport for ClaudeCode {
    fn capability(&self) -> Capability {
        Capability {
            transport: "claude_code_cli".into(),
            executable: self.executable.clone(),
            version: self.version.clone(),
            model: self.model.id().into(),
            effort: EFFORT.into(),
            persistent_sessions: true,
            hard_usd_cap: false,
            cost_semantics: COST_SEMANTICS.into(),
        }
    }

    /// The pinned executable is unchanged (checked by hash; the CLI auto-updater is also disabled for authors).
    fn preflight(&mut self) -> Result<(), String> {
        self.check_pinned_executable()
    }

    /// A call directory without any of this transport's dispatch records was never launched.
    fn definitely_not_dispatched(&self, call_dir: &Path) -> Result<bool, String> {
        for name in DISPATCH_RECORDS {
            match fs::symlink_metadata(call_dir.join(name)) {
                Ok(_) => return Ok(false),
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                Err(error) => return Err(error.to_string()),
            }
        }
        Ok(true)
    }

    /// The call's transcript holds the provider's init event naming its session: the CLI created the session.
    fn usage_scope(&self) -> Option<UsageScope> {
        transcript::declared_usage_scope(&self.version)
    }

    fn provider_session_exists(&self, call_dir: &Path) -> bool {
        read_transcript(call_dir).ok().and_then(|transcript| transcript::init_event(&transcript).map(|(_, init)| init["session_id"].is_string())).unwrap_or(false)
    }

    fn tool_activity_lock(&mut self, path: &Path) -> Result<bool, String> {
        activity::check_shell_version(&self.version)?;
        if !path.is_absolute() {
            return Err("absolute author activity lock required".into());
        }
        activity::check_guardian_support()?;
        self.activity_lock = Some(path.to_owned());
        Ok(true)
    }

    /// Read the role's local-tool declaration: no `local_tools` key means the author has no local tools; a
    /// declaration must name an existing tool context and at least one required tool.
    fn configure_context(&mut self, context: &Value) -> Result<(), String> {
        self.local_tools = None;
        self.subagents = match &context["author_subagents"]["max_concurrent"] {
            Value::Null => None,
            max => Some(max.as_u64().filter(|max| (1..=5).contains(max)).ok_or_else(|| format!("prepared context author_subagents.max_concurrent {max}: expected 1..=5"))? as u32),
        };
        let Some(declared) = context.get("local_tools").filter(|declared| !declared.is_null()) else {
            return Ok(());
        };
        let mut tools: LocalTools =
            serde_json::from_value(declared.clone()).map_err(|e| format!("prepared context local_tools: {e}"))?;
        if tools.required_tools.is_empty() {
            return Err("prepared context lists no required local tools".into());
        }
        tools.mcp_context = tools
            .mcp_context
            .canonicalize()
            .map_err(|e| format!("local tool context {}: {e}", tools.mcp_context.display()))?;
        self.local_tools = Some(tools);
        Ok(())
    }

    fn invoke(&mut self, request: &AuthorCall) -> Receipt {
        if let Err(error) = self.check_pinned_executable() {
            // Refused before anything is written to the call directory: a proven pre-dispatch refusal.
            return predispatch_refusal(request, &error);
        }
        let started = Instant::now();
        let call_dir = match fs::create_dir_all(request.call_dir).and_then(|()| request.call_dir.canonicalize()) {
            Ok(call_dir) => call_dir,
            Err(error) => {
                let failure = InvocationFailure::Launch(format!("{}: {error}", request.call_dir.display()));
                return failed_call_receipt(request, self.model, request.call_dir, &failure, None);
            }
        };
        let Dispatched { result, init_stop } = self.dispatch(request, &call_dir, started);
        let mut receipt = match result {
            Ok(receipt) => receipt,
            Err(failure) => failed_call_receipt(request, self.model, &call_dir, &failure, init_stop.as_ref()),
        };
        let init_evidence = init_stop.map_or(Value::Null, |stop| stop.evidence);
        complete_receipt(&call_dir, &mut receipt, self.model, self.required_tools(), Some(&self.version), init_evidence);
        receipt.ended_unix_ms = records::now_unix_ms();
        receipt.elapsed_ms = started.elapsed().as_millis() as u64;
        receipt
    }

    /// The condition behind a provider error result, from the call's transcript (`transcript::provider_condition`).
    fn provider_condition(&self, call_dir: &Path, receipt: &Receipt) -> Option<ProviderCondition> {
        let raw_result = receipt.raw_result.as_ref()?;
        transcript::provider_condition(raw_result, &read_transcript(call_dir).ok()?)
    }

    /// The call ran under this transport's model: a ledger resumes only with the capability (model included) it
    /// recorded.
    fn recover_receipt(&self, call: &Call, session_id: &str, call_dir: &Path, workspace: &Path) -> Result<Option<Receipt>, String> {
        recovery::recover_receipt(call, session_id, self.model, call_dir, workspace)
    }
}
