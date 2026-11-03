//! The provider command line, environment and MCP configuration of one author call.

use super::{AuthorModel, EFFORT, LocalToolServer};
use crate::controller::author::CandidateSubmission;
use crate::controller::limits::Money;
use serde_json::{Value, json};
use std::path::Path;

/// The author's built-in tools. Claude Code's `--tools` selects built-in tools only; MCP tools are allowed separately.
const BUILTIN_TOOLS: &str = "Read,Write,Edit,Glob,Grep,Bash";

/// The MCP server name of the framework's local tools; tools appear as `mcp__gendb_local__<tool>`.
pub(super) const LOCAL_TOOL_SERVER_NAME: &str = "gendb_local";

/// Every flag a launch can pass. Inspection refuses an executable whose help lacks one, before any run exists. There
/// is no fallback model and no turn cap: `--fallback-model` and `--max-turns` are never passed.
pub const LAUNCH_FLAGS: [&str; 18] = [
    "--print",
    "--verbose",
    "--output-format",
    "--model",
    "--effort",
    "--permission-mode",
    "--allow-dangerously-skip-permissions",
    "--tools",
    "--allowedTools",
    "--disable-slash-commands",
    "--strict-mcp-config",
    "--mcp-config",
    "--setting-sources",
    "--prompt-suggestions",
    "--max-budget-usd",
    "--json-schema",
    "--resume",
    "--session-id",
];

/// Fresh task-session policy for every author process (not an OS restriction), recorded in each `invocation.json`:
/// - Claude Code auto-memory would otherwise load the project memory index of whoever runs the controller into each
///   author session. Inspected Claude Code 2.1.270/2.1.273/2.1.280 read this variable before their default-on
///   `autoMemoryEnabled` setting.
/// - Claude Code makes small internal calls (for example session titles) with its auxiliary "small fast" model, a
///   Haiku model by default. Inspected 2.1.280 selects that model from `ANTHROPIC_SMALL_FAST_MODEL` first, so it is
///   routed to the session's pinned author model; any other model a receipt still lists is recorded as a named finding
///   (`transcript::model_usage_record`), never a fallback and never dropped from the cost.
///
/// - The CLI's auto-updater is disabled (`DISABLE_AUTOUPDATER`): an update during a run replaced the launcher and removed
///   the pinned version's binary (Q15, nm-01). The executable is also pinned by its SHA-256 (`ClaudeCode::preflight`).
///
/// Authentication, permissions and tools are inherited unchanged; no variable value is secret.
pub fn author_session_environment(model: AuthorModel) -> [(&'static str, &'static str); 3] {
    [("CLAUDE_CODE_DISABLE_AUTO_MEMORY", "1"), ("ANTHROPIC_SMALL_FAST_MODEL", model.id()), ("DISABLE_AUTOUPDATER", "1")]
}

/// The built-in tools plus Claude Code's sub-agent tool, when the role allows sub-agents.
const BUILTIN_TOOLS_WITH_SUBAGENTS: &str = "Read,Write,Edit,Glob,Grep,Bash,Agent";

/// Sub-agent policy of an author whose role allows sub-agents (general engine line): every
/// sub-agent runs on the session's pinned author model, at most `max_concurrent` run at once, and a sub-agent cannot
/// start further sub-agents (spawn depth 1). Recorded in each `invocation.json` with the session environment.
pub fn subagent_environment(model: AuthorModel, max_concurrent: u32) -> Vec<(&'static str, String)> {
    vec![
        ("CLAUDE_CODE_SUBAGENT_MODEL", model.id().to_string()),
        ("CLAUDE_CODE_MAX_CONCURRENT_SUBAGENTS", max_concurrent.to_string()),
        ("CLAUDE_CODE_MAX_SUBAGENT_SPAWN_DEPTH", "1".to_string()),
    ]
}

/// What varies between the calls of one session.
pub(super) struct Launch<'a> {
    /// The session's pinned author model.
    pub model: AuthorModel,
    /// The role allows sub-agents (`Agent` among the built-in tools).
    pub subagents: bool,
    pub session_id: &'a str,
    /// Continue the existing provider session (`--resume`) instead of creating it (`--session-id`).
    pub resume: bool,
    /// The call's provider-cost stop guard (its reservation); unset passes no CLI budget.
    pub stop_guard_usd: Money,
    pub mcp_config: &'a Path,
    /// Local MCP tools the author may call without a permission prompt; empty when the role declares none.
    pub local_tools: &'a [String],
}

/// Command-line arguments of one call: print mode with a structured JSON event stream, the session's model and effort,
/// full permissions, the built-in tools plus the declared local tools, only this call's MCP configuration, no user or
/// project settings, the stop guard, the submission schema and the session.
pub(super) fn arguments(launch: &Launch) -> Vec<String> {
    let mut argv: Vec<String> = [
        "--print",
        "--verbose",
        "--output-format",
        "stream-json",
        "--model",
        launch.model.id(),
        "--effort",
        EFFORT,
        "--permission-mode",
        "bypassPermissions",
        "--allow-dangerously-skip-permissions",
        "--tools",
        if launch.subagents { BUILTIN_TOOLS_WITH_SUBAGENTS } else { BUILTIN_TOOLS },
        "--disable-slash-commands",
    ]
    .map(String::from)
    .into();
    if !launch.local_tools.is_empty() {
        // Claude Code documents --tools as a built-in-tool selector: MCP names placed there were absent from the
        // provider's init event even though the server was connected. Permission is this separate flag.
        argv.extend(["--allowedTools".into(), launch.local_tools.join(",")]);
    }
    argv.extend(["--strict-mcp-config".into(), "--mcp-config".into(), launch.mcp_config.display().to_string()]);
    argv.extend(["--setting-sources", "", "--prompt-suggestions", "false"].map(String::from));
    if !launch.stop_guard_usd.is_unset() {
        argv.extend(["--max-budget-usd".into(), launch.stop_guard_usd.decimal()]);
    }
    argv.extend(["--json-schema".into(), CandidateSubmission::schema().to_string()]);
    argv.extend([if launch.resume { "--resume" } else { "--session-id" }.into(), launch.session_id.into()]);
    argv
}

/// The local tools a recorded command line allowed (the inverse of [`arguments`]), for rebuilding a receipt.
pub(super) fn allowed_local_tools(argv: &[String]) -> Vec<String> {
    argv.iter()
        .position(|argument| argument == "--allowedTools")
        .and_then(|at| argv.get(at + 1))
        .map(|tools| tools.split(',').filter(|tool| !tool.is_empty()).map(String::from).collect())
        .unwrap_or_default()
}

/// The call's `mcp-config.json`: the framework's local-tool server over stdio, started as `server.program
/// server.arguments… <tool context> <local-jobs dir>`, or no server at all.
pub(super) fn mcp_config(server: Option<(&LocalToolServer, &Path)>, local_jobs: &Path) -> Value {
    let servers = match server {
        Some((server, tool_context)) => {
            let mut args: Vec<Value> = server.arguments.iter().map(|argument| json!(argument)).collect();
            args.extend([json!(tool_context), json!(local_jobs)]);
            json!({LOCAL_TOOL_SERVER_NAME:{"type":"stdio","command":server.program,"args":args}})
        }
        None => json!({}),
    };
    json!({"mcpServers":servers})
}
