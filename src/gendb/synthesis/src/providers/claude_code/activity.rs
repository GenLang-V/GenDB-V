//! Per-tool activity leases for the author's Bash tool.
//!
//! Model inference and file-text tools hold no lease. Every Bash invocation runs through a generated guardian
//! (`activity_shell.py`, installed as Claude Code's shell through `CLAUDE_CODE_SHELL`) that holds a shared `flock` on
//! the run's activity lock for the shell and all its descendants, so a framework job that needs the machine alone
//! (an exclusive lease, for example a timed measurement) waits until the author's shell work has quiesced, while the
//! provider keeps running. Structured local tools (MCP) take their own leases. The guardian records only lifecycle
//! metadata (queue, acquire and finish times, exit codes), never command text, arguments or environment.

use crate::controller::records;
use serde::Serialize;
use serde_json::json;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

/// Claude Code versions whose shell selection and dispatch were inspected (read-only inspection of the executables):
/// they honor an executable bash/zsh override in `CLAUDE_CODE_SHELL`, start detached shell children with `-c [-l]`
/// arguments, and read the two Bash timeout variables set by [`ActivityShell::environment`]. 2.1.283 was checked by two
/// real calls through a logging `CLAUDE_CODE_SHELL` shim (`-c`, `-c -l`; a 2 s `BASH_DEFAULT_TIMEOUT_MS` stopped a
/// 6 s command). A real 2.1.283 author call
/// also showed the other behaviour: a command reaching its 600 s timeout "was moved to the background" and kept
/// running with its children; the guardian is then not cancelled, so the call keeps its
/// lease and group until it exits, the provider exits, or the author sends TERM to that group. Author prompts state
/// both routes (`prompts::sections::PROCESSES_APPENDIX`). 2.1.286 was checked the same way: `-c` and `-c -l` through
/// the shim, both timeout variables read, a 2 s `BASH_DEFAULT_TIMEOUT_MS` stopped a 6 s command (exit 143).
const INSPECTED_SHELL_VERSIONS: [&str; 5] = ["2.1.270", "2.1.273", "2.1.280", "2.1.283", "2.1.286"];

/// The guardian needs Linux child subreaping (`PR_SET_CHILD_SUBREAPER`) and this interpreter.
const GUARDIAN_INTERPRETER: &str = "/usr/bin/python3";

/// Upper bounds of one Bash tool call's default and maximum timeouts, covering queue wait, execution and descendant
/// cleanup. Both are further capped by the call's own wall guard. They raise Claude Code's shorter built-in defaults
/// so that ordinary compiles and diagnostic runs fit; they stay below the user's 30-minute ceiling for one test.
const BASH_DEFAULT_TIMEOUT_MS: u64 = 600_000;
const BASH_MAX_TIMEOUT_MS: u64 = 1_740_000;

/// Refuse a Claude Code version whose shell dispatch was not inspected, rather than silently losing the lease.
pub(super) fn check_shell_version(version: &str) -> Result<(), String> {
    match version.split_whitespace().next() {
        Some(release) if INSPECTED_SHELL_VERSIONS.contains(&release) => Ok(()),
        _ => Err("per-tool activity transport requires inspected Claude Code 2.1.270, 2.1.273, 2.1.280, 2.1.283 or 2.1.286".into()),
    }
}

/// Fail before any paid dispatch when this host cannot supervise Linux children.
pub(super) fn check_guardian_support() -> Result<(), String> {
    let status = Command::new(GUARDIAN_INTERPRETER)
        .args([
            "-c",
            "import ctypes,os; assert hasattr(os, 'fork') and hasattr(os, 'pipe2'); assert ctypes.CDLL(None).prctl(36,1,0,0,0)==0",
        ])
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status();
    // A check ended by the user's stop is never read (`gendb_runtime::process_stop`).
    gendb_runtime::process_stop::park_if_stopping();
    let status = status.map_err(|e| format!("author shell supervisor unavailable: {e}"))?;
    if !status.success() {
        return Err("author shell supervisor requires Linux subreaping and /usr/bin/python3".into());
    }
    Ok(())
}

/// The installed guardian of one call (`invocation.json` `tool_activity`, format 1).
#[derive(Clone, Debug, Serialize)]
pub(super) struct ActivityShell {
    format_version: u32,
    /// The executable guardian (`<call>/author-shell/gendb-author-bash`).
    pub wrapper: PathBuf,
    activity_lock: PathBuf,
    /// One lifecycle-event file per Bash invocation.
    events: PathBuf,
    default_timeout_ms: u64,
    max_timeout_ms: u64,
    timeout_scope: &'static str,
    scope: &'static str,
    accounting: &'static str,
}

impl ActivityShell {
    /// Install the guardian and its configuration in `<call_dir>/author-shell/`.
    pub fn install(call_dir: &Path, activity_lock: &Path, author_timeout_seconds: u64) -> Result<Self, String> {
        let shell_dir = call_dir.join("author-shell");
        let events = shell_dir.join("tool-activity");
        fs::create_dir(&shell_dir).map_err(|e| format!("{}: {e}", shell_dir.display()))?;
        fs::create_dir(&events).map_err(|e| format!("{}: {e}", events.display()))?;
        let wrapper = shell_dir.join("gendb-author-bash");
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&wrapper)
            .map_err(|e| format!("{}: {e}", wrapper.display()))?;
        file.write_all(include_bytes!("activity_shell.py")).map_err(|e| e.to_string())?;
        file.set_permissions(fs::Permissions::from_mode(0o700)).map_err(|e| e.to_string())?;
        records::write_json_atomic(
            &shell_dir.join("activity-config.json"),
            &json!({"activity_lock":activity_lock,"policy":"all Bash subprocess trees hold shared activity; structured MCP jobs schedule themselves"}),
        )
        .map_err(|e| e.to_string())?;
        let author_timeout_ms = author_timeout_seconds.saturating_mul(1000).max(1);
        Ok(Self {
            format_version: 1,
            wrapper,
            activity_lock: activity_lock.to_path_buf(),
            events,
            default_timeout_ms: author_timeout_ms.min(BASH_DEFAULT_TIMEOUT_MS),
            max_timeout_ms: author_timeout_ms.min(BASH_MAX_TIMEOUT_MS),
            timeout_scope: "queue, shell execution and descendant cleanup",
            scope: "shell invocation and descendants; inference and file-text tools hold no activity lease",
            accounting: "author elapsed includes tool queue waits; per-tool monotonic wait/execution intervals may overlap and must not be added as exclusive wall phases",
        })
    }

    /// Variables that route the provider's Bash tool through the guardian. `CLAUDE_CODE_SHELL_PREFIX` must be removed
    /// from the provider environment as well: a prefix command would run outside the lease.
    pub fn environment(&self) -> [(&'static str, String); 3] {
        [
            ("CLAUDE_CODE_SHELL", self.wrapper.display().to_string()),
            ("BASH_DEFAULT_TIMEOUT_MS", self.default_timeout_ms.to_string()),
            ("BASH_MAX_TIMEOUT_MS", self.max_timeout_ms.to_string()),
        ]
    }
}
