//! Supervising one running provider process until it exits.
//!
//! The provider leads its own process group (spawned with `process_group(0)`), and only that owned group is ever
//! signalled:
//! - SIGINT when its init event disqualifies the call (another model or session, or missing required local tools):
//!   the CLI then emits its terminal result, so the usage of the stopped call is still accounted;
//! - SIGKILL when that interrupted process outlives [`INIT_ABORT_GRACE`], when the call's wall guard
//!   (`author_timeout_seconds`) elapses, or when waiting on the process fails.
//!
//! The Bash guardian of the call dies with the provider on its own (`activity_shell.py`); nothing else is killed.
//!
//! The user's stop (`gendb_runtime::process_stop`) sends the group SIGINT; once the provider has ended, the supervising
//! thread parks instead of settling the call, so the relaunch recovers it from its transcript.

use super::AuthorModel;
use super::transcript::{ToolCapabilities, init_event, init_refusal};
use crate::controller::records;
use serde_json::{Value, json};
use std::fs;
use std::path::Path;
use std::process::{Child, ExitStatus};
use std::time::{Duration, Instant};

/// After a call is interrupted at its init event, the provider gets this long to emit its terminal result.
const INIT_ABORT_GRACE: Duration = Duration::from_secs(30);
const POLL_INTERVAL: Duration = Duration::from_millis(100);
/// How often the supervisor records that the provider process is alive (`heartbeat.json` in the call directory), so an
/// interrupted controller leaves evidence of when the call was last seen running.
const HEARTBEAT_INTERVAL: Duration = Duration::from_secs(60);

/// What the supervision watches.
pub(super) struct Watch<'a> {
    /// The provider's `stdout.jsonl`, read only until its init event appears.
    pub transcript: &'a Path,
    pub session_id: &'a str,
    /// The session's pinned author model, which the init event must name.
    pub model: AuthorModel,
    pub required_tools: &'a [String],
    pub wall_guard: Duration,
    pub started: Instant,
}

/// How the provider process ended.
pub(super) enum ProcessEnd {
    Exited(ExitStatus),
    /// The call's wall guard elapsed; the group was killed and the process reaped.
    WallGuardElapsed,
    /// Waiting failed; the group was killed.
    WaitFailed(std::io::Error),
}

/// The call was interrupted at its provider init event.
pub(super) struct InitStop {
    pub reason: String,
    /// `init_capability_abort` of `process-exit.json` and `tool-capabilities.json`.
    pub evidence: Value,
}

pub(super) struct Supervised {
    pub end: ProcessEnd,
    pub init_stop: Option<InitStop>,
}

/// Poll the process until it exits, applying the init check once and the wall guard throughout.
pub(super) fn supervise(child: &mut Child, watch: &Watch) -> Supervised {
    let mut init_checked = false;
    let mut init_stop = None;
    let mut interrupted_at: Option<Instant> = None;
    let mut last_heartbeat: Option<Instant> = None;
    loop {
        if last_heartbeat.is_none_or(|at| at.elapsed() >= HEARTBEAT_INTERVAL) {
            write_heartbeat(child, watch);
            last_heartbeat = Some(Instant::now());
        }
        match child.try_wait() {
            Ok(Some(status)) => {
                gendb_runtime::process_stop::park_if_stopping();
                return Supervised { end: ProcessEnd::Exited(status), init_stop };
            }
            Ok(None) => {}
            Err(error) => {
                gendb_runtime::process_stop::park_if_stopping();
                signal_owned_group(child, libc::SIGKILL);
                let _ = child.wait();
                return Supervised { end: ProcessEnd::WaitFailed(error), init_stop };
            }
        }
        if !init_checked {
            let transcript = fs::read_to_string(watch.transcript).unwrap_or_default();
            if let Some((_, init)) = init_event(&transcript) {
                init_checked = true;
                if let Some(reason) = init_refusal(&init, watch.session_id, watch.model, watch.required_tools) {
                    signal_owned_group(child, libc::SIGINT);
                    interrupted_at = Some(Instant::now());
                    let evidence = json!({"stopped_at_provider_init":true,"signal":"SIGINT","unix_ms":records::now_unix_ms(),
                        "reason":reason,"observed":ToolCapabilities::observe(&transcript, watch.required_tools)});
                    init_stop = Some(InitStop { reason, evidence });
                }
            }
        }
        if interrupted_at.is_some_and(|at| at.elapsed() >= INIT_ABORT_GRACE) {
            signal_owned_group(child, libc::SIGKILL);
            interrupted_at = None;
        }
        if watch.started.elapsed() >= watch.wall_guard {
            signal_owned_group(child, libc::SIGKILL);
            let _ = child.wait();
            return Supervised { end: ProcessEnd::WallGuardElapsed, init_stop };
        }
        std::thread::sleep(POLL_INTERVAL);
    }
}

/// Record that the provider process is alive: its pid, the call's elapsed time and the transcript size (evidence only;
/// a failed write is ignored).
fn write_heartbeat(child: &Child, watch: &Watch) {
    let Some(call_dir) = watch.transcript.parent() else { return };
    let transcript_bytes = fs::metadata(watch.transcript).map(|m| m.len()).ok();
    let _ = records::write_json_atomic(&call_dir.join("heartbeat.json"), &json!({"unix_ms":records::now_unix_ms(),"provider_pid":child.id(),
        "elapsed_ms":watch.started.elapsed().as_millis() as u64,"transcript_bytes":transcript_bytes,"session_id":watch.session_id}));
}

fn signal_owned_group(child: &Child, signal: libc::c_int) {
    // SAFETY: the child was spawned as the leader of a new process group and has not been reaped (its pid cannot be
    // reused), so the negative pid names only the group this call owns.
    unsafe {
        libc::kill(-(child.id() as i32), signal);
    }
}
