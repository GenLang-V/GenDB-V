//! The operator's end of a provider wait: `gendb engine operator-resume RUN_DIR BRANCH [TEXT]`. When a
//! branch's session waits for the provider (`controller::provider_wait`: a rate limit until its reset time, or a
//! backoff) and the operator knows the limit is over sooner (for example a weekly limit that was reset
//! early), the command records that the wait is over, so the relaunched controller calls at once instead of waiting
//! again until the recorded deadline.
//!
//! - It writes `provider-wait-cleared.json` (`controller::provider_wait::WaitCleared`: when, `by: operator`, the
//!   optional reason TEXT, the call the wait follows and its deadline) in the waiting call's directory of the branch's
//!   latest session, beside the wait's `provider-wait.json`; written once, never replaced or removed.
//! - It refuses (nothing written) when there is no wait to clear: no session, the latest call has no recorded wait,
//!   the wait is not `waiting`, or it was cleared already.
//! - **The controller must be stopped** (the simpler safe option, as for `gendb engine re-evaluate`): a running
//!   controller sleeps until its deadline and does not read the record. The command refuses while a controller launch
//!   of the run is alive (`gendb_runtime::process_stop::live_launches`) and holds the session's run lock
//!   (`<session>/controller.lock`) while it writes. The operator stops the run (SIGTERM), runs this command, then relaunches.
//!
//! On relaunch the controller logs the clearing on stderr, marks the wait's record `cleared` and resumes the same
//! provider session with the short continuation message. If the provider is still limited, that call fails and a new
//! wait starts as usual.

use super::operator_note::branch_directory;
use super::re_evaluation::hold_session;
use super::rounds::engine_directory;
use crate::controller::layout::RunLayout;
use crate::controller::provider_wait::{self, PROVIDER_WAIT_CLEARED_FILE};
use serde_json::{Value, json};
use std::fs;
use std::path::{Path, PathBuf};

/// Clear the wait of `branch`'s latest session in the run `run_dir` (module documentation). Returns the record of
/// what was written.
pub fn operator_resume(run_dir: &Path, branch: &str, reason: Option<&str>) -> Result<Value, String> {
    let root = run_dir.canonicalize().map_err(|e| format!("{}: {e}", run_dir.display()))?;
    if let Some(launch) = gendb_runtime::process_stop::live_launches(&root)?.last() {
        return Err(format!(
            "the run's controller is running (pid {}, launch {}): stop it (SIGTERM to that pid), run operator-resume, then relaunch it",
            launch.pid, launch.id
        ));
    }
    let session = latest_session(&engine_directory(&root), branch)?;
    let _session_lock = hold_session(&session)?;
    let layout = RunLayout::new(&session);
    let cleared = provider_wait::clear_recorded_wait(&layout, "operator", reason).map_err(|e| e.to_string())?;
    Ok(json!({
        "cleared": cleared,
        "record": layout.call(cleared.after_call).join(PROVIDER_WAIT_CLEARED_FILE),
        "session": session,
        "next": "relaunch the run's controller: it resumes the same provider session at once with the short continuation message"
    }))
}

/// The latest session directory of `branch` (`engine/branches/<branch>/sessions/session-NNNN`, highest number).
fn latest_session(engine_dir: &Path, branch: &str) -> Result<PathBuf, String> {
    let sessions = branch_directory(engine_dir, branch).join("sessions");
    if branch.is_empty() || branch.contains('/') || !sessions.is_dir() {
        return Err(format!("{branch} is not a branch of this run with a session (no {})", sessions.display()));
    }
    let entries = fs::read_dir(&sessions).map_err(|e| format!("{}: {e}", sessions.display()))?;
    entries
        .flatten()
        .map(|entry| entry.path())
        .filter(|path| path.is_dir() && path.file_name().and_then(|name| name.to_str()).is_some_and(|name| name.starts_with("session-")))
        .max()
        .ok_or_else(|| format!("{branch} has no session (none under {})", sessions.display()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::controller::test_support::scratch_root;

    /// Done-check: the command refuses a branch without a session and a session without a wait, and runs
    /// on the branch's latest session only. (The clearing's rules: `controller::provider_wait` tests.)
    #[test]
    fn operator_resume_needs_a_waiting_session_of_the_branch() {
        let root = scratch_root("engine-operator-resume");
        let engine = engine_directory(&root);
        fs::create_dir_all(&root).unwrap();
        assert!(operator_resume(&root, "b1", None).unwrap_err().contains("b1 is not a branch of this run with a session"));
        for number in [2, 3] {
            fs::create_dir_all(super::super::sessions::session_directory(&engine, "b1", number)).unwrap();
        }
        let error = operator_resume(&root, "b1", Some("reset")).unwrap_err();
        assert!(error.contains("session-0003") && error.contains("no wait to clear: the session has no ledger"), "{error}");
        assert!(operator_resume(&root, "../b1", None).is_err());
        fs::remove_dir_all(&root).ok();
    }
}
