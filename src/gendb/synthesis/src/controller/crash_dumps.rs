//! Crash-dump containment of one controller process and every process it starts.
//!
//! This host pipes core dumps to a crash handler (`/proc/sys/kernel/core_pattern`), and Linux does not apply
//! `RLIMIT_CORE` to piped dumps (`man 5 core`), so a crashed child that maps or allocates gigabytes is dumped whole and
//! held until the handler has read it. [`contain`] writes 0 to `/proc/self/coredump_filter` (dump no anonymous,
//! file-backed or huge-page mappings) once per process, before any child starts. A child inherits the value across
//! fork and exec (`man 5 core`), so it covers the author provider and its Bash commands (whose guardian also sets it,
//! `providers/claude_code/activity_shell.py`), the MCP server, rust_verify and every `gendb worker` evaluation, trial,
//! build and serving child. A crash is still reported by the host's handler, with the registers, the mapped-file
//! list and the vDSO but no memory contents. Nothing system-wide changes, and this is no claim that every crash is
//! harmless or quick: the handler's own work and scheduling remain the host's.
//!
//! [`observe`] reports what is actually set (read back from `/proc`, never assumed) with the containment error, if
//! any; it appears in the authors' facts (CURRENT FACTS, Host and measurement; the context's
//! `observed_hardware.crash_dumps`).

use serde_json::{Value, json};
use std::fs;
use std::sync::OnceLock;

const FILTER: &str = "/proc/self/coredump_filter";

/// The filter value [`contain`] writes: no memory mapping of any kind is dumped.
pub const CONTAINED_FILTER: &str = "00000000";

static CONTAINMENT: OnceLock<Result<String, String>> = OnceLock::new();

/// Set this process's coredump filter to 0 (once per process) and return the value read back, or why it could not be
/// set. A failure is reported by [`observe`]; it never stops a run.
pub fn contain() -> Result<String, String> {
    CONTAINMENT
        .get_or_init(|| {
            fs::write(FILTER, "0").map_err(|e| format!("{FILTER}: {e}"))?;
            fs::read_to_string(FILTER).map(|value| value.trim().to_string()).map_err(|e| format!("{FILTER}: {e}"))
        })
        .clone()
}

/// The crash-dump setting this process and its children inherit now, the containment outcome and the host's handler.
pub fn observe() -> Value {
    let filter = fs::read_to_string(FILTER).ok().map(|value| value.trim().to_string());
    let error = match CONTAINMENT.get() {
        None => Some("containment was not requested in this process".to_string()),
        Some(Err(error)) => Some(error.clone()),
        Some(Ok(_)) => None,
    };
    let handler = fs::read_to_string("/proc/sys/kernel/core_pattern").ok().map(|pattern| pattern.trim().to_string());
    json!({"coredump_filter":filter,"contained":filter.as_deref() == Some(CONTAINED_FILTER),"containment_error":error,"host_crash_handler":handler,
        "scope":"this GenDB process and every process it starts, including author Bash commands (Linux coredump_filter is inherited across fork and exec); system-wide settings are unchanged",
        "meaning":"00000000: a crash is still reported by the host's crash handler, but its dump holds no memory mappings (registers, mapped-file list and vDSO only); the handler's own time is not bounded by this",
        "source":"man 5 core (/proc/[pid]/coredump_filter)"})
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::os::unix::process::ExitStatusExt;
    use std::path::{Path, PathBuf};
    use std::process::Command;
    use std::time::Instant;

    /// Containment reads back 0 and a fork+exec child inherits it (no crash involved).
    #[test]
    fn children_inherit_the_contained_filter() {
        assert_eq!(contain().as_deref(), Ok(CONTAINED_FILTER));
        let child = Command::new("/bin/sh").args(["-c", "cat /proc/self/coredump_filter"]).output().unwrap();
        assert_eq!(String::from_utf8_lossy(&child.stdout).trim(), CONTAINED_FILTER);
        let observed = observe();
        assert_eq!((observed["contained"].as_bool(), &observed["containment_error"]), (Some(true), &Value::Null), "{observed}");
    }

    /// One deliberate abort of a tiny owned child (a uniquely named copy of `sleep`, so a handler report's name cannot
    /// collide with another program's), recorded before it is signalled: its inherited filter, the signal, whether the
    /// kernel dumped, the time until it was reaped and the handler's report (path and size, or null when the handler
    /// wrote none). Evidence goes to `$TMPDIR/gendb-crash-probe-<pid>/evidence.json`; a report, if any, is kept.
    #[test]
    #[ignore = "deliberately aborts one tiny owned child; the host crash handler may write a small report"]
    fn a_contained_abort_of_a_tiny_owned_child_is_recorded() {
        contain().unwrap();
        let tmp = PathBuf::from(std::env::var_os("TMPDIR").expect("TMPDIR must name a scratch directory"));
        let dir = tmp.join(format!("gendb-crash-probe-{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        let probe = dir.join("gendb-crash-probe");
        fs::copy("/usr/bin/sleep", &probe).unwrap();
        let mut child = Command::new(&probe).arg("30").spawn().unwrap();
        let pid = child.id();
        let evidence = dir.join("evidence.json");
        fs::write(&evidence, json!({"status":"started","pid":pid,"probe":probe}).to_string()).unwrap();
        let child_filter = fs::read_to_string(format!("/proc/{pid}/coredump_filter")).map(|v| v.trim().to_string()).ok();
        let started = Instant::now();
        assert_eq!(unsafe { libc::kill(pid as libc::pid_t, libc::SIGABRT) }, 0);
        let status = child.wait().unwrap();
        let reaped_ns = started.elapsed().as_nanos() as u64;
        let uid = unsafe { libc::getuid() };
        let report = Path::new("/var/crash").join(format!("{}.{uid}.crash", probe.display().to_string().replace('/', "_")));
        let report_bytes = fs::metadata(&report).ok().map(|m| m.len());
        let record = json!({"status":"completed","pid":pid,"probe":probe,"child_coredump_filter":child_filter,"signal":status.signal(),
            "core_dumped":status.core_dumped(),"kill_to_reaped_ns":reaped_ns,"handler_report":report,"handler_report_bytes":report_bytes,
            "crash_dumps":observe()});
        fs::write(&evidence, serde_json::to_string_pretty(&record).unwrap()).unwrap();
        println!("{record}");
        assert_eq!((status.signal(), child_filter.as_deref()), (Some(libc::SIGABRT), Some(CONTAINED_FILTER)));
    }
}
