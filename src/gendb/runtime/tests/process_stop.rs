//! The user's stop of a controller process (`gendb_runtime::process_stop`) end to end. This test executable doubles as
//! the controller (`main` below; `harness = false`): with `GENDB_PROCESS_STOP_TEST_RUN=<run dir>` it installs the stop
//! and starts stand-ins for a controller's children, then idles until it is stopped. No GenDB run, no provider: `sleep`,
//! `bash`, `setsid` and `timeout` stand in. Scratch under `TMPDIR` (a scratch directory).
//!
//! The stand-ins (`controller`):
//! - `plain`: a child in the controller's process group (as `rust_verify`), waited for by a thread that calls
//!   `park_if_stopping` and would then write `after-the-wait` (the result of a child the stop ended must never be used);
//! - `provider`: `bash` leading its own owned group, stopped by SIGINT (as the author provider), with a background
//!   `sleep` in its group (`provider-child`; a non-interactive shell's background job ignores SIGINT) and a
//!   `setsid sleep` in a session of its own (`provider-setsid`; as the author's Bash calls);
//! - `worker`: `timeout 600 sleep 600` leading its own owned group, stopped by SIGTERM (as a worker child);
//! - `escaped`: a `setsid sleep` whose shell exited at once, so it is no longer the controller's descendant: only the
//!   launch tag in its environment names it.
//!
//! Checks:
//! 1. **TERM**: the controller ends by SIGTERM; every stand-in is gone, none survived (`stop-<id>.json`), the provider's
//!    group got SIGINT and the worker's SIGTERM, the waiting thread never used the stopped child's result, and
//!    `leftovers` lists nothing;
//! 2. **SIGKILL of the controller's process group** (the operator's hard stop; the controller leads its group, as under
//!    `setsid`): the children in the group die with it, the worker's and the provider's groups get their death signals
//!    from the kernel, and exactly what does not end with its leader is left: the provider's background job, its
//!    `setsid` job and the escaped job. `leftovers` lists exactly those (each by the launch tag); the test then kills
//!    them.

use gendb_runtime::process_stop::{self, LATEST_LAUNCH, ProcessStat, RECORD_DIRECTORY, die_with_controller, leftovers, live_launches, own_group};
use serde_json::{Value, json};
use std::collections::BTreeSet;
use std::fs;
use std::os::unix::process::{CommandExt, ExitStatusExt};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

const RUN_VARIABLE: &str = "GENDB_PROCESS_STOP_TEST_RUN";
const READY_FILE: &str = "ready.json";
const AFTER_THE_WAIT: &str = "after-the-wait";

fn main() {
    if let Some(run) = std::env::var_os(RUN_VARIABLE) {
        controller(Path::new(&run));
    }
    let tmp = PathBuf::from(std::env::var_os("TMPDIR").expect("TMPDIR must name a scratch directory"));
    let root = tmp.join(format!("process-stop-{}", std::process::id()));
    fs::create_dir_all(&root).unwrap();
    term_stops_every_process_tree(&root.join("term"));
    process_group_kill_leaves_only_what_leftovers_lists(&root.join("kill"));
    fs::remove_dir_all(&root).unwrap();
    println!("process_stop: ok (TERM stops every process tree; a SIGKILL leaves exactly what leftovers lists)");
}

// ------------------------------------------------------------------------------------------------ the controller

/// The controller child: install the stop, start the stand-ins (module documentation), write `ready.json` with their
/// pids and start ticks, and idle.
fn controller(run: &Path) -> ! {
    let launch = process_stop::install(run).unwrap();
    let mut plain = Command::new("sleep");
    plain.arg("600");
    die_with_controller(&mut plain, libc::SIGTERM);
    let mut plain = plain.spawn().unwrap();
    let plain_pid = plain.id();
    let waited = run.join(AFTER_THE_WAIT);
    std::thread::spawn(move || {
        let status = plain.wait();
        process_stop::park_if_stopping();
        fs::write(&waited, format!("{status:?}")).unwrap();
    });
    let script = "trap 'exit 130' INT; sleep 600 & echo $! > \"$1/provider-child\"; setsid sleep 600 > /dev/null 2>&1 < /dev/null & echo $! > \"$1/provider-setsid\"; wait";
    let mut provider = Command::new("bash");
    provider.args(["-c", script, "provider"]).arg(run).process_group(0);
    die_with_controller(&mut provider, libc::SIGINT);
    let provider = provider.spawn().unwrap();
    let provider_group = own_group(provider.id(), libc::SIGINT, "provider stand-in");
    let mut worker = Command::new("timeout");
    worker.args(["600", "sleep", "600"]).process_group(0);
    die_with_controller(&mut worker, libc::SIGTERM);
    let worker = worker.spawn().unwrap();
    let worker_group = own_group(worker.id(), libc::SIGTERM, "worker stand-in");
    let escaped = Command::new("bash")
        .args(["-c", "setsid sleep 600 > /dev/null 2>&1 < /dev/null & echo $! > \"$1/escaped\"", "escape"])
        .arg(run)
        .status()
        .unwrap();
    assert!(escaped.success());
    let pid_in = |name: &str| -> u32 {
        let path = run.join(name);
        let started = Instant::now();
        loop {
            if let Some(pid) = fs::read_to_string(&path).ok().and_then(|t| t.trim().parse().ok()) {
                return pid;
            }
            assert!(started.elapsed() < Duration::from_secs(20), "{} never appeared", path.display());
            std::thread::sleep(Duration::from_millis(20));
        }
    };
    let mut pids = serde_json::Map::new();
    for (name, pid) in [("plain", plain_pid), ("provider", provider.id()), ("worker", worker.id())] {
        pids.insert(name.into(), json!(pid));
    }
    for name in ["provider-child", "provider-setsid", "escaped"] {
        pids.insert(name.into(), json!(pid_in(name)));
    }
    // The worker's `sleep` (timeout's child) appears once timeout has started it.
    let started = Instant::now();
    let worker_sleep = loop {
        let child = fs::read_to_string(format!("/proc/{}/task/{}/children", worker.id(), worker.id())).unwrap_or_default();
        if let Some(pid) = child.split_whitespace().next().and_then(|p| p.parse::<u32>().ok()) {
            break pid;
        }
        assert!(started.elapsed() < Duration::from_secs(20), "timeout never started its child");
        std::thread::sleep(Duration::from_millis(20));
    };
    pids.insert("worker-child".into(), json!(worker_sleep));
    let starts: serde_json::Map<String, Value> =
        pids.iter().map(|(name, pid)| (name.clone(), json!(ProcessStat::read(pid.as_i64().unwrap() as i32).map(|s| s.start_ticks)))).collect();
    let ready = json!({"launch":launch.id,"pids":pids,"start_ticks":starts});
    fs::write(run.join(READY_FILE), serde_json::to_vec_pretty(&ready).unwrap()).unwrap();
    let _keep = (provider, worker, provider_group, worker_group);
    loop {
        std::thread::sleep(Duration::from_secs(60));
    }
}

// ------------------------------------------------------------------------------------------------ the checks

fn start_controller(run: &Path, own_process_group: bool) -> (Child, Value) {
    fs::create_dir_all(run).unwrap();
    let log = fs::File::create(run.with_extension("log")).unwrap();
    let mut command = Command::new(std::env::current_exe().unwrap());
    command.env(RUN_VARIABLE, run).stdin(Stdio::null()).stdout(log.try_clone().unwrap()).stderr(log);
    if own_process_group {
        command.process_group(0);
    }
    let child = command.spawn().unwrap();
    let ready = run.join(READY_FILE);
    let started = Instant::now();
    while !ready.is_file() {
        assert!(started.elapsed() < Duration::from_secs(60), "the controller never got ready ({})", run.with_extension("log").display());
        std::thread::sleep(Duration::from_millis(50));
    }
    let ready: Value = serde_json::from_slice(&fs::read(&ready).unwrap()).unwrap();
    (child, ready)
}

fn wait_with_timeout(child: &mut Child, limit: Duration) -> ExitStatus {
    let started = Instant::now();
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            return status;
        }
        assert!(started.elapsed() < limit, "the controller did not end within {limit:?}");
        std::thread::sleep(Duration::from_millis(50));
    }
}

/// The stand-ins of `ready` (name, pid) still alive: same pid and start, not ended.
fn alive(ready: &Value) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for (name, pid) in ready["pids"].as_object().unwrap() {
        let pid = pid.as_i64().unwrap() as i32;
        let start = ready["start_ticks"][name].as_u64();
        if ProcessStat::read(pid).is_some_and(|s| !matches!(s.state, 'Z' | 'X' | 'x') && Some(s.start_ticks) == start) {
            names.insert(name.clone());
        }
    }
    names
}

/// Wait (at most 10 s) until the stand-ins alive are exactly `expected`.
fn settle(ready: &Value, expected: &[&str]) -> BTreeSet<String> {
    let expected: BTreeSet<String> = expected.iter().map(|s| s.to_string()).collect();
    let started = Instant::now();
    loop {
        let now = alive(ready);
        if now == expected || started.elapsed() > Duration::from_secs(10) {
            return now;
        }
        std::thread::sleep(Duration::from_millis(50));
    }
}

fn term_stops_every_process_tree(run: &Path) {
    let (mut child, ready) = start_controller(run, false);
    let launch = ready["launch"].as_str().unwrap();
    assert_eq!(alive(&ready).len(), 7, "every stand-in runs: {ready}");
    let latest: Value = serde_json::from_slice(&fs::read(run.join(RECORD_DIRECTORY).join(LATEST_LAUNCH)).unwrap()).unwrap();
    assert_eq!(latest["launch"]["id"], launch);
    let started = Instant::now();
    // SAFETY: kill(2) on the controller child this test started and has not reaped.
    unsafe {
        libc::kill(child.id() as i32, libc::SIGTERM);
    }
    let status = wait_with_timeout(&mut child, process_stop::GRACE + process_stop::KILL_WAIT + Duration::from_secs(20));
    let elapsed = started.elapsed();
    assert_eq!(status.signal(), Some(libc::SIGTERM), "the controller ends with the stop signal: {status:?}");
    let left = settle(&ready, &[]);
    assert!(left.is_empty(), "stand-ins left after the TERM stop: {left:?}");
    let stop: Value = serde_json::from_slice(&fs::read(run.join(RECORD_DIRECTORY).join(format!("stop-{launch}.json"))).unwrap()).unwrap();
    assert_eq!(stop["signal"], "SIGTERM");
    assert_eq!(stop["survivors"], json!([]), "{stop}");
    assert_eq!(stop["resumable"], true);
    let groups: Vec<(String, String)> = stop["owned_groups"].as_array().unwrap().iter().map(|g| (g["what"].as_str().unwrap().into(), g["signal"].as_str().unwrap().into())).collect();
    assert!(groups.contains(&("provider stand-in".into(), "SIGINT".into())) && groups.contains(&("worker stand-in".into(), "SIGTERM".into())), "{groups:?}");
    let recorded: BTreeSet<i64> = stop["processes"].as_array().unwrap().iter().filter(|p| !p["ended_after_ms"].is_null()).map(|p| p["pid"].as_i64().unwrap()).collect();
    for (name, pid) in ready["pids"].as_object().unwrap() {
        assert!(recorded.contains(&pid.as_i64().unwrap()), "{name} ({pid}) is not recorded as stopped and ended: {stop}");
    }
    let killed: Vec<&Value> = stop["processes"].as_array().unwrap().iter().filter(|p| p["signals"].as_array().unwrap().iter().any(|s| s["signal"] == "SIGKILL")).collect();
    assert!(killed.is_empty(), "nothing needed SIGKILL: {killed:?}");
    assert!(!run.join(AFTER_THE_WAIT).exists(), "the thread waiting for the plain child used the result of a child the stop ended");
    let leftovers = leftovers(run).unwrap();
    assert_eq!(leftovers.processes, Vec::<Value>::new(), "{leftovers:?}");
    println!("TERM: the controller ended by SIGTERM after {elapsed:?}; {} processes stopped, none left", stop["processes"].as_array().unwrap().len());
}

fn process_group_kill_leaves_only_what_leftovers_lists(run: &Path) {
    let (mut child, ready) = start_controller(run, true);
    let launch = ready["launch"].as_str().unwrap().to_string();
    assert_eq!(alive(&ready).len(), 7, "every stand-in runs: {ready}");
    let live: Vec<String> = live_launches(run).unwrap().into_iter().map(|l| l.id).collect();
    assert_eq!(live, [launch.clone()], "the running controller's launch is live (gendb engine re-evaluate refuses then)");
    // SAFETY: kill(2) of the process group led by the controller child this test started (`process_group(0)`).
    unsafe {
        libc::kill(-(child.id() as i32), libc::SIGKILL);
    }
    let status = wait_with_timeout(&mut child, Duration::from_secs(20));
    assert_eq!(status.signal(), Some(libc::SIGKILL), "{status:?}");
    let expected = ["escaped", "provider-child", "provider-setsid"];
    let left = settle(&ready, &expected);
    assert_eq!(left, expected.iter().map(|s| s.to_string()).collect::<BTreeSet<_>>(), "after the process group's SIGKILL");
    assert!(!run.join(RECORD_DIRECTORY).join(format!("stop-{launch}.json")).exists(), "no stop runs after SIGKILL");
    assert!(live_launches(run).unwrap().is_empty(), "an ended controller's launch is not live");
    let listed = leftovers(run).unwrap();
    let listed_pids: BTreeSet<i64> = listed.processes.iter().map(|p| p["pid"].as_i64().unwrap()).collect();
    let expected_pids: BTreeSet<i64> = expected.iter().map(|name| ready["pids"][*name].as_i64().unwrap()).collect();
    assert_eq!(listed_pids, expected_pids, "leftovers lists exactly what was left: {listed:?}");
    for process in &listed.processes {
        let why = process["why"].as_array().unwrap();
        assert!(why.iter().any(|w| w.as_str().unwrap().contains(&format!("carries the tag of launch {launch}"))), "{process}");
    }
    for pid in &listed_pids {
        // SAFETY: kill(2) of a leftover this test's controller child started (listed by its launch tag).
        unsafe {
            libc::kill(*pid as i32, libc::SIGKILL);
        }
    }
    let left = settle(&ready, &[]);
    assert!(left.is_empty(), "{left:?}");
    assert_eq!(leftovers(run).unwrap().processes, Vec::<Value>::new());
    println!("KILL: the process group's SIGKILL left {} processes, all listed by leftovers (then killed)", listed_pids.len());
}
