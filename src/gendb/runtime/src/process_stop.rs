//! The user's stop of a controller process (`gendb engine synthesize|prepare`): on SIGTERM or SIGINT the controller
//! stops every process tree it started, waits for them to end, records the stop and ends itself with the same signal,
//! so the run stays resumable from its records and leaves no orphan behind. Host code outside every claim.
//!
//! Without this module a TERM ended the controller at once, and its children ran on as orphans: `rust_verify` and its
//! `z3` processes, worker children, the author provider and the author's tool processes.
//!
//! **Install** ([`install`], once, first thing in a controller process):
//! - the launch record `<run>/processes/launch-<id>.json`, copied to `latest-launch.json` ([`Launch`]: pid, parent,
//!   process group, session, command); `<id>` is `<start unix ms>-<pid>`;
//! - the launch tag `GENDB_CONTROLLER_LAUNCH=<id>` in the controller's environment: every child that inherits the
//!   environment carries it, also after it leaves the controller's process group or session on purpose (the author's
//!   Bash calls run in sessions of their own; an author's `setsid` job). The Verus runs start with a fixed environment
//!   and carry no tag; they stay in the controller's process group;
//! - SIGTERM and SIGINT handlers: the handler marks the controller stopping, then wakes the stop thread.
//!
//! **Owned groups.** A spawn site that starts a child as the leader of its own process group registers it
//! ([`own_group`]) with the signal that stops it gracefully, and arms [`die_with_controller`] (the kernel signals the
//! child when the thread that started it ends, so also when the controller dies by SIGKILL):
//! - the author provider: SIGINT (Claude Code then writes its terminal result, so the stopped call's usage is accounted
//!   when the relaunch recovers the call), also as its death signal;
//! - each worker child's `timeout`: SIGTERM (which `timeout` forwards to its process group), also as its death signal.
//!
//! **The stop** (the stop thread, on the first signal):
//! 1. each owned group gets its signal; every other process of the controller outside an owned group's tree gets
//!    SIGTERM, also one that appears while the stop waits;
//! 2. it waits until none is left, at most [`GRACE`];
//! 3. whatever is left gets SIGKILL (each owned group too), and it waits at most [`KILL_WAIT`];
//! 4. it writes `<run>/processes/stop-<id>.json`: the signal, every process seen with the signals it got and when it
//!    ended, and the survivors (none expected). The run is resumable: relaunching the same command continues from its
//!    records;
//! 5. it ends the controller with the same signal (exit status 143 for SIGTERM), so a launcher sees how it ended.
//!
//! A process of the controller ([`ProcessTable::of_launch`]) is a descendant (parent chain), a member of an owned group
//! in the controller's session, or a process whose environment carries this launch's tag. A zombie has ended.
//!
//! **No stopped child's result is recorded.** The handler marks the controller stopping before any child is signalled.
//! Every site that waits for a child calls [`park_if_stopping`] when the wait returns (the worker parent, the Verus runs
//! and their version check, the provider supervision and inspection, the Bash guardian check): the thread then parks
//! until the controller ends, so a child's death by the stop never becomes a result (a worker killed by a signal would
//! otherwise be an unfinished cell, a killed `rust_verify` a tool failure). The same sites start no child once the
//! controller is stopping. Any other thread runs on until the controller ends, as before this module: every record is
//! written atomically and a relaunch resumes from the records. Not covered: the SQL frontend's short parser process
//! (`gendb-frontend` cannot depend on this crate); a parser ended by the stop returns a process error, which callers
//! treat as a framework error, never as a refusal.
//!
//! **After a SIGKILL** of the controller (the operator's hard stop: `kill -KILL -- -<process group>`) no stop runs. Children in
//! the controller's process group die with it; the owned groups get their death signal from the kernel; the author's
//! tool processes are ended by their Bash guardians once the provider is gone. A child of an owned group that does not
//! end with its leader can be left. [`leftovers`] (`gendb processes RUN_DIR`) lists what is left of every recorded
//! launch whose controller has ended: processes that carry its tag, are in its process group or session after their
//! leader ended, or work under the run directory (working directory or `TMPDIR`).

use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::os::unix::fs::MetadataExt;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicBool, AtomicI32, Ordering};
use std::sync::{Mutex, MutexGuard, OnceLock, PoisonError};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

/// The directory of a run's process records: `<run>/processes/`.
pub const RECORD_DIRECTORY: &str = "processes";
/// The newest launch's record (a copy of its `launch-<id>.json`).
pub const LATEST_LAUNCH: &str = "latest-launch.json";
/// The environment variable that tags every child of one launch; its value is the launch id.
pub const LAUNCH_VARIABLE: &str = "GENDB_CONTROLLER_LAUNCH";
/// How long the graceful phase of a stop waits for the processes it signalled: the provider's terminal result after
/// SIGINT may take a while (the provider supervision gives an interrupted call the same 30 s).
pub const GRACE: Duration = Duration::from_secs(30);
/// How long the stop waits after SIGKILL before it records the survivors.
pub const KILL_WAIT: Duration = Duration::from_secs(10);
/// How often the stop reads the process table while it waits.
const POLL: Duration = Duration::from_millis(100);

/// Set by the signal handler (first) and never cleared: the controller is stopping.
static STOPPING: AtomicBool = AtomicBool::new(false);
/// The write end of the stop thread's wake pipe (-1 before [`install`]).
static WAKE: AtomicI32 = AtomicI32::new(-1);
/// The owned groups whose leader has not been reaped yet, by leader pid.
static OWNED_GROUPS: Mutex<BTreeMap<i32, OwnedGroup>> = Mutex::new(BTreeMap::new());
/// This process's launch, once installed.
static LAUNCH: OnceLock<Launch> = OnceLock::new();

/// One launch of a controller process (`launch-<id>.json`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Launch {
    pub format_version: u32,
    /// `<start unix ms>-<pid>`; also the value of [`LAUNCH_VARIABLE`] in its children.
    pub id: String,
    pub pid: i32,
    /// Start of the process in clock ticks since boot (`/proc/<pid>/stat` field 22): with `pid`, the process's identity
    /// (a pid is reused once its process ended).
    pub start_ticks: u64,
    pub parent: i32,
    pub process_group: i32,
    pub session: i32,
    /// Start ticks of the process group's and the session's leader at launch (`None`: no such process then).
    pub process_group_leader_start_ticks: Option<u64>,
    pub session_leader_start_ticks: Option<u64>,
    pub started_unix_ms: u64,
    pub run_directory: PathBuf,
    pub command: Vec<String>,
    /// `GENDB_CONTROLLER_LAUNCH=<id>`, as it appears in a child's environment.
    pub tag: String,
}

impl Launch {
    fn record_directory(&self) -> PathBuf {
        self.run_directory.join(RECORD_DIRECTORY)
    }
}

/// A child that leads its own process group, with the signal that stops it gracefully.
#[derive(Clone, Copy, Debug)]
struct OwnedGroup {
    leader: i32,
    stop_signal: libc::c_int,
    what: &'static str,
}

/// The registration of an owned group ([`own_group`]); dropping it (after the leader is reaped) ends the registration.
#[must_use = "the group is owned only while this guard lives"]
pub struct OwnedGroupGuard {
    leader: i32,
}

impl Drop for OwnedGroupGuard {
    fn drop(&mut self) {
        owned_groups().remove(&self.leader);
    }
}

fn owned_groups() -> MutexGuard<'static, BTreeMap<i32, OwnedGroup>> {
    OWNED_GROUPS.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Register the child `leader`, started as the leader of its own process group, as owned: a stop sends `stop_signal`
/// to its group and leaves the processes of its tree to it until [`GRACE`] ends. `what` names it in the stop record.
/// Keep the guard until the child is reaped.
pub fn own_group(leader: u32, stop_signal: libc::c_int, what: &'static str) -> OwnedGroupGuard {
    let leader = leader as i32;
    owned_groups().insert(leader, OwnedGroup { leader, stop_signal, what });
    OwnedGroupGuard { leader }
}

/// Arm `command`'s child to receive `signal` from the kernel when the thread that starts it ends (`PR_SET_PDEATHSIG`):
/// when the controller ends, even by SIGKILL. The kernel ties the signal to the starting *thread*, so call it only where
/// that thread waits for the child (every caller does). A child whose controller ended before the signal was armed does
/// not start (`ESRCH`).
pub fn die_with_controller(command: &mut Command, signal: libc::c_int) -> &mut Command {
    // SAFETY: getpid has no preconditions.
    let controller = unsafe { libc::getpid() };
    // SAFETY: the closure runs in the forked child before exec and calls only async-signal-safe functions (prctl,
    // getppid, reading errno); it allocates nothing.
    unsafe {
        command.pre_exec(move || {
            if libc::prctl(libc::PR_SET_PDEATHSIG, signal as libc::c_ulong, 0, 0, 0) != 0 {
                return Err(std::io::Error::last_os_error());
            }
            if libc::getppid() != controller {
                return Err(std::io::Error::from_raw_os_error(libc::ESRCH));
            }
            Ok(())
        })
    }
}

/// Whether the controller is stopping (a stop signal arrived).
pub fn is_stopping() -> bool {
    STOPPING.load(Ordering::SeqCst)
}

/// When the controller is stopping, park this thread until the stop ends the process (module documentation): call it
/// when a wait for a child returns, before the result is used, and before a child is started. A no-op otherwise, and
/// in every process without [`install`].
pub fn park_if_stopping() {
    if is_stopping() {
        loop {
            std::thread::park();
        }
    }
}

/// This process's launch, when [`install`] ran.
pub fn launch() -> Option<&'static Launch> {
    LAUNCH.get()
}

/// Install the user's stop in this controller process for the run directory `run_dir` (module documentation): the
/// launch record, the launch tag in the environment, the SIGTERM and SIGINT handlers and the stop thread. Call it once,
/// first thing in the controller, while no other thread reads or writes the environment.
pub fn install(run_dir: &Path) -> Result<&'static Launch, String> {
    if let Some(launch) = LAUNCH.get() {
        return Err(format!("the user's stop is already installed for launch {}", launch.id));
    }
    let record_dir = run_dir.join(RECORD_DIRECTORY);
    fs::create_dir_all(&record_dir).map_err(|e| format!("{}: {e}", record_dir.display()))?;
    let run_directory = run_dir.canonicalize().map_err(|e| format!("{}: {e}", run_dir.display()))?;
    // SAFETY: getpid has no preconditions.
    let pid = unsafe { libc::getpid() };
    let me = ProcessStat::read(pid).ok_or("this process's /proc/self/stat is unreadable")?;
    let started_unix_ms = now_unix_ms();
    let id = format!("{started_unix_ms}-{pid}");
    let launch = Launch {
        format_version: 1,
        tag: format!("{LAUNCH_VARIABLE}={id}"),
        id,
        pid,
        start_ticks: me.start_ticks,
        parent: me.parent,
        process_group: me.process_group,
        session: me.session,
        process_group_leader_start_ticks: ProcessStat::read(me.process_group).map(|s| s.start_ticks),
        session_leader_start_ticks: ProcessStat::read(me.session).map(|s| s.start_ticks),
        started_unix_ms,
        run_directory,
        command: std::env::args().collect(),
    };
    let record = json!({"launch":launch,
        "stop":"SIGTERM (or SIGINT) to this pid stops every process this controller started, waits, records stop-<id>.json and ends with the same signal; the run is resumable",
        "hard_stop":"SIGKILL to the process group stops no child of an owned group gracefully; gendb processes RUN_DIR lists what is left"});
    write_json_atomic(&launch.record_directory().join(format!("launch-{}.json", launch.id)), &record)?;
    write_json_atomic(&launch.record_directory().join(LATEST_LAUNCH), &record)?;
    // SAFETY: the caller's contract: no other thread reads or writes the environment now.
    unsafe { std::env::set_var(LAUNCH_VARIABLE, &launch.id) };
    let wake_reader = install_handlers()?;
    let launch = LAUNCH.get_or_init(|| launch);
    std::thread::Builder::new()
        .name("user-stop".into())
        .spawn(move || stop_thread(wake_reader, launch))
        .map_err(|e| format!("the user-stop thread: {e}"))?;
    Ok(launch)
}

/// The wake pipe (close-on-exec; its write end non-blocking, so the handler never blocks) and the SIGTERM and SIGINT
/// handlers. Returns the read end.
fn install_handlers() -> Result<libc::c_int, String> {
    let mut ends = [0 as libc::c_int; 2];
    // SAFETY: pipe2 writes two descriptors into `ends`; fcntl and sigaction get valid arguments: the handler is an
    // `extern "C" fn(c_int)` that only stores an atomic, calls write(2) and restores errno.
    unsafe {
        if libc::pipe2(ends.as_mut_ptr(), libc::O_CLOEXEC) != 0 {
            return Err(format!("pipe2: {}", std::io::Error::last_os_error()));
        }
        let flags = libc::fcntl(ends[1], libc::F_GETFL);
        if flags < 0 || libc::fcntl(ends[1], libc::F_SETFL, flags | libc::O_NONBLOCK) != 0 {
            return Err(format!("fcntl: {}", std::io::Error::last_os_error()));
        }
        WAKE.store(ends[1], Ordering::SeqCst);
        for signal in [libc::SIGTERM, libc::SIGINT] {
            let mut action: libc::sigaction = std::mem::zeroed();
            action.sa_sigaction = on_stop_signal as *const () as libc::sighandler_t;
            action.sa_flags = libc::SA_RESTART;
            libc::sigemptyset(&mut action.sa_mask);
            if libc::sigaction(signal, &action, std::ptr::null_mut()) != 0 {
                return Err(format!("sigaction({signal}): {}", std::io::Error::last_os_error()));
            }
        }
    }
    Ok(ends[0])
}

/// The SIGTERM/SIGINT handler: mark the controller stopping (before anything else, so no thread acts on a child that
/// the stop ends), then write the signal number into the wake pipe.
extern "C" fn on_stop_signal(signal: libc::c_int) {
    STOPPING.store(true, Ordering::SeqCst);
    let wake = WAKE.load(Ordering::SeqCst);
    if wake >= 0 {
        let byte = signal as u8;
        // SAFETY: write(2) on the pipe's write end with a one-byte buffer is async-signal-safe; errno is restored.
        unsafe {
            let errno = *libc::__errno_location();
            libc::write(wake, (&byte as *const u8).cast(), 1);
            *libc::__errno_location() = errno;
        }
    }
}

/// The stop thread: wait for the first stop signal, stop the processes, record the stop and end the controller.
fn stop_thread(wake: libc::c_int, launch: &'static Launch) {
    let signal = wait_for_signal(wake);
    let record = stop_processes(launch, signal);
    let path = launch.record_directory().join(format!("stop-{}.json", launch.id));
    let written = write_json_atomic(&path, &record);
    let survivors = record["survivors"].as_array().map_or(0, Vec::len);
    eprintln!(
        "gendb: {} received: {} processes of this controller stopped, {survivors} left; the run is resumable (relaunch the same command); record {}{}",
        signal_name(signal),
        record["processes"].as_array().map_or(0, Vec::len),
        path.display(),
        written.err().map_or(String::new(), |e| format!(" NOT WRITTEN: {e}"))
    );
    end_with(signal)
}

fn wait_for_signal(wake: libc::c_int) -> libc::c_int {
    loop {
        let mut byte = 0u8;
        // SAFETY: read(2) into a one-byte buffer from the pipe's read end.
        let read = unsafe { libc::read(wake, (&mut byte as *mut u8).cast(), 1) };
        if read == 1 {
            return libc::c_int::from(byte);
        }
        if read < 0 && std::io::Error::last_os_error().kind() == std::io::ErrorKind::Interrupted {
            continue;
        }
        // The pipe's write end is never closed; should reading fail anyway, a controller that is stopping must still
        // stop (its waiting threads are parked).
        if is_stopping() {
            return libc::SIGTERM;
        }
        std::thread::sleep(Duration::from_secs(1));
    }
}

/// End this process with `signal` (its default action), as if the signal had ended it.
fn end_with(signal: libc::c_int) -> ! {
    // SAFETY: restoring the default action of a stop signal and sending it to this process; its default action ends
    // the process.
    unsafe {
        libc::signal(signal, libc::SIG_DFL);
        libc::kill(libc::getpid(), signal);
    }
    std::thread::sleep(Duration::from_secs(10));
    std::process::exit(128 + signal)
}

/// The stop's phases (module documentation); returns the stop record.
fn stop_processes(launch: &Launch, signal: libc::c_int) -> Value {
    let started = Instant::now();
    let received_unix_ms = now_unix_ms();
    let groups: Vec<OwnedGroup> = owned_groups().values().copied().collect();
    let leaders: BTreeSet<i32> = groups.iter().map(|g| g.leader).collect();
    let mut log = StopLog::new(started);
    let mut left = log.observe(launch, &leaders);
    for group in &groups {
        send(-group.leader, group.stop_signal);
        send(group.leader, group.stop_signal);
        log.signalled(group.leader, group.stop_signal);
    }
    let graceful_until = started + GRACE;
    while !left.is_empty() && Instant::now() < graceful_until {
        // An owned group's leader stops its own tree; what is left of the tree once the leader has ended gets SIGTERM.
        let live_leaders: BTreeSet<i32> = left.iter().map(|p| p.stat.pid).filter(|pid| leaders.contains(pid)).collect();
        for process in &left {
            let left_to_leader = process.in_owned_group_tree.is_some_and(|leader| live_leaders.contains(&leader));
            if !left_to_leader && !leaders.contains(&process.stat.pid) && !log.was_signalled(process) {
                send(process.stat.pid, libc::SIGTERM);
                log.signalled(process.stat.pid, libc::SIGTERM);
            }
        }
        std::thread::sleep(POLL);
        left = log.observe(launch, &leaders);
    }
    let graceful_ms = started.elapsed().as_millis() as u64;
    let killed_until = Instant::now() + KILL_WAIT;
    while !left.is_empty() && Instant::now() < killed_until {
        for process in &left {
            send(process.stat.pid, libc::SIGKILL);
            log.signalled(process.stat.pid, libc::SIGKILL);
        }
        for group in &groups {
            send(-group.leader, libc::SIGKILL);
        }
        std::thread::sleep(POLL);
        left = log.observe(launch, &leaders);
    }
    let survivors: Vec<Value> = left.iter().map(|p| log.entry_of(p)).collect();
    json!({"format_version":1,"launch":launch.id,"pid":launch.pid,"signal":signal_name(signal),"received_unix_ms":received_unix_ms,
        "ended_unix_ms":now_unix_ms(),"graceful_phase_ms":graceful_ms,"grace_ms":GRACE.as_millis() as u64,"kill_wait_ms":KILL_WAIT.as_millis() as u64,
        "owned_groups":groups.iter().map(|g| json!({"leader":g.leader,"what":g.what,"signal":signal_name(g.stop_signal)})).collect::<Vec<_>>(),
        "processes":log.entries(),"survivors":survivors,
        "resumable":true,
        "relaunch":"run the same command again: the run resumes from its records (an interrupted author call is recovered from its transcript, an interrupted evaluation is evaluated again, an admission happens once)",
        "meaning":"every process this controller started (descendants, members of its owned process groups, processes carrying its launch tag) was signalled and waited for before the controller ended; survivors lists any still alive when it ended"})
}

fn send(target: i32, signal: libc::c_int) {
    // SAFETY: kill(2) with a valid signal; a target that no longer exists only yields ESRCH.
    unsafe {
        libc::kill(target, signal);
    }
}

fn signal_name(signal: libc::c_int) -> String {
    match signal {
        libc::SIGTERM => "SIGTERM".into(),
        libc::SIGINT => "SIGINT".into(),
        libc::SIGKILL => "SIGKILL".into(),
        other => format!("signal {other}"),
    }
}

/// What a stop saw of each process: when it was first seen and why it is the controller's, the signals it got, and when
/// it was seen gone.
struct StopLog {
    started: Instant,
    entries: BTreeMap<(i32, u64), LogEntry>,
}

struct LogEntry {
    stat: ProcessStat,
    why: &'static str,
    command: String,
    seen_after_ms: u64,
    signals: Vec<(String, u64)>,
    ended_after_ms: Option<u64>,
}

impl StopLog {
    fn new(started: Instant) -> Self {
        Self { started, entries: BTreeMap::new() }
    }

    fn now_ms(&self) -> u64 {
        self.started.elapsed().as_millis() as u64
    }

    /// The controller's live processes now; new ones are added, gone ones marked ended.
    fn observe(&mut self, launch: &Launch, leaders: &BTreeSet<i32>) -> Vec<OwnedProcess> {
        let now = self.now_ms();
        let live = ProcessTable::read().map(|t| t.of_launch(launch, leaders)).unwrap_or_default();
        let keys: BTreeSet<(i32, u64)> = live.iter().map(|p| (p.stat.pid, p.stat.start_ticks)).collect();
        for process in &live {
            self.entries.entry((process.stat.pid, process.stat.start_ticks)).or_insert_with(|| LogEntry {
                stat: process.stat.clone(),
                why: process.why,
                command: command_line(process.stat.pid),
                seen_after_ms: now,
                signals: vec![],
                ended_after_ms: None,
            });
        }
        for (key, entry) in self.entries.iter_mut() {
            if entry.ended_after_ms.is_none() && !keys.contains(key) {
                entry.ended_after_ms = Some(now);
            }
        }
        live
    }

    /// Record that `pid` got `signal` (once per signal: the hard phase repeats SIGKILL while a process stays).
    fn signalled(&mut self, pid: i32, signal: libc::c_int) {
        let now = self.now_ms();
        let name = signal_name(signal);
        if let Some(entry) = self.entries.values_mut().filter(|e| e.stat.pid == pid && e.ended_after_ms.is_none()).last()
            && !entry.signals.iter().any(|(s, _)| *s == name)
        {
            entry.signals.push((name, now));
        }
    }

    fn was_signalled(&self, process: &OwnedProcess) -> bool {
        self.entries.get(&(process.stat.pid, process.stat.start_ticks)).is_some_and(|e| !e.signals.is_empty())
    }

    fn entry_of(&self, process: &OwnedProcess) -> Value {
        self.entries.get(&(process.stat.pid, process.stat.start_ticks)).map_or(Value::Null, LogEntry::to_json)
    }

    fn entries(&self) -> Vec<Value> {
        self.entries.values().map(LogEntry::to_json).collect()
    }
}

impl LogEntry {
    fn to_json(&self) -> Value {
        json!({"pid":self.stat.pid,"start_ticks":self.stat.start_ticks,"parent":self.stat.parent,"process_group":self.stat.process_group,
            "session":self.stat.session,"why":self.why,"command":self.command,"seen_after_ms":self.seen_after_ms,
            "signals":self.signals.iter().map(|(s, at)| json!({"signal":s,"after_ms":at})).collect::<Vec<_>>(),"ended_after_ms":self.ended_after_ms})
    }
}

// ------------------------------------------------------------------------------------------------ the process table

/// The fields of `/proc/<pid>/stat` the stop uses, and the owner's uid.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ProcessStat {
    pub pid: i32,
    pub state: char,
    pub parent: i32,
    pub process_group: i32,
    pub session: i32,
    pub start_ticks: u64,
    pub uid: u32,
}

impl ProcessStat {
    /// `/proc/<pid>/stat`, or `None` when the process is gone (or unreadable).
    pub fn read(pid: i32) -> Option<Self> {
        let dir = PathBuf::from(format!("/proc/{pid}"));
        let uid = fs::metadata(&dir).ok()?.uid();
        let mut stat = Self::parse(&fs::read_to_string(dir.join("stat")).ok()?)?;
        stat.uid = uid;
        Some(stat)
    }

    /// Parse one `/proc/<pid>/stat` line: `pid (comm) state ppid pgrp session ...`, start time = field 22. The command
    /// name may hold spaces and parentheses, so the fields after it are counted from its last `)`.
    fn parse(text: &str) -> Option<Self> {
        let open = text.find('(')?;
        let close = text.rfind(')')?;
        let pid = text[..open].trim().parse().ok()?;
        let fields: Vec<&str> = text.get(close + 1..)?.split_whitespace().collect();
        Some(Self {
            pid,
            state: fields.first()?.chars().next()?,
            parent: fields.get(1)?.parse().ok()?,
            process_group: fields.get(2)?.parse().ok()?,
            session: fields.get(3)?.parse().ok()?,
            start_ticks: fields.get(19)?.parse().ok()?,
            uid: 0,
        })
    }

    /// A zombie (or dead) process has ended; only its parent's reaping is pending.
    fn ended(&self) -> bool {
        matches!(self.state, 'Z' | 'X' | 'x')
    }
}

/// A process of a launch and why.
#[derive(Clone, Debug)]
pub struct OwnedProcess {
    pub stat: ProcessStat,
    /// `descendant`, `owned process group` or `launch tag`.
    pub why: &'static str,
    /// The owned group leader on its parent chain (below the controller), if any: the leader's own stop handles it.
    pub in_owned_group_tree: Option<i32>,
}

/// Every process of the host this user can read, at one moment.
pub struct ProcessTable {
    processes: BTreeMap<i32, ProcessStat>,
}

impl ProcessTable {
    pub fn read() -> Result<Self, String> {
        let mut processes = BTreeMap::new();
        for entry in fs::read_dir("/proc").map_err(|e| format!("/proc: {e}"))? {
            let Ok(entry) = entry else { continue };
            let Some(pid) = entry.file_name().to_str().and_then(|n| n.parse::<i32>().ok()) else { continue };
            if let Some(stat) = ProcessStat::read(pid) {
                processes.insert(pid, stat);
            }
        }
        Ok(Self { processes })
    }

    /// Whether the process `pid` that started at `start_ticks` (any start when `None`) is alive (not ended).
    fn alive(&self, pid: i32, start_ticks: Option<u64>) -> bool {
        self.processes.get(&pid).is_some_and(|p| !p.ended() && start_ticks.is_none_or(|t| t == p.start_ticks))
    }

    /// The live processes of `launch` (module documentation), the controller itself excluded: descendants (with the
    /// owned group leader on their parent chain), members of the owned groups `leaders` in its session, and processes
    /// of this user whose environment carries its tag.
    pub fn of_launch(&self, launch: &Launch, leaders: &BTreeSet<i32>) -> Vec<OwnedProcess> {
        let mut children: BTreeMap<i32, Vec<i32>> = BTreeMap::new();
        for p in self.processes.values() {
            children.entry(p.parent).or_default().push(p.pid);
        }
        let mut owned: BTreeMap<i32, OwnedProcess> = BTreeMap::new();
        if self.alive(launch.pid, Some(launch.start_ticks)) {
            let mut stack: Vec<(i32, Option<i32>)> = vec![(launch.pid, None)];
            while let Some((pid, in_group)) = stack.pop() {
                let below = in_group.or_else(|| (pid != launch.pid && leaders.contains(&pid)).then_some(pid));
                for child in children.get(&pid).into_iter().flatten() {
                    if let Some(stat) = self.processes.get(child) {
                        owned.insert(*child, OwnedProcess { stat: stat.clone(), why: "descendant", in_owned_group_tree: below });
                        stack.push((*child, below));
                    }
                }
            }
        }
        for p in self.processes.values() {
            if !owned.contains_key(&p.pid) && leaders.contains(&p.process_group) && p.session == launch.session && p.pid != launch.pid {
                let in_group = (p.pid != p.process_group).then_some(p.process_group);
                owned.insert(p.pid, OwnedProcess { stat: p.clone(), why: "owned process group", in_owned_group_tree: in_group });
            }
        }
        // SAFETY: getuid has no preconditions.
        let uid = unsafe { libc::getuid() };
        for p in self.processes.values() {
            if !owned.contains_key(&p.pid) && p.pid != launch.pid && p.uid == uid && !p.ended() && environment_has(p.pid, &launch.tag) {
                owned.insert(p.pid, OwnedProcess { stat: p.clone(), why: "launch tag", in_owned_group_tree: None });
            }
        }
        owned.into_values().filter(|p| !p.stat.ended()).collect()
    }
}

/// Whether `/proc/<pid>/environ` (the environment the process started with) holds the entry `entry`.
fn environment_has(pid: i32, entry: &str) -> bool {
    fs::read(format!("/proc/{pid}/environ")).is_ok_and(|environ| environ.split(|b| *b == 0).any(|e| e == entry.as_bytes()))
}

/// The value of `name` in `/proc/<pid>/environ`, if any.
fn environment_value(pid: i32, name: &str) -> Option<PathBuf> {
    let environ = fs::read(format!("/proc/{pid}/environ")).ok()?;
    let prefix = format!("{name}=");
    environ.split(|b| *b == 0).find_map(|e| e.strip_prefix(prefix.as_bytes()).map(|v| PathBuf::from(String::from_utf8_lossy(v).into_owned())))
}

/// The command line of `pid` (arguments joined by spaces, at most 300 characters).
fn command_line(pid: i32) -> String {
    let raw = fs::read(format!("/proc/{pid}/cmdline")).unwrap_or_default();
    let text = String::from_utf8_lossy(&raw).replace('\0', " ").trim().to_string();
    match text.char_indices().nth(300) {
        Some((cut, _)) => format!("{}...", &text[..cut]),
        None => text,
    }
}

// ------------------------------------------------------------------------------------------------ leftovers

/// What is left of a run's recorded launches ([`leftovers`]).
#[derive(Debug, Serialize)]
pub struct Leftovers {
    pub run_directory: PathBuf,
    /// Every recorded launch: `(id, pid, whether its controller is alive)`.
    pub launches: Vec<Value>,
    /// Live processes left by launches whose controller ended, each with why it belongs to the run.
    pub processes: Vec<Value>,
    pub meaning: &'static str,
}

/// Every launch recorded under `<run_directory>/processes/` (`launch-<id>.json`), oldest first.
fn recorded_launches(run_directory: &Path) -> Result<Vec<Launch>, String> {
    let records = run_directory.join(RECORD_DIRECTORY);
    let mut launches: Vec<Launch> = vec![];
    if records.is_dir() {
        for entry in fs::read_dir(&records).map_err(|e| format!("{}: {e}", records.display()))? {
            let path = entry.map_err(|e| e.to_string())?.path();
            let name = path.file_name().and_then(|n| n.to_str()).unwrap_or_default();
            if name.starts_with("launch-") && name.ends_with(".json") {
                let record: Value = serde_json::from_slice(&fs::read(&path).map_err(|e| format!("{}: {e}", path.display()))?).map_err(|e| format!("{}: {e}", path.display()))?;
                launches.push(serde_json::from_value(record["launch"].clone()).map_err(|e| format!("{}: {e}", path.display()))?);
            }
        }
    }
    launches.sort_by_key(|l| l.started_unix_ms);
    Ok(launches)
}

/// The recorded launches of `run_dir` whose controller process is alive now (the same pid and start time), oldest
/// first: empty when no controller of the run runs. Reads only (`gendb engine re-evaluate` refuses while one runs).
pub fn live_launches(run_dir: &Path) -> Result<Vec<Launch>, String> {
    let run_directory = run_dir.canonicalize().map_err(|e| format!("{}: {e}", run_dir.display()))?;
    let launches = recorded_launches(&run_directory)?;
    Ok(launches.into_iter().filter(|l| ProcessStat::read(l.pid).is_some_and(|p| !p.ended() && p.start_ticks == l.start_ticks)).collect())
}

/// The live processes left by the recorded launches of `run_dir` whose controller has ended (module documentation):
/// processes carrying a launch's tag, in a launch's process group or session after that leader ended, or whose working
/// directory or `TMPDIR` is under the run directory. The processes of a live controller of the run, this process and its
/// ancestors are never listed. Lists only; signals nothing.
pub fn leftovers(run_dir: &Path) -> Result<Leftovers, String> {
    let run_directory = run_dir.canonicalize().map_err(|e| format!("{}: {e}", run_dir.display()))?;
    let launches = recorded_launches(&run_directory)?;
    let table = ProcessTable::read()?;
    // SAFETY: getpid and getuid have no preconditions.
    let (me, uid) = unsafe { (libc::getpid(), libc::getuid()) };
    let mut excluded: BTreeSet<i32> = BTreeSet::new();
    let mut ancestor = Some(me);
    while let Some(pid) = ancestor.filter(|p| *p > 1) {
        excluded.insert(pid);
        ancestor = table.processes.get(&pid).map(|p| p.parent);
    }
    let (live, ended): (Vec<&Launch>, Vec<&Launch>) = launches.iter().partition(|l| table.alive(l.pid, Some(l.start_ticks)));
    for launch in &live {
        excluded.insert(launch.pid);
        excluded.extend(table.of_launch(launch, &BTreeSet::new()).iter().map(|p| p.stat.pid));
    }
    let under_run = |path: &Path| path.starts_with(&run_directory);
    let mut processes = vec![];
    for p in table.processes.values().filter(|p| p.uid == uid && !p.ended() && !excluded.contains(&p.pid)) {
        let mut why: Vec<String> = vec![];
        for launch in &ended {
            if environment_has(p.pid, &launch.tag) {
                why.push(format!("carries the tag of launch {}", launch.id));
            }
            if p.process_group == launch.process_group && !table.alive(launch.process_group, launch.process_group_leader_start_ticks) {
                why.push(format!("in process group {} of launch {}, whose leader ended", launch.process_group, launch.id));
            }
            if p.session == launch.session && !table.alive(launch.session, launch.session_leader_start_ticks) {
                why.push(format!("in session {} of launch {}, whose leader ended", launch.session, launch.id));
            }
        }
        if fs::read_link(format!("/proc/{}/cwd", p.pid)).is_ok_and(|cwd| under_run(&cwd)) {
            why.push("its working directory is under the run directory".into());
        }
        if environment_value(p.pid, "TMPDIR").is_some_and(|tmp| under_run(&tmp)) {
            why.push("its TMPDIR is under the run directory".into());
        }
        if !why.is_empty() {
            processes.push(json!({"pid":p.pid,"parent":p.parent,"process_group":p.process_group,"session":p.session,"state":p.state.to_string(),
                "command":command_line(p.pid),"why":why}));
        }
    }
    Ok(Leftovers {
        run_directory,
        launches: launches.iter().map(|l| json!({"id":l.id,"pid":l.pid,"process_group":l.process_group,"session":l.session,"controller_alive":live.contains(&l)})).collect(),
        processes,
        meaning: "live processes left by this run's ended controller launches; none is signalled here. Stop one with kill -TERM <pid> (kill -KILL <pid> if it stays); a listed process group or session can be stopped whole with kill -KILL -- -<group>",
    })
}

// ------------------------------------------------------------------------------------------------ small helpers

fn now_unix_ms() -> u64 {
    SystemTime::now().duration_since(UNIX_EPOCH).map_or(0, |d| d.as_millis() as u64)
}

/// Write `value` to `path` through a temporary file in the same directory and a rename.
fn write_json_atomic(path: &Path, value: &Value) -> Result<(), String> {
    let staged = path.with_extension(format!("json.{}.tmp", std::process::id()));
    let bytes = serde_json::to_vec_pretty(value).map_err(|e| e.to_string())?;
    fs::write(&staged, bytes).map_err(|e| format!("{}: {e}", staged.display()))?;
    fs::rename(&staged, path).map_err(|e| format!("{}: {e}", path.display()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stat_lines_parse_after_the_last_parenthesis() {
        let line = "4242 (z3 (worker) x) S 4200 4100 4000 0 -1 4194560 100 0 0 0 1 2 0 0 20 0 1 0 987654 1000 10 18446744073709551615 0 0 0 0 0 0 0 0 0 0 0 0 17 3 0 0 0 0 0\n";
        let stat = ProcessStat::parse(line).unwrap();
        assert_eq!((stat.pid, stat.state, stat.parent, stat.process_group, stat.session, stat.start_ticks), (4242, 'S', 4200, 4100, 4000, 987654));
        assert!(ProcessStat::parse("17 (short) S 1").is_none(), "a truncated line is not a process");
        let me = ProcessStat::read(std::process::id() as i32).unwrap();
        assert_eq!(me.pid, std::process::id() as i32);
        assert!(!me.ended());
    }

    #[test]
    fn nothing_parks_or_stops_without_a_stop_signal() {
        assert!(!is_stopping());
        park_if_stopping();
        let guard = own_group(999_999, libc::SIGINT, "test");
        assert!(owned_groups().contains_key(&999_999));
        drop(guard);
        assert!(!owned_groups().contains_key(&999_999));
    }
}
