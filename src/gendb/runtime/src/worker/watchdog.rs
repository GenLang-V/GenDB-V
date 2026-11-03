//! The per-call limits of a limited engine job, enforced inside the worker child.
//!
//! One watchdog thread per child. Before each engine call the child arms it with the call's identity; after the call
//! it disarms it and records the call's observation here. While a call is armed the watchdog wakes at least every
//! [`MEMORY_POLL_INTERVAL_MS`] ms (and exactly at the time limit), reads the process's anonymous resident memory
//! (`RssAnon` of `/proc/self/status`, the kernel's per-process anonymous page counter: no page-table walk, unlike
//! `/proc/self/smaps_rollup`, whose `Anonymous` total is the same quantity) and stops the child when the call has run
//! for the wall-time limit or its anonymous memory exceeds the memory limit: it writes the result so far (every
//! recorded observation, plus [`Unfinished`] naming the stopped call, its elapsed time, memory and, when sampling,
//! its samples) to the result file and ends the process at once with [`UNFINISHED_EXIT_CODE`] (`_exit`: no
//! destructor, `atexit` handler or other thread runs after it).
//!
//! Stopping mid-call is safe for the evidence: an engine call only reads mapped parts and writes nothing outside the
//! process. The decision and the exit happen under the state lock, and the child disarms under the same lock, so a
//! call is either recorded as finished or reported as stopped, never both. Memory is anonymous memory only, because
//! mapped storage parts (file-backed) can be far larger than the limit and are not the call's allocation. Wall time and
//! memory are host observations outside the claim; this module decides only whether a timing cell finished.

use super::protocol::{
    CallObservation, MEMORY_POLL_INTERVAL_MS, StoppedCall, UNFINISHED_EXIT_CODE, Unfinished, WorkerResult,
};
use super::sampler;
use std::path::PathBuf;
use std::sync::{Arc, Condvar, Mutex, MutexGuard, PoisonError};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

/// What the watchdog enforces and where it reports a stop.
pub(super) struct WatchdogConfig {
    pub call_limit_ns: Option<u64>,
    pub anon_memory_limit_bytes: Option<u64>,
    /// The child's result file.
    pub result_path: PathBuf,
    /// The result written on a stop, without observations (they are added from the recorded calls).
    pub skeleton: WorkerResult,
}

/// The armed call.
struct Armed {
    statement: usize,
    workers: u32,
    repetition: u32,
    started: Instant,
    peak_anon_bytes: Option<u64>,
}

struct State {
    armed: Option<Armed>,
    observations: Vec<CallObservation>,
    shutdown: bool,
}

struct Shared {
    config: WatchdogConfig,
    state: Mutex<State>,
    wake: Condvar,
}

impl Shared {
    fn lock(&self) -> MutexGuard<'_, State> {
        self.state.lock().unwrap_or_else(PoisonError::into_inner)
    }
}

/// The running watchdog of one child (see the module notes).
pub(super) struct Watchdog {
    shared: Arc<Shared>,
    thread: Option<JoinHandle<()>>,
}

impl Watchdog {
    pub fn start(config: WatchdogConfig) -> std::io::Result<Self> {
        let shared = Arc::new(Shared { config, state: Mutex::new(State { armed: None, observations: vec![], shutdown: false }), wake: Condvar::new() });
        let watched = Arc::clone(&shared);
        let thread = std::thread::Builder::new().name("gendb-call-watchdog".into()).spawn(move || watch(&watched))?;
        Ok(Self { shared, thread: Some(thread) })
    }

    /// Arm the watchdog for the call about to start (statement index, worker count, repetition).
    pub fn arm(&self, statement: usize, workers: u32, repetition: u32) {
        let mut state = self.shared.lock();
        state.armed = Some(Armed { statement, workers, repetition, started: Instant::now(), peak_anon_bytes: anon_resident_bytes() });
        drop(state);
        self.shared.wake.notify_one();
    }

    /// Disarm after the call returned: the largest anonymous memory seen during it (absent when unreadable).
    pub fn disarm(&self) -> Option<u64> {
        let mut state = self.shared.lock();
        let armed = state.armed.take()?;
        let at_end = anon_resident_bytes();
        armed.peak_anon_bytes.max(at_end)
    }

    /// Record a finished call's observation (part of the result if a later call is stopped).
    pub fn record(&self, observation: CallObservation) {
        self.shared.lock().observations.push(observation);
    }

    /// Stop the watchdog thread and return every recorded observation, in call order.
    pub fn finish(mut self) -> Vec<CallObservation> {
        self.shared.lock().shutdown = true;
        self.shared.wake.notify_one();
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
        std::mem::take(&mut self.shared.lock().observations)
    }
}

/// The watchdog thread: wait while disarmed; while armed, poll memory at least every poll interval and wake exactly at
/// the time limit; stop the child at the first limit reached (time is checked first).
fn watch(shared: &Shared) {
    let poll = Duration::from_millis(MEMORY_POLL_INTERVAL_MS);
    let config = &shared.config;
    let mut state = shared.lock();
    loop {
        if state.shutdown {
            return;
        }
        let Some(armed) = state.armed.as_mut() else {
            state = shared.wake.wait(state).unwrap_or_else(PoisonError::into_inner);
            continue;
        };
        let elapsed = armed.started.elapsed();
        let anon = anon_resident_bytes();
        armed.peak_anon_bytes = armed.peak_anon_bytes.max(anon);
        let elapsed_ns = u64::try_from(elapsed.as_nanos()).unwrap_or(u64::MAX);
        if let Some(limit) = config.call_limit_ns.filter(|&limit| elapsed_ns >= limit) {
            stop(config, &mut state, Unfinished::OverTimeLimit, elapsed_ns, limit, anon);
        }
        if let Some(limit) = config.anon_memory_limit_bytes.filter(|&limit| anon.is_some_and(|bytes| bytes > limit)) {
            stop(config, &mut state, Unfinished::OverMemoryLimit, elapsed_ns, limit, anon);
        }
        let until_limit = config.call_limit_ns.map_or(poll, |limit| Duration::from_nanos(limit.saturating_sub(elapsed_ns)));
        state = shared.wake.wait_timeout(state, poll.min(until_limit)).unwrap_or_else(PoisonError::into_inner).0;
    }
}

/// Write the result so far with the stopped call and end the process (holding the state lock, so the child cannot
/// record the call as finished meanwhile). A result that cannot be written ends the child with exit status 1 and the
/// reason on stderr (the parent then reports a child that ended without a result).
fn stop(config: &WatchdogConfig, state: &mut State, reason: fn(StoppedCall) -> Unfinished, elapsed_ns: u64, limit: u64, anon: Option<u64>) -> ! {
    let armed = state.armed.as_ref().expect("stop is called while a call is armed");
    let call = StoppedCall {
        statement: armed.statement,
        workers: armed.workers,
        repetition: armed.repetition,
        elapsed_ns,
        limit,
        anon_bytes: anon,
        peak_anon_bytes: armed.peak_anon_bytes,
        samples: sampler::stop_active_call(),
    };
    let mut result = config.skeleton.clone();
    result.observations = std::mem::take(&mut state.observations);
    result.unfinished = Some(reason(call));
    let written = serde_json::to_vec_pretty(&result)
        .map_err(|e| e.to_string())
        .and_then(|bytes| std::fs::write(&config.result_path, bytes).map_err(|e| format!("{}: {e}", config.result_path.display())));
    let status = match written {
        Ok(()) => i32::from(UNFINISHED_EXIT_CODE),
        Err(error) => {
            eprintln!("the watchdog stopped a call at its limit but could not write the result: {error}");
            1
        }
    };
    // SAFETY: `_exit` ends the process immediately; nothing after it runs, and no lock or file is left for a later
    // reader (the result file is complete and closed).
    unsafe { libc::_exit(status) }
}

/// `RssAnon` of `/proc/self/status` in bytes (the kernel's anonymous resident page counter), or `None`.
fn anon_resident_bytes() -> Option<u64> {
    parse_rss_anon(&std::fs::read_to_string("/proc/self/status").ok()?)
}

/// `RssAnon:   <n> kB` of a `/proc/<pid>/status` text, in bytes.
pub(super) fn parse_rss_anon(status: &str) -> Option<u64> {
    let line = status.lines().find_map(|line| line.strip_prefix("RssAnon:"))?;
    let kib: u64 = line.trim().strip_suffix("kB")?.trim().parse().ok()?;
    kib.checked_mul(1024)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rss_anon_is_read_in_bytes() {
        let status = "Name:\tgendb\nVmRSS:\t  2048 kB\nRssAnon:\t    1536 kB\nRssFile:\t     512 kB\n";
        assert_eq!(parse_rss_anon(status), Some(1536 * 1024));
        assert_eq!(parse_rss_anon("VmRSS:\t2048 kB\n"), None);
        assert_eq!(parse_rss_anon("RssAnon:\tlots kB\n"), None);
        assert!(anon_resident_bytes().is_some_and(|bytes| bytes > 0), "this process has anonymous memory");
    }
}
