//! The quiet-moment gate before each timing pair of an interleaved timing. The host is shared with other services: in one run's
//! attempt the 1-minute load average rose from 8 to 21 during the race and the parent itself went over the call limit
//! on cells it had finished in 10–50 s before.
//!
//! Before a pair's children run, [`QuietGate::wait`] waits until the host's 1-minute load average is below
//! [`QuietGate::threshold`] ([`QUIET_LOAD_FRACTION`] of the CPUs this process may use: 16 on the 64-CPU host),
//! reading `/proc/loadavg` every [`QUIET_POLL`]. It waits at most [`QUIET_MAX_WAIT`]; then the pair is timed anyway and
//! the record says so ([`QuietWait::timed_out`]). The wait is recorded with the pair (`engine::race::RacePair`); the
//! load average read under the timing lease is recorded as before.
//!
//! The gate waits **before** the timing lease is taken (`engine::race`): the exclusive lease stops every author's shell
//! command on the host (`query::host_locks`), so holding it through a wait of up to ten minutes would stall every live
//! session. GenDB's own builds still run during the wait; the lease then waits for them as before.
//!
//! The clock is a parameter ([`Clock`]), so the wait and its timeout are tested with a fake clock and fake loads.

use super::timing::LoadAverage;
use serde::{Deserialize, Serialize};
use std::time::{Duration, Instant};

/// The gate's threshold as a fraction of the CPUs: 16 load units on this 64-CPU host.
pub const QUIET_LOAD_FRACTION: f64 = 0.25;
/// The longest wait before a pair is timed anyway.
pub const QUIET_MAX_WAIT: Duration = Duration::from_secs(600);
/// How often the load average is read while waiting.
pub const QUIET_POLL: Duration = Duration::from_secs(15);

/// Time as the gate sees it: elapsed time since the gate started, and a sleep.
pub trait Clock {
    fn elapsed(&self) -> Duration;
    fn sleep(&self, duration: Duration);
}

/// The host's monotonic clock, started when made.
pub struct HostClock(Instant);

impl HostClock {
    pub fn start() -> Self {
        Self(Instant::now())
    }
}

impl Clock for HostClock {
    fn elapsed(&self) -> Duration {
        self.0.elapsed()
    }

    fn sleep(&self, duration: Duration) {
        std::thread::sleep(duration);
    }
}

/// The gate: wait until the 1-minute load average is below `threshold`, at most `max_wait`, reading it every `poll`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct QuietGate {
    /// Load units (`/proc/loadavg`'s 1-minute field).
    pub threshold: f64,
    pub max_wait: Duration,
    pub poll: Duration,
}

/// One wait of the gate before one pair, as the race records it.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct QuietWait {
    /// The gate's threshold on the 1-minute load average (load units) and its longest wait in ms.
    pub threshold_one_minute: f64,
    pub max_wait_ms: u64,
    /// The 1-minute load average at the first reading and at the last (`None`: `/proc/loadavg` unreadable, no wait).
    pub first_one_minute: Option<f64>,
    pub last_one_minute: Option<f64>,
    /// Wall time spent waiting, in ms (0 when the host was quiet at once).
    pub waited_ms: u64,
    /// The host was not quiet within `max_wait_ms`: the pair was timed anyway.
    pub timed_out: bool,
}

impl QuietGate {
    /// The gate of this host: [`QUIET_LOAD_FRACTION`] of the CPUs this process may use (`available_parallelism`, which
    /// respects the CPU affinity; 1 when unknown), [`QUIET_MAX_WAIT`], [`QUIET_POLL`].
    pub fn for_host() -> Self {
        let cpus = std::thread::available_parallelism().map_or(1, |n| n.get());
        Self { threshold: QUIET_LOAD_FRACTION * cpus as f64, max_wait: QUIET_MAX_WAIT, poll: QUIET_POLL }
    }

    /// Wait until `load()` reports a 1-minute load average below the threshold, or until `max_wait` has passed on
    /// `clock` (then `timed_out`). An unreadable load average ends the wait at once (nothing to wait on; recorded).
    pub fn wait(&self, load: impl Fn() -> Option<LoadAverage>, clock: &impl Clock) -> QuietWait {
        let started = clock.elapsed();
        let mut record = QuietWait {
            threshold_one_minute: self.threshold,
            max_wait_ms: self.max_wait.as_millis() as u64,
            first_one_minute: None,
            last_one_minute: None,
            waited_ms: 0,
            timed_out: false,
        };
        loop {
            let now = load().map(|l| l.one_minute);
            record.first_one_minute = record.first_one_minute.or(now);
            record.last_one_minute = now;
            let waited = clock.elapsed().saturating_sub(started);
            record.waited_ms = waited.as_millis() as u64;
            match now {
                None => return record,
                Some(one_minute) if one_minute < self.threshold => return record,
                Some(_) if waited >= self.max_wait => {
                    record.timed_out = true;
                    return record;
                }
                Some(_) => clock.sleep(self.poll.min(self.max_wait - waited)),
            }
        }
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::engine::timing::parse_load_average;
    use std::cell::{Cell, RefCell};

    /// A clock that only moves when slept on.
    #[derive(Default)]
    pub(crate) struct FakeClock {
        now: Cell<Duration>,
        pub(crate) sleeps: RefCell<Vec<Duration>>,
    }

    impl Clock for FakeClock {
        fn elapsed(&self) -> Duration {
            self.now.get()
        }

        fn sleep(&self, duration: Duration) {
            self.sleeps.borrow_mut().push(duration);
            self.now.set(self.now.get() + duration);
        }
    }

    const GATE: QuietGate = QuietGate { threshold: 16.0, max_wait: Duration::from_secs(600), poll: Duration::from_secs(15) };

    /// Loads read in order from `values` (the last one repeats).
    fn loads(values: &[f64]) -> impl Fn() -> Option<LoadAverage> + '_ {
        let next = Cell::new(0usize);
        move || {
            let i = next.get().min(values.len() - 1);
            next.set(next.get() + 1);
            parse_load_average(&format!("{} 5.00 5.00 1/100 7", values[i]))
        }
    }

    /// The threshold is a quarter of the CPUs: 16 on a 64-CPU host.
    #[test]
    fn the_threshold_is_a_quarter_of_the_cpus() {
        let cpus = std::thread::available_parallelism().map_or(1, |n| n.get()) as f64;
        assert_eq!(QuietGate::for_host().threshold, cpus / 4.0);
        assert_eq!((QuietGate::for_host().max_wait, QuietGate::for_host().poll), (Duration::from_secs(600), Duration::from_secs(15)));
    }

    /// A quiet host is timed at once; a busy one is read every poll until the load drops below the threshold, and the
    /// wait is recorded.
    #[test]
    fn the_gate_waits_until_the_load_drops() {
        let clock = FakeClock::default();
        let quiet = GATE.wait(loads(&[8.0]), &clock);
        assert_eq!((quiet.waited_ms, quiet.timed_out, quiet.first_one_minute, quiet.last_one_minute), (0, false, Some(8.0), Some(8.0)));
        assert!(clock.sleeps.borrow().is_empty());
        let clock = FakeClock::default();
        let waited = GATE.wait(loads(&[21.0, 18.5, 16.0, 15.9]), &clock);
        assert_eq!((waited.waited_ms, waited.timed_out, waited.first_one_minute, waited.last_one_minute), (45_000, false, Some(21.0), Some(15.9)), "16.0 is not below 16");
        assert_eq!(*clock.sleeps.borrow(), [Duration::from_secs(15); 3]);
        assert_eq!(waited.threshold_one_minute, 16.0);
    }

    /// A host that stays busy is timed anyway after the longest wait, which is never overshot; an unreadable load
    /// average does not wait.
    #[test]
    fn the_gate_times_out_after_ten_minutes() {
        let clock = FakeClock::default();
        let gate = QuietGate { poll: Duration::from_secs(70), ..GATE };
        let busy = gate.wait(loads(&[30.0]), &clock);
        assert_eq!((busy.waited_ms, busy.timed_out, busy.last_one_minute, busy.max_wait_ms), (600_000, true, Some(30.0), 600_000));
        let sleeps = clock.sleeps.borrow();
        assert_eq!((sleeps.len(), *sleeps.last().unwrap()), (9, Duration::from_secs(40)), "8 polls of 70 s, then the 40 s left");
        let clock = FakeClock::default();
        let unreadable = GATE.wait(|| None, &clock);
        assert_eq!((unreadable.waited_ms, unreadable.timed_out, unreadable.first_one_minute), (0, false, None));
    }
}
