//! Interleaved timing of two engine versions in one window (same-window
//! relative performance only, never absolute medians compared across time on this shared host).
//!
//! The two sides are the **parent** (the incumbent: a branch head, or the main-line head when a branch head challenges
//! it) and the **candidate**. Every official cell (template at the timing binding x worker count) is run
//! for both sides back to back, each in a fresh worker child through its own [`EngineCellRunner`], with the order
//! alternating across consecutive cells (parent first, then candidate first: ABBA). Each side of a cell makes the
//! setup's calls ([`RaceSetup::calls`], the evaluation plan's, `super::protocol`: 1 warm + 1 hot in development, where
//! the hot call's time is the cell's time and a warm call over the limit ends the cell unfinished with no hot call).
//!
//! Each pair first passes the **quiet-moment gate** (`super::quiet`: it waits, at most ten minutes, until the
//! host's 1-minute load average is below a quarter of the CPUs; the wait is recorded with the pair), then takes one
//! exclusive timing lease (the host's `HostLocks::timing`, the same queue every timing on the host shares) for both of
//! its children; the load average (`/proc/loadavg`) is recorded after the lease is taken, before the first child.
//!
//! Skips (each saves up to one call limit per call):
//! - when the parent's record at this scale says the cell did not finish, the parent is not run again: only the
//!   candidate runs, and the parent keeps its recorded state (whether the candidate finishes or not);
//! - when the candidate ran first and did not finish, and the parent's record says the cell finished, the parent is not
//!   run again: the finished count decides that cell, and the parent's recorded median stands in (from another window;
//!   it can matter only when the finished counts tie overall).
//!
//! **Re-timing**. The
//! host is shared with other services, and a burst of their load can push a cell over the call limit: then the finished
//! counts, which decide first, are decided by the host. After the main pass every pair is checked against the parent's
//! recorded time `R` for the cell at this scale and binding ([`suspicion`]); a pair is **suspicious** when a side run in
//! this window
//! - did not finish while `R` is below the call limit (whatever `R` is, so a cell recorded near the
//!   limit is re-timed too); or
//! - took more than `2 R` while `R` is below half the call limit.
//!
//! The candidate has no record of its own at the scale, so the parent's recorded time stands in for it (the version it
//! builds on). Without a finished parent record there is no reference and nothing is suspicious. Every suspicious pair
//! is timed again once at the end of the race, in the same way (the gate, one lease, the skips; the order alternating
//! across the re-timed pairs), and its re-timed result is used; the pair keeps its first result and the reason
//! ([`Retimed`]). Nothing is re-timed twice. [`retime_recorded`] applies the same re-timing to the pairs of an earlier
//! race of the same two versions (`gendb engine re-evaluate`, `super::re_evaluation`).
//!
//! Every side's cell is scored with `super::score` against the saved baselines; the candidate wins when its score is
//! better ([`super::score::Score::is_better_than`]). A runner error (an answer the saved answers do not allow, a tool
//! failure) ends the comparison with that side named ([`RaceError`]): a wrong answer refuses the submission and is
//! flagged for the operator. Times are wall times in the children; no performance claim.

use super::quiet::QuietWait;
use super::score::{CellResult, CellStatus, ScaleScore, ScoreError, score};
use super::timing::{CellRecord, CellRequest, CellTiming, EngineCellRunner, EngineStatement, LoadAverage, UnfinishedCell, read_cell};
use super::totals::Baselines;
use crate::controller::records::{now_unix_ms, read_json};
use gendb_verification::admission::AdmissionError;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::path::{Path, PathBuf};

/// The comparison rule as recorded with every report.
pub const RACE_RULE: &str = "same-window interleaved timing: per official cell, parent and candidate in fresh children back to back under one \
timing lease, each side 1 warm call then the evaluation plan's hot calls (calls_per_cell; the cell's time the median hot call, and a warm call \
over the limit ends the cell unfinished), the order alternating across consecutive cells (ABBA); before each pair GenDB waits (at most 10 minutes, \
before the lease) until the host's 1-minute load average is below a quarter of the CPUs, and records the wait and the load average; a parent recorded as \
unfinished at this scale is not run again, nor is a parent recorded as finished when the candidate (run first) did not finish; after the main pass a pair \
is timed again once, in the same way, when a side did not finish while the parent's recorded time for the cell is below the limit, or took more than twice \
that time while it is below half the limit (the parent's recorded time stands in for the candidate), and the re-timed \
result is used (both kept); the candidate is accepted when its score is better (more finished cells, or as many and a smaller normalized time)";

/// One side of the comparison.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Side {
    Parent,
    Candidate,
}

/// One version in the comparison: its name in records and the runner of its cells.
pub struct Contender<'a, R> {
    pub version: &'a str,
    pub runner: &'a R,
}

/// What the comparison runs.
pub struct RaceSetup<'a> {
    /// The official statements: every template at the timing binding (one binding for all).
    pub statements: &'a [EngineStatement],
    pub workers: &'a [usize],
    pub baselines: &'a Baselines,
    /// The call limit the runners apply (unfinished cells count it; timed cells are judged against it).
    pub call_limit_ns: u64,
    /// Calls per side of a cell, the first warm (`super::protocol::EvaluationPlan::cell_calls`).
    pub calls: u32,
    /// The parent's recorded cells at this scale (its official timing or its last comparison), for the skips and the
    /// re-timing rule; `None` when it has no record at this scale (then it always runs, and nothing is re-timed).
    pub parent_record: Option<&'a [CellResult]>,
    /// Evidence root: `<work>/<statement>/w<workers>/{parent,candidate}`, re-timed pairs under `<work>/retime/`.
    pub work: &'a Path,
}

/// What the host gives a comparison: its timing lease, its load average and its quiet-moment gate
/// (`super::quiet::QuietGate::wait`; `None`: no gate, as in tests).
pub struct RaceHost<L, A, Q> {
    pub timing_lease: L,
    pub load_average: A,
    pub wait_for_quiet: Q,
}

/// How a side's cell state was obtained.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SideSource {
    /// Run in this window.
    Measured,
    /// Taken from the parent's record at this scale (a skip).
    ParentRecord,
}

/// One side's cell.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct SideCell {
    pub status: CellStatus,
    pub source: SideSource,
    /// The measured cell (absent when taken from the record).
    pub timed: Option<CellTiming>,
    pub unfinished: Option<UnfinishedCell>,
}

impl SideCell {
    fn measured(record: CellRecord, call_limit_ns: u64) -> Self {
        match record {
            CellRecord::Timed(timing) => Self { status: timing.status(Some(call_limit_ns)), source: SideSource::Measured, timed: Some(timing), unfinished: None },
            CellRecord::Unfinished(cell) => {
                Self { status: CellStatus::Unfinished { reason: cell.reason }, source: SideSource::Measured, timed: None, unfinished: Some(cell) }
            }
        }
    }

    fn recorded(status: CellStatus) -> Self {
        Self { status, source: SideSource::ParentRecord, timed: None, unfinished: None }
    }
}

/// One timing of one cell pair: the gate's wait, the order the children ran in, the load average before them, both
/// sides, and the candidate/parent median ratio when both finished (report only).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct PairTiming {
    /// The sides run in this window, in run order (one side when the parent was skipped).
    pub run_order: Vec<Side>,
    pub load_average: Option<LoadAverage>,
    /// The quiet-moment gate's wait before the pair (absent in races timed before the gate existed).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub quiet_wait: Option<QuietWait>,
    pub parent: SideCell,
    pub candidate: SideCell,
    pub candidate_over_parent: Option<f64>,
}

/// A pair's first timing when it was timed again (module documentation), and why.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct Retimed {
    pub reason: String,
    pub first_pass: PairTiming,
}

/// One cell of the comparison: the timing used (the re-timed one when `retimed` is set). Its record has the timing's
/// fields at the top level (`PairRecord`), as every reader of `race.json` expects.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
#[serde(from = "PairRecord", into = "PairRecord")]
pub struct RacePair {
    pub template: String,
    pub binding: String,
    pub workers: usize,
    pub timing: PairTiming,
    pub retimed: Option<Retimed>,
}

/// A pair as `race.json` holds it: the timing's fields beside the cell's. (Spelled out rather than `#[serde(flatten)]`,
/// which cannot read this workspace's numbers back: serde_json's `arbitrary_precision` buffers them as maps.)
#[derive(Clone, Serialize, Deserialize)]
struct PairRecord {
    template: String,
    binding: String,
    workers: usize,
    run_order: Vec<Side>,
    load_average: Option<LoadAverage>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    quiet_wait: Option<QuietWait>,
    parent: SideCell,
    candidate: SideCell,
    candidate_over_parent: Option<f64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    retimed: Option<Retimed>,
}

impl From<PairRecord> for RacePair {
    fn from(r: PairRecord) -> Self {
        let timing = PairTiming { run_order: r.run_order, load_average: r.load_average, quiet_wait: r.quiet_wait, parent: r.parent, candidate: r.candidate, candidate_over_parent: r.candidate_over_parent };
        Self { template: r.template, binding: r.binding, workers: r.workers, timing, retimed: r.retimed }
    }
}

impl From<RacePair> for PairRecord {
    fn from(p: RacePair) -> Self {
        let t = p.timing;
        Self { template: p.template, binding: p.binding, workers: p.workers, run_order: t.run_order, load_average: t.load_average, quiet_wait: t.quiet_wait, parent: t.parent,
            candidate: t.candidate, candidate_over_parent: t.candidate_over_parent, retimed: p.retimed }
    }
}

/// The earlier race whose pairs a report reuses ([`retime_recorded`]).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct ReusedPairs {
    pub race: PathBuf,
    pub window_start_unix_ms: u64,
    pub window_end_unix_ms: u64,
    pub pairs: usize,
}

/// The comparison of two versions in one window.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct RaceReport {
    pub parent: String,
    pub candidate: String,
    pub binding: String,
    /// The window of this report's timings (a re-evaluation's: its re-timing only; `reused` names the earlier one).
    pub window_start_unix_ms: u64,
    pub window_end_unix_ms: u64,
    pub pairs: Vec<RacePair>,
    /// Calls per side of a cell, the first warm.
    pub calls_per_cell: u32,
    pub parent_score: ScaleScore,
    pub candidate_score: ScaleScore,
    /// The candidate's score is better than the parent's.
    pub candidate_better: bool,
    /// Children run in this report's window (the main pass and the re-timing), and parent children skipped there by the
    /// rules above.
    pub children_run: usize,
    pub parent_children_skipped: usize,
    /// Pairs timed again (module documentation); each such pair keeps its first result under `retimed`.
    pub retimed_pairs: usize,
    /// The earlier race whose pairs were reused (a re-evaluation); absent for a race timed whole.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reused: Option<ReusedPairs>,
    pub rule: &'static str,
}

/// An earlier race read back for re-timing ([`retime_recorded`]): who was timed, how, and every pair.
#[derive(Clone, Debug, Deserialize)]
pub struct RecordedRace {
    #[serde(skip)]
    pub file: PathBuf,
    pub parent: String,
    pub binding: String,
    pub calls_per_cell: u32,
    pub window_start_unix_ms: u64,
    pub window_end_unix_ms: u64,
    pub pairs: Vec<RacePair>,
}

impl RecordedRace {
    /// The race recorded at `file` (a `race.json` written from a [`RaceReport`]).
    pub fn read(file: &Path) -> Result<Self, String> {
        let mut race: Self = read_json(file).map_err(|e| e.to_string())?;
        race.file = file.to_path_buf();
        Ok(race)
    }
}

/// Why a comparison ended without a report.
#[derive(Debug)]
pub enum RaceError {
    /// A side's cell runner failed (an answer the saved answers do not allow, a refused statement, a tool failure).
    Cell { side: Side, version: String, template: String, workers: usize, error: AdmissionError },
    /// The timing lease could not be taken.
    Lease(String),
    /// The cells could not be scored (missing baselines, malformed setup).
    Score(ScoreError),
}

impl fmt::Display for RaceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Cell { side, version, template, workers, error } => write!(f, "{side:?} {version}: {template} at {workers} workers: {error}"),
            Self::Lease(reason) => write!(f, "timing lease: {reason}"),
            Self::Score(error) => write!(f, "score: {error}"),
        }
    }
}

impl std::error::Error for RaceError {}

impl From<ScoreError> for RaceError {
    fn from(error: ScoreError) -> Self {
        Self::Score(error)
    }
}

/// Whether the pair `timing` is suspicious under the re-timing rule (module documentation), given the parent's recorded
/// state of the cell at this scale and the call limit: the reason when it is. Only sides run in this window count.
pub fn suspicion(timing: &PairTiming, parent_recorded: Option<CellStatus>, call_limit_ns: u64) -> Option<String> {
    let Some(CellStatus::Finished { median_ns: recorded }) = parent_recorded else { return None };
    if recorded >= call_limit_ns {
        return None;
    }
    let seconds = |ns: u64| format!("{:.1} s", ns as f64 / 1e9);
    let twice = recorded.saturating_mul(2);
    let suspicious: Vec<String> = [("the parent", &timing.parent), ("the candidate", &timing.candidate)]
        .into_iter()
        .filter(|(_, side)| side.source == SideSource::Measured)
        .filter_map(|(name, side)| match side.status {
            CellStatus::Unfinished { .. } => Some(format!("{name} did not finish")),
            CellStatus::Finished { median_ns } | CellStatus::Unchecked { median_ns } if twice < call_limit_ns && median_ns > twice => {
                Some(format!("{name} took {}, more than twice the recorded time", seconds(median_ns)))
            }
            _ => None,
        })
        .collect();
    (!suspicious.is_empty())
        .then(|| format!("{}; the parent's recorded time for this cell is {}, below the {} limit", suspicious.join(" and "), seconds(recorded), seconds(call_limit_ns)))
}

/// Children run and parent children skipped.
#[derive(Clone, Copy, Debug, Default)]
struct Counts {
    children_run: usize,
    parent_children_skipped: usize,
}

/// The parent's recorded state of every cell at this scale.
fn recorded_statuses(record: Option<&[CellResult]>) -> BTreeMap<(String, usize), CellStatus> {
    record.into_iter().flatten().map(|c| ((c.template.clone(), c.workers), c.status)).collect()
}

/// Time `parent` and `candidate` interleaved over every official cell of `setup` (see the module notes), each pair after
/// the host's quiet-moment gate and under one timing lease, the load average recorded before each pair; re-time the
/// suspicious pairs once; and score both.
pub fn race<P: EngineCellRunner, C: EngineCellRunner, Lease>(
    setup: &RaceSetup<'_>,
    parent: Contender<'_, P>,
    candidate: Contender<'_, C>,
    host: &RaceHost<impl Fn() -> Result<Lease, String>, impl Fn() -> Option<LoadAverage>, impl Fn() -> Option<QuietWait>>,
) -> Result<RaceReport, RaceError> {
    let binding = official_binding(setup.statements)?;
    let recorded = recorded_statuses(setup.parent_record);
    let window_start_unix_ms = now_unix_ms();
    let mut counts = Counts::default();
    let mut pairs = Vec::new();
    for (index, (statement, workers)) in setup.statements.iter().flat_map(|s| setup.workers.iter().map(move |&w| (s, w))).enumerate() {
        let parent_recorded = recorded.get(&(statement.template.clone(), workers)).copied();
        let dir = setup.work.join(statement.name()).join(format!("w{workers}"));
        let timing = run_pair(setup, &parent, &candidate, statement, workers, index % 2 == 0, parent_recorded, &dir, host, &mut counts)?;
        pairs.push(RacePair { template: statement.template.clone(), binding: statement.binding.clone(), workers, timing, retimed: None });
    }
    retime_and_score(setup, &binding, &parent, &candidate, pairs, &recorded, counts, window_start_unix_ms, None, host)
}

/// The re-timing of an earlier race of the same two versions (`recorded`, at this scale and binding, every official
/// cell of `setup`): its suspicious pairs (module documentation) timed again once, the others kept as recorded, and both
/// sides scored over the result. A pair already re-timed is not timed again.
pub fn retime_recorded<P: EngineCellRunner, C: EngineCellRunner, Lease>(
    setup: &RaceSetup<'_>,
    parent: Contender<'_, P>,
    candidate: Contender<'_, C>,
    recorded_race: RecordedRace,
    host: &RaceHost<impl Fn() -> Result<Lease, String>, impl Fn() -> Option<LoadAverage>, impl Fn() -> Option<QuietWait>>,
) -> Result<RaceReport, RaceError> {
    let binding = official_binding(setup.statements)?;
    let malformed = |what: String| RaceError::Score(ScoreError(format!("{}: {what}", recorded_race.file.display())));
    if recorded_race.parent != parent.version || recorded_race.binding != binding || recorded_race.calls_per_cell != setup.calls {
        return Err(malformed(format!(
            "the recorded race timed parent {} at binding {} with {} calls per cell, not {} at {binding} with {}",
            recorded_race.parent, recorded_race.binding, recorded_race.calls_per_cell, parent.version, setup.calls
        )));
    }
    let cells: BTreeSet<(String, usize)> = setup.statements.iter().flat_map(|s| setup.workers.iter().map(move |&w| (s.template.clone(), w))).collect();
    let recorded_cells: BTreeSet<(String, usize)> = recorded_race.pairs.iter().map(|p| (p.template.clone(), p.workers)).collect();
    if cells != recorded_cells || recorded_race.pairs.len() != cells.len() {
        return Err(malformed("the recorded pairs are not exactly the official cells of this scale".into()));
    }
    let reused = ReusedPairs {
        race: recorded_race.file.clone(),
        window_start_unix_ms: recorded_race.window_start_unix_ms,
        window_end_unix_ms: recorded_race.window_end_unix_ms,
        pairs: recorded_race.pairs.len(),
    };
    let recorded = recorded_statuses(setup.parent_record);
    retime_and_score(setup, &binding, &parent, &candidate, recorded_race.pairs, &recorded, Counts::default(), now_unix_ms(), Some(reused), host)
}

/// Re-time the suspicious pairs of `pairs` once (module documentation) and score both sides.
#[allow(clippy::too_many_arguments)]
fn retime_and_score<P: EngineCellRunner, C: EngineCellRunner, Lease>(
    setup: &RaceSetup<'_>,
    binding: &str,
    parent: &Contender<'_, P>,
    candidate: &Contender<'_, C>,
    mut pairs: Vec<RacePair>,
    recorded: &BTreeMap<(String, usize), CellStatus>,
    mut counts: Counts,
    window_start_unix_ms: u64,
    reused: Option<ReusedPairs>,
    host: &RaceHost<impl Fn() -> Result<Lease, String>, impl Fn() -> Option<LoadAverage>, impl Fn() -> Option<QuietWait>>,
) -> Result<RaceReport, RaceError> {
    let suspicious: Vec<(usize, String)> = pairs
        .iter()
        .enumerate()
        .filter(|(_, pair)| pair.retimed.is_none())
        .filter_map(|(i, pair)| suspicion(&pair.timing, recorded.get(&(pair.template.clone(), pair.workers)).copied(), setup.call_limit_ns).map(|reason| (i, reason)))
        .collect();
    for (k, (i, reason)) in suspicious.iter().enumerate() {
        let (template, workers) = (pairs[*i].template.clone(), pairs[*i].workers);
        let statement = setup.statements.iter().find(|s| s.template == template).ok_or_else(|| ScoreError(format!("pair {template} is not an official statement")))?;
        let dir = setup.work.join("retime").join(statement.name()).join(format!("w{workers}"));
        let parent_recorded = recorded.get(&(template.clone(), workers)).copied();
        let timing = run_pair(setup, parent, candidate, statement, workers, k % 2 == 0, parent_recorded, &dir, host, &mut counts)?;
        let first_pass = std::mem::replace(&mut pairs[*i].timing, timing);
        pairs[*i].retimed = Some(Retimed { reason: reason.clone(), first_pass });
    }
    let window_end_unix_ms = now_unix_ms();
    let results = |pick: fn(&PairTiming) -> &SideCell| -> Vec<CellResult> {
        pairs.iter().map(|p| CellResult { template: p.template.clone(), workers: p.workers, status: pick(&p.timing).status }).collect()
    };
    let parent_score = score(setup.baselines, binding, setup.workers, setup.call_limit_ns, &results(|t| &t.parent))?;
    let candidate_score = score(setup.baselines, binding, setup.workers, setup.call_limit_ns, &results(|t| &t.candidate))?;
    Ok(RaceReport {
        parent: parent.version.to_string(),
        candidate: candidate.version.to_string(),
        binding: binding.to_string(),
        window_start_unix_ms,
        window_end_unix_ms,
        candidate_better: candidate_score.score.is_better_than(&parent_score.score),
        retimed_pairs: pairs.iter().filter(|p| p.retimed.is_some()).count(),
        pairs,
        calls_per_cell: setup.calls,
        parent_score,
        candidate_score,
        children_run: counts.children_run,
        parent_children_skipped: counts.parent_children_skipped,
        reused,
        rule: RACE_RULE,
    })
}

/// Time one cell pair (module documentation): the gate, then one lease for both children, the load average, the sides
/// in order (parent first when `parent_first`) under the skip rules, evidence under `dir`.
#[allow(clippy::too_many_arguments)]
fn run_pair<P: EngineCellRunner, C: EngineCellRunner, Lease>(
    setup: &RaceSetup<'_>,
    parent: &Contender<'_, P>,
    candidate: &Contender<'_, C>,
    statement: &EngineStatement,
    workers: usize,
    parent_first: bool,
    parent_recorded: Option<CellStatus>,
    dir: &Path,
    host: &RaceHost<impl Fn() -> Result<Lease, String>, impl Fn() -> Option<LoadAverage>, impl Fn() -> Option<QuietWait>>,
    counts: &mut Counts,
) -> Result<PairTiming, RaceError> {
    let cell = CellRequest { statement, workers, calls: setup.calls };
    let order = match parent_recorded {
        Some(status) if !status.is_finished() => vec![Side::Candidate],
        _ if parent_first => vec![Side::Parent, Side::Candidate],
        _ => vec![Side::Candidate, Side::Parent],
    };
    let quiet_wait = (host.wait_for_quiet)();
    let _lease = (host.timing_lease)().map_err(RaceError::Lease)?;
    let load_average = (host.load_average)();
    let (mut parent_cell, mut candidate_cell, mut run_order) = (None, None, vec![]);
    for side in order {
        let candidate_unfinished = candidate_cell.as_ref().is_some_and(|c: &SideCell| !c.status.is_finished());
        if side == Side::Parent && candidate_unfinished && parent_recorded.is_some_and(|s| s.is_finished()) {
            continue;
        }
        let (version, record) = match side {
            Side::Parent => (parent.version, parent.runner.run_cell(cell, &dir.join("parent"))),
            Side::Candidate => (candidate.version, candidate.runner.run_cell(cell, &dir.join("candidate"))),
        };
        let measured = record.and_then(|r| read_cell(cell, r)).map_err(|error| RaceError::Cell {
            side,
            version: version.to_string(),
            template: statement.template.clone(),
            workers,
            error,
        })?;
        let measured = SideCell::measured(measured, setup.call_limit_ns);
        match side {
            Side::Parent => parent_cell = Some(measured),
            Side::Candidate => candidate_cell = Some(measured),
        }
        run_order.push(side);
        counts.children_run += 1;
    }
    let parent_cell = match parent_cell {
        Some(cell) => cell,
        None => {
            counts.parent_children_skipped += 1;
            SideCell::recorded(parent_recorded.expect("the parent is skipped only when it has a record"))
        }
    };
    let candidate_cell = candidate_cell.expect("the candidate runs in every pair");
    let candidate_over_parent = match (parent_cell.status, candidate_cell.status) {
        (CellStatus::Finished { median_ns: p }, CellStatus::Finished { median_ns: c }) => Some(c as f64 / p.max(1) as f64),
        _ => None,
    };
    Ok(PairTiming { run_order, load_average, quiet_wait, parent: parent_cell, candidate: candidate_cell, candidate_over_parent })
}

/// The one binding of the official statements (templates only, one binding).
fn official_binding(statements: &[EngineStatement]) -> Result<String, RaceError> {
    let first = statements.first().ok_or_else(|| ScoreError("a comparison needs at least one statement".into()))?;
    if statements.iter().any(|s| s.variant.is_some() || s.binding != first.binding) {
        return Err(ScoreError("a comparison runs the official statements: templates only, all at the timing binding".into()).into());
    }
    Ok(first.binding.clone())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::protocol::{DEVELOPMENT, FINAL};
    use crate::engine::timing::parse_load_average;
    use gendb_runtime::worker::UnfinishedReason;
    use serde_json::{Value, json};
    use std::cell::RefCell;

    const TARGETS: &str = r#"{
        "Q01": {"v0": {"1": {"duckdb_ms": 10, "umbra_ms": 8, "target_ms": 8, "agreement": "exact-order"},
                       "32": {"duckdb_ms": 2, "umbra_ms": 3, "target_ms": 2, "agreement": "exact-order"}}},
        "Q02": {"v0": {"1": {"duckdb_ms": 20, "umbra_ms": 4, "target_ms": 4, "agreement": "exact-order"},
                       "32": {"duckdb_ms": 1, "umbra_ms": 1, "target_ms": 1, "agreement": "exact-order"}}}
    }"#;
    const LIMIT: u64 = 1_000_000_000;
    const MS: u64 = 1_000_000;

    /// The shared log of both canned runners and the gate: `side template w<workers> leases=<held>[ retime]`, and
    /// `quiet leases=<held>` for each wait of the gate.
    struct Log {
        lines: RefCell<Vec<String>>,
        leases: RefCell<u32>,
    }

    /// A canned side: each cell's record from `cell(template, workers, n)`, `n` counting this side's earlier runs of
    /// the cell: `Some(median)` finished (every hot call of the cell's calls equal to it), `None` stopped at the time
    /// limit in its warm call.
    struct Canned<'a> {
        side: &'static str,
        log: &'a Log,
        cell: fn(&str, usize, u32) -> Option<u64>,
        runs: RefCell<BTreeMap<(String, usize), u32>>,
    }

    fn canned<'a>(side: &'static str, log: &'a Log, cell: fn(&str, usize, u32) -> Option<u64>) -> Canned<'a> {
        Canned { side, log, cell, runs: RefCell::new(BTreeMap::new()) }
    }

    impl EngineCellRunner for Canned<'_> {
        fn run_cell(&self, cell: CellRequest<'_>, work: &Path) -> Result<Value, AdmissionError> {
            let name = cell.statement.name();
            assert!(work.ends_with(format!("{name}/w{}/{}", cell.workers, self.side)), "{}", work.display());
            let retime = if work.components().any(|c| c.as_os_str() == "retime") { " retime" } else { "" };
            self.log.lines.borrow_mut().push(format!("{} {name} w{} leases={}{retime}", self.side, cell.workers, self.log.leases.borrow()));
            let n = {
                let mut runs = self.runs.borrow_mut();
                let n = runs.entry((name.to_string(), cell.workers)).or_default();
                *n += 1;
                *n - 1
            };
            Ok(match (self.cell)(name, cell.workers, n) {
                Some(median) => json!({"status":"saved_answers_agree","warm_wall_ns":median,"hot_wall_ns":vec![median; cell.calls as usize - 1],"median_hot_wall_ns":median}),
                None => json!({"status":"unfinished","warm_wall_ns":null,"hot_wall_ns":[],"median_hot_wall_ns":null,
                    "unfinished":{"reason":"over_time_limit","statement":0,"workers":cell.workers,"repetition":0,"elapsed_ns":LIMIT,"limit":LIMIT,"anon_bytes":null,"peak_anon_bytes":null}}),
            })
        }
    }

    struct Lease<'a>(&'a RefCell<u32>);
    impl Drop for Lease<'_> {
        fn drop(&mut self) {
            *self.0.borrow_mut() -= 1;
        }
    }

    fn statements() -> Vec<EngineStatement> {
        ["Q01", "Q02"].iter().map(|t| EngineStatement { template: t.to_string(), variant: None, binding: "v0".into(), ast: vec![1] }).collect()
    }

    /// The gate's record of one wait (as `QuietGate::wait` returns it).
    fn waited(ms: u64) -> QuietWait {
        QuietWait { threshold_one_minute: 16.0, max_wait_ms: 600_000, first_one_minute: Some(18.0), last_one_minute: Some(15.0), waited_ms: ms, timed_out: false }
    }

    /// A host whose lease counts its holders in the log, whose load average counts up per pair (1.25, 2.25, ...) and
    /// whose gate logs each wait with the leases held then.
    fn host<'a>(log: &'a Log, loads: &'a RefCell<u32>) -> RaceHost<impl Fn() -> Result<Lease<'a>, String> + 'a, impl Fn() -> Option<LoadAverage> + 'a, impl Fn() -> Option<QuietWait> + 'a> {
        RaceHost {
            timing_lease: move || {
                *log.leases.borrow_mut() += 1;
                Ok::<_, String>(Lease(&log.leases))
            },
            load_average: move || {
                *loads.borrow_mut() += 1;
                parse_load_average(&format!("{}.25 5.50 6.75 3/1234 99", loads.borrow()))
            },
            wait_for_quiet: move || {
                log.lines.borrow_mut().push(format!("quiet leases={}", log.leases.borrow()));
                Some(waited(1000))
            },
        }
    }

    /// A host without a gate or a lease (errors and plan tests).
    fn bare_host() -> RaceHost<impl Fn() -> Result<(), String>, impl Fn() -> Option<LoadAverage>, impl Fn() -> Option<QuietWait>> {
        RaceHost { timing_lease: || Ok::<_, String>(()), load_average: || None, wait_for_quiet: || None }
    }

    fn setup_with<'a>(statements: &'a [EngineStatement], baselines: &'a Baselines, record: Option<&'a [CellResult]>) -> RaceSetup<'a> {
        RaceSetup { statements, workers: &[1, 32], baselines, call_limit_ns: LIMIT, calls: DEVELOPMENT.cell_calls, parent_record: record, work: Path::new("work") }
    }

    fn run(log: &Log, parent: fn(&str, usize, u32) -> Option<u64>, candidate: fn(&str, usize, u32) -> Option<u64>, record: Option<&[CellResult]>) -> Result<RaceReport, RaceError> {
        let statements = statements();
        let baselines = Baselines::from_targets_json(TARGETS).unwrap();
        let loads = RefCell::new(0u32);
        let (p, c) = (canned("parent", log, parent), canned("candidate", log, candidate));
        race(&setup_with(&statements, &baselines, record), Contender { version: "v001", runner: &p }, Contender { version: "b1-a002", runner: &c }, &host(log, &loads))
    }

    fn new_log() -> Log {
        Log { lines: RefCell::new(vec![]), leases: RefCell::new(0) }
    }

    /// The runner log without the gate's lines.
    fn cells_run(log: &Log) -> Vec<String> {
        log.lines.borrow().iter().filter(|l| !l.starts_with("quiet")).cloned().collect()
    }

    fn finished(template: &str, workers: usize, median_ns: u64) -> CellResult {
        CellResult { template: template.into(), workers, status: CellStatus::Finished { median_ns } }
    }

    /// Pairs alternate parent-first and candidate-first (ABBA), both children of a pair hold the one lease of that
    /// pair, every lease is released, each pair records the load average read under its lease, and the gate waits
    /// before each pair with no lease held, its wait recorded with the pair.
    #[test]
    fn pairs_alternate_under_one_lease_each_with_load_averages() {
        let log = new_log();
        let report = run(&log, |_, w, _| Some(10_000_000 * w as u64), |_, w, _| Some(5_000_000 * w as u64), None).unwrap();
        assert_eq!(*log.lines.borrow(), [
            "quiet leases=0", "parent Q01 w1 leases=1", "candidate Q01 w1 leases=1",
            "quiet leases=0", "candidate Q01 w32 leases=1", "parent Q01 w32 leases=1",
            "quiet leases=0", "parent Q02 w1 leases=1", "candidate Q02 w1 leases=1",
            "quiet leases=0", "candidate Q02 w32 leases=1", "parent Q02 w32 leases=1",
        ]);
        assert_eq!(*log.leases.borrow(), 0, "every lease released");
        let orders: Vec<Vec<Side>> = report.pairs.iter().map(|p| p.timing.run_order.clone()).collect();
        assert_eq!(orders[0], [Side::Parent, Side::Candidate]);
        assert_eq!(orders[1], [Side::Candidate, Side::Parent]);
        let loads: Vec<f64> = report.pairs.iter().map(|p| p.timing.load_average.as_ref().unwrap().one_minute).collect();
        assert_eq!(loads, [1.25, 2.25, 3.25, 4.25], "one load average per pair, in pair order");
        assert_eq!(report.pairs[0].timing.load_average.as_ref().unwrap().line, "1.25 5.50 6.75 3/1234 99");
        assert!(report.pairs.iter().all(|p| p.timing.quiet_wait == Some(waited(1000))), "each pair records its gate's wait");
        assert!(report.candidate_better, "same finished count, half the time");
        assert_eq!((report.children_run, report.parent_children_skipped, report.retimed_pairs), (8, 0, 0));
        assert_eq!(report.pairs[0].timing.candidate_over_parent, Some(0.5));
        assert!(report.window_start_unix_ms <= report.window_end_unix_ms);
        // The record keeps the fields every reader of race.json uses at the pair's top level.
        let json = serde_json::to_value(&report).unwrap();
        assert_eq!((json["pairs"][0]["candidate_over_parent"].as_f64(), json["pairs"][0]["run_order"][0].as_str()), (Some(0.5), Some("parent")));
        assert_eq!(json["pairs"][0]["quiet_wait"]["waited_ms"], 1000);
        assert!(json["pairs"][0].get("retimed").is_none() && json.get("reused").is_none());
    }

    /// The general line's race: every side of every cell is 1 warm + 1 hot call (the development plan), the
    /// hot call's time is the cell's time, and the report records the protocol; the final plan's race makes 1 warm + 3
    /// hot calls per side.
    #[test]
    fn a_development_race_cell_is_one_warm_and_one_hot_call() {
        let log = new_log();
        let report = run(&log, |_, w, _| Some(10_000_000 * w as u64), |_, w, _| Some(5_000_000 * w as u64), None).unwrap();
        assert_eq!(report.calls_per_cell, 2);
        for pair in &report.pairs {
            for side in [&pair.timing.parent, &pair.timing.candidate] {
                let timed = side.timed.as_ref().unwrap();
                assert_eq!((timed.hot_ns.len(), side.status), (1, CellStatus::Finished { median_ns: timed.hot_ns[0] }), "one hot call, the cell's time");
            }
        }
        let statements = statements();
        let baselines = Baselines::from_targets_json(TARGETS).unwrap();
        let setup = RaceSetup { statements: &statements, workers: &[1], baselines: &baselines, call_limit_ns: LIMIT, calls: FINAL.cell_calls, parent_record: None, work: Path::new("work") };
        let log = new_log();
        let (parent, candidate) = (canned("parent", &log, |_, _, _| Some(7)), canned("candidate", &log, |_, _, _| Some(7)));
        let full = race(&setup, Contender { version: "v001", runner: &parent }, Contender { version: "v002", runner: &candidate }, &bare_host()).unwrap();
        assert_eq!((full.calls_per_cell, full.pairs[0].timing.parent.timed.as_ref().unwrap().hot_ns.len()), (4, 3));
    }

    /// The parent recorded as unfinished is never run again (whether the candidate finishes or not); a parent
    /// recorded as finished is skipped when the candidate ran first and did not finish; without a record the parent
    /// always runs. (Where a side does not finish here, the parent's recorded time is at the limit: nothing is re-timed.)
    #[test]
    fn skip_rules() {
        let record = [
            CellResult { template: "Q01".into(), workers: 1, status: CellStatus::Unfinished { reason: UnfinishedReason::OverTimeLimit } },
            finished("Q01", 32, 7),
            CellResult { template: "Q02".into(), workers: 1, status: CellStatus::Unfinished { reason: UnfinishedReason::OverMemoryLimit } },
            finished("Q02", 32, LIMIT),
        ];
        // The candidate finishes Q01 only; it does not finish Q02 at all.
        let log = new_log();
        let report = run(&log, |_, _, _| Some(8), |t, _, _| (t == "Q01").then_some(4), Some(&record)).unwrap();
        assert_eq!(cells_run(&log), [
            "candidate Q01 w1 leases=1",                               // parent recorded unfinished: not run (candidate finishes)
            "candidate Q01 w32 leases=1", "parent Q01 w32 leases=1",  // candidate first and finished: parent runs
            "candidate Q02 w1 leases=1",                               // parent recorded unfinished: not run (candidate unfinished too)
            "candidate Q02 w32 leases=1",                              // candidate first, unfinished; parent recorded finished: skipped
        ]);
        let sources: Vec<SideSource> = report.pairs.iter().map(|p| p.timing.parent.source).collect();
        assert_eq!(sources, [SideSource::ParentRecord, SideSource::Measured, SideSource::ParentRecord, SideSource::ParentRecord]);
        assert_eq!(report.pairs[3].timing.parent.status, CellStatus::Finished { median_ns: LIMIT }, "the recorded median stands in");
        assert_eq!((report.children_run, report.parent_children_skipped, report.retimed_pairs), (5, 3, 0));
        assert_eq!((report.parent_score.score.finished, report.candidate_score.score.finished), (2, 2));
        assert!(report.candidate_better, "same F; G decides: unfinished cells and the parent's recorded Q02 w32 count the limit, and the candidate's Q01 is faster");

        // Parent first (even pair) cannot be skipped by the candidate's result; without a record everything runs, and
        // nothing is re-timed (no reference).
        let log2 = new_log();
        let report = run(&log2, |_, _, _| Some(8), |_, _, _| None, None).unwrap();
        assert_eq!((report.children_run, report.retimed_pairs), (8, 0));
        assert_eq!(report.candidate_score.score.finished, 0);
        assert!(report.pairs.iter().all(|p| p.timing.candidate.status == CellStatus::Unfinished { reason: UnfinishedReason::OverTimeLimit }));
        assert_eq!(report.candidate_score.workers[0].total_ns, 2 * LIMIT, "unfinished cells count the limit");
    }

    fn side(status: CellStatus, source: SideSource) -> SideCell {
        SideCell { status, source, timed: None, unfinished: None }
    }

    fn pair_timing(parent: SideCell, candidate: SideCell) -> PairTiming {
        PairTiming { run_order: vec![], load_average: None, quiet_wait: None, parent, candidate, candidate_over_parent: None }
    }

    /// The suspicious-pair rule : a side run in this window that did not finish
    /// while the parent's recorded time is below the limit (whatever that time is), or that took more than twice the
    /// recorded time while it is below half the limit; the parent's record stands in for the candidate. A side taken
    /// from the record never counts, and without a finished parent record below the limit nothing is suspicious.
    #[test]
    fn the_suspicious_pair_rule() {
        let unfinished = CellStatus::Unfinished { reason: UnfinishedReason::OverTimeLimit };
        let done = |ms: u64| CellStatus::Finished { median_ns: ms * MS };
        let (measured, recorded) = (SideSource::Measured, SideSource::ParentRecord);
        let rec = |ms: u64| Some(done(ms));
        let limit = 60_000 * MS;
        // A side did not finish (b1-a003: Q12 recorded at 7.2 s, the candidate run first did not finish and the parent
        // was skipped; Q09 recorded at 42.9 s, the parent did not finish and the candidate finished).
        let candidate_alone = pair_timing(side(done(7_180), recorded), side(unfinished, measured));
        assert_eq!(suspicion(&candidate_alone, rec(7_180), limit).as_deref(),
            Some("the candidate did not finish; the parent's recorded time for this cell is 7.2 s, below the 60.0 s limit"));
        let parent_over = pair_timing(side(unfinished, measured), side(done(42_820), measured));
        assert_eq!(suspicion(&parent_over, rec(42_868), limit).as_deref(),
            Some("the parent did not finish; the parent's recorded time for this cell is 42.9 s, below the 60.0 s limit"), "a recorded time near the limit counts too");
        let both = pair_timing(side(unfinished, measured), side(unfinished, measured));
        assert_eq!(suspicion(&both, rec(45_000), limit).as_deref(),
            Some("the parent did not finish and the candidate did not finish; the parent's recorded time for this cell is 45.0 s, below the 60.0 s limit"));
        assert_eq!(suspicion(&both, rec(60_000), limit), None, "a recorded time at the limit");
        // More than twice the recorded time, below half the limit.
        let slow = pair_timing(side(done(25_000), measured), side(done(9_000), measured));
        assert_eq!(suspicion(&slow, rec(10_000), limit).as_deref(),
            Some("the parent took 25.0 s, more than twice the recorded time; the parent's recorded time for this cell is 10.0 s, below the 60.0 s limit"));
        assert_eq!(suspicion(&slow, rec(12_500), limit), None, "exactly twice is not more than twice");
        let both_slow = pair_timing(side(unfinished, measured), side(done(21_000), measured));
        assert_eq!(suspicion(&both_slow, rec(10_000), limit).as_deref(),
            Some("the parent did not finish and the candidate took 21.0 s, more than twice the recorded time; the parent's recorded time for this cell is 10.0 s, below the 60.0 s limit"));
        // No reference: no record, or a record that did not finish; a recorded side is never suspicious itself.
        assert_eq!(suspicion(&both, None, limit), None);
        assert_eq!(suspicion(&both, Some(unfinished), limit), None);
        assert_eq!(suspicion(&pair_timing(side(unfinished, recorded), side(done(100), measured)), rec(100), limit), None);
        assert_eq!(suspicion(&pair_timing(side(done(100), measured), side(done(150), measured)), rec(100), limit), None, "a normal pair");
    }

    /// The noisy race of the re-timing tests: the parent's first Q01 w1 run and the candidate's first Q01 w32 run do not
    /// finish, and the parent's first Q02 w32 run is slow; every later run is normal. Q02 w1's parent is slower than its
    /// record, but not twice: it is not re-timed.
    fn noisy_parent(template: &str, workers: usize, n: u32) -> Option<u64> {
        match (template, workers, n) {
            ("Q01", 1, 0) => None,
            ("Q02", 32, 0) => Some(300 * MS),
            ("Q02", 1, _) => Some(650 * MS),
            _ => Some(100 * MS),
        }
    }

    fn noisy_candidate(template: &str, workers: usize, n: u32) -> Option<u64> {
        match (template, workers, n) {
            ("Q01", 32, 0) => None,
            ("Q02", 1, _) => Some(550 * MS),
            ("Q02", 32, _) => Some(90 * MS),
            _ => Some(80 * MS),
        }
    }

    fn noisy_record() -> Vec<CellResult> {
        vec![finished("Q01", 1, 100 * MS), finished("Q01", 32, 100 * MS), finished("Q02", 1, 600 * MS), finished("Q02", 32, 100 * MS)]
    }

    /// Done-check: the suspicious pairs are timed again once at the end of the race, after the gate and
    /// under one lease each, the order alternating across them; the re-timed result is used and decides; each re-timed
    /// pair keeps its first result and the reason.
    #[test]
    fn suspicious_pairs_are_timed_again_once_and_the_retimed_result_decides() {
        let log = new_log();
        let record = noisy_record();
        let report = run(&log, noisy_parent, noisy_candidate, Some(&record)).unwrap();
        assert_eq!(cells_run(&log), [
            "parent Q01 w1 leases=1", "candidate Q01 w1 leases=1",
            "candidate Q01 w32 leases=1",                              // the parent is skipped (recorded finished)
            "parent Q02 w1 leases=1", "candidate Q02 w1 leases=1",
            "candidate Q02 w32 leases=1", "parent Q02 w32 leases=1",
            "parent Q01 w1 leases=1 retime", "candidate Q01 w1 leases=1 retime",
            "candidate Q01 w32 leases=1 retime", "parent Q01 w32 leases=1 retime",
            "parent Q02 w32 leases=1 retime", "candidate Q02 w32 leases=1 retime",
        ]);
        assert_eq!(log.lines.borrow().iter().filter(|l| *l == "quiet leases=0").count(), 7, "the gate before each of the 4 + 3 pairs, never under a lease");
        assert_eq!((report.children_run, report.parent_children_skipped, report.retimed_pairs), (13, 1, 3));
        let reasons: Vec<Option<&str>> = report.pairs.iter().map(|p| p.retimed.as_ref().map(|r| r.reason.as_str())).collect();
        assert_eq!(reasons, [
            Some("the parent did not finish; the parent's recorded time for this cell is 0.1 s, below the 1.0 s limit"),
            Some("the candidate did not finish; the parent's recorded time for this cell is 0.1 s, below the 1.0 s limit"),
            None,
            Some("the parent took 0.3 s, more than twice the recorded time; the parent's recorded time for this cell is 0.1 s, below the 1.0 s limit"),
        ]);
        let first = &report.pairs[1].retimed.as_ref().unwrap().first_pass;
        assert_eq!((first.run_order.as_slice(), first.parent.source, first.candidate.status), ([Side::Candidate].as_slice(), SideSource::ParentRecord,
            CellStatus::Unfinished { reason: UnfinishedReason::OverTimeLimit }), "the first result is kept");
        assert_eq!(report.pairs[1].timing.run_order, [Side::Candidate, Side::Parent], "the second re-timed pair runs the candidate first");
        assert_eq!(report.pairs[0].timing.run_order, [Side::Parent, Side::Candidate]);
        assert_eq!(report.pairs[1].timing.candidate.status, CellStatus::Finished { median_ns: 80 * MS }, "the re-timed result is used");
        assert_eq!(report.pairs[3].timing.parent.status, CellStatus::Finished { median_ns: 100 * MS });
        assert_eq!(report.pairs[3].timing.load_average.as_ref().unwrap().one_minute, 7.25, "the re-timed pair records its own load average");
        assert_eq!((report.parent_score.score.finished, report.candidate_score.score.finished), (4, 4));
        assert!(report.candidate_better, "the re-timed cells decide: as many finished cells, and faster");
        let json = serde_json::to_value(&report).unwrap();
        assert_eq!(json["pairs"][0]["retimed"]["first_pass"]["parent"]["status"]["status"], "unfinished", "race.json keeps both results");
        assert_eq!(json["retimed_pairs"], 3);
    }

    /// Done-check: an earlier race read back from its record has only its suspicious pairs timed
    /// again (the others are reused as recorded), both sides are scored over the result, and the report names the
    /// reused race; pairs already re-timed are not timed again, and a record of another parent or other cells is
    /// refused.
    #[test]
    fn a_recorded_race_has_only_its_suspicious_pairs_timed_again() {
        let statements = statements();
        let baselines = Baselines::from_targets_json(TARGETS).unwrap();
        let record = noisy_record();
        // The earlier race, timed before the re-timing rule existed (no parent record given: nothing re-timed).
        let log = new_log();
        let earlier = run(&log, noisy_parent, noisy_candidate, None).unwrap();
        assert_eq!((earlier.retimed_pairs, earlier.parent_score.score.finished, earlier.candidate_score.score.finished), (0, 3, 3));
        let mut recorded: RecordedRace = serde_json::from_value(json!(earlier)).unwrap();
        recorded.file = PathBuf::from("/e/evaluation-0/race.json");
        // Re-evaluation: the second runs of every cell are normal.
        let log = new_log();
        let loads = RefCell::new(0u32);
        let (p, c) = (canned("parent", &log, |t, w, _| noisy_parent(t, w, 1)), canned("candidate", &log, |t, w, _| noisy_candidate(t, w, 1)));
        let setup = setup_with(&statements, &baselines, Some(&record));
        let report = retime_recorded(&setup, Contender { version: "v001", runner: &p }, Contender { version: "b1-a002", runner: &c }, recorded.clone(), &host(&log, &loads)).unwrap();
        assert_eq!(cells_run(&log), [
            "parent Q01 w1 leases=1 retime", "candidate Q01 w1 leases=1 retime",
            "candidate Q01 w32 leases=1 retime", "parent Q01 w32 leases=1 retime",
            "parent Q02 w32 leases=1 retime", "candidate Q02 w32 leases=1 retime",
        ], "only the suspicious pairs, in alternating order; Q02 w1 is reused");
        assert_eq!((report.children_run, report.retimed_pairs, report.parent_score.score.finished, report.candidate_score.score.finished), (6, 3, 4, 4));
        assert!(report.candidate_better);
        assert_eq!(report.pairs[2], earlier.pairs[2], "a pair that is not suspicious is reused as recorded");
        assert_eq!(report.reused, Some(ReusedPairs { race: PathBuf::from("/e/evaluation-0/race.json"), window_start_unix_ms: earlier.window_start_unix_ms,
            window_end_unix_ms: earlier.window_end_unix_ms, pairs: 4 }));
        // Read back again, nothing is timed a second time.
        let again: RecordedRace = serde_json::from_value(json!(report)).unwrap();
        let log = new_log();
        let (p, c) = (canned("parent", &log, |_, _, _| None), canned("candidate", &log, |_, _, _| None));
        let same = retime_recorded(&setup, Contender { version: "v001", runner: &p }, Contender { version: "b1-a002", runner: &c }, again, &bare_host()).unwrap();
        assert!(cells_run(&log).is_empty() && same.candidate_better && same.retimed_pairs == 3);
        // Another parent, or other cells, is refused.
        let wrong = retime_recorded(&setup, Contender { version: "v009", runner: &p }, Contender { version: "b1-a002", runner: &c }, recorded.clone(), &bare_host());
        assert!(matches!(wrong, Err(RaceError::Score(_))));
        let mut fewer = recorded;
        fewer.pairs.pop();
        assert!(matches!(retime_recorded(&setup, Contender { version: "v001", runner: &p }, Contender { version: "b1-a002", runner: &c }, fewer, &bare_host()), Err(RaceError::Score(_))));
    }

    /// A failing runner ends the comparison naming its side; a variant or a mixed binding is refused.
    #[test]
    fn errors_name_the_side() {
        struct Refuses;
        impl EngineCellRunner for Refuses {
            fn run_cell(&self, _: CellRequest<'_>, _: &Path) -> Result<Value, AdmissionError> {
                Err(AdmissionError::execution("rows disagree with the saved answers"))
            }
        }
        let log = new_log();
        let statements = statements();
        let baselines = Baselines::from_targets_json(TARGETS).unwrap();
        let setup = setup_with(&statements, &baselines, None);
        let parent = canned("parent", &log, |_, _, _| Some(1));
        let error = race(&setup, Contender { version: "v001", runner: &parent }, Contender { version: "b1-a003", runner: &Refuses }, &bare_host()).unwrap_err();
        assert!(matches!(&error, RaceError::Cell { side: Side::Candidate, version, template, workers: 1, .. } if version == "b1-a003" && template == "Q01"), "{error}");
        let mut mixed = statements.clone();
        mixed[1].binding = "v1".into();
        let setup = RaceSetup { statements: &mixed, ..setup };
        assert!(matches!(race(&setup, Contender { version: "a", runner: &Refuses }, Contender { version: "b", runner: &Refuses }, &bare_host()), Err(RaceError::Score(_))));
    }
}
