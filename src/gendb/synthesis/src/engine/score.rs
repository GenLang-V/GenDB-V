//! The score of one engine version at one scale.
//!
//! Definitions, at one scale and the timing binding:
//! - a **cell** is a (template, worker count) pair: every template with a saved baseline cell times every configured
//!   worker count;
//! - a cell is **finished** when its warm call and its hot calls each ended within the call limit and every answer
//!   agreed with the saved answers ([`CellStatus::Finished`]); otherwise it is unfinished with its reason (over the
//!   time limit, over the memory limit, a child failure), or [`CellStatus::Unchecked`] when every call ended within the
//!   limit but no saved answer was compared (never counted as finished: finishing requires agreement);
//! - the **cell time** is the median hot call of a finished cell (capped at the limit), and the call limit otherwise;
//! - the **total at w** is the sum of the cell times at worker count `w`;
//! - the **score** is `(F, G)`: `F` the number of finished cells, `G` the sum over worker counts of
//!   `total_w / target_w`, where `target_w` is the faster baseline's total at `w` (`super::totals::Baselines::totals`;
//!   DuckDB's when Umbra did not time every template, `super::totals::target_of`);
//! - **better** means a larger `F`, or the same `F` and a smaller `G` ([`Score::is_better_than`]).
//!
//! `G` is kept exactly in integer billionths ([`NormalizedTime`]: each `total_w / target_w` is floored to a billionth
//! before the sum), so the decision compares integers; nothing here is a float decision. The milestone "beats both at
//! this scale" ([`ScaleScore::beats_both`]) is every cell finished and every total below both baseline totals: a
//! report, never a stop. Units: nanoseconds (`_ns`). Arithmetic over recorded cells only; no performance claim.
//!
//! A run of several workloads (`engine.workloads`) decides every submission by the
//! **combined score** ([`CombinedScore`], [`COMBINED_RULE`]): `F` the sum of every counted workload's `F_w` and `G` the
//! sum of every counted workload's `G_w`, each `(F_w, G_w)` the workload's score at its own scale; better is ordered as
//! above. [`SCORE_RULE`] stays the rule recorded with every scale score, so the records of runs of one workload are
//! unchanged.

use super::totals::{Baselines, TotalsError, target_of};
use gendb_runtime::worker::UnfinishedReason;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt;

/// The rule as recorded with every score.
pub const SCORE_RULE: &str = "a cell (template, worker count) is finished when its warm call and its hot calls each ended within the call limit and \
its answers agreed with the saved answers; its time is its median hot call, or the call limit when unfinished; F = finished cells; \
G = sum over worker counts of (sum of cell times) / (the faster baseline's total), in billionths; a version is better than another \
with a larger F, or the same F and a smaller G";

/// A record that cannot be scored as this module needs it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScoreError(pub String);

impl fmt::Display for ScoreError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for ScoreError {}

impl From<TotalsError> for ScoreError {
    fn from(error: TotalsError) -> Self {
        Self(error.0)
    }
}

/// The state of one cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case")]
pub enum CellStatus {
    /// Every call ended within the call limit and every answer agreed with the saved answers.
    Finished { median_ns: u64 },
    /// A call stopped at a limit, or the child failed.
    Unfinished { reason: UnfinishedReason },
    /// Every call ended within the call limit, but no answer was compared with saved answers: not finished.
    Unchecked { median_ns: u64 },
}

impl CellStatus {
    pub fn is_finished(&self) -> bool {
        matches!(self, Self::Finished { .. })
    }

    /// The cell time: a finished cell's median capped at `call_limit_ns`, else `call_limit_ns`.
    pub fn time_ns(&self, call_limit_ns: u64) -> u64 {
        match self {
            Self::Finished { median_ns } => (*median_ns).min(call_limit_ns),
            Self::Unfinished { .. } | Self::Unchecked { .. } => call_limit_ns,
        }
    }
}

/// One cell's state, as the timing or an interleaved comparison recorded it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CellResult {
    pub template: String,
    pub workers: usize,
    pub status: CellStatus,
}

/// `G` in integer billionths. JSON: its decimal text (`"2.345678901"`), exact and free of floating point.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NormalizedTime {
    billionths: u64,
}

impl NormalizedTime {
    pub const fn from_billionths(billionths: u64) -> Self {
        Self { billionths }
    }

    pub fn billionths(self) -> u64 {
        self.billionths
    }

    /// For display and reports only.
    pub fn as_f64(self) -> f64 {
        self.billionths as f64 / 1e9
    }

    /// `floor(total_ns * 10^9 / target_ns)`; a zero target is an error.
    fn of(total_ns: u64, target_ns: u64) -> Result<Self, ScoreError> {
        if target_ns == 0 {
            return Err(ScoreError("a baseline total of 0 ns cannot normalize a total".into()));
        }
        let billionths = u128::from(total_ns) * 1_000_000_000 / u128::from(target_ns);
        u64::try_from(billionths).map(Self::from_billionths).map_err(|_| ScoreError(format!("{total_ns} / {target_ns} does not fit in billionths")))
    }
}

impl fmt::Display for NormalizedTime {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}.{:09}", self.billionths / 1_000_000_000, self.billionths % 1_000_000_000)
    }
}

impl Serialize for NormalizedTime {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.collect_str(self)
    }
}

impl<'de> Deserialize<'de> for NormalizedTime {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let text = String::deserialize(deserializer)?;
        let refuse = || serde::de::Error::custom(format!("{text:?} is not a normalized time with 9 fractional digits"));
        let (whole, fraction) = text.split_once('.').ok_or_else(refuse)?;
        if fraction.len() != 9 || !whole.bytes().chain(fraction.bytes()).all(|b| b.is_ascii_digit()) || whole.is_empty() {
            return Err(refuse());
        }
        let whole: u64 = whole.parse().map_err(|_| refuse())?;
        let fraction: u64 = fraction.parse().map_err(|_| refuse())?;
        whole.checked_mul(1_000_000_000).and_then(|w| w.checked_add(fraction)).map(Self::from_billionths).ok_or_else(refuse)
    }
}

/// The score `(F, G)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Score {
    /// F: finished cells.
    pub finished: usize,
    /// G: the sum over worker counts of the total over the faster baseline's total.
    pub normalized_time: NormalizedTime,
}

impl Score {
    /// `Greater` when `self` is better than `other`: more finished cells, or as many and a smaller normalized time.
    pub fn rank_against(&self, other: &Score) -> Ordering {
        self.finished.cmp(&other.finished).then_with(|| other.normalized_time.cmp(&self.normalized_time))
    }

    /// Strictly better (an equal score is not better).
    pub fn is_better_than(&self, other: &Score) -> bool {
        self.rank_against(other) == Ordering::Greater
    }
}

/// One scored cell.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ScoredCell {
    pub template: String,
    pub workers: usize,
    pub status: CellStatus,
    /// The cell time (finished: the median capped at the limit; otherwise the limit).
    pub time_ns: u64,
    /// The faster baseline's median of this template at this worker count (the per-cell gap's denominator).
    pub faster_baseline_ns: u64,
}

/// The totals of one worker count.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct WorkerScore {
    pub workers: usize,
    pub cells: usize,
    pub finished: usize,
    /// Sum of the cell times.
    pub total_ns: u64,
    pub duckdb_ns: u64,
    /// Umbra's total, `None` when Umbra did not time every template (`super::totals::BaselineCell::umbra_ns`).
    pub umbra_ns: Option<u64>,
    /// The faster baseline total (`super::totals::target_of`) and its engine.
    pub target_ns: u64,
    pub target_engine: &'static str,
    /// `total_ns / target_ns`, floored to a billionth.
    pub normalized: NormalizedTime,
    /// Every cell finished and the total is below both baseline totals (below DuckDB's when Umbra's does not exist).
    pub below_both: bool,
}

/// The score of one version at one scale, with every cell and the per-worker totals.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ScaleScore {
    pub binding: String,
    pub call_limit_ns: u64,
    pub score: Score,
    /// Number of cells (templates times worker counts).
    pub cells_total: usize,
    pub workers: Vec<WorkerScore>,
    pub cells: Vec<ScoredCell>,
    /// The milestone: every cell finished and every total below both baseline totals (a report, never a stop).
    pub beats_both: bool,
    pub rule: &'static str,
}

impl ScaleScore {
    /// The worker count where `template`'s cell time is largest relative to the faster baseline's median (the
    /// largest gap; the first such count on ties), or `None` for a template without cells. The profile pass profiles
    /// each template there.
    pub fn largest_gap_workers(&self, template: &str) -> Option<usize> {
        let mut best: Option<&ScoredCell> = None;
        for cell in self.cells.iter().filter(|c| c.template == template) {
            // a/b > c/d exactly, with b, d > 0 (u128 products of u64 values).
            let larger = best.is_none_or(|b| {
                u128::from(cell.time_ns) * u128::from(b.faster_baseline_ns.max(1)) > u128::from(b.time_ns) * u128::from(cell.faster_baseline_ns.max(1))
            });
            if larger {
                best = Some(cell);
            }
        }
        best.map(|c| c.workers)
    }
}

/// The rule of the combined score of a run of several workloads (module documentation), recorded with it.
pub const COMBINED_RULE: &str = "the combined score of a run of several workloads: F = the sum of every counted workload's F, G = the sum of every \
counted workload's G (each at its own scale, in exact billionths); a version is better than another with a larger F, or the same F and a smaller G; \
there is no guard per workload";

/// The combined score of a run of several workloads (module documentation): the sums over the counted workloads, the
/// cells summed likewise, and which workloads were summed (in run order).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CombinedScore {
    pub score: Score,
    pub cells: usize,
    pub workloads: Vec<String>,
}

impl CombinedScore {
    /// The sum of `scores` (`(workload, its score, its cells)`, counted workloads only). An overflow is an error.
    pub fn of(scores: &[(&str, Score, usize)]) -> Result<Self, ScoreError> {
        let (mut finished, mut billionths, mut cells) = (0usize, 0u64, 0usize);
        for (name, score, workload_cells) in scores {
            finished = finished.checked_add(score.finished).ok_or_else(|| ScoreError(format!("the combined F overflows at {name}")))?;
            billionths = billionths.checked_add(score.normalized_time.billionths()).ok_or_else(|| ScoreError(format!("the combined G overflows at {name}")))?;
            cells = cells.checked_add(*workload_cells).ok_or_else(|| ScoreError(format!("the combined cells overflow at {name}")))?;
        }
        Ok(Self { score: Score { finished, normalized_time: NormalizedTime::from_billionths(billionths) }, cells, workloads: scores.iter().map(|(n, _, _)| n.to_string()).collect() })
    }

    /// Strictly better ([`Score::is_better_than`] of the sums).
    pub fn is_better_than(&self, other: &CombinedScore) -> bool {
        self.score.is_better_than(&other.score)
    }
}

/// Score `cells` at `binding` against `baselines` at each count of `workers`, with the call limit `call_limit_ns`.
/// Every template with a baseline cell must have exactly one cell at every worker count, and no other cell may be
/// given.
pub fn score(baselines: &Baselines, binding: &str, workers: &[usize], call_limit_ns: u64, cells: &[CellResult]) -> Result<ScaleScore, ScoreError> {
    if workers.is_empty() || call_limit_ns == 0 {
        return Err(ScoreError("a score needs at least one worker count and a positive call limit".into()));
    }
    let templates = baselines.templates();
    let mut by_cell: BTreeMap<(&str, usize), CellStatus> = BTreeMap::new();
    for cell in cells {
        if !templates.contains(cell.template.as_str()) || !workers.contains(&cell.workers) {
            return Err(ScoreError(format!("cell {} at {} workers is not a cell of this scale", cell.template, cell.workers)));
        }
        if by_cell.insert((cell.template.as_str(), cell.workers), cell.status).is_some() {
            return Err(ScoreError(format!("two results for {} at {} workers", cell.template, cell.workers)));
        }
    }
    let mut scored = Vec::new();
    let mut per_workers = Vec::new();
    for &w in workers {
        let (duckdb_ns, umbra_ns) = baselines.totals(&templates, binding, w)?;
        let (target_ns, target_engine) = target_of(duckdb_ns, umbra_ns);
        let (mut total_ns, mut finished) = (0u64, 0usize);
        for &template in &templates {
            let status = *by_cell.get(&(template, w)).ok_or_else(|| ScoreError(format!("no result for {template} at {w} workers")))?;
            let baseline = baselines.cell(template, binding, w).expect("every template of `templates` has its baseline cells (checked by totals)");
            let time_ns = status.time_ns(call_limit_ns);
            total_ns = total_ns.checked_add(time_ns).ok_or_else(|| ScoreError("total time overflows".into()))?;
            finished += usize::from(status.is_finished());
            scored.push(ScoredCell { template: template.to_string(), workers: w, status, time_ns, faster_baseline_ns: baseline.faster_ns() });
        }
        per_workers.push(WorkerScore {
            workers: w,
            cells: templates.len(),
            finished,
            total_ns,
            duckdb_ns,
            umbra_ns,
            target_ns,
            target_engine,
            normalized: NormalizedTime::of(total_ns, target_ns)?,
            below_both: finished == templates.len() && total_ns < duckdb_ns && umbra_ns.is_none_or(|umbra| total_ns < umbra),
        });
    }
    let finished = per_workers.iter().map(|w| w.finished).sum();
    let billionths = per_workers.iter().try_fold(0u64, |sum, w| sum.checked_add(w.normalized.billionths())).ok_or_else(|| ScoreError("G overflows".into()))?;
    let cells_total = templates.len() * workers.len();
    Ok(ScaleScore {
        binding: binding.to_string(),
        call_limit_ns,
        score: Score { finished, normalized_time: NormalizedTime::from_billionths(billionths) },
        cells_total,
        beats_both: finished == cells_total && per_workers.iter().all(|w| w.below_both),
        workers: per_workers,
        cells: scored,
        rule: SCORE_RULE,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Two templates, two worker counts. Totals: 1 worker DuckDB 30 ms, Umbra 12 ms (target Umbra); 32 workers DuckDB
    /// 3 ms, Umbra 4 ms (target DuckDB).
    const TARGETS: &str = r#"{
        "Q01": {"v0": {"1": {"duckdb_ms": 10, "umbra_ms": 8, "target_ms": 8, "agreement": "exact-order"},
                       "32": {"duckdb_ms": 2, "umbra_ms": 3, "target_ms": 2, "agreement": "exact-order"}}},
        "Q02": {"v0": {"1": {"duckdb_ms": 20, "umbra_ms": 4, "target_ms": 4, "agreement": "exact-order"},
                       "32": {"duckdb_ms": 1, "umbra_ms": 1, "target_ms": 1, "agreement": "exact-order"}}}
    }"#;
    const LIMIT: u64 = 60_000_000_000;

    fn finished(template: &str, workers: usize, median_ns: u64) -> CellResult {
        CellResult { template: template.into(), workers, status: CellStatus::Finished { median_ns } }
    }

    fn unfinished(template: &str, workers: usize, reason: UnfinishedReason) -> CellResult {
        CellResult { template: template.into(), workers, status: CellStatus::Unfinished { reason } }
    }

    fn scored(cells: &[CellResult]) -> ScaleScore {
        score(&Baselines::from_targets_json(TARGETS).unwrap(), "v0", &[1, 32], LIMIT, cells).unwrap()
    }

    /// G is the sum over worker counts of total / faster baseline total, exactly in billionths.
    #[test]
    fn normalization_divides_each_total_by_the_faster_baseline() {
        let s = scored(&[finished("Q01", 1, 6_000_000), finished("Q02", 1, 6_000_000), finished("Q01", 32, 1_000_000), finished("Q02", 32, 2_000_000)]);
        assert_eq!((s.workers[0].target_ns, s.workers[0].target_engine), (12_000_000, "umbra"));
        assert_eq!((s.workers[1].target_ns, s.workers[1].target_engine), (3_000_000, "duckdb"));
        assert_eq!(s.workers[0].normalized, NormalizedTime::from_billionths(1_000_000_000), "12 ms / 12 ms");
        assert_eq!(s.workers[1].normalized, NormalizedTime::from_billionths(1_000_000_000), "3 ms / 3 ms");
        assert_eq!(s.score, Score { finished: 4, normalized_time: NormalizedTime::from_billionths(2_000_000_000) });
        assert!(!s.beats_both, "equal totals are not below");
        let s = scored(&[finished("Q01", 1, 1_000_000), finished("Q02", 1, 2_000_000), finished("Q01", 32, 1_000_000), finished("Q02", 32, 1)]);
        assert_eq!(s.workers[0].normalized.billionths(), 250_000_000, "3 ms / 12 ms");
        assert_eq!(s.workers[1].normalized.billionths(), 333_333_666, "1.000001 ms / 3 ms, floored");
        assert!(s.beats_both);
        assert_eq!(serde_json::to_value(s.score).unwrap(), serde_json::json!({"finished": 4, "normalized_time": "0.583333666"}));
        assert_eq!(serde_json::from_value::<Score>(serde_json::to_value(s.score).unwrap()).unwrap(), s.score);
    }

    /// A training set with a statement timed on DuckDB alone: Umbra's total does not exist, so
    /// DuckDB's total is the target at every worker count, the statement's faster baseline is DuckDB's median, and the
    /// milestone needs every total below DuckDB's.
    #[test]
    fn a_statement_on_duckdb_alone_makes_duckdb_the_target() {
        let text = r#"{
            "Q01": {"v0": {"1": {"duckdb_ms": 10, "umbra_ms": 8, "target_ms": 8, "agreement": "exact-order"}}},
            "U07": {"v0": {"1": {"duckdb_ms": 5, "target_ms": 5, "agreement": "duckdb_only"}}}
        }"#;
        let baselines = Baselines::from_targets_json(text).unwrap();
        let s = score(&baselines, "v0", &[1], LIMIT, &[finished("Q01", 1, 4_000_000), finished("U07", 1, 2_000_000)]).unwrap();
        assert_eq!((s.workers[0].duckdb_ns, s.workers[0].umbra_ns, s.workers[0].target_ns, s.workers[0].target_engine), (15_000_000, None, 15_000_000, "duckdb"));
        assert_eq!(s.workers[0].normalized.billionths(), 400_000_000, "6 ms / 15 ms");
        assert_eq!(s.cells.iter().map(|c| (c.template.as_str(), c.faster_baseline_ns)).collect::<Vec<_>>(), [("Q01", 8_000_000), ("U07", 5_000_000)]);
        assert!(s.beats_both && s.workers[0].below_both, "below DuckDB, the only baseline with a total");
        assert_eq!(serde_json::to_value(&s.workers[0]).unwrap()["umbra_ns"], serde_json::Value::Null);
        let slow = score(&baselines, "v0", &[1], LIMIT, &[finished("Q01", 1, 9_000_000), finished("U07", 1, 6_000_000)]).unwrap();
        assert!(!slow.beats_both, "15 ms is not below DuckDB's 15 ms");
    }

    /// An unfinished or unchecked cell counts the call limit, and a finished median above the limit is capped.
    #[test]
    fn unfinished_cells_count_the_limit() {
        let s = scored(&[
            unfinished("Q01", 1, UnfinishedReason::OverTimeLimit),
            CellResult { template: "Q02".into(), workers: 1, status: CellStatus::Unchecked { median_ns: 5 } },
            unfinished("Q01", 32, UnfinishedReason::OverMemoryLimit),
            finished("Q02", 32, LIMIT + 7),
        ]);
        assert_eq!(s.score.finished, 1);
        assert_eq!(s.workers[0].total_ns, 2 * LIMIT);
        assert_eq!(s.workers[1].total_ns, 2 * LIMIT, "a finished median is capped at the limit");
        assert_eq!(s.cells.iter().map(|c| c.time_ns).collect::<Vec<_>>(), [LIMIT, LIMIT, LIMIT, LIMIT]);
        assert_eq!(s.workers[0].normalized.billionths(), 10_000_000_000_000, "120 s / 12 ms");
    }

    /// Better = more finished cells first, then a smaller G; an equal score is not better.
    #[test]
    fn ordering_is_finished_cells_then_normalized_time() {
        let fast_unfinished = scored(&[finished("Q01", 1, 1), finished("Q02", 1, 1), finished("Q01", 32, 1), unfinished("Q02", 32, UnfinishedReason::ChildFailure)]);
        let slow_finished = scored(&[finished("Q01", 1, 59_000_000_000), finished("Q02", 1, 59_000_000_000), finished("Q01", 32, 59_000_000_000), finished("Q02", 32, 59_000_000_000)]);
        assert!(fast_unfinished.score.normalized_time < slow_finished.score.normalized_time);
        assert!(slow_finished.score.is_better_than(&fast_unfinished.score), "F decides first");
        let faster = scored(&[finished("Q01", 1, 1), finished("Q02", 1, 1), finished("Q01", 32, 1), finished("Q02", 32, 1)]);
        assert!(faster.score.is_better_than(&slow_finished.score) && !slow_finished.score.is_better_than(&faster.score), "then G");
        assert!(!faster.score.is_better_than(&faster.score), "equal is not better");
        assert_eq!(faster.score.rank_against(&faster.score), Ordering::Equal);
    }

    /// Every cell of the scale exactly once; nothing else.
    #[test]
    fn every_cell_exactly_once() {
        let baselines = Baselines::from_targets_json(TARGETS).unwrap();
        let three = [finished("Q01", 1, 1), finished("Q02", 1, 1), finished("Q01", 32, 1)];
        assert!(score(&baselines, "v0", &[1, 32], LIMIT, &three).unwrap_err().0.contains("no result for Q02 at 32"));
        let mut five = three.to_vec();
        five.extend([finished("Q02", 32, 1), finished("Q02", 32, 2)]);
        assert!(score(&baselines, "v0", &[1, 32], LIMIT, &five).unwrap_err().0.contains("two results"));
        let mut other = three.to_vec();
        other.extend([finished("Q02", 32, 1), finished("Q03", 32, 1)]);
        assert!(score(&baselines, "v0", &[1, 32], LIMIT, &other).unwrap_err().0.contains("not a cell of this scale"));
        assert!(score(&baselines, "v0", &[1, 64], LIMIT, &[]).is_err(), "no baseline at 64 workers");
        assert!(score(&baselines, "v0", &[1, 32], 0, &[]).is_err());
    }

    /// The largest gap: the worker count with the largest cell time over the faster baseline median.
    #[test]
    fn largest_gap_picks_the_worst_ratio() {
        // Q01: 1 worker 16 ms / 8 ms = 2; 32 workers 6 ms / 2 ms = 3. Q02: 1 worker 40 ms / 4 = 10; 32 workers 1 ms / 1 = 1.
        let s = scored(&[finished("Q01", 1, 16_000_000), finished("Q02", 1, 40_000_000), finished("Q01", 32, 6_000_000), finished("Q02", 32, 1_000_000)]);
        assert_eq!((s.largest_gap_workers("Q01"), s.largest_gap_workers("Q02"), s.largest_gap_workers("Q09")), (Some(32), Some(1), None));
    }

    /// The combined score of a run of several workloads: the sums of F, G and the cells over the counted workloads; a
    /// larger combined F wins first, then a smaller combined G, so a loss on one workload is accepted when another gains
    /// more (no guard); an equal sum is not better.
    #[test]
    fn the_combined_score_sums_the_counted_workloads() {
        let score = |finished: usize, billionths: u64| Score { finished, normalized_time: NormalizedTime::from_billionths(billionths) };
        let parent = CombinedScore::of(&[("tpch", score(12, 2_545_797_717), 12), ("sec", score(18, 15_343_889_487), 18)]).unwrap();
        assert_eq!((parent.score.finished, parent.score.normalized_time.to_string(), parent.cells), (30, "17.889687204".to_string(), 30));
        assert_eq!(parent.workloads, ["tpch", "sec"]);
        // Slower on tpch, faster on sec by more: better in sum.
        let mixed = CombinedScore::of(&[("tpch", score(12, 2_600_000_000), 12), ("sec", score(18, 13_948_990_443), 18)]).unwrap();
        assert!(mixed.is_better_than(&parent) && !parent.is_better_than(&mixed));
        // Faster on tpch, slower on sec by more: worse in sum.
        let worse = CombinedScore::of(&[("tpch", score(12, 2_000_000_000), 12), ("sec", score(18, 16_000_000_000), 18)]).unwrap();
        assert!(!worse.is_better_than(&parent));
        // One more finished cell decides first, whatever G.
        let more = CombinedScore::of(&[("tpch", score(12, 9_000_000_000), 12), ("sec", score(18, 99_000_000_000), 18)]).unwrap();
        let fewer = CombinedScore::of(&[("tpch", score(11, 1), 12), ("sec", score(18, 1), 18)]).unwrap();
        assert!(more.is_better_than(&fewer));
        assert!(!parent.is_better_than(&parent.clone()), "equal is not better");
        assert!(CombinedScore::of(&[("a", score(1, u64::MAX), 1), ("b", score(1, 1), 1)]).is_err(), "an overflow is refused");
        assert_eq!(serde_json::to_value(&parent).unwrap(), serde_json::json!({"score":{"finished":30,"normalized_time":"17.889687204"},"cells":30,"workloads":["tpch","sec"]}));
    }

    #[test]
    fn normalized_time_text_is_exact() {
        for (billionths, text) in [(0, "0.000000000"), (2_345_678_901, "2.345678901"), (1, "0.000000001")] {
            let t = NormalizedTime::from_billionths(billionths);
            assert_eq!(t.to_string(), text);
            assert_eq!(serde_json::from_value::<NormalizedTime>(serde_json::json!(text)).unwrap(), t);
        }
        for bad in ["1.5", "1", "-1.000000000", "1.00000000x", ".000000001"] {
            assert!(serde_json::from_value::<NormalizedTime>(serde_json::json!(bad)).is_err(), "{bad}");
        }
    }
}
