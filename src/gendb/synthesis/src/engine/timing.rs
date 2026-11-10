//! Engine evaluation matrices.
//!
//! - The **official matrix**: every template at the timing binding x every configured worker count, one cell per fresh
//!   worker child, 1 warm call then 3 hot calls ([`OFFICIAL_CALLS`], the evaluations' `TIMED_REPETITIONS`), the cell's
//!   time is the median hot call. Its medians feed `super::totals` (totals, gap, stop).
//! - The **variant matrix**: every frozen variant (`fixtures/tpch/engine-variants`) x every worker count, 1 warm call
//!   then 1 hot call ([`VARIANT_CALLS`]). Each variant cell must return its template's saved answers (a gating check
//!   the runner's record states); its time is only compared with its template's in the [`VariantRatioReport`], which is
//!   a report with no threshold.
//!
//! This module owns the cell order, the timing lease per cell, the call counts, reading each cell's timing from its
//! record, the matrices and the ratio report. A gating matrix ends at its first failing cell ([`run_matrix`]); the
//! official timing of an admitted version records each failing cell and goes on ([`run_matrix_recording_failures`]). It does not own:
//! - **the engine call.** A cell runs through [`EngineCellRunner`], which Stage 2 wires to the worker child of the
//!   fixed entry `abi_engine_query` over the engine's storage assets. The runner returns the cell record of
//!   `gendb_verification::admission::execution` (`status`, `warm_wall_ns`, `hot_wall_ns`, `median_hot_wall_ns`, the
//!   saved-answer comparison), so the median and the answer check are that code's, not a second implementation here;
//! - **the AST bytes.** Each statement is translated and encoded before the matrix runs; translation and encoding are
//!   untimed and recorded by the caller;
//! - **the lease.** The caller passes the host's exclusive timing lease (`HostLocks::timing`) as `timing_lease`, as for
//!   `QuerySession::evaluate_submission` and `trial`. It is held for exactly one cell (one child), so no other timing or
//!   build overlaps a cell, and other work may run between cells. The host's load averages ([`LoadAverage`],
//!   `/proc/loadavg`) are read once the lease is held and recorded with the cell.
//!
//! Timings are wall time of the engine call in the child (planning included); nothing here is a performance claim.
//!
//! **Unfinished cells**: when the runner applies per-call limits, a cell whose call
//! was stopped at a limit (or whose child failed) comes back as a record carrying `unfinished`
//! (`gendb_runtime::worker::Unfinished`) with the observations before the stopped call. [`read_cell`] reads it as an
//! [`UnfinishedCell`]; a gating matrix ends there like at a failing cell, and a recording matrix keeps it in
//! [`EngineMatrix::unfinished`] and goes on. [`EngineMatrix::cell_results`] gives every official cell's status for
//! `super::score`, and [`CellTiming::status`] decides a timed cell's status against the call limit.
//!
//! **The general line's plans** (`super::protocol`): its timings run official cells at the plan's call count
//! ([`run_official_recording_failures`]: 1 warm + `engine.timed_calls` hot in development, by default 3 as in the final
//! evaluation), and its
//! development evaluation checks variants for their answers only ([`check_answers`]: one call per statement, no time
//! read).

use super::score::{CellResult, CellStatus, ScoreError};
use super::totals::{EngineMedian, EngineMedians, TotalsError};
use gendb_runtime::worker::{Unfinished, UnfinishedReason};
use gendb_verification::admission::AdmissionError;
use gendb_verification::admission::execution::TIMED_REPETITIONS;
use gendb_verification::admission::validation::checked_cell_status;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::collections::BTreeMap;
use std::path::Path;

/// Calls per official cell: 1 warm, then 3 hot (the evaluations' protocol; the saved baselines used the same).
pub const OFFICIAL_CALLS: u32 = TIMED_REPETITIONS;
/// Calls per variant cell: 1 warm, then 1 hot.
pub const VARIANT_CALLS: u32 = 2;

/// A variant's identity: its manifest id (`Q07-from_permutation`) and transformation kind.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct VariantOf {
    pub id: String,
    pub kind: String,
}

/// One statement of a matrix: a template, or one of its variants, at one binding, with its encoded engine AST.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EngineStatement {
    /// The template's name (`Q01`..`Q22`); a variant names its template.
    pub template: String,
    pub variant: Option<VariantOf>,
    /// The binding's name (`v0`).
    pub binding: String,
    /// The engine AST bytes of the statement with the binding substituted (encoded before timing).
    pub ast: Vec<u8>,
}

impl EngineStatement {
    /// The statement's name in records and evidence paths: the template, or the variant id.
    pub fn name(&self) -> &str {
        self.variant.as_ref().map_or(self.template.as_str(), |v| v.id.as_str())
    }
}

/// One cell to run: `calls` sequential calls (the first warm) of `statement` at `workers` workers.
#[derive(Clone, Copy, Debug)]
pub struct CellRequest<'a> {
    pub statement: &'a EngineStatement,
    pub workers: usize,
    pub calls: u32,
}

/// Runs one matrix cell in one fresh worker child. Wired in Stage 2 to the engine entry's worker request.
pub trait EngineCellRunner {
    /// Run `cell` with evidence under `work` (a new directory), compare every answer with the saved answers of
    /// `cell.statement`'s template at its binding, and return the cell record of `admission::execution`: at least
    /// `status`, `warm_wall_ns`, `hot_wall_ns` (the hot calls in order) and `median_hot_wall_ns`. An answer the claim
    /// does not allow, a failed child or a refused statement is an `Err`.
    fn run_cell(&self, cell: CellRequest<'_>, work: &Path) -> Result<Value, AdmissionError>;
}

/// The timing of one cell, read from its record.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct CellTiming {
    pub template: String,
    pub variant: Option<VariantOf>,
    pub binding: String,
    pub workers: usize,
    /// The record's comparison status (`saved_answers_agree`, `exact`, ...).
    pub status: String,
    /// Whether the answer was checked (`admission::validation::checked_cell_status`).
    pub checked: bool,
    pub warm_ns: u64,
    pub hot_ns: Vec<u64>,
    pub median_ns: u64,
    /// The runner's full cell record (comparison details, dispatch, usage).
    pub record: Value,
    /// The host's load averages when the cell's lease was taken (absent in records written before they were kept, and
    /// where a comparison records them per pair).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub load_average: Option<LoadAverage>,
}

impl CellTiming {
    /// The cell's status for the score: finished when its answers were checked and every call (warm and hot) ended
    /// within `call_limit_ns` (when given; a call the watchdog let finish just past the limit is over it), unchecked
    /// when every call ended within the limit but no answer was compared.
    pub fn status(&self, call_limit_ns: Option<u64>) -> CellStatus {
        let within = |ns: u64| call_limit_ns.is_none_or(|limit| ns <= limit);
        if !(within(self.warm_ns) && self.hot_ns.iter().all(|&ns| within(ns))) {
            return CellStatus::Unfinished { reason: UnfinishedReason::OverTimeLimit };
        }
        match self.checked {
            true => CellStatus::Finished { median_ns: self.median_ns },
            false => CellStatus::Unchecked { median_ns: self.median_ns },
        }
    }

    /// Read the timing of `cell` from the runner's record; a record without its timings is a tool failure.
    fn from_record(cell: CellRequest<'_>, record: Value) -> Result<Self, AdmissionError> {
        let what = format!("cell {} at {} workers", cell.statement.name(), cell.workers);
        let number = |field: &str| record[field].as_u64().ok_or_else(|| AdmissionError::tool(format!("{what}: record without {field}")));
        let hot_ns: Vec<u64> = record["hot_wall_ns"].as_array().into_iter().flatten().filter_map(Value::as_u64).collect();
        if hot_ns.len() != cell.calls.saturating_sub(1) as usize {
            return Err(AdmissionError::tool(format!("{what}: {} hot calls recorded, {} expected", hot_ns.len(), cell.calls.saturating_sub(1))));
        }
        Ok(Self {
            template: cell.statement.template.clone(),
            variant: cell.statement.variant.clone(),
            binding: cell.statement.binding.clone(),
            workers: cell.workers,
            status: record["status"].as_str().unwrap_or_default().to_string(),
            checked: checked_cell_status(&record["status"]),
            warm_ns: number("warm_wall_ns")?,
            median_ns: number("median_hot_wall_ns")?,
            hot_ns,
            record,
            load_average: None,
        })
    }
}

/// A cell whose call did not finish: the stop (or child failure) as the worker reported it, and the calls before it.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct UnfinishedCell {
    pub template: String,
    pub variant: Option<VariantOf>,
    pub binding: String,
    pub workers: usize,
    pub reason: UnfinishedReason,
    /// The worker's report: the stopped call (statement, repetition, elapsed time, limit, memory) or the child failure.
    pub unfinished: Unfinished,
    /// The calls that finished before the stop (the first is the warm call).
    pub warm_ns: Option<u64>,
    pub hot_ns: Vec<u64>,
    /// The runner's full cell record.
    pub record: Value,
    /// The host's load averages when the cell's lease was taken (see [`CellTiming::load_average`]).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub load_average: Option<LoadAverage>,
}

impl UnfinishedCell {
    fn from_record(cell: CellRequest<'_>, record: Value) -> Result<Self, AdmissionError> {
        let unfinished: Unfinished = serde_json::from_value(record["unfinished"].clone())
            .map_err(|e| AdmissionError::tool(format!("cell {} at {} workers: unreadable unfinished record: {e}", cell.statement.name(), cell.workers)))?;
        Ok(Self {
            template: cell.statement.template.clone(),
            variant: cell.statement.variant.clone(),
            binding: cell.statement.binding.clone(),
            workers: cell.workers,
            reason: unfinished.reason(),
            unfinished,
            warm_ns: record["warm_wall_ns"].as_u64(),
            hot_ns: record["hot_wall_ns"].as_array().into_iter().flatten().filter_map(Value::as_u64).collect(),
            record,
            load_average: None,
        })
    }
}

/// One cell's record as read: timed (every call ended), or unfinished.
#[derive(Clone, Debug, PartialEq)]
pub enum CellRecord {
    Timed(CellTiming),
    Unfinished(UnfinishedCell),
}

/// Read the runner's record of `cell`: [`CellRecord::Unfinished`] when it carries `unfinished`, else its timings (a
/// record without them is a tool failure).
pub fn read_cell(cell: CellRequest<'_>, record: Value) -> Result<CellRecord, AdmissionError> {
    match record.get("unfinished").is_some_and(|u| !u.is_null()) {
        true => UnfinishedCell::from_record(cell, record).map(CellRecord::Unfinished),
        false => CellTiming::from_record(cell, record).map(CellRecord::Timed),
    }
}

/// Which matrix: the official template matrix or the variant matrix.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum MatrixKind {
    Official,
    Variants,
}

impl MatrixKind {
    /// Calls per cell of this kind of matrix ([`OFFICIAL_CALLS`], [`VARIANT_CALLS`]).
    pub fn calls(self) -> u32 {
        match self {
            Self::Official => OFFICIAL_CALLS,
            Self::Variants => VARIANT_CALLS,
        }
    }
}

/// The cells of one matrix, in run order (statement, then worker count).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct EngineMatrix {
    pub kind: MatrixKind,
    pub calls_per_cell: u32,
    pub workers: Vec<usize>,
    pub cells: Vec<CellTiming>,
    /// Cells whose runner failed, recorded by [`run_matrix_recording_failures`] (always empty from [`run_matrix`]): a
    /// failed cell has no median, so its template is missing from the totals at that worker count.
    pub failed: Vec<FailedCell>,
    /// Cells whose call did not finish, recorded by [`run_matrix_recording_failures`] (always empty from
    /// [`run_matrix`]); absent from the JSON when empty (records of unlimited runs keep their form).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub unfinished: Vec<UnfinishedCell>,
}

/// One cell whose runner returned an error (a failed or bounded child, an answer the saved answers do not allow, an
/// unequal echo, a missing input), with that error's failure class and message.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct FailedCell {
    pub template: String,
    pub variant: Option<VariantOf>,
    pub binding: String,
    pub workers: usize,
    pub class: String,
    pub error: String,
    /// The host's load averages when the cell's lease was taken.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub load_average: Option<LoadAverage>,
}

/// The host's load averages (`/proc/loadavg`): 1, 5 and 15 minutes, and the raw line (descriptive; recorded with
/// every timing, as the work rules require).
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct LoadAverage {
    pub one_minute: f64,
    pub five_minutes: f64,
    pub fifteen_minutes: f64,
    pub line: String,
}

/// The load averages of this host now, or `None` when `/proc/loadavg` is unreadable.
pub fn read_load_average() -> Option<LoadAverage> {
    parse_load_average(&std::fs::read_to_string("/proc/loadavg").ok()?)
}

/// The load averages of a `/proc/loadavg` line.
pub fn parse_load_average(line: &str) -> Option<LoadAverage> {
    let mut words = line.split_whitespace();
    let mut next = || words.next()?.parse::<f64>().ok();
    Some(LoadAverage { one_minute: next()?, five_minutes: next()?, fifteen_minutes: next()?, line: line.trim().to_string() })
}

impl EngineMatrix {
    /// The official matrix's template medians at `binding`, for the totals. Variant cells are not medians of the
    /// timing protocol and are refused.
    pub fn medians(&self, binding: &str) -> Result<EngineMedians, TotalsError> {
        if self.kind != MatrixKind::Official {
            return Err(TotalsError("only the official matrix gives the medians of the totals".into()));
        }
        let mut medians = EngineMedians::new(binding);
        for cell in self.cells.iter().filter(|c| c.binding == binding && c.variant.is_none()) {
            medians.insert(&cell.template, cell.workers, EngineMedian { median_ns: cell.median_ns, checked: cell.checked })?;
        }
        Ok(medians)
    }

    /// Cells whose answer was not checked (gating for variants: each must return its template's saved answers).
    pub fn unchecked_cells(&self) -> Vec<&CellTiming> {
        self.cells.iter().filter(|c| !c.checked).collect()
    }

    /// Every official cell's status for the score (`super::score::score`), timed cells judged against
    /// `call_limit_ns` ([`CellTiming::status`]). A matrix with a failed cell has no score: a failure is an error to
    /// review (a refused answer, a tool failure), not a cell state.
    pub fn cell_results(&self, call_limit_ns: Option<u64>) -> Result<Vec<CellResult>, ScoreError> {
        if self.kind != MatrixKind::Official {
            return Err(ScoreError("only the official matrix is scored".into()));
        }
        if let Some(f) = self.failed.first() {
            return Err(ScoreError(format!("{} failed cells (first: {} at {} workers, {}: {}); a failed cell has no score", self.failed.len(), f.template, f.workers, f.class, f.error)));
        }
        let timed = self.cells.iter().map(|c| CellResult { template: c.template.clone(), workers: c.workers, status: c.status(call_limit_ns) });
        let unfinished = self.unfinished.iter().map(|c| CellResult { template: c.template.clone(), workers: c.workers, status: CellStatus::Unfinished { reason: c.reason } });
        Ok(timed.chain(unfinished).collect())
    }
}

/// Run `statements` at every count of `workers`, `calls` calls per cell, one cell per child under `work/<statement>/
/// w<workers>/`, each holding the timing lease. The first failing or unfinished cell ends the matrix with its error
/// (an unfinished cell as an `execution_failure` naming its reason).
pub fn run_matrix<Lease>(
    runner: &impl EngineCellRunner,
    kind: MatrixKind,
    statements: &[EngineStatement],
    workers: &[usize],
    work: &Path,
    timing_lease: impl Fn() -> Result<Lease, String>,
) -> Result<EngineMatrix, AdmissionError> {
    run_cells(runner, kind, statements, workers, kind.calls(), work, timing_lease, false)
}

/// [`run_matrix`], but a cell whose runner fails is recorded in [`EngineMatrix::failed`], an unfinished cell in
/// [`EngineMatrix::unfinished`], and the matrix goes on (the official timing of an admitted engine version: timing
/// records, it does not gate). A failed timing lease or a record without its timings still ends the matrix.
pub fn run_matrix_recording_failures<Lease>(
    runner: &impl EngineCellRunner,
    kind: MatrixKind,
    statements: &[EngineStatement],
    workers: &[usize],
    work: &Path,
    timing_lease: impl Fn() -> Result<Lease, String>,
) -> Result<EngineMatrix, AdmissionError> {
    run_cells(runner, kind, statements, workers, kind.calls(), work, timing_lease, true)
}

/// [`run_matrix_recording_failures`] of official statements with `calls` calls per cell (the first warm): the general
/// line's timings at its plan's call count (`super::protocol::EvaluationPlan::cell_calls`).
pub fn run_official_recording_failures<Lease>(
    runner: &impl EngineCellRunner,
    statements: &[EngineStatement],
    workers: &[usize],
    calls: u32,
    work: &Path,
    timing_lease: impl Fn() -> Result<Lease, String>,
) -> Result<EngineMatrix, AdmissionError> {
    run_cells(runner, MatrixKind::Official, statements, workers, calls, work, timing_lease, true)
}

#[allow(clippy::too_many_arguments)]
fn run_cells<Lease>(
    runner: &impl EngineCellRunner,
    kind: MatrixKind,
    statements: &[EngineStatement],
    workers: &[usize],
    calls: u32,
    work: &Path,
    timing_lease: impl Fn() -> Result<Lease, String>,
    record_failures: bool,
) -> Result<EngineMatrix, AdmissionError> {
    if calls < 2 {
        return Err(AdmissionError::tool(format!("a timed cell needs a warm and at least one hot call, not {calls} calls")));
    }
    let mut cells = Vec::with_capacity(statements.len() * workers.len());
    let mut failed = vec![];
    let mut unfinished = vec![];
    for statement in statements {
        if (kind == MatrixKind::Official) != statement.variant.is_none() {
            return Err(AdmissionError::tool(format!("statement {} does not belong in the {kind:?} matrix", statement.name())));
        }
        for &w in workers {
            let cell = CellRequest { statement, workers: w, calls };
            let (result, load_average) = {
                let _lease = timing_lease().map_err(AdmissionError::tool)?;
                let load_average = read_load_average();
                (runner.run_cell(cell, &work.join(statement.name()).join(format!("w{w}"))), load_average)
            };
            match result {
                Ok(record) => match read_cell(cell, record)? {
                    CellRecord::Timed(timing) => cells.push(CellTiming { load_average, ..timing }),
                    CellRecord::Unfinished(stopped) if record_failures => unfinished.push(UnfinishedCell { load_average, ..stopped }),
                    CellRecord::Unfinished(stopped) => {
                        return Err(AdmissionError::execution(format!(
                            "cell {} at {w} workers did not finish ({:?}); evidence {}",
                            statement.name(),
                            stopped.reason,
                            work.join(statement.name()).join(format!("w{w}")).display()
                        )));
                    }
                },
                Err(e) if record_failures => failed.push(FailedCell {
                    template: statement.template.clone(),
                    variant: statement.variant.clone(),
                    binding: statement.binding.clone(),
                    workers: w,
                    class: e.class.to_string(),
                    error: e.message,
                    load_average,
                }),
                Err(e) => return Err(e),
            }
        }
    }
    Ok(EngineMatrix { kind, calls_per_cell: calls, workers: workers.to_vec(), cells, failed, unfinished })
}

/// One statement's answer check ([`check_answers`]): one call in a fresh child, its answer compared with the saved
/// answers; no time is read.
#[derive(Clone, Debug, PartialEq, Serialize, Deserialize)]
pub struct AnswerCell {
    pub template: String,
    pub variant: Option<VariantOf>,
    pub binding: String,
    pub workers: usize,
    /// The record's comparison status (`saved_answers_agree`, `not_compared`, `unfinished`, ...).
    pub status: String,
    /// Whether the answer was compared with the saved answers and agreed (`admission::validation::checked_cell_status`).
    pub checked: bool,
    /// The call did not finish (a limit, or a child failure): nothing was compared.
    pub unfinished: Option<UnfinishedReason>,
    /// The runner's full cell record.
    pub record: Value,
    /// The host's load averages when the cell's lease was taken.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub load_average: Option<LoadAverage>,
}

/// Check the answers of `statements` (templates or variants) at `workers` workers: one call each in a fresh child under
/// `work/<statement>/w<workers>/`, each under its own timing lease (the calls share the host with timings). The first
/// runner error (an answer the saved answers do not allow, a failed child, a refused statement) ends the check with
/// that error; a call over a limit is recorded unfinished and the check goes on.
pub fn check_answers<Lease>(
    runner: &impl EngineCellRunner,
    statements: &[EngineStatement],
    workers: usize,
    work: &Path,
    timing_lease: impl Fn() -> Result<Lease, String>,
) -> Result<Vec<AnswerCell>, AdmissionError> {
    let mut cells = Vec::with_capacity(statements.len());
    for statement in statements {
        let cell = CellRequest { statement, workers, calls: 1 };
        let (record, load_average) = {
            let _lease = timing_lease().map_err(AdmissionError::tool)?;
            let load_average = read_load_average();
            (runner.run_cell(cell, &work.join(statement.name()).join(format!("w{workers}")))?, load_average)
        };
        let unfinished = match record.get("unfinished").filter(|u| !u.is_null()) {
            Some(stopped) => Some(
                serde_json::from_value::<Unfinished>(stopped.clone())
                    .map_err(|e| AdmissionError::tool(format!("{} at {workers} workers: unreadable unfinished record: {e}", statement.name())))?
                    .reason(),
            ),
            None => None,
        };
        cells.push(AnswerCell {
            template: statement.template.clone(),
            variant: statement.variant.clone(),
            binding: statement.binding.clone(),
            workers,
            status: record["status"].as_str().unwrap_or_default().to_string(),
            checked: unfinished.is_none() && checked_cell_status(&record["status"]),
            unfinished,
            record,
            load_average,
        });
    }
    Ok(cells)
}

/// One variant cell against its template's official median at the same worker count.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct VariantRatio {
    pub variant: VariantOf,
    pub template: String,
    pub workers: usize,
    /// The variant's one hot call.
    pub variant_hot_ns: u64,
    pub template_median_ns: u64,
    /// `variant_hot_ns / template_median_ns`.
    pub ratio: f64,
}

/// Per worker count: how many variant cells were compared, their largest ratio and the geometric mean of the ratios.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct RatioSummary {
    pub workers: usize,
    pub compared: usize,
    pub largest: Option<VariantRatio>,
    pub geometric_mean: Option<f64>,
}

/// The variant/template time ratios: a report for the author's feedback and the operator's review, with no threshold.
#[derive(Clone, Debug, PartialEq, Serialize)]
pub struct VariantRatioReport {
    pub rows: Vec<VariantRatio>,
    pub summary: Vec<RatioSummary>,
    /// Variant cells without an official template median at the same worker count (not compared).
    pub without_template: Vec<String>,
    pub note: &'static str,
}

const RATIO_NOTE: &str = "report only: no bound applies; a large ratio is a reason for the operator to inspect the \
planner, never an automatic rejection. One hot call per variant cell, so a ratio carries the noise of a single sample; variants whose \
AST equals the template's (wrapped tables: the frontend elides `SELECT *` wrappers) measure only that noise";

/// The ratio of every variant cell of `variants` to its template's median in `official` at the same worker count.
pub fn variant_ratios(official: &EngineMatrix, variants: &EngineMatrix) -> VariantRatioReport {
    let medians: BTreeMap<(&str, usize), u64> =
        official.cells.iter().filter(|c| c.variant.is_none()).map(|c| ((c.template.as_str(), c.workers), c.median_ns)).collect();
    let mut rows = Vec::new();
    let mut without_template = Vec::new();
    for cell in &variants.cells {
        let (Some(variant), Some(hot)) = (&cell.variant, cell.hot_ns.first()) else { continue };
        match medians.get(&(cell.template.as_str(), cell.workers)) {
            Some(&median) => rows.push(VariantRatio {
                variant: variant.clone(),
                template: cell.template.clone(),
                workers: cell.workers,
                variant_hot_ns: *hot,
                template_median_ns: median,
                ratio: *hot as f64 / median.max(1) as f64,
            }),
            None => without_template.push(format!("{} at {} workers", variant.id, cell.workers)),
        }
    }
    let summary = variants
        .workers
        .iter()
        .map(|&w| {
            let at: Vec<&VariantRatio> = rows.iter().filter(|r| r.workers == w).collect();
            let largest = at.iter().copied().max_by(|a, b| a.ratio.total_cmp(&b.ratio)).cloned();
            let geometric_mean = (!at.is_empty()).then(|| (at.iter().map(|r| r.ratio.max(f64::MIN_POSITIVE).ln()).sum::<f64>() / at.len() as f64).exp());
            RatioSummary { workers: w, compared: at.len(), largest, geometric_mean }
        })
        .collect();
    VariantRatioReport { rows, summary, without_template, note: RATIO_NOTE }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;

    /// A runner that returns a canned record per cell (hot calls = `base * workers-index` style values) and logs each
    /// call with the number of leases held at that moment.
    struct Canned {
        log: RefCell<Vec<String>>,
        leases: RefCell<u32>,
        hot: fn(&str, usize, u32) -> Vec<u64>,
        status: &'static str,
    }

    impl EngineCellRunner for Canned {
        fn run_cell(&self, cell: CellRequest<'_>, work: &Path) -> Result<Value, AdmissionError> {
            self.log.borrow_mut().push(format!("{} w{} c{} leases={} {}", cell.statement.name(), cell.workers, cell.calls, self.leases.borrow(), work.display()));
            let hot = (self.hot)(cell.statement.name(), cell.workers, cell.calls - 1);
            let mut sorted = hot.clone();
            sorted.sort_unstable();
            Ok(serde_json::json!({"status":self.status,"warm_wall_ns":1,"hot_wall_ns":hot,"median_hot_wall_ns":sorted[sorted.len() / 2]}))
        }
    }

    struct Lease<'a>(&'a RefCell<u32>);
    impl Drop for Lease<'_> {
        fn drop(&mut self) {
            *self.0.borrow_mut() -= 1;
        }
    }

    fn statement(template: &str, variant: Option<&str>) -> EngineStatement {
        EngineStatement {
            template: template.into(),
            variant: variant.map(|kind| VariantOf { id: format!("{template}-{kind}"), kind: kind.into() }),
            binding: "v0".into(),
            ast: vec![1, 2, 3],
        }
    }

    fn runner(hot: fn(&str, usize, u32) -> Vec<u64>, status: &'static str) -> Canned {
        Canned { log: RefCell::new(vec![]), leases: RefCell::new(0), hot, status }
    }

    fn run(r: &Canned, kind: MatrixKind, statements: &[EngineStatement]) -> Result<EngineMatrix, AdmissionError> {
        run_matrix(r, kind, statements, &[1, 32], Path::new("work"), || {
            *r.leases.borrow_mut() += 1;
            Ok::<_, String>(Lease(&r.leases))
        })
    }

    /// Cells run in statement-then-worker order, one lease held per cell, 1 warm + 3 hot calls; the medians go to the
    /// totals keyed by template and worker count.
    #[test]
    fn official_matrix_runs_each_cell_under_its_own_lease() {
        let r = runner(|name, w, hot| (0..hot as u64).map(|i| (if name == "Q01" { 100 } else { 10 }) * w as u64 + i).collect(), "saved_answers_agree");
        let matrix = run(&r, MatrixKind::Official, &[statement("Q01", None), statement("Q02", None)]).unwrap();
        assert_eq!(*r.log.borrow(), ["Q01 w1 c4 leases=1 work/Q01/w1", "Q01 w32 c4 leases=1 work/Q01/w32", "Q02 w1 c4 leases=1 work/Q02/w1", "Q02 w32 c4 leases=1 work/Q02/w32"]);
        assert_eq!(*r.leases.borrow(), 0, "every lease released");
        let medians = matrix.medians("v0").unwrap();
        assert_eq!(medians.get("Q01", 32), Some(EngineMedian { median_ns: 3201, checked: true }));
        assert_eq!(matrix.cells[0].hot_ns, [100, 101, 102]);
        assert!(matrix.unchecked_cells().is_empty());
    }

    /// Variants run 1 warm + 1 hot; the ratio report compares each with its template's official median and applies no
    /// bound; a matrix holds only its own kind of statement.
    #[test]
    fn variant_ratios_are_reported_without_a_bound() {
        let official = run(&runner(|_, w, hot| vec![1000 * w as u64; hot as usize], "saved_answers_agree"), MatrixKind::Official, &[statement("Q01", None)]).unwrap();
        let r = runner(|name, w, hot| vec![if name.ends_with("from_permutation") { 50_000 * w as u64 } else { 900 * w as u64 }; hot as usize], "saved_answers_agree");
        let variants = run(&r, MatrixKind::Variants, &[statement("Q01", Some("from_permutation")), statement("Q01", Some("wrapped_tables")), statement("Q02", Some("wrapped_tables"))]).unwrap();
        assert!(r.log.borrow().iter().all(|l| l.contains(" c2 ")), "{:?}", r.log.borrow());
        let report = variant_ratios(&official, &variants);
        assert_eq!(report.rows.len(), 4);
        assert_eq!(report.without_template, ["Q02-wrapped_tables at 1 workers", "Q02-wrapped_tables at 32 workers"]);
        let at1 = &report.summary[0];
        assert_eq!((at1.compared, at1.largest.as_ref().unwrap().variant.id.as_str(), at1.largest.as_ref().unwrap().ratio), (2, "Q01-from_permutation", 50.0));
        assert!((at1.geometric_mean.unwrap() - (50.0f64 * 0.9).sqrt()).abs() < 1e-9);
        assert!(variants.medians("v0").is_err(), "variant cells are not totals medians");
        assert!(run(&r, MatrixKind::Variants, &[statement("Q01", None)]).is_err());
        assert!(run(&r, MatrixKind::Official, &[statement("Q01", Some("wrapped_tables"))]).is_err());
    }

    /// A cell whose answers were not checked is listed (gating for variants) and reaches the totals as unchecked; a
    /// record without its timings is a tool failure.
    #[test]
    fn unchecked_and_malformed_records() {
        let matrix = run(&runner(|_, _, hot| vec![5; hot as usize], "status_only"), MatrixKind::Official, &[statement("Q03", None)]).unwrap();
        assert_eq!(matrix.unchecked_cells().len(), 2);
        assert!(!matrix.medians("v0").unwrap().get("Q03", 1).unwrap().checked);
        let short = runner(|_, _, _| vec![5], "saved_answers_agree");
        let error = run(&short, MatrixKind::Official, &[statement("Q03", None)]).unwrap_err();
        assert!(error.message.contains("1 hot calls recorded, 3 expected"), "{error}");
    }

    /// Recording failures, a failing cell is listed with its class and error and has no median (its template is
    /// missing from the totals at that worker count) while the other cells still run; without recording it ends the
    /// matrix.
    #[test]
    fn failed_cells_are_recorded_when_asked() {
        struct FailsAt32(Canned);
        impl EngineCellRunner for FailsAt32 {
            fn run_cell(&self, cell: CellRequest<'_>, work: &Path) -> Result<Value, AdmissionError> {
                if cell.statement.template == "Q02" && cell.workers == 32 {
                    return Err(AdmissionError::execution("the child exceeded its bound"));
                }
                self.0.run_cell(cell, work)
            }
        }
        let r = FailsAt32(runner(|_, _, hot| vec![7; hot as usize], "saved_answers_agree"));
        let statements = [statement("Q01", None), statement("Q02", None)];
        let matrix = run_matrix_recording_failures(&r, MatrixKind::Official, &statements, &[1, 32], Path::new("work"), || Ok::<_, String>(())).unwrap();
        assert_eq!(matrix.cells.len(), 3);
        let failed = &matrix.failed[0];
        assert_eq!((failed.template.as_str(), failed.workers, failed.class.as_str()), ("Q02", 32, "execution_failure"));
        assert_eq!(matrix.medians("v0").unwrap().get("Q02", 32), None);
        assert!(run_matrix(&r, MatrixKind::Official, &statements, &[1, 32], Path::new("work"), || Ok::<_, String>(())).is_err());
    }

    /// The general line's development timing: official cells at the default 4 calls, 1 warm + 3 hot, the median hot
    /// call the cell's time; a timed cell needs a hot call. The answer check makes one call per statement and reads no time: an
    /// agreeing answer is checked, an unfinished call or an uncompared answer is not, and a refused answer ends it.
    #[test]
    fn development_cells_and_answer_checks() {
        let r = runner(|_, w, hot| vec![10 * w as u64; hot as usize], "saved_answers_agree");
        let calls = crate::engine::protocol::development(crate::engine::protocol::DEFAULT_TIMED_CALLS).cell_calls;
        let matrix = run_official_recording_failures(&r, &[statement("Q01", None)], &[1, 32], calls, Path::new("work"), || Ok::<_, String>(())).unwrap();
        assert_eq!(*r.log.borrow(), ["Q01 w1 c4 leases=0 work/Q01/w1", "Q01 w32 c4 leases=0 work/Q01/w32"]);
        assert_eq!((matrix.calls_per_cell, matrix.cells[1].hot_ns.clone(), matrix.cells[1].median_ns), (4, vec![320; 3], 320));
        assert_eq!(matrix.cell_results(Some(1_000)).unwrap()[1].status, CellStatus::Finished { median_ns: 320 });
        assert!(run_official_recording_failures(&r, &[statement("Q01", None)], &[1], 1, Path::new("work"), || Ok::<_, String>(())).is_err(), "no hot call");

        struct OneCall(RefCell<Vec<String>>);
        impl EngineCellRunner for OneCall {
            fn run_cell(&self, cell: CellRequest<'_>, work: &Path) -> Result<Value, AdmissionError> {
                self.0.borrow_mut().push(format!("{} c{} {}", cell.statement.name(), cell.calls, work.display()));
                let unanswered = serde_json::json!({"warm_wall_ns":null,"hot_wall_ns":[],"median_hot_wall_ns":null});
                Ok(match cell.statement.template.as_str() {
                    "Q01" => serde_json::json!({"status":"saved_answers_agree","warm_wall_ns":5,"hot_wall_ns":[],"median_hot_wall_ns":null}),
                    "Q02" => serde_json::json!({"status":"unfinished","warm_wall_ns":null,"hot_wall_ns":[],"median_hot_wall_ns":null,
                        "unfinished":{"reason":"over_time_limit","statement":0,"workers":cell.workers,"repetition":0,"elapsed_ns":9,"limit":9,"anon_bytes":null,"peak_anon_bytes":null}}),
                    "Q03" => {
                        let mut record = unanswered;
                        record["status"] = "not_compared".into();
                        record
                    }
                    _ => return Err(AdmissionError::execution("rows disagree with the saved answers")),
                })
            }
        }
        let variants = [statement("Q01", Some("wrapped_tables")), statement("Q02", Some("wrapped_tables")), statement("Q03", Some("from_permutation"))];
        let one = OneCall(RefCell::new(vec![]));
        let checked = check_answers(&one, &variants, 64, Path::new("v"), || Ok::<_, String>(())).unwrap();
        assert_eq!(*one.0.borrow(), ["Q01-wrapped_tables c1 v/Q01-wrapped_tables/w64", "Q02-wrapped_tables c1 v/Q02-wrapped_tables/w64", "Q03-from_permutation c1 v/Q03-from_permutation/w64"]);
        let states: Vec<(bool, Option<UnfinishedReason>)> = checked.iter().map(|c| (c.checked, c.unfinished)).collect();
        assert_eq!(states, [(true, None), (false, Some(UnfinishedReason::OverTimeLimit)), (false, None)]);
        assert!(checked.iter().all(|c| c.workers == 64 && c.load_average.is_some()));
        let wrong = [statement("Q01", Some("wrapped_tables")), statement("Q04", Some("wrapped_tables")), statement("Q02", Some("wrapped_tables"))];
        let refused = check_answers(&OneCall(RefCell::new(vec![])), &wrong, 64, Path::new("v"), || Ok::<_, String>(())).unwrap_err();
        assert!(refused.message.contains("rows disagree"), "{refused}");
    }

    #[test]
    fn load_average_parses() {
        let load = parse_load_average("7.83 9.96 10.91 7/37349 507601\n").unwrap();
        assert_eq!((load.one_minute, load.five_minutes, load.fifteen_minutes), (7.83, 9.96, 10.91));
        assert_eq!(load.line, "7.83 9.96 10.91 7/37349 507601");
        assert!(parse_load_average("x 1 2").is_none());
        assert!(read_load_average().is_some(), "this host has /proc/loadavg");
    }

    /// A record carrying `unfinished` (a call stopped at a limit): a recording matrix keeps it with its reason and the
    /// calls before the stop and goes on; a gating matrix ends there; the scored statuses are finished, unfinished, or
    /// over the limit for a timed cell whose call ran past it; a matrix with a failed cell has no score.
    #[test]
    fn unfinished_cells_are_recorded_and_scored() {
        struct StopsQ02(Canned);
        impl EngineCellRunner for StopsQ02 {
            fn run_cell(&self, cell: CellRequest<'_>, work: &Path) -> Result<Value, AdmissionError> {
                if cell.statement.template != "Q02" {
                    return self.0.run_cell(cell, work);
                }
                let (reason, limit) = if cell.workers == 1 { ("over_time_limit", 1_000_000_000u64) } else { ("over_memory_limit", 1u64 << 30) };
                Ok(serde_json::json!({"status":"saved_answers_agree","warm_wall_ns":5,"hot_wall_ns":[6],"median_hot_wall_ns":6,
                    "unfinished":{"reason":reason,"statement":0,"workers":cell.workers,"repetition":2,"elapsed_ns":1_000_000_001u64,"limit":limit,"anon_bytes":7,"peak_anon_bytes":9}}))
            }
        }
        let r = StopsQ02(runner(|_, w, hot| vec![700 * w as u64; hot as usize], "saved_answers_agree"));
        let statements = [statement("Q01", None), statement("Q02", None)];
        let matrix = run_matrix_recording_failures(&r, MatrixKind::Official, &statements, &[1, 32], Path::new("work"), || Ok::<_, String>(())).unwrap();
        assert_eq!((matrix.cells.len(), matrix.unfinished.len(), matrix.failed.len()), (2, 2, 0));
        let stopped = &matrix.unfinished[0];
        assert_eq!((stopped.template.as_str(), stopped.workers, stopped.reason, stopped.warm_ns, stopped.hot_ns.clone()), ("Q02", 1, UnfinishedReason::OverTimeLimit, Some(5), vec![6]));
        assert_eq!(stopped.unfinished.stopped().map(|c| c.repetition), Some(2));
        assert_eq!(matrix.unfinished[1].reason, UnfinishedReason::OverMemoryLimit);
        assert_eq!(matrix.medians("v0").unwrap().get("Q02", 1), None, "an unfinished cell has no median");
        let results = matrix.cell_results(Some(1_000_000)).unwrap();
        let status = |t: &str, w: usize| results.iter().find(|c| c.template == t && c.workers == w).unwrap().status;
        assert_eq!(status("Q01", 1), CellStatus::Finished { median_ns: 700 });
        assert_eq!(status("Q02", 32), CellStatus::Unfinished { reason: UnfinishedReason::OverMemoryLimit });
        let over = matrix.cell_results(Some(10_000)).unwrap();
        assert_eq!(over.iter().find(|c| c.template == "Q01" && c.workers == 32).unwrap().status, CellStatus::Unfinished { reason: UnfinishedReason::OverTimeLimit },
            "a timed call past the limit is not finished");
        let unchecked = run_matrix_recording_failures(&runner(|_, _, hot| vec![3; hot as usize], "status_only"), MatrixKind::Official, &[statement("Q01", None)], &[1], Path::new("work"), || Ok::<_, String>(())).unwrap();
        assert_eq!(unchecked.cell_results(None).unwrap()[0].status, CellStatus::Unchecked { median_ns: 3 });
        let error = run_matrix(&r, MatrixKind::Official, &statements, &[1, 32], Path::new("work"), || Ok::<_, String>(())).unwrap_err();
        assert!(error.message.contains("Q02 at 1 workers did not finish (OverTimeLimit)"), "{error}");
        let mut failed = matrix.clone();
        failed.failed.push(FailedCell { template: "Q01".into(), variant: None, binding: "v0".into(), workers: 1, class: "execution_failure".into(), error: "rows disagree".into(), load_average: None });
        assert!(matrix.cells.iter().all(|c| c.load_average.is_some()) && matrix.unfinished.iter().all(|c| c.load_average.is_some()), "load averages are recorded per cell");
        assert!(failed.cell_results(None).is_err(), "a failed cell has no score");
        let restored: EngineMatrix = serde_json::from_value(serde_json::to_value(&matrix).unwrap()).unwrap();
        assert_eq!(restored, matrix);
        let mut earlier = serde_json::to_value(&matrix).unwrap();
        earlier.as_object_mut().unwrap().remove("unfinished");
        assert!(serde_json::from_value::<EngineMatrix>(earlier).unwrap().unfinished.is_empty(), "records written before limits still read");
    }
}
