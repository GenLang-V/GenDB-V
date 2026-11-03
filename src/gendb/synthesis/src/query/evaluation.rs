//! Tests of a compiled query library over its storage assets: the evaluation of a submission after its whole-crate
//! verification, and the author's diagnostic trial/profile jobs. Both run the framework checks of
//! `admission::stored_execution`; neither is a proof, and neither builds data: the storage assets are the admitted
//! (or session-checked) assets of the storage uses for the current capture.

use super::session::QuerySession;
use crate::prompts::{EarlyStop, RuntimeTarget};
use gendb_verification::admission::bindings::CONCRETE_BINDING;
use gendb_artifacts::ContentId;
use gendb_frontend::params::parse_arguments;
use gendb_storage::io::PartAccess;
use gendb_verification::admission::AdmissionError;
use gendb_verification::admission::validation::checked_cell_status;
use gendb_verification::admission::execution::{PROFILE_REPETITIONS, TIMED_REPETITIONS};
use gendb_verification::admission::stored_execution::{
    StorageUseRun, TinyBuilder, TinyCaseSelection, check_stored_parameter_refusals, check_stored_prepared_data, check_stored_prepared_data_measured,
    check_stored_tiny_cases,
};
use gendb_verification::obligations::{DeclaredSource, StorageName};
use serde_json::{Value, json};
use std::path::{Path, PathBuf};

/// Kind of a diagnostic local job.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TrialKind {
    /// 1 warm + [`DEFAULT_TRIAL_HOT_CALLS`] hot calls per cell, or the author's `hot_calls`.
    Trial,
    /// 1 warm + 1 measured call, with per-call dispatch and CPU usage.
    Profile,
}

/// One storage use of a candidate with its asset for the current capture.
#[derive(Clone, Debug)]
pub struct ResolvedStorage {
    pub name: StorageName,
    pub declaration: DeclaredSource,
    pub package: ContentId,
    /// Whether the package is admitted (a workspace storage is admitted at qualification).
    pub admitted: bool,
    /// The storage's checked library.
    pub library: PathBuf,
    /// How its tiny-case assets are built (its library, from columns or from its sources' tiny assets).
    pub tiny: TinyBuilder,
    pub asset: ContentId,
    /// The asset's parts directory in the library.
    pub parts: PathBuf,
    pub storage_bytes: u64,
    pub build_wall_ns: u64,
    /// Whether resolving it built the asset now (its first use for this capture).
    pub asset_built_now: bool,
    /// Whether its builder assumes the run's declared integrity constraints (storage entry v2).
    pub assumes_declared_constraints: bool,
}

impl ResolvedStorage {
    fn run(&self) -> StorageUseRun<'_> {
        StorageUseRun {
            name: &self.name,
            declaration: &self.declaration,
            builder: &self.tiny,
            prepared_parts: &self.parts,
            stored_bytes: self.storage_bytes,
            assumes_declared_constraints: self.assumes_declared_constraints,
        }
    }
}

/// Kernel advice of every evaluation, trial and profile: the default (normal OS readahead, as when serving) and no
/// page drop. Requested bytes and the child's device reads are different quantities, both descriptive; no run is a
/// cold-cache measurement.
fn part_access() -> PartAccess {
    PartAccess::default()
}

/// Hot calls per cell of a local trial (after 1 warm call) unless the author asks for more (`hot_calls`): fast
/// feedback; one sample gives no spread estimate. Official evaluations and final measurements keep 1 warm + 3 hot.
pub const DEFAULT_TRIAL_HOT_CALLS: u32 = 1;

/// Annotate each trial cell (`binding`, `workers`, `median_hot_wall_ns`, `hot_wall_ns`) with the user's target at
/// that cell, the early-stop bar (target / factor), the spread of its hot calls and whether it meets the bar.
fn annotate_cells(cells: &mut [Value], targets: &[RuntimeTarget], early_stop: Option<EarlyStop>) {
    let factor = early_stop.map_or(1, |stop| u64::from(stop.min_speedup.max(1)));
    for cell in cells {
        let binding = cell["binding"].as_str().unwrap_or(CONCRETE_BINDING).to_string();
        let target = targets.iter().find(|t| t.binding_name() == binding && Some(t.workers as u64) == cell["workers"].as_u64()).map(|t| t.median_ns);
        let samples: Vec<u64> = cell["hot_wall_ns"].as_array().into_iter().flatten().filter_map(Value::as_u64).collect();
        let median = cell["median_hot_wall_ns"].as_u64();
        cell["target_ns"] = json!(target);
        cell["bar_ns"] = json!(target.map(|t| t / factor));
        cell["min_hot_ns"] = json!(samples.iter().min());
        cell["max_hot_ns"] = json!(samples.iter().max());
        cell["met_bar"] = json!(median.zip(target).map(|(m, t)| checked_cell_status(&cell["status"]) && u128::from(m) * u128::from(factor) <= u128::from(t)));
        cell["speedup_over_target"] = json!(median.zip(target).map(|(m, t)| format!("{:.2}x", t as f64 / m.max(1) as f64)));
    }
}

/// One line per trial cell for the author, and whether every timed cell meets the bar (`all_cells_meet_bar`; null
/// without targets).
fn matrix_summary(prepared_data: &Value, early_stop: Option<EarlyStop>) -> Value {
    let cells: Vec<&Value> = prepared_data["cells"].as_array().into_iter().flatten().collect();
    let lines: Vec<String> = cells
        .iter()
        .map(|c| format!("{} @ {} workers: {} median {} ns (min {}, max {}), target {}, bar {}, met {}",
            c["binding"].as_str().unwrap_or(CONCRETE_BINDING), c["workers"], c["status"].as_str().unwrap_or("?"), c["median_hot_wall_ns"], c["min_hot_ns"], c["max_hot_ns"], c["target_ns"], c["bar_ns"], c["met_bar"]))
        .collect();
    let all = cells.iter().map(|c| c["met_bar"].as_bool()).collect::<Option<Vec<bool>>>().map(|met| met.iter().all(|m| *m));
    json!({"cells":lines,"all_cells_meet_bar":all,"factor":early_stop.map(|s| s.min_speedup),
        "note":"a local trial is diagnostic: only the official evaluation of a submission counts for the early stop; with one hot call per cell (the default) median, min and max are that one sample, with no spread estimate"})
}

/// How `score_ns` is computed (recorded with every evaluation).
pub const SCORE_RULE: &str = "geometric mean of the hot medians over every benchmark binding x configured worker count (each cell weighs equally), rounded to whole ns; absent unless every cell was measured";

/// The score of the measurement cells of one evaluation: the geometric mean of their hot medians (`median_ns`, at
/// least 1 ns), every cell weighing equally, rounded to whole nanoseconds (evaluations are qualification evidence, whose
/// records hold no floats). `None` unless exactly `cells` cells have a median: a matrix with a missing cell is not
/// ranked.
pub fn matrix_score(measurements: &[Value], cells: usize) -> Option<u64> {
    let medians: Vec<f64> = measurements.iter().filter_map(|m| m["median_ns"].as_u64()).map(|n| n.max(1) as f64).collect();
    (cells > 0 && medians.len() == cells && measurements.len() == cells).then(|| (medians.iter().map(|m| m.ln()).sum::<f64>() / cells as f64).exp().round() as u64)
}

/// The per-use facts of an evaluation record.
fn storage_record(storages: &[ResolvedStorage]) -> Value {
    json!(storages.iter().map(|s| json!({"name":s.name.as_str(),"package":s.package,"admitted":s.admitted,"asset":s.asset,
        "storage_bytes":s.storage_bytes,"build_wall_ns":s.build_wall_ns,"asset_built_now":s.asset_built_now})).collect::<Vec<_>>())
}

impl QuerySession {
    /// Evaluate a submission's compiled `library` over `storages` in `evaluation_dir`: query the prepared data at every
    /// admission binding and configured worker count (under `timing_lease` for the execution-time objective; the
    /// benchmark bindings 1 warm + 3 hot calls, the other admission bindings one untimed test call), probe out-of-domain
    /// arguments and run every tiny case. The measurements are the cells of the benchmark bindings at every configured
    /// worker count; the score is their [`matrix_score`].
    pub fn evaluate_submission<Lease>(
        &self,
        evaluation_dir: &Path,
        library: &Path,
        storages: &[ResolvedStorage],
        timing_lease: impl Fn() -> Result<Lease, String>,
    ) -> Result<Value, AdmissionError> {
        let execution = evaluation_dir.join("execution");
        let runs: Vec<StorageUseRun<'_>> = storages.iter().map(ResolvedStorage::run).collect();
        let benchmark = &self.statement().benchmark;
        let prepared_data = {
            let _lease = if self.performance { Some(timing_lease().map_err(AdmissionError::tool)?) } else { None };
            check_stored_prepared_data_measured(&self.runner, &self.preflight, &self.references, library, &runs, part_access(), &execution.join("query"), benchmark, &self.worker_counts, TIMED_REPETITIONS)?
        };
        let refusals = check_stored_parameter_refusals(&self.runner, &self.preflight, library, &runs, &execution.join("parameter-refusals"))?;
        let every_case = TinyCaseSelection::every(&self.preflight, &self.worker_counts);
        let cases = check_stored_tiny_cases(&self.runner, &self.preflight, library, &runs, &execution.join("cases"), &every_case)?;
        let benchmark = self.statement().benchmark_names();
        let measurements: Vec<Value> = prepared_data["cells"]
            .as_array()
            .into_iter()
            .flatten()
            .filter(|c| c["binding"].as_str().is_some_and(|b| benchmark.contains(&b)))
            .map(|c| json!({"workers":c["workers"],"status":c["status"],"binding":c["binding"],"arguments":c["arguments"],"median_ns":c["median_hot_wall_ns"],"samples_ns":c["hot_wall_ns"],
                "warm_ns":c["warm_wall_ns"],"calling_thread_share_permille":c["calling_thread_share_permille"],
                "storage_requests":c["storage_requests"],"process_io":c["process_io"],
                "boundary":"wall time of one library query call over the mapped storage parts (hot); storage builds, compile, process start and decoding excluded"}))
            .collect();
        let score = matrix_score(&measurements, benchmark.len() * self.worker_counts.len());
        Ok(json!({"measurements":measurements,"score_ns":score,"score_rule":SCORE_RULE,"benchmark_bindings":benchmark,
            "library":library,"storage":storage_record(storages),
            "requested_bytes_meaning":"storage_requests count the verified extent requests of each use (requests, elements, bytes; overlapping or repeated extents count again; saturating); they are not device reads. process_io.read_bytes is the child's device read delta, environment-dependent (page cache)",
            "real_data":prepared_data,"parameter_refusals":refusals,"boundary":cases}))
    }

    /// A diagnostic trial or profile of a compiled `library` over `storages` in the local job directory `job`, holding
    /// the host timing lease (`timing_lease`) while it times, so local timings never overlap other timings.
    ///
    /// A trial times a matrix: the admission binding named by `arguments`, or every benchmark binding when absent (the
    /// first admission binding for a statement without benchmark bindings), at `workers`, or every configured worker
    /// count when absent; each cell 1 warm + `hot_calls` (default [`DEFAULT_TRIAL_HOT_CALLS`]) hot calls, reported
    /// against the user's target and early-stop bar ([`annotate_cells`]). A profile times one cell (`workers` required)
    /// with 1 warm + 1 measured call.
    /// The tiny cases run at the timed worker counts unless `tiny_cases_passed` (an earlier job of identical crate
    /// content and storages passed them; the result says so). `bound`: the author's per-child timeout in seconds.
    #[allow(clippy::too_many_arguments)]
    pub fn trial<Lease>(
        &self,
        job: &Path,
        library: &Path,
        storages: &[ResolvedStorage],
        kind: TrialKind,
        workers: Option<usize>,
        hot_calls: Option<u32>,
        bound: Option<u64>,
        arguments: Option<&[String]>,
        tiny_cases_passed: bool,
        timing_lease: impl Fn() -> Result<Lease, String>,
    ) -> Result<Value, AdmissionError> {
        let workers: Vec<usize> = match workers {
            Some(w) if self.worker_counts.contains(&w) => vec![w],
            Some(_) => return Err(AdmissionError::missing_input(format!("workers must be one of {:?}", self.worker_counts))),
            None if kind == TrialKind::Profile => return Err(AdmissionError::missing_input("profile times one cell: workers is required")),
            None => self.worker_counts.clone(),
        };
        let bindings = match (arguments, kind) {
            (Some(_), _) | (None, TrialKind::Profile) => vec![self.binding_of(arguments)?],
            (None, TrialKind::Trial) if self.statement().benchmark.is_empty() => vec![0],
            (None, TrialKind::Trial) => self.statement().benchmark.clone(),
        };
        let runs: Vec<StorageUseRun<'_>> = storages.iter().map(ResolvedStorage::run).collect();
        let repetitions = match kind {
            TrialKind::Trial => hot_calls.unwrap_or(DEFAULT_TRIAL_HOT_CALLS).saturating_add(1),
            TrialKind::Profile => PROFILE_REPETITIONS,
        };
        let mut prepared_data = {
            let _lease = timing_lease().map_err(AdmissionError::tool)?;
            check_stored_prepared_data(&self.runner, &self.preflight, &self.references, library, &runs, part_access(), &job.join("query"), &bindings, &workers, repetitions, bound)?
        };
        if let Some(cells) = prepared_data["cells"].as_array_mut() {
            annotate_cells(cells, &self.runtime_targets, self.early_stop);
        }
        let cases = if tiny_cases_passed && !self.preflight.validation.formal {
            json!({"reused":true,"note":"an earlier job of identical crate content and storages passed every tiny case; not rerun"})
        } else {
            check_stored_tiny_cases(&self.runner, &self.preflight, library, &runs, &job.join("cases"), &TinyCaseSelection::every(&self.preflight, &workers))?
        };
        Ok(json!({"status":"allowed","workers":workers,"bindings":bindings.iter().map(|&b| &self.statement().bindings[b]).collect::<Vec<_>>(),
            "storage":storage_record(storages),"real_data":prepared_data,"boundary":cases,
            "matrix":matrix_summary(&prepared_data, self.early_stop)}))
    }

    /// The admission binding named by `arguments` (texts of the free parameters in slot order), default the first.
    fn binding_of(&self, arguments: Option<&[String]>) -> Result<usize, AdmissionError> {
        let statement = self.statement();
        let Some(texts) = arguments else { return Ok(0) };
        let values = parse_arguments(&statement.instance.free, texts).map_err(|e| AdmissionError::missing_input(format!("arguments: {e}")))?;
        statement.bindings.iter().position(|b| b.values == values).ok_or_else(|| {
            AdmissionError::missing_input(format!(
                "arguments {texts:?} are not an admission binding; local jobs run at the admission bindings (parameters.json): {:?}",
                statement.bindings.iter().map(|b| &b.texts).collect::<Vec<_>>()
            ))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Every benchmark binding x worker count cell weighs equally; a missing cell leaves the matrix unranked; one binding
    /// is the geometric mean over the worker counts, as before benchmark bindings.
    #[test]
    fn matrix_score_is_the_geometric_mean_of_the_whole_matrix() {
        let cell = |median: u64| json!({"median_ns":median});
        assert_eq!(matrix_score(&[cell(100), cell(400)], 2), Some(200));
        assert_eq!(matrix_score(&[cell(10), cell(1000), cell(100), cell(100)], 4), Some(100));
        assert_eq!(matrix_score(&[cell(100), cell(400)], 4), None, "two of four cells");
        assert_eq!(matrix_score(&[cell(100), json!({"median_ns":null})], 2), None);
        assert_eq!(matrix_score(&[], 0), None);
    }
}
