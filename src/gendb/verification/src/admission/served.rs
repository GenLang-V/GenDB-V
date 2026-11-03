//! Serving an admitted package again from the library and comparing its answers with the prepared-data reference:
//! the offline harness after admission. Serving itself (`gendb_runtime::serve`) resolves the package by the statement
//! key and the asset by the current source versions and runs the stored library in a worker child; no proof,
//! regeneration, hashing or validation happens on that path.

use super::execution::{CHILD_TIMEOUT_SECONDS, CandidateRunner, RANGE_CAPACITY, TIMED_REPETITIONS, call_answer};
use super::preflight::QueryPreflight;
use super::prepared_reference::BindingReference;
use super::statement::StatementInputs;
use super::AdmissionError;
use gendb_artifacts::ObjectStore;
use gendb_runtime::answer::QueryAnswer;
use gendb_runtime::serve::{WorkerExecutor, serve};
use gendb_storage::io::PartAccess;
use gendb_storage::versions::CurrentCapture;
use gendb_sqlspec::codec::SqlErrorKind;
use serde_json::{Value, json};
use std::path::Path;

/// What the serving path does, for records.
pub const SERVING_PATH: &str = "gendb_runtime::serve resolves the admitted package by the statement key v2 (query entry v4 over stored data: the asset of every storage use for the current capture) or else by the statement key v1 (saved v3 route: the asset by the current source version of every source table), passes the arguments in slot order and executes the stored library in the child worker; no proof, regeneration, hashing or validation on that path (the comparison here is the offline harness)";

/// Serve the admitted package at every admission binding queried on the full data (under the validation policy
/// `formal_proofs` the benchmark bindings only) and every count of `workers` (one call each, evidence under `work`),
/// and compare each answer with that binding's reference, or else its saved answers
/// (`StatementValidation::judge_without_reference`). Returns one record per served cell.
pub fn check_served_bindings(
    store: &ObjectStore,
    runner: &CandidateRunner,
    preflight: &QueryPreflight,
    inputs: &StatementInputs,
    references: &[BindingReference],
    workers: &[usize],
    work: &Path,
) -> Result<Vec<Value>, AdmissionError> {
    let statement = &preflight.statement;
    let current = CurrentCapture::of(&inputs.source).map_err(AdmissionError::tool)?;
    let mut served = vec![];
    for i in preflight.validation.full_data_bindings(statement) {
        let binding = &statement.bindings[i];
        let reference = references.get(i).ok_or_else(|| AdmissionError::tool("reference absent"))?;
        for w in workers {
            let executor = WorkerExecutor::new(&runner.worker, work, CHILD_TIMEOUT_SECONDS, RANGE_CAPACITY, 1);
            let answer = serve(store, &statement.instance, &binding.texts, &current, PartAccess::default(), &executor, *w as u32).map_err(AdmissionError::tool)?;
            let (status, rule) = match (reference, &answer.answer) {
                (Ok(exact), QueryAnswer::Rows(rows)) => {
                    let rule = preflight
                        .window
                        .allowed_output(&exact.rows, rows)
                        .map_err(|d| AdmissionError::execution(format!("served rows at binding {} and {w} workers: {d}", binding.name)))?;
                    ("allowed", rule.to_string())
                }
                (Ok(exact), QueryAnswer::SqlError(e)) if preflight.reference_wraps_integers && SqlErrorKind::from_code(e.code) == Some(SqlErrorKind::NumericValueOutOfRange) => (
                    "status_only",
                    format!("served the exact SQL error {} where DataFusion has {} rows: DataFusion wraps integer overflow (reference not exact here); correctness untested", e.name, exact.rows.len()),
                ),
                (Ok(_), other) => {
                    let what = match other {
                        QueryAnswer::SqlError(e) => format!("SQL error {}", e.name),
                        QueryAnswer::Capacity => "Capacity".into(),
                        QueryAnswer::ParamRefused => "ParamRefused".into(),
                        QueryAnswer::Rows(_) => "rows".into(),
                    };
                    return Err(AdmissionError::execution(format!("served answer at binding {} and {w} workers is {what}, the reference has rows", binding.name)));
                }
                (Err(reason), answer) => {
                    let what = format!("served answer at binding {} and {w} workers", binding.name);
                    preflight.validation.judge_without_reference(&preflight.window, i, answer, &what, &reason.0)?
                }
            };
            let mut record = answer.record().map_err(AdmissionError::tool)?;
            record["binding"] = json!(binding.name);
            record["workers"] = json!(w);
            record["status"] = json!(status);
            record["comparison"] = json!(rule);
            served.push(record);
        }
    }
    Ok(served)
}

/// Why a final same-window cell has no measurement.
#[derive(Debug)]
pub enum FinalCellError {
    /// A served answer is not allowed by the SQL: the admitted package must not be reported (`served_answer_not_allowed`).
    NotAllowed(AdmissionError),
    /// Serving or measuring failed; there is no performance comparison, but nothing wrong was served.
    Failed(AdmissionError),
}

impl std::fmt::Display for FinalCellError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotAllowed(e) => write!(f, "served_answer_not_allowed: {e}"),
            Self::Failed(e) => e.fmt(f),
        }
    }
}

/// One final same-window measurement of the served package at admission binding `binding` (an index of the statement's
/// bindings) with `workers` workers: one warm and three hot calls in one child, every call compared with that
/// binding's exact `reference`, or without one judged by the validation policy (saved answers of other engines;
/// `StatementValidation::judge_without_reference`). The caller holds the host timing lease and measures any baselines
/// in the same window.
#[allow(clippy::too_many_arguments)]
pub fn final_served_cell(
    store: &ObjectStore,
    runner: &CandidateRunner,
    preflight: &QueryPreflight,
    inputs: &StatementInputs,
    binding: usize,
    reference: &BindingReference,
    workers: usize,
    work: &Path,
) -> Result<Value, FinalCellError> {
    let index = binding;
    let binding = preflight.statement.bindings.get(binding).ok_or_else(|| FinalCellError::Failed(AdmissionError::tool("final measurement binding absent")))?;
    let executor = WorkerExecutor::new(&runner.worker, &work.join(format!("final-{}-{workers}", binding.name)), CHILD_TIMEOUT_SECONDS, RANGE_CAPACITY, TIMED_REPETITIONS);
    let current = CurrentCapture::of(&inputs.source).map_err(|e| FinalCellError::Failed(AdmissionError::tool(e)))?;
    let served = serve(store, &preflight.statement.instance, &binding.texts, &current, PartAccess::default(), &executor, workers as u32).map_err(|e| FinalCellError::Failed(AdmissionError::tool(e)))?;
    let calls = executor.calls();
    let mut status = "allowed";
    let mut comparisons = vec![];
    for (i, call) in calls.iter().enumerate() {
        let what = format!("final served call {i} at binding {} and {workers} workers", binding.name);
        match (reference, call_answer(call, &what, work).map_err(FinalCellError::NotAllowed)?) {
            (Ok(exact), QueryAnswer::Rows(rows)) => {
                preflight
                    .window
                    .allowed_output(&exact.rows, &rows)
                    .map_err(|d| FinalCellError::NotAllowed(AdmissionError::execution(format!("{what}: {d}"))))?;
            }
            (Ok(_), other) => return Err(FinalCellError::NotAllowed(AdmissionError::execution(format!("{what} returned {other:?}")))),
            (Err(reason), _) if !preflight.validation.formal => {
                return Err(FinalCellError::NotAllowed(AdmissionError::execution(format!("no exact reference at benchmark binding {}: {reason}", binding.name))));
            }
            (Err(reason), answer) => {
                let (judged, rule) =
                    preflight.validation.judge_without_reference(&preflight.window, index, &answer, &what, &reason.0).map_err(FinalCellError::NotAllowed)?;
                status = judged;
                comparisons.push(rule);
            }
        }
    }
    let samples: Vec<u64> = calls.iter().skip(1).map(|o| o.usage.wall_ns).collect();
    let mut ordered = samples.clone();
    ordered.sort_unstable();
    Ok(json!({"admission":served.admission,"package":served.package,"asset":served.asset,"storage_assets":served.asset_ids(),
        "status":status,"comparisons":comparisons,"warm_ns":calls.first().map(|o| o.usage.wall_ns),"samples_ns":samples,"median_ns":ordered.get(ordered.len() / 2),
        "usage":calls.iter().map(|o| &o.usage).collect::<Vec<_>>(),"boundary":"wall time of one library query call over the admitted asset (hot); process start and decoding excluded"}))
}
