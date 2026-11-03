//! Framework checks of a compiled candidate library, each run in the isolated worker process (ABI v3): build its asset,
//! query the prepared data at admission bindings and worker counts, probe out-of-domain arguments, and run every tiny
//! case. Every answer is compared with exactly the outputs the SQL allows. Tests after the proof, never proof; timings
//! are descriptive. The comparisons and records are shared with the checks over stored data (`stored_execution`).

use super::cases::{inline_columns, label_record};
use super::comparison::rows_text;
use super::preflight::QueryPreflight;
use super::prepared_reference::BindingReference;
use super::statement::StatementInputs;
use super::validation::StatementValidation;
use super::{AdmissionError, FailureClass};
use gendb_frontend::columns::SourceType;
use gendb_runtime::abi::{CallOutcome, CallStatus, StatementArgument};
use gendb_runtime::answer::QueryAnswer;
use gendb_runtime::worker::{CallObservation, TableColumns, WorkerError, WorkerInput, WorkerRequest, WorkerResult, spawn};
use gendb_sqlspec::codec::{RunOutcome, SqlErrorKind};
use serde_json::{Value, json};
use std::path::{Path, PathBuf};

/// Framework safety bound of one child job, in seconds. A verified entry terminates, so reaching it is a
/// `tool_failure`, never a result.
pub const CHILD_TIMEOUT_SECONDS: u64 = 3600;
/// Leading text of the error of a child that refused a write at the storage free-space reserve.
pub(super) const RESERVE_STOP: &str = "insufficient_storage: the child stopped writing at the free-space reserve (no candidate is implicated)";
/// Timed calls per binding and worker count of evaluations and trials: one warm call, then three hot calls.
pub const TIMED_REPETITIONS: u32 = 4;
/// Calls per binding and worker count of a profile job: one warm call and one measured call.
pub const PROFILE_REPETITIONS: u32 = 2;
/// Dispatch ranges recorded per call.
pub const RANGE_CAPACITY: u64 = 64;

/// Runs candidate libraries in worker children: `worker` is the executable run as `<worker> worker REQUEST RESULT`.
#[derive(Clone, Debug)]
pub struct CandidateRunner {
    pub worker: PathBuf,
}

/// The stored parts of a candidate's representation built over some source columns.
#[derive(Clone, Debug)]
pub struct BuiltAsset {
    pub parts: PathBuf,
    /// The build job's result: parts manifest, column rows, the builder call.
    pub result: WorkerResult,
}

impl CandidateRunner {
    /// Run one request in a fresh child under `work`. `bound`: an author-requested diagnostic bound in seconds (local
    /// trial/profile only), clamped to the framework bound; reaching it is a censored `execution_failure`.
    pub fn run(&self, work: &Path, request: &WorkerRequest, bound: Option<u64>) -> Result<WorkerResult, AdmissionError> {
        let seconds = bound.unwrap_or(CHILD_TIMEOUT_SECONDS).clamp(1, CHILD_TIMEOUT_SECONDS);
        match spawn(&self.worker, work, request, seconds) {
            Ok(result) => Ok(result),
            Err(WorkerError::ChildFailed(failure)) if failure.timed_out() && bound.is_some() => Err(AdmissionError::execution(format!(
                "censored: the child did not finish within the requested timeout_seconds={seconds} (no result, no timing); evidence {}",
                work.display()
            ))),
            Err(WorkerError::ChildFailed(failure)) if failure.timed_out() => {
                Err(AdmissionError::tool(format!("child worker timed out or was killed ({failure:?}); evidence {}", work.display())))
            }
            Err(WorkerError::ChildFailed(failure)) if failure.stopped_at_storage_reserve() => {
                Err(AdmissionError::tool(format!("{RESERVE_STOP}: {}; evidence {}", failure.stderr.trim(), work.display())))
            }
            Err(WorkerError::ChildFailed(failure)) => Err(AdmissionError::execution(format!(
                "child worker ended without a status (exit {:?}, signal {:?}; the calling thread unwound or aborted, outside the calling_thread_progress assumption): {}; evidence {}",
                failure.exit_code,
                failure.signal,
                failure.stderr.trim(),
                work.display()
            ))),
            Err(other) => Err(AdmissionError::tool(other)),
        }
    }

    /// Run the candidate's builder once over `input` with `workers` workers and store its parts in `<work>/parts`
    /// (evidence in `<work>/build`).
    pub fn build_asset(&self, library: &Path, input: WorkerInput, work: &Path, workers: u32, bound: Option<u64>) -> Result<BuiltAsset, AdmissionError> {
        let parts = work.join("parts");
        let evidence = work.join("build");
        let result = self.run(&evidence, &WorkerRequest::for_build(library, input, &parts, workers, RANGE_CAPACITY), bound)?;
        let status = result.observations.first().map(|o| o.outcome.status);
        if status == Some(CallStatus::InvalidInput) {
            // The fixed entry decides in_domain with its verified source_in_domain BEFORE the author's builder runs.
            return Err(AdmissionError::tool(format!(
                "the input columns are outside the declared column domain (the fixed entry's verified source_in_domain refused them before the builder ran; the candidate is not implicated); column rows {:?}; evidence {}",
                result.column_rows,
                evidence.display()
            )));
        }
        if status != Some(CallStatus::Ok) || result.parts.is_none() {
            return Err(status_error(status, &format!("builder (column rows {:?})", result.column_rows), &evidence));
        }
        Ok(BuiltAsset { parts, result })
    }
}

/// The prepared data of every delivered source table, in declaration order (a self-joined table once).
pub fn prepared_input(preflight: &QueryPreflight, inputs: &StatementInputs) -> WorkerInput {
    WorkerInput::Tables {
        path: inputs.archive.clone(),
        tables: preflight
            .statement
            .source
            .tables
            .iter()
            .map(|t| TableColumns { table: t.name.clone(), ordinals: t.columns.iter().map(|c| c.ordinal).collect() })
            .collect(),
    }
}

/// Status of a child call that is not a result: `WorkerFailed` is a trusted-runtime failure (every worker body is
/// Verus-checked `no_unwind`), anything else a wrong execution.
pub fn status_error(status: Option<CallStatus>, what: &str, evidence: &Path) -> AdmissionError {
    let class = if status == Some(CallStatus::WorkerFailed) { FailureClass::ToolFailure } else { FailureClass::ExecutionFailure };
    AdmissionError::new(class, format!("{what} returned status {status:?}; never a result; evidence {}", evidence.display()))
}

/// The answer of one query call: rows, the exact SQL error or Capacity; any other status is an error.
pub fn call_answer(outcome: &CallOutcome, what: &str, evidence: &Path) -> Result<QueryAnswer, AdmissionError> {
    match outcome.status {
        CallStatus::Ok | CallStatus::Capacity | CallStatus::SqlError => QueryAnswer::of(outcome).map_err(|e| AdmissionError::execution(format!("{what}: {e}"))),
        status => Err(status_error(Some(status), what, evidence)),
    }
}

fn answer_name(answer: &QueryAnswer) -> String {
    match answer {
        QueryAnswer::Rows(r) => format!("{} rows", r.len()),
        QueryAnswer::SqlError(e) => format!("SqlError {}", e.name),
        QueryAnswer::Capacity => "Capacity".into(),
        QueryAnswer::ParamRefused => "ParamRefused".into(),
    }
}

fn is_numeric_out_of_range(answer: &QueryAnswer) -> bool {
    matches!(answer, QueryAnswer::SqlError(e) if SqlErrorKind::from_code(e.code) == Some(SqlErrorKind::NumericValueOutOfRange))
}

/// Descriptive sizes of a built asset: canonical fixed-width bytes of the delivered columns and the stored bytes.
pub fn asset_bytes(preflight: &QueryPreflight, result: &WorkerResult) -> Value {
    let width = |ty: SourceType| -> u64 {
        match ty {
            SourceType::Int32 | SourceType::Date32 => 4,
            SourceType::Int64 | SourceType::Utf8 => 8,
            SourceType::Decimal { .. } => 16,
        }
    };
    let mut column = 0;
    let mut tables = vec![];
    let mut total = 0u64;
    for t in &preflight.statement.source.tables {
        let rows = result.column_rows.get(column).copied().unwrap_or(0);
        let fixed: u64 = t.columns.iter().map(|c| width(c.ty)).sum::<u64>() * rows;
        column += t.columns.len();
        total += fixed;
        tables.push(json!({"table":t.name,"rows":rows,"canonical_fixed_width_bytes":fixed}));
    }
    json!({"tables":tables,"canonical_fixed_width_bytes":total,"text_bytes":"Utf8 fields also carry their value bytes (not counted above)",
        "built_asset_bytes":result.parts.as_ref().map(|p| p.storage_bytes),"parts":result.parts.as_ref().map(|p| &p.parts),"scope":"descriptive; not an acceptance threshold"})
}

/// Query the stored `parts` at the admission `bindings` (indices) and every worker count of `workers`,
/// `repetitions` calls each, and compare every answer with that binding's prepared-data reference. At least one
/// compared cell must have an exact reference.
#[allow(clippy::too_many_arguments)]
pub fn check_prepared_data(
    runner: &CandidateRunner,
    preflight: &QueryPreflight,
    references: &[BindingReference],
    library: &Path,
    parts: &Path,
    work: &Path,
    bindings: &[usize],
    workers: &[usize],
    repetitions: u32,
    bound: Option<u64>,
) -> Result<Value, AdmissionError> {
    let request =
        WorkerRequest::for_query(library, Some(parts), binding_arguments(preflight, bindings), worker_counts(workers), repetitions, RANGE_CAPACITY);
    let result = runner.run(work, &request, bound)?;
    let cells = compare_prepared_data(preflight, references, &result, bindings, workers, work)?;
    prepared_data_record(preflight, cells.into_iter().map(|cell| cell.record).collect(), work)
}

/// The argument lists of the admission bindings `bindings` (indices of the statement's bindings), in that order.
pub(super) fn binding_arguments(preflight: &QueryPreflight, bindings: &[usize]) -> Vec<Vec<StatementArgument>> {
    bindings.iter().map(|b| preflight.statement.bindings[*b].abi.clone()).collect()
}

pub(super) fn worker_counts(workers: &[usize]) -> Vec<u32> {
    workers.iter().map(|w| *w as u32).collect()
}

/// One binding and worker count of a prepared-data query job: its record and its calls (1 warm, then hot).
pub(super) struct PreparedCell<'r> {
    pub record: Value,
    pub calls: Vec<&'r CallObservation>,
}

/// Compare every call of the query job `result` (argument list `i` = admission binding `bindings[i]`, at each count of
/// `workers`) with that binding's prepared-data reference: the allowed-output rule where the reference is exact, the
/// status only where it is not (no reference, or an integer overflow DataFusion wraps). A call whose answer the child
/// stored bounded (`CallObservation::stored_answer`, a job that compares nothing) is judged by its summary
/// ([`stored_answer_verdict`]); the cell's record then lists every call's `stored_answers`.
pub(super) fn compare_prepared_data<'r>(
    preflight: &QueryPreflight,
    references: &[BindingReference],
    result: &'r WorkerResult,
    bindings: &[usize],
    workers: &[usize],
    work: &Path,
) -> Result<Vec<PreparedCell<'r>>, AdmissionError> {
    let statement = &preflight.statement;
    let mut cells = vec![];
    for (request_index, b) in bindings.iter().enumerate() {
        let binding = &statement.bindings[*b];
        let reference = references.get(*b).ok_or_else(|| AdmissionError::tool("prepared reference absent"))?;
        for w in workers {
            let calls: Vec<&CallObservation> = result.observations.iter().filter(|o| o.workers as usize == *w && o.binding == Some(request_index)).collect();
            if calls.is_empty() {
                return Err(AdmissionError::tool(format!("no observation for binding {} at {w} workers; evidence {}", binding.name, work.display())));
            }
            let mut rule = String::new();
            let mut status = "exact";
            for call in &calls {
                let what = format!("query on the prepared data at binding {} ({:?}) and {w} workers", binding.name, binding.texts);
                if let Some(stored) = &call.stored_answer {
                    (status, rule) = stored_answer_verdict(&preflight.validation, reference, *b, call.outcome.status, &stored.describe(), &what, work)?;
                    continue;
                }
                let got = call_answer(&call.outcome, &what, work)?;
                match (reference, &got) {
                    (Ok(exact), QueryAnswer::Rows(rows)) => {
                        rule = preflight
                            .window
                            .allowed_output(&exact.rows, rows)
                            .map_err(|d| {
                                AdmissionError::execution(format!(
                                    "{what}: {d}; expected {} got {}; evidence {}",
                                    json!(rows_text(&exact.rows[..exact.rows.len().min(20)])),
                                    json!(rows_text(&rows[..rows.len().min(20)])),
                                    work.display()
                                ))
                            })?
                            .to_string();
                    }
                    (Ok(exact), QueryAnswer::Capacity) => {
                        return Err(AdmissionError::execution(format!(
                            "{what} returned Capacity, but the independent reference has {} exact rows here; a Capacity answer is allowed by the claim only outside the capacity domain, which this test cannot confirm, so the package would not answer this data; not qualified; evidence {}",
                            exact.rows.len(),
                            work.display()
                        )));
                    }
                    (Ok(exact), QueryAnswer::SqlError(e)) if preflight.reference_wraps_integers && is_numeric_out_of_range(&got) => {
                        status = "status_only";
                        rule = format!(
                            "the candidate returned the exact SQL error {} and DataFusion {} rows: the statement has integer arithmetic, which DataFusion wraps on overflow (PostgreSQL/VERUS_SQL raise 22003), so the reference is not exact here; result correctness untested at this binding",
                            e.name,
                            exact.rows.len()
                        );
                    }
                    (Ok(exact), QueryAnswer::SqlError(e)) => {
                        return Err(AdmissionError::execution(format!(
                            "{what} returned SqlError {}, but the independent reference has {} rows; evidence {}",
                            e.name,
                            exact.rows.len(),
                            work.display()
                        )));
                    }
                    (Err(reason), got) => {
                        let (judged, text) = preflight.validation.judge_without_reference(&preflight.window, *b, got, &what, &reason.0).map_err(|mut e| {
                            e.message = format!("{}; evidence {}", e.message, work.display());
                            e
                        })?;
                        status = judged;
                        rule = text;
                    }
                    (_, other) => return Err(AdmissionError::execution(format!("{what}: unexpected outcome {other:?}"))),
                }
            }
            let hot: Vec<u64> = calls.iter().skip(1).map(|o| o.outcome.usage.wall_ns).collect();
            let mut ordered = hot.clone();
            ordered.sort_unstable();
            let last = &calls.last().expect("at least one call").outcome;
            let mut record = json!({"binding":binding.name,"arguments":binding.texts,"workers":w,"status":status,"comparison":rule,
                "reference_rows":reference.as_ref().ok().map(|r| r.rows.len()),"calls":calls.len(),
                "warm_wall_ns":calls.first().map(|o| o.outcome.usage.wall_ns),"hot_wall_ns":hot,"median_hot_wall_ns":ordered.get(ordered.len() / 2),
                "dispatch":{"spawned":last.dispatch.spawned,"joined":last.dispatch.joined,"ranges":last.dispatch.ranges,"ranges_reported":last.dispatch.ranges_reported},
                "usage":calls.iter().map(|o| &o.outcome.usage).collect::<Vec<_>>(),
                "calling_thread_share_permille":(last.usage.wall_ns > 0).then(|| (last.usage.caller_cpu_ns as u128 * 1000 / last.usage.wall_ns as u128) as u64),
                "parallel_dispatch_observed":last.dispatch.spawned > 1 && last.dispatch.joined == last.dispatch.spawned});
            if calls.iter().any(|o| o.stored_answer.is_some()) {
                record["stored_answers"] = json!(calls.iter().map(|o| &o.stored_answer).collect::<Vec<_>>());
            }
            cells.push(PreparedCell { record, calls });
        }
    }
    Ok(cells)
}

/// The verdict of a call (status `status`) whose rows answer the child stored bounded (`returned`: its description) at
/// admission binding `binding`: only where nothing is compared (no exact reference, no saved answer; `not_compared`
/// under `formal_proofs`, else `status_only`, with the words of an answer stored in full). An exact reference or saved
/// answers there are a tool failure (a compared cell stores its answers in full), and so is a stored answer of a call
/// whose status is not `Ok` (the child checked the call's status, code and wire before storing it).
fn stored_answer_verdict(
    validation: &StatementValidation,
    reference: &BindingReference,
    binding: usize,
    status: CallStatus,
    returned: &str,
    what: &str,
    work: &Path,
) -> Result<(&'static str, String), AdmissionError> {
    let with_evidence = |mut error: AdmissionError| {
        error.message = format!("{}; evidence {}", error.message, work.display());
        error
    };
    if status != CallStatus::Ok {
        return Err(with_evidence(AdmissionError::tool(format!("{what}: a stored rows answer on a call with status {status:?}"))));
    }
    match reference {
        Ok(_) => Err(with_evidence(AdmissionError::tool(format!(
            "{what}: the answer was stored bounded ({returned}), but this binding has an exact reference: a compared cell stores its answers in full"
        )))),
        Err(reason) => validation.judge_stored(binding, returned, what, &reason.0).map_err(with_evidence),
    }
}

/// The prepared-data record of compared `cells`; `no_independent_reference` when no cell had an exact reference, except
/// under the validation policy `formal_proofs`, where no reference is computed: the proof is the claim, and cells
/// with saved answers of other engines record their agreement.
pub(super) fn prepared_data_record(preflight: &QueryPreflight, cells: Vec<Value>, work: &Path) -> Result<Value, AdmissionError> {
    let exact_cells = cells.iter().filter(|c| c["status"] == "exact").count();
    if preflight.validation.formal {
        let count = |status: &str| cells.iter().filter(|c| c["status"] == status).count();
        let (all, partly) = (count("saved_answers_agree"), count("saved_answers_agree_partly"));
        let status = match (all + partly, cells.len()) {
            (0, _) => "not_compared",
            (agreeing, total) if agreeing < total => "saved_answers_agree_where_given",
            _ if partly > 0 => "saved_answers_agree_partly",
            _ => "saved_answers_agree",
        };
        return Ok(json!({"status":status,
            "validation":preflight.validation.record(),"cells":cells,"evidence":work,
            "timing":"descriptive only: child wall time per call (1 warm, then hot calls); not a performance claim"}));
    }
    if exact_cells == 0 {
        return Err(AdmissionError::unsupported(format!(
            "no_independent_reference: no admission binding has an exact prepared-data reference; evidence {}",
            work.display()
        )));
    }
    Ok(json!({"status":if exact_cells == cells.len() { "exact" } else { "exact_where_referenced" },"cells":cells,"evidence":work,
        "timing":"descriptive only: child wall time per call (1 warm, then hot calls); not a performance claim"}))
}

/// The verified entry refuses every value just outside the declared domain (`ParamRefused`, before any author code):
/// a check of the host/ABI wiring of the checked decision.
pub fn check_parameter_refusals(runner: &CandidateRunner, preflight: &QueryPreflight, library: &Path, parts: &Path, work: &Path) -> Result<Value, AdmissionError> {
    check_refusal_probes(runner, preflight, work, |probes| WorkerRequest::for_query(library, Some(parts), probes, vec![1], 1, RANGE_CAPACITY))
}

/// Run the statement's out-of-domain probes with the query job `request(probe argument lists)` (one worker, one call
/// each) and require `ParamRefused` for every probe.
pub(super) fn check_refusal_probes(
    runner: &CandidateRunner,
    preflight: &QueryPreflight,
    work: &Path,
    request: impl FnOnce(Vec<Vec<StatementArgument>>) -> WorkerRequest,
) -> Result<Value, AdmissionError> {
    let probes = &preflight.statement.refusal_probes;
    if probes.is_empty() {
        return Ok(json!({"status":"not_applicable","reason":"no free parameter bound is inside its type's range"}));
    }
    let result = runner.run(work, &request(probes.iter().map(|b| b.abi.clone()).collect()), None)?;
    let mut out = vec![];
    for (i, probe) in probes.iter().enumerate() {
        let status = result.observations.iter().find(|o| o.binding == Some(i)).map(|o| o.outcome.status);
        if status != Some(CallStatus::ParamRefused) {
            return Err(AdmissionError::tool(format!(
                "the verified entry did not refuse the out-of-domain binding {} ({:?}): status {status:?}; evidence {}",
                probe.name,
                probe.texts,
                work.display()
            )));
        }
        out.push(json!({"binding":probe.name,"arguments":probe.texts,"status":"param_refused"}));
    }
    Ok(json!({"status":"refused_as_declared","probes":out,"evidence":work}))
}

/// Every tiny case: builder -> stored parts -> query at every admission binding and every count of `workers`, compared
/// with the verified evaluator's label of that binding.
pub fn check_tiny_cases(runner: &CandidateRunner, preflight: &QueryPreflight, library: &Path, work: &Path, workers: &[usize]) -> Result<Value, AdmissionError> {
    if preflight.validation.formal {
        return Ok(super::stored_execution::tiny_cases_not_run(preflight));
    }
    let statement = &preflight.statement;
    let build_workers = *workers.iter().max().ok_or_else(|| AdmissionError::tool("workers absent"))? as u32;
    let all_bindings: Vec<usize> = (0..statement.bindings.len()).collect();
    let mut judged = CaseJudgements::default();
    for (index, case) in preflight.cases.iter().enumerate() {
        let dir = case_directory(work, &case.name);
        let input = WorkerInput::Inline { columns: inline_columns(&statement.source, &preflight.databases[index])? };
        let asset = runner.build_asset(library, input, &dir, build_workers, None).map_err(|mut e| {
            e.message = format!("{} (case {})", e.message, case.name);
            e
        })?;
        let request = WorkerRequest::for_query(library, Some(&asset.parts), binding_arguments(preflight, &all_bindings), worker_counts(workers), 1, RANGE_CAPACITY);
        let query = runner.run(&dir.join("query"), &request, None)?;
        let verdicts = judged.judge(preflight, index, &all_bindings, &query, &dir)?;
        judged.cases.push(case_record(preflight, index, verdicts));
    }
    Ok(judged.record(preflight, work))
}

/// The evidence directory of one tiny case under `work`.
pub(super) fn case_directory(work: &Path, case_name: &str) -> PathBuf {
    work.join(case_name.replace('/', "__"))
}

/// The judged tiny cases of one check.
#[derive(Default)]
pub(super) struct CaseJudgements {
    pub cases: Vec<Value>,
    compared: usize,
    status_only: usize,
}

impl CaseJudgements {
    /// Judge every call of the query job `query` of tiny case `case` (argument list `i` = admission binding
    /// `bindings[i]`) against that binding's evaluator label; one verdict record per observation, in observation order.
    pub(super) fn judge(&mut self, preflight: &QueryPreflight, case: usize, bindings: &[usize], query: &WorkerResult, dir: &Path) -> Result<Vec<Value>, AdmissionError> {
        let statement = &preflight.statement;
        let (tiny, labels) = (&preflight.cases[case], &preflight.labels[case]);
        let mut verdicts = vec![];
        for observation in &query.observations {
            let b = observation.binding.and_then(|i| bindings.get(i).copied()).ok_or_else(|| AdmissionError::tool("observation without an admission binding"))?;
            let what = format!("case {} (rows {:?}) at binding {} and {} workers", tiny.name, tiny.rows(), statement.bindings[b].name, observation.workers);
            let got = call_answer(&observation.outcome, &what, dir)?;
            let verdict = case_verdict(preflight, &labels[b], &got).map_err(|mut e| {
                e.message = format!("{what}: {}; evidence {}", e.message, dir.display());
                e
            })?;
            match verdict {
                Verdict::Compared(_) => self.compared += 1,
                Verdict::StatusOnly(_) => self.status_only += 1,
            }
            verdicts.push(json!({"binding":statement.bindings[b].name,"workers":observation.workers,"verdict":verdict.text(),
                "spawned":observation.outcome.dispatch.spawned,"joined":observation.outcome.dispatch.joined}));
        }
        Ok(verdicts)
    }

    /// The tiny-case record of the whole check.
    pub(super) fn record(self, preflight: &QueryPreflight, work: &Path) -> Value {
        let mut record = json!({"status":"allowed","reference":"verified VERUS_SQL evaluator of each admission binding's fully fixed instance (LIMIT/OFFSET cleared; the comparison applies them tie-aware) over generated source tables (tests, not proof)",
            "exact_comparisons":self.compared,"status_only_observations":self.status_only,
            "status_only_meaning":"inputs outside the capacity domain (or without an evaluator label): the outcome is recorded, its correctness is not tested",
            "generation":preflight.case_generation,"cases":self.cases,"evidence":work});
        if preflight.constraints_assumed {
            // Only certified cases are run; the skipped ones and their reasons are in the preflight's record.
            let c = &preflight.case_certification;
            record["certification"] = json!({"generated":c["generated"],"certified":c["certified"],"certified_with_rows":c["certified_with_rows"],
                "skipped":c["skipped_by_reason"],"warnings":c["warnings"]});
        }
        record
    }
}

/// The record of tiny case `case` with its verdicts.
pub(super) fn case_record(preflight: &QueryPreflight, case: usize, verdicts: Vec<Value>) -> Value {
    let tiny = &preflight.cases[case];
    let labels: Vec<Value> = preflight.labels[case].iter().map(label_record).collect();
    json!({"case":tiny.name,"rows":tiny.rows(),"labels":labels,"verdicts":verdicts})
}

/// A candidate answer judged against an evaluator label.
enum Verdict {
    /// Compared exactly; the rule that allowed it.
    Compared(String),
    /// Outside what the label can judge; recorded, correctness untested.
    StatusOnly(String),
}

impl Verdict {
    fn text(&self) -> &str {
        match self {
            Self::Compared(rule) | Self::StatusOnly(rule) => rule,
        }
    }
}

/// Judge a candidate answer against the verified evaluator's label. `Err`: an answer the SQL does not allow
/// (`execution_failure`), or a label that is not a case label (`tool_failure`).
fn case_verdict(preflight: &QueryPreflight, label: &RunOutcome, got: &QueryAnswer) -> Result<Verdict, AdmissionError> {
    match (label, got) {
        (RunOutcome::Rows(full), QueryAnswer::Rows(rows)) => preflight
            .window
            .allowed_output(full, rows)
            .map(|rule| Verdict::Compared(rule.into()))
            .map_err(|d| AdmissionError::execution(format!("{d}; evaluator {} candidate {}", json!(rows_text(full)), json!(rows_text(rows))))),
        (RunOutcome::Rows(_), other) => Err(AdmissionError::execution(format!(
            "the verified evaluator shows the input inside the capacity domain with a value, but the candidate returned {}",
            answer_name(other)
        ))),
        (RunOutcome::SqlError(kind), QueryAnswer::SqlError(e)) if SqlErrorKind::from_code(e.code) == Some(*kind) => {
            Ok(Verdict::Compared(format!("exact SQL error {} (the meaning's error)", kind.name())))
        }
        (RunOutcome::SqlError(kind), other) => Err(AdmissionError::execution(format!(
            "the meaning is exactly the SQL error {} (inside the capacity domain), but the candidate returned {}",
            kind.name(),
            answer_name(other)
        ))),
        // A run case of a statement with declared constraints is certified at some binding, so Capacity is the
        // evaluator's proof of !capacity_domain here as well.
        (RunOutcome::Capacity, other) => Ok(Verdict::StatusOnly(format!(
            "status_only: outside the capacity domain (proved by the verified evaluator); the candidate returned {}; no exact reference, result correctness untested",
            answer_name(other)
        ))),
        (other, _) => Err(AdmissionError::tool(format!("evaluator label {other:?} is not a case label"))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::admission::prepared_reference::{ExactReference, NoReference};
    use crate::admission::validation::SavedAnswer;
    use gendb_runtime::worker::{AnswerBound, StoredAnswer};

    /// A bounded answer of an author's own statement is judged by its summary alone, and the verdict says what was
    /// stored and that the rest was not; where something is compared (saved answers or an exact reference) a bounded
    /// answer is a tool failure, because a compared cell stores its answers in full; so is one on a call that is not Ok.
    #[test]
    fn a_bounded_answer_is_judged_by_its_summary_only_where_nothing_is_compared() {
        let stored = StoredAnswer { rows: 11_829_402, stored_rows: 100, wire_bytes: 512_000_000, wire_sha256: "ab".repeat(32), bound: AnswerBound::STORED };
        let returned = stored.describe();
        let work = Path::new("/w/cells/sql-2/w32");
        let no_reference: BindingReference = Err(NoReference("not computed".into()));
        let formal = StatementValidation { formal: true, answers: vec![vec![]], tolerance: 0.0, required_engines: vec![] };
        let (status, text) = stored_answer_verdict(&formal, &no_reference, 0, CallStatus::Ok, &returned, "sql-2", work).unwrap();
        assert_eq!(status, "not_compared");
        assert_eq!(
            text,
            format!(
                "not computed; no saved answer at this binding; the candidate returned 11829402 rows; stored: the first 100 rows (at most 100 rows and 1048576 bytes of row text), the rest not stored; SHA-256 of the result wire {} (512000000 bytes)",
                "ab".repeat(32)
            )
        );
        let (status, _) = stored_answer_verdict(&StatementValidation::default(), &no_reference, 0, CallStatus::Ok, &returned, "sql-2", work).unwrap();
        assert_eq!(status, "status_only");
        let saved = SavedAnswer { engine: "duckdb".into(), description: "d".into(), path: "/saved.json".into(), rows: vec![] };
        let with_saved = StatementValidation { answers: vec![vec![saved]], ..formal.clone() };
        let refused = stored_answer_verdict(&with_saved, &no_reference, 0, CallStatus::Ok, &returned, "Q18 at v0", work).unwrap_err();
        assert_eq!(refused.class, FailureClass::ToolFailure);
        assert!(refused.message.contains("a compared cell stores its answers in full") && refused.message.ends_with("evidence /w/cells/sql-2/w32"), "{}", refused.message);
        let exact: BindingReference = Ok(ExactReference { rows: vec![], record: Value::Null });
        assert_eq!(stored_answer_verdict(&StatementValidation::default(), &exact, 0, CallStatus::Ok, &returned, "q", work).unwrap_err().class, FailureClass::ToolFailure);
        assert_eq!(stored_answer_verdict(&formal, &no_reference, 0, CallStatus::Capacity, &returned, "q", work).unwrap_err().class, FailureClass::ToolFailure);
    }
}
