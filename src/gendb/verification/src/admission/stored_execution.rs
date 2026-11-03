//! Framework checks of a compiled query library over stored data (query entry v4) and of a compiled storage library,
//! each run in the isolated worker process (ABI v4): query the prepared assets of the storage uses at admission
//! bindings and worker counts, probe out-of-domain arguments, and run tiny cases whose storage inputs each storage's
//! checked builder turns into tiny assets. Tests after the proof, never proof, as in [`super::execution`], whose
//! comparisons, error classes and records these checks share (Capacity against an exact reference is an execution
//! failure, a DataFusion integer wrap is status-only, `no_independent_reference` when no binding has an exact
//! reference).
//!
//! Added per prepared-data cell: the request counters of every storage use (the verified counts of extent requests,
//! not accesses, unique bytes or device reads) and the child's `read_bytes` (environment-dependent device reads;
//! page-cache hits count 0). Both are descriptive.
//!
//! Tiny assets: the storage input of a case ([`storage_case_input`]) is the case's complete database (the one the
//! verified evaluator labelled) projected onto the stored columns; stored columns the statement does not deliver and
//! stored tables it does not read hold that database's completion (defaults and no rows without declared integrity
//! constraints). Those are test fixtures: every case record names them. A builder that assumes the declared constraints
//! (storage entry v2) runs only on the certified complete databases of a statement whose preflight assumed them.

use super::cases::{StorageCaseInput, storage_case_input};
use super::execution::{
    CandidateRunner, CaseJudgements, RANGE_CAPACITY, binding_arguments, case_directory, case_record, check_refusal_probes, compare_prepared_data,
    prepared_data_record, status_error, worker_counts,
};
use super::preflight::QueryPreflight;
use super::prepared_reference::BindingReference;
use super::AdmissionError;
use crate::obligations::{DeclaredSource, StorageName};
use gendb_runtime::abi::{CallOutcome, CallStatus};
use gendb_runtime::worker::{CallObservation, StorageUseInput, WorkerInput, WorkerRequest, WorkerResult};
use gendb_storage::io::PartAccess;
use serde_json::{Value, json};
use std::path::{Path, PathBuf};

/// One storage use of a query candidate in a test run, in the query's declared use order.
#[derive(Clone, Copy, Debug)]
pub struct StorageUseRun<'a> {
    pub name: &'a StorageName,
    /// The storage's declaration (`DeclaredSource::for_storage` of the storage package or candidate).
    pub declaration: &'a DeclaredSource,
    /// How the storage's tiny-case assets are built (its checked library, from columns or from its sources' tiny assets).
    pub builder: &'a TinyBuilder,
    /// Parts directory of this storage's asset over the current prepared data.
    pub prepared_parts: &'a Path,
    /// Stored bytes of that asset (its manifest's `storage_bytes`); the query job's mapping must agree.
    pub stored_bytes: u64,
    /// Whether the storage's builder assumes the run's declared integrity constraints (storage entry v2): it is run
    /// only on certified case databases ([`refuse_uncertified_tiny_builds`]).
    pub assumes_declared_constraints: bool,
}

/// How a storage's tiny-case assets are built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TinyBuilder {
    /// Its checked library builds them from the case's columns (storage entries v1/v2).
    Columns { library: PathBuf },
    /// Built from admitted storages (derived entry): every source's tiny asset of the same case first (recursively),
    /// then its checked library over them, the extended source's parts linked first.
    Derived { library: PathBuf, sources: Vec<TinySource>, extends: Option<usize> },
}

/// One source of a derived storage's tiny builds.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TinySource {
    pub name: String,
    pub declaration: DeclaredSource,
    pub builder: TinyBuilder,
    pub assumes_declared_constraints: bool,
}

impl TinyBuilder {
    /// Whether this builder or any source's assumes the declared integrity constraints (`own`: this storage's opt-in).
    fn assumes_constraints(&self, own: bool) -> bool {
        own || match self {
            TinyBuilder::Columns { .. } => false,
            TinyBuilder::Derived { sources, .. } => sources.iter().any(|s| s.builder.assumes_constraints(s.assumes_declared_constraints)),
        }
    }

    /// Build the tiny asset of case `case` of `preflight` for a storage of `declaration` under `dir` (`<dir>/parts`):
    /// the parts directory and the record of its input.
    fn build(&self, runner: &CandidateRunner, preflight: &QueryPreflight, declaration: &DeclaredSource, case: usize, dir: &Path, workers: u32) -> Result<(PathBuf, Value), AdmissionError> {
        match self {
            TinyBuilder::Columns { library } => {
                let input = tiny_input(preflight, declaration, case)?;
                let (parts, built) = build_tiny_asset(runner, library, &input, dir, workers)?;
                Ok((parts, json!({"input":input.record(),"parts":built.parts})))
            }
            TinyBuilder::Derived { library, sources, extends } => {
                let mut uses = vec![];
                let mut inputs = vec![];
                for (k, source) in sources.iter().enumerate() {
                    let (parts, record) = source.builder.build(runner, preflight, &source.declaration, case, &dir.join(format!("source-{k}-{}", source.name)), workers)?;
                    uses.push(StorageUseInput { name: source.name.clone(), parts_directory: parts });
                    inputs.push(json!({"source":source.name,"build":record}));
                }
                let (parts, evidence) = (dir.join("parts"), dir.join("build"));
                let request = WorkerRequest::for_storage_build(library, WorkerInput::StoredParts { uses, extends: *extends }, &parts, workers, RANGE_CAPACITY);
                let result = runner.run(&evidence, &request, None)?;
                let status = result.observations.first().map(|o| o.outcome.status);
                if status != Some(CallStatus::Ok) || result.parts.is_none() {
                    return Err(status_error(status, "derived storage builder on a tiny case", &evidence));
                }
                Ok((parts, json!({"derived_from":inputs,"parts":result.parts})))
            }
        }
    }
}

/// Why a storage builder that assumes the declared integrity constraints is not run on a statement's tiny cases:
/// outside its precondition (`source_witnessed`) verified code guarantees nothing, and only the complete case databases
/// of a statement whose preflight assumed the declarations are certified by the verified evaluator (the others are
/// never certified, so no checked case database witnesses the declarations).
pub const UNCERTIFIED_TINY_BUILDS: &str = "tiny_cases_uncertified: the storage builder assumes the declared integrity constraints and is run only on \
     complete case databases the verified evaluator certified to satisfy them; this statement's preflight assumed no declared constraints, so its cases are not certified";

/// Refuse tiny-case builds by a builder that assumes declared constraints ([`UNCERTIFIED_TINY_BUILDS`], `builder`
/// naming it) over a statement whose cases are not certified, before any input is written or any library is run.
/// Every case a constrained preflight keeps is certified ([`super::cases::certification`]).
fn refuse_uncertified_tiny_builds(builder: &str, assumes_declared_constraints: bool, preflight: &QueryPreflight) -> Result<(), AdmissionError> {
    certified_for(builder, assumes_declared_constraints, preflight.constraints_assumed, &preflight.statement.key_v4_id)
}

/// [`refuse_uncertified_tiny_builds`] on the facts it reads: whether the builder assumes the declarations and whether
/// the statement's preflight certified its cases under them.
fn certified_for(builder: &str, assumes_declared_constraints: bool, constraints_assumed: bool, statement: &str) -> Result<(), AdmissionError> {
    if assumes_declared_constraints && !constraints_assumed {
        return Err(AdmissionError::refusal(format!("{UNCERTIFIED_TINY_BUILDS} ({builder}; statement {statement})")));
    }
    Ok(())
}

/// Which tiny cases a check runs: indices into `preflight.cases`, admission binding indices and worker counts. An
/// evaluation runs [`TinyCaseSelection::every`] case; a diagnostic job may choose fewer.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TinyCaseSelection {
    pub cases: Vec<usize>,
    pub bindings: Vec<usize>,
    pub workers: Vec<usize>,
}

impl TinyCaseSelection {
    /// Every tiny case at every admission binding and each count of `workers`.
    pub fn every(preflight: &QueryPreflight, workers: &[usize]) -> Self {
        Self { cases: (0..preflight.cases.len()).collect(), bindings: (0..preflight.statement.bindings.len()).collect(), workers: workers.to_vec() }
    }
}

/// Query `library` over the uses' prepared assets (mapped with `access`) at the admission `bindings` (indices) and
/// every count of `workers`, `repetitions` calls each, and compare every answer with the binding's prepared-data
/// reference. The cells of `execution::check_prepared_data`, plus per cell the storage request counters and the
/// child's `read_bytes` of its last call. `bound`: an author-requested child timeout in seconds (diagnostic jobs).
#[allow(clippy::too_many_arguments)]
pub fn check_stored_prepared_data(
    runner: &CandidateRunner,
    preflight: &QueryPreflight,
    references: &[BindingReference],
    library: &Path,
    uses: &[StorageUseRun<'_>],
    access: PartAccess,
    work: &Path,
    bindings: &[usize],
    workers: &[usize],
    repetitions: u32,
    bound: Option<u64>,
) -> Result<Value, AdmissionError> {
    let cells = stored_prepared_cells(runner, preflight, references, library, uses, access, work, bindings, workers, repetitions, bound)?;
    let mut record = prepared_data_record(preflight, cells, work)?;
    record["access"] = json!(access);
    Ok(record)
}

/// The prepared-data check of a submission's evaluation: the `measured` (benchmark) bindings with `repetitions` calls
/// each in one child job (evidence `work`), and every other admission binding with one call each in a second job
/// (`<work>-tests`): those bindings are tests, so they are compared exactly but not timed. Both at every count of
/// `workers`; one record over all cells (as [`check_stored_prepared_data`]).
#[allow(clippy::too_many_arguments)]
pub fn check_stored_prepared_data_measured(
    runner: &CandidateRunner,
    preflight: &QueryPreflight,
    references: &[BindingReference],
    library: &Path,
    uses: &[StorageUseRun<'_>],
    access: PartAccess,
    work: &Path,
    measured: &[usize],
    workers: &[usize],
    repetitions: u32,
) -> Result<Value, AdmissionError> {
    let tested: Vec<usize> = preflight.validation.full_data_bindings(&preflight.statement).into_iter().filter(|b| !measured.contains(b)).collect();
    let mut tests_work = work.as_os_str().to_owned();
    tests_work.push("-tests");
    let tests_work = PathBuf::from(tests_work);
    let mut cells = stored_prepared_cells(runner, preflight, references, library, uses, access, work, measured, workers, repetitions, None)?;
    if !tested.is_empty() {
        cells.extend(stored_prepared_cells(runner, preflight, references, library, uses, access, &tests_work, &tested, workers, 1, None)?);
    }
    let names = |bindings: &[usize]| bindings.iter().map(|&b| preflight.statement.bindings[b].name.clone()).collect::<Vec<_>>();
    let mut record = prepared_data_record(preflight, cells, work)?;
    record["access"] = json!(access);
    record["jobs"] = json!([{"bindings":names(measured),"calls":repetitions,"evidence":work,"role":"measured: the benchmark bindings (1 warm, then hot calls)"},
        {"bindings":names(&tested),"calls":1,"evidence":(!tested.is_empty()).then_some(&tests_work),"role":"tested only: the other admission bindings, one call each, compared exactly, not timed"}]);
    Ok(record)
}

/// The compared cells of one query job over the uses' prepared assets (`check_stored_prepared_data`).
#[allow(clippy::too_many_arguments)]
fn stored_prepared_cells(
    runner: &CandidateRunner,
    preflight: &QueryPreflight,
    references: &[BindingReference],
    library: &Path,
    uses: &[StorageUseRun<'_>],
    access: PartAccess,
    work: &Path,
    bindings: &[usize],
    workers: &[usize],
    repetitions: u32,
    bound: Option<u64>,
) -> Result<Vec<Value>, AdmissionError> {
    let arguments = binding_arguments(preflight, bindings);
    let request = WorkerRequest::for_storage_query(library, prepared_uses(uses), access, arguments, worker_counts(workers), repetitions, RANGE_CAPACITY);
    let result = runner.run(work, &request, bound)?;
    check_mapped_uses(uses, &result, work)?;
    let mut cells = vec![];
    for cell in compare_prepared_data(preflight, references, &result, bindings, workers, work)? {
        let last = cell.calls.last().expect("a compared cell has calls");
        let mut record = cell.record;
        record["storage_requests"] = storage_requests(&result, &last.outcome)?;
        record["process_io"] = process_io(&cell.calls);
        cells.push(record);
    }
    Ok(cells)
}

/// Every out-of-domain probe returns `ParamRefused` over the uses' prepared assets (as
/// `execution::check_parameter_refusals`).
pub fn check_stored_parameter_refusals(
    runner: &CandidateRunner,
    preflight: &QueryPreflight,
    library: &Path,
    uses: &[StorageUseRun<'_>],
    work: &Path,
) -> Result<Value, AdmissionError> {
    check_refusal_probes(runner, preflight, work, |probes| {
        WorkerRequest::for_storage_query(library, prepared_uses(uses), PartAccess::default(), probes, vec![1], 1, RANGE_CAPACITY)
    })
}

/// The selected tiny cases: per case, each use's tiny asset built by its `builder_library` from the case's storage
/// input, then `library` queried over those assets at the selected bindings and worker counts, each answer compared
/// with the verified evaluator's label (as `execution::check_tiny_cases`). Each case record lists every use's input
/// (synthetic columns, undelivered tables) and each verdict the request counters of its call.
pub fn check_stored_tiny_cases(
    runner: &CandidateRunner,
    preflight: &QueryPreflight,
    library: &Path,
    uses: &[StorageUseRun<'_>],
    work: &Path,
    selection: &TinyCaseSelection,
) -> Result<Value, AdmissionError> {
    if preflight.validation.formal {
        return Ok(tiny_cases_not_run(preflight));
    }
    let build_workers = *selection.workers.iter().max().ok_or_else(|| AdmissionError::tool("workers absent"))? as u32;
    for u in uses {
        refuse_uncertified_tiny_builds(&format!("storage {}", u.name), u.builder.assumes_constraints(u.assumes_declared_constraints), preflight)?;
    }
    let mut judged = CaseJudgements::default();
    for &index in &selection.cases {
        let case = preflight.cases.get(index).ok_or_else(|| AdmissionError::missing_input(format!("tiny case {index} does not exist")))?;
        let dir = case_directory(work, &case.name);
        let mut assets = vec![];
        let mut inputs = vec![];
        for (k, u) in uses.iter().enumerate() {
            let (parts, record) = u.builder.build(runner, preflight, u.declaration, index, &dir.join(format!("storage-{k}-{}", u.name)), build_workers)
                .map_err(|e| in_case(e, &case.name))?;
            inputs.push(json!({"storage":u.name.as_str(),"build":record}));
            assets.push(StorageUseInput { name: u.name.to_string(), parts_directory: parts });
        }
        let arguments = binding_arguments(preflight, &selection.bindings);
        let request = WorkerRequest::for_storage_query(library, assets, PartAccess::default(), arguments, worker_counts(&selection.workers), 1, RANGE_CAPACITY);
        let query = runner.run(&dir.join("query"), &request, None)?;
        let mut verdicts = judged.judge(preflight, index, &selection.bindings, &query, &dir)?;
        for (verdict, observation) in verdicts.iter_mut().zip(&query.observations) {
            // `stored_bytes`: the case's tiny assets as the child mapped them (not the prepared assets).
            verdict["storage_requests"] = storage_requests(&query, &observation.outcome)?;
        }
        let mut record = case_record(preflight, index, verdicts);
        record["storages"] = json!(inputs);
        judged.cases.push(record);
    }
    let mut record = judged.record(preflight, work);
    record["selection"] = json!({"cases":selection.cases.len(),"of_cases":preflight.cases.len(),"bindings":selection.bindings,"workers":selection.workers});
    Ok(record)
}

/// Storage-only test (the workload storage role): the storage `builder_library` of `declaration` builds the storage
/// input of every tiny case of every statement of `statements` that reads a stored table, with `workers` workers; every
/// build must return `Ok`. One record per build: statement, case, rows, synthetic columns, undelivered tables, parts
/// and builder wall time. Evidence under `work`. A builder that assumes the declared constraints
/// (`assumes_declared_constraints`) builds only certified cases; a statement without certified cases refuses it
/// ([`UNCERTIFIED_TINY_BUILDS`]) before anything is built.
pub fn check_storage_tiny_builds(
    runner: &CandidateRunner,
    builder_library: &Path,
    declaration: &DeclaredSource,
    assumes_declared_constraints: bool,
    statements: &[&QueryPreflight],
    work: &Path,
    workers: u32,
) -> Result<Value, AdmissionError> {
    if statements.iter().any(|p| p.validation.formal) {
        return Ok(json!({"status":"not_run","reason":TINY_NOT_RUN}));
    }
    for preflight in statements {
        refuse_uncertified_tiny_builds(&format!("storage library {}", builder_library.display()), assumes_declared_constraints, preflight)?;
    }
    let mut builds = vec![];
    let mut statements_read = vec![];
    for (s, preflight) in statements.iter().enumerate() {
        let statement = &preflight.statement;
        let reads_stored_table = statement.source.tables.iter().any(|t| declaration.tables.iter().any(|d| d.table_id == t.table_id));
        let mut read = json!({"statement_key":statement.key_v4_id,"reads_stored_table":reads_stored_table,"cases":preflight.cases.len()});
        if preflight.constraints_assumed {
            // Only certified cases are kept, so these are the certified ones; the skipped ones are counted here.
            read["certification"] = json!({"generated":preflight.case_certification["generated"],"skipped":preflight.case_certification["skipped_by_reason"],
                "warnings":preflight.case_certification["warnings"]});
        }
        statements_read.push(read);
        if !reads_stored_table {
            continue;
        }
        for (index, case) in preflight.cases.iter().enumerate() {
            let input = tiny_input(preflight, declaration, index)?;
            let dir = case_directory(&work.join(format!("statement-{s}")), &case.name);
            let (_, built) = build_tiny_asset(runner, builder_library, &input, &dir, workers).map_err(|e| in_case(e, &case.name))?;
            let wall_ns = built.observations.first().map(|o| o.outcome.usage.wall_ns);
            builds.push(json!({"statement_key":statement.key_v4_id,"case":case.name,"input":input.record(),"parts":built.parts,"build_wall_ns":wall_ns}));
        }
    }
    Ok(json!({"status":"built","builds":builds,"statements":statements_read,"evidence":work,
        "meaning":"the storage's checked builder on tiny-case inputs: each the projection of a case's complete database (tests, not proof; synthetic columns and undelivered tables hold its completion, fixtures; under declared constraints only certified cases)"}))
}

/// Why no tiny case runs under the validation policy `formal_proofs`.
pub const TINY_NOT_RUN: &str = "not_run: validation policy formal_proofs (no tiny cases are generated; the Verus proof against the fixed entry claim is the correctness claim)";

/// The tiny-case record of a check under the validation policy `formal_proofs`: nothing run.
pub(super) fn tiny_cases_not_run(preflight: &QueryPreflight) -> Value {
    json!({"status":"not_run","reason":TINY_NOT_RUN,"validation":preflight.validation.record()})
}

/// The storage input of tiny case `case` for one storage: its complete database's projection.
fn tiny_input(preflight: &QueryPreflight, declaration: &DeclaredSource, case: usize) -> Result<StorageCaseInput, AdmissionError> {
    let statement = &preflight.statement;
    storage_case_input(declaration, &statement.source, &preflight.databases[case]).map_err(|e| in_case(e, &preflight.cases[case].name))
}

/// Build one tiny asset with a storage's checked builder library: parts in `<dir>/parts`, evidence in `<dir>/build`.
/// The fixed storage entry refusing the input (`InvalidInput`) is a named tool failure, never the author's.
fn build_tiny_asset(runner: &CandidateRunner, library: &Path, input: &StorageCaseInput, dir: &Path, workers: u32) -> Result<(PathBuf, WorkerResult), AdmissionError> {
    let (parts, evidence) = (dir.join("parts"), dir.join("build"));
    let request = WorkerRequest::for_storage_build(library, input.input.clone(), &parts, workers, RANGE_CAPACITY);
    let result = runner.run(&evidence, &request, None)?;
    let status = result.observations.first().map(|o| o.outcome.status);
    if status == Some(CallStatus::InvalidInput) {
        return Err(AdmissionError::tool(format!(
            "tiny_storage_input_refused: the fixed storage entry refused the tiny input as outside the declared column domain before the builder ran (synthetic columns {:?}, undelivered tables {:?}); the candidate is not implicated; evidence {}",
            input.synthetic_columns,
            input.undelivered_tables,
            evidence.display()
        )));
    }
    if status != Some(CallStatus::Ok) || result.parts.is_none() {
        return Err(status_error(status, &format!("storage builder on a tiny case (rows {:?})", input.rows), &evidence));
    }
    Ok((parts, result))
}

/// The prepared assets of the uses, in use order.
fn prepared_uses(uses: &[StorageUseRun<'_>]) -> Vec<StorageUseInput> {
    uses.iter().map(|u| StorageUseInput { name: u.name.to_string(), parts_directory: u.prepared_parts.to_owned() }).collect()
}

/// The query job mapped exactly the given assets, in use order (names and stored bytes of their manifests).
fn check_mapped_uses(uses: &[StorageUseRun<'_>], result: &WorkerResult, work: &Path) -> Result<(), AdmissionError> {
    let mapped: Vec<(&str, u64)> = result.storage_uses.iter().map(|m| (m.name.as_str(), m.storage_bytes)).collect();
    let given: Vec<(&str, u64)> = uses.iter().map(|u| (u.name.as_str(), u.stored_bytes)).collect();
    if mapped != given {
        return Err(AdmissionError::tool(format!(
            "the query job mapped storage assets {mapped:?}, not the resolved assets {given:?} (name, stored bytes); evidence {}",
            work.display()
        )));
    }
    Ok(())
}

/// The request counters of one call of the query job `result` per storage use:
/// `[{"name","use_index","requests","elements","bytes","stored_bytes"}]`; name and stored bytes are those of the asset the
/// job mapped for that use (its manifest).
fn storage_requests(result: &WorkerResult, outcome: &CallOutcome) -> Result<Value, AdmissionError> {
    let counts = outcome.storage_requests.iter().map(|c| {
        let u = usize::try_from(c.use_index).ok().and_then(|i| result.storage_uses.get(i)).ok_or_else(|| AdmissionError::tool(format!("request counters of an unmapped storage use {}", c.use_index)))?;
        Ok(json!({"name":u.name,"use_index":c.use_index,"requests":c.requests,"elements":c.elements,"bytes":c.bytes,"stored_bytes":u.storage_bytes}))
    });
    Ok(Value::Array(counts.collect::<Result<_, AdmissionError>>()?))
}

/// The child's device reads during the calls of one cell (`None` where `/proc/self/io` was unavailable).
fn process_io(calls: &[&CallObservation]) -> Value {
    let per_call: Vec<Option<u64>> = calls.iter().map(|c| c.process_io.map(|io| io.read_bytes)).collect();
    json!({"read_bytes":per_call.last().copied().flatten(),"read_bytes_per_call":per_call,
        "meaning":"bytes the child caused to be read from the storage layer during the call (/proc/self/io read_bytes; page-cache hits count 0): environment dependent, descriptive only"})
}

fn in_case(mut error: AdmissionError, case: &str) -> AdmissionError {
    error.message = format!("{} (case {case})", error.message);
    error
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A builder that assumes the declared constraints runs only on a statement whose preflight certified its cases;
    /// every other builder runs on every kept case.
    #[test]
    fn constrained_builders_need_certified_cases() {
        let refused = certified_for("storage s", true, false, "k").unwrap_err();
        assert!(refused.message.starts_with("tiny_cases_uncertified:") && refused.message.ends_with("(storage s; statement k)") && refused.class.name() == "refusal", "{refused}");
        assert!(certified_for("storage s", true, true, "k").is_ok());
        assert!(certified_for("storage s", false, false, "k").is_ok() && certified_for("storage s", false, true, "k").is_ok());
    }
}
