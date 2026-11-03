//! Child side: the body of `gendb worker REQUEST RESULT`. Reads and checks the request, runs the build or query job
//! with every input retained until process exit ([`super::inputs`]), and writes the result. A limited engine job runs
//! each call under the watchdog ([`super::watchdog`], which may end the child with the result so far), a profile job
//! samples each call ([`super::sampler`]), and an engine job with an answer bound stores each rows answer over it as its
//! summary and first rows ([`super::stored_answer`]), right after the call, before the call is recorded.

use super::error::WorkerError;
use super::inputs::{
    RetainedStorageUses, retained, retained_bindings, retained_columns, retained_parts, retained_storage_uses,
};
use super::process_io::{ProcessIoDelta, measure_process_io};
use super::protocol::{decode_hex, CallObservation, RequestAbi, StorageUseInput, WorkerInput, WorkerRequest, WorkerResult, WorkerJob};
use super::sampler::Sampler;
use super::stored_answer::{AnswerBound, stored_rows};
use super::watchdog::{Watchdog, WatchdogConfig};
use crate::abi::{CallOutcome, DerivedStorageBuildLibrary, EngineLibrary, StorageBuildLibrary, StorageQueryLibrary, VerusLibrary};
use crate::answer::{AnswerError, QueryAnswer, rows_json};
use crate::identity::WorkerBuildIdentity;
use gendb_storage::io::{NativeColumn, PartAccess, PartFilesWriter, PartsFormat, PartsManifest};
use serde_json::Value;
use std::ffi::OsString;
use std::path::Path;
use std::process::ExitCode;

/// Entry of the worker subcommand (`arguments`: the words after `worker`). Exit 0 with the result file written, 1
/// with the refusal on stderr and no result file, 2 for a usage error, and
/// [`UNFINISHED_EXIT_CODE`](super::protocol::UNFINISHED_EXIT_CODE) when the watchdog stopped a call at a limit (the
/// result so far written; the watchdog ends the process itself).
pub fn worker_main(arguments: &[OsString]) -> ExitCode {
    let [request, result] = arguments else {
        eprintln!("usage: gendb worker REQUEST RESULT");
        return ExitCode::from(2);
    };
    match run_child(Path::new(request), Path::new(result)) {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}

/// Run the request at `request_path` and write its result to `result_path`. Must run in a dedicated child process:
/// everything loaded is leaked on purpose and lives until the OS ends the process, after the result is complete.
pub fn run_child(request_path: &Path, result_path: &Path) -> Result<(), WorkerError> {
    let request = read_request(request_path)?;
    let result = match &request.job {
        WorkerJob::Build { output_directory } => run_build(&request, output_directory)?,
        WorkerJob::Query { parts_directory } => run_queries(&request, parts_directory.as_deref())?,
        WorkerJob::StorageBuild { output_directory } => run_storage_build(&request, output_directory)?,
        WorkerJob::StorageQuery { storage_uses, access } => run_storage_queries(&request, storage_uses, access)?,
        WorkerJob::EngineQuery { storage_uses, access, asts } => run_engine_queries(&request, storage_uses, access, asts, result_path)?,
    };
    let bytes = serde_json::to_vec_pretty(&result).map_err(WorkerError::json(result_path))?;
    std::fs::write(result_path, bytes).map_err(WorkerError::file(result_path))
}

/// The request, refused before anything is opened unless it carries a v3 or v4 marker, names exactly this build and
/// follows the request rules. The build is compared before the full decode, so a request of another build (a saved
/// request of the earlier GenDB version has another identity form) is reported as such rather than as a malformed request.
fn read_request(path: &Path) -> Result<WorkerRequest, WorkerError> {
    let bytes = std::fs::read(path).map_err(WorkerError::file(path))?;
    let probe: Value = serde_json::from_slice(&bytes).map_err(WorkerError::json(path))?;
    let markers = [RequestAbi::V3, RequestAbi::V4].map(|abi| serde_json::to_value(abi).ok());
    match probe.get("abi") {
        Some(marker) if markers.iter().flatten().any(|known| known == marker) => {}
        marker => {
            let marker = marker.map(|m| m.as_str().map_or_else(|| m.to_string(), String::from));
            return Err(WorkerError::SavedAbi { marker });
        }
    }
    let current = serde_json::to_value(WorkerBuildIdentity::current()).map_err(WorkerError::json(path))?;
    if probe.get("build") != Some(&current) {
        return Err(WorkerError::BuildIdentity { requested: probe.get("build").cloned().unwrap_or(Value::Null) });
    }
    let request: WorkerRequest = serde_json::from_value(probe).map_err(WorkerError::json(path))?;
    request.check_shape().map_err(WorkerError::Request)?;
    Ok(request)
}

/// v3 build job: run the builder once over the source columns; its parts are written as delivered and committed
/// (manifest written) only if it returned `Ok`.
fn run_build(request: &WorkerRequest, output_directory: &Path) -> Result<WorkerResult, WorkerError> {
    let columns = retained_columns(&request.input)?;
    // SAFETY: an offline child loading a library produced by the framework's Verus build of a frozen crate.
    let library = retained(unsafe { VerusLibrary::load(&request.library)? });
    let workers = request.workers[0];
    let parts = PartFilesWriter::new(output_directory, PartsFormat::SavedV3)?;
    // SAFETY: `columns` and `library` are retained until this process exits.
    let (outcome, stored) = unsafe { library.call_build(columns, workers as usize, range_capacity(request)?, parts)? };
    let observation = build_observation(workers, outcome, None);
    Ok(run_result(request, library.path(), columns, vec![observation], stored))
}

/// v4 storage build job: as a v3 build, through the storage library's entry, storing format-2 (little-endian) parts;
/// the call's process I/O is recorded.
fn run_storage_build(request: &WorkerRequest, output_directory: &Path) -> Result<WorkerResult, WorkerError> {
    if let WorkerInput::StoredParts { uses, extends } = &request.input {
        return run_derived_storage_build(request, uses, *extends, output_directory);
    }
    let columns = retained_columns(&request.input)?;
    // SAFETY: an offline child loading a library produced by the framework's Verus build of a frozen crate.
    let library = retained(unsafe { StorageBuildLibrary::load(&request.library)? });
    let workers = request.workers[0];
    let parts = PartFilesWriter::new(output_directory, PartsFormat::LittleEndian)?;
    let capacity = range_capacity(request)?;
    // SAFETY: `columns` and `library` are retained until this process exits.
    let (call, process_io) = measure_process_io(|| unsafe { library.call_build(columns, workers as usize, capacity, parts) });
    let (outcome, stored) = call?;
    let observation = build_observation(workers, outcome, process_io);
    Ok(run_result(request, library.path(), columns, vec![observation], stored))
}

/// v4 build of a storage built from admitted storages: the sources' parts mapped as a query maps its storage uses, the
/// extended source's part files linked unchanged as the first parts, then the derived builder's parts; the call's
/// process I/O is recorded.
fn run_derived_storage_build(request: &WorkerRequest, uses: &[StorageUseInput], extends: Option<usize>, output_directory: &Path) -> Result<WorkerResult, WorkerError> {
    let RetainedStorageUses { part_lists, mapped } = retained_storage_uses(uses, &PartAccess::default())?;
    // SAFETY: an offline child loading a library produced by the framework's Verus build of a frozen crate.
    let library = retained(unsafe { DerivedStorageBuildLibrary::load(&request.library)? });
    let workers = request.workers[0];
    let mut parts = PartFilesWriter::new(output_directory, PartsFormat::LittleEndian)?;
    if let Some(k) = extends {
        parts.link_parts_of(&uses[k].parts_directory)?;
    }
    let capacity = range_capacity(request)?;
    // SAFETY: every source's parts and `library` are retained until this process exits.
    let (call, process_io) = measure_process_io(|| unsafe { library.call_build(part_lists, workers as usize, capacity, parts) });
    let (outcome, stored) = call?;
    let observation = build_observation(workers, outcome, process_io);
    let mut result = run_result(request, library.path(), &[], vec![observation], stored);
    result.storage_uses = mapped;
    Ok(result)
}

fn build_observation(workers: u32, outcome: CallOutcome, process_io: Option<ProcessIoDelta>) -> CallObservation {
    CallObservation { binding: None, workers, repetition: 0, outcome, rows: None, sql_error: None, process_io, peak_anon_bytes: None, samples: None, stored_answer: None }
}

/// v3 query job: every binding, then every worker count, then every repetition, over the same mapped parts.
fn run_queries(request: &WorkerRequest, parts_directory: Option<&Path>) -> Result<WorkerResult, WorkerError> {
    let parts = retained_parts(parts_directory)?;
    // SAFETY: an offline child loading a library produced by the framework's Verus build of a frozen crate.
    let library = retained(unsafe { VerusLibrary::load(&request.library)? });
    let observations = every_call(request, |arguments, workers, capacity| {
        // SAFETY: `parts`, `arguments` and `library` are retained until this process exits.
        Ok((unsafe { library.call_query(parts, arguments, workers, capacity)? }, None))
    }, None)?;
    Ok(run_result(request, library.path(), &[], observations, None))
}

/// v4 query job: as a v3 query job, over one mapped part list per storage use (declared use order); every call
/// records its per-use request counters (in the outcome) and its process I/O.
fn run_storage_queries(
    request: &WorkerRequest,
    uses: &[StorageUseInput],
    access: &PartAccess,
) -> Result<WorkerResult, WorkerError> {
    let RetainedStorageUses { part_lists, mapped } = retained_storage_uses(uses, access)?;
    // SAFETY: an offline child loading a library produced by the framework's Verus build of a frozen crate.
    let library = retained(unsafe { StorageQueryLibrary::load(&request.library)? });
    let observations = every_call(request, |arguments, workers, capacity| {
        // SAFETY: every use's parts, `arguments` and `library` are retained until this process exits.
        let (call, process_io) =
            measure_process_io(|| unsafe { library.call_query(part_lists, arguments, workers, capacity) });
        Ok((call?, process_io))
    }, None)?;
    let mut result = run_result(request, library.path(), &[], observations, None);
    result.storage_uses = mapped;
    Ok(result)
}

/// Engine job: the verified echo of every statement first (untimed), then every statement (outer loop), every worker
/// count and every repetition over one mapped part list per storage use; each call records its per-use request
/// counters and its process I/O. The AST bytes are retained like the parts. With limits, the watchdog is armed for each
/// call and every finished call is recorded with it (a stop writes them to `result_path` and ends the child); with
/// sampling, each call is sampled; with an answer bound, each answer is stored under it.
fn run_engine_queries(request: &WorkerRequest, uses: &[StorageUseInput], access: &PartAccess, asts: &[String], result_path: &Path) -> Result<WorkerResult, WorkerError> {
    let RetainedStorageUses { part_lists, mapped } = retained_storage_uses(uses, access)?;
    // SAFETY: an offline child loading a library produced by the framework's Verus build of a frozen crate.
    let library = retained(unsafe { EngineLibrary::load(&request.library)? });
    let statements: Vec<&'static [u8]> = asts
        .iter()
        .map(|hex| decode_hex(hex).map(|bytes| &retained(bytes)[..]).ok_or(WorkerError::Request("an engine job's AST bytes must be lowercase hex")))
        .collect::<Result<_, _>>()?;
    let mut echoes = vec![];
    for ast in &statements {
        // SAFETY: `ast` and `library` are retained until this process exits.
        let text = unsafe { library.echo(ast)? };
        echoes.push(String::from_utf8(text).map_err(|_| WorkerError::Request("an engine echo is not UTF-8"))?);
    }
    let capacity = range_capacity(request)?;
    let mut result = run_result(request, library.path(), &[], vec![], None);
    result.storage_uses = mapped;
    result.echoes = echoes;
    let watchdog = request
        .is_limited()
        .then(|| {
            Watchdog::start(WatchdogConfig {
                call_limit_ns: request.call_limit_ns,
                anon_memory_limit_bytes: request.anon_memory_limit_bytes,
                result_path: result_path.to_owned(),
                skeleton: result.clone(),
            })
        })
        .transpose()
        .map_err(WorkerError::file(result_path))?;
    let sampler = request.sampling.map(|s| Sampler::install(s.interval_us)).transpose().map_err(WorkerError::file("sigaction(SIGPROF)"))?;
    let mut observations = vec![];
    for (statement, ast) in statements.iter().enumerate() {
        for &workers in &request.workers {
            for repetition in 0..request.repetitions {
                if let Some(watchdog) = &watchdog {
                    watchdog.arm(statement, workers, repetition);
                }
                if let Some(sampler) = &sampler {
                    sampler.begin_call();
                }
                // SAFETY: every use's parts, `ast` and `library` are retained until this process exits.
                let (call, process_io) = measure_process_io(|| unsafe { library.call(part_lists, ast, workers as usize, capacity) });
                let samples = sampler.as_ref().map(Sampler::end_call);
                let peak_anon_bytes = watchdog.as_ref().and_then(Watchdog::disarm);
                let mut observation = observed_query(statement, workers, repetition, call?, process_io, request.answer_bound)?;
                observation.peak_anon_bytes = peak_anon_bytes;
                observation.samples = samples;
                match &watchdog {
                    Some(watchdog) => watchdog.record(observation),
                    None => observations.push(observation),
                }
            }
        }
    }
    if let Some(watchdog) = watchdog {
        observations = watchdog.finish();
    }
    result.observations = observations;
    Ok(result)
}

/// Every binding (outer loop), then every worker count, then every repetition: one `call` each, with its readable
/// answer (stored under `bound` when given).
fn every_call(
    request: &WorkerRequest,
    mut call: impl FnMut(&'static [crate::abi::StatementArgument], usize, usize) -> Result<(CallOutcome, Option<ProcessIoDelta>), WorkerError>,
    bound: Option<AnswerBound>,
) -> Result<Vec<CallObservation>, WorkerError> {
    let bindings = retained_bindings(&request.bindings);
    let capacity = range_capacity(request)?;
    let mut observations = vec![];
    for (binding, arguments) in bindings.iter().enumerate() {
        for &workers in &request.workers {
            for repetition in 0..request.repetitions {
                let (outcome, process_io) = call(arguments, workers as usize, capacity)?;
                observations.push(observed_query(binding, workers, repetition, outcome, process_io, bound)?);
            }
        }
    }
    Ok(observations)
}

/// A query call with its readable answer: rows as PostgreSQL output text (`Ok`) or the exact SQL error (`SqlError`).
/// With `bound`, a rows answer over it is stored as its summary and first rows (its wire taken out of the outcome).
pub(super) fn observed_query(
    binding: usize,
    workers: u32,
    repetition: u32,
    mut outcome: CallOutcome,
    process_io: Option<ProcessIoDelta>,
    bound: Option<AnswerBound>,
) -> Result<CallObservation, WorkerError> {
    let (rows, sql_error, stored_answer) = match QueryAnswer::of(&outcome) {
        Ok(QueryAnswer::Rows(rows)) => match bound {
            None => (Some(rows_json(&rows).map_err(AnswerError::from)?), None, None),
            Some(bound) => {
                let (kept, stored) = stored_rows(&mut outcome, &rows, bound).map_err(AnswerError::from)?;
                (Some(kept), None, stored)
            }
        },
        Ok(QueryAnswer::SqlError(error)) => (None, Some(error), None),
        Ok(QueryAnswer::Capacity | QueryAnswer::ParamRefused) | Err(AnswerError::NoAnswer(_)) => (None, None, None),
        Err(error) => return Err(error.into()),
    };
    Ok(CallObservation { binding: Some(binding), workers, repetition, outcome, rows, sql_error, process_io, peak_anon_bytes: None, samples: None, stored_answer })
}

fn range_capacity(request: &WorkerRequest) -> Result<usize, WorkerError> {
    usize::try_from(request.range_capacity)
        .map_err(|_| WorkerError::Request("range capacity exceeds the address space"))
}

fn run_result(
    request: &WorkerRequest,
    library: &Path,
    columns: &[NativeColumn],
    observations: Vec<CallObservation>,
    parts: Option<PartsManifest>,
) -> WorkerResult {
    WorkerResult {
        abi: request.abi,
        purpose: request.purpose,
        library: library.to_owned(),
        input_columns: columns.len(),
        column_rows: columns.iter().map(|column| column.len as u64).collect(),
        bindings: request.bindings.clone(),
        observations,
        parts,
        storage_uses: vec![],
        echoes: vec![],
        unfinished: None,
    }
}
