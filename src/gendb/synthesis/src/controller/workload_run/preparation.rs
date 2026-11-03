//! What a workload run establishes before its first author call, once per controller process:
//!
//! 1. each statement is translated, bound and analyzed (`admission::prepare_statement`); a refused statement closes
//!    its query before any data is read, and so does a query whose `reselect_from` source does not match it
//!    (`reselection::check_source`) or whose `continue_from` source does not (`continuation::check_source`);
//! 2. the union of the accepted statements' source declarations (with a workload storage role: every declared column,
//!    for complete lossless coverage) is prepared once (`import::prepare_source`: resumed, reused, extended or
//!    imported; a resumed root lacking columns is extended by them), and every session shares that one capture (`storage::capture::SharedCapture`),
//!    which a storage may later extend by columns no statement demands; a resumed controller reopens the newest
//!    extension (`data-current.json`);
//! 3. each query's session is opened on the shared source with its objective (`QuerySession::open`: its inputs,
//!    preflight and prepared-data references, or those of the completed preflight named by `preflight_from`); a
//!    refused preflight (or an execution-time benchmark binding without an exact reference) closes the query before
//!    any author call.
//!
//! Every refusal is written as the query's `summary.json`. Nothing here depends on an author.

use super::WorkloadError;
use super::lifecycle::{data_root, query_directory, record_refusal};
use super::{continuation, reselection};
use crate::controller::records::{self, now_unix_ms};
use crate::controller::request::WorkloadRequest;
use crate::query::{PreflightFrom, QuerySession};
use crate::storage::capture::{CaptureSetting, SharedCapture, current_data_root};
use gendb_frontend::parser::SqlParser;
use gendb_storage::import::{ColumnDemand, ImportError, PreparationReport, PreparationRequest, PreparedRecord, PreparedSource, SqlReference, prepare_source};
use gendb_verification::admission::execution::CandidateRunner;
use gendb_verification::admission::{AdmissionError, EVIDENCE_FILE, Refused, Statement, prepare_statement, read_legacy_attestations, LegacyReferenceAttestation};
use serde_json::{Value, json};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;

/// Directory (under a query's directory) of its statement evidence and preflight records.
pub const STATEMENT_DIRECTORY: &str = "verus-preflight";

/// A workload whose queries are ready for their author sessions, or refused.
pub struct PreparedWorkload {
    /// One entry per request query, in request order.
    pub queries: Vec<PreparedQuery>,
    /// The shared prepared source; `None` when every statement was refused before data preparation.
    pub data: Option<PreparedData>,
}

pub enum PreparedQuery {
    /// The statement's session, shared by its query role and the workload storage role.
    Ready(Arc<QuerySession>),
    /// The refusal record (also the query's `summary.json`).
    Refused(Value),
}

/// The run's one prepared source and how it was obtained.
pub struct PreparedData {
    /// The source prepared (or reopened) by this controller process.
    pub source: Arc<PreparedSource>,
    /// The capture every session shares (starts at `source`; storages may extend it).
    pub capture: SharedCapture,
    pub report: PreparationReport,
    pub preparation_ns: u128,
    /// `workload-preparation-<ms>-<pid>.json` of this controller process.
    pub record: PathBuf,
}

/// Prepare every query of `request` in the run directory `root`. `worker`: the executable that runs candidate
/// libraries (`<worker> worker REQUEST RESULT`). Errors are framework failures; query refusals are results.
pub async fn prepare_workload(request: &WorkloadRequest, root: &Path, parser: &SqlParser, worker: &Path) -> Result<PreparedWorkload, WorkloadError> {
    let mut outcomes: Vec<Option<PreparedQuery>> = request.queries.iter().map(|_| None).collect();
    // Found before `prepare_statement` gives a restarted run a fresh statement directory.
    let earlier: Vec<Option<PathBuf>> = (0..request.queries.len()).map(|index| earlier_preflight(root, index)).collect();
    let statements = translate_statements(request, root, parser, &mut outcomes)?;
    let (demand, statements) = column_demand(request, root, statements, &mut outcomes)?;
    let data = if statements.is_empty() {
        None
    } else {
        let data = prepare_data(request, root, &demand)?;
        if request.storage_policy.is_fixed_flat() {
            require_flat_storages(request, &statements[0].1, &data)?;
        }
        let reference = SqlReference::new(data.source.clone()).map_err(WorkloadError::Preparation)?;
        let runner = CandidateRunner { worker: worker.to_path_buf() };
        let attestations = read_legacy_attestations(root).map_err(|e| WorkloadError::Record(records::RecordError::new(root, e.to_string())))?;
        // `max_concurrent_preparations` statements open their sessions at once (absent: one at a time), each on its own
        // thread driving its open on this runtime. Statements without an earlier preflight of this run go first: they
        // have the most work (fresh references).
        let context = SessionContext { request, root, parser, reference: &reference, runner: &runner, source: &data.source, earlier: &earlier, attestations: &attestations };
        let concurrency = request.max_concurrent_preparations.unwrap_or(1).min(statements.len()).max(1);
        let mut statements = statements;
        statements.sort_by_key(|(index, _)| earlier[*index].is_some());
        let started = Instant::now();
        eprintln!("preflight: preparing {} statements, {concurrency} at a time (max_concurrent_preparations)", statements.len());
        let opened: Vec<(usize, String, Result<QuerySession, Refused>)> = match tokio::runtime::Handle::current().runtime_flavor() {
            tokio::runtime::RuntimeFlavor::MultiThread if concurrency > 1 => {
                let handle = tokio::runtime::Handle::current();
                let queue = std::sync::Mutex::new(statements.into_iter());
                let done = std::sync::Mutex::new(Vec::new());
                tokio::task::block_in_place(|| {
                    std::thread::scope(|scope| {
                        for _ in 0..concurrency {
                            scope.spawn(|| {
                                loop {
                                    let next = queue.lock().expect("preparation queue").next();
                                    let Some((index, statement)) = next else { break };
                                    let opened = handle.block_on(context.open(index, statement));
                                    done.lock().expect("prepared sessions").push(opened);
                                }
                            });
                        }
                    })
                });
                done.into_inner().expect("prepared sessions")
            }
            _ => {
                let mut opened = vec![];
                for (index, statement) in statements {
                    opened.push(context.open(index, statement).await);
                }
                opened
            }
        };
        eprintln!("preflight: every statement session opened or refused in {:.1} s", started.elapsed().as_secs_f64());
        for (index, sql, opened) in opened {
            let query = &request.queries[index];
            outcomes[index] = Some(match opened {
                Ok(session) => PreparedQuery::Ready(Arc::new(session.with_targets(query.objective.runtime_targets().to_vec(), query.objective.early_stop()))),
                Err(refused) => refusal(root, index, &sql, &refused)?,
            });
        }
        Some(data)
    };
    let queries = outcomes.into_iter().map(|outcome| outcome.expect("every query is ready or refused")).collect();
    Ok(PreparedWorkload { queries, data })
}

/// Step 1 for every query: its translated statement, or its refusal recorded in `outcomes`.
fn translate_statements(request: &WorkloadRequest, root: &Path, parser: &SqlParser, outcomes: &mut [Option<PreparedQuery>]) -> Result<Vec<(usize, Statement)>, WorkloadError> {
    let mut statements = Vec::new();
    for (index, query) in request.queries.iter().enumerate() {
        let directory = query_directory(root, index).join(STATEMENT_DIRECTORY);
        let constraints = request.integrity_constraints.as_ref();
        match prepare_statement(parser, &request.dataset, constraints, &query.sql, &query.parameters, &query.test_bindings, query.objective.benchmark_bindings(), &directory) {
            Ok(statement) => {
                let source_check = if query.reselect_from.is_some() {
                    reselection::check_source(request, index, &statement.key_v4_id).err().map(|reason| (reason, RESELECTION_REFUSAL_REASON))
                } else if query.continue_from.is_some() {
                    continuation::check_source(request, index, &statement.key_v4_id).err().map(|reason| (reason, CONTINUATION_REFUSAL_REASON))
                } else {
                    None
                };
                match source_check {
                    Some((reason, why)) => outcomes[index] = Some(source_refusal(root, index, &query.sql, &reason, why)?),
                    None => statements.push((index, statement)),
                }
            }
            Err(refused) => outcomes[index] = Some(refusal(root, index, &query.sql, &refused)?),
        }
    }
    Ok(statements)
}

/// Steps 1 and 2 only, for `gendb prepare-flat-storage`: the statements (for the dataset schema) and the capture of
/// every column of every table; no preflight, no reference, no author. Returns one accepted statement and the data.
pub fn prepare_flat_capture(request: &WorkloadRequest, root: &Path, parser: &SqlParser) -> Result<(Statement, PreparedData), WorkloadError> {
    let mut outcomes: Vec<Option<PreparedQuery>> = request.queries.iter().map(|_| None).collect();
    let statements = translate_statements(request, root, parser, &mut outcomes)?;
    let (demand, mut statements) = column_demand(request, root, statements, &mut outcomes)?;
    if statements.is_empty() {
        return Err(WorkloadError::invalid("no statement of the request was accepted, so the dataset schema is not known"));
    }
    let data = prepare_data(request, root, &demand)?;
    Ok((statements.swap_remove(0).1, data))
}

/// What opening one statement's session reads (shared by the concurrent opens).
struct SessionContext<'a> {
    request: &'a WorkloadRequest,
    root: &'a Path,
    parser: &'a SqlParser,
    reference: &'a SqlReference,
    runner: &'a CandidateRunner,
    source: &'a Arc<PreparedSource>,
    earlier: &'a [Option<PathBuf>],
    attestations: &'a [LegacyReferenceAttestation],
}

impl SessionContext<'_> {
    /// Open query `index`'s session (`QuerySession::open`) from its named or its own earlier preflight, or fresh.
    async fn open(&self, index: usize, statement: Statement) -> (usize, String, Result<QuerySession, Refused>) {
        let sql = statement.sql.clone();
        let query = &self.request.queries[index];
        let validation = match self.request.validation.for_statement(query.name.as_deref(), &statement) {
            Ok(validation) => validation,
            Err(error) => return (index, sql, Err(Refused::at(error, json!({"stage":"validation"})))),
        };
        let from = match (query.preflight_from.as_deref(), self.earlier[index].as_deref()) {
            (Some(named), _) => PreflightFrom::Named(named),
            (None, Some(own)) => PreflightFrom::Earlier { from: own, attestations: self.attestations },
            (None, None) => PreflightFrom::Fresh,
        };
        let directory = query_directory(self.root, index);
        let workers = self.request.hardware.threads.clone();
        let execution_time = query.objective.is_execution_time();
        let opened = QuerySession::open(statement, self.source.clone(), self.reference, self.parser, &directory, self.runner.clone(), workers, execution_time, from, validation).await;
        (index, sql, opened)
    }
}

/// This run's newest completed preflight of query `index`: a statement directory (`verus-preflight` or a restart's
/// `verus-preflight-<ms>`) holding preflight evidence, written by an earlier controller process of the run. A restart
/// reuses it when its evidence identity is still the current one (`PreflightFrom::Earlier`).
fn earlier_preflight(root: &Path, index: usize) -> Option<PathBuf> {
    let restart_prefix = format!("{STATEMENT_DIRECTORY}-");
    std::fs::read_dir(query_directory(root, index))
        .ok()?
        .filter_map(|entry| entry.ok().map(|e| e.path()))
        .filter(|path| path.file_name().and_then(|n| n.to_str()).is_some_and(|n| n == STATEMENT_DIRECTORY || n.starts_with(&restart_prefix)))
        .filter_map(|path| Some((std::fs::metadata(path.join(EVIDENCE_FILE)).ok()?.modified().ok()?, path)))
        .max()
        .map(|(_, path)| path)
}

/// The union of the accepted statements' source declarations, and the statements that remain accepted: a
/// declaration that does not bind to the dataset refuses its query.
fn column_demand(
    request: &WorkloadRequest,
    root: &Path,
    statements: Vec<(usize, Statement)>,
    outcomes: &mut [Option<PreparedQuery>],
) -> Result<(ColumnDemand, Vec<(usize, Statement)>), WorkloadError> {
    let mut demand = ColumnDemand::default();
    let mut accepted = Vec::with_capacity(statements.len());
    for (index, statement) in statements {
        let mut with_statement = demand.clone();
        match with_statement.add_declaration(&request.dataset, &statement.source) {
            Ok(()) => {
                demand = with_statement;
                accepted.push((index, statement));
            }
            Err(error) => {
                let refused = Refused::at(AdmissionError::unsupported(format!("source declaration: {error}")), json!({"stage":"capture"}));
                outcomes[index] = Some(refusal(root, index, &statement.sql, &refused)?);
            }
        }
    }
    Ok((demand, accepted))
}

/// The columns the run's capture must hold: the accepted statements' columns, and with a workload storage role or
/// under `fixed_flat` every declared column of every table. The workload storages must together store every column
/// (complete lossless coverage, `storage::coverage`), so their builders read columns no statement
/// delivers; the flat storages store every column of every table.
fn capture_demand(request: &WorkloadRequest, statements: &ColumnDemand) -> Result<ColumnDemand, WorkloadError> {
    let mut demand = statements.clone();
    if request.workload_storage.is_some() || request.storage_policy.is_fixed_flat() {
        for table in &request.dataset.tables {
            let every: Vec<usize> = (0..table.fields.len()).collect();
            demand.add_columns(&request.dataset, &table.name, &every).map_err(WorkloadError::Preparation)?;
        }
    }
    Ok(demand)
}

/// Prepare the capture once for the whole workload ([`capture_demand`]) and record how (this controller process's
/// `workload-preparation-<ms>-<pid>.json`, written before any author call). A resumed run reopens its newest prepared
/// root for the columns that root was prepared for; columns it lacks are added by one extension of that root
/// (`SharedCapture::covering_demand`: only the missing columns are read from the original files, every captured
/// column, row order and data fact is kept).
fn prepare_data(request: &WorkloadRequest, root: &Path, statements: &ColumnDemand) -> Result<PreparedData, WorkloadError> {
    let started = Instant::now();
    let registry = request.library.with_extension("prepared-workloads");
    let data_root = current_data_root(root)?.unwrap_or_else(|| data_root(root));
    let demand = capture_demand(request, statements)?;
    let resumed_demand = PreparedRecord::read(&data_root).ok().map(|record| record.demand);
    let (source, report) = prepare_source(&PreparationRequest {
        dataset: &request.dataset,
        demand: resumed_demand.as_ref().unwrap_or(&demand),
        base: request.prepared_workload.as_deref(),
        registry: &registry,
        root: &data_root,
    })
    .map_err(WorkloadError::Preparation)?;
    let capture = SharedCapture::new(CaptureSetting { dataset: request.dataset.clone(), registry, run_root: root.to_path_buf() }, Arc::new(source));
    let (source, extension) = capture
        .covering_demand(&demand)
        .map_err(|e| WorkloadError::Preparation(ImportError::Prepared { path: data_root.clone(), reason: format!("extending the capture to the run's demand: {e}") }))?;
    let preparation_ns = started.elapsed().as_nanos();
    let record = root.join(format!("workload-preparation-{}-{}.json", now_unix_ms(), std::process::id()));
    records::write_new_json(
        &record,
        &json!({"format_version":2,"preparation_ns":preparation_ns,"preparation":report,"demand":demand,"statements_demand":statements,
            "complete_capture":request.workload_storage.is_some() || request.storage_policy.is_fixed_flat(),"extension":extension,"validation":request.validation.name(),
            "source_version":source.source_snapshot(),"prepared_workload":source.root().join("workload.json"),
            "scope":"this controller process: the union of the accepted statements' source columns (with a workload storage role: every declared column), prepared once and shared read-only by every query; persisted before any author call"}),
    )?;
    Ok(PreparedData { source, capture, report, preparation_ns, record })
}

/// Under `fixed_flat`, stop before any preflight or author unless every table's flat storage and asset are prepared for
/// this capture (`storage::flat::flat_readiness`; prepared once by `gendb prepare-flat-storage`, never here).
fn require_flat_storages(request: &WorkloadRequest, statement: &Statement, data: &PreparedData) -> Result<(), WorkloadError> {
    let store = gendb_artifacts::ObjectStore::open(&request.library).map_err(|e| WorkloadError::invalid(format!("library: {e}")))?;
    let capture = gendb_storage::versions::CurrentCapture::of(&data.capture.current()).map_err(|e| WorkloadError::invalid(e.to_string()))?;
    match crate::storage::flat::flat_readiness(&store, &statement.instance.doc.tables, &capture).map_err(|e| WorkloadError::invalid(e.to_string()))? {
        Ok(_) => Ok(()),
        Err(missing) => Err(WorkloadError::invalid(format!(
            "flat_storage_not_prepared: storage_policy fixed_flat reads the prepared flat storages; run gendb prepare-flat-storage with this request first ({})",
            missing.join("; ")
        ))),
    }
}

/// Why a query whose `reselect_from` source does not match it is refused.
const RESELECTION_REFUSAL_REASON: (&str, &str) =
    (crate::controller::reselect::SOURCE_REFUSAL, "refused before data preparation: the named reselection source is not a closed session of this query under the same conditions");

/// Why a query whose `continue_from` source does not match it is refused.
const CONTINUATION_REFUSAL_REASON: (&str, &str) = (
    crate::query::incumbent::SOURCE_REFUSAL,
    "refused before data preparation: the named continuation source is not a closed session of this statement under the same correctness conditions that admitted a candidate",
);

/// A query whose named source session (`reselect_from` or `continue_from`) does not match it, refused before any data
/// preparation with `why` (failure class, reason); its record is also written as the query's `summary.json`.
fn source_refusal(root: &Path, index: usize, sql: &str, error: &str, why: (&str, &str)) -> Result<PreparedQuery, WorkloadError> {
    let (class, reason) = why;
    let record = json!({"status":"refused","sql":sql,"error":error,"failure_class":class,
        "inference_dispatched":false,"calls":0,"iterations":0,"reason":reason});
    record_refusal(root, index, &record)?;
    Ok(PreparedQuery::Refused(record))
}

/// A query refused before any author call; its record is also written as the query's `summary.json`.
fn refusal(root: &Path, index: usize, sql: &str, refused: &Refused) -> Result<PreparedQuery, WorkloadError> {
    let record = json!({"status":"unsupported_capability","sql":sql,"error":refused.error.to_string(),"failure_class":refused.error.class,
        "inference_dispatched":false,"calls":0,"iterations":0,
        "reason":"refused before any author call: the frontend, the parameter declaration, the source binding, the framework crate check, the saved answers or (validation policy tests_and_references) the test references could not be established",
        "preflight":refused.detail});
    record_refusal(root, index, &record)?;
    Ok(PreparedQuery::Refused(record))
}
