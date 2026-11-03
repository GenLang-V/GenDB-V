//! Serving one statement from an admitted engine version: compose and execute only.
//!
//! The caller resolves the engine version (`gendb_artifacts::verus::resolve_engine`: the selected version, or one
//! admitted version by package) and hands over the statement either as a bound, encoded document
//! ([`EngineStatement::Bound`]: SQL translated over the engine's recorded DDL, its binding substituted after the
//! constant check and encoded by `gendb_frontend::engine_encode`) or as AST bytes as given ([`EngineStatement::Bytes`],
//! whose meaning is `decode_spec(bytes)`). Serving then:
//! 1. decides the worker count against the engine's proved domain: outside it the answer is [`EngineAnswer::Refused`]
//!    and nothing runs (the entry's `Refused` condition; the trusted shim would refuse such a count before the entry);
//! 2. resolves one asset per storage use for the current capture (`gendb_storage::versions`); a use without one is
//!    refused by name, never served from another route or another package;
//! 3. runs one worker child (`WorkerJob::EngineQuery`): the engine's verified echo of the bytes first (untimed), then the
//!    calls (the last one is served);
//! 4. compares the echo with the host's rendering of the bound document (`gendb_sqlspec::evaluator::echo_text`): an
//!    unequal echo withholds the answer (`engine_echo_mismatch`), because the host's encoding is the trusted step the
//!    echo validates; bytes given as such have no host document, and their echo is recorded for review;
//! 5. returns the answer with its checked meaning: rows, the exact SQL error, `Capacity`, or the named refusals
//!    `ParamRefused` (the decoded statement is not supported: not well typed for the schema) and `Malformed` (the bytes
//!    decode to no statement).
//!
//! The AST digest (SHA-256 of the bytes) and the echo verdict are part of every record. Nothing here proves,
//! regenerates, rebuilds or validates stored data, nothing is written to the library, and there is no fallback to a
//! per-template package.

use super::error::ServeError;
use super::ServedStorage;
use crate::abi::{CallOutcome, CallStatus};
use crate::answer::{AnswerError, QueryAnswer};
use crate::worker::{MappedStorageUse, ProcessIoDelta, StorageUseInput, WorkerError, WorkerRequest, WorkerResult, spawn};
use gendb_artifacts::verus::{ResolvedEngine, library_path};
use gendb_artifacts::{ContentId, ObjectStore};
use gendb_frontend::engine_encode::{ENGINE_AST_FORMAT, EngineAst};
use gendb_sqlspec::evaluator::echo_text;
use gendb_storage::io::PartAccess;
use gendb_storage::versions::{CurrentCapture, resolve_storage_assets};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::fmt;
use std::path::{Path, PathBuf};

/// Trusted serving item of engine packages, `(id, statement)`, for their TCB list.
pub const ENGINE_SERVING_ITEMS: [(&str, &str); 1] = [(
    "engine_serving",
    "gendb_runtime::serve::engine: the engine version is resolved from the library's engine stream (the selected version or \
     an admitted version by package), every storage use's asset for one current capture (gendb_storage::versions), the \
     worker count outside the proved domain is answered Refused before any call, and the answer is served only when the \
     engine's verified echo equals the host's rendering of the bound document (gendb_sqlspec::evaluator::echo_text); the \
     SQL is translated over the engine's recorded DDL by the trusted frontend, bound after the constant check and encoded \
     (host_ast_encoding); a use without an asset is refused, never served from another route or package",
)];

/// The statement one serving call answers.
#[derive(Clone, Debug)]
pub enum EngineStatement {
    /// A translated statement with its binding substituted and encoded (`engine_encode::encode_binding`): the bytes
    /// and the document they encode, whose rendering the engine's echo must equal.
    Bound(Box<EngineAst>),
    /// AST bytes as given (for example to see how the engine answers bytes no frontend produces). Their meaning is
    /// `decode_spec(bytes)`, which the engine's echo shows; there is no host document to compare it with.
    Bytes(Vec<u8>),
}

impl EngineStatement {
    pub fn bytes(&self) -> &[u8] {
        match self {
            Self::Bound(ast) => &ast.bytes,
            Self::Bytes(bytes) => bytes,
        }
    }

    /// The host's echo text of the statement (`None` for bytes given as such).
    fn host_echo(&self) -> Option<String> {
        match self {
            Self::Bound(ast) => Some(echo_text(&ast.document)),
            Self::Bytes(_) => None,
        }
    }
}

/// SHA-256 of AST bytes as lowercase hex (the digest serving records).
pub fn ast_digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes).iter().map(|b| format!("{b:02x}")).collect()
}

/// How the engine's verified echo of the bytes compared with the host's rendering of the document.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EchoVerdict {
    /// Equal byte for byte: the bytes encode the document (translation validation of the host encoder).
    Equal,
    /// The statement was given as bytes: the engine's echo is recorded, with nothing to compare it with.
    NoHostDocument,
    /// No call ran (a refused worker count).
    NotRun,
}

impl EchoVerdict {
    fn name(&self) -> &'static str {
        match self {
            Self::Equal => "equal",
            Self::NoHostDocument => "no_host_document",
            Self::NotRun => "not_run",
        }
    }
}

/// What the engine answered, each with its checked meaning (`theorem_engine_end_to_end`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EngineAnswer {
    /// Rows (an allowed output), the exact SQL error, or `Capacity` (the database is outside the capacity domain).
    Answer(QueryAnswer),
    /// The decoded statement is not supported: not well typed for the schema (`!wf_ordered`), decided by the verified
    /// entry before author code.
    ParamRefused,
    /// The bytes decode to no statement (`decode_spec(bytes)` is `None`), decided by the verified decoder.
    Malformed,
    /// The worker count is outside the engine's proved domain; decided before any call.
    Refused { workers: u32, domain: (u32, u32) },
}

impl EngineAnswer {
    /// Record form: the query answer's (`ok`, `sql_error`, `capacity`), or `param_refused`, `malformed`, `refused`.
    pub fn record(&self) -> Result<Value, AnswerError> {
        Ok(match self {
            Self::Answer(answer) => answer.record()?,
            Self::ParamRefused => json!({"status":"param_refused",
                "meaning":"the statement the bytes decode to is not supported: not well typed for the schema (wf_ordered), decided by the verified entry"}),
            Self::Malformed => json!({"status":"malformed","meaning":"the bytes decode to no statement (decode_spec is None), decided by the verified decoder"}),
            Self::Refused { workers, domain } => json!({"status":"refused","workers":workers,"domain":[domain.0, domain.1],
                "meaning":"the worker count is outside the engine's proved domain (the entry's Refused condition); decided before any call"}),
        })
    }

    /// The answer of an engine call's outcome; a status that answers nothing is an error.
    fn of(outcome: &CallOutcome) -> Result<Self, EngineServeError> {
        match outcome.status {
            CallStatus::Malformed => Ok(Self::Malformed),
            CallStatus::ParamRefused => Ok(Self::ParamRefused),
            CallStatus::Ok | CallStatus::SqlError | CallStatus::Capacity => Ok(Self::Answer(QueryAnswer::of(outcome).map_err(ServeError::from)?)),
            status => Err(EngineServeError::NoAnswer(status)),
        }
    }
}

/// Runs engine calls in worker children: one fresh child per served statement, evidence in
/// `<work>/engine-<workers>-<n>`; the child runs the statement `repetitions` times (the last call is served).
#[derive(Clone, Debug)]
pub struct EngineExecutor {
    /// The executable run as `<worker> worker REQUEST RESULT`.
    pub worker: PathBuf,
    pub work: PathBuf,
    pub timeout_seconds: u64,
    pub range_capacity: u64,
    pub repetitions: u32,
}

impl EngineExecutor {
    fn run(&self, library: &Path, uses: Vec<StorageUseInput>, access: PartAccess, ast: &[u8], workers: u32) -> Result<WorkerResult, WorkerError> {
        let request = WorkerRequest::for_engine_query(library, uses, access, &[ast.to_vec()], vec![workers], self.repetitions, self.range_capacity);
        let directory = (0..)
            .map(|ordinal| self.work.join(format!("engine-{workers}-{ordinal}")))
            .find(|directory| !directory.exists())
            .expect("an unbounded ordinal range always has an unused name");
        spawn(&self.worker, &directory, &request, self.timeout_seconds)
    }
}

/// A served engine statement: the answer, what it was computed by and over, and the statement's digest and echo.
#[derive(Clone, Debug)]
pub struct EngineServed {
    pub answer: EngineAnswer,
    /// The engine package, its version on the engine stream and whether it is the selected version.
    pub package: ContentId,
    pub version: u64,
    pub selected: bool,
    pub admission: ContentId,
    pub build: ContentId,
    /// SHA-256 (hex) and length of the AST bytes.
    pub ast_digest: String,
    pub ast_bytes: usize,
    pub echo: EchoVerdict,
    /// The engine's verified echo text (absent when no call ran).
    pub engine_echo: Option<String>,
    pub workers: u32,
    /// The asset of every storage use, in use order (empty when no call ran).
    pub storages: Vec<ServedStorage>,
    /// The served call (the child's last), with its per-use request counters; absent when no call ran.
    pub outcome: Option<CallOutcome>,
    pub storage_uses: Vec<MappedStorageUse>,
    pub process_io: Option<ProcessIoDelta>,
}

impl EngineServed {
    /// Record form: the answer, the engine version, the AST digest and echo verdict, the storage assets, and the served
    /// call's dispatch, wall time, request counters (extent requests, not device I/O) and process I/O.
    pub fn record(&self) -> Result<Value, AnswerError> {
        let mut record = json!({
            "route": "engine",
            "answer": self.answer.record()?,
            "engine": {"package": self.package, "version": self.version, "selected": self.selected, "admission": self.admission, "build": self.build},
            "ast": {"format": ENGINE_AST_FORMAT, "sha256": self.ast_digest, "bytes": self.ast_bytes},
            "echo": {"verdict": self.echo.name(), "engine": self.engine_echo},
            "workers": self.workers,
            "storage_assets": self.storages.iter().map(|s| json!({"storage": s.name, "package": s.package, "asset": s.asset})).collect::<Vec<_>>(),
        });
        if let Some(outcome) = &self.outcome {
            record["dispatch"] = json!({"spawned": outcome.dispatch.spawned, "joined": outcome.dispatch.joined});
            record["wall_ns"] = json!(outcome.usage.wall_ns);
            record["storage_requests"] = json!(outcome.storage_requests);
            record["storage_uses"] = json!(self.storage_uses);
            record["process_io"] = json!(self.process_io);
        }
        Ok(record)
    }
}

/// Why an engine statement was not served. `Display` texts start with the named reason.
#[derive(Debug)]
pub enum EngineServeError {
    /// Records, assets or the worker (including `no_storage_asset`).
    Serve(ServeError),
    /// The library has no admitted engine version (or none of the requested package).
    NoEngine,
    /// The engine's echo differs from the host's rendering of the bound document: the answer is withheld.
    EchoMismatch { ast_digest: String, host: String, engine: String },
    /// The call returned a status that answers nothing (a shim refusal, a worker failure or a sink failure).
    NoAnswer(CallStatus),
}

impl fmt::Display for EngineServeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Serve(error) => error.fmt(f),
            Self::NoEngine => f.write_str("no_engine_version: the library has no admitted engine version of this package (an engine library's versions are on its engine stream)"),
            Self::EchoMismatch { ast_digest, host, engine } => write!(
                f,
                "engine_echo_mismatch: the engine's verified echo of AST {ast_digest} differs from the host's rendering of the bound document, so the encoding is not validated and the answer is withheld; host {host:?}, engine {engine:?}"
            ),
            Self::NoAnswer(status) => write!(f, "engine_call_answered_nothing: status {status:?} (a shim refusal, worker failure or sink failure; never a result)"),
        }
    }
}

impl std::error::Error for EngineServeError {}

impl From<ServeError> for EngineServeError {
    fn from(error: ServeError) -> Self {
        Self::Serve(error)
    }
}

impl From<WorkerError> for EngineServeError {
    fn from(error: WorkerError) -> Self {
        Self::Serve(ServeError::Worker(error))
    }
}

/// Serve `statement` from the engine version `engine` at `workers` workers over the assets of its storage uses for
/// `capture` (mapped with `access`), through `executor` (see the module documentation).
pub fn serve_engine(
    store: &ObjectStore,
    engine: &ResolvedEngine,
    statement: &EngineStatement,
    capture: &CurrentCapture,
    access: PartAccess,
    executor: &EngineExecutor,
    workers: u32,
) -> Result<EngineServed, EngineServeError> {
    let package = &engine.version.package;
    let bytes = statement.bytes();
    let mut served = EngineServed {
        answer: EngineAnswer::Refused { workers, domain: package.workers },
        package: engine.version.package_id,
        version: engine.version.version,
        selected: engine.selected,
        admission: engine.version.admission_id,
        build: package.build,
        ast_digest: ast_digest(bytes),
        ast_bytes: bytes.len(),
        echo: EchoVerdict::NotRun,
        engine_echo: None,
        workers,
        storages: vec![],
        outcome: None,
        storage_uses: vec![],
        process_io: None,
    };
    if !(package.workers.0..=package.workers.1).contains(&workers) {
        return Ok(served);
    }
    let uses = package.storage_uses.iter().zip(&engine.storages).map(|(u, p)| (u.name.as_str(), u.package, p));
    let assets = resolve_storage_assets(store, uses, capture).map_err(ServeError::from)?;
    let inputs: Vec<StorageUseInput> = assets.iter().map(|a| StorageUseInput { name: a.name.clone(), parts_directory: a.directory.clone() }).collect();
    let library = library_path(store, &engine.build).map_err(ServeError::from)?;
    let result = executor.run(&library, inputs, access, bytes, workers)?;
    let engine_echo = result.echoes.first().cloned().ok_or(ServeError::NoCall)?;
    served.echo = match statement.host_echo() {
        Some(host) if host == engine_echo => EchoVerdict::Equal,
        Some(host) => return Err(EngineServeError::EchoMismatch { ast_digest: served.ast_digest, host, engine: engine_echo }),
        None => EchoVerdict::NoHostDocument,
    };
    let call = result.observations.last().cloned().ok_or(ServeError::NoCall)?;
    served.answer = EngineAnswer::of(&call.outcome)?;
    served.engine_echo = Some(engine_echo);
    served.storages = assets.iter().map(|a| ServedStorage { name: a.name.clone(), package: a.package, asset: a.asset_id }).collect();
    served.outcome = Some(call.outcome);
    served.storage_uses = result.storage_uses;
    served.process_io = call.process_io;
    Ok(served)
}
