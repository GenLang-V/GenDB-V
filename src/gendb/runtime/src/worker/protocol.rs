//! Request and result files of one worker run. v3 JSON forms are those of the earlier version's `quality_gate::verus_worker` v3 runs
//! (`VerusRunRequestV3`, `VerusRunResultV3`, ...); only the build identity has the new, single-field form. v4 runs
//! (`"abi": "v4"`) are storage builds and storage-use queries; their extra result fields are absent from v3 results.
//!
//! Engine jobs may carry per-call limits (`call_limit_ns`,
//! `anon_memory_limit_bytes`), profile sampling (`sampling`) and a stored-answer bound (`answer_bound`, `super::stored_answer`).
//! Every such field is absent from the JSON when unset, so requests and results without them keep their earlier form
//! byte for byte. A call stopped at a limit ends the child with the result so far ([`WorkerResult::unfinished`],
//! [`Unfinished`]); see `super::watchdog` and `super::sampler`.

use super::parent::ChildFailure;
use super::process_io::ProcessIoDelta;
use super::stored_answer::{AnswerBound, StoredAnswer};
use crate::abi::{CallOutcome, StatementArgument};
use crate::answer::SqlErrorAnswer;
use crate::identity::WorkerBuildIdentity;
use gendb_storage::io::{PartAccess, PartsManifest};
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

/// Why the library is run. `AbiFixtureUnproved` marks framework ABI fixtures whose entry is not a checked query
/// theorem; their evidence can never support publication.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RunPurpose {
    Candidate,
    AbiFixtureUnproved,
}

/// Element type of an inline fixture column.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum InlineElem {
    I32,
    I64,
    I128,
    /// Each value is the UTF-8 text itself (canonical Utf8 column, offsets from 0).
    Utf8,
}

/// A tiny inline canonical column (fixtures and boundary cases only).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct InlineColumn {
    pub elem: InlineElem,
    /// Decimal text of each value (an i128 does not fit a JSON number), or the text itself for `Utf8`. A NULL row
    /// holds a placeholder value (`0`, or empty text), which its validity marks as NULL.
    pub values: Vec<String>,
    /// A nullable column: one byte per row, 1 valid, 0 NULL (delivered as the column's validity buffer). Absent: a NOT
    /// NULL column.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub validity: Option<Vec<u8>>,
}

/// One source table of a [`WorkerInput::Tables`] input: its original column ordinals (ascending, the source
/// declaration's field order of that table).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TableColumns {
    pub table: String,
    pub ordinals: Vec<usize>,
}

/// Source columns of a build job.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum WorkerInput {
    /// No source column (every query job: it reads only stored parts).
    None,
    /// A prepared archive projected to the distinct source tables in declaration table order, each to its original
    /// ordinals. The ABI column list is table 0's columns, then table 1's, ...; every table keeps its own row count. A
    /// table read by several FROM occurrences (a self-join) is listed once; naming a table twice is refused.
    Tables { path: PathBuf, tables: Vec<TableColumns> },
    /// Inline fixture columns in ABI order (each column carries its own values, so tables may differ in length).
    Inline { columns: Vec<InlineColumn> },
    /// A storage built from admitted storages: the stored parts of its sources, in the builder's use order (a v4
    /// storage build of a derived storage library). `extends`: the source whose part files are linked unchanged as the
    /// first parts of the new directory, before the builder's parts.
    StoredParts {
        uses: Vec<StorageUseInput>,
        #[serde(default, skip_serializing_if = "Option::is_none")]
        extends: Option<usize>,
    },
}

/// One storage use of a v4 query job: the storage's name (for records) and its stored parts directory.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StorageUseInput {
    pub name: String,
    pub parts_directory: PathBuf,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "snake_case")]
pub enum WorkerJob {
    /// v3: run the builder once and store its parts in a new directory (format 1).
    Build { output_directory: PathBuf },
    /// v3: run the query entry over stored parts (none: a query without parts).
    Query { parts_directory: Option<PathBuf> },
    /// v4: run a storage crate's builder once and store its parts in a new directory (format 2, little-endian).
    StorageBuild { output_directory: PathBuf },
    /// v4: run a query crate's entry over the parts of its storage uses, in the query's declared use order, each
    /// directory mapped with the kernel advice `access`.
    StorageQuery { storage_uses: Vec<StorageUseInput>, access: PartAccess },
    /// Engine crates (v4 records, engine entries): first the verified echo of every statement (untimed, recorded in
    /// `WorkerResult::echoes`), then the engine over the parts of its storage uses (declared use order, mapped with
    /// `access`) for every statement (outer loop, `CallObservation::binding` is its index), worker count and repetition.
    /// `asts`: each statement's AST bytes (`gendb_frontend::engine_encode`) as lowercase hex.
    EngineQuery { storage_uses: Vec<StorageUseInput>, access: PartAccess, asts: Vec<String> },
}

impl WorkerJob {
    /// The ABI version the job belongs to.
    pub fn abi(&self) -> RequestAbi {
        match self {
            Self::Build { .. } | Self::Query { .. } => RequestAbi::V3,
            Self::StorageBuild { .. } | Self::StorageQuery { .. } | Self::EngineQuery { .. } => RequestAbi::V4,
        }
    }
}

/// ABI marker of a request/result (`"abi": "v3"` or `"v4"`). Requests without it (ABI v1) or with `"v2"` are saved
/// requests of the earlier GenDB version.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RequestAbi {
    V3,
    V4,
}

/// Request of one child run. Rules (checked by the child before it opens anything): the ABI marker is the job's; at
/// least one worker count and one repetition; a build job (either version) runs once, at one worker count, with no
/// binding; a query job (either version) has input `None` and at least one binding (`[[]]` for a statement without
/// parameters); storage-use names are non-empty and distinct.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WorkerRequest {
    pub abi: RequestAbi,
    pub build: WorkerBuildIdentity,
    pub library: PathBuf,
    pub purpose: RunPurpose,
    pub input: WorkerInput,
    pub job: WorkerJob,
    /// Argument lists, each one argument per free parameter in slot order (query job; empty for a build).
    pub bindings: Vec<Vec<StatementArgument>>,
    /// Worker counts, run in this order. A build job takes exactly one.
    pub workers: Vec<u32>,
    /// Sequential calls per binding and worker count (for example 1 warm + 3 hot = 4).
    pub repetitions: u32,
    /// Dispatch ranges recorded per call (the caller's declared evidence capacity).
    pub range_capacity: u64,
    /// Engine jobs only: the wall-time limit of each call, in nanoseconds. A call still running at the limit is
    /// stopped by the child's watchdog ([`Unfinished::OverTimeLimit`]).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub call_limit_ns: Option<u64>,
    /// Engine jobs only: the limit of the child's anonymous resident memory during a call, in bytes, polled every
    /// [`MEMORY_POLL_INTERVAL_MS`] ms ([`Unfinished::OverMemoryLimit`]).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub anon_memory_limit_bytes: Option<u64>,
    /// Engine profile jobs only: sample the instruction pointer of every call ([`CallObservation::samples`]). Serving
    /// never sets it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub sampling: Option<SamplingRequest>,
    /// Engine jobs only: the caller compares no rows of this job, so the child stores each rows answer over this bound
    /// as its summary and first rows ([`CallObservation::stored_answer`]). Absent: every answer in full.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub answer_bound: Option<AnswerBound>,
}

/// The per-call limits of an engine job, both set together ([`WorkerRequest::with_call_limits`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CallLimits {
    /// Wall time of each call, nanoseconds.
    pub call_limit_ns: u64,
    /// Anonymous resident memory of the child during a call, bytes.
    pub anon_memory_limit_bytes: u64,
}

impl CallLimits {
    /// The general-engine run's framework safety limits, the same for every scale and version: 60 s per call (the
    /// general line's setting) and 144 GiB of anonymous memory, the memory of the Umbra container in
    /// the saved SF100 baselines.
    pub const GENERAL_ENGINE: CallLimits = CallLimits { call_limit_ns: 60_000_000_000, anon_memory_limit_bytes: 144 << 30 };
}

/// How often the watchdog polls the child's anonymous resident memory while a call runs (also the granularity of
/// [`CallObservation::peak_anon_bytes`]).
pub const MEMORY_POLL_INTERVAL_MS: u64 = 100;

/// Exit status of a child whose watchdog stopped a call at a limit, after writing the result so far (0 = result
/// written, 1 = refusal, 2 = usage error; [`super::worker_main`]).
pub const UNFINISHED_EXIT_CODE: u8 = 3;

/// Profile sampling of an engine job: a `SIGPROF` interval timer over the process's CPU time
/// (`setitimer(ITIMER_PROF)`), armed for each call.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SamplingRequest {
    /// Process CPU time between samples, microseconds (the kernel checks CPU timers at its tick, so the effective
    /// interval can be longer).
    pub interval_us: u32,
}

/// Why an engine call did not finish.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum UnfinishedReason {
    OverTimeLimit,
    OverMemoryLimit,
    ChildFailure,
}

/// The call of an engine job that did not finish (the observations before it are kept in the result).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "reason", rename_all = "snake_case")]
pub enum Unfinished {
    /// The watchdog stopped the call at the wall-time limit.
    OverTimeLimit(StoppedCall),
    /// The watchdog stopped the call at the anonymous-memory limit.
    OverMemoryLimit(StoppedCall),
    /// A limited child ended by a signal without writing a result (a crash, an abort, or a kill such as the kernel's
    /// out-of-memory killer): which call it was in and the earlier observations are unknown.
    ChildFailure(ChildFailure),
}

impl Unfinished {
    pub fn reason(&self) -> UnfinishedReason {
        match self {
            Self::OverTimeLimit(_) => UnfinishedReason::OverTimeLimit,
            Self::OverMemoryLimit(_) => UnfinishedReason::OverMemoryLimit,
            Self::ChildFailure(_) => UnfinishedReason::ChildFailure,
        }
    }

    /// The stopped call (absent for a child failure).
    pub fn stopped(&self) -> Option<&StoppedCall> {
        match self {
            Self::OverTimeLimit(call) | Self::OverMemoryLimit(call) => Some(call),
            Self::ChildFailure(_) => None,
        }
    }
}

/// A call the watchdog stopped, as it saw it when it stopped the child.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StoppedCall {
    /// The statement's index in the job's ASTs, the worker count and the repetition of the call.
    pub statement: usize,
    pub workers: u32,
    pub repetition: u32,
    /// Wall time from arming the watchdog (just before the call) to the stop, nanoseconds.
    pub elapsed_ns: u64,
    /// The limit that was reached (nanoseconds or bytes, by the reason).
    pub limit: u64,
    /// Anonymous resident memory at the last poll, and the largest seen during the call (bytes; absent when
    /// `/proc/self/status` could not be read).
    pub anon_bytes: Option<u64>,
    pub peak_anon_bytes: Option<u64>,
    /// Sampling armed: the samples of the call up to the stop.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub samples: Option<CallSamples>,
}

/// The instruction-pointer samples of one call, by loaded object (descriptive; a profile, never a measurement).
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CallSamples {
    pub interval_us: u32,
    /// Samples recorded during the call.
    pub taken: u64,
    /// Samples lost because the sample buffer was full.
    pub dropped: u64,
    /// Samples whose address lies in no loaded object.
    pub unmapped: u64,
    pub objects: Vec<SampledObject>,
}

/// The samples that fell in one loaded object: its path as the loader names it (the executable's own path for the main
/// program) and `(address, count)` pairs in ascending address order. An address is relative to the object's load bias,
/// i.e. an ELF virtual address of that file, the coordinates of its symbol table.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SampledObject {
    pub path: String,
    pub addresses: Vec<(u64, u64)>,
}

impl WorkerRequest {
    /// A build job of this build: run the builder of `library` once over `input` at `workers` and store its parts in
    /// the new directory `output_directory`.
    pub fn for_build(
        library: &Path,
        input: WorkerInput,
        output_directory: &Path,
        workers: u32,
        range_capacity: u64,
    ) -> Self {
        Self {
            abi: RequestAbi::V3,
            build: WorkerBuildIdentity::current(),
            library: library.to_owned(),
            purpose: RunPurpose::Candidate,
            input,
            job: WorkerJob::Build { output_directory: output_directory.to_owned() },
            bindings: vec![],
            workers: vec![workers],
            repetitions: 1,
            range_capacity,
            call_limit_ns: None,
            anon_memory_limit_bytes: None,
            sampling: None,
            answer_bound: None,
        }
    }

    /// A query job of this build: run the query entry of `library` over the stored parts `parts_directory` at every
    /// binding and worker count, `repetitions` times each.
    pub fn for_query(
        library: &Path,
        parts_directory: Option<&Path>,
        bindings: Vec<Vec<StatementArgument>>,
        workers: Vec<u32>,
        repetitions: u32,
        range_capacity: u64,
    ) -> Self {
        Self {
            abi: RequestAbi::V3,
            build: WorkerBuildIdentity::current(),
            library: library.to_owned(),
            purpose: RunPurpose::Candidate,
            input: WorkerInput::None,
            job: WorkerJob::Query { parts_directory: parts_directory.map(Path::to_owned) },
            bindings,
            workers,
            repetitions,
            range_capacity,
            call_limit_ns: None,
            anon_memory_limit_bytes: None,
            sampling: None,
            answer_bound: None,
        }
    }

    /// A v4 storage build job of this build: run the storage builder of `library` once over `input` at `workers` and
    /// store its parts (format 2) in the new directory `output_directory`.
    pub fn for_storage_build(
        library: &Path,
        input: WorkerInput,
        output_directory: &Path,
        workers: u32,
        range_capacity: u64,
    ) -> Self {
        Self {
            abi: RequestAbi::V4,
            job: WorkerJob::StorageBuild { output_directory: output_directory.to_owned() },
            ..Self::for_build(library, input, output_directory, workers, range_capacity)
        }
    }

    /// A v4 query job of this build: run the query entry of `library` over `storage_uses` (declared use order, mapped
    /// with `access`) at every binding and worker count, `repetitions` times each.
    pub fn for_storage_query(
        library: &Path,
        storage_uses: Vec<StorageUseInput>,
        access: PartAccess,
        bindings: Vec<Vec<StatementArgument>>,
        workers: Vec<u32>,
        repetitions: u32,
        range_capacity: u64,
    ) -> Self {
        Self {
            abi: RequestAbi::V4,
            job: WorkerJob::StorageQuery { storage_uses, access },
            ..Self::for_query(library, None, bindings, workers, repetitions, range_capacity)
        }
    }

    /// An engine job of this build: the verified echo of every statement `asts` (AST bytes), then the engine of
    /// `library` over `storage_uses` (declared use order, mapped with `access`) for every statement, worker count and
    /// repetition.
    pub fn for_engine_query(
        library: &Path,
        storage_uses: Vec<StorageUseInput>,
        access: PartAccess,
        asts: &[Vec<u8>],
        workers: Vec<u32>,
        repetitions: u32,
        range_capacity: u64,
    ) -> Self {
        let asts = asts.iter().map(|ast| ast.iter().map(|b| format!("{b:02x}")).collect()).collect();
        Self {
            abi: RequestAbi::V4,
            job: WorkerJob::EngineQuery { storage_uses, access, asts },
            bindings: vec![],
            ..Self::for_query(library, None, vec![], workers, repetitions, range_capacity)
        }
    }

    /// This engine job with the per-call limits `limits` (the child's watchdog enforces them call by call).
    pub fn with_call_limits(self, limits: CallLimits) -> Self {
        Self { call_limit_ns: Some(limits.call_limit_ns), anon_memory_limit_bytes: Some(limits.anon_memory_limit_bytes), ..self }
    }

    /// This engine job with profile sampling of every call (profile jobs only; serving never samples).
    pub fn with_sampling(self, sampling: SamplingRequest) -> Self {
        Self { sampling: Some(sampling), ..self }
    }

    /// This engine job with every rows answer over `bound` stored as its summary and first rows (a job whose answers
    /// the caller does not compare; serving never bounds an answer).
    pub fn with_answer_bound(self, bound: AnswerBound) -> Self {
        Self { answer_bound: Some(bound), ..self }
    }

    /// Whether the request carries a per-call limit (its child then runs a watchdog, and the parent reads a stopped or
    /// failed child as an unfinished result).
    pub fn is_limited(&self) -> bool {
        self.call_limit_ns.is_some() || self.anon_memory_limit_bytes.is_some()
    }

    /// The request rules above; the v3 reason texts are the earlier version's refusals. Limits and sampling belong to engine jobs
    /// only, and every limit and interval is positive.
    pub(super) fn check_shape(&self) -> Result<(), &'static str> {
        if self.abi != self.job.abi() {
            return Err("the request's ABI marker differs from its job's ABI version");
        }
        let engine = matches!(self.job, WorkerJob::EngineQuery { .. });
        if !engine && (self.is_limited() || self.sampling.is_some()) {
            return Err("call limits and profile sampling belong to engine jobs only");
        }
        if !engine && self.answer_bound.is_some() {
            return Err("a stored-answer bound belongs to engine jobs only");
        }
        if self.call_limit_ns == Some(0) || self.anon_memory_limit_bytes == Some(0) || self.sampling.is_some_and(|s| s.interval_us == 0) {
            return Err("a call limit, memory limit or sampling interval must be positive");
        }
        if self.workers.is_empty() || self.repetitions == 0 {
            return Err("verus run requires worker counts and repetitions");
        }
        let build = matches!(self.job, WorkerJob::Build { .. } | WorkerJob::StorageBuild { .. });
        if build && (self.workers.len() != 1 || self.repetitions != 1 || !self.bindings.is_empty()) {
            return Err("a verus build job runs once at one worker count and takes no argument binding");
        }
        if let WorkerJob::EngineQuery { asts, .. } = &self.job {
            if asts.is_empty() || !self.bindings.is_empty() {
                return Err("an engine job names at least one statement (AST bytes) and no argument binding");
            }
            if asts.iter().any(|hex| decode_hex(hex).is_none()) {
                return Err("an engine job's AST bytes must be lowercase hex");
            }
        } else if !build && self.bindings.is_empty() {
            return Err("a verus query job needs at least one argument binding ([[]] for a statement without parameters)");
        }
        if matches!(self.input, WorkerInput::StoredParts { .. }) && !matches!(self.job, WorkerJob::StorageBuild { .. }) {
            return Err("stored-part inputs belong to a v4 storage build of a derived storage");
        }
        if let WorkerInput::StoredParts { uses, extends } = &self.input {
            let mut names = std::collections::BTreeSet::new();
            if uses.is_empty() || uses.iter().any(|u| u.name.is_empty() || !names.insert(u.name.as_str())) || extends.is_some_and(|k| k >= uses.len()) {
                return Err("a derived storage build names distinct, non-empty sources and extends one of them");
            }
        }
        if !build && self.input != WorkerInput::None {
            return Err("a verus query job reads only stored parts; its input must be none");
        }
        if let WorkerJob::StorageQuery { storage_uses, .. } | WorkerJob::EngineQuery { storage_uses, .. } = &self.job {
            let mut names = std::collections::BTreeSet::new();
            if storage_uses.iter().any(|u| u.name.is_empty() || !names.insert(u.name.as_str())) {
                return Err("storage-use names must be non-empty and distinct");
            }
        }
        Ok(())
    }
}

/// Result of one child run.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct WorkerResult {
    pub abi: RequestAbi,
    pub purpose: RunPurpose,
    pub library: PathBuf,
    pub input_columns: usize,
    /// Row count of every input column in ABI order (tables may differ).
    pub column_rows: Vec<u64>,
    /// The argument lists exactly as passed to the library (echo of the request).
    pub bindings: Vec<Vec<StatementArgument>>,
    pub observations: Vec<CallObservation>,
    /// Build job only: the stored parts (absent when the build did not return `Ok`).
    pub parts: Option<PartsManifest>,
    /// v4 query job only: the stored bytes and part count of every storage use, in use order (from each manifest).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub storage_uses: Vec<MappedStorageUse>,
    /// Engine job only: the verified echo text of every statement, in the request's order (the evaluator's echo
    /// grammar; the host compares it with its own rendering of the document it encoded).
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub echoes: Vec<String>,
    /// Limited engine job only: the call that did not finish; `observations` are then the calls before it (none for a
    /// child failure). Absent when every call finished.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub unfinished: Option<Unfinished>,
}

/// The bytes of lowercase hex text (two digits per byte), or `None`.
pub fn decode_hex(text: &str) -> Option<Vec<u8>> {
    if text.len() % 2 != 0 || !text.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)) {
        return None;
    }
    (0..text.len()).step_by(2).map(|i| u8::from_str_radix(&text[i..i + 2], 16).ok()).collect()
}

/// A storage use as mapped by a v4 query job.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct MappedStorageUse {
    pub name: String,
    pub parts: u64,
    pub storage_bytes: u64,
}

/// One call. `binding` indexes the request's bindings (absent for a build). `rows` is the answer's rows as PostgreSQL
/// output text (NULL as null), present for `Ok`; `sql_error` is present for `SqlError`; the exact wire stays in
/// `outcome.result_wire` (decode with [`crate::answer::QueryAnswer::of`]). `process_io` (v4 calls only, absent when
/// `/proc/self/io` is unavailable): the process's I/O counters over the call ([`ProcessIoDelta`]; environment
/// sensitive, descriptive only). `peak_anon_bytes` (limited engine jobs): the largest anonymous resident memory the
/// watchdog saw during the call (polled every [`MEMORY_POLL_INTERVAL_MS`] ms, so a sampled peak). `samples` (profile
/// jobs): the call's instruction-pointer samples. `stored_answer` (an answer stored over its bound,
/// `super::stored_answer`): `rows` then holds only the answer's first rows and `outcome.result_wire` is absent.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CallObservation {
    pub binding: Option<usize>,
    pub workers: u32,
    pub repetition: u32,
    pub outcome: CallOutcome,
    pub rows: Option<Vec<Vec<serde_json::Value>>>,
    pub sql_error: Option<SqlErrorAnswer>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub process_io: Option<ProcessIoDelta>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub peak_anon_bytes: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub samples: Option<CallSamples>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub stored_answer: Option<StoredAnswer>,
}
