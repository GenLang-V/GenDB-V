//! The isolated worker process: one short-lived child runs one compiled library (a v3 candidate, or a v4 storage or
//! query library) at the requested argument bindings and worker counts, writes one JSON result and exits.
//!
//! - [`WorkerRequest`] / [`WorkerResult`]: the request and result files (JSON forms of the earlier version's v3 runs, except the build
//!   identity);
//! - [`run_child`] / [`worker_main`]: the child side, the body of `gendb worker REQUEST RESULT`;
//! - [`spawn`]: the parent side, which runs `<executable> worker REQUEST RESULT` under the caller's timeout and reports
//!   a child that ended without a result as [`WorkerError::ChildFailed`] with its actual exit status and stderr.
//!
//! Why a separate process: the trusted shim hands verified code `&'static` slices of host memory. The child keeps
//! the library, every input column, every mapped part (of every storage use) and every argument list until the OS ends it (they are
//! leaked on purpose and the library is never unloaded), on every return path, even if a library left a thread
//! running. That retention, not a proof, makes those slices honest; it is scoped to one child. A crash or abort is
//! contained in the child and is never a result. Timings and CPU usage are descriptive only. No query identity
//! appears here.
//!
//! A build job runs the representation builder once over source columns (projected from a prepared archive, table by
//! table, or tiny inline fixture columns) and stores its parts; it reads no argument, so one asset serves every
//! binding. A query job reads only stored parts and runs every binding (outer loop) at every worker count, each
//! `repetitions` times. Arguments are passed exactly as requested and echoed; the verified entry decides the
//! parameter domain (`ParamRefused`). Saved ABI v1/v2 requests run only in the earlier GenDB version.
//!
//! v4 jobs: a storage build runs a storage library's builder the same way and stores little-endian (format 2) parts; a
//! storage query maps the parts directory of every storage use (lazily, with the request's explicit kernel advice),
//! passes one part list per use in the declared use order, and records each call's verified request counters per use
//! and its process I/O ([`ProcessIoDelta`], descriptive and environment sensitive).
//!
//! Engine jobs ([`WorkerJob::EngineQuery`]): the same storage-use mapping, then one engine library (v4 records plus the
//! engine entries) called once per statement (AST bytes, retained like the parts) at every worker count and
//! repetition, after the verified echo of every statement (recorded in [`WorkerResult::echoes`], untimed).
//!
//! Limited engine jobs ([`CallLimits`]) run every call under a watchdog thread in the
//! child (`watchdog`): a call over its wall-time limit or over the anonymous-memory limit ends the child with the
//! result so far and [`Unfinished`] naming that call; the parent reads it, or a limited child that died by a signal,
//! as an unfinished result. Profile jobs ([`SamplingRequest`]) sample every call's instruction pointer
//! (`sampler`); serving never sets either.
//!
//! Stored answers (`stored_answer`): an engine job whose answers the caller does not compare carries an
//! [`AnswerBound`], and the child stores each rows answer over it as its [`StoredAnswer`] summary (row count, the
//! result wire's size and SHA-256) and its first rows; the rest of the answer is not stored. A caller that compared the
//! full answers it read may store the result the same way afterwards ([`store_bounded_result`]). Serving never bounds
//! an answer.

mod child;
mod error;
mod inputs;
mod parent;
mod process_io;
mod protocol;
mod sampler;
mod stored_answer;
#[cfg(test)]
mod tests;
mod watchdog;

pub use child::{run_child, worker_main};
pub use error::WorkerError;
pub use parent::{ChildFailure, WORKER_SUBCOMMAND, spawn, store_bounded_result};
pub use process_io::{ProcessIoDelta, measure_process_io, parse_read_bytes};
pub use protocol::{
    CallLimits, CallObservation, CallSamples, InlineColumn, InlineElem, MEMORY_POLL_INTERVAL_MS, MappedStorageUse, RequestAbi, RunPurpose,
    SampledObject, SamplingRequest, StoppedCall, StorageUseInput, TableColumns, UNFINISHED_EXIT_CODE, Unfinished, UnfinishedReason,
    WorkerInput, WorkerJob, WorkerRequest, WorkerResult, decode_hex,
};
pub use stored_answer::{AnswerBound, StoredAnswer, bounded_observation};

/// Trusted items of the worker, `(id, statement)`, for the TCB list of admitted packages (ids unchanged from the earlier GenDB version).
pub const TRUSTED_ITEMS: [(&str, &str); 3] = [
    (
        "child_worker_v3",
        "gendb_runtime::worker: keeps library, columns, parts and arguments mapped until process exit; decodes the \
         rows wire with the SQLSpec result codec (gendb_sqlspec::codec)",
    ),
    (
        "canonical_columns",
        "the host delivers exactly the columns named by the source declaration, table by table, from the prepared \
         archive (gendb_storage::io::SourceColumns::map_archive + project)",
    ),
    (
        "stored_asset_at_ffi",
        "the stored parts are the builder's output for the current source versions (asset key: every source table's \
         metadata version, fields and row count) and are read back unchanged",
    ),
];

/// Host items of limited and profiled engine jobs, `(id, statement)`, for the TCB lists of records whose timings or
/// profiles they produced. They decide whether a timing cell finished and what a profile shows; they never touch an
/// answer, and nothing they observe (wall time, memory, samples) is part of the claim.
pub const TRUSTED_ITEMS_ENGINE_LIMITS: [(&str, &str); 2] = [
    (
        "engine_call_watchdog",
        "gendb_runtime::worker (limited engine jobs): a watchdog thread in the child stops a call still running at the \
         wall-time limit, or whose process anonymous resident memory (RssAnon of /proc/self/status, polled every 100 ms) \
         exceeds the memory limit, writing the earlier calls' observations and the stopped call, then ending the child \
         (_exit); the parent reads that result, or a limited child that died by a signal, as unfinished",
    ),
    (
        "engine_profile_sampler",
        "gendb_runtime::worker (engine profile jobs only, never serving): a SIGPROF interval timer over process CPU time \
         records the interrupted instruction pointer of each sample (no stack walk), placed in the loaded objects by \
         dl_iterate_phdr; descriptive only",
    ),
];

/// Trusted items of the worker for v4 storage builds and storage-use queries, `(id, statement)`. The storage source
/// binding and the storage round trip of the query claim are premises of the fixed entries (composed with the
/// records that select the assets).
pub const TRUSTED_ITEMS_V4: [(&str, &str); 1] = [(
    "child_worker_v4",
    "gendb_runtime::worker (v4 jobs): keeps the library, the build's columns, every storage use's part mappings and \
     every argument list mapped until process exit; passes one part list per storage use in the request's use order; \
     decodes the rows wire with the SQLSpec result codec; request counters and process read_bytes are recorded as \
     descriptive evidence only",
)];

