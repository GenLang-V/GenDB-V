//! Runtime of admitted Verus packages: ABI v3 and v4 loading and calls, the isolated worker process, serving (including
//! template bindings) and the runtime build identity. Trusted: ABI, loader and OS; one verified runtime path (no
//! native MLIR/JIT fallback; saved ABI v1/v2 packages run only in the earlier GenDB version).
//!
//! - [`abi`]: ABI host (library loading, argument and storage-use descriptors, call status and result wire, request
//!   counters, mapped parts, parts written straight to files) and the Verus framework files `verus/gendb_{abi,shim}.rs`
//!   (v3 candidates) and `verus/shim_v4/` (v4 storage and query crates);
//! - [`answer`]: the answer of a query call (rows, exact SQL error, capacity, parameter refusal) and its record form;
//! - [`worker`]: the child process that runs one library (`gendb worker`, [`worker::worker_main`]) and its parent side
//!   ([`worker::spawn`]);
//! - [`serve`]: resolving an admitted package by statement key and its asset by current source versions, and serving a
//!   binding through a worker child ([`serve::serve`]);
//! - [`identity`]: the build identity every worker request carries;
//! - [`process_stop`]: the user's stop of a controller process (SIGTERM/SIGINT): every process tree it started is
//!   stopped and waited for, and the stop recorded, before the controller ends (host code outside every claim).
//!
//! `build.rs` exports the compiler settings of this build (`GENDB_BUILD_*`) for the runtime identity.

pub mod abi;
pub mod answer;
pub mod identity;
pub mod process_stop;
pub mod serve;
pub mod worker;

/// Every trusted host item of the runtime, `(id, statement)`, for the TCB list of admitted packages: the ABI boundary,
/// the worker and serving. Callers add the toolchain, semantics and entry items.
pub fn trusted_items() -> Vec<(&'static str, &'static str)> {
    abi::TRUSTED_ITEMS.into_iter().chain(worker::TRUSTED_ITEMS).chain(serve::TRUSTED_ITEMS).collect()
}

/// Every trusted host item of the runtime's v4 path (storage builds and storage-use queries), `(id, statement)`: the
/// v4 ABI boundary and the worker. The owners of v4 argument conversion, package/asset lookup and the entry premises
/// add theirs.
pub fn trusted_items_v4() -> Vec<(&'static str, &'static str)> {
    abi::TRUSTED_ITEMS_V4.into_iter().chain(worker::TRUSTED_ITEMS_V4).collect()
}
