//! Query authoring on the storage-aware verified path: the per-statement state of an author session and the query
//! role. The statement, preflight, references, candidate checks and qualification themselves are framework decisions
//! in `gendb_verification::admission`; this module sequences them for the controller and the author's local jobs.
//!
//! - [`QuerySession`] (`session`): opened once per statement before the first author call (inputs, preflight,
//!   prepared-data references), then only read, by the statement's query role and by the workload storage role.
//! - `evaluation`: [`QuerySession::evaluate_submission`] and [`QuerySession::trial`] (tests of a compiled query
//!   library over its storage assets); `closing`: [`QuerySession::close`] (serving again from the library and, for
//!   the execution-time objective, the final measurement).
//! - [`role`]: [`QueryAuthorRole`], the `SynthesisRole` and `LocalJobs` of one query author session;
//! - [`candidate`]: the author's manifest (`verus-query.json`) and the freeze of a submission over its storage uses;
//!   [`compile`]: the Verus runs of a frozen crate of either kind and its declared items; [`source_items`]: lexical
//!   reading of Verus sources (catalogs, records);
//! - `import`: the copy of another session's frozen candidate for a reselection without an author; [`incumbent`]: the
//!   admitted candidate of an earlier session written into the workspace of a session that continues from it;
//! - [`library`]: the admitted library code as the author sees it; [`assets`]: free-space facts and guard;
//!   [`host_locks`]: the host activity/timing leases; [`serving`]: serving an admitted statement without synthesis.

pub mod assets;
pub mod candidate;
mod closing;
pub mod compile;
pub mod evaluation;
pub mod host_locks;
mod import;
pub mod incumbent;
pub mod library;
pub mod role;
pub mod serving;
mod session;
pub mod source_items;

pub use closing::SERVED_NOT_ALLOWED;
pub use evaluation::TrialKind;
pub use role::{QueryAuthorRole, QueryRoleConfig};
pub use session::{PreflightFrom, QuerySession};
