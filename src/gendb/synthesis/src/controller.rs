//! Public controller of the verified path: the workload run (request, data preparation, one author session per query,
//! summary), the generic author-session state machine, its ledger of calls, receipts and submissions, the user's
//! iteration/money controls, and the retained role service.
//!
//! Migrated from the earlier version's `program-synthesis/src/{integrated_run,integrated_session,integrated_budget,
//! integrated_evaluator}.rs` (verified path only; the native path and prior-run context stayed in that version).
//!
//! Module map:
//! - [`benchmark_inputs`]: the user's visible benchmark bindings and runtime targets written into a request;
//! - [`workload_run`]: the public entries `synthesize`, `preflight` (no author) and `serve`, phase by phase;
//! - [`request`]: the user's workload request; [`hardware`]: requested worker counts and the observed host;
//! - [`run`]: one author session, phase by phase ([`run::run`]), and why it stopped ([`run::StopReason`]);
//! - [`reselect`]: a session without an author that recovers an evaluated candidate of a closed session;
//! - [`import`]: a session without an author that admits a published package (`gendb import`);
//! - [`role`]: the hooks a role implements ([`role::SynthesisRole`] stages, [`role::RolePolicy`] decisions);
//! - [`author`]: the provider port ([`author::AuthorTransport`]) and the submission contract;
//! - [`provider_wait`]: what follows a call the provider ended (wait for its reset, fresh session, or refusal);
//! - [`ledger`]: calls, receipts, counted usage, guards and trials; [`limits`]: the user's controls and exact dollars;
//! - [`trajectory`]: local-job counts, unchanged-resubmission detection and summary counters;
//! - [`schedule`]: several sessions with bounded concurrency; [`session`]: one retained role owner thread shared by
//!   the controller and the author's local tools;
//! - [`layout`], [`records`]: run directory file names and durable JSON writes.
//!
//! Trust: outside the TCB. The controller records what the provider and the role report; it cannot change fixed
//! obligations, and no author claim is authority for usage or evaluation.

pub mod author;
pub mod benchmark_inputs;
pub mod crash_dumps;
pub mod hardware;
pub mod import;
pub mod layout;
pub mod ledger;
pub mod limits;
pub mod provider_wait;
pub mod records;
pub mod request;
pub mod reselect;
pub mod role;
pub mod run;
pub mod schedule;
pub mod session;
pub mod trajectory;
pub mod workload_run;

#[cfg(test)]
pub(crate) mod test_support;

pub use author::{AuthorCall, AuthorTransport, CandidateSubmission, Capability, ProviderCondition};
pub use ledger::{Call, Ledger, LedgerState, Receipt, Tokens, Trial, UsageScope};
pub use limits::{Limits, Money, SpendPolicy};
pub use role::{PromptInput, QualificationAttempt, RolePolicy, SeededIncumbent, SynthesisRole};
pub use run::{RunRequest, StopReason, qualification_order, run};

use ledger::LedgerError;
use records::RecordError;
use std::fmt;

/// Why a session (or the retained role service) could not continue. Every variant is resumable from the run's
/// records unless the request itself is invalid.
#[derive(Debug)]
pub enum ControllerError {
    /// The request, its limits or a role-declared value is invalid.
    InvalidRequest(String),
    /// The ledger refused an operation (ownership, resume identity, receipts, guards).
    Ledger(LedgerError),
    /// A durable record could not be read or written.
    Record(RecordError),
    /// The author transport failed outside an invocation (readiness, dispatch proof, receipt recovery, context).
    Author { stage: &'static str, detail: String },
    /// A role stage that stops the run failed (`prepare`, `close`).
    Role { stage: &'static str, detail: String },
    /// A settled receipt violated the submission protocol.
    Protocol(String),
    /// The retained role service is unavailable.
    Session(String),
}

impl fmt::Display for ControllerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ControllerError::InvalidRequest(detail) | ControllerError::Protocol(detail) => f.write_str(detail),
            ControllerError::Ledger(error) => write!(f, "{error}"),
            ControllerError::Record(error) => write!(f, "{error}"),
            ControllerError::Author { stage, detail } => write!(f, "author {stage}: {detail}"),
            ControllerError::Role { stage, detail } => write!(f, "role {stage}: {detail}"),
            ControllerError::Session(detail) => write!(f, "retained role service: {detail}"),
        }
    }
}

impl std::error::Error for ControllerError {}

impl From<LedgerError> for ControllerError {
    fn from(error: LedgerError) -> Self {
        match error {
            LedgerError::Record(error) => ControllerError::Record(error),
            other => ControllerError::Ledger(other),
        }
    }
}

impl From<RecordError> for ControllerError {
    fn from(error: RecordError) -> Self {
        ControllerError::Record(error)
    }
}
