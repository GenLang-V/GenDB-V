//! Admission: the framework's decisions about one statement and one candidate, before and after an author writes code.
//!
//! The fixed meaning is the emitted SQLSpec statement and the fixed entry's final claim (`crate::obligations`);
//! everything here is test infrastructure and record keeping around that claim, never a proof and never a second
//! meaning. The steps, in the order the controller calls them:
//!
//! 1. [`statement`]: translate the SQL once (over the dataset DDL with the request's declared
//!    [`integrity_constraints`]), bind its parameters, derive its source declaration and statement key, and choose the
//!    admission bindings and out-of-domain probes ([`Statement`]). Every refusal here precedes data preparation and any
//!    author call.
//! 2. [`preflight`] (after data preparation): the capture covers the statement, the framework crate check verifies, a
//!    verified SQLSpec evaluator exists for every admission binding, generated tiny cases are labelled by those
//!    evaluators, and the prepared-data reference is chosen ([`QueryPreflight`]). No author call happens before it.
//! 3. [`prepared_reference`]: the independent exact result on the prepared data at every admission binding (DataFusion
//!    over the capture, or a SUM/COUNT rewrite finalized by a verified evaluator), when one exists.
//! 4. [`execution`]: run a compiled candidate library in the isolated worker: build its asset, query the prepared data
//!    at every binding and worker count, probe out-of-domain arguments, run every tiny case; compare each answer with
//!    exactly the outputs the SQL allows ([`comparison`]).
//! 5. [`qualification`]: publish the build, representation, asset, statement key, SQL claim and package records and
//!    admit the package, after a fresh translation reproduces the statement key and framework files.
//! 6. [`served`]: serve the admitted package again from the library and compare every answer with the reference.
//!
//! Over stored data (fixed storage entry and query entry v4): [`storage`] publishes a checked storage build, builds
//! each stored asset once with the stored library and admits the storage; [`stored_execution`] runs the worker checks
//! of a compiled query library over its storage uses' assets (prepared data, refusal probes, tiny cases with tiny
//! assets built by each storage's checked builder) and the tiny-case builds of a storage library;
//! [`qualification_v4`] admits a query package that reads admitted storages, after the storage composition checks.
//!
//! Engines (fixed engine entry, one verified engine for a whole schema): [`engine`] freezes and checks an engine
//! version's sources, verifies it whole, qualifies it on the training templates (saved answers, echoes), provides the
//! one call cell of every engine matrix, and admits it as the engine library's next version.
//!
//! Which of the tests in steps 2–4 and 6 run is the request's [`validation`] policy: under `formal_proofs` no evaluator,
//! tiny case or reference engine runs, only the benchmark bindings are queried on the full data, and their results are
//! compared with saved answers of other engines where given (agreement, not proof).
//!
//! Trust. The SQL -> AST translation, the DataFusion reference, the tiny-case generator and the comparisons are tests;
//! a candidate that passes them is admitted only because Verus checked its whole crate against the fixed claim. What
//! is trusted for the claim is listed by [`qualification::tcb_record`].
//!
//! Errors carry the author-contract failure class ([`FailureClass`]); callers match on the class, never on text.

pub mod bindings;
pub mod cases;
pub mod comparison;
pub mod engine;
pub mod execution;
pub mod integrity_constraints;
pub mod preflight;
pub mod prepared_reference;
pub mod qualification;
pub mod qualification_v4;
pub mod served;
pub mod statement;
pub mod storage;
pub mod stored_execution;
pub mod validation;

mod records;

pub use bindings::{BenchmarkBinding, Binding, BindingOrigin};
pub use integrity_constraints::IntegrityConstraints;
pub use comparison::Window;
pub use preflight::reuse::{
    EVIDENCE_FILE, LEGACY_REFERENCE_ATTESTATIONS, LegacyReferenceAttestation, PREFLIGHT_SOURCES, REFERENCE_SOURCES, ReusableEvidence, ReusableReferences,
    load_evidence, load_references, read_legacy_attestations, record_preflight_evidence, reuse_preflight,
};
pub use preflight::{BindingEvaluator, QueryPreflight, preflight};
pub use prepared_reference::{BindingReference, ExactReference, NoReference, PreparedMode, prepared_references};
pub use statement::{Statement, StatementInputs, dataset_ddl, prepare_statement, sql_ident};
pub use validation::{SavedAnswerSource, StatementValidation, ValidationPolicy};

use serde::Serialize;
use serde_json::Value;
use std::fmt;

/// The author-contract vocabulary of failures: every framework error of the verified path has exactly one class.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum FailureClass {
    UnsupportedCapability,
    MissingInput,
    Refusal,
    ProofFailure,
    ToolFailure,
    ExecutionFailure,
}

impl FailureClass {
    pub const ALL: [FailureClass; 6] = [
        Self::UnsupportedCapability,
        Self::MissingInput,
        Self::Refusal,
        Self::ProofFailure,
        Self::ToolFailure,
        Self::ExecutionFailure,
    ];

    /// The recorded name (also the prefix of an error text).
    pub fn name(self) -> &'static str {
        match self {
            Self::UnsupportedCapability => "unsupported_capability",
            Self::MissingInput => "missing_input",
            Self::Refusal => "refusal",
            Self::ProofFailure => "proof_failure",
            Self::ToolFailure => "tool_failure",
            Self::ExecutionFailure => "execution_failure",
        }
    }

    /// What the class means for an author.
    pub fn meaning(self) -> &'static str {
        match self {
            Self::UnsupportedCapability => {
                "decided before any author call, nothing the author can change: a named refusal of the frontend \
                 (translation, typing, placeholder use), an invalid parameter declaration or test binding, a demanded \
                 source column the ABI cannot bind, a failed framework crate check, or no independent test reference \
                 (no_independent_reference)"
            }
            Self::MissingInput => {
                "a required tool argument, manifest file, crate directory or declared item is absent; fix the request"
            }
            Self::Refusal => {
                "the candidate was read and refused before or by Verus without a proof attempt: manifest schema, \
                 refusal-list scanner finding, a reference to the whole-query evaluator, edited framework file, a \
                 declared item Verus did not check, or a Verus rejection (for example --no-cheating)"
            }
            Self::ProofFailure => {
                "Verus ran and reported verification errors (verbatim diagnostics in the job/evaluation record)"
            }
            Self::ToolFailure => {
                "the toolchain, child worker or framework service failed (installation, rustc crash, timeout, evidence \
                 write); the candidate is not implicated"
            }
            Self::ExecutionFailure => {
                "the verified library ran but a child job crashed, returned a non-Ok status, or returned a result the \
                 SQL does not allow (independent reference on the prepared data, verified evaluator on tiny cases); \
                 never promoted"
            }
        }
    }
}

impl fmt::Display for FailureClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

/// A failed admission step: its failure class and the recorded explanation. Displayed as `<class>: <message>`, the
/// error text of evaluation and job records.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdmissionError {
    pub class: FailureClass,
    pub message: String,
}

impl AdmissionError {
    pub fn new(class: FailureClass, message: impl fmt::Display) -> Self {
        Self { class, message: message.to_string() }
    }

    pub fn unsupported(message: impl fmt::Display) -> Self {
        Self::new(FailureClass::UnsupportedCapability, message)
    }

    pub fn missing_input(message: impl fmt::Display) -> Self {
        Self::new(FailureClass::MissingInput, message)
    }

    pub fn refusal(message: impl fmt::Display) -> Self {
        Self::new(FailureClass::Refusal, message)
    }

    pub fn tool(message: impl fmt::Display) -> Self {
        Self::new(FailureClass::ToolFailure, message)
    }

    pub fn execution(message: impl fmt::Display) -> Self {
        Self::new(FailureClass::ExecutionFailure, message)
    }
}

impl fmt::Display for AdmissionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.class, self.message)
    }
}

impl std::error::Error for AdmissionError {}

/// A statement or preflight refused before any author call: the error and the record detail describing the stage
/// (`{"stage": ...}`, or `null` for a tool failure without one).
#[derive(Clone, Debug)]
pub struct Refused {
    pub error: AdmissionError,
    pub detail: Value,
}

impl Refused {
    pub fn at(error: AdmissionError, detail: Value) -> Self {
        Self { error, detail }
    }
}

impl From<AdmissionError> for Refused {
    fn from(error: AdmissionError) -> Self {
        Self { error, detail: Value::Null }
    }
}
