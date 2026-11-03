//! Pinned Verus toolchain: freeze a candidate crate, then verify (and compile) exactly that snapshot.
//!
//! Flow of one check:
//! 1. [`freeze_author_crate`] (author crate: one or more author roots such as `agent/`, `builder/`,
//!    `stores/<name>/interface/`; [`freeze_crate`] is its one-root `agent/` form) or [`freeze_framework_crate`]
//!    (framework-only crate) writes the crate directory once: framework-generated files plus the author trees copied
//!    under their roots. It scans every author file with the refusal list ([`VERUS_REFUSAL_RULES`]) and makes the
//!    whole directory read-only. A refused snapshot is kept as evidence.
//! 2. [`run_verus`] starts ONE `rust_verify --no-cheating` invocation over exactly that directory. In
//!    [`VerusMode::VerifyAndCompile`] Verus verifies the entire crate and then compiles the same source files to
//!    a `cdylib`; a failed verification writes no library.
//!    [`verify_modules`] is the one module-scoped diagnostic run and [`compile_unverified`] the one `--no-verify`
//!    diagnostic build (authors' unverified trials); neither is ever admission evidence, and admission refuses any
//!    stored build argv carrying either option.
//!
//! Trust: the installed toolchain ([`VerusToolchain`], checked against the source-controlled pin) and the
//! immutability of a frozen directory are trusted. Nothing here hashes sources or binaries. The refusal scan is a
//! lexical check, not a proof. Callers serialize runs that must not overlap (the controller's activity lease).
//!
//! Failure classes: every error and non-success outcome maps to one stable class of the author contract
//! (`refusal`, `proof_failure`, `tool_failure`, `missing_input`) through its `failure_class` method.

mod freeze;
mod lexer;
mod refusal;
mod run;
mod toolchain;

pub use freeze::{freeze_author_crate, freeze_crate, freeze_framework_crate, AuthorRoot, FrameworkSource, FreezeError, FrozenCrate};
pub use refusal::engine_rules;
pub use refusal::{
    rule, scan_source, scan_static_items, scan_whole_statement_evaluator, RefusalFinding, RefusalRule, ALLOWED_ATTRIBUTES, ALLOWED_EXTERNAL_TRAITS,
    ALLOWED_VERIFIER_ATTRIBUTES, STATIC_ITEM_RULE, SUPPORTED_DERIVES, SUPPORTED_MACROS, VERUS_REFUSAL_RULES,
};
pub use run::{
    compile_unverified, run_verus, verify_modules, verus_args, CodegenOptions, Diagnostic, RunError, VerificationSummary, VerusInvocation,
    VerusMode, VerusOptions, VerusOutcome, VerusRun, NO_VERIFY,
};
pub use toolchain::{verus_pin, RustPin, ToolchainError, VerusPin, VerusRelease, VerusToolchain, Z3Pin, VERUS_PIN_JSON};
