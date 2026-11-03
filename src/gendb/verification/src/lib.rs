//! Verification: the pinned Verus toolchain, the fixed proof obligations with candidate crate assembly, and admission.
//! Admission decisions are framework-owned; the toolchain is trusted.
//!
//! - `verus`: the pinned toolchain, freezing and the one verify/compile run.
//! - `reference`: the SQLSpec reference evaluator workflow (library check, evaluator builds, fixture runs,
//!   PostgreSQL differential tests).
//! - `obligations`: the fixed entries (v3 candidate, storage v1/v2 and derived, query v4/v5; Verus text under
//!   `verification/obligations/`), their claims and trusted assumptions (`obligations::claim`), the data-only
//!   generators, the one assembly of each crate kind and the storage composition rule.
//! - `admission`: the statement instance, the preflight before any author call, the independent prepared-data
//!   reference, the worker checks of a compiled candidate (asset, prepared data, refusal probes, tiny cases),
//!   qualification with the TCB record, and re-serving of admitted packages.
//! - `baseline`: exact qualification of a recorded baseline-engine answer at one binding (bound SQL and runner
//!   session, then admission's answer acceptance against the binding's prepared reference) before it may be a target.

pub mod admission;
pub mod baseline;
pub mod obligations;
pub mod reference;
pub mod verus;
