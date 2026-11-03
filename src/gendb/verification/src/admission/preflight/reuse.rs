//! Reuse of a completed preflight by a later run of the same statement (the request's `queries[].preflight_from`).
//!
//! After a successful preflight and its prepared-data references, the run writes [`EVIDENCE_FILE`] into the statement
//! directory, last: the evidence identity, the framework check record, each binding's evaluator library, the reference
//! mode and each binding's exact reference rows (result wire, [`encode_result_rows`]) or the reason it has none. A
//! later run (a new run directory with its own immutable request, for example with runtime targets measured after the
//! preflight) loads these instead of rerunning the Verus check, the evaluator builds, the reference mode and the
//! DataFusion references, only when the identity it computes now is the recorded one:
//! - `statement`: the run's own `statement.json` (SQL, statement keys, parameter declaration and domains, source
//!   declaration, every admission binding with its name, origin and values, benchmark binding names, refusal probes)
//!   and the schema DDL;
//! - `data`: the source version and delivered row count of every table the statement reads (the key admitted assets
//!   are bound to; other tables or captured columns may differ);
//! - `framework`: the preflight source identity (`GENDB_PREFLIGHT_SOURCES`, computed by `build.rs` at compile time:
//!   the exact content of every file of the crates the preflight is computed by — SQLSpec library, fixed entries,
//!   generators, the SQL frontend, capture and IPC decoding, the DataFusion reference — with the workspace lock file,
//!   the compiler and its settings), the runtime build identity and the entry identities (the query entry is the
//!   statement's: v4, or v5 under declared integrity constraints, whose declarations are also in the statement record
//!   and the schema DDL, so evidence never crosses a change of the declared assumptions). A rebuild that changes only
//!   the synthesis controller, prompts or CLI keeps it; any change in those crates refuses reuse;
//! - `prover`: the Verus pin and the toolchain directory.
//!
//! Runtime targets, early stop, limits and worker counts are not part of it: they guide the search, and the tiny cases
//! (the only worker-count-dependent part) are generated again. Every loaded library and rows file must still have its
//! recorded SHA-256. Anything else (no evidence: a pending, failed or refused preflight; another format; any identity
//! field; a missing or changed file) refuses the query before any author call, naming what differs; there is no
//! silent fresh preflight and no stale evidence.
//!
//! The reusing run records `reused_from` in its `preflight.json`: the framework check and evaluator builds shown there
//! are the earlier run's, not rerun. It writes its own evidence file (same identity, the original libraries), so the
//! earlier run directory must be kept.

use super::{BindingEvaluator, Established, QueryPreflight, capture_readiness, complete, unsliced};
use crate::admission::prepared_reference::{BindingReference, ExactReference, NoReference, PreparedMode, write_descriptive_copies};
use crate::admission::prepared_reference::rewrite::{FinalizationType, RewritePlan};
use crate::admission::records::write_new_json;
use crate::admission::statement::{Statement, StatementInputs};
use crate::admission::{AdmissionError, Refused};
use crate::obligations::{ENTRY_IDENTITY, query_entry};
use crate::verus::{VerusToolchain, verus_pin};
use gendb_artifacts::ContentId;
use gendb_runtime::identity::runtime_build_identity;
use gendb_sqlspec::codec::{RunOutcome, decode_result, encode_result_rows};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};
use std::time::Instant;

/// The evidence record of a completed preflight, in its statement directory.
pub const EVIDENCE_FILE: &str = "preflight-evidence.json";
/// Format 2 adds the reference identity (`identity.reference`) and `references_from`; format 1 (identity by the
/// executable's SHA-256) is reused only for its references, through a [`LegacyReferenceAttestation`].
const EVIDENCE_FORMAT: u32 = 2;
const LEGACY_EVIDENCE_FORMAT: u32 = 1;

/// [`EVIDENCE_FILE`].
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Evidence {
    format_version: u32,
    identity: Value,
    /// The Verus statement check record (`framework-check/check.json` of the run that ran it).
    framework_check: Value,
    /// Per admission binding, in binding order.
    evaluators: Vec<EvaluatorEvidence>,
    prepared: ModeEvidence,
    /// Per admission binding, in binding order.
    references: Vec<ReferenceEvidence>,
    /// When the references were loaded from an earlier preflight instead of computed: its provenance record.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    references_from: Option<Value>,
}

/// A file a later run loads, with its SHA-256.
#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Artifact {
    path: PathBuf,
    sha256: String,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct EvaluatorEvidence {
    binding: String,
    library: Artifact,
    build: Value,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(tag = "mode", rename_all = "snake_case", deny_unknown_fields)]
enum ModeEvidence {
    DatafusionDirect,
    SumCountRewrite { plan: Box<RewritePlan>, types: Vec<FinalizationType>, library: Artifact },
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ReferenceEvidence {
    binding: String,
    /// The exact full ordered body (result wire file) and its record.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    exact: Option<ExactEvidence>,
    /// Why the binding has no exact reference.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    none: Option<String>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ExactEvidence {
    rows: Artifact,
    record: Value,
}

/// Write [`EVIDENCE_FILE`] for a completed preflight (fresh or reused) and its references, with each exact reference's
/// rows as `prepared-reference-<binding>.rows`. Called last, once the statement's session is established.
/// `references_from`: the provenance of references loaded from an earlier preflight ([`ReusableReferences`]).
pub fn record_preflight_evidence(preflight: &QueryPreflight, references: &[BindingReference], inputs: &StatementInputs, references_from: Option<Value>) -> Result<PathBuf, AdmissionError> {
    let statement = &preflight.statement;
    let directory = &statement.directory;
    let evaluators = preflight
        .evaluators
        .iter()
        .zip(&statement.bindings)
        .map(|(evaluator, binding)| Ok(EvaluatorEvidence { binding: binding.name.clone(), library: artifact(&evaluator.library)?, build: evaluator.record.clone() }))
        .collect::<Result<_, AdmissionError>>()?;
    let prepared = match &preflight.prepared {
        PreparedMode::Direct => ModeEvidence::DatafusionDirect,
        PreparedMode::Rewrite { plan, types, library } => ModeEvidence::SumCountRewrite { plan: plan.clone(), types: types.clone(), library: artifact(library)? },
        PreparedMode::NotComputed => return Err(AdmissionError::tool("a formal_proofs preflight has no reference evidence to record")),
    };
    let mut recorded = vec![];
    for (binding, reference) in statement.bindings.iter().zip(references) {
        recorded.push(match reference {
            Ok(exact) => {
                let path = directory.join(format!("prepared-reference-{}.rows", binding.name));
                write_new(&path, &encode_result_rows(&exact.rows))?;
                ReferenceEvidence { binding: binding.name.clone(), exact: Some(ExactEvidence { rows: artifact(&path)?, record: exact.record.clone() }), none: None }
            }
            Err(reason) => ReferenceEvidence { binding: binding.name.clone(), exact: None, none: Some(reason.0.clone()) },
        });
    }
    let evidence = Evidence {
        format_version: EVIDENCE_FORMAT,
        identity: evidence_identity(statement, inputs)?,
        framework_check: preflight.framework_check.clone(),
        evaluators,
        prepared,
        references: recorded,
        references_from,
    };
    let path = directory.join(EVIDENCE_FILE);
    write_new_json(&path, &evidence)?;
    Ok(path)
}

/// The preflight of `statement` and its references at every admission binding, loaded from the completed preflight in
/// the statement directory `from` (module doc). Capture readiness, the v3 candidate files and the labelled tiny cases
/// (`worker_counts`) are established again; the records go to `statement.directory` as for a fresh preflight, with
/// `reused_from`, and the reference copies.
pub fn reuse_preflight(statement: Statement, inputs: &StatementInputs, from: &Path, worker_counts: &[usize]) -> Result<(QueryPreflight, Vec<BindingReference>), Refused> {
    let started = Instant::now();
    load_evidence(&statement, inputs, from)?.complete(statement, worker_counts, started)
}

/// A completed preflight's established part and references, loaded and checked against the current identity
/// ([`load_evidence`]); nothing is written until [`ReusableEvidence::complete`].
pub struct ReusableEvidence {
    established: Established,
    references: Vec<BindingReference>,
    reused_from: Value,
    references_from: Option<Value>,
}

impl ReusableEvidence {
    /// Where the loaded references were computed, when the loaded preflight had itself reused them (its
    /// `references_from`, carried into the new evidence).
    pub fn references_from(&self) -> Option<Value> {
        self.references_from.clone()
    }

    /// The rest of the preflight over the loaded part (tiny cases, records), as in [`reuse_preflight`].
    pub fn complete(self, statement: Statement, worker_counts: &[usize], started: Instant) -> Result<(QueryPreflight, Vec<BindingReference>), Refused> {
        let preflight = complete(statement, self.established, worker_counts, started, Some(self.reused_from))?;
        write_descriptive_copies(&preflight.statement, &self.references);
        Ok((preflight, self.references))
    }
}

/// Load the completed preflight in the statement directory `from` when its evidence identity is the current one
/// (module doc). Writes nothing: a refusal leaves the statement directory as it was, so a caller may still run a fresh
/// preflight there.
pub fn load_evidence(statement: &Statement, inputs: &StatementInputs, from: &Path) -> Result<ReusableEvidence, Refused> {
    let readiness = capture_readiness(statement, inputs)?;
    let evidence_path = from.join(EVIDENCE_FILE);
    let refuse = |detail: String| {
        Refused::at(
            AdmissionError::unsupported(format!("preflight_reuse_refused: {detail}; remove preflight_from for a fresh preflight or name a completed preflight of this statement")),
            json!({"stage":"preflight_reuse","from":from,"evidence":evidence_path}),
        )
    };
    let text = std::fs::read(&evidence_path).map_err(|e| refuse(format!("no completed preflight evidence at {} ({e}): the preflight is pending, failed or refused, or the directory is not a statement directory", evidence_path.display())))?;
    let evidence: Evidence = serde_json::from_slice(&text).map_err(|e| refuse(format!("evidence record {} unreadable: {e}", evidence_path.display())))?;
    if evidence.format_version != EVIDENCE_FORMAT {
        return Err(refuse(format!("evidence format {} (expected {EVIDENCE_FORMAT})", evidence.format_version)));
    }
    let current = evidence_identity(statement, inputs)?;
    if let Some(field) = first_difference(&evidence.identity, &current, "identity") {
        return Err(refuse(format!("{field} differs from the preflight's")));
    }
    if current["data"].as_array().is_none_or(|tables| tables.iter().any(|t| !t["source_version"].is_string())) {
        return Err(refuse("a table the statement reads has no recorded source version, so the prepared data cannot be identified".into()));
    }
    if evidence.framework_check["outcome"] != "verified" || evidence.framework_check["entry_identity"] != query_entry(&statement.instance).identity {
        return Err(refuse("the recorded statement check is not a verified check of the current query entry".into()));
    }
    let names: Vec<&str> = statement.bindings.iter().map(|b| b.name.as_str()).collect();
    let evaluator_names: Vec<&str> = evidence.evaluators.iter().map(|e| e.binding.as_str()).collect();
    let reference_names: Vec<&str> = evidence.references.iter().map(|r| r.binding.as_str()).collect();
    if evaluator_names != names || reference_names != names {
        return Err(refuse(format!("evidence bindings {evaluator_names:?} / {reference_names:?} are not the admission bindings {names:?}")));
    }
    let mut evaluators = vec![];
    for (recorded, binding) in evidence.evaluators.into_iter().zip(&statement.bindings) {
        let library = checked(&recorded.library).map_err(refuse)?;
        let doc = unsliced(&statement.fixed_at(binding)?);
        evaluators.push(BindingEvaluator { doc, library, record: recorded.build });
    }
    let prepared = match evidence.prepared {
        ModeEvidence::DatafusionDirect => PreparedMode::Direct,
        ModeEvidence::SumCountRewrite { plan, types, library } => PreparedMode::Rewrite { plan, types, library: checked(&library).map_err(refuse)? },
    };
    let references = load_reference_rows(evidence.references).map_err(refuse)?;
    let reused_from = json!({"directory":from,"evidence":evidence_path,"identity":current,
        "not_rerun":["Verus statement check of the query entry (record shown is the earlier run's)","verified evaluator build per admission binding (libraries loaded)","prepared-data reference mode","prepared-data references (DataFusion)"],
        "established_again":["statement translation and binding (statement.json)","capture readiness","v3 candidate files","tiny cases and their labels (loaded evaluators)"]});
    Ok(ReusableEvidence {
        established: Established { readiness, framework_check: evidence.framework_check, evaluators, prepared },
        references,
        reused_from,
        references_from: evidence.references_from,
    })
}

/// Each recorded reference: the exact rows (rows file checked by its SHA-256, then decoded) or the recorded reason.
fn load_reference_rows(recorded: Vec<ReferenceEvidence>) -> Result<Vec<BindingReference>, String> {
    let mut references: Vec<BindingReference> = vec![];
    for reference in recorded {
        references.push(match (reference.exact, reference.none) {
            (Some(exact), None) => {
                let bytes = read_checked(&exact.rows)?;
                match decode_result(&bytes) {
                    Ok(RunOutcome::Rows(rows)) => Ok(ExactReference { rows, record: exact.record }),
                    other => return Err(format!("{} is not a rows result wire ({other:?})", exact.rows.path.display())),
                }
            }
            (None, Some(reason)) => Err(NoReference(reason)),
            _ => return Err(format!("binding {} must have exactly one of an exact reference and a reason", reference.binding)),
        });
    }
    Ok(references)
}

/// File in a run directory listing [`LegacyReferenceAttestation`]s (absent: none).
pub const LEGACY_REFERENCE_ATTESTATIONS: &str = "legacy-reference-attestations.json";

/// A reviewed statement that the gendb executable with SHA-256 `executable_sha256`, which wrote format-1 evidence
/// (identified by that SHA only), computed its prepared-data references with the sources whose reference identity is
/// `reference_sources` ([`REFERENCE_SOURCES`]). It is trusted as recorded (not checked by the framework); `method`
/// says how it was established and by whom, and is copied into every use. It lets only the references of such
/// evidence be reused; its proofs and evaluators are always established again.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LegacyReferenceAttestation {
    pub executable_sha256: String,
    pub reference_sources: String,
    pub method: Value,
}

/// The attestations in `run_directory` ([`LEGACY_REFERENCE_ATTESTATIONS`]); none when the file is absent.
pub fn read_legacy_attestations(run_directory: &Path) -> Result<Vec<LegacyReferenceAttestation>, AdmissionError> {
    let path = run_directory.join(LEGACY_REFERENCE_ATTESTATIONS);
    match std::fs::read(&path) {
        Ok(bytes) => serde_json::from_slice(&bytes).map_err(|e| AdmissionError::tool(format!("{}: {e}", path.display()))),
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => Ok(vec![]),
        Err(e) => Err(AdmissionError::tool(format!("{}: {e}", path.display()))),
    }
}

/// The exact references of a completed preflight that a fresh preflight of the same statement may use instead of
/// executing them again ([`load_references`]), with their provenance.
pub struct ReusableReferences {
    references: Vec<BindingReference>,
    mode: ModeEvidence,
    provenance: Value,
}

impl ReusableReferences {
    /// The references and their provenance, when the fresh preflight chose the recorded reference mode: direct, or the
    /// same SUM/COUNT rewrite plan and finalization types (the fresh finalization library is a new build of the same
    /// verified evaluator source, inside the reference identity).
    pub fn for_mode(self, prepared: &PreparedMode) -> Result<(Vec<BindingReference>, Value), String> {
        let same = match (&self.mode, prepared) {
            (ModeEvidence::DatafusionDirect, PreparedMode::Direct) => true,
            (ModeEvidence::SumCountRewrite { plan, types, .. }, PreparedMode::Rewrite { plan: fresh, types: fresh_types, .. }) => plan == fresh && types == fresh_types,
            _ => false,
        };
        if !same {
            return Err(format!("the fresh preflight chose reference mode {} with a different plan than the recorded one", prepared.name()));
        }
        Ok((self.references, self.provenance))
    }
}

/// The exact references of the completed preflight in the statement directory `from`, for reuse by a fresh preflight
/// of `statement`, when what they were computed from is unchanged: the statement record and schema DDL, the data (source
/// version and rows of every table read) and the reference sources ([`REFERENCE_SOURCES`]; for format-1 evidence, by an
/// attestation of its executable). The reference mode is compared after the fresh preflight chose it
/// ([`ReusableReferences::for_mode`]). Every rows file must keep its recorded SHA-256. Writes nothing; `Err` names
/// what differs.
pub fn load_references(statement: &Statement, inputs: &StatementInputs, from: &Path, attestations: &[LegacyReferenceAttestation]) -> Result<ReusableReferences, String> {
    let evidence_path = from.join(EVIDENCE_FILE);
    let text = std::fs::read(&evidence_path).map_err(|e| format!("no completed preflight evidence at {} ({e})", evidence_path.display()))?;
    let evidence: Evidence = serde_json::from_slice(&text).map_err(|e| format!("evidence record {} unreadable: {e}", evidence_path.display()))?;
    let current = evidence_identity(statement, inputs).map_err(|e| e.to_string())?;
    for part in ["statement", "data"] {
        if let Some(field) = first_difference(&evidence.identity[part], &current[part], &format!("identity.{part}")) {
            return Err(format!("{field} differs from the preflight's"));
        }
    }
    if current["data"].as_array().is_none_or(|tables| tables.iter().any(|t| !t["source_version"].is_string())) {
        return Err("a table the statement reads has no recorded source version, so the prepared data cannot be identified".into());
    }
    let attestation = match evidence.format_version {
        EVIDENCE_FORMAT => {
            let recorded = &evidence.identity["reference"]["sources"];
            if recorded != REFERENCE_SOURCES {
                return Err(format!("identity.reference.sources {recorded} differs from the current {REFERENCE_SOURCES}"));
            }
            None
        }
        LEGACY_EVIDENCE_FORMAT => {
            let executable = evidence.identity["framework"]["executable_sha256"].as_str().unwrap_or_default();
            let attested = attestations.iter().find(|a| a.executable_sha256 == executable).ok_or_else(|| format!("format-1 evidence of executable {executable} has no reference attestation ({LEGACY_REFERENCE_ATTESTATIONS})"))?;
            if attested.reference_sources != REFERENCE_SOURCES {
                return Err(format!("the attestation of executable {executable} names reference sources {} but the current ones are {REFERENCE_SOURCES}", attested.reference_sources));
            }
            Some(attested.clone())
        }
        other => return Err(format!("evidence format {other} (expected {EVIDENCE_FORMAT} or {LEGACY_EVIDENCE_FORMAT})")),
    };
    let names: Vec<&str> = statement.bindings.iter().map(|b| b.name.as_str()).collect();
    let reference_names: Vec<&str> = evidence.references.iter().map(|r| r.binding.as_str()).collect();
    if reference_names != names {
        return Err(format!("evidence bindings {reference_names:?} are not the admission bindings {names:?}"));
    }
    let references = load_reference_rows(evidence.references)?;
    let provenance = json!({"directory":from,"evidence":evidence_path,"evidence_format":evidence.format_version,
        "recorded_identity":evidence.identity,"reference_sources":REFERENCE_SOURCES,"attestation":attestation,
        "earlier_references_from":evidence.references_from,
        "compared":["statement record and schema DDL","source version and rows of every table read","reference sources (or the attestation of a format-1 executable)","reference mode, rewrite plan and finalization types","SHA-256 of every rows file"],
        "not_rerun":"the DataFusion prepared-data reference executions (rows loaded from the recorded rows files)",
        "established_again":"the whole preflight: Verus statement check, evaluator builds, reference mode, tiny cases"});
    Ok(ReusableReferences { references, mode: evidence.prepared, provenance })
}

/// The evidence identity of `statement` over `inputs` now (module doc).
fn evidence_identity(statement: &Statement, inputs: &StatementInputs) -> Result<Value, AdmissionError> {
    let data = statement
        .source
        .tables
        .iter()
        .map(|t| Ok(json!({"table":t.name,"source_version":inputs.source.source_version(&t.name),"rows":inputs.rows(&t.name)?})))
        .collect::<Result<Vec<_>, AdmissionError>>()?;
    let toolchain = VerusToolchain::from_env().map_err(AdmissionError::tool)?;
    Ok(json!({"statement":statement_identity(statement)?,"data":data,
        "framework":{"preflight_sources":PREFLIGHT_SOURCES,"runtime":runtime_build_identity(),"entry":ENTRY_IDENTITY,"query_entry":query_entry(&statement.instance).identity},
        "prover":{"pin":verus_pin(),"home":toolchain.home},"reference":{"sources":REFERENCE_SOURCES}}))
}

/// The statement part of the evidence identity: its `statement.json` (with the declared integrity constraints) and
/// the schema DDL (with their ALTER clauses).
fn statement_identity(statement: &Statement) -> Result<Value, AdmissionError> {
    let statement_path = statement.directory.join("statement.json");
    let record: Value = serde_json::from_slice(&std::fs::read(&statement_path).map_err(|e| AdmissionError::tool(format!("{}: {e}", statement_path.display())))?)
        .map_err(AdmissionError::tool)?;
    Ok(json!({"record":record,"schema_ddl":statement.schema_ddl}))
}

/// The first place where `recorded` and `current` differ, as a dotted path under `at`.
fn first_difference(recorded: &Value, current: &Value, at: &str) -> Option<String> {
    match (recorded, current) {
        (Value::Object(r), Value::Object(c)) => {
            let mut keys = r.keys().chain(c.keys().filter(|k| !r.contains_key(*k)));
            keys.find_map(|k| first_difference(r.get(k).unwrap_or(&Value::Null), c.get(k).unwrap_or(&Value::Null), &format!("{at}.{k}")))
        }
        (Value::Array(r), Value::Array(c)) if r.len() == c.len() => r.iter().zip(c).enumerate().find_map(|(i, (r, c))| first_difference(r, c, &format!("{at}[{i}]"))),
        _ if recorded == current => None,
        _ => Some(at.to_string()),
    }
}

/// The content identity of the sources the preflight is computed by (module doc; `build.rs`).
pub const PREFLIGHT_SOURCES: &str = env!("GENDB_PREFLIGHT_SOURCES");
/// The content identity of the sources the exact prepared-data references are computed by (`build.rs`).
pub const REFERENCE_SOURCES: &str = env!("GENDB_REFERENCE_SOURCES");

fn file_sha256(path: &Path) -> Result<String, String> {
    let mut file = std::fs::File::open(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut digest = Sha256::new();
    std::io::copy(&mut file, &mut digest).map_err(|e| format!("{}: {e}", path.display()))?;
    Ok(hex(digest))
}

fn hex(digest: Sha256) -> String {
    ContentId::from_bytes(digest.finalize().into()).to_hex()
}

fn artifact(path: &Path) -> Result<Artifact, AdmissionError> {
    Ok(Artifact { path: path.to_path_buf(), sha256: file_sha256(path).map_err(AdmissionError::tool)? })
}

/// The recorded file (a library loaded by path), still present with its recorded SHA-256.
fn checked(artifact: &Artifact) -> Result<PathBuf, String> {
    same_digest(artifact, file_sha256(&artifact.path)?)?;
    Ok(artifact.path.clone())
}

/// The recorded file's bytes, read once and checked against its recorded SHA-256.
fn read_checked(artifact: &Artifact) -> Result<Vec<u8>, String> {
    let bytes = std::fs::read(&artifact.path).map_err(|e| format!("{}: {e}", artifact.path.display()))?;
    same_digest(artifact, hex(Sha256::new_with_prefix(&bytes)))?;
    Ok(bytes)
}

fn same_digest(artifact: &Artifact, now: String) -> Result<(), String> {
    if now != artifact.sha256 {
        return Err(format!("{} changed since the preflight (sha256 {now}, recorded {})", artifact.path.display(), artifact.sha256));
    }
    Ok(())
}

fn write_new(path: &Path, bytes: &[u8]) -> Result<(), AdmissionError> {
    use std::io::Write;
    std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .and_then(|mut file| file.write_all(bytes))
        .map_err(|e| AdmissionError::tool(format!("{}: {e}", path.display())))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn identity() -> Value {
        json!({"statement":{"record":{"sql":"select 1","admission_bindings":[{"name":"qgen","values":["Brand#45"]}]},"schema_ddl":"CREATE TABLE t (a integer);"},
            "data":[{"table":"part","source_version":"v1","rows":10}],
            "framework":{"preflight_sources":"aa","runtime":"r","entry":"e3","query_entry":"e4"},"prover":{"pin":{"verus":"x"},"home":"/v"}})
    }

    /// Changed SQL, benchmark argument, source version, framework build or prover, and changed declared constraints
    /// (schema DDL, statement record, query entry) are each named; equal identities (key order aside) are accepted.
    #[test]
    fn identity_differences_are_named() {
        let recorded = identity();
        assert_eq!(first_difference(&recorded, &identity(), "identity"), None);
        let cases = [
            ("/statement/record/sql", json!("select 2"), "identity.statement.record.sql"),
            ("/statement/record/admission_bindings/0/values/0", json!("Brand#12"), "identity.statement.record.admission_bindings[0].values[0]"),
            ("/data/0/source_version", json!("v2"), "identity.data[0].source_version"),
            ("/framework/preflight_sources", json!("bb"), "identity.framework.preflight_sources"),
            ("/prover/home", json!("/other"), "identity.prover.home"),
            // Declared constraints added: the DDL gains the ALTER clause, the record the declarations, the entry is v5.
            ("/statement/schema_ddl", json!("CREATE TABLE t (a integer);\nALTER TABLE t ADD PRIMARY KEY (a);\n"), "identity.statement.schema_ddl"),
            ("/framework/query_entry", json!("gendb-verus-entry-v5"), "identity.framework.query_entry"),
        ];
        for (pointer, value, named) in cases {
            let mut current = identity();
            *current.pointer_mut(pointer).unwrap() = value;
            assert_eq!(first_difference(&recorded, &current, "identity").as_deref(), Some(named));
        }
        let mut extra = identity();
        extra["statement"]["record"]["admission_bindings"].as_array_mut().unwrap().push(json!({"name":"minimum"}));
        assert_eq!(first_difference(&recorded, &extra, "identity").as_deref(), Some("identity.statement.record.admission_bindings"));
        let mut added = identity();
        added["framework"]["new"] = json!(1);
        assert_eq!(first_difference(&recorded, &added, "identity").as_deref(), Some("identity.framework.new"));
    }

    /// The same SQL prepared without and with a declared key: the statement identity (record and DDL) and the query
    /// entry differ, so a preflight of one is never reused for the other; preparing it again gives the same identity.
    #[test]
    fn declared_constraints_change_the_statement_identity() {
        use crate::admission::integrity_constraints::{ConstraintDeclaration, IntegrityConstraints, USER_DECLARED};
        use crate::admission::prepare_statement;
        use gendb_artifacts::{ColType, ColumnSpec};
        use gendb_frontend::parser::SqlParser;
        use gendb_storage::import::{DataFormat, DatasetSpec, TableSpec};
        let dataset = DatasetSpec {
            tables: vec![TableSpec {
                name: "t".into(),
                fields: vec![ColumnSpec { name: "a".into(), ty: ColType::I32, nullable: false }],
                locations: vec![PathBuf::from("t.parquet")],
                format: DataFormat::Parquet,
            }],
        };
        let key = IntegrityConstraints { trust: USER_DECLARED.into(), declarations: vec![ConstraintDeclaration { table: "t".into(), sql: "PRIMARY KEY (a)".into() }] };
        let parser = SqlParser::from_environment().unwrap();
        let dir = std::env::temp_dir().join(format!("gendb-preflight-reuse-constraints-{}", std::process::id()));
        let prepare = |constraints: Option<&IntegrityConstraints>, name: &str| {
            prepare_statement(&parser, &dataset, constraints, "SELECT a FROM t", &[], &[], &[], &dir.join(name)).unwrap_or_else(|r| panic!("{}", r.error))
        };
        let (plain, declared, again) = (prepare(None, "plain"), prepare(Some(&key), "declared"), prepare(Some(&key), "again"));
        let identity = |s: &Statement| json!({"statement":statement_identity(s).unwrap(),"query_entry":query_entry(&s.instance).identity});
        assert_eq!(first_difference(&identity(&plain), &identity(&declared), "identity").as_deref(), Some("identity.query_entry"));
        let differs = first_difference(&identity(&plain)["statement"], &identity(&declared)["statement"], "statement").unwrap();
        assert!(differs.starts_with("statement.record"), "{differs}");
        assert_ne!(identity(&plain)["statement"]["schema_ddl"], identity(&declared)["statement"]["schema_ddl"]);
        assert_ne!(identity(&plain)["query_entry"], identity(&declared)["query_entry"]);
        assert_eq!(first_difference(&identity(&declared), &identity(&again), "identity"), None);
        std::fs::remove_dir_all(&dir).unwrap();
    }

    /// A changed or missing artifact is refused; an unchanged one is accepted.
    #[test]
    fn artifacts_must_keep_their_digest() {
        let dir = std::env::temp_dir().join(format!("gendb-preflight-reuse-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let path = dir.join("rows");
        std::fs::write(&path, b"one").unwrap();
        let recorded = artifact(&path).unwrap();
        assert_eq!(checked(&recorded).unwrap(), path);
        assert_eq!(read_checked(&recorded).unwrap(), b"one");
        std::fs::write(&path, b"two").unwrap();
        assert!(checked(&recorded).unwrap_err().contains("changed since the preflight"));
        assert!(read_checked(&recorded).unwrap_err().contains("changed since the preflight"));
        std::fs::remove_file(&path).unwrap();
        assert!(checked(&recorded).is_err() && read_checked(&recorded).is_err());
        std::fs::remove_dir(&dir).unwrap();
    }
}
