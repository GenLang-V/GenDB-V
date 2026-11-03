//! One statement's verified-path state, established once before any author call and then only read: its preflight,
//! the prepared-data references at every admission binding, the statement's prepared inputs and how candidate
//! libraries are run. Shared (`Arc`) by the query role of that statement and by the workload storage role, whose
//! diagnostic query crates and tiny-input builds use every statement.

use crate::prompts::{EarlyStop, RuntimeTarget};
use gendb_frontend::parser::SqlParser;
use gendb_storage::import::{PreparedSource, SqlReference};
use gendb_verification::admission::execution::CandidateRunner;
use gendb_verification::admission::{
    AdmissionError, BindingOrigin, BindingReference, LegacyReferenceAttestation, QueryPreflight, Refused, Statement, StatementInputs, StatementValidation,
    load_evidence, load_references, preflight, prepared_references, record_preflight_evidence, reuse_preflight,
};
use gendb_verification::obligations::DeclaredSource;
use serde_json::json;
use std::path::Path;
use std::sync::Arc;
use std::time::Instant;

/// Where a session's preflight comes from.
#[derive(Clone, Copy, Debug)]
pub enum PreflightFrom<'a> {
    /// A fresh preflight and fresh prepared-data references.
    Fresh,
    /// The completed preflight the request names (`queries[].preflight_from`): reused, or the query is refused.
    Named(&'a Path),
    /// This run's own completed preflight of the statement, written by an earlier controller process of the run
    /// (a restart): reused when its evidence identity is the current one. Otherwise a fresh preflight runs (the reason
    /// is logged) and only its exact references are reused when what they were computed from is unchanged
    /// (`load_references`; format-1 evidence through the run's `attestations`). Never stale: every reused part is
    /// checked against the current identity.
    Earlier { from: &'a Path, attestations: &'a [LegacyReferenceAttestation] },
}

/// Everything established for one statement before its first author call.
pub struct QuerySession {
    pub preflight: QueryPreflight,
    /// Per admission binding: the exact full ordered body on the prepared data, or why none exists there.
    pub references: Vec<BindingReference>,
    /// The statement's delivered columns in the capture it was prepared on (references, serving records).
    pub inputs: StatementInputs,
    pub runner: CandidateRunner,
    /// The configured worker counts (every evaluation measures each).
    pub worker_counts: Vec<usize>,
    /// Execution-time objective (user-selected): every submission is measured at the benchmark bindings under the
    /// exclusive host timing lease, and the close measures the served package again at the same bindings.
    pub performance: bool,
    /// The user's runtime targets of the execution-time objective and its early stop: local trials report each cell
    /// against them (target, early-stop bar, met). Empty and `None` for correctness.
    pub runtime_targets: Vec<RuntimeTarget>,
    pub early_stop: Option<EarlyStop>,
}

impl QuerySession {
    /// Prepare the statement's inputs from the shared capture (`<query_directory>/verus-inputs`), run its preflight and
    /// compute the prepared-data reference at every admission binding, or load both from the completed preflight in
    /// the statement directory `preflight_from` when its evidence identity is the current one (`reuse_preflight`).
    /// `Err` refuses the query before any author call, including the execution-time objective on a template without
    /// user benchmark bindings, or with a benchmark binding that has no exact prepared-data reference (a measured
    /// cell is always compared exactly), and evidence that cannot be reused. Once established, the preflight's
    /// evidence is recorded for later runs (`record_preflight_evidence`).
    ///
    /// Under the validation policy `formal_proofs` (`validation`) the preflight is the capture readiness and the Verus
    /// statement check only, always fresh (`preflight_from` and earlier evidence of the other policy are not used), no
    /// reference is computed and nothing is recorded for reuse; the benchmark bindings carry their saved answers.
    #[allow(clippy::too_many_arguments)]
    pub async fn open(
        statement: Statement,
        source: Arc<PreparedSource>,
        reference: &SqlReference,
        parser: &SqlParser,
        query_directory: &Path,
        runner: CandidateRunner,
        worker_counts: Vec<usize>,
        performance: bool,
        preflight_from: PreflightFrom<'_>,
        validation: StatementValidation,
    ) -> Result<Self, Refused> {
        let inputs = StatementInputs::project(&statement, source, query_directory).map_err(|e| Refused::at(e, json!({"stage":"capture"})))?;
        let benchmark_named = statement.benchmark.iter().all(|&b| matches!(statement.bindings[b].origin, BindingOrigin::Benchmark | BindingOrigin::Concrete));
        if performance && !benchmark_named {
            return Err(AdmissionError::unsupported("the execution-time objective on a template is measured at the user's benchmark bindings (objective.bindings); none were given").into());
        }
        let started = Instant::now();
        let label = query_directory.display().to_string();
        if validation.formal {
            let preflight = preflight(statement, &inputs, reference, parser, &worker_counts, validation).await?;
            let references = prepared_references(&preflight, reference).await;
            eprintln!("preflight {label}: formal_proofs statement check in {:.1} s (no evaluators, tiny cases or references)", started.elapsed().as_secs_f64());
            return Ok(Self { preflight, references, inputs, runner, worker_counts, performance, runtime_targets: vec![], early_stop: None });
        }
        let earlier = match preflight_from {
            PreflightFrom::Earlier { from, .. } => match load_evidence(&statement, &inputs, from) {
                Ok(evidence) => Some(evidence),
                Err(refused) => {
                    eprintln!("preflight: earlier preflight {} not reused whole ({}); running a fresh preflight", from.display(), refused.error);
                    None
                }
            },
            _ => None,
        };
        let earlier_references = match (preflight_from, &earlier) {
            (PreflightFrom::Earlier { from, attestations }, None) => match load_references(&statement, &inputs, from, attestations) {
                Ok(references) => Some(references),
                Err(reason) => {
                    eprintln!("preflight {label}: earlier references of {} not reusable ({reason}); computing them", from.display());
                    None
                }
            },
            _ => None,
        };
        let (preflight, references, references_from) = match (preflight_from, earlier) {
            (_, Some(evidence)) => {
                let references_from = evidence.references_from();
                let (preflight, references) = evidence.complete(statement, &worker_counts, started)?;
                eprintln!("preflight {label}: reused whole in {:.1} s", started.elapsed().as_secs_f64());
                (preflight, references, references_from)
            }
            (PreflightFrom::Named(from), None) => {
                let (preflight, references) = reuse_preflight(statement, &inputs, from, &worker_counts)?;
                (preflight, references, None)
            }
            (PreflightFrom::Fresh | PreflightFrom::Earlier { .. }, None) => {
                let preflight = preflight(statement, &inputs, reference, parser, &worker_counts, validation).await?;
                let established = started.elapsed().as_secs_f64();
                let reusable = earlier_references.map(|loaded| loaded.for_mode(&preflight.prepared));
                match reusable {
                    Some(Ok((references, provenance))) => {
                        let record = preflight.statement.directory.join("prepared-references-reused.json");
                        let _ = std::fs::write(&record, serde_json::to_vec_pretty(&provenance).unwrap_or_default());
                        eprintln!("preflight {label}: established in {established:.1} s; exact references reused ({})", record.display());
                        (preflight, references, Some(provenance))
                    }
                    other => {
                        if let Some(Err(reason)) = other {
                            eprintln!("preflight {label}: earlier references not reusable ({reason}); computing them");
                        }
                        let computing = Instant::now();
                        let references = prepared_references(&preflight, reference).await;
                        eprintln!("preflight {label}: established in {established:.1} s; references computed in {:.1} s", computing.elapsed().as_secs_f64());
                        (preflight, references, None)
                    }
                }
            }
        };
        if performance {
            let statement = &preflight.statement;
            for &b in &statement.benchmark {
                if let Some(Err(reason)) = references.get(b) {
                    let name = &statement.bindings[b].name;
                    return Err(Refused::at(
                        AdmissionError::unsupported(format!("benchmark_binding_without_reference: benchmark binding {name} has no exact prepared-data reference ({reason}), so its measurements could not be compared exactly")),
                        json!({"stage":"reference","binding":name}),
                    ));
                }
            }
        }
        record_preflight_evidence(&preflight, &references, &inputs, references_from).map_err(|e| Refused::at(e, json!({"stage":"preflight_evidence"})))?;
        Ok(Self { preflight, references, inputs, runner, worker_counts, performance, runtime_targets: vec![], early_stop: None })
    }

    /// The session with the user's runtime targets and early stop of its objective (shown in local trials).
    pub fn with_targets(mut self, runtime_targets: Vec<RuntimeTarget>, early_stop: Option<EarlyStop>) -> Self {
        self.runtime_targets = runtime_targets;
        self.early_stop = early_stop;
        self
    }

    pub fn statement(&self) -> &Statement {
        &self.preflight.statement
    }

    /// The statement's demanded columns as a declaration (what its storage uses must cover).
    pub fn demand(&self) -> Result<DeclaredSource, AdmissionError> {
        let statement = self.statement();
        DeclaredSource::of_statement(&statement.instance.doc, &statement.source).map_err(AdmissionError::tool)
    }

    /// The largest configured worker count (asset builds use it).
    pub fn build_workers(&self) -> Result<u32, AdmissionError> {
        self.worker_counts.iter().max().map(|w| *w as u32).ok_or_else(|| AdmissionError::tool("workers absent"))
    }

    /// The statement's inputs over another (extended) capture of the same run: the same projection and view archive,
    /// resolved against `source` (serving resolves storage assets for that capture).
    pub fn inputs_over(&self, source: Arc<PreparedSource>) -> StatementInputs {
        StatementInputs { source, ..self.inputs.clone() }
    }
}
