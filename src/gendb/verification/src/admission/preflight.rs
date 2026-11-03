//! Preflight of one statement, after data preparation and before any author call: everything the framework must
//! establish so that an author's candidate can be judged. A failure here refuses the statement explicitly.
//!
//! 1. The prepared capture covers every delivered column (capture metadata; no data scan, no hashing).
//! 2. The statement check crate of the statement's query entry ([`query_entry`]: v4, or v5 under declared integrity
//!    constraints; [`query_statement_check_files`]: SQLSpec library, schema, declared constraints for v5, statement,
//!    parameter module, ABI types and fixed entry submodules) and one `--no-cheating` Verus check of it. The storages,
//!    the entry's items and the shim need the author's storage choice and module; they are checked in every query
//!    crate. The v3 candidate files ([`candidate_framework_files`]) are still assembled, unchecked here, for the
//!    saved-route compatibility functions, except for a statement with declared constraints (entry v3 has no such
//!    hypothesis).
//! 3. One verified SQLSpec evaluator per admission binding (its fully fixed instance, LIMIT/OFFSET cleared), built
//!    concurrently with the framework check.
//! 4. Generated tiny cases (per binding, united), each completed to one database ([`cases::complete_database`]) and
//!    labelled by every binding's evaluator. Under declared integrity constraints only the cases the evaluator
//!    certifies are kept ([`cases::certification`]); the others are recorded with their reason and never run, and no
//!    certified case with rows is a recorded warning (`no_certified_nonempty_case`).
//! 5. The prepared-data reference mode ([`prepared_reference::choose_mode`]).
//!
//! Under the validation policy `formal_proofs` ([`super::validation`]) only steps 1 and 2 run: no evaluator, tiny case
//! or reference mode, and the record says so ([`formal_preflight`]).
//!
//! A later run of the same statement may load steps 2, 3 and 5 and the prepared-data references from a completed
//! preflight instead of rerunning them, after checking that the evidence identity is still the current one
//! ([`reuse`]); steps 1 and 4 run again.

pub mod reuse;

use super::cases::{self, Case, Model, Uncertified, label_record};
use super::comparison::Window;
use super::prepared_reference::{self, PreparedMode, build_verified_evaluator};
use super::records::{create_dir, write_new_json};
use super::statement::{Statement, StatementInputs};
use super::validation::StatementValidation;
use super::{AdmissionError, Refused};
use crate::obligations::{ENTRY_IDENTITY, QUERY_ENTRY_V5, QueryEntry, candidate_framework_files, query_entry, query_statement_check_files};
use crate::verus::{CodegenOptions, FrameworkSource, VerusMode, VerusOptions, VerusOutcome, VerusToolchain, freeze_framework_crate, run_verus};
use gendb_frontend::ast::{AstDocument, FieldValue, schema};
use gendb_frontend::columns;
use gendb_frontend::params::ParamType;
use gendb_frontend::parser::SqlParser;
use gendb_runtime::abi::MAX_WORKERS;
use gendb_sqlspec::codec::{HostTables, RunOutcome};
use gendb_sqlspec::evaluator::EvaluatorLibrary;
use gendb_storage::import::SqlReference;
use serde_json::{Value, json};
use std::path::{Path, PathBuf};
use std::time::Instant;

/// Crate name of the framework crate check.
const FRAMEWORK_CHECK_CRATE_NAME: &str = "gendb_framework_check";
/// Verus solver threads of the framework crate check (verification speed only).
const FRAMEWORK_CHECK_THREADS: u32 = 8;

/// The verified SQLSpec evaluator of one admission binding (labels of the tiny cases).
#[derive(Clone, Debug)]
pub struct BindingEvaluator {
    /// The fully fixed instance with LIMIT/OFFSET cleared.
    pub doc: AstDocument,
    pub library: PathBuf,
    /// Build status and Verus wall time.
    pub record: Value,
}

/// Everything the preflight established before any author call.
#[derive(Clone)]
pub struct QueryPreflight {
    pub statement: Statement,
    /// Complete framework file set of the v3 candidate crate (entry v3), for the saved-route compatibility functions
    /// only; not checked by the preflight; empty for a statement with a free text parameter (no v3 text argument) or
    /// with declared integrity constraints (no v3 entry states them). New synthesis assembles query crates with
    /// `query_crate_files`.
    pub framework: Vec<FrameworkSource>,
    /// The record of the statement check (the statement files of its query entry, [`query_statement_check_files`]).
    pub framework_check: Value,
    /// The schema declares integrity constraints (query entry v5): every kept case is certified to satisfy them.
    pub constraints_assumed: bool,
    /// Per admission binding.
    pub evaluators: Vec<BindingEvaluator>,
    /// The cases that are run: every generated case, or under declared constraints the certified ones.
    pub cases: Vec<Case>,
    /// `databases[case]`: the case's complete database, the one the labels are of and every input is projected from.
    pub databases: Vec<HostTables>,
    pub case_generation: Value,
    /// `labels[case][binding]`: the verified evaluator's outcome.
    pub labels: Vec<Vec<RunOutcome>>,
    /// Under declared constraints: generated, certified, certified-with-rows and skipped counts, the skipped cases with
    /// their reasons and any warning (`tiny-cases.json` `certification`); `Null` otherwise.
    pub case_certification: Value,
    pub prepared: PreparedMode,
    /// The statement has integer arithmetic (`+ - *`, unary minus, integer division): DataFusion wraps integer
    /// overflow where PostgreSQL and SQLSpec raise 22003, so the DataFusion reference is not exact for that error.
    pub reference_wraps_integers: bool,
    pub window: Window,
    pub readiness: Value,
    /// The run's validation policy for this statement (saved answers per admission binding under `formal_proofs`).
    pub validation: StatementValidation,
}

/// The preflight of `statement` over its prepared `inputs` (`reference`: the DataFusion reference over the same
/// capture; `worker_counts`: the configured worker counts). Records go to the statement directory (`preflight.json`,
/// `tiny-cases.json`, `framework-check/`, `reference/`, `oracle/`).
/// `validation`: the run's policy for this statement; under `formal_proofs` see [`formal_preflight`].
pub async fn preflight(
    statement: Statement,
    inputs: &StatementInputs,
    reference: &SqlReference,
    parser: &SqlParser,
    worker_counts: &[usize],
    validation: StatementValidation,
) -> Result<QueryPreflight, Refused> {
    if validation.formal {
        return formal_preflight(statement, inputs, validation);
    }
    let started = Instant::now();
    let readiness = capture_readiness(&statement, inputs)?;
    let check_files = query_statement_check_files(&statement.instance, &statement.identity()).map_err(framework_stage)?;
    let toolchain = VerusToolchain::from_env().map_err(AdmissionError::tool)?;
    let (framework_check, evaluators) = check_framework_and_build_evaluators(&statement, &check_files, &toolchain)?;
    let prepared = prepared_reference::choose_mode(&statement, reference, &toolchain, parser).await?;
    complete(statement, Established { readiness, framework_check, evaluators, prepared }, worker_counts, started, None)
}

/// The preflight under the validation policy `formal_proofs`: capture readiness and the Verus statement check of the
/// query entry, nothing else. No verified evaluator is built, no tiny case is generated and no reference mode is chosen
/// (`PreparedMode::NotComputed`); `preflight.json` records what was not run and why.
fn formal_preflight(statement: Statement, inputs: &StatementInputs, validation: StatementValidation) -> Result<QueryPreflight, Refused> {
    let started = Instant::now();
    let readiness = capture_readiness(&statement, inputs)?;
    let check_files = query_statement_check_files(&statement.instance, &statement.identity()).map_err(framework_stage)?;
    let toolchain = VerusToolchain::from_env().map_err(AdmissionError::tool)?;
    let check_dir = statement.directory.join("framework-check");
    let framework_check = check_framework(&toolchain, query_entry(&statement.instance), &check_files, &check_dir)
        .map_err(|e| Refused::at(e, json!({"stage":"framework_check","record":check_dir.join("check.json")})))?;
    let framework = v3_framework_files(&statement)?;
    let constraints_assumed = statement.instance.doc.tables.iter().any(|t| !t.constraints.is_empty());
    let not_run = json!({"status":"not_run","reason":"validation policy formal_proofs: no tiny cases, verified evaluators or reference engine; the Verus proof of every submitted crate against the fixed entry claim is the correctness claim"});
    write_new_json(&statement.directory.join("preflight.json"), &json!({"status":"ready","statement_key":statement.key_id,"entry_identity":ENTRY_IDENTITY,
        "readiness":readiness,"framework_check":framework_check,"validation":validation.record(),
        "references":not_run,"prepared_reference":PreparedMode::NotComputed.name(),"tiny_cases":not_run,
        "constraints_assumed":constraints_assumed,"framework_files":framework.iter().map(|f| &f.path).collect::<Vec<_>>(),"preflight_ns":started.elapsed().as_nanos()}))?;
    Ok(QueryPreflight {
        window: Window::of(&statement.instance.doc),
        reference_wraps_integers: has_integer_arithmetic(&statement.instance.doc),
        statement,
        framework,
        framework_check,
        constraints_assumed,
        evaluators: vec![],
        cases: vec![],
        databases: vec![],
        case_generation: not_run,
        labels: vec![],
        case_certification: Value::Null,
        prepared: PreparedMode::NotComputed,
        readiness,
        validation,
    })
}

/// The v3 candidate files of a statement (saved-route compatibility only), or none: the v3 candidate ABI has no text
/// argument (`gendb_abi::ParamArg`), so a statement with a free text parameter has only the v4 query crate; entry v3 has
/// no constraint hypothesis, so a statement with declared constraints has only its v5 query crate.
fn v3_framework_files(statement: &Statement) -> Result<Vec<FrameworkSource>, Refused> {
    let v3_arguments = statement.instance.free.iter().all(|f| f.ty != ParamType::Text);
    let v3_entry = statement.instance.doc.tables.iter().all(|t| t.constraints.is_empty());
    if v3_arguments && v3_entry {
        candidate_framework_files(&statement.instance, &statement.source, &statement.identity()).map_err(framework_stage)
    } else {
        Ok(Vec::new())
    }
}

/// What a preflight establishes with the prover and the reference engine, computed fresh ([`preflight`]) or loaded
/// from a completed preflight of the same statement ([`reuse::reuse_preflight`]).
struct Established {
    readiness: Value,
    framework_check: Value,
    evaluators: Vec<BindingEvaluator>,
    prepared: PreparedMode,
}

fn framework_stage(error: impl std::fmt::Display) -> Refused {
    Refused::at(AdmissionError::tool(error), json!({"stage":"framework"}))
}

/// The rest of a preflight, the same for a fresh and a reused one: the v3 candidate files, the tiny cases labelled by
/// every binding's evaluator (`tiny-cases.json`) and the record `preflight.json` (`reused_from`: where the established
/// part was loaded from and what was not rerun).
fn complete(statement: Statement, established: Established, worker_counts: &[usize], started: Instant, reused_from: Option<Value>) -> Result<QueryPreflight, Refused> {
    let Established { readiness, framework_check, evaluators, prepared } = established;
    let framework = v3_framework_files(&statement)?;
    let constraints_assumed = statement.instance.doc.tables.iter().any(|t| !t.constraints.is_empty());
    let labelled = labelled_cases(&statement, &evaluators, worker_counts)?;
    let (LabelledCases { cases, databases, generation: case_generation, labels, labelling_ns }, case_certification) =
        if constraints_assumed { certified_cases(labelled, &statement) } else { (labelled, Value::Null) };
    let meaningful = labels.iter().filter(|row| has_rows(row)).count();
    let reference_wraps_integers = has_integer_arithmetic(&statement.instance.doc);
    let directory = &statement.directory;
    let cases_record = directory.join("tiny-cases.json");
    let mut cases_json = json!({"format_version":1,"bindings":statement.bindings,"generation":case_generation,
        "cases":cases.iter().zip(&labels).map(|(c, l)| json!({"case":c.name,"rows_per_table":c.rows(),
            "labels":l.iter().zip(&statement.bindings).map(|(o, b)| json!({"binding":b.name,"reference":label_record(o)})).collect::<Vec<_>>()})).collect::<Vec<_>>(),
        "cases_with_nonempty_rows_at_some_binding":meaningful,"labelling_ns":labelling_ns});
    if constraints_assumed {
        cases_json["certification"] = case_certification.clone();
    }
    write_new_json(&cases_record, &cases_json)?;
    let mut record = json!({"status":"ready","statement_key":statement.key_id,"entry_identity":ENTRY_IDENTITY,
        "readiness":readiness,"framework_check":framework_check,
        "references":evaluators.iter().zip(&statement.bindings).map(|(r, b)| json!({"binding":b.name,"library":r.library,"build":r.record})).collect::<Vec<_>>(),
        "prepared_reference":prepared.name(),
        "reference_limits":if reference_wraps_integers { json!(["integer_overflow: the statement has integer arithmetic; DataFusion wraps integer overflow where PostgreSQL/VERUS_SQL raise 22003, so a candidate's exact 22003 where DataFusion has rows is status-only on the prepared data (the tiny cases check errors exactly)"]) } else { json!([]) },
        "tiny_cases":{"record":cases_record,"cases":cases.len(),"cases_with_nonempty_rows_at_some_binding":meaningful,"labelling_ns":labelling_ns},
        "constraints_assumed":constraints_assumed,
        "framework_files":framework.iter().map(|f| &f.path).collect::<Vec<_>>(),"preflight_ns":started.elapsed().as_nanos()});
    if constraints_assumed {
        record["tiny_cases"]["certification"] = json!({"generated":case_certification["generated"],"certified":case_certification["certified"],
            "certified_with_rows":case_certification["certified_with_rows"],"skipped":case_certification["skipped_by_reason"],"meaning":case_certification["meaning"]});
        record["warnings"] = case_certification["warnings"].clone();
    }
    if let Some(reused_from) = reused_from {
        record["reused_from"] = reused_from;
    }
    write_new_json(&directory.join("preflight.json"), &record)?;
    Ok(QueryPreflight {
        window: Window::of(&statement.instance.doc),
        statement,
        framework,
        framework_check,
        constraints_assumed,
        evaluators,
        cases,
        databases,
        case_generation,
        labels,
        case_certification,
        prepared,
        reference_wraps_integers,
        readiness,
        validation: StatementValidation::default(),
    })
}

/// Every delivered `(table, ordinal)` is a column of the prepared capture.
fn capture_readiness(statement: &Statement, inputs: &StatementInputs) -> Result<Value, Refused> {
    let captured = inputs.source.coverage();
    let mut missing = vec![];
    for t in &statement.source.tables {
        let have = captured.iter().find(|(name, _)| *name == t.name).map(|(_, ordinals)| ordinals.as_slice()).unwrap_or_default();
        for c in &t.columns {
            if !have.contains(&c.ordinal) {
                missing.push(format!("{}.{} (ordinal {})", t.name, c.name, c.ordinal));
            }
        }
    }
    let mut row_counts: Vec<Value> = inputs.columns.bindings().iter().map(|b| json!({"table":b.table,"rows":b.row_count})).collect();
    row_counts.dedup();
    let readiness = json!({"captured":captured,"row_counts":row_counts,"missing":missing,
        "check":"every delivered column of the source declaration is a column of the prepared capture (capture metadata; no data scan, no hashing)"});
    if !missing.is_empty() {
        return Err(Refused::at(AdmissionError::tool(format!("the prepared capture lacks delivered columns {missing:?}")), json!({"stage":"capture","readiness":readiness})));
    }
    Ok(readiness)
}

/// The statement check (`check_files`) and one verified evaluator per admission binding, run concurrently.
fn check_framework_and_build_evaluators(statement: &Statement, check_files: &[FrameworkSource], toolchain: &VerusToolchain) -> Result<(Value, Vec<BindingEvaluator>), Refused> {
    let reference_dir = statement.directory.join("reference");
    create_dir(&reference_dir)?;
    let docs: Vec<AstDocument> = statement.bindings.iter().map(|b| statement.fixed_at(b).map(|d| unsliced(&d))).collect::<Result<_, _>>()?;
    let check_dir = statement.directory.join("framework-check");
    let (check, builds) = std::thread::scope(|scope| {
        let check = scope.spawn(|| check_framework(toolchain, query_entry(&statement.instance), check_files, &check_dir));
        let builds: Vec<_> = docs
            .iter()
            .zip(&statement.bindings)
            .enumerate()
            .map(|(i, (doc, binding))| {
                let dir = reference_dir.join(format!("binding-{i}"));
                scope.spawn(move || -> Result<(PathBuf, Value), AdmissionError> {
                    create_dir(&dir)?;
                    let note = dir.join("instance.json");
                    write_new_json(&note, &json!({"binding":binding,"meaning":"the statement with every parameter fixed at this binding (params::instantiate) and LIMIT/OFFSET cleared"}))?;
                    build_verified_evaluator(toolchain, doc, &note, &dir.join("build"), &format!("gendb_query_reference_{i}"))
                })
            })
            .collect();
        (check.join(), builds.into_iter().map(|h| h.join()).collect::<Vec<_>>())
    });
    let framework_check = check
        .map_err(|_| AdmissionError::tool("framework check thread panicked"))?
        .map_err(|e| Refused::at(e, json!({"stage":"framework_check","record":check_dir.join("check.json")})))?;
    let mut evaluators = vec![];
    for (i, (build, doc)) in builds.into_iter().zip(docs).enumerate() {
        let (library, record) = build
            .map_err(|_| AdmissionError::tool("reference build thread panicked"))?
            .map_err(|e| Refused::at(e, json!({"stage":"reference","binding":i})))?;
        evaluators.push(BindingEvaluator { doc, library, record: json!({"status":record["status"],"wall_ns":record["run"]["wall_ns"]}) });
    }
    Ok((framework_check, evaluators))
}

/// One `--no-cheating` Verus check of the framework-only statement check crate `files` of `entry` in `out`.
fn check_framework(toolchain: &VerusToolchain, entry: QueryEntry, files: &[FrameworkSource], out: &Path) -> Result<Value, AdmissionError> {
    let unscanned: Vec<&str> = files.iter().map(|f| f.path.as_str()).collect();
    let frozen = freeze_framework_crate(files, &unscanned, &out.join("crate")).map_err(|e| AdmissionError::tool(format!("{e:?}")))?;
    let options = VerusOptions {
        crate_name: FRAMEWORK_CHECK_CRATE_NAME.into(),
        codegen: CodegenOptions { opt_level: 0, target_cpu: None },
        num_threads: Some(FRAMEWORK_CHECK_THREADS),
    };
    let run = run_verus(toolchain, &frozen, &options, VerusMode::Verify, &out.join("verus")).map_err(AdmissionError::tool)?;
    let mut record = json!({"outcome":run.outcome,"verification":run.verification,"wall_ns":run.wall_ns,"errors":run.rendered_errors(),
        "argv":run.invocation.args,"frozen":frozen.root,"files":frozen.framework_files,"entry_identity":entry.identity,
        "scope":"statement check of the query entry v4: SQLSpec library + schema.rs + query.rs + gendb_params + ABI + fixed entry submodules (query_statement_check_files); the storages' declarations and interfaces, the entry items and the shim need the author's storage choice and module and are checked in every query crate"});
    if entry == QUERY_ENTRY_V5 {
        record["scope"] = json!("statement check of the query entry v5: SQLSpec library + schema.rs + gendb_constraints.rs (lemma_declared_schema: the declared constraints are well formed over the column schema) + query.rs + gendb_params + ABI + fixed entry submodules (query_statement_check_files); the storages' declarations and interfaces, the entry items and the shim need the author's storage choice and module and are checked in every query crate");
    }
    write_new_json(&out.join("check.json"), &record)?;
    if run.outcome != VerusOutcome::Verified {
        return Err(AdmissionError::unsupported(format!("the framework crate check did not verify ({:?}): {}", run.outcome, run.rendered_errors())));
    }
    Ok(record)
}

/// The tiny cases of a statement with their complete databases and every binding's label.
struct LabelledCases {
    cases: Vec<Case>,
    /// `databases[case]`: the complete database each label is of.
    databases: Vec<HostTables>,
    /// Generation facts per binding.
    generation: Value,
    /// `labels[case][binding]`.
    labels: Vec<Vec<RunOutcome>>,
    /// Wall time of labelling every case by every binding's evaluator.
    labelling_ns: u128,
}

/// Tiny cases of every binding (named `<binding>/<case>` when there are several bindings), each completed to its
/// database and labelled by every binding's evaluator. A case whose delivered tables equal an earlier case's is
/// recorded, not kept: it has the same complete database, labels and checks. Each stage and each case about to be
/// labelled is announced on stderr, so a slow step is visible while it runs.
fn labelled_cases(statement: &Statement, evaluators: &[BindingEvaluator], worker_counts: &[usize]) -> Result<LabelledCases, AdmissionError> {
    let libraries: Vec<EvaluatorLibrary> = evaluators.iter().map(|r| EvaluatorLibrary::load(&r.library)).collect::<Result<_, _>>().map_err(AdmissionError::tool)?;
    let mut all_cases: Vec<Case> = vec![];
    let mut generation = vec![];
    for (i, evaluator) in evaluators.iter().enumerate() {
        eprintln!("preflight tiny cases: generating at binding {}", statement.bindings[i].name);
        let started = Instant::now();
        let demand = columns::analyze(&evaluator.doc).map_err(AdmissionError::tool)?;
        let model = Model::new(&evaluator.doc, &demand, &statement.source, &libraries[i])?;
        let (binding_cases, info) = model.generate(worker_counts, MAX_WORKERS)?;
        let (mut kept, mut repeated) = (0usize, vec![]);
        for mut case in binding_cases {
            if evaluators.len() > 1 {
                case.name = format!("{}/{}", statement.bindings[i].name, case.name);
            }
            match all_cases.iter().find(|earlier| earlier.tables == case.tables) {
                Some(earlier) => repeated.push(json!({"case":case.name,"same_database_as":earlier.name})),
                None => {
                    all_cases.push(case);
                    kept += 1;
                }
            }
        }
        generation.push(json!({"binding":statement.bindings[i].name,"cases":kept,"repeated_databases_not_kept":repeated,
            "generation_ns":started.elapsed().as_nanos(),"generation":info}));
    }
    let constrained = statement.instance.doc.tables.iter().any(|t| !t.constraints.is_empty());
    let labelling = Instant::now();
    // Cases are labelled in parallel, one case per task: each evaluator call is a pure function of its input (the
    // verified evaluator's `abi_run` between a decode and an encode), and the results are taken in case order.
    let labelled = label_in_parallel(&all_cases, |case| {
        let database = cases::complete_database(&statement.instance.doc.tables, &statement.source, &case.tables);
        let row = libraries.iter().map(|evaluator| evaluator.run(&database)).collect::<Result<Vec<_>, _>>();
        (database, row)
    });
    eprintln!("preflight tiny cases: labelled {} cases at {} bindings in {} ms", all_cases.len(), evaluators.len(), labelling.elapsed().as_millis());
    let mut labels = vec![];
    let mut databases = vec![];
    for (case, (database, row)) in all_cases.iter().zip(labelled) {
        let row = row.map_err(AdmissionError::tool)?;
        for (i, outcome) in row.iter().enumerate() {
            // Without declared constraints the case database is the generated values and defaults: a database the
            // evaluator refuses is a framework failure. With them, BadDatabase can come from the heuristic completion
            // and only loses that case (`certified_cases`).
            let completion_refused = constrained && *outcome == RunOutcome::BadDatabase;
            if !completion_refused && matches!(outcome, RunOutcome::BadDatabase | RunOutcome::IllTyped | RunOutcome::WireRefused) {
                return Err(AdmissionError::tool(format!(
                    "generated case {} is not a valid input of the evaluator at binding {} ({outcome:?})",
                    case.name, statement.bindings[i].name
                )));
            }
        }
        labels.push(row);
        databases.push(database);
    }
    Ok(LabelledCases { cases: all_cases, databases, generation: json!(generation), labels, labelling_ns: labelling.elapsed().as_nanos() })
}

/// `label(case)` for every case, on up to the host's available threads (one case per task), in case order.
fn label_in_parallel<T: Send>(cases: &[Case], label: impl Fn(&Case) -> T + Sync) -> Vec<T> {
    let next = std::sync::atomic::AtomicUsize::new(0);
    let results: Vec<std::sync::Mutex<Option<T>>> = cases.iter().map(|_| std::sync::Mutex::new(None)).collect();
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get()).min(cases.len()).max(1);
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| {
                loop {
                    let index = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    let Some(case) = cases.get(index) else { break };
                    let value = label(case);
                    *results[index].lock().expect("label slot") = Some(value);
                }
            });
        }
    });
    results.into_iter().map(|slot| slot.into_inner().expect("label slot").expect("every case is labelled")).collect()
}

/// A case's labels show rows at some binding.
fn has_rows(labels: &[RunOutcome]) -> bool {
    labels.iter().any(|o| matches!(o, RunOutcome::Rows(r) if !r.is_empty()))
}

/// Under declared integrity constraints: the cases the verified evaluator certifies (the rest are recorded with their
/// reason and dropped, so no check ever runs them) and the certification record: counts, the skipped cases and the
/// warning `no_certified_nonempty_case` when no certified case has rows at any binding.
fn certified_cases(labelled: LabelledCases, statement: &Statement) -> (LabelledCases, Value) {
    let LabelledCases { cases: all, databases: all_databases, generation, labels: all_labels, labelling_ns } = labelled;
    let generated = all.len();
    let (mut cases, mut databases, mut labels, mut skipped) = (vec![], vec![], vec![], vec![]);
    let mut by_reason = std::collections::BTreeMap::<&str, usize>::new();
    for ((case, database), row) in all.into_iter().zip(all_databases).zip(all_labels) {
        match cases::certification(&row) {
            Ok(()) => {
                cases.push(case);
                databases.push(database);
                labels.push(row);
            }
            Err(reason) => {
                *by_reason.entry(reason.name()).or_default() += 1;
                skipped.push(json!({"case":case.name,"rows_per_table":case.rows(),"reason":reason.name(),
                    "labels":row.iter().zip(&statement.bindings).map(|(o, b)| json!({"binding":b.name,"outcome":format!("{o:?}")})).collect::<Vec<_>>()}));
            }
        }
    }
    let with_rows = labels.iter().filter(|row| has_rows(row)).count();
    let mut warnings = vec![];
    if with_rows == 0 {
        eprintln!("preflight tiny cases: warning no_certified_nonempty_case ({} certified of {generated})", cases.len());
        warnings.push(json!("no_certified_nonempty_case: no tiny case certified to satisfy the declared constraints has rows at any admission binding; the tiny cases test no row values (the exact prepared-data references still test every admission binding)"));
    }
    let reasons: serde_json::Map<String, Value> = [Uncertified::OutsideDeclaredConstraints, Uncertified::CompletionOutsideDomain, Uncertified::ConstraintsUndecided]
        .into_iter()
        .map(|r| (r.name().to_string(), json!(r.meaning())))
        .collect();
    let record = json!({"constraints_assumed":true,"generated":generated,"certified":cases.len(),"certified_with_rows":with_rows,
        "skipped_by_reason":by_reason,"skipped":skipped,"warnings":warnings,
        "reasons":reasons,
        "meaning":"each case's complete database (the delivered rows completed by a heuristic: distinct keys, referenced parent rows, CHECK-accepted values; delivered values and delivered row counts unchanged) is certified when the verified evaluator returns rows or an SQL error at some binding (Done implies db_wf and constraints_hold); only certified cases are labelled for candidates and given to storage builders, as the same database's projections"});
    (LabelledCases { cases, databases, generation, labels, labelling_ns }, record)
}

/// The same document with ORDER BY kept and LIMIT/OFFSET cleared (the full ordered body).
fn unsliced(doc: &AstDocument) -> AstDocument {
    let mut d = doc.clone();
    let spec = &schema().kinds["OrderedQuery"];
    let root = d.root;
    for (i, (name, _)) in spec.fields.iter().enumerate() {
        match name.as_str() {
            "limit" => d.nodes[root].fields[i] = FieldValue::OptNat(None),
            "offset" => d.nodes[root].fields[i] = FieldValue::Nat(0),
            _ => {}
        }
    }
    d
}

/// Integer `+ - *`, unary minus or integer division anywhere in the statement.
fn has_integer_arithmetic(doc: &AstDocument) -> bool {
    doc.nodes.iter().any(|n| match (n.tag.as_str(), n.field("kind"), n.field("f")) {
        ("Arith" | "Neg", Some(FieldValue::Enum(k)), _) => k == "Int4" || k == "Int8",
        ("Call", _, Some(FieldValue::Enum(f))) => f == "DivInt4" || f == "DivInt8",
        _ => false,
    })
}

#[cfg(test)]
mod tests {
    //! Tiny cases of a correlated scalar subquery over a three-table join (the TPC-H Q2 shape whose join and size cases
    //! once took hours to label) and of a grouped two-table join: every case kind is generated, the join and size cases
    //! enlarge one table over the companion rows only, and no two kept cases share a database.
    use super::*;
    use crate::admission::statement::prepare_statement;
    use gendb_artifacts::{ColType, ColumnSpec};
    use gendb_storage::import::{DataFormat, DatasetSpec, TableSpec};

    /// Only the DDL is used: no data is read.
    fn dataset() -> DatasetSpec {
        let column = |name: &str, ty: ColType| ColumnSpec { name: name.into(), ty, nullable: false };
        let table = |name: &str, fields| TableSpec { name: name.into(), fields, locations: vec![PathBuf::from(format!("{name}.parquet"))], format: DataFormat::Parquet };
        let money = || ColType::Decimal { p: 15, s: 2 };
        DatasetSpec {
            tables: vec![
                table("part", vec![column("p_partkey", ColType::I64), column("p_size", ColType::I32)]),
                table("partsupp", vec![column("ps_partkey", ColType::I64), column("ps_suppkey", ColType::I64), column("ps_supplycost", money())]),
                table("supplier", vec![column("s_suppkey", ColType::I64), column("s_region", ColType::Utf8), column("s_acctbal", money())]),
            ],
        }
    }

    #[test]
    #[ignore = "runs the pinned Verus toolchain and the frontend; -- --ignored"]
    fn join_and_size_cases_enlarge_one_table_over_the_companion_rows() {
        let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
        let work = std::env::temp_dir().join(format!("gendb-tiny-cases-{}-{nanos}", std::process::id()));
        let (parser, toolchain) = (SqlParser::from_environment().unwrap(), VerusToolchain::from_env().unwrap());
        let correlated = "SELECT s_acctbal, p_partkey FROM part, supplier, partsupp WHERE p_partkey = ps_partkey AND s_suppkey = ps_suppkey \
            AND p_size = 15 AND s_region = 'EUROPE' AND ps_supplycost = (SELECT MIN(ps_supplycost) FROM partsupp, supplier \
            WHERE p_partkey = ps_partkey AND s_suppkey = ps_suppkey AND s_region = 'EUROPE') ORDER BY s_acctbal DESC, p_partkey LIMIT 10";
        let grouped = "SELECT s_region, SUM(ps_supplycost) AS cost FROM partsupp, supplier WHERE ps_suppkey = s_suppkey GROUP BY s_region ORDER BY s_region";
        // (name, SQL, tables sharing a row, companion rows per table in the size cases, many_to_many rows per table, a
        // constant predicate to find boundaries of)
        let expected: [(&str, &str, Vec<&str>, usize, Vec<usize>, bool); 2] =
            [("correlated", correlated, vec!["partsupp", "supplier"], 1, vec![2, 3, 2], true), ("grouped", grouped, vec![], 3, vec![4, 6], false)];
        for (name, sql, shared, companions, many_to_many, boundaries) in expected {
            let statement = prepare_statement(&parser, &dataset(), None, sql, &[], &[], &[], &work.join(name)).unwrap_or_else(|r| panic!("{name}: {}", r.error));
            let doc = unsliced(&statement.fixed_at(&statement.bindings[0]).unwrap());
            let dir = work.join(name).join("reference");
            create_dir(&dir).unwrap();
            let (library, _) = build_verified_evaluator(&toolchain, &doc, &dir.join("note.json"), &dir.join("build"), "gendb_tiny_cases").unwrap();
            let started = Instant::now();
            let labelled = labelled_cases(&statement, &[BindingEvaluator { doc, library, record: Value::Null }], &[1, 32, 64]).unwrap();
            println!("{name}: {} cases generated and labelled in {:?}", labelled.cases.len(), started.elapsed());
            let facts = &labelled.generation[0];
            assert_eq!(facts["generation"]["qualifying_tuple_found"], true, "{name}");
            assert_eq!(facts["generation"]["companion_tables_with_one_shared_row"], json!(shared), "{name}");
            let repeated: Vec<&str> = facts["repeated_databases_not_kept"].as_array().unwrap().iter().map(|r| r["case"].as_str().unwrap()).collect();
            let named = |case: &str| labelled.cases.iter().position(|c| c.name == case);
            let mut kinds = vec!["empty_input".to_string(), "one_row".into(), "many_to_many".into(), "unmatched_rows".into()];
            if boundaries {
                kinds.push("predicate_boundaries".into());
            }
            for j in 0..statement.source.tables.len() {
                kinds.push(format!("empty_table_t{j}"));
                kinds.extend([1, 2, 31, 32, 33, 63, 64, 65].map(|n| format!("rows_t{j}_{n}")));
            }
            for kind in &kinds {
                assert!(named(kind).is_some() || repeated.contains(&kind.as_str()), "{name}: no case {kind}");
            }
            for (a, case) in labelled.cases.iter().enumerate() {
                assert!(labelled.cases[..a].iter().all(|earlier| earlier.tables != case.tables), "{name}: {} repeats a database", case.name);
                if let Some(j) = case.name.strip_prefix("rows_t").and_then(|s| s.split('_').next()).and_then(|j| j.parse::<usize>().ok()) {
                    let rows = case.rows();
                    assert!(rows.iter().enumerate().all(|(k, r)| k == j || *r <= companions), "{name}: {} has rows {rows:?}", case.name);
                }
            }
            assert_eq!(labelled.cases[named("many_to_many").unwrap()].rows(), many_to_many, "{name}");
            let rows_at = |case: &str| match &labelled.labels[named(case).unwrap()][0] {
                RunOutcome::Rows(r) => r.len(),
                other => panic!("{name}: {case} labelled {other:?}"),
            };
            assert!(rows_at("one_row") > 0 && rows_at("many_to_many") > 0 && rows_at("rows_t1_65") > 0, "{name}");
        }
    }

    /// p (k PRIMARY KEY, w CHECK 1..9), c (a PRIMARY KEY, k REFERENCES p, v CHECK >= 0), and t/u, a self-referencing
    /// key cycle no statement reads (t.x REFERENCES t.y, u.z REFERENCES t.x). Only the DDL is used: no data is read.
    fn constrained_dataset() -> (DatasetSpec, crate::admission::IntegrityConstraints) {
        use crate::admission::integrity_constraints::{ConstraintDeclaration, IntegrityConstraints, USER_DECLARED};
        let column = |name: &str, ty: ColType| ColumnSpec { name: name.into(), ty, nullable: false };
        let table = |name: &str, fields| TableSpec { name: name.into(), fields, locations: vec![PathBuf::from(format!("{name}.parquet"))], format: DataFormat::Parquet };
        let dataset = DatasetSpec {
            tables: vec![
                table("c", vec![column("a", ColType::I64), column("k", ColType::I64), column("v", ColType::Decimal { p: 15, s: 2 })]),
                table("p", vec![column("k", ColType::I64), column("w", ColType::I32)]),
                table("t", vec![column("x", ColType::I64), column("y", ColType::I64)]),
                table("u", vec![column("z", ColType::I64)]),
            ],
        };
        let declarations = [
            ("c", "PRIMARY KEY (a)"),
            ("p", "PRIMARY KEY (k)"),
            ("t", "PRIMARY KEY (x)"),
            ("t", "UNIQUE (y)"),
            ("c", "FOREIGN KEY (k) REFERENCES p (k)"),
            ("t", "FOREIGN KEY (x) REFERENCES t (y)"),
            ("u", "FOREIGN KEY (z) REFERENCES t (x)"),
            ("p", "CONSTRAINT w_digit CHECK (w BETWEEN 1 AND 9)"),
            ("c", "CONSTRAINT v_nonnegative CHECK (v >= 0)"),
        ];
        let constraints = IntegrityConstraints {
            trust: USER_DECLARED.into(),
            declarations: declarations.iter().map(|(t, sql)| ConstraintDeclaration { table: (*t).into(), sql: (*sql).into() }).collect(),
        };
        (dataset, constraints)
    }

    /// Certification keeps exactly the cases with a Done label, records every other case with its reason, recomputes
    /// the counts, and warns when no certified case has rows.
    #[test]
    fn certification_keeps_certified_cases_and_reports_the_others() {
        let parser = SqlParser::from_environment().unwrap();
        let (dataset, constraints) = constrained_dataset();
        let work = std::env::temp_dir().join(format!("gendb-certification-{}", std::process::id()));
        let statement = prepare_statement(&parser, &dataset, Some(&constraints), "SELECT k, SUM(v) FROM c GROUP BY k ORDER BY k", &[], &[], &[], &work)
            .unwrap_or_else(|r| panic!("{}", r.error));
        let row = vec![gendb_sqlspec::codec::HostValue::Int(1)];
        let outcomes = [
            ("rows", RunOutcome::Rows(vec![row])),
            ("empty", RunOutcome::Rows(vec![])),
            ("error", RunOutcome::SqlError(gendb_sqlspec::codec::SqlErrorKind::NumericValueOutOfRange)),
            ("violation", RunOutcome::ConstraintViolation),
            ("capacity", RunOutcome::Capacity),
            ("domain", RunOutcome::BadDatabase),
        ];
        let labelled = |names: &[&str]| LabelledCases {
            cases: names.iter().map(|n| Case { name: n.to_string(), tables: vec![vec![]] }).collect(),
            databases: names.iter().map(|_| vec![]).collect(),
            generation: Value::Null,
            labels: names.iter().map(|n| vec![outcomes.iter().find(|(o, _)| o == n).unwrap().1.clone()]).collect(),
            labelling_ns: 0,
        };
        let (kept, record) = certified_cases(labelled(&["rows", "violation", "empty", "capacity", "error", "domain"]), &statement);
        let names: Vec<&str> = kept.cases.iter().map(|c| c.name.as_str()).collect();
        assert_eq!(names, ["rows", "empty", "error"]);
        assert_eq!((kept.databases.len(), kept.labels.len()), (3, 3));
        assert_eq!((record["generated"].as_u64(), record["certified"].as_u64(), record["certified_with_rows"].as_u64()), (Some(6), Some(3), Some(1)));
        assert_eq!(record["skipped_by_reason"], json!({"completion_outside_domain":1,"constraints_undecided":1,"outside_declared_constraints":1}));
        let skipped: Vec<(&str, &str)> = record["skipped"].as_array().unwrap().iter().map(|s| (s["case"].as_str().unwrap(), s["reason"].as_str().unwrap())).collect();
        assert_eq!(skipped, [("violation", "outside_declared_constraints"), ("capacity", "constraints_undecided"), ("domain", "completion_outside_domain")]);
        assert_eq!(record["warnings"], json!([]));
        let (kept, record) = certified_cases(labelled(&["empty", "violation"]), &statement);
        assert_eq!(kept.cases.len(), 1);
        assert!(record["warnings"][0].as_str().unwrap().starts_with("no_certified_nonempty_case"), "{record}");
        std::fs::remove_dir_all(&work).ok();
    }

    /// With declared constraints, against the statement's verified evaluator: the generated cases are completed (keys
    /// distinct, the referenced parent rows added, the CHECK-read column set), certified cases with rows exist, cases
    /// whose delivered values violate a declaration (negative v) are skipped as proved violations, every kept database
    /// keeps the case's delivered cells and row counts, and a database completed around the t/u key cycle is a proved
    /// violation, never run.
    #[test]
    #[ignore = "runs the pinned Verus toolchain and the frontend; -- --ignored"]
    fn constrained_cases_are_completed_and_certified_by_the_verified_evaluator() {
        let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos();
        let work = std::env::temp_dir().join(format!("gendb-constrained-cases-{}-{nanos}", std::process::id()));
        let (parser, toolchain) = (SqlParser::from_environment().unwrap(), VerusToolchain::from_env().unwrap());
        let (dataset, constraints) = constrained_dataset();
        let sql = "SELECT k, SUM(v) AS total FROM c GROUP BY k ORDER BY k";
        let statement = prepare_statement(&parser, &dataset, Some(&constraints), sql, &[], &[], &[], &work.join("statement")).unwrap_or_else(|r| panic!("{}", r.error));
        let doc = unsliced(&statement.fixed_at(&statement.bindings[0]).unwrap());
        let dir = work.join("reference");
        create_dir(&dir).unwrap();
        let started = Instant::now();
        let (library, _) = build_verified_evaluator(&toolchain, &doc, &dir.join("note.json"), &dir.join("build"), "gendb_constrained_cases").unwrap();
        println!("evaluator built in {:?}", started.elapsed());
        let started = Instant::now();
        let labelled = labelled_cases(&statement, &[BindingEvaluator { doc, library: library.clone(), record: Value::Null }], &[1, 32, 64]).unwrap();
        let generated = labelled.cases.len();
        let (kept, record) = certified_cases(labelled, &statement);
        println!("{generated} cases labelled and certified in {:?}: {}", started.elapsed(), json!({"certified":kept.cases.iter().map(|c| &c.name).collect::<Vec<_>>(),"with_rows":record["certified_with_rows"],"skipped":record["skipped"]}));
        assert!(record["certified_with_rows"].as_u64().unwrap() > 0 && record["warnings"] == json!([]), "{record}");
        assert!(record["skipped_by_reason"]["outside_declared_constraints"].as_u64().unwrap() > 0, "{record}");
        assert!(record["skipped"].as_array().unwrap().iter().all(|s| s["reason"] == "outside_declared_constraints"), "{record}");
        let schema = &statement.instance.doc.tables;
        let id = |name: &str| schema.iter().position(|t| t.name == name).unwrap();
        let (c, p) = (id("c"), id("p"));
        for (case, database) in kept.cases.iter().zip(&kept.databases) {
            // Delivered cells (c.k, c.v) and the delivered row count unchanged: the candidate's inline input, projected
            // from the database, is the case's values.
            assert_eq!(database[c].len(), case.tables[0].len(), "{}", case.name);
            let projected = cases::inline_columns(&statement.source, database).unwrap();
            for (k, column) in projected.iter().enumerate() {
                let values: Vec<String> = case.tables[0].iter().map(|row| match &row[k] {
                    cases::CaseValue::Num(n) => n.to_string(),
                    cases::CaseValue::Text(t) => t.clone(),
                    cases::CaseValue::Null => unreachable!("the statement's columns are NOT NULL"),
                }).collect();
                assert_eq!(column.values, values, "{}", case.name);
            }
            // Every c.k has its parent in p, whose w the CHECK accepts.
            for row in &database[c] {
                assert!(database[p].iter().any(|parent| parent[0] == row[1]), "{}: {database:?}", case.name);
            }
            assert!(database[p].iter().all(|parent| parent[1] == gendb_sqlspec::codec::HostValue::Int(1)), "{}: {database:?}", case.name);
        }
        // The key cycle: one delivered u row makes the completion add t rows round after round; it stops, and the
        // verified evaluator proves the violation.
        let u_only = columns::SourceDeclaration {
            tables: vec![columns::SourceTable { index: 0, table_id: id("u"), name: "u".into(), columns: vec![columns::SourceColumn { ordinal: 0, name: "z".into(), ty: columns::SourceType::Int64, row_count_only: false, nullable: false }] }],
        };
        let cyclic = cases::complete_database(schema, &u_only, &vec![vec![vec![cases::CaseValue::Num(7)]]]);
        assert!(cyclic[id("t")].len() > 1 && cyclic[id("t")].len() <= schema.len() + 2, "{cyclic:?}");
        let outcome = EvaluatorLibrary::load(&library).unwrap().run(&cyclic).unwrap();
        assert_eq!(outcome, RunOutcome::ConstraintViolation);
        assert_eq!(cases::certification(&[outcome]), Err(Uncertified::OutsideDeclaredConstraints));
        std::fs::remove_dir_all(&work).ok();
    }
}
