//! Admission of an engine version (fixed engine entry `gendb-verus-engine-entry-v1`). An engine version arrives frozen and verified: the engine controller freezes the author's
//! `agent/` tree with a fresh generation of the framework files (`gendb_synthesis::engine::submission`) and runs one
//! whole-crate verify-and-compile with `--no-cheating`. Admission decides from the published records alone and repeats
//! every check it relies on:
//!
//! 1. [`qualify_templates`]: every training template at every visible binding, one call each at
//!    [`QUALIFICATION_WORKERS`] workers (one worker child per template), every answer compared with the saved answers of
//!    other engines by the `formal_proofs` comparator (`execution::compare_prepared_data`), every echo with the host's
//!    rendering of the bound document.
//! 2. Variants (meaning-preserving rewrites of the templates): [`distinct_variants`] keeps those whose encoded bytes
//!    differ from their template's and from every earlier variant's; the controller runs them at
//!    [`QUALIFICATION_WORKERS`] workers, 1 warm + 1 hot, through [`EngineRunner::cell`] (the timing harness's variant
//!    matrix). A variant must return its template's saved answers (gating); its time ratio is only reported.
//! 3. [`admit_engine_on_line`] ([`admit_engine`] for the schema-engine line), from the published build: the TCB; the
//!    build record of the verify-and-compile run (admissible evidence: 0 errors, entire crate, `--no-cheating`); every
//!    author file read back from the stored records and checked by the central author-source scan (every current
//!    rule), [`STATIC_ITEM_RULE`] (every author file) and the engine rules of the run's line (`agent/**`;
//!    [`EngineRuleSet`]: the schema-engine line's `ENGINE_RULES`, template constants, AST fragments and the
//!    whole-statement evaluator, or the general line's `GENERAL_ENGINE_RULES`, template constants, AST fragments and
//!    schema names, plus the schema-name rule on the own interface and builder files of every use that is not a
//!    generated flat storage); the uses' complete column coverage (`check_engine_coverage`); the implementation records;
//!    the package, whose
//!    framework files are compared byte for byte with a fresh generation ([`engine_framework_files`]: the library's
//!    admitted storage packages give each use's declaration and interface, the schema, the embedded toolkit and the
//!    fixed texts the rest); and its admission as the library's next engine version, which checks per use the same
//!    check configuration, the storage's dependency closure carried byte for byte and the storage composition rule
//!    (`check_storage_composition`).
//!
//! The storage policy of the uses (eligibility, one copy of each column, the budget, as the serving storage will stand
//! once the version is selected) is checked by the caller under the library's budget lock immediately before step 3
//! (`gendb_synthesis::storage::engine_library::admit_engine_version`), because the policy lives in synthesis.
//!
//! [`EngineRunner::cell`] is the one cell of every engine matrix (variants and official timing): one statement's AST at
//! one binding and worker count, `calls` calls in one fresh child, returning the record of
//! `execution::compare_prepared_data` (`status`, `warm_wall_ns`, `hot_wall_ns`, `median_hot_wall_ns`, the comparison)
//! with the echo verdict. Timing is descriptive; nothing here is a performance claim.
//!
//! **Per-call limits (general line).** An [`EngineRunner`] with `limits` (`CallLimits::GENERAL_ENGINE` on the general
//! line: 60 s and 144 GiB of anonymous memory per call) starts every engine job with them; the child's watchdog stops a
//! call over a limit and the job ends there (`gendb_runtime::worker`, trusted items `TRUSTED_ITEMS_ENGINE_LIMITS`). Such
//! a cell is recorded, not refused: its record carries the worker's `unfinished` report (`over_time_limit`,
//! `over_memory_limit` or `child_failure`); the calls that finished before the stop are compared as usual (a wrong answer
//! before a stop is still refused), and a cell with none has `status: "unfinished"`. A child failure leaves no echo
//! (`echo: not_run`). Qualification ([`qualify_finished_templates`]) skips the templates the caller names as unfinished
//! at the timing binding and, when a call stops, runs the template's later bindings in a fresh child.
//! Without limits (the schema-engine line) requests, children and records are exactly as before.
//!
//! **Stage runs**: each workload's crate is admitted in that workload's library by
//! [`admit_stage_engine`], with the run's stage rule set (`EngineRuleSet::for_stage`: every workload's names and
//! constants, the workload-module rule) and the uniform flat access (`FlatAccess::Uniform`) in the fresh generation it
//! compares the build with. Its source-checks record adds the flat access, the workload module's report
//! (`engine_rules::workload_module_report`: lines, item kinds, loops, storages named) and the reported schema-name
//! mentions as a summary per name (a stage run reports many). A run of several workloads (`EngineRuleSet::for_members`)
//! is admitted the same way, and the plan (`builder/plan.rs`) of every storage family instance it reads (a storage built
//! from admitted storages that stores every column of every table) is scanned again with the plan rule
//! (`engine_rules::PLAN_IS_DATA_RULE`, R4), recorded as `families` in the source checks. Every other admission is as
//! before.
//!
//! **Templates without free parameters.** A training template with no free parameter is prepared as a concrete
//! statement (its one binding is `CONCRETE_BINDING`); its one visible binding (`v0`, no arguments) names that binding
//! in every check ([`TemplateCheck::statement_binding`]).
//!
//! **Stored answers (general line).** An [`EngineRunner`] with `answer_bound` (`AnswerBound::STORED` on the general
//! line) bounds what a job stores on disk, never what it compares: a job none of whose statements has saved answers at
//! its bindings (the author's own `sql` statements) has its child store each answer over the bound as its row count,
//! the SHA-256 of its result wire and its first rows (`gendb_runtime::worker::StoredAnswer`), judged `not_compared` by
//! that summary; a job with saved answers stores them in full and is compared in full, and when its checks fail (a
//! wrong answer can be of any size) its result file is stored the same way after the comparison. Without it (the
//! schema-engine line) every answer is stored in full, as before.

use super::bindings::{BenchmarkBinding, CONCRETE_BINDING};
use super::comparison::Window;
use super::execution::{CandidateRunner, RANGE_CAPACITY, compare_prepared_data};
use super::integrity_constraints::IntegrityConstraints;
use super::preflight::QueryPreflight;
use super::prepared_reference::{BindingReference, NoReference, PreparedMode};
use super::qualification::{ClauseText, CandidateModule, entry_assumptions, framework_trusted_items, publish_checked_build, record_error, store_error};
use super::statement::prepare_statement;
use super::storage::{build_files, crate_sources, refuse_unscanned_author_sources, v4_host_items};
use super::validation::{NO_REFERENCE_BY_POLICY, ValidationPolicy, checked_cell_status};
use super::{AdmissionError, FailureClass, Refused};
use crate::obligations::{
    check_engine_coverage, check_storage_composition, engine_crate_files_with, with_trusted_shim, DeclaredSource, FlatAccess, StorageName, StorageUse,
    ENGINE_CLAIM_V1, ENGINE_CRATE_NAME, ENGINE_ENTRY_IDENTITY, ENGINE_ENTRY_SOURCE, ENGINE_THEOREMS, ENGINE_TOOLKIT_DIRECTORY, ENGINE_TRUSTED_ASSUMPTIONS,
};
use crate::obligations::{generated_flat_table, whole_schema_declaration};
use crate::verus::engine_rules::{scan_plan_source, workload_module_report, EngineLine, EngineRuleSet, TemplateConstants, PLAN_IS_DATA_RULE};
use crate::verus::{scan_static_items, FrameworkSource, RefusalFinding, RefusalRule, VerusToolchain, STATIC_ITEM_RULE, VERUS_REFUSAL_RULES};
use gendb_artifacts::verus::{
    self as records, StorageComposition, VerusClosureFileV1, VerusEngineAdmissionV1, VerusEnginePackageV1, VerusImplementationV1, VerusItemV1,
    VerusStoragePackageV1, VerusStorageUseV1, VerusTcbV1, ENGINE_PACKAGE_ABI_VERSION,
};
use gendb_artifacts::{blob_id, ContentId, ObjectStore};
use gendb_frontend::ast::TableDef;
use gendb_frontend::engine_encode::{encode_binding, EngineAst};
use gendb_frontend::params::ParamRequest;
use gendb_frontend::parser::SqlParser;
use gendb_registry::author_definition;
use gendb_runtime::abi::{GENDB_ENGINE_SHIM_SOURCE, MAX_WORKERS, TRUSTED_ITEMS_ENGINE};
use gendb_runtime::serve::engine::{ast_digest, ENGINE_SERVING_ITEMS};
use gendb_runtime::worker::{
    AnswerBound, CallLimits, StorageUseInput, Unfinished, UnfinishedReason, WorkerRequest, WorkerResult, TRUSTED_ITEMS_ENGINE_LIMITS, store_bounded_result,
};
use gendb_sqlspec::evaluator::echo_text;
use gendb_storage::import::DatasetSpec;
use gendb_storage::io::PartAccess;
use serde::Serialize;
use serde_json::{json, Value};
use std::path::Path;

/// Gate identity of every engine admission written here.
pub const ENGINE_GATE_IDENTITY: &str = "gendb.verus.engine-admission.v1";
/// Worker count of qualification calls and variant cells.
pub const QUALIFICATION_WORKERS: usize = 64;
/// Record kind of the source checks admission repeats from the stored build (scans, coverage).
pub const ENGINE_SOURCE_CHECKS_KIND: &str = "gendb.verus.engine-source-checks.v1";
/// Record kind of a template qualification ([`qualify_templates`]).
pub const ENGINE_QUALIFICATION_KIND: &str = "gendb.verus.engine-qualification.v1";
/// Entry items recorded with their `requires`/`ensures` text in the entry's implementation record.
const RECORDED_ENTRY_ITEMS: [&str; 4] = ["abi_engine_query", "abi_engine_echo", "theorem_engine_end_to_end", "corollary_inside_capacity"];
/// The author root of engine crates.
const AGENT_ROOT: &str = "agent";

/// The dataset schema an engine is checked over: a translated document's tables (with the request's declared integrity
/// constraints), the DDL text they were translated from and the frontend that translated it.
#[derive(Clone, Copy)]
pub struct EngineSchema<'a> {
    pub tables: &'a [TableDef],
    pub ddl: &'a str,
    pub frontend: &'a Value,
}

/// One storage use as the crate assembly and the composition rule need it, from the library's records.
struct UseFiles {
    name: StorageName,
    declaration: DeclaredSource,
    interface: Vec<FrameworkSource>,
    package: VerusStoragePackageV1,
}

/// The admitted storage package of every use, with its declaration and its checked build's interface files.
fn use_files(store: &ObjectStore, uses: &[VerusStorageUseV1]) -> Result<Vec<UseFiles>, AdmissionError> {
    uses.iter()
        .map(|u| {
            let package = records::resolve_admitted_storage(store, u.package).map_err(|e| AdmissionError::missing_input(format!("storage use {} ({}): {e}", u.name, u.package)))?;
            if package.name != u.name {
                return Err(AdmissionError::refusal(format!("storage use {} names package {} of storage {}", u.name, u.package, package.name)));
            }
            let name = StorageName::new(&u.name).map_err(AdmissionError::refusal)?;
            let declaration: DeclaredSource = serde_json::from_value(package.declaration.clone()).map_err(AdmissionError::tool)?;
            let prefix = name.interface_prefix();
            let build = build_files(store, &records::storage_build(store, &package).map_err(record_error)?)?;
            let interface = build.into_iter().filter(|f| f.path.starts_with(&prefix)).collect();
            Ok(UseFiles { name, declaration, interface, package })
        })
        .collect()
}

fn storage_uses(files: &[UseFiles]) -> Vec<StorageUse<'_>> {
    files.iter().map(|u| StorageUse { name: &u.name, declaration: &u.declaration, interface: &u.interface }).collect()
}

/// Every framework file of the engine crate over `schema` reading `uses` of `store` (with the trusted engine shim;
/// `identity` names the engine in generated headers): the generation admission compares the build with, byte for byte.
pub fn engine_framework_files(store: &ObjectStore, schema: &[TableDef], uses: &[VerusStorageUseV1], identity: &str) -> Result<Vec<FrameworkSource>, AdmissionError> {
    generate(schema, &use_files(store, uses)?, identity, FlatAccess::AsUsed)
}

/// The framework files of the engine crate over `schema` reading `files`, with the flat access `access` and the trusted
/// engine shim.
fn generate(schema: &[TableDef], files: &[UseFiles], identity: &str, access: FlatAccess) -> Result<Vec<FrameworkSource>, AdmissionError> {
    let framework = engine_crate_files_with(schema, &storage_uses(files), identity, access).map_err(|e| {
        let class = FailureClass::ALL.into_iter().find(|c| c.name() == e.failure_class()).unwrap_or(FailureClass::ToolFailure);
        AdmissionError::new(class, e)
    })?;
    Ok(with_trusted_shim(framework, GENDB_ENGINE_SHIM_SOURCE))
}

/// The engine-specific author-source findings of a crate's files: [`STATIC_ITEM_RULE`] on every author file (the
/// registry's author definitions: `agent/**` and the copied storage interfaces) and the engine rules of `rules`' line
/// on the engine's own files (`agent/**`). The central scan (`verus::scan_source`) is separate.
pub fn engine_source_findings(files: &[FrameworkSource], rules: &EngineRuleSet) -> Vec<RefusalFinding> {
    let mut findings = vec![];
    for f in files.iter().filter(|f| author_definition(&f.path).is_some()) {
        findings.extend(scan_static_items(&f.path, &f.text));
        if f.path.starts_with(&format!("{AGENT_ROOT}/")) {
            findings.extend(rules.scan_agent_source(&f.path, &f.text));
        }
    }
    findings
}

/// The findings of `rules`' storage scan ([`EngineRuleSet::scan_storage_source`]; the schema-name rule on the general
/// line, nothing on the schema-engine line) in the own author files (`stores/<name>/interface/**`, `builder/**`) of the
/// storage build `files` of use `name`. A generated flat storage is framework code named after its table and is not
/// scanned (the caller skips it).
pub fn engine_storage_findings(files: &[FrameworkSource], name: &StorageName, rules: &EngineRuleSet) -> Vec<RefusalFinding> {
    let interface = name.interface_prefix();
    files
        .iter()
        .filter(|f| f.path.starts_with(&interface) || f.path.starts_with("builder/"))
        .flat_map(|f| rules.scan_storage_source(&f.path, &f.text))
        .collect()
}

/// The compiled engine and the stored parts one engine call runs over.
pub struct EngineRunner<'a> {
    pub runner: &'a CandidateRunner,
    /// The compiled engine library (the checked build's).
    pub library: &'a Path,
    /// The asset parts directory of every storage use, in the engine's use order (the current capture's assets).
    pub uses: &'a [StorageUseInput],
    pub access: PartAccess,
    /// The per-call limits of every engine job this runner starts: `Some(CallLimits::GENERAL_ENGINE)` on the general
    /// line (a call over a limit ends the job and its cell is recorded unfinished); `None` on the schema-engine line
    /// (unlimited children, records as before).
    pub limits: Option<CallLimits>,
    /// The bound of stored answers: `Some(AnswerBound::STORED)` on the general line (see the module notes: a job that
    /// compares no answer stores each answer over it as its summary and first rows, and a job whose checks failed is
    /// stored the same way after its comparison); `None` on the schema-engine line (every answer stored in full).
    pub answer_bound: Option<AnswerBound>,
}

/// One training template (or one variant of it) prepared for comparison: its statement translated over the dataset
/// with every visible binding as a benchmark binding, and the saved answers of other engines at those bindings
/// (`formal_proofs`), in the shape the existing comparator reads (`QueryPreflight` without evaluators, cases or
/// references).
pub struct TemplateCheck {
    /// The template's name (`Q01`) or the variant's id (`Q07-from_permutation`).
    pub name: String,
    /// The template whose saved answers apply (its own name for a template).
    pub answers_of: String,
    pub preflight: QueryPreflight,
    /// The visible bindings, in order (name, argument texts in ascending `$index`).
    pub bindings: Vec<BenchmarkBinding>,
}

impl TemplateCheck {
    /// Translate `sql` (parameters `parameters`) over `dataset` with the declared `constraints`, with `bindings` as its
    /// benchmark bindings (statement records under `directory`), and read the saved answers of query `answers_of` under
    /// `validation`. A frontend refusal keeps its class (`unsupported_capability`).
    #[allow(clippy::too_many_arguments)]
    pub fn prepare(
        parser: &SqlParser,
        dataset: &DatasetSpec,
        constraints: Option<&IntegrityConstraints>,
        validation: &ValidationPolicy,
        name: &str,
        answers_of: &str,
        sql: &str,
        parameters: &[ParamRequest],
        bindings: &[BenchmarkBinding],
        directory: &Path,
    ) -> Result<Self, AdmissionError> {
        let statement = prepare_statement(parser, dataset, constraints, sql, parameters, &[], bindings, directory).map_err(|Refused { error, .. }| error)?;
        let validation = validation.for_statement(Some(answers_of), &statement)?;
        let preflight = QueryPreflight {
            window: Window::of(&statement.instance.doc),
            reference_wraps_integers: false,
            constraints_assumed: constraints.is_some(),
            statement,
            framework: vec![],
            framework_check: json!({"status":"not_run","reason":"an engine statement is checked by the engine entry (wf_ordered) at every call"}),
            evaluators: vec![],
            cases: vec![],
            databases: vec![],
            case_generation: Value::Null,
            labels: vec![],
            case_certification: Value::Null,
            prepared: PreparedMode::NotComputed,
            readiness: Value::Null,
            validation,
        };
        Ok(Self { name: name.into(), answers_of: answers_of.into(), preflight, bindings: bindings.to_vec() })
    }

    /// Whether a cell of this statement at admission binding `index` compares its answers: it has saved answers there
    /// (an engine cell has no exact reference). The author's own statements have none.
    pub fn compares_answers_at(&self, index: usize) -> bool {
        !self.preflight.validation.answers_at(index).is_empty()
    }

    /// The statement's name of visible binding `binding`: the binding itself, except for a statement without free
    /// parameters (a template without them is prepared as a concrete statement, whose one binding is
    /// [`CONCRETE_BINDING`]): its one visible binding (`v0`, no arguments) is that binding.
    pub fn statement_binding<'b>(&self, binding: &'b str) -> &'b str {
        statement_binding_name(&self.preflight.statement.benchmark_names(), &self.bindings, binding)
    }

    /// The position of visible binding `binding` among the statement's admission bindings (benchmark bindings come
    /// first; [`TemplateCheck::statement_binding`] names it).
    fn binding_index(&self, binding: &str) -> Result<usize, AdmissionError> {
        let statement = &self.preflight.statement;
        let name = self.statement_binding(binding);
        statement
            .benchmark
            .iter()
            .copied()
            .find(|&b| statement.bindings[b].name == name)
            .ok_or_else(|| AdmissionError::tool(format!("{}: no visible binding {binding}", self.name)))
    }

    /// The engine AST of the statement at `binding`: the template document bound after the constant check and encoded
    /// (`engine_encode::encode_binding`). Deterministic and untimed.
    pub fn ast(&self, binding: &str) -> Result<EngineAst, AdmissionError> {
        let found = self.bindings.iter().find(|b| b.name == binding).ok_or_else(|| AdmissionError::tool(format!("{}: no visible binding {binding}", self.name)))?;
        encode_binding(&self.preflight.statement.template, &found.arguments).map_err(|e| AdmissionError::unsupported(format!("{} at {binding}: engine AST encoding: {e}", self.name)))
    }

    fn no_references(&self) -> Vec<BindingReference> {
        self.preflight.statement.bindings.iter().map(|_| Err(NoReference(NO_REFERENCE_BY_POLICY.into()))).collect()
    }
}

/// [`TemplateCheck::statement_binding`] from the statement's benchmark binding names and the visible bindings: a
/// concrete statement (its one benchmark binding is [`CONCRETE_BINDING`]) with one visible binding without arguments
/// names it by that binding; every other binding is its own name.
fn statement_binding_name<'b>(benchmark: &[&str], visible: &[BenchmarkBinding], binding: &'b str) -> &'b str {
    let concrete = benchmark == [CONCRETE_BINDING];
    if concrete && matches!(visible, [only] if only.name == binding && only.arguments.is_empty()) { CONCRETE_BINDING } else { binding }
}

/// The echo verdict of statement `index` of an engine job: equal to the host's rendering of its document, else a tool
/// failure naming both (the trusted encoding is not validated; no answer counts).
fn echo_verdict(echoes: &[String], index: usize, ast: &EngineAst, what: &str, work: &Path) -> Result<Value, AdmissionError> {
    let host = echo_text(&ast.document);
    match echoes.get(index) {
        Some(engine) if *engine == host => Ok(json!({"verdict":"equal","ast_sha256":ast_digest(&ast.bytes),"ast_bytes":ast.bytes.len()})),
        other => Err(AdmissionError::tool(format!(
            "engine_echo_mismatch: {what}: the engine's verified echo {other:?} differs from the host's rendering {host:?} (the host encoding is not validated); evidence {}",
            work.display()
        ))),
    }
}

/// The echo verdict of statement `index` of an engine job's `result`: [`echo_verdict`], except that a limited child that
/// died by a signal (`child_failure`) left no echo (`not_run`).
fn job_echo_verdict(result: &WorkerResult, index: usize, ast: &EngineAst, what: &str, work: &Path) -> Result<Value, AdmissionError> {
    match &result.unfinished {
        Some(Unfinished::ChildFailure(_)) => Ok(json!({"verdict":"not_run","reason":"child_failure: the limited child ended by a signal before writing a result, so no echo was written"})),
        _ => echo_verdict(&result.echoes, index, ast, what, work),
    }
}

/// The record of a cell no call of which finished (the first call was stopped, or the child failed): the shape of
/// `compare_prepared_data`'s records with no call; the caller adds the worker's `unfinished` report.
fn unfinished_cell(check: &TemplateCheck, index: usize, workers: usize) -> Value {
    let binding = &check.preflight.statement.bindings[index];
    json!({"binding":binding.name,"arguments":binding.texts,"workers":workers,"status":"unfinished","calls":0,
        "warm_wall_ns":null,"hot_wall_ns":[],"median_hot_wall_ns":null})
}

/// The record of one engine cell from its job's `result` (statement `check` at admission binding `index`, AST `ast`):
/// the echo verdict and the comparison of every call with the saved answers (`compare_prepared_data`), or the
/// unfinished record when no call finished; with `statement`, `echo` and the worker's `unfinished` report added.
fn cell_record(check: &TemplateCheck, index: usize, ast: &EngineAst, workers: usize, result: &WorkerResult, work: &Path) -> Result<Value, AdmissionError> {
    let binding = &check.preflight.statement.bindings[index].name;
    let echo = job_echo_verdict(result, 0, ast, &format!("{} at {binding}", check.name), work)?;
    let mut record = match &result.unfinished {
        Some(_) if result.observations.is_empty() => unfinished_cell(check, index, workers),
        _ => {
            let mut cells = compare_prepared_data(&check.preflight, &check.no_references(), result, &[index], &[workers], work)?;
            cells.pop().map(|cell| cell.record).ok_or_else(|| AdmissionError::tool("an engine cell compared no call"))?
        }
    };
    record["statement"] = json!(check.name);
    record["echo"] = echo;
    if let Some(unfinished) = &result.unfinished {
        record["unfinished"] = json!(unfinished);
    }
    Ok(record)
}

impl EngineRunner<'_> {
    /// An engine job of `asts` at `workers` workers, `calls` calls each, over this runner's library and uses, with its
    /// limits when it has them, and with its answer bound when it has one and the job compares no answer (`compared`
    /// false).
    fn request(&self, asts: &[Vec<u8>], workers: usize, calls: u32, compared: bool) -> WorkerRequest {
        let mut request = WorkerRequest::for_engine_query(self.library, self.uses.to_vec(), self.access, asts, vec![workers as u32], calls, RANGE_CAPACITY);
        if let Some(limits) = self.limits {
            request = request.with_call_limits(limits);
        }
        match self.answer_bound {
            Some(bound) if !compared => request.with_answer_bound(bound),
            _ => request,
        }
    }

    /// `checked` (the checks of `result`, read from the child under `work`), with that result file stored under this
    /// runner's answer bound when the checks failed: its full answers were compared, and a wrong answer can be of any
    /// size. A store that fails is named in the error, which stays the checks' error.
    fn bounded_on_failure<T>(&self, checked: Result<T, AdmissionError>, result: &WorkerResult, work: &Path) -> Result<T, AdmissionError> {
        match (checked, self.answer_bound) {
            (Err(mut error), Some(bound)) => {
                if let Err(store) = store_bounded_result(work, result, bound) {
                    error.message = format!("{} (its evidence could not be stored under the answer bound: {store})", error.message);
                }
                Err(error)
            }
            (checked, _) => checked,
        }
    }

    /// One matrix cell (the timing harness's `EngineCellRunner::run_cell`): the statement of `check` at visible binding
    /// `binding`, whose engine AST must be exactly `ast` (the bytes encoded before timing), `calls` sequential calls (the
    /// first warm) at `workers` workers in one fresh child under `work` (`bound`: an optional diagnostic child bound in
    /// seconds). Every answer is compared with the saved answers of `check.answers_of` at `binding`
    /// (`compare_prepared_data`), and the echo must equal the host's rendering. Returns that cell record with
    /// `statement` and `echo` added. An answer the claim does not allow, a disagreement, a failed child or an unequal
    /// echo is an `Err`. With limits, a call over a limit is not an error: the record carries the worker's `unfinished`
    /// report, the calls that finished before it are compared as usual, and a cell without a finished call has
    /// `status: "unfinished"` (`synthesis::engine::timing::read_cell` reads it). With an answer bound, a cell without
    /// saved answers stores its answers bounded, and a failed cell's evidence is stored bounded after the comparison.
    #[allow(clippy::too_many_arguments)]
    pub fn cell(&self, check: &TemplateCheck, binding: &str, ast: &[u8], workers: usize, calls: u32, work: &Path, bound: Option<u64>) -> Result<Value, AdmissionError> {
        let encoded = check.ast(binding)?;
        if encoded.bytes != ast {
            return Err(AdmissionError::tool(format!("{} at {binding}: the cell's AST bytes are not the encoding of this statement and binding", check.name)));
        }
        let index = check.binding_index(binding)?;
        let request = self.request(std::slice::from_ref(&encoded.bytes), workers, calls, check.compares_answers_at(index));
        let result = self.runner.run(work, &request, bound)?;
        let checked = cell_record(check, index, &encoded, workers, &result, work);
        self.bounded_on_failure(checked, &result, work)
    }
}

/// A template that qualification skips: a cell of it at the timing binding did not
/// finish, so calls at its other bindings would only reach the limit too.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SkippedTemplate {
    pub template: String,
    /// The worker count and reason of its first unfinished cell at the timing binding.
    pub workers: usize,
    pub reason: UnfinishedReason,
}

/// Qualification of the training templates, every template run: [`qualify_finished_templates`]
/// skipping none.
pub fn qualify_templates(engine: &EngineRunner<'_>, checks: &[TemplateCheck], work: &Path) -> Result<Value, AdmissionError> {
    qualify_finished_templates(engine, checks, &[], work)
}

/// Qualification of the training templates: every template of `checks` except the `skipped` ones
/// at every visible binding, one call each at [`QUALIFICATION_WORKERS`] workers, one fresh child per template under
/// `work/<template>`. Each echo must equal the host's rendering and each answer must be allowed by the saved answers
/// (`compare_prepared_data`; a cell without saved answers is recorded `not_compared`). Returns the qualification record
/// (kind [`ENGINE_QUALIFICATION_KIND`]).
///
/// With limits, a call over a limit is recorded (its binding's cell `status: "unfinished"` with the worker's report),
/// not refused, and the template's later bindings run in a fresh child (`work/<template>-from-<binding>`); a child
/// failure leaves its job's bindings recorded unfinished. The record then also names the limits, the unfinished cells
/// and the skipped templates. Without limits and skips the record is exactly the one before limits existed. With an
/// answer bound, a child none of whose bindings has saved answers stores its answers bounded, and a child whose checks
/// failed has its evidence stored bounded after the comparison.
pub fn qualify_finished_templates(engine: &EngineRunner<'_>, checks: &[TemplateCheck], skipped: &[SkippedTemplate], work: &Path) -> Result<Value, AdmissionError> {
    if let Some(s) = skipped.iter().find(|s| !checks.iter().any(|c| c.name == s.template)) {
        return Err(AdmissionError::tool(format!("qualification: the skipped template {} is not a training template", s.template)));
    }
    let mut templates = vec![];
    let (mut compared, mut not_compared, mut unfinished_cells) = (0usize, 0usize, 0usize);
    for check in checks.iter().filter(|c| !skipped.iter().any(|s| s.template == c.name)) {
        let names: Vec<&str> = check.bindings.iter().map(|b| b.name.as_str()).collect();
        let asts: Vec<EngineAst> = names.iter().map(|b| check.ast(b)).collect::<Result<_, _>>()?;
        let indices: Vec<usize> = names.iter().map(|b| check.binding_index(b)).collect::<Result<_, _>>()?;
        let bytes: Vec<Vec<u8>> = asts.iter().map(|a| a.bytes.clone()).collect();
        let mut bindings = vec![];
        // One child for the template's bindings `start..`; with limits a stopped call ends the child, and the bindings
        // after it run in the next child.
        let mut start = 0;
        while start < names.len() {
            let dir = if start == 0 { work.join(&check.name) } else { work.join(format!("{}-from-{}", check.name, names[start])) };
            let job_compares = indices[start..].iter().any(|&i| check.compares_answers_at(i));
            let result = engine.runner.run(&dir, &engine.request(&bytes[start..], QUALIFICATION_WORKERS, 1, job_compares), None)?;
            let finished = match &result.unfinished {
                None => names.len() - start,
                Some(unfinished) => unfinished.stopped().map_or(0, |call| call.statement),
            };
            let echo = |i: usize| job_echo_verdict(&result, i - start, &asts[i], &format!("{} at {}", check.name, names[i]), &dir);
            let checked = (start..start + finished).map(echo).collect::<Result<Vec<Value>, _>>().and_then(|echoes| {
                let cells = compare_prepared_data(&check.preflight, &check.no_references(), &result, &indices[start..start + finished], &[QUALIFICATION_WORKERS], &dir)?;
                Ok((echoes, cells))
            });
            let (echoes, cells) = engine.bounded_on_failure(checked, &result, &dir)?;
            for ((name, echo), cell) in names[start..].iter().zip(echoes).zip(cells) {
                if checked_cell_status(&cell.record["status"]) {
                    compared += 1;
                } else {
                    not_compared += 1;
                }
                bindings.push(json!({"binding":name,"echo":echo,"cell":cell.record}));
            }
            let Some(unfinished) = &result.unfinished else { break };
            // The stopped binding; after a child failure, every binding of the job (which call failed is unknown).
            let end = if unfinished.stopped().is_some() { start + finished + 1 } else { names.len() };
            for i in start + finished..end {
                let mut cell = unfinished_cell(check, indices[i], QUALIFICATION_WORKERS);
                cell["unfinished"] = json!(unfinished);
                unfinished_cells += 1;
                bindings.push(json!({"binding":names[i],"echo":engine.bounded_on_failure(echo(i), &result, &dir)?,"cell":cell}));
            }
            start = end;
        }
        templates.push(json!({"template":check.name,"statement":check.preflight.statement.directory,"bindings":bindings}));
    }
    let status = match (not_compared, unfinished_cells) {
        (0, 0) => "saved_answers_agree",
        (_, 0) => "saved_answers_agree_where_given",
        _ => "saved_answers_agree_where_finished",
    };
    let mut record = json!({"status":status,
        "workers":QUALIFICATION_WORKERS,"calls_per_binding":1,"cells_compared":compared,"cells_without_saved_answers":not_compared,
        "templates":templates,"comparator":"formal_proofs: our rows in ORDER BY order; integers, text and dates exactly, other numerics as decimals or within the relative tolerance; ORDER BY key sequence row by row, tie classes as multisets, under LIMIT the last tie class by count and keys; at least one engine agrees (each engine's verdict recorded)",
        "echo":"every statement's echo (the engine's verified render_query of the decoded bytes) equals the host's rendering of the bound document",
        "scope":"a test of the trusted base (frontend, encoder, shim, host) and the environment; the claim is the proof"});
    if engine.limits.is_some() || !skipped.is_empty() {
        record["limits"] = json!(engine.limits);
        record["cells_unfinished"] = json!(unfinished_cells);
        record["skipped"] = json!(skipped);
        record["unfinished_rule"] = json!("a call over a limit is recorded unfinished, not refused (a wrong answer before it still refuses); the template's later bindings run in a fresh child; templates unfinished at the timing binding are skipped");
    }
    Ok(record)
}

/// One variant of a template: its manifest id and kind, and its statement prepared against the template's saved
/// answers ([`TemplateCheck::prepare`] with `answers_of` the template).
pub struct VariantCheck {
    pub id: String,
    pub kind: String,
    pub template: String,
    pub check: TemplateCheck,
}

/// The variants to run with their ASTs, and the records of those whose bytes equal an earlier statement's.
pub type DistinctVariants<'v> = (Vec<(&'v VariantCheck, EngineAst)>, Vec<Value>);

/// The variants that are run: those whose encoded bytes at `binding` differ from their template's and from every
/// earlier variant's (in the given order), with their ASTs. The others are listed with the statement whose bytes they
/// equal (`same_ast_as`). Encoding only; nothing runs.
pub fn distinct_variants<'v>(templates: &[TemplateCheck], variants: &'v [VariantCheck], binding: &str) -> Result<DistinctVariants<'v>, AdmissionError> {
    let mut seen: Vec<(String, Vec<u8>)> = vec![];
    for template in templates {
        seen.push((template.name.clone(), template.ast(binding)?.bytes));
    }
    let (mut distinct, mut skipped) = (vec![], vec![]);
    for variant in variants {
        let ast = variant.check.ast(binding)?;
        match seen.iter().find(|(_, bytes)| *bytes == ast.bytes) {
            Some((same, _)) => skipped.push(json!({"variant":variant.id,"kind":variant.kind,"template":variant.template,"same_ast_as":same,"ast_sha256":ast_digest(&ast.bytes)})),
            None => {
                seen.push((variant.id.clone(), ast.bytes.clone()));
                distinct.push((variant, ast));
            }
        }
    }
    Ok((distinct, skipped))
}

/// What admission records of one frozen, verified, qualified engine version.
pub struct EngineCandidate<'a> {
    /// The frozen engine crate (`<root>/src/`) that one whole-crate verify-and-compile run checked.
    pub frozen_root: &'a Path,
    /// That run's record (`VerusRun::record`: argv, environment, exit code, stdout, wall time, library).
    pub verus_run: &'a Value,
    /// The admitted storages it reads, in the entry's use order (a workspace storage is registered first).
    pub uses: Vec<VerusStorageUseV1>,
    /// The identity the frozen crate's generated headers name (`engine_crate_files(.., identity)`).
    pub generation_identity: &'a str,
    pub constants: &'a TemplateConstants,
    /// The author's modules with their checked items (descriptive).
    pub modules: Vec<CandidateModule>,
    /// `(record kind, record)` of every evidence record (storage policy, qualification, variants, timing), stored and
    /// named by the admission after the source checks admission records itself.
    pub evidence: Vec<(&'a str, Value)>,
    /// The storage assets qualification ran over.
    pub assets: Vec<ContentId>,
}

/// Every record id of an admitted engine version.
#[derive(Clone, Debug, Serialize)]
pub struct EngineAdmission {
    pub admission: ContentId,
    /// 1-based version on the library's engine stream (now the selected version).
    pub version: u64,
    pub package: ContentId,
    pub build: ContentId,
    pub tcb: ContentId,
    pub implementations: Vec<ContentId>,
    pub storage_uses: Vec<VerusStorageUseV1>,
    pub evidence: Vec<ContentId>,
}

impl EngineAdmission {
    pub fn record(&self) -> Value {
        json!({"admitted":true,"kind":"verus_engine","entry_identity":ENGINE_ENTRY_IDENTITY,"version":self.version,"admission":self.admission,
            "package":self.package,"build":self.build,"tcb":self.tcb,"implementations":self.implementations,"storage_uses":self.storage_uses,
            "evidence":self.evidence,"claim":ENGINE_CLAIM_V1.claim,
            "proof_link":"the build record stores the frozen sources, the raw Verus JSON (0 errors, entire crate, including gendb_entry::theorem_engine_end_to_end over the actual entry, the AST codec, the copied storage interfaces and the agent code) and the library compiled by that same invocation; admission compared every framework file byte for byte with a fresh generation from the library's admitted storage packages, scanned every author file again from the stored records, and checked for every storage use the same check configuration, the storage's dependency closure byte for byte and implementation ownership"})
    }
}

/// The TCB record of engine packages of `line`: the shared items, the v4 runtime and stored assets, the engine ABI and
/// serving (on the general line also the per-call limits' watchdog and the profile sampler,
/// `TRUSTED_ITEMS_ENGINE_LIMITS`), the entry's assumptions, and the refusal rules applied (the central list, the
/// static-item rule, the line's engine rules: `ENGINE_RULES` or `GENERAL_ENGINE_RULES`). The schema-engine line's record
/// is the record engine packages had before the general line existed, byte for byte.
pub fn engine_tcb_record(line: EngineLine) -> Result<VerusTcbV1, AdmissionError> {
    tcb_record(line, line.rules())
}

/// [`engine_tcb_record`] with the engine rules `engine_rules` of the rule set applied (a stage run's
/// `STAGE_ENGINE_RULES`, else the line's).
fn tcb_record(line: EngineLine, engine_rules: &[RefusalRule]) -> Result<VerusTcbV1, AdmissionError> {
    let mut items = framework_trusted_items();
    let mut host: Vec<(&str, &str)> = TRUSTED_ITEMS_ENGINE.into_iter().chain(ENGINE_SERVING_ITEMS).collect();
    if line == EngineLine::General {
        // General-line versions are evaluated under per-call limits: the watchdog decides whether a cell finished.
        host.extend(TRUSTED_ITEMS_ENGINE_LIMITS);
    }
    items.extend(v4_host_items(&host));
    items.extend(entry_assumptions(ENGINE_TRUSTED_ASSUMPTIONS, ENGINE_ENTRY_IDENTITY));
    let rules: Vec<_> = VERUS_REFUSAL_RULES.iter().chain([&STATIC_ITEM_RULE]).chain(engine_rules).collect();
    Ok(VerusTcbV1 { items, refusal_rules: serde_json::to_value(rules).map_err(AdmissionError::tool)? })
}

/// [`admit_engine_on_line`] on the schema-engine line (a request without `engine.line`):
/// its records are those of every engine admission before the general line existed.
pub fn admit_engine(store: &ObjectStore, schema: EngineSchema<'_>, candidate: EngineCandidate<'_>, clause_text: ClauseText<'_>) -> Result<EngineAdmission, AdmissionError> {
    admit_engine_on_line(store, schema, candidate, EngineLine::SchemaEngine, clause_text)
}

/// Publish every record of a frozen, verified, qualified engine and admit it as the library's next engine version (step
/// 3 of the module documentation), under the engine source rules of `line` over the candidate's template constants and
/// `schema`. The caller holds the library's budget lock and has just checked the storage policy of the uses.
pub fn admit_engine_on_line(
    store: &ObjectStore,
    schema: EngineSchema<'_>,
    candidate: EngineCandidate<'_>,
    line: EngineLine,
    clause_text: ClauseText<'_>,
) -> Result<EngineAdmission, AdmissionError> {
    let rules = EngineRuleSet::for_line(line, candidate.constants.clone(), schema.tables);
    admit(store, schema, candidate, &rules, FlatAccess::AsUsed, clause_text)
}

/// [`admit_engine_on_line`] for one workload's crate of a stage run (module documentation, "Stage runs"): `schema` and
/// the candidate's uses are that workload's, `store` its library, and `rules` the run's stage rule set
/// (`EngineRuleSet::for_stage`, the candidate's `constants` are not read); the fresh generation has the uniform flat
/// access. A rule set that is not a stage run's is refused (a tool failure: the caller's).
pub fn admit_stage_engine(
    store: &ObjectStore,
    schema: EngineSchema<'_>,
    candidate: EngineCandidate<'_>,
    rules: &EngineRuleSet,
    clause_text: ClauseText<'_>,
) -> Result<EngineAdmission, AdmissionError> {
    if !rules.is_stage() {
        return Err(AdmissionError::tool("admit_stage_engine: the rule set is not a stage run's (EngineRuleSet::for_stage)"));
    }
    admit(store, schema, candidate, rules, FlatAccess::Uniform, clause_text)
}

/// The admission of [`admit_engine_on_line`] and [`admit_stage_engine`] under `rules`, comparing the build with a fresh
/// generation under `access`.
fn admit(
    store: &ObjectStore,
    schema: EngineSchema<'_>,
    candidate: EngineCandidate<'_>,
    rules: &EngineRuleSet,
    access: FlatAccess,
    clause_text: ClauseText<'_>,
) -> Result<EngineAdmission, AdmissionError> {
    let line = rules.line();
    let files = use_files(store, &candidate.uses)?;
    check_engine_coverage(schema.tables, &storage_uses(&files)).map_err(AdmissionError::refusal)?;
    let toolchain = VerusToolchain::from_env().map_err(AdmissionError::tool)?;
    let tcb = store.put(1, records::VERUS_TCB_KIND, &tcb_record(line, rules.rules())?).map_err(store_error)?;
    let sources = crate_sources(candidate.frozen_root, &|path| path.starts_with(&format!("{AGENT_ROOT}/")))?;
    let build = publish_checked_build(store, &toolchain, tcb, candidate.frozen_root, sources, candidate.verus_run)?;
    let build_record: records::VerusBuildV1 = store.read(build).and_then(|o| o.decode()).map_err(store_error)?;
    refuse_unscanned_author_sources(store, &build_record)?;
    let stored = build_files(store, &build_record)?;
    refuse_source_findings(&engine_source_findings(&stored, rules), "author files of the engine build")?;
    let (mut storage_findings, mut storages_scanned) = (vec![], vec![]);
    for (u, use_) in files.iter().zip(storage_uses(&files)) {
        let storage_build = records::storage_build(store, &u.package).map_err(record_error)?;
        refuse_unscanned_author_sources(store, &storage_build)?;
        if line == EngineLine::General && generated_flat_table(schema.tables, &use_).is_none() {
            storage_findings.extend(engine_storage_findings(&build_files(store, &storage_build)?, &u.name, rules));
            storages_scanned.push(u.name.to_string());
        }
    }
    refuse_source_findings(&storage_findings, "author files of the storages the engine reads")?;
    // A run of several workloads: the plan of every family instance the engine reads is data (R4), checked again here.
    let plans_scanned = if rules.is_members() { refuse_instance_plans(store, schema.tables, &files)? } else { vec![] };
    let fresh = generate(schema.tables, &files, candidate.generation_identity, access)?;
    let constraints = fresh
        .iter()
        .find(|f| f.path == records::CONSTRAINTS_MODULE_PATH)
        .map(|f| blob_id(f.text.as_bytes()))
        .ok_or_else(|| AdmissionError::refusal("engine_requires_declared_constraints: the fresh generation has no gendb_constraints.rs"))?;
    let toolkit: Vec<VerusClosureFileV1> = build_record
        .sources
        .iter()
        .filter(|s| s.path.starts_with(ENGINE_TOOLKIT_DIRECTORY))
        .map(|s| VerusClosureFileV1 { path: s.path.clone(), blob: s.blob, bytes: s.bytes })
        .collect();
    let implementations = publish_implementations(store, build, &candidate.modules, clause_text)?;
    let package = VerusEnginePackageV1 {
        entry_identity: ENGINE_ENTRY_IDENTITY.into(),
        build,
        theorems: ENGINE_THEOREMS.iter().map(|t| t.to_string()).collect(),
        schema_ddl: store.put_blob(schema.ddl.as_bytes()).map_err(store_error)?,
        frontend: schema.frontend.clone(),
        constraints,
        generation_identity: candidate.generation_identity.into(),
        storage_uses: candidate.uses.clone(),
        toolkit,
        implementations: implementations.clone(),
        abi_version: ENGINE_PACKAGE_ABI_VERSION,
        workers: (1, MAX_WORKERS as u32),
        tcb,
    };
    let expected: Vec<(&str, &str)> = fresh.iter().map(|f| (f.path.as_str(), f.text.as_str())).collect();
    let package_id = records::publish_engine_package(store, &package, &expected).map_err(record_error)?;
    let mut checks = json!({"build":build,"author_files":build_record.sources.iter().filter(|s| author_definition(&s.path).is_some()).map(|s| &s.path).collect::<Vec<_>>(),
        "rules":{"central":VERUS_REFUSAL_RULES.iter().map(|r| r.id).collect::<Vec<_>>(),"static_items":STATIC_ITEM_RULE.id,"engine":rules.rules().iter().map(|r| r.id).collect::<Vec<_>>(),
            "template_constants":candidate.constants.constants().len(),"findings":0,"read_from":"the stored build record (every author file as verified)"},
        "coverage":"complete: the storage uses together store every column of every table (check_engine_coverage)",
        "framework_files":"byte for byte a fresh generation from the library's admitted storage packages, the schema and the embedded toolkit (publish_engine_package)",
        "storage_uses":candidate.uses});
    if line == EngineLine::General {
        // The schema-engine line's record stays as before; the general line names its rule set and what it scanned.
        let agent_files: Vec<&FrameworkSource> = stored.iter().filter(|f| f.path.starts_with(&format!("{AGENT_ROOT}/"))).collect();
        checks["rule_set"] = rules.record();
        checks["schema_names"] = json!({"storages_scanned":storages_scanned,
            "generated_flat_storages_not_scanned":"a generated flat storage's sources are the flat storage generator's output for its declaration (framework code named after its table)"});
        if rules.is_stage() {
            // A stage run reports many mentions (one-word column names, short table names): summarized per name.
            checks["schema_names"]["reported_mentions"] = rules.schema_name_report_summary(agent_files.iter().map(|f| (f.path.as_str(), f.text.as_str())));
            checks["flat_access"] = json!(access);
            checks["workload_module"] = workload_module_report(&stored);
            if rules.is_members() {
                checks["families"] = json!({"plans_scanned":plans_scanned,"rule":PLAN_IS_DATA_RULE.id,
                    "meaning":"the builder/plan.rs of every family instance the engine reads (a derived storage that stores every column of every table) is data"});
            }
        } else {
            let reports: Vec<Value> = agent_files
                .iter()
                .flat_map(|f| rules.schema_name_reports(&f.path, &f.text))
                .map(|x| json!({"file":x.file,"line":x.line,"detail":x.detail}))
                .collect();
            checks["schema_names"]["reported_table_mentions"] = json!(reports);
        }
    }
    let mut evidence = vec![store.put(1, ENGINE_SOURCE_CHECKS_KIND, &checks).map_err(store_error)?];
    for (kind, record) in &candidate.evidence {
        evidence.push(store.put(1, kind, record).map_err(store_error)?);
    }
    let composition = |use_: &StorageComposition<'_>| -> Result<(), String> {
        let name = StorageName::new(use_.name).map_err(|e| e.to_string())?;
        let storage_files = build_files(store, use_.storage_build).map_err(|e| e.to_string())?;
        let engine_files = build_files(store, use_.query_build).map_err(|e| e.to_string())?;
        check_storage_composition(&storage_files, &engine_files, &name).map_err(|e| e.to_string())
    };
    let admission = VerusEngineAdmissionV1 { package: package_id, gate_identity: ENGINE_GATE_IDENTITY.into(), evidence: evidence.clone(), assets: candidate.assets };
    let (admission, version) = records::admit_engine_version(store, &admission, &composition).map_err(record_error)?;
    Ok(EngineAdmission { admission, version, package: package_id, build, tcb, implementations, storage_uses: candidate.uses, evidence })
}

/// R4 (`plan_is_data`) on the uses that are family instances (built from admitted storages, storing every column of
/// every table of `schema`): each one's `builder/plan.rs`, read from its checked build, is scanned with
/// [`scan_plan_source`]; the first findings refuse. Returns the names of the instances whose plan was scanned.
fn refuse_instance_plans(store: &ObjectStore, schema: &[TableDef], files: &[UseFiles]) -> Result<Vec<String>, AdmissionError> {
    let mut scanned = vec![];
    for u in files.iter().filter(|u| u.package.derived_from.is_some() && whole_schema_declaration(schema, &u.declaration)) {
        let build = build_files(store, &records::storage_build(store, &u.package).map_err(record_error)?)?;
        if let Some(plan) = build.iter().find(|f| f.path == FAMILY_PLAN_PATH) {
            refuse_source_findings(&scan_plan_source(&format!("{}/{}", u.name, plan.path), &plan.text), "the plan of a family instance the engine reads")?;
            scanned.push(u.name.to_string());
        }
    }
    Ok(scanned)
}

/// The plan's path in a family instance's storage crate (`gendb_synthesis::storage::family::PLAN_PATH`).
const FAMILY_PLAN_PATH: &str = "builder/plan.rs";

/// `Ok` without findings; otherwise a refusal listing every finding of the files `what` names.
fn refuse_source_findings(findings: &[RefusalFinding], what: &str) -> Result<(), AdmissionError> {
    if findings.is_empty() {
        return Ok(());
    }
    let listed: Vec<String> = findings.iter().map(|x| format!("{}:{}: {}: {}", x.file, x.line, x.rule, x.detail)).collect();
    Err(AdmissionError::refusal(format!("{what} break the engine source rules: {}", listed.join("; "))))
}

/// The fixed entry's implementation record and one per author module.
fn publish_implementations(store: &ObjectStore, build: ContentId, modules: &[CandidateModule], clause_text: ClauseText<'_>) -> Result<Vec<ContentId>, AdmissionError> {
    let entry_items = RECORDED_ENTRY_ITEMS
        .iter()
        .map(|name| {
            let (requires, ensures) = clause_text(ENGINE_ENTRY_SOURCE, name).ok_or_else(|| AdmissionError::tool(format!("engine entry clause text of {name} absent")))?;
            Ok(VerusItemV1 { path: format!("{ENGINE_CRATE_NAME}::gendb_entry::{name}"), requires, ensures })
        })
        .collect::<Result<Vec<_>, AdmissionError>>()?;
    let entry = VerusImplementationV1 { build, module: "gendb_entry".into(), operations: vec![], items: entry_items };
    let mut implementations = vec![store.put(1, records::VERUS_IMPLEMENTATION_KIND, &entry).map_err(store_error)?];
    for module in modules {
        let record = VerusImplementationV1 { build, module: format!("{AGENT_ROOT}/{} ({})", module.file, module.role), operations: vec![], items: module.items.clone() };
        implementations.push(store.put(1, records::VERUS_IMPLEMENTATION_KIND, &record).map_err(store_error)?);
    }
    Ok(implementations)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verus::engine_rules::{ENGINE_RULES, GENERAL_ENGINE_RULES};

    /// The fixed entry the obligations assemble is the one the engine records require, and the TCB of engine packages
    /// names the engine ABI and serving items, every assumption of the engine entry and the three rule sets admission
    /// applies.
    #[test]
    fn engine_records_name_the_fixed_entry_and_its_trusted_base() {
        assert_eq!(ENGINE_ENTRY_IDENTITY, records::VERUS_ENGINE_ENTRY_V1_IDENTITY);
        assert!(ENGINE_ENTRY_SOURCE.contains(ENGINE_ENTRY_IDENTITY));
        for theorem in ENGINE_THEOREMS {
            assert!(ENGINE_ENTRY_SOURCE.contains(&format!("pub proof fn {}(", theorem.trim_start_matches("gendb_entry::"))), "{theorem}");
        }
        let tcb = engine_tcb_record(EngineLine::SchemaEngine).unwrap();
        let ids: Vec<&str> = tcb.items.iter().map(|i| i.id.as_str()).collect();
        for id in ["shim_engine", "host_abi_engine", "engine_serving", "storage_asset_resolution", "verus"] {
            assert!(ids.contains(&id), "{id} missing from {ids:?}");
        }
        for assumption in ENGINE_TRUSTED_ASSUMPTIONS {
            assert!(ids.contains(&format!("entry_assumption:{}", assumption.id).as_str()), "{}", assumption.id);
        }
        let rules: Vec<&str> = tcb.refusal_rules.as_array().unwrap().iter().map(|r| r["id"].as_str().unwrap()).collect();
        assert!(rules.contains(&STATIC_ITEM_RULE.id) && ENGINE_RULES.iter().all(|r| rules.contains(&r.id)) && rules.len() == VERUS_REFUSAL_RULES.len() + 1 + ENGINE_RULES.len());
    }

    /// Without limits a runner's engine job is exactly the request engine cells sent before limits existed; with limits
    /// it is the same job carrying them (`call_limit_ns`, `anon_memory_limit_bytes`).
    #[test]
    fn engine_jobs_carry_the_runner_limits_only() {
        let runner = CandidateRunner { worker: "/nonexistent/worker".into() };
        let uses = [StorageUseInput { name: "flat_t".into(), parts_directory: "/nonexistent/parts".into() }];
        let library = Path::new("/nonexistent/libgendb_engine.so");
        let unlimited = EngineRunner { runner: &runner, library, uses: &uses, access: PartAccess::default(), limits: None, answer_bound: None };
        let asts = vec![b"GSQLAST1".to_vec()];
        let before = WorkerRequest::for_engine_query(library, uses.to_vec(), PartAccess::default(), &asts, vec![64], 4, RANGE_CAPACITY);
        let as_json = |r: &WorkerRequest| serde_json::to_value(r).unwrap();
        assert_eq!(as_json(&unlimited.request(&asts, 64, 4, false)), as_json(&before));
        let limited = EngineRunner { limits: Some(CallLimits::GENERAL_ENGINE), ..unlimited };
        let request = as_json(&limited.request(&asts, 64, 4, true));
        assert_eq!(request["call_limit_ns"], 60_000_000_000u64);
        assert_eq!(request["anon_memory_limit_bytes"], 144u64 << 30);
        let mut without = request.clone();
        without.as_object_mut().unwrap().retain(|key, _| key != "call_limit_ns" && key != "anon_memory_limit_bytes");
        assert_eq!(without, as_json(&before));
    }

    /// With an answer bound, a runner's job carries it exactly when the job compares no answer (an author's own
    /// statement): a compared job (a template with saved answers) is the unbounded job, so its child stores every answer
    /// in full for the comparison. Without one no job carries a bound.
    #[test]
    fn only_jobs_that_compare_no_answer_carry_the_answer_bound() {
        let runner = CandidateRunner { worker: "/nonexistent/worker".into() };
        let uses = [StorageUseInput { name: "flat_t".into(), parts_directory: "/nonexistent/parts".into() }];
        let library = Path::new("/nonexistent/libgendb_engine.so");
        let schema_line = EngineRunner { runner: &runner, library, uses: &uses, access: PartAccess::default(), limits: None, answer_bound: None };
        let general = EngineRunner { limits: Some(CallLimits::GENERAL_ENGINE), answer_bound: Some(AnswerBound::STORED), ..schema_line };
        let asts = vec![b"GSQLAST1".to_vec()];
        assert!(schema_line.request(&asts, 64, 2, false).answer_bound.is_none());
        assert_eq!(general.request(&asts, 64, 2, false).answer_bound, Some(AnswerBound { rows: 100, row_text_bytes: 1 << 20 }));
        let compared = general.request(&asts, 64, 2, true);
        assert_eq!(compared, EngineRunner { answer_bound: None, ..general }.request(&asts, 64, 2, true), "a compared job is stored in full");
        assert!(compared.answer_bound.is_none());
    }

    /// A template without free parameters is a concrete statement: its one visible binding (`v0`, no arguments) names
    /// the statement's binding `statement`; a template's bindings name themselves, and a concrete statement with
    /// another visible binding list keeps the names given (its lookup then fails by name).
    #[test]
    fn a_concrete_statement_is_named_by_its_one_visible_binding() {
        let v = |name: &str, arguments: &[&str]| BenchmarkBinding { name: name.into(), arguments: arguments.iter().map(|a| a.to_string()).collect() };
        assert_eq!(statement_binding_name(&[CONCRETE_BINDING], &[v("v0", &[])], "v0"), CONCRETE_BINDING);
        assert_eq!(statement_binding_name(&["v0", "v1"], &[v("v0", &["1"]), v("v1", &["2"])], "v1"), "v1");
        assert_eq!(statement_binding_name(&[CONCRETE_BINDING], &[v("v0", &[]), v("v1", &[])], "v1"), "v1");
        assert_eq!(statement_binding_name(&[CONCRETE_BINDING], &[v("v0", &[])], "v9"), "v9");
    }

    /// A stage run's TCB names the general line's trusted items and the stage rules (the workload-module rule, the
    /// schema-name rule in its stage form); the line's own records are unchanged.
    #[test]
    fn stage_tcb_names_the_stage_rules() {
        use crate::verus::engine_rules::{SchemaNames, STAGE_ENGINE_RULES};
        let rules = EngineRuleSet::stage_with_names(&["sec", "tpch"], TemplateConstants::default(), SchemaNames::default());
        let stage = tcb_record(rules.line(), rules.rules()).unwrap();
        let general = engine_tcb_record(EngineLine::General).unwrap();
        assert_eq!(stage.items, general.items);
        let ids: Vec<&str> = stage.refusal_rules.as_array().unwrap().iter().map(|r| r["id"].as_str().unwrap()).collect();
        assert!(ids.contains(&"workload_module_statement") && ids.contains(&"schema_name") && ids.len() == VERUS_REFUSAL_RULES.len() + 1 + STAGE_ENGINE_RULES.len(), "{ids:?}");
        assert_eq!(tcb_record(EngineLine::General, EngineLine::General.rules()).unwrap().refusal_rules, general.refusal_rules);
    }

    /// A run of several workloads' TCB names the stage rules and R3-R5, with the same trusted items.
    #[test]
    fn member_tcb_names_the_family_rules() {
        use crate::verus::engine_rules::{SchemaNames, FAMILY_RULES, STAGE_ENGINE_RULES};
        let rules = EngineRuleSet::members_with_names(&["tpch", "sec", "anyschema"], TemplateConstants::default(), SchemaNames::default());
        let members = tcb_record(rules.line(), rules.rules()).unwrap();
        assert_eq!(members.items, engine_tcb_record(EngineLine::General).unwrap().items, "no trusted item is added");
        let ids: Vec<&str> = members.refusal_rules.as_array().unwrap().iter().map(|r| r["id"].as_str().unwrap()).collect();
        assert_eq!(ids.len(), VERUS_REFUSAL_RULES.len() + 1 + STAGE_ENGINE_RULES.len() + FAMILY_RULES.len(), "{ids:?}");
        assert!(["storage_family_required", "plan_is_data", "workload_module_scope", "workload_module_statement"].iter().all(|id| ids.contains(id)), "{ids:?}");
    }

    /// The general line's TCB names the schema-engine line's trusted items plus the per-call limits' watchdog and the
    /// profile sampler, and its own rule set: no whole-statement evaluator rule, the schema-name rule.
    #[test]
    fn general_line_tcb_names_its_rule_set() {
        let schema = engine_tcb_record(EngineLine::SchemaEngine).unwrap();
        let general = engine_tcb_record(EngineLine::General).unwrap();
        let ids = |tcb: &VerusTcbV1| tcb.items.iter().map(|i| i.id.clone()).collect::<Vec<_>>();
        let limits: Vec<String> = TRUSTED_ITEMS_ENGINE_LIMITS.iter().map(|(id, _)| id.to_string()).collect();
        assert!(limits.iter().all(|id| !ids(&schema).contains(id) && ids(&general).contains(id)), "{:?}", ids(&general));
        let general_without_limits: Vec<String> = ids(&general).into_iter().filter(|id| !limits.contains(id)).collect();
        assert_eq!(general_without_limits, ids(&schema));
        let rules: Vec<&str> = general.refusal_rules.as_array().unwrap().iter().map(|r| r["id"].as_str().unwrap()).collect();
        assert!(GENERAL_ENGINE_RULES.iter().all(|r| rules.contains(&r.id)) && rules.len() == VERUS_REFUSAL_RULES.len() + 1 + GENERAL_ENGINE_RULES.len());
        assert!(rules.contains(&"schema_name") && !rules.contains(&"whole_statement_evaluator"), "{rules:?}");
    }
}
