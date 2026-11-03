//! The author workspace of the workload storage session and its generated contract bundle `contract/storage/**`.
//!
//! Workspace layout (paths the prompt and the local tools name):
//! - `storages/`: where the author writes its storage crates (`<crate>/src/stores/<name>/interface/**`,
//!   `<crate>/src/builder/**`) and their `verus-storage.json`; the `storage_check` tool writes each crate's framework
//!   files; `verus-storages.json` (the submission) lists the storages submitted together;
//! - `diagnostic-queries/<statement>/verus/src/**`: a query crate per workload statement with its statement-level
//!   framework files and an `agent/mod.rs` stub, for diagnostic query crates over the author's storages (never
//!   submitted), and `diagnostic-queries/<statement>/verus-query-example.json`;
//! - `reference/src/**`: the SQLSpec library, `schema.rs` and the fixed entry submodules, read-only, for reading;
//! - `admitted-storages/<name>@<id>/`: read-only interface copies of storages already admitted;
//! - `contract/storage/index.json`: the map of every input below; `contract/storage/{task,workload,union-demand,data,
//!   storages,stored-data,obligations,final-claim,registry,parallel,performance,rules,toolchain,tools,failure-classes,
//!   accounting}.json`, `statements/<statement>/{sql-meaning,demand,parameters,domains,output,tests}.json` +
//!   `annotated-ast.txt` (the same statement files a query author reads), `fixed/{storage_entry,query_entry,stored}.rs`,
//!   `proof-library/**` (with `patterns.json`); when the request declares integrity constraints also `integrity-constraints.json` and
//!   `fixed/storage_entry_v2.rs` (`fixed/query_entry.rs` is then the entry v5, `reference/src/gendb_constraints.rs`
//!   the generated module);
//! - `verus-storage-example.json`, `verus-storages-example.json`, `verus-query-example.json`, `verus-tmp/`,
//!   `local-tool.json`.
//!
//! Every fact is generated from the enforcing code, the statement instances, the prepared capture's metadata (no data
//! is scanned) and the library's records; nothing is specific to a query or a dataset.

use super::common::{self, write};
use super::{StatementView, final_claim, write_agent_stub, write_statement_files};
use crate::controller::author::{CANDIDATE_MANIFEST_RULE, CandidateSubmission};
use crate::controller::layout::NOTES_FILE;
use crate::controller::limits::Limits;
use crate::prompts::policy::{
    CORRECTNESS_OBJECTIVE, IMPLEMENTATION_PROVENANCE_TEXT, PERFORMANCE_OBJECTIVE, RuntimeTarget, SCORE_RULE, STORAGE_CHOICE_TEXT, STORAGE_OBJECTIVE, STORAGE_RULE,
};
use crate::query::QuerySession;
use crate::query::candidate::{QueryManifest, StorageUseDeclaration};
use crate::storage::catalog::write_read_only;
use crate::storage::manifest::StorageManifest;
use crate::storage::policy::{StoredDataPolicy, storage_choices};
use crate::tools::{self, AuthorRole, ToolAction};
use crate::workload::submission::WorkloadSubmission;
use gendb_artifacts::ObjectStore;
use gendb_storage::import::PreparedSource;
use gendb_verification::admission::AdmissionError;
use gendb_verification::obligations::{DeclaredSource, query_statement_check_files};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;
use std::sync::Arc;

/// The contract bundle directory, relative to the workspace.
pub const CONTRACT_DIRECTORY: &str = "contract/storage";
/// `scope` of the prepared context.
pub const SCOPE: &str = "verus_workload_storage";

/// What the workload contract is generated from.
pub struct StorageBriefInputs<'a> {
    /// Every ready statement of the workload (index = the tools' `statement`).
    pub statements: &'a [Arc<QuerySession>],
    pub task: &'a Value,
    pub limits: &'a Limits,
    pub store: &'a ObjectStore,
    /// The run's current prepared capture.
    pub capture: &'a PreparedSource,
    pub hardware: &'a Value,
    pub observed_hardware: &'a Value,
    /// Per statement (same index), the user's runtime targets of its query objective (empty: none).
    pub runtime_targets: &'a [Vec<RuntimeTarget>],
    pub free_bytes: Option<u64>,
    /// The user's storage budget (`data_allowance.live_bytes`): the bound on all serving storage together, if set.
    pub data_allowance: Option<u64>,
    /// The user's stored-data policy.
    pub storage_policy: &'a StoredDataPolicy,
}

/// Generate the workload workspace and contract bundle; returns the prepared context.
pub fn write_workload_contract(workspace_root: &Path, inputs: &StorageBriefInputs) -> Result<Value, AdmissionError> {
    fs::create_dir_all(workspace_root).map_err(AdmissionError::tool)?;
    let root = workspace_root.canonicalize().map_err(AdmissionError::tool)?;
    let contract = root.join(CONTRACT_DIRECTORY);
    fs::create_dir_all(&contract).map_err(AdmissionError::tool)?;
    fs::create_dir_all(root.join("storages")).map_err(AdmissionError::tool)?;
    let first = inputs.statements.first().ok_or_else(|| AdmissionError::tool("a workload storage session needs at least one ready statement"))?;
    let reference = root.join("reference/src");
    let reference_files = query_statement_check_files(&first.statement().instance, &first.statement().identity()).map_err(AdmissionError::tool)?;
    let library: Vec<_> = reference_files.into_iter().filter(|f| !matches!(f.path.as_str(), "lib.rs" | "gendb_entry.rs" | "query.rs" | "gendb_params.rs")).collect();
    for f in &library {
        write_read_only(&reference.join(&f.path), &f.text)?;
    }
    let fixed = common::write_fixed_files(&contract, first.statement())?;
    let constrained = fixed.constrained();
    let final_claim_file = contract.join("final-claim.json");
    write(&final_claim_file, &final_claim(&fixed.query_entry, fixed.query))?;
    if constrained {
        write(&contract.join("integrity-constraints.json"), &common::integrity_constraints(first.statement(), &fixed, &library, &reference))?;
    }
    let statements = write_statements(&root, &contract, inputs, &final_claim_file)?;
    let demands: Vec<(String, DeclaredSource)> = inputs.statements.iter().map(|s| Ok((s.statement().key_v4_id.clone(), s.demand()?))).collect::<Result<_, AdmissionError>>()?;
    let statement_demands: Vec<(usize, &DeclaredSource)> = demands.iter().enumerate().map(|(index, (_, demand))| (index, demand)).collect();
    let storages = common::storages_catalog(inputs.store, inputs.capture, &first.statement().instance.doc.tables, &root, &demands, inputs.storage_policy)?;
    let examples = write_examples(&root)?;
    let search_index = super::search_index::write_search_index(inputs.store, &[], &root, inputs.storage_policy)?;
    let c = |name: &str| contract.join(name);
    write(&c("task.json"), &task(&root, &contract, &examples, inputs.storage_policy, constrained, fixed.nullable))?;
    write(&c("workload.json"), &json!({"format_version":1,"statements":statements,
        "note":"the tools' statement argument is the index; each statement's diagnostic query crate is diagnostic-queries/<index>/verus and its full inputs are files.statement_files (the same files a query author of that statement reads)"}))?;
    write(&c("union-demand.json"), &union_demand(&statement_demands, inputs.capture))?;
    write(&c("data.json"), &data_facts(inputs, &first.statement().instance.doc.tables))?;
    write(&c("storages.json"), &storages)?;
    write(&c("stored-data.json"), &common::stored_data(&fixed.stored, inputs.storage_policy, constrained, fixed.nullable))?;
    write(&c("obligations.json"), &json!({"format_version":1,"storage":common::storage_obligations(&fixed),"query":common::query_obligations(&fixed),
        "note":"your storages are proved against the storage obligations; query authors prove the SQL claims over them using only what `represents` and your readers' ensures state"}))?;
    write(&c("registry.json"), &common::registry_index(constrained))?;
    common::write_proof_library(&contract, &reference, &library)?;
    write(&c("parallel.json"), &common::parallel(&first.worker_counts))?;
    write(&c("performance.json"), &performance(&statements, &first.worker_counts))?;
    write(&c("rules.json"), &common::rules())?;
    write(&c("toolchain.json"), &common::toolchain_file(&root, &root.join("diagnostic-queries/0/verus"))?)?;
    write(&c("failure-classes.json"), &common::failure_classes())?;
    let sessions: Vec<&QuerySession> = inputs.statements.iter().map(|s| s.as_ref()).collect();
    write(&c("tools.json"), &common::tools_file(AuthorRole::WorkloadStorage, &sessions, &first.worker_counts, false))?;
    write(&c("validation.json"), &common::validation(AuthorRole::WorkloadStorage, &sessions))?;
    write(&c("accounting.json"), &common::accounting(inputs.limits))?;
    write(&c("index.json"), &index(&root, &contract, inputs, constrained))?;
    let mut context = context(&root, &contract, inputs, &statements, &search_index);
    context["storage_budget"] = common::storage_budget(inputs.store, inputs.capture, &first.statement().instance.doc.tables, inputs.storage_policy, inputs.data_allowance, &c("storage-budget.json"))?;
    if constrained {
        context["integrity_constraints"] = common::constraints_fact(first.statement(), &contract.join("integrity-constraints.json"));
    }
    Ok(context)
}

/// Per statement: its contract files (`statements/<index>/`), its diagnostic query crate (statement-level framework
/// files, an `agent/mod.rs` stub and an example manifest over a workspace storage) and its summary record.
fn write_statements(root: &Path, contract: &Path, inputs: &StorageBriefInputs, final_claim_file: &Path) -> Result<Vec<Value>, AdmissionError> {
    let mut records = vec![];
    for (index, session) in inputs.statements.iter().enumerate() {
        let statement = session.statement();
        let diagnostic = root.join(format!("diagnostic-queries/{index}"));
        let src = diagnostic.join("verus/src");
        let framework = query_statement_check_files(&statement.instance, &statement.identity()).map_err(AdmissionError::tool)?;
        for f in framework.iter().filter(|f| f.path != "lib.rs" && f.path != "gendb_entry.rs") {
            write_read_only(&src.join(&f.path), &f.text)?;
        }
        write_agent_stub(&src, final_claim_file)?;
        let files = contract.join(format!("statements/{index}"));
        write_statement_files(&files, &StatementView { session, framework: &framework, src: &src }, inputs.capture, inputs.storage_policy)?;
        let example = diagnostic.join("verus-query-example.json");
        write(&example, &json!(diagnostic_query_example()))?;
        let demand = session.demand()?;
        records.push(json!({"index":index,"sql":statement.sql,"parameters":statement.declaration_json(),"statement_key":statement.key_v4_id,
            "admission_bindings":statement.bindings.iter().map(|b| &b.texts).collect::<Vec<_>>(),
            "demand":demand.tables.iter().map(|t| json!({"table":t.name,"columns":t.columns.iter().filter(|c| !c.row_count_only).map(|c| &c.name).collect::<Vec<_>>(),
                "row_count_only":t.columns.iter().all(|c| c.row_count_only)})).collect::<Vec<_>>(),
            "objective":statement_objective(session, inputs.runtime_targets.get(index).map_or(&[], Vec::as_slice)),
            "tiny_cases":if session.preflight.validation.formal { json!("not_run: validation policy formal_proofs (validation.json)") } else { json!(session.preflight.cases.len()) },
            "tiny_case_meaning":if session.preflight.constraints_assumed { json!("certified cases only: statement_files.tests tiny_cases.certification counts the generated, certified and skipped cases") } else { Value::Null },
            "statement_files":{"directory":files,"sql_meaning":files.join("sql-meaning.json"),"annotated_ast":files.join("annotated-ast.txt"),"demand":files.join("demand.json"),
                "parameters":files.join("parameters.json"),"domains":files.join("domains.json"),"output":files.join("output.json"),"tests":files.join("tests.json")},
            "diagnostic_query":{"crate":diagnostic.join("verus"),"module_root":src.join("agent/mod.rs"),"query_module":src.join("query.rs"),"manifest_example":example}}));
    }
    Ok(records)
}

/// The example manifest of a diagnostic query crate: the crate next to it, reading one storage of the workspace.
pub(super) fn diagnostic_query_example() -> QueryManifest {
    let mut example = QueryManifest::example();
    example.storage_uses = vec![StorageUseDeclaration {
        name: "<storage name>".into(),
        admitted: None,
        workspace: Some("../../storages/<name>/verus-storage.json".into()),
        family: None,
    }];
    example
}

/// A statement's query objective as its query author receives it: the kind, the benchmark bindings (names and argument
/// texts) and the user's runtime targets.
fn statement_objective(session: &QuerySession, targets: &[RuntimeTarget]) -> Value {
    if !session.performance {
        return json!({"kind":CORRECTNESS_OBJECTIVE});
    }
    let statement = session.statement();
    let bindings: Vec<Value> = statement.benchmark.iter().map(|&b| json!({"name":statement.bindings[b].name,"arguments":statement.bindings[b].texts})).collect();
    json!({"kind":PERFORMANCE_OBJECTIVE,"benchmark_bindings":bindings,"runtime_targets":targets})
}

/// What the statements' query authors will be measured on, and how a diagnostic query is timed (`performance.json`).
fn performance(statements: &[Value], worker_counts: &[usize]) -> Value {
    let protocol = common::measurement_protocol(worker_counts);
    json!({"format_version":1,
        "statements":statements.iter().map(|s| json!({"index":s["index"],"objective":s["objective"]})).collect::<Vec<_>>(),
        "query_objectives":{PERFORMANCE_OBJECTIVE:format!("its query author submits exact verified candidates until the user's guards and the lowest score wins: {SCORE_RULE}"),
            CORRECTNESS_OBJECTIVE:"its query author stops at the first exact verified candidate; timings are descriptive"},
        "runtime_targets":"user-supplied search guidance for a statement's query at one benchmark binding (binding; absent for a concrete statement's one binding) and worker count: the exact hot median of its timed query call, with the provenance and timing scope the user recorded; not measured in this run's timing windows, so no comparison claim follows from it. Absent or empty: no external target",
        "benchmark_bindings":"per statement with the execution-time objective, the argument bindings its query is measured and scored at (every one at every configured worker count); a template's are the user's samples of its parameter domain",
        "what_is_timed":"targets and scores cover only the query call (execution_environment.timed_call) over mapped storage parts. Your storages' stored bytes, asset build time and read requests are measured and recorded separately with each storage and are not part of any target or score; no weighting among them is prescribed (stored-data.json choice)",
        "this_session":"your submission is accepted by the storage rule (verified and built; index.json acceptance), not by speed. Query authors may reuse, extend or replace your storages, including with query-specific variants",
        "diagnostic_queries":"trial and profile of a diagnostic query (task.json diagnostic_query) time a statement's query over your candidate storages under the protocol below; they are diagnostics, not that query's official measurement",
        "execution_environment":protocol["execution_environment"],"profiling":protocol["profiling"],"compiler_controls":protocol["compiler_controls"],
        "host":"data.json hardware (configured worker counts and the observed host)",
        "not_supplied":"no other engine's plans or per-operator times and no data statistics beyond data.json; measure what you need"})
}

/// Per table, the union of the statements' demanded columns: which statements (workload.json index) demand each and
/// whether the capture holds it.
fn union_demand(demands: &[(usize, &DeclaredSource)], capture: &PreparedSource) -> Value {
    let coverage = capture.coverage();
    let captured = |table: &str, ordinal: usize| coverage.iter().any(|(name, ordinals)| name == table && ordinals.contains(&ordinal));
    let mut tables: BTreeMap<String, BTreeMap<(usize, String), BTreeSet<usize>>> = BTreeMap::new();
    let mut row_count_only: BTreeMap<String, BTreeSet<usize>> = BTreeMap::new();
    for (statement, demand) in demands {
        for t in &demand.tables {
            let columns = tables.entry(t.name.clone()).or_default();
            for c in t.columns.iter().filter(|c| !c.row_count_only) {
                columns.entry((c.ordinal, c.name.clone())).or_default().insert(*statement);
            }
            if t.columns.iter().all(|c| c.row_count_only) {
                row_count_only.entry(t.name.clone()).or_default().insert(*statement);
            }
        }
    }
    json!({"format_version":1,"tables":tables.iter().map(|(table, columns)| json!({"table":table,
        "columns":columns.iter().map(|((ordinal, column), by)| json!({"column":column,"ordinal":ordinal,"demanded_by":by,"captured":captured(table, *ordinal)})).collect::<Vec<_>>(),
        "row_count_only_for":row_count_only.get(table)})).collect::<Vec<_>>(),
        "demanded_by":"statement indexes of workload.json (the tools' statement argument)",
        "meaning":"a statement can be served by storages that together store every column and table it demands; one storage may serve several statements. row_count_only_for: statements that enumerate the table without reading a column (they need its row count only). captured: false means the first storage that stores the column imports it once (data.json capture_extension)"})
}

/// The data facts (`common::data_facts`) with the source data facts computed at import (only this role gets them), the host
/// and the user's storage budget.
fn data_facts(inputs: &StorageBriefInputs, schema: &[gendb_frontend::ast::TableDef]) -> Value {
    let mut facts = common::data_facts(inputs.capture, schema);
    facts["source_facts"] = common::source_data_facts(inputs.capture);
    // This role has the source data facts: they replace the "not computed" notes of the shared data facts.
    facts["unavailable"] = json!({"source_facts":"value ranges, estimated distinct counts, sortedness, key density and text byte lengths of every captured column are in source_facts (computed once at import); a column not captured yet has none until the first build that imports it (capture_extension), which adds its facts to source_facts.file",
        "compressibility":"not computed: measure with unverified storage builds (storage_build verification not_run)",
        "how_to_measure":"storage_build/trial/profile over a candidate storage, or read-only scripts over the source files above; never hash or fingerprint whole datasets, never write into the source or capture directories"});
    facts["hardware"] = json!({"configured":inputs.hardware,"observed":inputs.observed_hardware});
    facts["free_bytes_at_prepare"] = json!(inputs.free_bytes);
    facts["data_allowance_bytes"] = json!(inputs.data_allowance);
    facts["data_allowance_meaning"] = json!("the user's storage budget: the bound on all serving storage (CURRENT FACTS, Storage shows what is used and left; null: none)");
    facts
}

/// Example manifests of the three kinds an author writes.
fn write_examples(root: &Path) -> Result<Value, AdmissionError> {
    let storage = root.join("verus-storage-example.json");
    let submission = root.join("verus-storages-example.json");
    let query = root.join("verus-query-example.json");
    write(&storage, &json!(StorageManifest::example()))?;
    write(&submission, &json!(WorkloadSubmission::example()))?;
    write(&query, &json!(QueryManifest::example()))?;
    Ok(json!({"storage":storage,"submission":submission,"diagnostic_query":query}))
}

fn task(root: &Path, contract: &Path, examples: &Value, policy: &StoredDataPolicy, constrained: bool, nullable: bool) -> Value {
    let mut task = json!({"format_version":1,
        "task":"Design, write and prove storages for this workload: for each, a builder (src/builder/**) over the delivered source columns and an interface (src/stores/<name>/interface/**) with the representation relation `represents(parts, rels)` the builder proves and readers over StoredParts extents that query authors call. Submit them together in a verus-storages.json",
        "you_own":root.join("storages"),"required_items":gendb_verification::obligations::STORAGE_AUTHOR_OBLIGATIONS,
        "you_choose":format!("{}; which columns and tables each storage stores, how many storages; every specification, lemma and proof", storage_choices(policy.kind())),
        "storage_policy":"stored-data.json storage_policy: what stored parts may hold under this run's policy; under physical_only each column's values are stored once and each manifest declares data_policy per part ({part, table, kind, columns, why})",
        "choice":STORAGE_CHOICE_TEXT,
        "complete_lossless_storage":"every column of every table is stored at least once by the storages you submit together (under storage_policy physical_only exactly once: one base_payload copy per column): columns the workload uses in layouts optimized for execution, the others compressed for space; all lossless, proved and counted in the storage budget, so the original source data can be deleted. The framework checks that the submitted storages together cover every column of every table",
        "one_submission":"the first submission whose storages all verify and build is admitted and ENDS this session: there is no later submission to improve it. Compare your candidate layouts with the tools (local jobs are unlimited diagnostics and never count as submissions) and submit only the storages you chose",
        "workflow":["read the statements (workload.json and each statement's files), union-demand.json and data.json; decide which tables and columns each storage stores and how",
            "write candidate storages under storages/ (a verus-storage.json and its crate each); storage_check writes the framework files, storage_verify checks the proof while you work",
            "storage_build each candidate unverified first (verification: \"not_run\") to compare sizes, build times and diagnostic query times; then verified whole: its asset built once over the prepared data (stored bytes, canonical column bytes, build time), and over every tiny input when the validation policy runs them (validation.json)",
            "read each statement's query objective and runtime targets (performance.json); where read or query cost matters to your choice, run a diagnostic query crate of a statement over a candidate (diagnostic_query) with trial/profile and compare requested bytes, stored bytes and hot medians across candidates",
            "choose; state the measured or expected costs in each manifest's layout.choice (and each part's kind and columns in data_policy under storage_policy physical_only); submit verus-storages.json with the chosen storages"],
        "diagnostic_query":{"what":"a query crate of one workload statement over your candidate storages, used only to measure; never submitted or admitted",
            "steps":["storage_build the storage it reads (storages/<name>/verus-storage.json)",
                "copy diagnostic-queries/<i>/verus-query-example.json to diagnostic-queries/<i>/verus-query.json and name each storage as {\"name\": <name>, \"workspace\": <its verus-storage.json relative to this manifest>} (or {\"admitted\": <package>} for an admitted one); together they must store the statement's demand (statements/<i>/demand.json)",
                "check with statement: <i> writes the use-specific framework files (lib.rs, gendb_entry**, stores/**) into diagnostic-queries/<i>/verus/src",
                "write src/agent/** with fn query proving the fixed final claim (final-claim.json) from statements/<i>/* and the proof library; verify with statement: <i> (modules while iterating)",
                "trial or profile with statement: <i>, workers (a configured count) and optionally arguments (an admission binding)"],
            "cost":"trial/profile compile the crate first, so a diagnostic query must verify whole: it is a real query proof. Use one when a layout's read or query cost matters to your decision; storage_build alone already reports size and build time"},
        "reader_specifications":"query authors prove the fixed final SQL claim (final-claim.json) using only your `represents` and your readers' requires/ensures. These intermediate specifications are yours; they are useful only if a query can connect them to that fixed claim for every database they bind (a diagnostic query shows whether it can). Nothing requires a particular algorithm, layout or reader",
        "fixed":"the storage entry, the declaration generated from your manifest's stored columns and every framework file are regenerated at freeze; edited workspace copies are never used",
        "manifests":{"storage":{"schema":common::manifest_schema(constrained, nullable),"example":examples["storage"]},"submission":{"schema":WorkloadSubmission::schema(),"example":examples["submission"]},
            "diagnostic_query":{"schema":QueryManifest::schema(),"example":examples["diagnostic_query"],
                "use":"per statement, diagnostic-queries/<i>/verus-query-example.json is the example over a workspace storage"},
            "rule":CANDIDATE_MANIFEST_RULE},
        "readability":"storages are published and reused by other authors: name parts and readers after what they hold; state layout, units and invariants in a short header per module; explain proof steps that are not obvious"});
    if constrained {
        task["declared_integrity_constraints"] = json!({"file":contract.join("integrity-constraints.json"),
            "choice":"per storage, set uses_declared_constraints: true when its builder needs the request's declared constraints (storage entry v2, precondition source_witnessed; required items obligations.json storage.storage_entry_v2.author_items); the storage then applies only to runs with exactly these declarations. Without it (default) the storage uses the entry v1 and applies in every run",
            "queries":"every query crate of this run (entry v5) assumes the declarations whichever storages it reads"});
    }
    task
}

fn index(root: &Path, contract: &Path, inputs: &StorageBriefInputs, constrained: bool) -> Value {
    let c = |name: &str| contract.join(name);
    let mut index = json!({"format_version":1,"scope":SCOPE,
        "task":"Design, write and prove the workload's shared storages (contract task.json); query authors then implement each statement over them",
        "statements":inputs.statements.iter().map(|s| json!({"sql":s.statement().sql,"statement_key":s.statement().key_v4_id})).collect::<Vec<_>>(),
        "read_order":["task","validation","workload","statement_files","union_demand","data","performance","stored_data","obligations","final_claim","storages","registry","proof_patterns","proof_library","tools"],
        "inputs":{"task":c("task.json"),"validation":c("validation.json"),"workload":c("workload.json"),"statement_files":c("statements"),"union_demand":c("union-demand.json"),"data":c("data.json"),"storages":c("storages.json"),
            "stored_data":c("stored-data.json"),"obligations":c("obligations.json"),"final_claim":c("final-claim.json"),"registry":c("registry.json"),"fixed":c("fixed"),
            "proof_library":c("proof-library/index.json"),"proof_patterns":c("proof-library/patterns.json"),"parallelism":c("parallel.json"),"performance":c("performance.json"),"source_rules":c("rules.json"),
            "toolchain":c("toolchain.json"),"tools":c("tools.json"),"failure_classes":c("failure-classes.json"),"accounting":c("accounting.json"),
            "reference_sources":root.join("reference/src"),"diagnostic_queries":root.join("diagnostic-queries"),"your_storages":root.join("storages")},
        "commands":{"tools":format!("mcp__{}__{{{}}} (tools.json)", tools::SERVER_NAME, ToolAction::ALL.map(ToolAction::name).join(",")),
            "api_lookup":common::api_lookup(contract),
            "direct_verify":"toolchain.json storage_crate.verify (after storage_check wrote the framework files; module-scoped diagnostic runs: toolchain.json scoped_verify through the foreground helper toolchain.json direct_verus); query_crate.verify for diagnostic-queries/0 (replace the crate directory for another statement)"},
        "output":{"submission":CandidateSubmission::schema(),"manifest":WorkloadSubmission::schema(),"rule":CANDIDATE_MANIFEST_RULE},
        "acceptance":STORAGE_RULE,
        "framework_source":"read your crates' framework files, reference/src and contract fixed/** freely: they are the authority (look items up with commands.api_lookup first, then read the regions you need). Host and controller source is not needed and is not an input",
        "input_boundary":"your task inputs are this workspace, the files mapped above and the prepared data they name; the pinned toolchain (including vstd sources), standard system tools and hardware diagnostics are available. Other GenDB runs, scratch directories, tests, fixtures and repository source are not inputs: do not read, list or search them (every tool call is recorded and audited)",
        "implementation_provenance":IMPLEMENTATION_PROVENANCE_TEXT});
    if constrained {
        index["inputs"]["integrity_constraints"] = json!(c("integrity-constraints.json"));
        index["read_order"].as_array_mut().expect("a list").insert(2, json!("integrity_constraints"));
    }
    index
}

fn context(root: &Path, contract: &Path, inputs: &StorageBriefInputs, statements: &[Value], search_index: &Path) -> Value {
    json!({"scope":SCOPE,"authoring":"verus_rust_storage","task":inputs.task,
        "statements":statements.iter().map(|s| json!({"index":s["index"],"sql":s["sql"],"parameters":s["parameters"],"statement_key":s["statement_key"],"demand":s["demand"],"objective":s["objective"]})).collect::<Vec<_>>(),
        "source_version":inputs.capture.source_snapshot(),"hardware":inputs.hardware,"observed_hardware":inputs.observed_hardware,
        "limits":inputs.limits.active(),"objective":{"kind":STORAGE_OBJECTIVE,"rule":STORAGE_RULE},"storage_policy":inputs.storage_policy.author_view(),
        "performance":{"free_bytes_at_prepare":inputs.free_bytes,"file":contract.join("performance.json"),
            "worker_counts":inputs.statements.first().map(|s| s.worker_counts.clone()),"worker_count_meaning":"the maximum a call may use, not a requirement (parallel.json)"},
        "files":{"workspace":root,"author_contract":contract.join("index.json"),"your_storages":root.join("storages"),"data":contract.join("data.json"),
            "workload":contract.join("workload.json"),"union_demand":contract.join("union-demand.json"),"notes":root.join(NOTES_FILE),"search_index":search_index,
            "toolchain":contract.join("toolchain.json"),"submission_example":root.join("verus-storages-example.json"),
            "full_context":root.parent().map(|p| p.join("context.json"))},
        "local_tools":{"transport":"typed stdio MCP sibling","server":tools::SERVER_NAME,"mcp_context":root.join(tools::CONTEXT_FILE),
            "required_tools":tools::required_tools(),"actions":ToolAction::ALL.iter().map(|a| a.name()).collect::<Vec<_>>()},
        "output":"Return CandidateSubmission whose candidate_manifest is a verus-storages.json inside this workspace; files.author_contract maps every input"})
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn performance_brief_carries_each_statements_targets_and_the_timing_scope() {
        let target = json!({"workers":64,"median_ns":1000,"provenance":"fixture engine, fixture host","timing_scope":"hot query call"});
        let statements = [json!({"index":0,"sql":"SELECT 1","objective":{"kind":PERFORMANCE_OBJECTIVE,"runtime_targets":[target]}}),
            json!({"index":1,"objective":{"kind":CORRECTNESS_OBJECTIVE}})];
        let brief = performance(&statements, &[1, 32, 64]);
        assert_eq!(brief["statements"][0]["objective"]["runtime_targets"][0]["provenance"], "fixture engine, fixture host");
        assert_eq!(brief["statements"][1]["objective"]["kind"], CORRECTNESS_OBJECTIVE);
        assert!(brief["statements"][0].get("sql").is_none(), "the SQL stays in workload.json");
        assert!(brief["what_is_timed"].as_str().unwrap().contains("not part of any target or score"));
        assert!(brief["execution_environment"]["asset_build"].as_str().unwrap().contains("(64)"));
        assert!(brief["query_objectives"][PERFORMANCE_OBJECTIVE].as_str().unwrap().contains(SCORE_RULE));
    }
}
