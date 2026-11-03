//! The author workspace of one query session and its generated contract bundle `contract/verus/**`.
//!
//! Workspace layout (paths the prompt and the local tools name):
//! - `verus/src/**`: the author's query crate; the statement-level framework files written read-only at prepare, the
//!   storage-specific ones (crate root, `stores/**`, the fixed entry) written by the `check` tool for the declared
//!   storage uses; `src/agent/mod.rs` stub;
//! - `contract/verus/index.json`: the map of every input below, the read order, commands and output contract;
//! - `contract/verus/{task,final-claim,sql-meaning,demand,storages,stored-data,obligations,registry,parameters,domains,
//!   output,tests,parallel,rules,toolchain,tools,failure-classes,accounting}.json`, `annotated-ast.txt`,
//!   `fixed/{query_entry,storage_entry,stored}.rs`, `proof-library/{index,patterns}.json` + `proof-library/files/*.json`,
//!   and `performance.json` for that objective; when the request declares integrity constraints also
//!   `integrity-constraints.json` and `fixed/storage_entry_v2.rs` (`fixed/query_entry.rs` is then the entry v5);
//! - `admitted-storages/<name>@<id>/stores/<name>/interface/**`: read-only copies of the admitted storages' interfaces;
//!   `new-storages/`: where the author may create storage crates of its own;
//! - `verus-query-example.json`, `verus-storage-example.json`, `verus-library.json` + `prior-verus-code/` (admitted
//!   library code), `search-index.{json,txt}` + `admitted-code/` (every admitted author source, `search_index`),
//!   `verus-tmp/` (scratch for direct toolchain use), `local-tool.json` (the MCP client's context), and the author's
//!   own `NOTES.md` for the next attempt.
//!
//! Every fact is generated from the enforcing code (fixed entries, obligations, registry, refusal rules, toolchain argv,
//! failure classes, tool schemas), the statement instance and the library's records; nothing is specific to a query.
//! A resumed session writes the same files again from the same inputs.

pub mod common;
mod patterns;
pub mod search_index;
mod sql_meaning;
pub mod storage;

use super::policy::{
    CORRECTNESS_OBJECTIVE, CORRECTNESS_RULE, EarlyStop, FIXED_FLAT_DATA_ACCESS_TEXT, IMPLEMENTATION_PROVENANCE_TEXT, Objective, PERFORMANCE_OBJECTIVE, PERFORMANCE_RULE,
    RuntimeTarget, SCORE_RULE, STORAGE_CHOICE_TEXT,
};
use crate::controller::author::{CANDIDATE_MANIFEST_RULE, CandidateSubmission};
use crate::controller::layout::NOTES_FILE;
use crate::controller::limits::Limits;
use crate::query::QuerySession;
use crate::query::candidate::{EVALUATOR_RULE, QueryManifest, StorageUseDeclaration};
use crate::query::source_items::item_text;
use crate::storage::catalog::write_read_only;
use crate::storage::manifest::StorageManifest;
use crate::storage::policy::StoredDataPolicy;
use crate::tools::{self, AuthorRole};
use common::{quoted_item, write};
use gendb_artifacts::ObjectStore;
use gendb_sqlspec::codec::RunOutcome;
use gendb_storage::import::PreparedSource;
use gendb_verification::admission::execution::CHILD_TIMEOUT_SECONDS;
use gendb_verification::admission::{AdmissionError, PreparedMode, Statement};
use gendb_verification::obligations::{DeclaredSource, FIXED_LINK_DEFINITIONS, PROVED_PROPERTIES, QueryEntry, query_statement_check_files};
use gendb_verification::verus::FrameworkSource;
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

/// The contract bundle directory, relative to the workspace.
pub const CONTRACT_DIRECTORY: &str = "contract/verus";
/// `scope` of the prepared context.
pub const SCOPE: &str = "verus_query_over_stored_data";
/// The crate directory of the workspace (the manifest example's `crate_dir`).
const CRATE_DIRECTORY: &str = "verus";

/// The only storage uses a query manifest may declare under `fixed_flat` (task.json and index.json beside the schema).
const FLAT_STORAGE_USES_RULE: &str = "under fixed_flat every storage use is {\"name\": \"flat_<table>\", \"admitted\": <that storage's package id, storages.json use_as.admitted>}, one per table the statement reads (verus-query-example.json lists them for this statement); a workspace use is refused (fixed_flat_workspace_storage) and any other storage is refused (storage_policy_ineligible)";

/// What the brief is generated from besides the query session.
pub struct BriefInputs<'a> {
    pub session: &'a QuerySession,
    /// The run request's task record and limits.
    pub task: &'a Value,
    pub limits: &'a Limits,
    /// The admitted library (`verus-library.json` lists its implementations).
    pub library: &'a Value,
    /// The admitted library's store (its storages are listed in `storages.json`).
    pub store: &'a ObjectStore,
    /// The run's current prepared capture (storage applicability and assets are for it).
    pub capture: &'a PreparedSource,
    /// The request's hardware record (configured worker counts), recorded verbatim.
    pub hardware: &'a Value,
    /// What the host exposes (CPUs, caches) as observed by the framework.
    pub observed_hardware: &'a Value,
    /// Free bytes of the workspace filesystem at preparation (descriptive).
    pub free_bytes: Option<u64>,
    /// User-supplied runtime targets of the execution-time objective (`session.performance`); empty otherwise.
    pub runtime_targets: &'a [RuntimeTarget],
    /// The user's early stop of the execution-time objective, if set.
    pub early_stop: Option<EarlyStop>,
    /// The user's storage budget (`data_allowance.live_bytes`): the bound on all serving storage together, if set.
    pub data_allowance: Option<u64>,
    /// The user's stored-data policy.
    pub storage_policy: &'a StoredDataPolicy,
}

/// Paths of the workspace, and the statement-level framework files (byte-equal to every query crate's copies).
struct Workspace {
    root: PathBuf,
    crate_dir: PathBuf,
    src: PathBuf,
    contract: PathBuf,
    statement_files: Vec<FrameworkSource>,
}

impl Workspace {
    fn contract_file(&self, name: &str) -> PathBuf {
        self.contract.join(name)
    }
}

/// The framework text of `path` (empty when the crate has no such file).
fn framework_text<'a>(framework: &'a [FrameworkSource], path: &str) -> &'a str {
    framework.iter().find(|f| f.path == path).map_or("", |f| f.text.as_str())
}

/// `<workspace src>/<file>:<line>` of the definition of `fn NAME` in the framework files.
fn definition(framework: &[FrameworkSource], src: &Path, name: &str) -> Value {
    for f in framework {
        for (i, line) in f.text.lines().enumerate() {
            let t = line.trim_start();
            let defines = t.contains(&format!("fn {name}(")) || t.contains(&format!("fn {name}<"));
            let item_line = ["pub", "fn", "open", "closed", "spec", "proof"].iter().any(|p| t.starts_with(p));
            if defines && item_line {
                return json!(format!("{}:{}", src.join(&f.path).display(), i + 1));
            }
        }
    }
    Value::Null
}

/// Generate the workspace and contract bundle; returns the prepared context (the prompt's CURRENT FACTS source).
pub fn write_author_contract(workspace_root: &Path, inputs: &BriefInputs) -> Result<Value, AdmissionError> {
    fs::create_dir_all(workspace_root).map_err(AdmissionError::tool)?;
    let root = workspace_root.canonicalize().map_err(AdmissionError::tool)?;
    let session = inputs.session;
    let statement = session.statement();
    let statement_files = query_statement_check_files(&statement.instance, &statement.identity()).map_err(AdmissionError::tool)?;
    let crate_dir = root.join(CRATE_DIRECTORY);
    let ws = Workspace { src: crate_dir.join("src"), contract: root.join(CONTRACT_DIRECTORY), crate_dir, root, statement_files };
    for f in ws.statement_files.iter().filter(|f| f.path != "lib.rs" && f.path != "gendb_entry.rs") {
        write_read_only(&ws.src.join(&f.path), &f.text)?;
    }
    fs::create_dir_all(&ws.contract).map_err(AdmissionError::tool)?;
    // Under fixed_flat no storage is created: no new-storages/ and no storage manifest example.
    let flat = inputs.storage_policy.is_fixed_flat();
    if !flat {
        fs::create_dir_all(ws.root.join("new-storages")).map_err(AdmissionError::tool)?;
    }
    let module_root = write_agent_stub(&ws.src, &ws.contract_file("final-claim.json"))?;
    let fixed = common::write_fixed_files(&ws.contract, statement)?;
    let constrained = fixed.constrained();
    let demand = session.demand()?;
    let storages = common::storages_catalog(inputs.store, inputs.capture, &statement.instance.doc.tables, &ws.root, &[(statement.key_v4_id.clone(), demand.clone())], inputs.storage_policy)?;
    let query_example = ws.root.join("verus-query-example.json");
    let query_example_manifest = if flat { flat_query_example_manifest(&storages, &demand) } else { query_example_manifest(&storages) };
    write(&query_example, &json!(query_example_manifest))?;
    let storage_example = ws.root.join("verus-storage-example.json");
    if !flat {
        write(&storage_example, &json!(StorageManifest::example()))?;
    }
    let library_file = ws.root.join("verus-library.json");
    write(&library_file, inputs.library)?;
    let search_index = search_index::write_search_index(inputs.store, &[], &ws.root, inputs.storage_policy)?;
    let objective = if session.performance { Objective::Performance } else { Objective::Correctness };

    write(&ws.contract_file("task.json"), &task(&ws, &fixed, &module_root, &query_example, (!flat).then_some(storage_example.as_path())))?;
    write(&ws.contract_file("final-claim.json"), &final_claim(&fixed.query_entry, fixed.query))?;
    if constrained {
        let mut constraints = common::integrity_constraints(statement, &fixed, &ws.statement_files, &ws.src);
        if flat {
            // The flat storages are generated without the opt-in; no storage builder is written in this run.
            constraints["storage"] = json!("the fixed flat storages use storage entry v1 (no uses_declared_constraints opt-in) and you create no storage: only your query crate uses the declarations (query entry v5)");
        }
        write(&ws.contract_file("integrity-constraints.json"), &constraints)?;
    }
    let view = StatementView { session, framework: &ws.statement_files, src: &ws.src };
    write_statement_files(&ws.contract, &view, inputs.capture, inputs.storage_policy)?;
    write(&ws.contract_file("data.json"), &common::query_data_facts(inputs.capture, &statement.instance.doc.tables))?;
    write(&ws.contract_file("storages.json"), &storages)?;
    write(&ws.contract_file("stored-data.json"), &common::stored_data(&fixed.stored, inputs.storage_policy, constrained, fixed.nullable))?;
    let obligations_note = if flat {
        "a query you submit is a query crate; the fixed flat storages are storage crates GenDB generated and verified (their obligations are listed for reference; you create no storage)"
    } else {
        "a query you submit is a query crate; a storage you create is a storage crate (its obligations are the storage author's)"
    };
    write(&ws.contract_file("obligations.json"), &json!({"format_version":1,"query":common::query_obligations(&fixed),"storage":common::storage_obligations(&fixed),
        "note":obligations_note}))?;
    write(&ws.contract_file("registry.json"), &common::registry_index(constrained))?;
    common::write_proof_library(&ws.contract, &ws.src, &ws.statement_files)?;
    write(&ws.contract_file("parallel.json"), &common::parallel(&session.worker_counts))?;
    write(&ws.contract_file("rules.json"), &common::rules())?;
    let mut toolchain = common::toolchain_file(&ws.root, &ws.crate_dir)?;
    if flat {
        // No storage crate is written under fixed_flat: only the query crate's direct commands apply.
        toolchain.as_object_mut().expect("toolchain object").remove("storage_crate");
        let scoped = toolchain["scoped_verify"].as_object_mut().expect("scoped_verify object");
        scoped.remove("storage_modules");
        scoped.insert("same_options_elsewhere".into(), json!("the same scope options can be appended to query_crate.verify when you want JSON output; run it in the foreground as well"));
        toolchain["direct_verus"]["usage"] = json!("direct-verus.sh query CRATE_DIR [rust_verify options]: the pinned rust_verify on CRATE_DIR/src/lib.rs with the environment and options of query_crate.verify, human-readable diagnostics instead of JSON, run from this directory");
    }
    write(&ws.contract_file("toolchain.json"), &toolchain)?;
    write(&ws.contract_file("failure-classes.json"), &common::failure_classes())?;
    write(&ws.contract_file("tools.json"), &common::tools_file(AuthorRole::Query, &[session], &session.worker_counts, flat))?;
    write(&ws.contract_file("validation.json"), &common::validation(AuthorRole::Query, &[session]))?;
    write(&ws.contract_file("accounting.json"), &common::accounting(inputs.limits))?;
    if objective == Objective::Performance {
        write(&ws.contract_file("performance.json"), &performance(&ws, inputs, &library_file))?;
    }
    write(&ws.contract_file("index.json"), &index(&ws, inputs, objective, constrained, &query_example, &library_file))?;
    let mut context = context(&ws, inputs, objective, &query_example, &library_file, &search_index);
    context["storage_budget"] = common::storage_budget(inputs.store, inputs.capture, &statement.instance.doc.tables, inputs.storage_policy, inputs.data_allowance, &ws.contract_file("storage-budget.json"))?;
    if constrained {
        context["integrity_constraints"] = common::constraints_fact(statement, &ws.contract_file("integrity-constraints.json"));
        if flat {
            context["integrity_constraints"]["in_words"] = json!("every query crate of this run uses the fixed entry v5: bound_db assumes these declarations on the whole database; the fixed flat storages do not use them (storage entry v1); the declarations are never checked against the data");
        }
    }
    Ok(context)
}

/// The manifest example: the first applicable admitted storage that alone covers the statement, else a workspace
/// storage placeholder.
fn query_example_manifest(storages: &Value) -> QueryManifest {
    let mut example = QueryManifest::example();
    let covering = storages["storages"].as_array().into_iter().flatten().find(|s| {
        s["applicable"] == true && s["statement_coverage"].as_array().is_some_and(|c| c.iter().all(|c| c["coverage"]["covers"] == true))
    });
    if let Some(storage) = covering {
        example.storage_uses = vec![StorageUseDeclaration {
            name: storage["name"].as_str().unwrap_or_default().to_string(),
            admitted: serde_json::from_value(storage["package"].clone()).ok(),
            workspace: None,
            family: None,
        }];
    }
    example
}

/// The manifest example under `fixed_flat`: one admitted flat storage use per table the statement demands (the
/// newest applicable version of each, as storages.json lists them newest first).
fn flat_query_example_manifest(storages: &Value, demand: &DeclaredSource) -> QueryManifest {
    let mut example = QueryManifest::example();
    example.storage_uses = demand
        .tables
        .iter()
        .filter_map(|table| {
            storages["storages"].as_array().into_iter().flatten().find(|s| s["applicable"] == true && s["tables"][0]["table"] == table.name.as_str())
        })
        .map(|storage| StorageUseDeclaration {
            name: storage["name"].as_str().unwrap_or_default().to_string(),
            admitted: serde_json::from_value(storage["package"].clone()).ok(),
            workspace: None,
            family: None,
        })
        .collect();
    example
}

/// `task.json`; `storage_example`: the storage manifest example, absent under `fixed_flat` (no storage is created).
fn task(ws: &Workspace, fixed: &common::FixedFiles, module_root: &Path, query_example: &Path, storage_example: Option<&Path>) -> Value {
    let mut task = json!({"format_version":1,
        "task":"Write Rust with Verus specifications and proofs in src/agent/** of the query crate so that Verus checks the fixed query entry's final SQL claim for the actual code: a query over stored data (Stores: one StoredParts per storage use) returning the SQL result, the exact SQL error, or Capacity (parallel via fork_join if you like). Choose the storages it reads: admitted storages (storages.json) or storages you create in new-storages/ with the storage tools",
        "you_own":ws.src.join("agent"),"module_root":module_root,
        "required_items":fixed.query.author_obligations,
        "you_choose":"the storages and every intermediate specification (your own normal form, qualifying-row predicate, group accumulators, how stored parts relate to rows through the storages' `represents`), helper contract, loop invariant, lemma and bridge proof from your code to the SQL meaning (spec::eval, spec::order::ordered_ok, denote_body, exec::relational::domain::fits_query). None is generated for you; the link/** toolkit is optional, except the fixed link definitions the final claim is stated with (final-claim.json)",
        "fixed":"every framework file (library, schema.rs, query.rs, stores/** including the copied storage interfaces, gendb_params.rs, gendb_arguments.rs, gendb_abi.rs, gendb_entry.rs and gendb_entry/**, gendb_shim.rs, lib.rs) is regenerated at freeze from the SQL and the declared storage uses; an edited workspace copy is never used",
        "manifest":{"schema":QueryManifest::schema(),"example":query_example,"rule":CANDIDATE_MANIFEST_RULE},
        "new_storage":{"manifest_schema":common::manifest_schema(fixed.constrained(), fixed.nullable),"example":null,"where":ws.root.join("new-storages"),
            "how":["write a storage crate (you own src/stores/<name>/interface/** and src/builder/**) and its verus-storage.json under new-storages/ (data.json says which columns can be stored; a column the capture lacks is imported once)",
                "storage_check writes its framework files into the crate and reports statement coverage; storage_verify iterates on the proof; storage_build verifies and compiles it whole, records it and builds its asset once over the prepared data (sizes, build time)",
                "name it in your query manifest as {\"name\": <name>, \"workspace\": <path of its verus-storage.json relative to the query manifest>} and compare it with admitted storages using trial/profile",
                "keep it: storage_register admits it now as a new version of its name, or submit the query with the workspace use and qualification registers it; either way the checked build and asset are reused, never rebuilt"],
            "when":"a new storage or a variant of an admitted one (other columns, order, blocks, metadata or readers) is an optional choice of yours; reusing admitted storages is equally valid",
            "policy":"stored-data.json storage_policy bounds what its parts may hold; under physical_only each column's values are stored once (add index_keys, permutation or skip metadata parts beside an admitted copy, never a second copy) and its manifest declares data_policy per part ({part, table, kind, columns, why})"},
        "no_privileged_path":EVALUATOR_RULE,
        "readability":"the admitted sources are published and read by people: use meaningful names and units, one purpose per function, and explain invariants, layouts and proof steps that are not obvious from the code",
        "registry":"declare every agent file with a role (entry, reader, kernel, helper) and its items; only the fixed entry's composition is recorded as implementing the SQL statement; your modules are recorded with their checked contracts"});
    if storage_example.is_none() {
        task["manifest"]["storage_uses_under_fixed_flat"] = json!(FLAT_STORAGE_USES_RULE);
        let object = task.as_object_mut().expect("task object");
        object.remove("new_storage");
        object.insert("task".into(), json!("Write Rust with Verus specifications and proofs in src/agent/** of the query crate so that Verus checks the fixed query entry's final SQL claim for the actual code: a query over stored data (Stores: one StoredParts per storage use) returning the SQL result, the exact SQL error, or Capacity (parallel via fork_join if you like). It reads the fixed flat storages of this run (storages.json: one flat_<table> per table, every column a plain array in source row order); you create or change no storage"));
        object.insert("storage".into(), json!({"policy":"fixed_flat (stored-data.json storage_policy: definition, representation, readers, runtime rule)","storages":ws.contract_file("storages.json"),
            "interfaces":"stores/flat_<table>/interface/mod.rs in your crate once check wrote the framework files, and admitted-storages/ copies"}));
        object.insert("you_choose".into(), json!("every runtime algorithm, plan, parallelism and compiler control, and every intermediate specification (your own normal form, qualifying-row predicate, group accumulators, how stored parts relate to rows through the flat storages' `represents`), helper contract, loop invariant, lemma and bridge proof from your code to the SQL meaning (spec::eval, spec::order::ordered_ok, denote_body, exec::relational::domain::fits_query). None is generated for you; the link/** toolkit is optional, except the fixed link definitions the final claim is stated with (final-claim.json)"));
    } else if let Some(example) = storage_example {
        task["new_storage"]["example"] = json!(example);
    }
    if fixed.constrained() {
        task["declared_integrity_constraints"] = json!({"file":ws.contract_file("integrity-constraints.json"),
            "query":"your query crate uses the entry v5: bound_db also assumes the request's declared constraints on the whole database (constraints_hold(declared_db(db))); use them through gendb_constraints.rs and the bridge lemmas",
            "new_storage":"a storage you create may opt in with uses_declared_constraints: true (storage entry v2); it then applies only to runs with exactly these declarations"});
        if storage_example.is_none() {
            task["declared_integrity_constraints"].as_object_mut().expect("object").remove("new_storage");
        }
    }
    task
}

/// The final claim of the run's query entry `entry` (v4, or v5 under declared integrity constraints), whose text is
/// at `query_entry`.
pub(super) fn final_claim(query_entry: &Path, entry: QueryEntry) -> Value {
    let declared = entry == gendb_verification::obligations::QUERY_ENTRY_V5;
    let mut claim = json!({"format_version":1,"file":query_entry,"identity":entry.identity,
        "answer":item_text(entry.source, "pub enum Answer"),
        "items":common::QUERY_CLAIM_ITEMS.iter().map(|n| quoted_item(entry.source, n)).collect::<Vec<_>>(),
        "fixed_link_definitions":{"items":FIXED_LINK_DEFINITIONS,"meaning":"the claim's relations and answer view are stated with these link definitions; they are framework text, byte-compared at admission, and part of the fixed meaning (not optional author specifications)"},
        "in_words":"Total correctness relative to the outcome contract. For every worker count 1..=MAX_WORKERS, every parameter binding in the declared domain (param_domain) and every database of the declared schema in db_wf whose stored relations every storage use's parts represent (bound_db: schema, db_wf and stored_ok), and under the trusted assumptions, the served call terminates and returns exactly one outcome: Ok rows that are an allowed output of the SQL instance (ordered_ok: values and numeric display scales, ORDER BY order with ties in any order, OFFSET/LIMIT with any choice among rows tied at the boundary); SqlError(e) only when the instance's meaning is exactly the error e; or Capacity only when the database is outside the capacity domain (!fits_query of the canonical evaluation: some intermediate, or the absolute mass of a SUM/AVG, is not machine-representable; this is about value sizes, never available memory). Arguments outside the declared domain get ParamRefused and a worker count outside 1..=MAX_WORKERS gets Refused, both decided by the entry before your code runs. So a call need not return rows. The fixed claim also permits WorkerFailed without a condition (only a really failed join of a worker creates its token); under the trusted assumption worker_failure (the thread runtime reports a failed join only when a worker panics; your workers are verified and no_unwind) it does not occur. Each storage's own theorem (its builder proved `represents` for the database its columns came from) closes the chain. The final theorems (theorems) state what each outcome means, a partial-correctness statement; termination is checked by Verus (a decreases measure on every loop and recursive function of your code, call-graph cycle checks; proved_properties) and is not part of the theorem statement. A process abort (an allocation failure, stack exhaustion, failed thread creation, an unwind on the calling thread) ends the call with no outcome; only the trusted assumption calling_thread_progress (sufficient memory, stack and threads) excludes it, so running out of memory is a process abort, never Capacity or a wrong answer. Under the listed trusted assumptions; no performance claim",
        "per_outcome_obligation":{
            "Ok(Answer::Rows(out))":"ordered_ok(db, query_spec_at(ps), Ok(view_rows(out@))) for EVERY bound db",
            "Ok(Answer::SqlError(e))":"denote_body(db, oq) == Err(e) EXACTLY, the canonical first error",
            "Ok(Answer::Capacity)":"!capacity_domain(db, oq); inside the domain Capacity is unprovable",
            "Err(WorkerFailed(_))":"only with a runtime::WorkerFailure token, which only a failed join inside fork_join creates",
            "Err(InvalidInput | Malformed)":"never"},
        "inputs_you_receive":{"query":"stores_ready(old(stores)@) (some database is bound to the stored parts), param_domain(params@), 1 <= workers <= MAX_WORKERS; the entry passes the Params it bound from the ABI arguments, and the claim is stated at exactly params@"},
        "what_you_cannot_do":[
            {"attempt":"weaken the goal, the domain or capacity_domain","prevented_by":"entry, schema, query, params and the library are framework files, regenerated and byte-compared"},
            {"attempt":"use a storage fact it does not prove","prevented_by":"only a storage's `represents` (and its readers' ensures) relate parts to rows, for every database bound to them"},
            {"attempt":"fabricate WorkerFailed","prevented_by":"private token of gendb_entry::runtime"},
            {"attempt":"arbitrary SqlError or Capacity","prevented_by":"each needs a proof about denote_body or fits_query for every bound db"},
            {"attempt":"unchecked assumptions","prevented_by":"--no-cheating and the source rules (rules.json)"},
            {"attempt":"call the whole-statement evaluator as the implementation","prevented_by":EVALUATOR_RULE}],
        "trusted_assumptions":entry.trusted_assumptions,
        "theorems":gendb_verification::obligations::QUERY_THEOREMS,
        "proved_properties":PROVED_PROPERTIES});
    if declared {
        claim["in_words"] = json!(claim["in_words"].as_str().unwrap_or_default().replace(
            "(bound_db: schema, db_wf and stored_ok)",
            "(bound_db: schema, db_wf, the request's declared integrity constraints constraints_hold(declared_db(db)) and stored_ok)",
        ) + ". The declared constraints are the user's assumption about the actual data (trusted assumption declared_integrity_constraints, never checked against the data; integrity-constraints.json): if they are false, nothing is claimed for that data");
        claim["what_you_cannot_do"].as_array_mut().expect("a list").push(json!({"attempt":"choose, add or weaken the declared constraints",
            "prevented_by":"gendb_constraints.rs and the entry are framework files generated from the request's declarations and byte-compared at admission"}));
    }
    claim
}

/// One statement as the author inputs describe it: its query session, its statement-level framework files and the
/// `src/` directory of the query crate that carries them (definitions are cited at their paths there).
pub(super) struct StatementView<'a> {
    pub session: &'a QuerySession,
    pub framework: &'a [FrameworkSource],
    pub src: &'a Path,
}

impl StatementView<'_> {
    fn definition(&self, name: &str) -> Value {
        definition(self.framework, self.src, name)
    }
}

/// The per-statement contract files, written into `dir`: `sql-meaning.json`, `annotated-ast.txt`, `demand.json`,
/// `parameters.json`, `domains.json`, `output.json` and `tests.json`. A query author reads its statement's files at the
/// contract root; the workload author reads one set per workload statement.
pub(super) fn write_statement_files(dir: &Path, view: &StatementView, capture: &PreparedSource, policy: &StoredDataPolicy) -> Result<(), AdmissionError> {
    let session = view.session;
    let statement = session.statement();
    fs::create_dir_all(dir).map_err(AdmissionError::tool)?;
    let (tree, environments) = sql_meaning::annotated_tree(&statement.instance.doc, &statement.demand);
    let tree_file = dir.join("annotated-ast.txt");
    fs::write(&tree_file, &tree).map_err(AdmissionError::tool)?;
    write(&dir.join("sql-meaning.json"), &sql_meaning_file(view, &tree_file, environments))?;
    write(&dir.join("demand.json"), &demand_file(session, capture)?)?;
    write(&dir.join("parameters.json"), &parameters(view))?;
    write(&dir.join("domains.json"), &domains(statement, view.framework, view.src))?;
    write(&dir.join("output.json"), &output(session))?;
    write(&dir.join("tests.json"), &tests(session, policy))
}

/// The author module root stub `src/agent/mod.rs` of a query crate (left alone once it exists).
pub(super) fn write_agent_stub(src: &Path, final_claim: &Path) -> Result<PathBuf, AdmissionError> {
    let module_root = src.join("agent/mod.rs");
    if !module_root.exists() {
        fs::create_dir_all(src.join("agent")).map_err(AdmissionError::tool)?;
        fs::write(&module_root, format!("// AUTHOR MODULE ROOT (crate::agent). You own every file under src/agent/.\n// Required item: fn query; its exact obligations: {}\nuse vstd::prelude::*;\n\nverus! {{\n\n}} // verus!\n",
            final_claim.display())).map_err(AdmissionError::tool)?;
    }
    Ok(module_root)
}

fn sql_meaning_file(view: &StatementView, tree_file: &Path, environments: Value) -> Value {
    let statement = view.session.statement();
    let def = |name: &str| view.definition(name);
    json!({"format_version":1,"sql":statement.sql,"parameters":statement.declaration_json(),
        "schema_ddl":statement.directory.join("schema.sql"),"ast_document":statement.directory.join("ast.json"),"query_module":view.src.join("query.rs"),
        "statement":"query.rs: schema_spec(), query_spec_at(ps) (THE meaning; for a statement without free parameters ps is empty and query_spec_at(ps) == query_spec()), param_typed(ps), param_domain(ps), lemma_query_wf_at(ps) (well-typedness at every typed binding). Fixed parameters are already literals in the AST",
        "query_spec_at":quoted_item(framework_text(view.framework, "query.rs"), "query_spec_at"),
        "annotated_ast":{"file":tree_file,
            "format":"one line per AST node, depth first from the root: `<role>: n<id> <Constructor> <fields>  : <static type>  env=E<k> | ctx_len=<c> output=[...]`; `env=E<k>` names the environment an expression/condition/aggregate is evaluated in (positions listed in environments below: `table.column@<Table node id>` for a column of that FROM occurrence, `computed@<node>` for a value computed by a node); a Query node shows its context length and output row. Col(i) reads position i of its node's environment; a correlated reference reads an outer position (ctx first, then the input row). Slots track lineage only: outer-join padding and computed values are defined by the SQL semantics, not by a claim that an output equals a raw base value",
            "environments":environments},
        "meaning":{"ordered_ok":def("ordered_ok"),"denote_body":def("denote_body"),"eval_query":def("eval_query"),"eval_pred":def("eval_pred"),"eval_expr":def("eval_expr"),
            "eval_agg":def("agg_value"),"fits_query":def("fits_query"),"db_wf":def("db_wf"),
            "rule":"ordered_ok(db, oq, Ok(rows)): rows is an allowed result of the statement on db (value AND numeric display scale of every column, ORDER BY order with ties in any order, OFFSET/LIMIT with any choice among tied boundary rows); ordered_ok(db, oq, Err(e)): the meaning is exactly the error e",
            "types":"query_spec_at returns an OrderedQuery; eval_query takes a Query body: ordered correctness goes through ordered_ok(db, oq, ..) / denote_body(db, oq) = eval_query(db, [], oq.body), not by treating the two types as interchangeable"},
        "postgresql":"the VERUS_SQL definitions are written to follow PostgreSQL rules and agree with PostgreSQL on the tested cases; there is no theorem of PostgreSQL equivalence"})
}

fn demand_file(session: &QuerySession, capture: &PreparedSource) -> Result<Value, AdmissionError> {
    let statement = session.statement();
    let doc = &statement.instance.doc;
    let mut tables = vec![];
    for t in &statement.source.tables {
        let declared = &doc.tables[t.table_id];
        let columns: Vec<Value> = t.columns.iter().map(|c| json!({"column":c.name,"source_ordinal":c.ordinal,"row_count_only":c.row_count_only,
            "encoding":sql_meaning::source_encoding(c.ty, &sql_meaning::sql_type_name(&declared.columns[c.ordinal].ty))})).collect();
        tables.push(json!({"table":t.name,"schema_table_id":t.table_id,"rows":capture.row_count(&t.name),"source_version":capture.source_version(&t.name),
            "row_order":capture.row_order_identity(&t.name),"columns":columns}));
    }
    Ok(json!({"format_version":1,"tables":tables,
        "demand":"the columns the statement demands (frontend column demand): every column a Col reads at any depth or whose whole rows are observed (output, DISTINCT, scalar/IN subquery rows); EXISTS observes only row existence. A table enumerated without a demanded column still needs its row count (row_count_only). Your storage uses must together store all of them (storage_does_not_cover_demand otherwise)",
        "binding":"a storage's declaration.rs states stored_relations(db): per stored table, the stored columns of db's table in canonical row order; the claim holds for every database bound to all storage uses; link::source lemma_proj_all_compose projects a stored relation onto the columns you read",
        "source_version_meaning":"file-metadata stamps and capture row-order labels (no content hash); a changed source makes assets built for the old version inapplicable",
        "declared_schema":statement.directory.join("schema.sql"),
        "statistics":"row counts above; every schema column and whether it can be stored are in data.json. What you know about the values comes from the storages' contracts and descriptions (storages.json); measure anything else with trial/profile"}))
}

fn parameters(view: &StatementView) -> Value {
    let statement = view.session.statement();
    let framework = view.framework;
    let params = framework_text(framework, "gendb_params.rs");
    let query = framework_text(framework, "query.rs");
    json!({"format_version":1,"declaration":statement.declaration_json(),"free_parameters":statement.free_json(),"concrete":statement.concrete(),
        "file":view.src.join("gendb_params.rs"),"params_struct":item_text(params, "pub struct Params"),"params_view":item_text(params, "impl View for Params"),
        "param_domain":quoted_item(query, "param_domain"),"param_typed":quoted_item(query, "param_typed"),
        "abi":{"QueryArg":item_text(framework_text(framework, "gendb_arguments.rs"), "pub enum QueryArg"),
            "slot_order":"ascending placeholder index of the FREE parameters; fixed parameters are literals in query.rs and not arguments"},
        "admission_bindings":statement.bindings,"benchmark_bindings":benchmark_bindings(statement),"refusal_probes":statement.refusal_probes,
        "binding_rule":"the entry's verified bind_params decides param_domain on the ABI arguments (ParamRefused before your code otherwise) and passes Params whose view is the binding ps of the claim; your query must be correct for EVERY ps with param_domain(ps), not only the admission or benchmark bindings (benchmark bindings are where the execution-time objective measures; admission bindings, which include them, are tests)",
        "host_conversion":"request texts are converted exactly (numeric: at most the declared scale's fractional digits, never rounded; integers in range; dates YYYY-MM-DD); inexact texts are refused by the host before execution"})
}

/// `domains.json` of `statement`, citing definitions in its framework files as written under `src`.
fn domains(statement: &Statement, framework: &[FrameworkSource], src: &Path) -> Value {
    let def = |name: &str| definition(framework, src, name);
    let mut domains = json!({"format_version":1,
        "input_domain":{"db_wf":def("db_wf"),"meaning":"db.schema == schema_spec() and db_wf(db): types, NOT NULL, value ranges, text validity. Integrity constraints (PK/FK/CHECK, constraints_hold) are NOT assumed by the claim",
            "in_domain":"gendb_source::in_domain(tables(v)): every delivered value lies in its declared column's domain; the entry decides it on the actual columns before build (InvalidInput otherwise), so build receives it as a precondition"},
        "capacity_domain":{"definition":"gendb_entry::capacity_domain(db, oq) = exec::relational::domain::fits_query(db, Seq::empty(), oq.body)","fits_query":def("fits_query"),"sum_mass_fits":def("sum_mass_fits"),
            "one_sided":"Capacity => !capacity_domain. Outside the domain you may still answer Ok (always an allowed SQL result) or SqlError (only the meaning's exact error). Inside it, the corollary gives Ok or the exact SqlError whenever no worker failed",
            "statement":sql_meaning::domain_notes(&statement.instance.doc)},
        "sql_errors":"SqlError(e) must be the meaning's exact error: spec::value::SqlError and the evaluation order in spec::eval decide which error is first",
        "authority":"the definitions in your crate (spec/**, exec/relational/domain.rs, exec/domain.rs, exec/aggs/avg.rs); this summary is descriptive"});
    if let Some(declared) = &statement.integrity_constraints {
        domains["input_domain"]["meaning"] = json!("db.schema == schema_spec(), db_wf(db): types, NOT NULL, value ranges, text validity; and the request's declared integrity constraints on the whole database: constraints_hold(declared_db(db)) (crate::gendb_constraints), assumed by bound_db of the entry v5");
        domains["input_domain"]["declared_integrity_constraints"] = json!({"trust":declared.trust,
            "basis":"the user's declaration about the full source tables; never checked against the data; if false, nothing is claimed for that data",
            "declarations":declared.declarations,"module":src.join("gendb_constraints.rs"),"constraints_hold":def("constraints_hold"),
            "details":"integrity-constraints.json in the contract directory (the query author's index.json inputs.integrity_constraints; the workload author's contract root): spec positions, bridge lemmas, projection rule, storage opt-in"});
    }
    domains
}

fn output(session: &QuerySession) -> Value {
    let doc = &session.statement().instance.doc;
    let window = &session.preflight.window;
    let outputs: Vec<Value> = doc.output.names.iter().enumerate().map(|(i, name)| {
        let c = &doc.output.columns[i];
        json!({"position":i,"name":name,"pg_type":doc.output.pg_types.get(i),"type":format!("{:?}", c.ty),"nullable":c.nullable,"dscale":c.dscale,"dscale_exact":c.dscale_exact})
    }).collect();
    json!({"format_version":1,
        "answer":"Answer::Rows(Vec<Vec<EVal>>) (crate::exec::value::EVal, one inner Vec per output row, columns in output order; view_rows maps it to a Relation), Answer::SqlError(SqlError) or Answer::Capacity",
        "outputs":outputs,"order_by":window.keys.iter().map(|(c, d, n)| json!({"output":c,"desc":d,"nulls_first":n})).collect::<Vec<_>>(),
        "offset":window.offset,"limit":window.limit,
        "ordering":"rows sorted by the ORDER BY keys (text in byte order, numbers by value); rows equal on every ORDER BY key may appear in any order; then OFFSET/LIMIT with any choice among rows tied at the boundary (spec::order::ordered_ok)",
        "values":"every value is the VERUS_SQL value including the numeric display scale (EVal::Num { coeff, scale }); exec/** has verified helpers for numeric division, sums, ordering and slicing (exec::relational::order, link::query exec_sum_out, exec_count_out, exec_avg_finalize)"})
}

fn label_name(label: &RunOutcome) -> &'static str {
    match label {
        RunOutcome::Rows(rows) if rows.is_empty() => "value_empty",
        RunOutcome::Rows(_) => "value_rows",
        RunOutcome::SqlError(_) => "sql_error",
        RunOutcome::Capacity => "outside_capacity_or_refused",
        _ => "other",
    }
}

/// `tests.json`: what is tested at admission besides the proof; `policy` says how the storage assets are obtained.
fn tests(session: &QuerySession, policy: &StoredDataPolicy) -> Value {
    let assets = if policy.is_fixed_flat() {
        "the prepared flat storage assets (reused; a missing one is refused, flat_storage_not_prepared, never built)"
    } else {
        "the storage assets over the prepared data (admitted assets reused; a missing one built once by its storage library)"
    };
    let preflight = &session.preflight;
    let statement = &preflight.statement;
    if preflight.validation.formal {
        let benchmark: Vec<Value> = statement.benchmark.iter().map(|&b| json!({"binding":statement.bindings[b].name,"arguments":statement.bindings[b].texts,
            "saved_answers":preflight.validation.answers_at(b).iter().map(|a| json!({"engine":a.engine,"rows":a.rows.len()})).collect::<Vec<_>>()})).collect();
        return json!({"format_version":1,"policy":preflight.validation.record(),
            "note":"validation policy formal_proofs: the whole-crate Verus check against the fixed final claim is the correctness claim; no tiny cases or reference engine run (validation.json)",
            "admission_bindings":statement.bindings,"full_data_bindings":benchmark,
            "parameter_refusals":"at evaluation, each refusal probe (just outside a declared bound) must return ParamRefused from the verified entry",
            "preflight":{"statement_check":preflight.framework_check["verification"],"capture_readiness":preflight.readiness},
            "evaluation":format!("whole-crate verify+compile (0 errors); {assets}; the query at every benchmark binding and configured worker count (1 warm + 3 hot), each result compared with that binding's saved answers of other engines where given (agreement rules in validation.json); parameter refusal probes. The generated domain bindings are not run on the full data")});
    }
    let per_binding: Vec<Value> = statement.bindings.iter().enumerate().map(|(i, b)| match session.references.get(i) {
        Some(Ok(exact)) => json!({"binding":b.name,"arguments":b.texts,"prepared_reference":"exact","rows":exact.rows.len()}),
        Some(Err(reason)) => json!({"binding":b.name,"arguments":b.texts,"prepared_reference":"none","reason":reason.to_string()}),
        None => json!({"binding":b.name,"prepared_reference":"absent"}),
    }).collect();
    let mut label_counts = BTreeMap::<&str, usize>::new();
    for label in preflight.labels.iter().flatten() {
        *label_counts.entry(label_name(label)).or_default() += 1;
    }
    let reference_limits = if preflight.reference_wraps_integers {
        json!("the statement has integer arithmetic: DataFusion wraps integer overflow where PostgreSQL/VERUS_SQL raise 22003; an exact 22003 where DataFusion has rows is recorded status-only")
    } else {
        json!("none known")
    };
    let certification = (preflight.constraints_assumed).then(|| {
        let c = &preflight.case_certification;
        json!({"generated":c["generated"],"certified":c["certified"],"certified_with_rows":c["certified_with_rows"],"skipped_by_reason":c["skipped_by_reason"],
            "skipped":c["skipped"].as_array().map(|s| s.iter().map(|s| json!({"case":s["case"],"reason":s["reason"]})).collect::<Vec<_>>()),
            "warnings":c["warnings"],"reasons":c["reasons"],"meaning":c["meaning"]})
    });
    let mode = match &preflight.prepared {
        PreparedMode::Direct => "DataFusion executes the SQL with its own typed parameter binding (exact-typed outputs)",
        PreparedMode::Rewrite { .. } => "SUM/COUNT rewrite in DataFusion with its own typed parameter binding at each binding + verified finalization (value-dependent display scales)",
        PreparedMode::NotComputed => "none: validation policy formal_proofs (no reference engine runs; results at the benchmark bindings are compared with saved answers of other engines where given)",
    };
    let mut tests = json!({"format_version":1,"note":"tests, never proof; the whole-crate Verus check is the claim",
        "admission_bindings":statement.bindings,"prepared_data":{"reference_limits":reference_limits,"mode":mode,"per_binding":per_binding},
        "tiny_cases":{"record":statement.directory.join("tiny-cases.json"),"cases":preflight.cases.len(),"label_counts":label_counts,"generation":preflight.case_generation,
            "labels":"per case and binding, the verified VERUS_SQL evaluator of the fully fixed instance: value (compare rows exactly), sql_error (the candidate must return exactly that error), outside capacity (any outcome; status only, no exact reference)"},
        "parameter_refusals":"at evaluation, each refusal probe (just outside a declared bound) must return ParamRefused from the verified entry",
        "preflight":{"statement_check":preflight.framework_check["verification"],"capture_readiness":preflight.readiness,
            "references":preflight.evaluators.iter().zip(&statement.bindings).map(|(e, b)| json!({"binding":b.name,"evaluator_build":e.record})).collect::<Vec<_>>()},
        "evaluation":format!("whole-crate verify+compile (0 errors); {assets}; the query at every admission binding and configured worker count (1 warm + 3 hot) compared with the prepared reference; parameter refusal probes; every tiny case (each storage builds its tiny asset from the case, stored columns the statement does not read filled with in-domain fixture values, recorded as synthetic) at every binding and worker count"),
        "status_only":"a comparison without an exact reference (no prepared reference at a binding, inputs outside the capacity domain) records the candidate's outcome and says that its correctness is untested"});
    if let Some(certification) = certification {
        // Under declared constraints only certified cases are listed above and run.
        tests["tiny_cases"]["certification"] = certification;
    }
    tests
}

fn performance(ws: &Workspace, inputs: &BriefInputs, library_file: &Path) -> Value {
    let mut protocol = common::measurement_protocol(&inputs.session.worker_counts);
    let flat = inputs.storage_policy.is_fixed_flat();
    let (assets, stored_data) = if flat {
        protocol["execution_environment"]["asset_build"] = json!("the flat storage assets were prepared once before this run (prepare-flat-storage: the capture's column files, hard-linked or copied; no storage library builds them); no query, trial or evaluation builds an asset, and a use whose asset is missing is refused (flat_storage_not_prepared)");
        ("the prepared flat storage assets (never built for a query)", json!({"free_bytes_at_prepare":inputs.free_bytes,"choice":FIXED_FLAT_DATA_ACCESS_TEXT}))
    } else {
        ("the storage assets (built once per storage and data version, never for the query)",
            json!({"free_bytes_at_prepare":inputs.free_bytes,"data_allowance_bytes":inputs.data_allowance,"choice":STORAGE_CHOICE_TEXT}))
    };
    let build_time = if flat { "" } else { "; storage build time is recorded with the storage, never charged to query time" };
    // Admitted query code is copied under prior-verus-code only when the library has some (stated under fixed_flat,
    // whose library starts without query code; other modes keep their text).
    let no_prior_code = inputs.library["implementations"].as_array().is_none_or(|i| i.is_empty());
    let prior_code = if flat && no_prior_code {
        json!("absent: the library has no admitted query code yet (verus-library.json implementations is empty)")
    } else {
        json!(ws.root.join("prior-verus-code"))
    };
    json!({"format_version":1,"objective":PERFORMANCE_RULE,
        "benchmark_bindings":benchmark_bindings(inputs.session.statement()),
        "benchmark_binding_meaning":"where every submission is measured and scored, at every configured worker count: a concrete statement's one binding, or the user's named bindings of a template (samples of the parameter domain chosen by the user; they are also tested exactly like admission bindings; your proof must still hold for every binding in the declared domain, parameters.json/domains.json)",
        "runtime_targets":inputs.runtime_targets,
        "early_stop":early_stop_record(inputs.early_stop),
        "runtime_target_meaning":"user-supplied search guidance at one benchmark binding (binding; absent for a concrete statement's one binding) and worker count, with the provenance and timing scope the user recorded; not measured in this run's timing windows, so no comparison claim is made from it; empty: optimize the measured runtime of this run without an external target",
        "candidate_protocol":format!("each submission: the whole-crate verify+compile, {assets}, then one child process runs the query over the mapped storage parts at every admission binding and configured worker count (1 warm + 3 hot, each compared with that binding's reference); the benchmark bindings' cells are the measurements; {SCORE_RULE}{build_time}; each child is bounded by the framework's {CHILD_TIMEOUT_SECONDS} s safety bound"),
        "execution_environment":protocol["execution_environment"],"profiling":protocol["profiling"],"compiler_controls":protocol["compiler_controls"],
        "starting_point":{"library":library_file,"code":prior_code,
            "measurements":"the library's admitted_package_evidence.packages_over_stored_data: per earlier package its SQL, storages, implementations and recorded medians with the data they ran on (descriptive, not targets)"},
        "stored_data":stored_data,
        "observed_hardware":inputs.observed_hardware,
        "unchanged":"proof obligations, --no-cheating, the fixed claim, entry and TCB are the same as for correctness; performance never relaxes them"})
}

/// The benchmark bindings of a statement as authors and the policy read them: name, origin and argument texts (slot
/// order), in the measured order.
fn benchmark_bindings(statement: &Statement) -> Value {
    json!(statement.benchmark.iter().map(|&b| {
        let binding = &statement.bindings[b];
        json!({"name":binding.name,"origin":binding.origin,"arguments":binding.texts})
    }).collect::<Vec<_>>())
}

/// performance.json's `early_stop`: the user's rule, or that the search runs to the user's guards.
fn early_stop_record(early_stop: Option<EarlyStop>) -> Value {
    match early_stop {
        Some(stop) => json!({"min_speedup":stop.min_speedup,"rule":stop.rule()}),
        None => json!("not_set: every submission up to the user's submission or cost guard is requested"),
    }
}

/// Every input file of the bundle, by name (`integrity_constraints` only when the request declares them).
fn input_files(ws: &Workspace, objective: Objective, constrained: bool, library_file: &Path, flat: bool) -> Value {
    let c = |name: &str| ws.contract_file(name);
    let mut files = json!({"task":c("task.json"),"validation":c("validation.json"),"final_claim":c("final-claim.json"),"sql_meaning":c("sql-meaning.json"),"annotated_ast":c("annotated-ast.txt"),
        "demand":c("demand.json"),"data":c("data.json"),"storages":c("storages.json"),"stored_data":c("stored-data.json"),"obligations":c("obligations.json"),"registry":c("registry.json"),
        "fixed":c("fixed"),"parameters":c("parameters.json"),"domains":c("domains.json"),"output":c("output.json"),"tests":c("tests.json"),
        "proof_library":c("proof-library/index.json"),"proof_patterns":c("proof-library/patterns.json"),"parallelism":c("parallel.json"),
        "source_rules":c("rules.json"),"toolchain":c("toolchain.json"),"tools":c("tools.json"),
        "failure_classes":c("failure-classes.json"),"accounting":c("accounting.json"),
        "performance":match objective { Objective::Performance => json!(c("performance.json")), Objective::Correctness => json!("not_applicable: correctness objective") },
        "crate":ws.crate_dir,"framework_sources":ws.src,"library":library_file,"new_storages":ws.root.join("new-storages")});
    if constrained {
        files["integrity_constraints"] = json!(c("integrity-constraints.json"));
    }
    if flat {
        files.as_object_mut().expect("object").remove("new_storages");
    }
    files
}

fn index(ws: &Workspace, inputs: &BriefInputs, objective: Objective, constrained: bool, query_example: &Path, library_file: &Path) -> Value {
    let statement = inputs.session.statement();
    let flat = inputs.storage_policy.is_fixed_flat();
    let storages_choice = if flat { "You read the fixed flat storages of this run (stored-data.json) and choose every runtime algorithm, intermediate specification and proof" } else { "You choose the storages (admitted or your own) and every intermediate specification and proof" };
    let mut index = json!({"format_version":1,"scope":SCOPE,
        "task":format!("Write Rust with Verus specifications and proofs (src/agent/** of the query crate) implementing the SQL statement below exactly over stored data, so that Verus checks the fixed query entry's final SQL claim (final-claim.json) for every valid database bound to your storages, every allowed parameter binding and every worker count in [1, MAX_WORKERS]. {storages_choice}"),
        "sql":statement.sql,"parameters":statement.declaration_json(),"statement_key":statement.key_v4_id,
        "read_order":read_order(objective, constrained),
        "inputs":input_files(ws, objective, constrained, library_file, flat),
        "hardware":{"configured":inputs.hardware,"observed":inputs.observed_hardware},
        "commands":{"tools":format!("mcp__{}__{{{}}} (tools.json)", tools::SERVER_NAME, tools::offered_actions(flat).iter().map(|a| a.name()).collect::<Vec<_>>().join(",")),
            "api_lookup":common::api_lookup(&ws.contract),
            "direct_verify":"toolchain.json query_crate.verify (after check wrote the framework files for your storage uses); module- or function-scoped diagnostic runs: toolchain.json scoped_verify through the foreground helper toolchain.json direct_verus","direct_compile":"toolchain.json query_crate.compile"},
        "output":{"manifest_schema":QueryManifest::schema(),"manifest_example":query_example,"submission":CandidateSubmission::schema(),"rule":CANDIDATE_MANIFEST_RULE},
        "acceptance":"one Verus verify+compile of the frozen query crate with 0 errors over the entire crate; then the library meets the checks of the run's validation policy over the storage assets at every configured worker count (validation.json: tests_and_references: allowed results at every admission binding, exact where a reference exists, and the verified evaluator's labels on the generated tiny cases; formal_proofs: the benchmark bindings on the full data, agreeing with the saved answers of other engines where given) and refuses the out-of-domain parameter probes; then the framework registers your new storages and admits the package",
        "framework_source":"read your crates (spec/**, exec/**, bridge/**, link/**, schema.rs, query.rs, stores/**, gendb_params.rs, gendb_arguments.rs, gendb_abi.rs, gendb_entry.rs and gendb_entry/**) and contract fixed/** freely: they are the authority (look items up with commands.api_lookup first, then read the regions you need). Host and controller source is not needed and is not an input",
        "input_boundary":"your task inputs are this workspace (including the crate, its framework files, the admitted storages' interface copies and the admitted code under prior-verus-code), the files mapped above and the prepared data they name; the pinned toolchain (including vstd sources), standard system tools and hardware diagnostics are available. Other GenDB runs, scratch directories, tests, fixtures and repository source are not inputs: do not read, list or search them (every tool call is recorded and audited)",
        "implementation_provenance":IMPLEMENTATION_PROVENANCE_TEXT});
    if flat {
        index["output"]["storage_uses_under_fixed_flat"] = json!(FLAT_STORAGE_USES_RULE);
        index["acceptance"] = json!("one Verus verify+compile of the frozen query crate with 0 errors over the entire crate; then the library meets the checks of the run's validation policy over the flat storage assets at every configured worker count (validation.json: tests_and_references: allowed results at every admission binding, exact where a reference exists, and the verified evaluator's labels on the generated tiny cases; formal_proofs: the benchmark bindings on the full data, agreeing with the saved answers of other engines where given) and refuses the out-of-domain parameter probes; then the framework admits the package");
    }
    index
}

/// The suggested read order of the bundle: declared integrity constraints follow the final claim; the execution-time
/// objective adds its performance brief and parallelism.
fn read_order(objective: Objective, constrained: bool) -> Vec<&'static str> {
    let mut order = vec!["task", "validation", "final_claim", "sql_meaning", "annotated_ast", "demand", "storages", "stored_data", "data", "obligations", "parameters", "domains", "output", "proof_patterns", "proof_library", "tests", "tools"];
    if constrained {
        order.insert(2, "integrity_constraints");
    }
    if objective == Objective::Performance {
        order.extend(["performance", "parallelism"]);
    }
    order
}

/// The prepared context (recorded as the session's `context.json`; the prompt shows its facts).
fn context(ws: &Workspace, inputs: &BriefInputs, objective: Objective, query_example: &Path, library_file: &Path, search_index: &Path) -> Value {
    let statement = inputs.session.statement();
    let flat = inputs.storage_policy.is_fixed_flat();
    let objective_record = match objective {
        Objective::Performance => {
            // `bindings` and `hardware.threads` are the benchmark matrix the policy reads.
            let mut record = json!({"kind":PERFORMANCE_OBJECTIVE,"rule":PERFORMANCE_RULE,"brief":ws.contract_file("performance.json"),
                "bindings":benchmark_bindings(statement)});
            if let Some(stop) = inputs.early_stop {
                // `early_stop` is what the policy reads; its rule text is stated beside it.
                record["early_stop"] = json!(stop);
                record["early_stop_rule"] = json!(stop.rule());
            }
            record
        }
        Objective::Correctness => json!({"kind":CORRECTNESS_OBJECTIVE,"rule":format!("a candidate is accepted when {CORRECTNESS_RULE}; the run then stops. No speedup is required; timings are descriptive only")}),
    };
    let performance = (objective == Objective::Performance).then(|| ws.contract_file("performance.json"));
    let mut context = json!({"scope":SCOPE,"authoring":"verus_rust_over_stored_data","task":inputs.task,"sql":statement.sql,"parameters":statement.declaration_json(),"statement_key":statement.key_v4_id,
        "source_version":inputs.capture.source_snapshot(),"hardware":inputs.hardware,"observed_hardware":inputs.observed_hardware,
        "limits":inputs.limits.active(),"objective":objective_record,
        "runtime_targets":inputs.runtime_targets,"storage_policy":inputs.storage_policy.author_view_for(common::has_nullable_column(&statement.instance.doc.tables)),
        "performance":performance_key_facts(inputs, performance.as_deref()),
        "files":{"workspace":ws.root,"author_contract":ws.contract_file("index.json"),"crate":ws.crate_dir,"agent_module_root":ws.src.join("agent/mod.rs"),
            "notes":ws.root.join(NOTES_FILE),"search_index":search_index,"storages":ws.contract_file("storages.json"),"performance":performance,
            "toolchain":ws.contract_file("toolchain.json"),"manifest_example":query_example,"new_storages":ws.root.join("new-storages"),"library":library_file,
            "full_context":ws.root.parent().map(|p| p.join("context.json"))},
        "local_tools":{"transport":"typed stdio MCP sibling","server":tools::SERVER_NAME,"mcp_context":ws.root.join(tools::CONTEXT_FILE),
            "required_tools":tools::required_tools_of(flat),
            "actions":tools::offered_actions(flat).iter().map(|a| a.name()).collect::<Vec<_>>()},
        "output":"Return CandidateSubmission whose candidate_manifest is a verus-query.json inside this workspace; files.author_contract maps every input"});
    if flat {
        // No storage is created under fixed_flat: the workspace has no new-storages/ directory.
        context["files"].as_object_mut().expect("files").remove("new_storages");
    }
    context
}

/// The key facts of `performance.json` repeated in CURRENT FACTS (authors rarely opened the file): free space, the
/// timing protocol of trials and evaluations, and where the rest is.
fn performance_key_facts(inputs: &BriefInputs, file: Option<&Path>) -> Value {
    json!({"free_bytes_at_prepare":inputs.free_bytes,
        "evaluation_timing":"each benchmark cell: 1 warm + 3 hot calls in one child process, the median hot wall time of one library query call; storage builds, compile, process start and result decoding are excluded; cached pages are never dropped",
        "worker_counts":inputs.session.worker_counts,"worker_count_meaning":"the maximum a call may use, not a requirement (parallel.json)",
        "file":file})
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::query::candidate::REQUIRED_ITEMS;

    #[test]
    fn required_items_match_the_fixed_obligations() {
        use gendb_verification::obligations::{QUERY_ENTRY_V4, QUERY_ENTRY_V5};
        for entry in [QUERY_ENTRY_V4, QUERY_ENTRY_V5] {
            let names: Vec<&str> = entry.author_obligations.iter().map(|i| i.name).collect();
            assert_eq!(names[..REQUIRED_ITEMS.len()], REQUIRED_ITEMS);
            for item in common::QUERY_CLAIM_ITEMS {
                assert_ne!(quoted_item(entry.source, item)["text"], "absent", "{item} is an item of the {}", entry.name);
            }
        }
    }

    #[test]
    fn performance_read_order_adds_its_brief_and_parallelism() {
        assert!(!read_order(Objective::Correctness, false).contains(&"performance"));
        assert!(read_order(Objective::Performance, false).ends_with(&["performance", "parallelism"]));
        assert!(!read_order(Objective::Correctness, false).contains(&"integrity_constraints"));
        assert_eq!(read_order(Objective::Correctness, true)[2], "integrity_constraints");
    }

    #[test]
    fn shell_words_quote_only_when_needed() {
        assert_eq!(common::shell_word("--crate-name=gendb_query"), "--crate-name=gendb_query");
        assert_eq!(common::shell_word("a b"), "'a b'");
    }

    #[test]
    fn source_rules_are_the_scanner_tables() {
        use gendb_verification::verus::{
            ALLOWED_ATTRIBUTES, ALLOWED_EXTERNAL_TRAITS, ALLOWED_VERIFIER_ATTRIBUTES, SUPPORTED_DERIVES, SUPPORTED_MACROS, VERUS_REFUSAL_RULES,
        };
        let rules = common::rules();
        let macros: Vec<String> = SUPPORTED_MACROS.iter().map(|m| format!("{m}!")).collect();
        assert_eq!(rules["supported"]["macros"], json!(macros));
        assert_eq!(rules["supported"]["derives"], json!(SUPPORTED_DERIVES));
        assert_eq!(rules["supported"]["attributes"], json!(ALLOWED_ATTRIBUTES));
        assert_eq!(rules["supported"]["verifier_attributes"], json!(ALLOWED_VERIFIER_ATTRIBUTES));
        assert_eq!(rules["supported"]["external_traits"], json!(ALLOWED_EXTERNAL_TRAITS));
        assert_eq!(rules["refusal_list"].as_array().map(Vec::len), Some(VERUS_REFUSAL_RULES.len()));
    }

    #[test]
    fn diagnostic_query_example_reads_a_workspace_storage() {
        let example = json!(storage::diagnostic_query_example());
        assert_eq!(example["crate_dir"], "verus");
        assert_eq!(example["storage_uses"][0]["workspace"], "../../storages/<name>/verus-storage.json");
        assert!(example["storage_uses"][0].get("admitted").is_none());
    }

    #[test]
    fn column_types_use_their_sql_names() {
        use gendb_frontend::ast::PgType;
        assert_eq!(sql_meaning::sql_type_name(&PgType::Numeric { typmod: Some((15, 2)) }), "numeric(15,2)");
        assert_eq!(sql_meaning::sql_type_name(&PgType::Bpchar { n: Some(1) }), "char(1)");
        assert_eq!(sql_meaning::sql_type_name(&PgType::Varchar { max_chars: None }), "varchar");
    }

    /// The rendered direct-verification helper returns every rust_verify exit at once with its status and output,
    /// and a TERM to the helper stops the verifier's process group. Needs the pinned Verus; scratch under `TMPDIR`.
    #[test]
    #[ignore]
    fn direct_verus_returns_every_exit_with_its_status() {
        use std::process::{Command, Stdio};
        let workspace = std::env::temp_dir().join(format!("direct-verus-check-{}", std::process::id()));
        let crate_dir = workspace.join("crate");
        std::fs::create_dir_all(crate_dir.join("src")).unwrap();
        std::fs::write(crate_dir.join("src/lib.rs"), "use vstd::prelude::*;\nverus! {\npub mod m {\n    use vstd::prelude::*;\n    pub proof fn lemma_ok(x: int) ensures x + 0 == x {}\n}\n}\n").unwrap();
        let toolchain = common::toolchain_file(&workspace, &crate_dir).unwrap();
        let script = PathBuf::from(toolchain["direct_verus"]["script"].as_str().unwrap());
        let run = |options: &[&str]| {
            let start = std::time::Instant::now();
            let output = Command::new(&script).arg("query").arg(&crate_dir).args(options).output().unwrap();
            let text = format!("{}{}", String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr));
            eprintln!("{options:?}: exit {:?} after {:?}\n{text}", output.status.code(), start.elapsed());
            (output.status.code(), text)
        };
        // The Q11 combination: refused at startup, one `Error:` line, no verification summary.
        let (code, text) = run(&["--verify-module", "m", "--verify-function", "lemma_ok"]);
        assert_eq!(code, Some(255));
        assert!(text.contains("Error: When using --verify-function, use --verify-only-module instead of --verify-module"));
        assert!(text.contains("direct-verus: rust_verify exit status 255") && !text.contains("verification results"));
        // An option rust_verify does not know: another early exit in a different spelling.
        let (code, text) = run(&["--no-such-option"]);
        assert!(code.is_some_and(|c| c != 0) && !text.contains("verification results"), "{text}");
        assert!(text.contains(&format!("direct-verus: rust_verify exit status {}", code.unwrap())));
        // The supported function scope.
        let (code, text) = run(&["--verify-only-module", "m", "--verify-function", "lemma_ok"]);
        assert_eq!(code, Some(0), "{text}");
        assert!(text.contains("verification results:: 1 verified, 0 errors") && text.contains("direct-verus: rust_verify exit status 0"));
        // A TERM to the helper stops the recorded group, removes the record and returns the verifier's status.
        let tmp = workspace.join("verus-tmp");
        let mut helper = Command::new(&script).arg("query").arg(&crate_dir).stdout(Stdio::null()).stderr(Stdio::null()).spawn().unwrap();
        // Wait for the helper's group record while watching the helper itself: if it exits first, fail at once
        // (it waited for its verifier before exiting, so only the scratch workspace is left to remove).
        let (record, group) = loop {
            let found = std::fs::read_dir(&tmp).unwrap().flatten().map(|e| e.path()).find(|p| p.extension().is_some_and(|x| x == "pgid"));
            if let Some((record, text)) = found.and_then(|p| std::fs::read_to_string(&p).ok().map(|t| (p, t))).filter(|(_, t)| t.ends_with('\n')) {
                break (record, text.trim().to_string());
            }
            if let Some(status) = helper.try_wait().unwrap() {
                std::fs::remove_dir_all(&workspace).unwrap();
                panic!("the helper exited ({status}) before its process-group record was seen, so the TERM case could not run");
            }
            std::thread::sleep(std::time::Duration::from_millis(10));
        };
        assert!(Command::new("kill").args(["-TERM", &helper.id().to_string()]).status().unwrap().success());
        let status = helper.wait().unwrap();
        assert_eq!(status.code(), Some(143), "the verifier was stopped by TERM");
        assert!(!record.exists());
        let alive = Command::new("kill").args(["-0", "--", &format!("-{group}")]).stderr(Stdio::null()).status().unwrap();
        assert!(!alive.success(), "no process of group {group} remains");
        std::fs::remove_dir_all(&workspace).unwrap();
    }

    /// A statement over p (k) and c (a, k, v), with or without declared constraints (PRIMARY KEYs, a FOREIGN KEY and a
    /// named CHECK), its statement-level framework files and a scratch directory. Only the DDL is used.
    fn statement(declared: bool, name: &str) -> (Statement, Vec<FrameworkSource>, PathBuf) {
        use gendb_artifacts::{ColType, ColumnSpec};
        use gendb_storage::import::{DataFormat, DatasetSpec, TableSpec};
        use gendb_verification::admission::integrity_constraints::{ConstraintDeclaration, IntegrityConstraints, USER_DECLARED};
        let column = |name: &str, ty: ColType| ColumnSpec { name: name.into(), ty, nullable: false };
        let table = |name: &str, fields| TableSpec { name: name.into(), fields, locations: vec![PathBuf::from(format!("{name}.parquet"))], format: DataFormat::Parquet };
        let dataset = DatasetSpec {
            tables: vec![
                table("c", vec![column("a", ColType::I64), column("k", ColType::I64), column("v", ColType::Decimal { p: 15, s: 2 })]),
                table("p", vec![column("k", ColType::I64)]),
            ],
        };
        let constraints = IntegrityConstraints {
            trust: USER_DECLARED.into(),
            declarations: [("c", "PRIMARY KEY (a)"), ("p", "PRIMARY KEY (k)"), ("c", "FOREIGN KEY (k) REFERENCES p (k)"), ("c", "CONSTRAINT v_nonnegative CHECK (v >= 0)")]
                .iter()
                .map(|(t, sql)| ConstraintDeclaration { table: (*t).into(), sql: (*sql).into() })
                .collect(),
        };
        let work = std::env::temp_dir().join(format!("gendb-brief-constraints-{}-{name}", std::process::id()));
        let parser = gendb_frontend::parser::SqlParser::from_environment().unwrap();
        let statement = gendb_verification::admission::prepare_statement(&parser, &dataset, declared.then_some(&constraints), "SELECT k, SUM(v) FROM c GROUP BY k", &[], &[], &[], &work.join("statement"))
            .unwrap_or_else(|r| panic!("{}", r.error));
        let framework = query_statement_check_files(&statement.instance, &statement.identity()).unwrap();
        (statement, framework, work)
    }

    /// Without declarations every author input keeps its unconstrained text (entry v4/v1, no constraints file, the
    /// input domain says constraints are not assumed). With them both roles' inputs name every declaration, the trust
    /// basis, the v5 hypothesis, the v2 opt-in, and every cited definition, lemma and file resolves, so no framework
    /// source has to be searched.
    #[test]
    fn constrained_inputs_name_the_declarations_and_default_inputs_do_not() {
        use gendb_verification::obligations::{QUERY_ENTRY_SOURCE, QUERY_ENTRY_V5_SOURCE, STORAGE_ENTRY_SOURCE, STORAGE_ENTRY_V2_SOURCE};
        let (plain, plain_files, work) = statement(false, "plain");
        let src = work.join("src");
        let default_domains = domains(&plain, &plain_files, &src);
        assert_eq!(default_domains["input_domain"]["meaning"], "db.schema == schema_spec() and db_wf(db): types, NOT NULL, value ranges, text validity. Integrity constraints (PK/FK/CHECK, constraints_hold) are NOT assumed by the claim");
        assert!(default_domains["input_domain"].get("declared_integrity_constraints").is_none());
        let fixed = common::write_fixed_files(&work.join("plain-contract"), &plain).unwrap();
        assert!(!fixed.constrained() && fixed.storage_entry_v2.is_none());
        assert_eq!(std::fs::read_to_string(&fixed.query_entry).unwrap(), QUERY_ENTRY_SOURCE);
        assert_eq!(std::fs::read_to_string(&fixed.storage_entry).unwrap(), STORAGE_ENTRY_SOURCE);
        let claim = final_claim(&fixed.query_entry, fixed.query);
        assert!(!claim["in_words"].as_str().unwrap().contains("integrity constraints") && claim["what_you_cannot_do"].as_array().unwrap().len() == 6);
        assert!(common::storage_obligations(&fixed).get("storage_entry_v2").is_none());
        let registry = common::registry_index(false);
        assert!(registry.get("storage_crate_uses_declared_constraints").is_none());
        assert!(!registry["query_crate"].as_array().unwrap().iter().any(|d| d["name"] == "declared_constraints" || d["name"] == "query_entry_v5"));
        assert!(common::manifest_schema(false, false)["properties"].get("uses_declared_constraints").is_none());
        // Stored columns: the NOT NULL wording unless the schema has a nullable column .
        let columns = |schema: Value| schema["properties"]["tables"]["items"]["properties"]["columns"]["description"].as_str().unwrap().to_string();
        assert!(columns(common::manifest_schema(false, false)).starts_with("stored NOT NULL columns;"));
        assert_eq!(columns(common::manifest_schema(true, true)), crate::storage::manifest::NULLABLE_STORED_COLUMNS);
        let mut nullable = common::manifest_schema(true, true);
        nullable["properties"]["tables"]["items"]["properties"]["columns"]["description"] = columns(common::manifest_schema(true, false)).into();
        assert_eq!(nullable, common::manifest_schema(true, false), "only that description differs");
        for policy in [StoredDataPolicy::Unrestricted, StoredDataPolicy::PhysicalOnly { eligible_storages: vec![] }, StoredDataPolicy::FixedFlat {}] {
            assert_eq!(policy.author_view_for(false), policy.author_view(), "a schema of NOT NULL columns keeps its policy text");
        }
        assert!(StoredDataPolicy::FixedFlat {}.author_view_for(true)["readers"].as_str().unwrap().contains("read_<column>_validity"));

        let (declared, files, work) = statement(true, "declared");
        let src = work.join("src");
        let constrained_domains = domains(&declared, &files, &src);
        let input = &constrained_domains["input_domain"];
        assert!(input["meaning"].as_str().unwrap().contains("constraints_hold(declared_db(db))"));
        assert_eq!(input["declared_integrity_constraints"]["declarations"][2]["sql"], "FOREIGN KEY (k) REFERENCES p (k)");
        assert_eq!(input["declared_integrity_constraints"]["trust"], "user_declared");
        let fixed = common::write_fixed_files(&work.join("declared-contract"), &declared).unwrap();
        assert!(fixed.constrained());
        assert_eq!(std::fs::read_to_string(&fixed.query_entry).unwrap(), QUERY_ENTRY_V5_SOURCE);
        assert_eq!(std::fs::read_to_string(fixed.storage_entry_v2.as_ref().unwrap()).unwrap(), STORAGE_ENTRY_V2_SOURCE);
        let claim = final_claim(&fixed.query_entry, fixed.query);
        assert_eq!(claim["identity"], fixed.query.identity);
        assert!(claim["in_words"].as_str().unwrap().contains("constraints_hold(declared_db(db))"), "{}", claim["in_words"]);
        assert!(claim["trusted_assumptions"].as_array().unwrap().iter().any(|a| a["id"] == "declared_integrity_constraints"));
        let bound_db = claim["items"].as_array().unwrap().iter().find(|i| i["name"] == "bound_db").unwrap();
        assert!(bound_db["body"].as_str().unwrap().contains("constraints_hold(declared_db(db))"), "{bound_db}");
        let query = common::query_obligations(&fixed);
        assert!(query["author_items"][0]["obligation"].as_str().unwrap().contains("constraints_hold(declared_db(db))"));
        let storage = common::storage_obligations(&fixed);
        assert!(storage["author_items"][3]["obligation"].as_str().unwrap().contains("any extra precondition fails"), "v1 builder text unchanged");
        assert!(storage["storage_entry_v2"]["author_items"][3]["obligation"].as_str().unwrap().contains("may require source_witnessed(src@)"));
        assert!(storage["storage_entry_v2"]["claim_items"].as_array().unwrap().iter().all(|i| i["text"] != "absent"));
        let registry = common::registry_index(true);
        let names = |kind: &str| registry[kind].as_array().unwrap().iter().map(|d| d["name"].as_str().unwrap().to_string()).collect::<Vec<_>>();
        assert!(names("query_crate").contains(&"declared_constraints".to_string()) && names("query_crate").contains(&"query_entry_v5".to_string()));
        assert!(!names("query_crate").contains(&"query_entry".to_string()));
        assert!(names("storage_crate").contains(&"storage_entry".to_string()) && names("storage_crate_uses_declared_constraints").contains(&"storage_entry_v2".to_string()));
        assert_eq!(common::manifest_schema(true, false)["properties"]["uses_declared_constraints"]["type"], "boolean");
        let record = common::integrity_constraints(&declared, &fixed, &files, &src);
        let declarations = record["declarations"].as_array().unwrap();
        assert_eq!(declarations.len(), 4);
        let table_id = |name: &str| declared.instance.doc.tables.iter().position(|t| t.name == name).unwrap();
        // Positions within each table's constraints, in declaration order: c's key, p's key, c's foreign key, c's CHECK.
        let spec: Vec<String> = declarations.iter().map(|d| d["spec"].as_str().unwrap().to_string()).collect();
        let (c, p) = (table_id("c"), table_id("p"));
        assert_eq!(spec, [format!("declared_schema()[{c}].constraints[0]"), format!("declared_schema()[{p}].constraints[0]"), format!("declared_schema()[{c}].constraints[1]"), format!("declared_schema()[{c}].constraints[2]")]);
        assert_eq!(declarations[2]["meaning"], json!({"kind":"foreign_key","columns":["k"],"column_positions":[1],"references":{"table":"p","table_id":p,"columns":["k"],"column_positions":[0]},"match_full":false}));
        assert_eq!(declarations[3]["meaning"]["name"], "v_nonnegative");
        for item in record["module"]["items"].as_array().unwrap().iter().chain(record["query"]["bridge_lemmas"].as_array().unwrap()) {
            assert_ne!(item["text"], "absent", "{item}");
        }
        assert_ne!(record["query"]["hypothesis"]["text"], "absent");
        assert_ne!(record["storage"]["precondition"]["text"], "absent");
        for (name, definition) in record["semantics"].as_object().unwrap().iter().filter(|(n, _)| *n != "authority") {
            assert!(definition.as_str().is_some_and(|d| d.contains("spec/constraints.rs:")), "{name}: {definition}");
        }
        assert!(files.iter().any(|f| f.path == "gendb_constraints.rs") && files.iter().any(|f| f.path == "bridge/constraints.rs"));
        assert_eq!(record["trust"]["constraints_digest"], json!(declared.key_v4.constraints_digest()));
        std::fs::remove_dir_all(work.parent().unwrap().join(format!("gendb-brief-constraints-{}-plain", std::process::id()))).ok();
        std::fs::remove_dir_all(&work).ok();
    }

    #[test]
    fn library_roles_mark_the_fixed_link_files() {
        assert!(common::library_role("link/query.rs").contains("fixed meaning"));
        assert!(common::library_role("link/exists.rs").starts_with("optional"));
        assert!(common::library_role("exec/relational/entry.rs").contains("refused"));
    }
}
