//! The general engine line's contract files:
//! what differs from the schema line's bundle (`prompts::engine_contract`), built on its generators so every shared
//! fact stays one text:
//!
//! - `task.json` and `index.json`: the general task, the manifest's general schema
//!   (`EngineManifest::general_schema`: `direction`, `findings`, `next_session`, `base`), the generated flat access and
//!   the run's records (tree, findings, versions, attempts);
//! - `rules.json`: the line's rule set (`EngineRuleSet::record`, `GENERAL_ENGINE_RULES`): the interpreter allowed, the
//!   schema-name rule added;
//! - `failure-classes.json`: the line's refusals and the states of an unfinished cell;
//! - `performance.json`: the interleaved timing against the parent, the score, the call limits, the ladder, the main
//!   line and the sampling profile (`engine::race::RACE_RULE`, `engine::score::SCORE_RULE`,
//!   `engine::profile::PROFILE_METHOD`), and the two evaluation plans (`engine::protocol`: the development evaluation
//!   of every submission, the final evaluation for reporting);
//! - `tools.json`: trials and profiles under the call limits, the sampling profile's result fields;
//! - `budget-rule.json`: the storage budget rule (plain storage only is allowed as is; any storage
//!   change stays within the original data size) at the current scale;
//! - `storage-authoring.md` ([`storage_authoring`]): the reference detail behind the prompt's Storage section (the
//!   generated flat access, how a storage built from admitted ones reads its sources, its interface, the plain-columns
//!   vocabulary, the `data_policy` kinds and every refusal code), so the prompt keeps only the rules;
//! - `data.json`: the budget beside the data facts;
//! - `versions.md`: every version timed at this scale (the per-scale tables of `output::engine::general`) and every
//!   attempt.

use crate::engine::profile::PROFILE_METHOD;
use crate::engine::protocol::{DEVELOPMENT, FINAL};
use crate::prompts::engine_general_sections::{ENGINE_MANIFEST_RULE, STORAGE_AUTHORING_FILE, Shape};
use crate::engine::race::RACE_RULE;
use crate::engine::role::GeneralInputs;
use crate::engine::score::SCORE_RULE;
use crate::engine::submission::{ENGINE_STATIC_ITEM_RULE, EngineManifest};
use crate::engine::tree::{self, VersionTree};
use crate::output::engine::general::{ScaleColumns, scale_markdown};
use gendb_verification::verus::engine_rules::{EngineRuleSet, GENERAL_ENGINE_RULES, SCHEMA_TABLE_MENTION};
use gendb_verification::verus::RefusalRule;
use gendb_registry::{ConstraintMode, CrateKind, WHOLE_SCHEMA_DEFINITIONS, optional_definitions_for};
use gendb_runtime::worker::AnswerBound;
use serde_json::{Value, json};
use std::path::Path;

/// The budget rule's file in the contract.
pub const BUDGET_RULE_FILE: &str = "budget-rule.json";
/// The plain-columns vocabulary (`gendb_verification::obligations::PLAIN_COLUMNS`, `gendb-plain-columns-v1`), offered as
/// a contract file for storage interfaces to copy unchanged.
pub const PLAIN_COLUMNS_CONTRACT_FILE: &str = "plain-columns.rs";

/// What the general line adds to the contract's inputs.
pub struct GeneralContract<'a> {
    /// `<run>/engine`: the version tree, the versions, the attempts and the findings log.
    pub engine_dir: &'a Path,
    /// The run's engine rules (the line, the template constants, the schema's names).
    pub rules: &'a EngineRuleSet,
    /// The scale, the call limits and the branches of these inputs.
    pub inputs: &'a GeneralInputs,
}

impl GeneralContract<'_> {
    fn call_limit_seconds(&self) -> u64 {
        self.inputs.call_limits.call_limit_ns / 1_000_000_000
    }

    /// The run's shape: one line (one branch) or several branches.
    fn shape(&self) -> Shape {
        Shape::of_branches(self.inputs.branches.len())
    }

    /// The manifest's schema as the author reads it: the general schema; on one line without `base` (a submission's
    /// parent is always the head) and with `direction` as one short line on what the session works on.
    fn manifest_schema(&self) -> Value {
        let mut schema = EngineManifest::general_schema();
        Self::one_line_schema(&mut schema, self.shape());
        schema
    }

    /// A general manifest schema as a run of `shape` reads it: on one line without `base` and with `direction` as one
    /// short line (the stage manifest schema too, `prompts::engine_contract::stage`).
    pub(super) fn one_line_schema(schema: &mut Value, shape: Shape) {
        if shape == Shape::OneLine {
            let properties = &mut schema["properties"];
            if let Some(fields) = properties.as_object_mut() {
                fields.remove("base");
            }
            properties["direction"]["description"] = json!("optional: one short line on what this session works on");
            properties["next_session"]["description"] = json!("continue (default): this session goes on after the evaluation; fresh: a fresh session continues the work from its files");
        }
    }

    fn limits(&self) -> Value {
        json!({"call_limit_seconds":self.call_limit_seconds(),"anon_memory_limit_bytes":self.inputs.call_limits.anon_memory_limit_bytes,
            "meaning":"framework safety limits of every engine call (trials, profiles and evaluations alike), the same for every version: a watchdog in the worker child ends a call at the time limit or when its anonymous resident memory passes the memory limit (polled every 100 ms), and the cell is unfinished (over_time_limit, over_memory_limit; a crashed child is child_failure). An unfinished cell counts the call limit in the score"})
    }
}

/// The storage budget rule (the template runs' allowance), as the contract and the prompt state it.
pub const BUDGET_RULE_TEXT: &str = "a version that reads only the plain storage is allowed as is, at every scale, whatever its size. The plain storage is version 0's storage: the generated flat storage of every table. A version with any storage change (a new layout, encoding, index or metadata: any storage it reads that is not a plain flat storage, or that it adds) must keep its serving storage at most the original data size of the scale (the raw generator text size, the same allowance as the template runs). A version's serving storage is every part file of the storages it reads, each file once";

/// `registry.json` of the general line: the schema line's index plus the definitions generated only when a crate's
/// storages call for them (`gendb_registry::optional_definitions_for`): the engine crate's flat access over generated
/// flat storages, and a derived storage crate's source handles and flat access. The whole-schema files of a storage
/// family's instance (`gendb_registry::WHOLE_SCHEMA_DEFINITIONS`) are listed only in a run of several workloads
/// (`engine_contract::workloads::amend_registry`).
pub fn registry(mut index: Value) -> Value {
    let optional = |kind: CrateKind, mode: ConstraintMode| -> Vec<Value> {
        optional_definitions_for(kind, mode).filter(|d| !WHOLE_SCHEMA_DEFINITIONS.contains(&d.name)).map(super::registry_row).collect()
    };
    index["engine_crate_when_its_storages_call_for_it"] = json!(optional(CrateKind::Engine, ConstraintMode::Declared));
    index["storage_crate_built_from_admitted_storages"] = json!(optional(CrateKind::Storage, ConstraintMode::Unconstrained));
    index["optional"] = json!("definitions in only some crates of a kind (presence optional): generated with the crate when its storages call for them (each summary says when) and checked by Verus with it; a storage crate built from admitted storages carries its source handles instead of gendb_source.rs and gendb_entry/binder.rs; plain_columns is GenDB's vocabulary an interface may copy unchanged");
    index["plain_columns_file"] = json!(PLAIN_COLUMNS_CONTRACT_FILE);
    index
}

/// The generated flat access (also listed in `registry.json` with the other optional definitions).
fn generated_access() -> Value {
    json!({"engine_crate":{"file":"src/flat_tables.rs","module":"crate::flat_tables",
            "items":["TABLE_COUNT","flat_table(t) / is_flat_table(t)","flat_bound(sv, db)","table_rows(stores, t, db)","materialize_table(stores, t, db)","column_slice(stores, t, c, lo, hi, db) -> ColumnSlice (Int32 | Int64 | Numeric(_, scale) | Date | Text(offsets, bytes)), slice_len, slice_wf, slice_value","lemma_flat_table_unique","materialize_database(stores, db) and lemma_flat_database_unique (when every table is flat-stored)"],
            "meaning":"generated with the crate whenever a storage use is a generated flat storage, and checked by Verus with it (no trust): every table of a flat storage by table id and column id, each item specified against the bound database, so engine code reads them without naming a table or column"},
        "derived_storage_crate":{"file":"src/sources_flat.rs","module":"crate::sources_flat","meaning":"the same access over the flat sources of a storage built from admitted storages (its builder)"},
        "plain_columns":{"files":["src/flat_tables/plain.rs","src/sources_flat/plain.rs"],"modules":["crate::flat_tables::plain","crate::sources_flat::plain"],
            "contract_file":PLAIN_COLUMNS_CONTRACT_FILE,"identity":gendb_verification::obligations::PLAIN_COLUMNS_IDENTITY,
            "meaning":"the plain-columns vocabulary (the same text everywhere): how the columns of one relation are held as plain typed arrays, by part index and declared type; lemma_flat_plain(sv, db, t) and flat_parts/flat_layout state in it what the flat parts of table t hold. A storage interface states represents with its own unchanged copy (stores/<name>/interface/plain.rs, pub mod plain;)"}})
}

/// `task.json` of the general line: the schema line's with the general task, manifest schema and generated access.
pub fn task(root: &Path, example: &Path, general: &GeneralContract) -> Value {
    let mut task = super::task(root, example);
    task["task"] = json!("Build the fastest verified engine as soon as possible: faster on the training templates at every worker count than the best of DuckDB and Umbra; first finish every template within the call limit at the current scale, then reduce the total time. crate::agent::engine answers every supported query (wf_ordered over the schema) over the stored data, proved against the fixed engine entry; submit your verus-engine.json once it holds several verified improvements (only admitted versions count; how long an evaluation takes at the current scale: the prompt's CURRENT FACTS, Scale)");
    task["line"] = json!("general");
    task["you_choose"] = json!("everything: the architecture, the planner, physical plans and operators, data representations, parallelism, compiler controls, which admitted storages the engine reads and any storage you add built from them, and every specification, lemma and proof. SQLSpec's verified interpreter (exec_ordered, its per-operator functions) may be called inside the proof as a fallback");
    task["manifest"]["schema"] = general.manifest_schema();
    task["manifest"]["rule"] = json!(ENGINE_MANIFEST_RULE);
    task["generated_access"] = generated_access();
    task["fixed_files"] = fixed_files();
    task
}

/// The framework files of the engine crate the prompt's "What is fixed" names by reference (`task.json` `fixed_files`).
fn fixed_files() -> Value {
    json!({"crate_src":["spec/**","exec/**","bridge/**","link/**","engine_link/**","schema.rs","gendb_constraints.rs","stores/**","flat_tables.rs","gendb_abi.rs","gendb_ast_codec.rs","gendb_entry.rs","gendb_entry/**"],
        "meaning":"every framework file of the engine crate (paths under its src/), fixed and regenerated at freeze with the engine entry gendb-verus-engine-entry-v1 (fixed/engine_entry.rs), its claim and statuses and the AST codec; edited workspace copies are never used. You own src/agent/** and the author roots of storages you add"})
}

/// The generated access to nullable columns, in a run whose schema has a nullable column (added to `task.json`'s and
/// `index.json`'s `generated_access`; nothing changes for a schema of NOT NULL columns).
pub fn add_nullable_access(access: &mut Value) {
    access["nullable_columns"] = json!({"items":["nullable_column(t, c) and lemma_nullable_column(t, c) (the declared nullability)",
            "nullable_column_slice(stores, t, c, lo, hi, db) -> (ColumnSlice, validity &[u8])","plain_table(t)"],
        "meaning":NULLABLE_ACCESS});
}

/// What the generated access offers for nullable columns (`storage-authoring.md` and `generated_access`).
const NULLABLE_ACCESS: &str = "a nullable column's flat storage holds its values and its validity (one U8 part, one byte per row, 0: NULL). column_slice reads a column that is not nullable (!nullable_column(t, c)); nullable_column_slice reads a nullable one: row lo + j of the column is Val::Null when validity[j] == 0, else slice_value(r.0, j). materialize_table and materialize_database give NULL rows as EVal::Null. The plain-columns vocabulary has no validity: lemma_flat_plain holds for the tables without a nullable column (plain_table(t))";

/// `storage-authoring.md`: the reference detail of reading the plain storage and of adding a storage, the prompt's
/// Storage section keeping the rules (the `physical_only` policy). A
/// schema with a nullable column (`nullable`) adds how the generated access reads it.
pub fn storage_authoring(nullable: bool) -> String {
    let identity = gendb_verification::obligations::PLAIN_COLUMNS_IDENTITY;
    let nullable_access = if nullable { format!("\n- Nullable columns: {NULLABLE_ACCESS}.") } else { String::new() };
    format!(
        r#"# Adding storage: the generated access, interfaces, plain columns and the declaration

The reference detail behind the prompt's Storage section: its rules decide, this file says how. Generated by GenDB for the general engine line.

## The plain storage's generated access

- In the engine crate, `crate::flat_tables` (`src/flat_tables.rs`), generated with the crate and checked by Verus with it, reads the generated flat storages by table id and column id, each item specified against the bound database: `TABLE_COUNT`, `is_flat_table`, `table_rows`, `materialize_table`, `materialize_database` (with `lemma_flat_database_unique`), and `column_slice` (rows `lo..hi` of one column as stored, without a copy; `slice_fits` states its variant from the column's declared type). Every item: `task.json` `generated_access`.
- `flat_parts(sv, t)`, `flat_layout(t)` and `lemma_flat_plain(sv, db, t)` state what the flat parts of table `t` hold, in the plain-columns vocabulary (`crate::flat_tables::plain`).{nullable_access}

## Writing a storage built from admitted storages

- **The manifest** (`verus-storage.json`; its schema, an example and the directory `new-storages/`: `task.json` `storage_manifest`) sets `built_from`, the admitted sources, and optionally `extends` one of them to keep that source's parts (linked, never copied or rebuilt) and add parts after them. The storage is proved against the derived storage entry (`fixed/storage_entry_derived.rs`; `obligations.json` `storage`). A storage built from source columns is refused (`storage_not_built_from_admitted`).
- **The builder's access.** A builder reads a source through its interface, or a flat source through `crate::sources_flat` by table id and column id (the same generated access, in the storage crate); every `crate::sources_flat` fact is stated against the bound database, so a builder never needs a flat source's interface.
- **The interface** is copied into every crate that reads the storage (as `stores/<name>/interface/**`), so it may name only the shared library, `crate::gendb_entry`'s shared modules and its own storage (`super::declaration`).
- **Plain typed arrays without names.** Copy GenDB's plain-columns vocabulary unchanged into your interface (`stores/<name>/interface/plain.rs` with `pub mod plain;`; contract file `{PLAIN_COLUMNS_CONTRACT_FILE}`, identity `{identity}`) and state `represents` with `plain::plain_columns(parts, rels[0], super::declaration::stored_columns_t0(), <the part of each column>)`.
- **Keeping a flat source's parts** (`extends`): restate them the same way. In the builder, `crate::sources_flat::lemma_flat_plain(sv, db, t)` states it of the flat parts (`flat_parts`, `flat_layout`), and the two copies are the same definitions.
- **Names.** Name the storage without a table name, and write its builder and interface over its declaration and the generated access: the schema-name rule (`rules.json` `engine_rules`) covers both.
- **Building.** The builder is verified; its asset is built in a worker child from the sources' assets (`storage_build`), and at each new scale GenDB builds it again with the same verified builder. `storage_register` admits it as a new library version (`tools.json`).

## The data_policy declaration (storage policy physical_only)

Every storage manifest declares `data_policy` with one entry per part: `{{part, table, kind, columns, why}}`.
- `kind`: `base_payload` (part of the one copy of `columns`; every part of a multi-part encoding lists the column), `index_keys` (`columns` are the keys), `permutation`, `own_skip_metadata` or `layout_offsets_counts`.
- `columns`: stored columns of `table`, required for `base_payload` and `index_keys`.
- `why`: the part's general use (the line's rule 7).
- Parts an extension inherits through `extends` are its source's and are not declared again.

Refusals:
- `storage_policy_declaration_missing`: a storage without a declaration.
- `storage_policy_declaration_revision`: an old kind, `own_source_values` or `own_index`.
- `storage_payload_duplicate`: a column that is already `base_payload` of another serving storage, refused before every build (unverified diagnostic builds included), at evaluation and at registration; so is an engine whose storage uses would add a second copy (an older version of a storage pinned beside its current version).
- `storage_policy_revision_superseded`: admitted storages registered before this rule are not offered.
- `storage_policy_excluded`: a package the user's review excluded is refused.
"#
    )
}

/// `index.json` of the general line: the schema line's with the general task, the run's records and the budget rule.
pub fn index(root: &Path, contract: &Path, general: &GeneralContract) -> Value {
    let mut index = super::index(root, contract);
    let engine = general.engine_dir;
    index["scope"] = json!(super::GENERAL_SCOPE);
    index["task"] = json!("Make the verified engine faster than the best of DuckDB and Umbra on the training templates at every worker count (contract task.json); every submission is judged against its parent in one interleaved timing");
    index["read_order"] = json!(["task","final_claim","obligations","tree","findings","templates","versions","engine_map","toolkit","storages","budget_rule","storage_authoring","stored_data","data","validation","performance","rules","tools","integrity_constraints","proof_library"]);
    let inputs = index["inputs"].as_object_mut().expect("the index's inputs");
    inputs.insert("budget_rule".into(), json!(contract.join(BUDGET_RULE_FILE)));
    inputs.insert("storage_authoring".into(), json!(contract.join(STORAGE_AUTHORING_FILE)));
    inputs.insert("plain_columns".into(), json!(contract.join(PLAIN_COLUMNS_CONTRACT_FILE)));
    inputs.insert("tree".into(), json!(engine.join("TREE.md")));
    inputs.insert("tree_data".into(), json!(engine.join("tree.json")));
    inputs.insert("findings".into(), json!(engine.join(tree::FINDINGS_MARKDOWN)));
    inputs.insert("versions_records".into(), json!(engine.join("versions")));
    inputs.insert("attempts_records".into(), json!(engine.join("attempts")));
    index["output"]["manifest"] = general.manifest_schema();
    index["output"]["rule"] = json!(ENGINE_MANIFEST_RULE);
    index["generated_access"] = generated_access();
    index["records"] = json!("the run's records (tree, findings, versions, attempts) are read-only inputs: GenDB writes them after every evaluation");
    index
}

/// `rules.json` of the general line: the central rules and the line's engine rules (no whole-statement evaluator rule).
pub fn rules(general: &GeneralContract) -> Value {
    let mut rules = super::rules();
    if let Some(fields) = rules.as_object_mut() {
        fields.remove("whole_query_evaluator");
    }
    let rules_list = rule_texts(GENERAL_ENGINE_RULES);
    rules["engine_rules"] = json!({"line":"general","rules":rules_list,"rule_set":general.rules.record(),"static_items":ENGINE_STATIC_ITEM_RULE,
        "scope":"at freeze (the check tool and every submission) and again at admission: template constants, AST fragments and the schema-name rule over every agent/ file; the schema-name rule also over the own interface and builder files of every storage the engine reads that is not a generated flat storage; no static item (no state between calls)",
        "reported":{"id":SCHEMA_TABLE_MENTION,"meaning":"a table name of the schema as a word or segment of an identifier outside literals and storage paths: reported with the evaluation, never refused (short table names collide with framework words)"}});
    rules["interpreter"] = json!({"allowed":true,"meaning":"on this line the whole-statement evaluator rule does not apply: crate::exec::relational::entry::exec_ordered and the interpreter's per-operator functions may be called inside the proof (the general fallback)"});
    rules
}

/// The rules as `rules.json` lists them: each id, what it refuses and its reason (without design references).
pub(super) fn rule_texts(rules: &[RefusalRule]) -> Vec<Value> {
    rules.iter().map(|r| json!({"id":r.id,"refuses":r.refuses,"reason":without_design_references(r.reason)})).collect()
}

/// `text` without its parenthesized references to the framework's design documents (a parenthesis that names a
/// `design ` section), which an author cannot read: the rule texts are shared with the schema line, whose contract keeps them as they are.
fn without_design_references(text: &str) -> String {
    let mut out = String::new();
    let mut rest = text;
    while let Some(open) = rest.find(" (") {
        let Some(close) = rest[open..].find(')').map(|c| open + c) else { break };
        let inner = &rest[open + 2..close];
        out.push_str(&rest[..open]);
        if !inner.contains("design ") {
            out.push_str(&rest[open..=close]);
        }
        rest = &rest[close + 1..];
    }
    out.push_str(rest);
    out
}

/// `failure-classes.json` of the general line: the schema line's named refusals without the evaluator rule, with the
/// line's refusals and the states of an unfinished cell.
pub fn failure_classes(general: &GeneralContract) -> Value {
    let one_line = general.shape() == Shape::OneLine;
    let mut file = super::failure_classes();
    let named = file["named_reasons"].as_object_mut().expect("named reasons");
    named.remove("whole_statement_evaluator");
    named.insert("schema_name".into(), json!("refusal (engine rules, general line): an agent/ file, or the own interface or builder file of a storage the engine reads that is not a generated flat storage, names a column of the schema, or a table of the schema in a literal or storage path (rules.json engine_rules)"));
    named.insert(SCHEMA_TABLE_MENTION.into(), json!("report only: a table-name word in an identifier; never refused"));
    if !one_line {
        // One line has no direction requirement (`acceptance::direction_required`).
        named.insert("branch_direction_required".into(), json!("refusal: a branch's first submission states its direction (verus-engine.json direction)"));
    }
    named.insert("storage_budget_exceeded".into(), json!("refusal: a version with a storage change serves more than the original data size at this scale (budget-rule.json)"));
    named.insert("not_better_than_parent".into(), json!(if one_line {
        "attempt: verified and timed, but its score was not better than its parent's in one interleaved timing; recorded with its race, the head stays"
    } else {
        "attempt: verified and timed, but its score was not better than its parent's in one interleaved timing; recorded with its race, the branch head stays"
    }));
    named.insert("over_time_limit".into(), json!("cell state, not a refusal: a call reached the call limit; the cell is unfinished and counts the call limit"));
    named.insert("over_memory_limit".into(), json!("cell state, not a refusal: a call's anonymous memory passed the memory limit; the cell is unfinished"));
    named.insert("child_failure".into(), json!("cell state, not a refusal: the worker child failed (crash, abort, kill); the cell is unfinished"));
    file
}

/// `performance.json` of the general line: the interleaved timing, the score, the limits, the ladder, the main line and
/// the profile, beside the shared execution environment.
pub fn performance(training: &Value, workers: &[usize], general: &GeneralContract) -> Value {
    let mut performance = super::performance(training, workers);
    let fields = performance.as_object_mut().expect("performance");
    for stale in ["official_matrix", "totals", "stop_rule", "variant_matrix", "other_bindings"] {
        fields.remove(stale);
    }
    fields.insert("submission_timing".into(), json!({"rule":RACE_RULE,
        "cells":format!("every training template at the timing binding {} x every configured worker count {workers:?}; each side of a cell is one fresh worker child, 1 warm call then 1 hot call (the development plan), the cell's time the hot call; a warm call over the limit leaves the cell unfinished", training["timing_binding"])}));
    fields.insert("evaluation_plans".into(), json!({"development":DEVELOPMENT.record(),"final":FINAL.record(),
        "meaning":"every submission (and every other timing of the run) is evaluated under the development plan; the final plan, the full protocol, is run by the operator for the final numbers only (gendb engine final-evaluation) and never decides a submission"}));
    fields.insert("score".into(), json!({"rule":SCORE_RULE,"baselines":"the saved totals of DuckDB and Umbra at this scale (templates.json baseline_totals); the target at each worker count is the faster one"}));
    fields.insert("finished_checks".into(), json!("after the timing (the development plan): every variant with AST bytes of its own, at the first scale of the ladder, one call at 64 workers, its answer compared with its template's saved answers there (no time read); a wrong answer refuses the submission, an unfinished call is recorded. No qualification at the other visible bindings: the final evaluation runs it (for the templates finished at the timing binding, and the variants of the templates finished at every worker count)"));
    fields.insert("call_limits".into(), general.limits());
    let (main_line, ladder) = match general.shape() {
        Shape::OneLine => (
            "one line of versions: each version builds on the best version; a submission's parent is the head (the best version so far), and an accepted submission becomes the new head",
            "move to the next scale when the head finishes every cell at the current scale. At the new scale the head is timed and sessions continue there",
        ),
        Shape::Branches => (
            "the main-line head is the best version over all branches: a branch version whose recorded score beats the main-line head's is timed against it in one interleaved timing, and the winner is the main-line head; an accepted merge becomes the main-line head",
            "move to the next scale when the main-line head finishes every cell at the current scale. At the new scale the heads are timed interleaved and sessions continue there",
        ),
    };
    fields.insert("main_line".into(), json!(main_line));
    fields.insert("scale_ladder".into(), json!({"scale":general.inputs.scale.name,"index":general.inputs.scale_index,"scales":general.inputs.scales,"rule":ladder}));
    fields.insert("stop".into(), json!("none from performance: the run stops only when its budget is used or the user stops it; beating both baselines at a scale is a milestone"));
    fields.insert("sampling_profile".into(), json!({"method":PROFILE_METHOD,"when":"on request (the profile tool: profile the templates you work on); also of version 0, and in the final evaluation (every template at the worker count of its largest gap to the faster baseline, under the call limits, after its timing); no profile follows a submission's admission","output":"PROFILE.md and profile/<statement>-w<workers>.json in the job (version 0: in its folder)"}));
    performance
}

/// `tools.json` of the general line: the schema line's with the limits, the sampling profile and the stored-answer
/// bound of the author's own statements.
pub fn tools_file(training: &Value, workers: &[usize], general: &GeneralContract) -> Value {
    let mut tools = super::tools_file(training, workers);
    tools["tools"]["trial"] = json!("compile (or verification not_run) + the engine over the training matrix (templates x workers at one binding) or your sql statements, one fresh child per cell under the timing lease and the call limits (an unfinished cell is reported with its reason)");
    tools["tools"]["profile"] = json!("one cell, 1 warm + 1 measured call under the call limits, with the sampled self time per function of the measured call");
    tools["result_fields"]["profile"] = json!("status, profile {statement, workers, calls[] (wall, process and calling-thread CPU, peak anonymous memory), stopped, sampled_call, samples_taken, functions[] (function, object, self_samples, self_permille)}, report (PROFILE.md of the job), method");
    tools["arguments"]["hot_calls"] = json!("trial only, optional, at least 1 (default 1): a submission's evaluation also runs 1 warm + 1 hot call per cell (the development plan); only the final evaluation runs 1 warm + 3 hot");
    tools["arguments"]["sql"] = json!(format!(
        "trial/profile: your own SQL statements over the schema (no parameters), instead of templates; each is translated and encoded like the templates; no saved answer (status, row count and times only). An answer's rows are stored up to {}: a larger answer keeps its first rows, and the cell's stored_answers gives its row count, the SHA-256 of its result wire and the rows stored (the rest is not stored)",
        AnswerBound::STORED.describe()
    ));
    tools["call_limits"] = general.limits();
    tools
}

/// `budget-rule.json`: the storage budget rule at this scale, and how it is decided.
pub fn budget_rule(general: &GeneralContract) -> Value {
    budget_rule_of(general.inputs, general.shape().head())
}

/// [`budget_rule`] of the inputs of one scale, whose best version the texts call `head` (a stage run's kept workloads
/// too, `prompts::engine_contract::stage`).
pub fn budget_rule_of(inputs: &GeneralInputs, head: &str) -> Value {
    let scale = &inputs.scale;
    json!({"format_version":3,"rule":BUDGET_RULE_TEXT,"scale":scale.name,
        "budget_bytes":scale.original_data_bytes,
        "budget":"the original data size at this scale: the raw generator text size (original_data_record), the same definition as the template runs' storage allowance (data_allowance.live_bytes). It bounds the serving storage of every version with a storage change",
        "original_data_record":scale.original_data_record,
        "plain_storage":{"bytes":inputs.plain_storage_bytes,"times_original":times(inputs.plain_storage_bytes, scale.original_data_bytes),"storages":inputs.plain_storages,
            "meaning":"version 0's storage, the generated flat storage of every table (these packages), measured from the run library at this scale's data, each part file once. A version that reads only these storages is allowed as is, whatever its size"},
        "what_follows":"the plain storage is larger than the original data, so a storage change must first compress or re-encode the data below the original size; only the space saved can hold indexes, skipping metadata and other structures",
        "serving_bytes":"every part file of the storages a version reads, each file once by filesystem identity, as the library counts them once the version is selected",
        "decided":"at every submission's evaluation and again at admission under the library's budget lock (storage_budget_exceeded)",
        "storage_policy":"physical_only, unchanged (the Storage policy section): one copy of each column, no precomputed results, no cross-table structures, metadata over one table's own rows only",
        "storage_budget_file":format!("storage-budget.json lists the {head}'s serving storage as the library counts it; its allowance_bytes is null because this line's budget is this rule, not a library allowance")})
}

/// `bytes` as a multiple of `of`, two decimals (`-` when `of` is 0).
fn times(bytes: u64, of: u64) -> String {
    if of == 0 { "-".into() } else { format!("{:.2}", bytes as f64 / of as f64) }
}

/// The budget beside the data facts (`data.json`).
pub fn add_data_facts(facts: &mut Value, general: &GeneralContract) {
    facts["storage_budget"] = json!({"budget_bytes":general.inputs.scale.original_data_bytes,"budget":"the original data size at this scale, the bound on a version with a storage change",
        "plain_storage_bytes":general.inputs.plain_storage_bytes,"plain_storage":"version 0's flat storage, allowed as is","scale":general.inputs.scale.name,"rule":BUDGET_RULE_FILE});
}

/// `versions.md` of the general line: every version timed at this scale with its totals and cells, then every attempt.
pub fn versions_markdown(general: &GeneralContract, training: &Value) -> String {
    let tree = match VersionTree::read(general.engine_dir) {
        Ok(tree) => tree,
        Err(error) => return format!("# Versions\n\nThe version tree could not be read: {error}.\n"),
    };
    let columns = ScaleColumns::from_training(training, general.inputs.call_limits.call_limit_ns);
    let mut out = format!("# Versions\n\nEvery version of every branch timed at the current scale, then every attempt. Generated by GenDB from the run's records when this session was prepared; the run's `TREE.md` ({}) is current.\n\n", general.engine_dir.join("TREE.md").display());
    let versions = format!("({}/versions/", general.engine_dir.display());
    out.push_str(&scale_markdown(general.engine_dir, &tree, &general.inputs.scale.name, &columns).replacen("# Scale", "## Scale", 1).replace("\n## ", "\n### ").replace("(../versions/", &versions));
    out.push_str("\n## Attempts\n\n| Attempt | Branch | Parent | Score | Why not accepted | Folder |\n|---|---|---|---|---|---|\n");
    for n in tree.attempts() {
        let score = n.score.as_ref().map_or("-".to_string(), |s| format!("{}: F {}/{}, G {}", s.scale, s.score.finished, s.cells, s.score.normalized_time));
        let reason = n.reason.as_deref().and_then(|r| r.lines().next()).unwrap_or("-").replace('|', "\\|");
        out.push_str(&format!("| {} | {} | {} | {score} | {reason} | `{}` |\n", n.id, n.branch, n.parents.join(", "), n.directory(general.engine_dir).display()));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::prompts::engine_general_sections::{self as sections, Shape};

    /// The reference detail moved out of the prompt is in `storage-authoring.md` (the generated access, the
    /// builder's access to its sources, the interface's names, the plain-columns vocabulary, keeping flat parts, the
    /// declaration's kinds and every refusal code), the framework file list is in `task.json` `fixed_files`, and the
    /// prompt points to both; the prompt keeps the rules that decide acceptance.
    #[test]
    fn the_moved_reference_detail_is_in_the_contract() {
        let text = storage_authoring(false);
        for moved in ["`TABLE_COUNT`, `is_flat_table`, `table_rows`, `materialize_table`, `materialize_database`", "`slice_fits` states its variant from the column's declared type",
            "`flat_parts(sv, t)`, `flat_layout(t)` and `lemma_flat_plain(sv, db, t)`", "a flat source through `crate::sources_flat` by table id and column id",
            "so a builder never needs a flat source's interface", "it may name only the shared library, `crate::gendb_entry`'s shared modules and its own storage (`super::declaration`)",
            "`stores/<name>/interface/plain.rs` with `pub mod plain;`", "contract file `plain-columns.rs`, identity `gendb-plain-columns-v1`",
            "`plain::plain_columns(parts, rels[0], super::declaration::stored_columns_t0(), <the part of each column>)`", "`crate::sources_flat::lemma_flat_plain(sv, db, t)`",
            "`{part, table, kind, columns, why}`", "`base_payload`", "`index_keys`", "`permutation`", "`own_skip_metadata`", "`layout_offsets_counts`",
            "Parts an extension inherits through `extends` are its source's and are not declared again", "`storage_policy_declaration_missing`", "`storage_policy_declaration_revision`",
            "`own_source_values` or `own_index`", "`storage_payload_duplicate`", "(unverified diagnostic builds included), at evaluation and at registration",
            "an older version of a storage pinned beside its current version", "`storage_policy_revision_superseded`", "`storage_policy_excluded`", "`storage_not_built_from_admitted`"] {
            assert!(text.contains(moved), "storage-authoring.md: {moved}");
        }
        let files = fixed_files();
        assert_eq!(files["crate_src"].as_array().map(Vec::len), Some(13));
        let prompt = format!("{}{}{}", sections::fixed(sections::Workloads::One), sections::storage_section(), sections::inputs(Shape::OneLine));
        for pointer in ["`task.json` `fixed_files`", "contract `storage-authoring.md`", "the kinds and every refusal code: `storage-authoring.md`", "is in that file's directory",
            "A storage without a declaration is refused", "(`storage_not_built_from_admitted`)", "(`engine_storage_coverage_incomplete`)"] {
            assert!(prompt.contains(pointer), "the prompt: {pointer}");
        }
    }

    /// Writes `storage-authoring.md` under `GENDB_GENERAL_RENDER_DIR` for review.
    #[test]
    #[ignore = "writes storage-authoring.md under GENDB_GENERAL_RENDER_DIR for review"]
    fn write_storage_authoring() {
        let out = std::path::PathBuf::from(std::env::var("GENDB_GENERAL_RENDER_DIR").expect("GENDB_GENERAL_RENDER_DIR"));
        std::fs::create_dir_all(&out).unwrap();
        std::fs::write(out.join(STORAGE_AUTHORING_FILE), storage_authoring(false)).unwrap();
        std::fs::write(out.join("task-fixed-files.json"), serde_json::to_string_pretty(&fixed_files()).unwrap()).unwrap();
    }
}
