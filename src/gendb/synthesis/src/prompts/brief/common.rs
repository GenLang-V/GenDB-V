//! Contract files both author roles receive, generated from the enforcing code: the fixed entry texts and the stored
//! parts read API, the registry index of fixed definitions, the stored-data guide (storage obligations, manifest,
//! request accounting, generic representation patterns), the proof-library catalog, parallelism, source rules,
//! toolchain commands, tools, failure classes, accounting and the admitted-storage catalog. Nothing here is specific to
//! a query or a dataset; the enforcing definitions stay the authority and these files point to them.

use crate::controller::limits::Limits;
use crate::controller::records::write_json_atomic;
use crate::prompts::policy::{FIXED_FLAT_DATA_ACCESS_TEXT, STORAGE_CHOICE_TEXT};
use crate::query::assets::STORAGE_MARGIN_BYTES;
use crate::query::QuerySession;
use crate::query::candidate::{CompilerChoice, EVALUATOR_RULE};
use crate::query::compile::crate_options;
use crate::query::evaluation::DEFAULT_TRIAL_HOT_CALLS;
use crate::query::source_items::{module_doc, public_items, spec_item};
use crate::storage::catalog::{self, write_read_only};
use crate::storage::manifest::StorageManifest;
use crate::storage::policy::StoredDataPolicy;
use crate::tools::{self, AuthorRole, ToolAction};
use gendb_artifacts::ObjectStore;
use gendb_frontend::ast::TableDef;
use gendb_frontend::columns::{SourceType, declared_columns};
use gendb_registry::{ConstraintMode, CrateKind, DEFINITIONS, STORED_PARTS_SOURCE, definitions_for};
use gendb_storage::import::PreparedSource;
use gendb_storage::versions::CurrentCapture;
use gendb_verification::admission::execution::CHILD_TIMEOUT_SECONDS;
use gendb_frontend::ast::ConstraintDef;
use gendb_verification::admission::{AdmissionError, FailureClass, Statement};
use gendb_verification::obligations::{
    PROVED_PROPERTIES, QUERY_ENTRY_V5, QUERY_THEOREMS, QueryEntry, STORAGE_ENTRY_DERIVED, STORAGE_ENTRY_DERIVED_V2, STORAGE_ENTRY_V1, STORAGE_ENTRY_V2, STORAGE_THEOREMS, StorageEntry,
    query_entry,
};
use gendb_verification::verus::{
    ALLOWED_ATTRIBUTES, ALLOWED_EXTERNAL_TRAITS, ALLOWED_VERIFIER_ATTRIBUTES, FrameworkSource, FrozenCrate, SUPPORTED_DERIVES, SUPPORTED_MACROS, VERUS_REFUSAL_RULES, VerusMode, VerusToolchain,
    verus_args, verus_pin,
};
use serde_json::{Value, json};
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};

/// Write a JSON contract file.
pub fn write(path: &Path, value: &Value) -> Result<(), AdmissionError> {
    write_json_atomic(path, value).map_err(AdmissionError::tool)
}

/// Signature, clauses and (for spec functions) the defining body of `fn NAME` in `text`.
pub fn quoted_item(text: &str, name: &str) -> Value {
    match spec_item(text, name) {
        Some(s) => json!({"name":name,"signature":s.signature,"requires":s.requires,"ensures":s.ensures,"body":s.body}),
        None => json!({"name":name,"text":"absent"}),
    }
}

/// Shell text of one command word (single-quoted when it is not plain).
pub fn shell_word(word: &str) -> String {
    let plain = !word.is_empty() && word.chars().all(|c| c.is_ascii_alphanumeric() || "/._-=:,+@%".contains(c));
    if plain { word.to_string() } else { format!("'{}'", word.replace('\'', "'\\''")) }
}

/// The run's fixed entries and the files that hold them under `<contract>/fixed/`.
pub struct FixedFiles {
    /// The query entry of every query crate of the run: v4, or v5 when the request declares integrity constraints.
    pub query: QueryEntry,
    /// `fixed/query_entry.rs` (the text of [`Self::query`]).
    pub query_entry: PathBuf,
    /// `fixed/storage_entry.rs`: the storage entry v1, usable in every run.
    pub storage_entry: PathBuf,
    /// `fixed/storage_entry_v2.rs`, written only when the run declares integrity constraints (the opt-in entry).
    pub storage_entry_v2: Option<PathBuf>,
    /// `fixed/storage_entry_derived.rs`: the entry of a storage built from admitted storages (manifest `built_from`).
    pub storage_entry_derived: PathBuf,
    /// `fixed/stored.rs`: the stored-parts read API.
    pub stored: PathBuf,
    /// The dataset schema has a nullable column: author texts about stored columns say how NULL rows are held (a
    /// schema of NOT NULL columns keeps its texts byte for byte).
    pub nullable: bool,
}

impl FixedFiles {
    /// The run declares integrity constraints (query entry v5).
    pub fn constrained(&self) -> bool {
        self.query == QUERY_ENTRY_V5
    }
}

/// The fixed entry texts and the stored-parts API of the run of `statement` (every statement of a run has the same
/// declarations), written read-only under `<contract>/fixed/` so an author can read them before any crate of its own
/// exists.
pub fn write_fixed_files(contract: &Path, statement: &Statement) -> Result<FixedFiles, AdmissionError> {
    let fixed = contract.join("fixed");
    let query = query_entry(&statement.instance);
    let files = FixedFiles {
        query,
        query_entry: fixed.join("query_entry.rs"),
        storage_entry: fixed.join("storage_entry.rs"),
        storage_entry_v2: (query == QUERY_ENTRY_V5).then(|| fixed.join("storage_entry_v2.rs")),
        storage_entry_derived: fixed.join("storage_entry_derived.rs"),
        stored: fixed.join("stored.rs"),
        nullable: has_nullable_column(&statement.instance.doc.tables),
    };
    write_read_only(&files.storage_entry_derived, STORAGE_ENTRY_DERIVED.source)?;
    write_read_only(&files.storage_entry, STORAGE_ENTRY_V1.source)?;
    write_read_only(&files.query_entry, query.source)?;
    write_read_only(&files.stored, STORED_PARTS_SOURCE)?;
    if let Some(v2) = &files.storage_entry_v2 {
        write_read_only(v2, STORAGE_ENTRY_V2.source)?;
    }
    Ok(files)
}

/// Items of the fixed storage entry its claim consists of (quoted verbatim).
const STORAGE_CLAIM_ITEMS: [&str; 5] = ["build_workers_ok", "delivered_source", "storage_build_meets", "abi_build_storage", "theorem_storage_built"];
/// Items of the fixed query entry v4 (the same in entry v5) its claim consists of (quoted verbatim).
pub const QUERY_CLAIM_ITEMS: [&str; 11] = [
    "capacity_domain", "bound_db", "outcome_ok", "answer_meets", "stores_ready", "workers_ok", "served", "query_meets", "abi_query", "theorem_end_to_end",
    "corollary_inside_capacity",
];

/// The storage obligations: what a storage author provides, the fixed storage entry's claim and its trust; in a run
/// with declared integrity constraints also those of the opt-in storage entry v2 (`storage_entry_v2`).
pub fn storage_obligations(fixed: &FixedFiles) -> Value {
    let mut obligations = storage_entry_obligations(&fixed.storage_entry);
    if let Some(v2) = &fixed.storage_entry_v2 {
        let entry = STORAGE_ENTRY_V2;
        obligations["storage_entry_v2"] = json!({"when":"a storage whose verus-storage.json sets uses_declared_constraints: true (integrity-constraints.json storage)",
            "fixed_entry":v2,"identity":entry.identity,"author_items":entry.author_obligations,
            "claim_items":STORAGE_CLAIM_ITEMS.iter().chain(["source_witnessed"].iter()).map(|n| quoted_item(entry.source, n)).collect::<Vec<_>>(),
            "theorems":STORAGE_THEOREMS,"trusted_assumptions":entry.trusted_assumptions,"proved_properties":PROVED_PROPERTIES,
            "in_words":"the storage entry v1 claim with one more hypothesis: the delivered source comes from a full database of the schema in db_wf that satisfies the declared constraints (source_witnessed; the builder may require it); the theorems take constraints_hold(declared_db(db)) as one more premise. The output relation and statuses are v1's. The storage applies only to runs with exactly this declaration set"});
    }
    let derived = if fixed.constrained() { STORAGE_ENTRY_DERIVED_V2 } else { STORAGE_ENTRY_DERIVED };
    let derived_claim: Vec<Value> =
        ["sources_bound", "derived_build_meets", "theorem_storage_built", "theorem_storage_build_total"].iter().map(|n| quoted_item(derived.source, n)).collect();
    obligations["storage_entry_derived"] = json!({"when":"a storage whose verus-storage.json sets built_from (required for every storage a query author creates; available to the workload author for a storage over admitted ones)",
        "fixed_entry":fixed.storage_entry_derived,"identity":derived.identity,"author_items":derived.author_obligations,
        "claim_items":derived_claim,
        "trusted_assumptions":derived.trusted_assumptions,"proved_properties":PROVED_PROPERTIES,
        "builder":"pub fn build(stores: &mut crate::gendb_entry::sources::Stores, workers: usize, dispatch: &mut Dispatch) -> Result<Vec<OwnedPart>, QueryError>: it reads each source only through that source's interface readers and StoredParts extents (the same Stores a query crate gets)",
        "in_words":"for every database whose stored relations the admitted sources' parts represent (sources_bound; under declared constraints also constraints_hold), if the builder returns Ok, the source parts it inherits (built_from.extends: that source's parts, linked unchanged) followed by the parts it returned represent (your represents) exactly this storage's stored relations: old represents + correct copy => new represents. No source column is read, so the original input may be deleted. Under the trusted assumptions every build terminates with exactly one outcome: Refused for a worker count outside the builder's domain, otherwise Ok (as above). The fixed contract also permits WorkerFailed without a condition (only a real failed join creates its token); under the trusted assumption worker_failure it does not occur. Termination is checked by Verus (proved_properties), not stated in the theorems"});
    obligations
}

/// The obligations of the storage entry v1 (`storage_entry`: its file under `fixed/`).
fn storage_entry_obligations(storage_entry: &Path) -> Value {
    let entry: StorageEntry = STORAGE_ENTRY_V1;
    json!({"format_version":1,"fixed_entry":storage_entry,
        "author_items":entry.author_obligations,
        "claim_items":STORAGE_CLAIM_ITEMS.iter().map(|n| quoted_item(entry.source, n)).collect::<Vec<_>>(),
        "theorems":STORAGE_THEOREMS,"trusted_assumptions":entry.trusted_assumptions,"proved_properties":PROVED_PROPERTIES,
        "in_words":"Total correctness relative to the outcome contract. For every database of the schema in db_wf and every worker count in the builder's domain, and under the trusted assumptions, the build terminates and returns exactly one outcome: Ok, whose parts represent (your `represents`) exactly the stored relations of that database (stored_relations: per stored table, its stored columns in canonical row order); or InvalidInput only outside the declared column domain (decided by the entry before your builder runs; never on such a database). The fixed contract also permits WorkerFailed without a condition (only a real failed join creates its token); under the trusted assumption worker_failure (the thread runtime reports a failed join only when a worker panics; workers are verified and no_unwind) it does not occur. The theorems state what Ok means (partial correctness); termination is checked by Verus (proved_properties) and is not part of the theorem statement. Your `represents` is your own relation; queries can use only what it states, and the builder must prove it for every in-domain source, so it must be satisfiable by real data",
        "what_you_cannot_do":[
            {"attempt":"narrow the source domain or assume facts about the data","prevented_by":"the entry passes only source_wf and in_domain; any extra precondition fails the entry's verification"},
            {"attempt":"a lossy summary presented as the table","prevented_by":"a query can prove the SQL claim only for every database whose relations your parts represent; whatever `represents` leaves open stays open"},
            {"attempt":"read stored bytes other than through extents","prevented_by":"StoredParts is private; only extent calls return data, each counted"}]})
}

/// The query obligations of the run's query entry (v4, or v5 under declared integrity constraints): what a query
/// author provides and the fixed final claim.
pub fn query_obligations(fixed: &FixedFiles) -> Value {
    let entry = fixed.query;
    let mut obligations = json!({"format_version":1,"fixed_entry":fixed.query_entry,
        "author_items":entry.author_obligations,
        "claim_items":QUERY_CLAIM_ITEMS.iter().map(|n| quoted_item(entry.source, n)).collect::<Vec<_>>(),
        "theorems":QUERY_THEOREMS,"trusted_assumptions":entry.trusted_assumptions,"proved_properties":PROVED_PROPERTIES});
    if fixed.constrained() {
        obligations["identity"] = json!(entry.identity);
    }
    obligations
}

/// The registry index of fixed definitions and author files, per crate kind, with each logical path. Without declared
/// integrity constraints: the crates of every existing run. With them (`constrained`): query crates of the entry v5,
/// storage crates of the entry v1 and, for a manifest that opts in, of the entry v2.
pub fn registry_index(constrained: bool) -> Value {
    let kinds = |kind: CrateKind, mode: ConstraintMode| -> Vec<Value> {
        definitions_for(kind, mode)
            .map(|d| json!({"name":d.name,"crate_path":d.crate_path,"presence":d.presence,"role":d.role,"origin":d.origin,"items":d.items,"summary":d.summary}))
            .collect()
    };
    let query_mode = if constrained { ConstraintMode::Declared } else { ConstraintMode::Unconstrained };
    let mut index = json!({"format_version":1,
        "storage_crate":kinds(CrateKind::Storage, ConstraintMode::Unconstrained),"query_crate":kinds(CrateKind::Query, query_mode),
        "references":DEFINITIONS.iter().filter(|d| d.crate_path.is_none()).map(|d| json!({"name":d.name,"origin":d.origin,"summary":d.summary})).collect::<Vec<_>>(),
        "placeholder":"<storage> in a crate path stands for a storage's name",
        "authority":"each definition's file is the authority; this index only says which file holds which items and where assembled crates carry it (gendb_registry)"});
    if constrained {
        index["storage_crate_uses_declared_constraints"] = json!(kinds(CrateKind::Storage, ConstraintMode::Declared));
        index["constraint_modes"] = json!({"query_crate":"declared: every query crate of this run uses the entry v5 and carries gendb_constraints.rs",
            "storage_crate":"unconstrained (storage entry v1): a storage whose manifest does not opt in; usable in every run",
            "storage_crate_uses_declared_constraints":"declared (storage entry v2 and gendb_constraints.rs): a storage whose manifest sets uses_declared_constraints: true; usable only in runs with exactly this declaration set"});
    }
    index
}

/// The run's declared integrity constraints as both author roles read them (`integrity-constraints.json`): the trust
/// basis, every declaration with its place in `declared_schema()`, the generated module and its items, the query
/// hypothesis and the storage opt-in with how to use each, the projection rule, the supported forms and how tiny cases
/// treat them. `src`: the directory whose `gendb_constraints.rs` and SQLSpec files (`framework`, as written there) the
/// author reads.
pub fn integrity_constraints(statement: &Statement, fixed: &FixedFiles, framework: &[FrameworkSource], src: &Path) -> Value {
    let def = |name: &str| super::definition(framework, src, name);
    let module = super::framework_text(framework, "gendb_constraints.rs");
    let bridge = super::framework_text(framework, "bridge/constraints.rs");
    let doc = &statement.instance.doc;
    let mut declarations = vec![];
    let mut per_table = vec![0usize; doc.tables.len()];
    for (i, declaration) in statement.integrity_constraints.iter().flat_map(|c| &c.declarations).enumerate() {
        let Some(t) = doc.tables.iter().position(|table| table.name == declaration.table) else { continue };
        let k = per_table[t];
        per_table[t] += 1;
        let mut record = json!({"index":i,"table":declaration.table,"sql":declaration.sql,"table_id":t,"spec":format!("declared_schema()[{t}].constraints[{k}]")});
        if let Some(constraint) = doc.tables[t].constraints.get(k) {
            record["meaning"] = constraint_meaning(doc, t, constraint);
        }
        declarations.push(record);
    }
    let storage_v2 = STORAGE_ENTRY_V2;
    let module_items: Vec<Value> = ["declared_schema", "declared_db", "lemma_declared_schema"].iter().map(|n| quoted_item(module, n)).collect();
    let bridge_lemmas: Vec<Value> =
        ["lemma_constraint_at", "lemma_unique_key", "lemma_primary_key_identifies", "lemma_foreign_key_target", "lemma_foreign_key_full", "lemma_check_row"]
            .iter()
            .map(|n| quoted_item(bridge, n))
            .collect();
    json!({"format_version":1,
        "trust":{"mode":statement.integrity_constraints.as_ref().map(|c| c.trust.clone()),"constraints_digest":statement.key_v4.constraints_digest(),
            "basis":"the request's declarations are the user's assumption about the full source tables at the recorded source versions, in SQLSpec's meaning (constraints_hold(declared_db(db))). GenDB checks only their form (the frontend binder's PostgreSQL rules, one constraint per declaration, the CHECK subset, constraints_wf by compute in lemma_declared_schema); it never reads the data to check them and PostgreSQL never validated them. If they are false on the data, the claims say nothing about that data",
            "trusted_assumption":"declared_integrity_constraints (final-claim.json trusted_assumptions; obligations.json storage_entry_v2)",
            "authors_cannot_change_them":"the declarations come only from the request; gendb_constraints.rs and the entries are framework files generated from them and byte-compared at admission"},
        "declarations":declarations,
        "module":{"file":src.join("gendb_constraints.rs"),"crate_path":"gendb_constraints.rs (module crate::gendb_constraints)",
            "items":module_items,
            "meaning":"declared_schema(): schema_spec()'s tables and columns with the declared SQLSpec constraints (declarations' spec positions above); declared_db(db): db's tables under it. The SQL meaning is still evaluated on db (column schema schema_spec()); the constraints are facts about declared_db(db), whose tables are db's"},
        "query":{"entry":fixed.query.identity,"fixed_entry":fixed.query_entry,"hypothesis":quoted_item(fixed.query.source, "bound_db"),
            "in_words":"every query crate of this run assumes, for every database db bound to its stored parts, constraints_hold(declared_db(db)) in bound_db, whichever storages it reads (with or without the storage opt-in)",
            "how_to_use":["call lemma_declared_schema() and name a declaration: assert(declared_schema()[t].constraints[k] == Constraint::...) by (compute) (spec positions above)",
                "bound_db gives constraints_hold(declared_db(db)); apply the bridge lemmas to d = declared_db(db): d.tables == db.tables, so their conclusions are about db's rows",
                "relate db's rows to the stored data only through each storage's represents and declaration::stored_relations (projections, same row order; see projections)"],
            "bridge_lemmas":bridge_lemmas,
            "bridge_file":src.join("bridge/constraints.rs")},
        "storage":{"opt_in":"uses_declared_constraints: true in a storage's verus-storage.json (manifest schema in task.json and stored-data.json); default false",
            "entry":storage_v2.identity,"fixed_entry":fixed.storage_entry_v2,"precondition":quoted_item(storage_v2.source, "source_witnessed"),
            "obligations":"obligations.json storage_entry_v2 (author items, claim, trusted assumptions)",
            "how_to_use":["the builder may add requires source_witnessed(src@) (gendb_entry::source_witnessed; the entry's abi_build_storage provides it)",
                "in a proof choose the witness: let db = choose|db: Database| db.schema == schema_spec() && db_wf(db) && constraints_hold(declared_db(db)) && source_columns_are_tables(v, db)",
                "lemma_declared_schema() and the bridge lemmas on declared_db(db) give facts about db's tables",
                "link::source::lemma_proj_all_index(db.tables[t], source_cols_tN()) moves a fact to the delivered row at the same position (gendb_source.rs: table_tN(v), source_table_tN(), source_cols_tN())",
                "state in represents what the builder proves (for example an order or a uniqueness the declarations made true); query authors use only represents and the readers' ensures"],
            "cost":"a storage that opts in applies only to runs whose declaration list is identical (the same gendb_constraints.rs: same clauses, same order); in every other run it is listed not applicable (storage_assumes_declared_constraints) and never offered, built or served. Without the opt-in (storage entry v1) a storage is usable in every run, including this one, and query crates of this run compose with it unchanged",
            "interface_rule":"interface files (stores/<name>/interface/**) may not name gendb_constraints (refusal interface_names_declared_constraints, rules.json): the interface is shared with query crates of other runs; use the constraints in builder/** only",
            "tiny_builds":"a builder that opts in builds only the tiny cases the verified evaluator certified (tests.json tiny_cases certification); never a default-filled or uncertified input"},
        "projections":"constraints are stated on the full database db (every table, every declared column). Stored relations and the delivered source are projections of db's tables (proj_all, same row order): a fact reaches them only by row position and stored or delivered column. A key (a, b) with only a stored gives: two rows equal on a differ on the unstored b, never that a is unique. A foreign key into a table that is not read still restricts db and is simply unused",
        "semantics":{"constraints_hold":def("constraints_hold"),"key_holds":def("key_holds"),"fk_holds":def("fk_holds"),"fk_row_holds":def("fk_row_holds"),"check_row_holds":def("check_row_holds"),
            "authority":"spec/constraints.rs in your crate; this summary is descriptive"},
        "supported":{"kinds":"PRIMARY KEY, UNIQUE [NULLS NOT DISTINCT], FOREIGN KEY ... REFERENCES t (...) [MATCH FULL], and CONSTRAINT <name> CHECK (...) (a CHECK must be named)",
            "order":"keys precede the foreign keys that reference them; the declaration order is part of the identity (constraints_digest)",
            "check_subset":"And, Or, Not, IS NULL, boolean columns, comparisons of boolean, integer, numeric and date/timestamp operands (only = and <> on text), columns, literals and the widening casts integer to bigint and integer to numeric: predicates that raise no error and do not depend on a collation; others are refused (check_may_raise, check_text_order, check_subquery)"},
        "tests":"each tiny case's complete database is a heuristic completion of its delivered rows (distinct keys, referenced parent rows, CHECK-accepted values; delivered values and delivered row counts unchanged). Only cases the verified evaluator certifies (rows or an SQL error imply constraints_hold) are run on candidates and storage builders; the others are recorded with their reason (outside_declared_constraints, completion_outside_domain, constraints_undecided) and never run. The exact prepared-data references are unchanged"})
}

/// The prompt fact of a run that declares integrity constraints (the context's `integrity_constraints`): the
/// declarations, their trust and digest, what they mean for each role and the contract file with the details.
pub fn constraints_fact(statement: &Statement, file: &Path) -> Value {
    let mut fact = statement.integrity_constraints_json();
    fact["details"] = json!(file);
    fact["in_words"] = json!("every query crate of this run uses the fixed entry v5: bound_db assumes these declarations on the whole database; a storage may opt in (uses_declared_constraints, storage entry v2) and then applies only to runs with exactly these declarations; the declarations are never checked against the data");
    fact
}

/// A declared constraint in author terms: kind, column names and the referenced table.
fn constraint_meaning(doc: &gendb_frontend::ast::AstDocument, t: usize, constraint: &ConstraintDef) -> Value {
    let names = |table: usize, columns: &[u64]| -> Vec<String> {
        columns.iter().map(|c| doc.tables.get(table).and_then(|d| d.columns.get(*c as usize)).map_or_else(|| format!("#{c}"), |c| c.name.clone())).collect()
    };
    match constraint {
        ConstraintDef::Key { primary, columns, nulls_distinct, .. } => json!({"kind":if *primary { "primary_key" } else { "unique" },"columns":names(t, columns),
            "column_positions":columns,"nulls_distinct":nulls_distinct}),
        ConstraintDef::ForeignKey { columns, table, ref_columns, match_full, .. } => json!({"kind":"foreign_key","columns":names(t, columns),"column_positions":columns,
            "references":{"table":doc.tables.get(*table as usize).map(|d| &d.name),"table_id":table,"columns":names(*table as usize, ref_columns),"column_positions":ref_columns},
            "match_full":match_full}),
        ConstraintDef::Check { name, .. } => json!({"kind":"check","name":name,"predicate":"the CHECK's Pred over the table's row (gendb_constraints.rs)"}),
    }
}

/// The stored-data guide: the read API, request accounting, the storage manifest (with the `uses_declared_constraints`
/// opt-in when the run is `constrained`), how storages are shared, generic representation patterns (pre-aggregates
/// only where the storage policy allows them), the storage choice and policy, and the builds' free-space reserve (the
/// same constant the build guard and the parts writer keep). Under `fixed_flat` no storage is designed or built: the
/// guide keeps the read API, request accounting, sharing and the policy, and its choice is the runtime data access.
pub fn stored_data(stored_rs: &Path, policy: &StoredDataPolicy, constrained: bool, nullable: bool) -> Value {
    let mut patterns = vec![
        json!({"name":"reordering","relation":"exists a permutation pi: stored rows = rels[j] o pi (plus sortedness facts)","use":"sums and counts are order independent (link::join lemma_sum_of_perm); ORDER BY is still fixed by ordered_ok"}),
        json!({"name":"zone maps / block skipping","relation":"per block b: min_b <= value(rels[j][i]) <= max_b for every row i of block b","use":"a reader returns a superset of the matching blocks; the query filters the residual rows exactly; skipped blocks hold no needed row"}),
        json!({"name":"dictionary or bit packing","relation":"decode_block(parts, b) == the values of rels at block b, per block","use":"a block decodes alone; no whole-table decode"}),
        json!({"name":"exact index","relation":"a table's key -> that table's row ranges, with sound and complete lookup postconditions","use":"probe instead of scanning"}),
    ];
    if policy.is_unrestricted() {
        patterns.push(json!({"name":"pre-aggregates","relation":"an aggregate related to rels","use":"useful only to queries whose proof can use it"}));
    }
    let mut guide = json!({"format_version":1,
        "choice":STORAGE_CHOICE_TEXT,"storage_policy":policy.author_view_for(nullable),
        "free_space_reserve":{"bytes":STORAGE_MARGIN_BYTES,
            "meaning":"every storage build keeps at least this many bytes free on the filesystem it writes to, which other work shares; it is not a size limit on your layout: a layout of any or unknown size may be built (canonical column bytes are only advisory)",
            "before_build":"free space must cover the reserve, plus the exact size of an earlier build of the same key when there is one; under pressure this session's own unprotected trial assets are removed first",
            "while_writing":"if the build's actual writes would cross the reserve, it stops and is refused as insufficient_storage (a tool failure, not your candidate's) and its partial output is removed. The free space measured when the session was prepared is free_bytes_at_prepare (workload storage authors: data.json; query authors under the performance objective: performance.json stored_data)"},
        "read_api":{"file":stored_rs,"header":module_doc(STORED_PARTS_SOURCE),"items":public_items("gendb_entry/stored.rs", STORED_PARTS_SOURCE, true)["items"],
            "in_crates":"crate::gendb_entry::stored in every storage and query crate; a query receives one StoredParts per storage use as the fields of gendb_entry::stores::Stores"},
        "request_accounting":"each extent call counts one request, hi - lo elements and (hi - lo) * width bytes (saturating); a returned slice may be read any number of times; overlapping or repeated extents count again; these are requests, not device reads (the page cache, readahead and lazy mapping decide device I/O, which is reported separately and is environment-dependent)",
        "access_in_tests":"trials, profiles, submission evaluations and serving map every part with the kernel's normal readahead and drop no cached pages: process_io.read_bytes is the child's device reads (readahead may read beyond the requested extents; what is already in the page cache, usually most after a first run, is not read again); storage_requests bytes are the extents your readers request. They are different quantities, both descriptive: compare storage_requests bytes and stored bytes across layouts; none is a cold-cache measurement",
        "storage_manifest":{"schema":manifest_schema(constrained, nullable),"example":StorageManifest::example()},
        "sharing":"a storage binds the columns it stores; a query proves its claim for every database bound to the storages it reads, so one storage may serve many statements and every parameter binding. A query's storages must together store every column and table it demands (storage_does_not_cover_demand otherwise). Storages over one table relate to the same canonical row order (same capture), so row positions correspond across them",
        "versions":"registering a storage admits a new immutable version of its name; queries pin exact package ids. An asset is built once per package and capture and reused; adding columns to the capture does not invalidate assets over unchanged tables",
        "patterns":patterns,
        "readability":"state the layout, units and invariants in a short header of each interface and builder module; name parts and readers after what they hold"});
    if policy.is_fixed_flat() {
        // The flat storages are fixed and prepared: no storage design, manifest, build reserve or new version.
        let guide_object = guide.as_object_mut().expect("the guide is an object");
        for storage_design in ["storage_manifest", "free_space_reserve", "versions", "patterns", "readability"] {
            guide_object.remove(storage_design);
        }
        guide_object.insert("choice".into(), json!(FIXED_FLAT_DATA_ACCESS_TEXT));
    }
    guide
}

/// The storage manifest schema authors write: with the `uses_declared_constraints` opt-in in a run that declares
/// integrity constraints, and with the nullable wording of the stored columns in a run whose schema has a nullable
/// column.
pub fn manifest_schema(constrained: bool, nullable: bool) -> Value {
    let schema = if constrained { StorageManifest::schema_with_declared_constraints() } else { StorageManifest::schema() };
    if nullable { StorageManifest::with_nullable_columns(schema) } else { schema }
}

/// Whether some column of the dataset schema `schema` is nullable.
pub fn has_nullable_column(schema: &[TableDef]) -> bool {
    schema.iter().any(|t| t.columns.iter().any(|c| c.nullable))
}

/// ABI bytes per row of a delivered column type (text: its offset only; its bytes are not in the metadata).
fn abi_row_bytes(ty: SourceType) -> u64 {
    match ty {
        SourceType::Int32 | SourceType::Date32 => 4,
        SourceType::Int64 | SourceType::Utf8 => 8,
        SourceType::Decimal { .. } => 16,
    }
}

/// The data facts both roles receive (`data.json`): per schema table, every column with its declared type, whether
/// it can be stored (the delivery rules of `declared_columns`) with its ABI encoding and size at the captured rows,
/// and whether the capture holds it; the captured rows, source version, row-order label and source files. Capture and
/// file metadata only: nothing is scanned, and what the metadata does not record is labelled unavailable.
pub fn data_facts(capture: &PreparedSource, schema: &[TableDef]) -> Value {
    let dataset = capture.dataset();
    let coverage = capture.coverage();
    let tables: Vec<Value> = schema
        .iter()
        .enumerate()
        .map(|(table_id, t)| {
            let captured = coverage.iter().find(|(name, _)| *name == t.name).map_or(&[][..], |(_, ordinals)| ordinals.as_slice());
            let rows = capture.row_count(&t.name);
            let columns: Vec<Value> = t
                .columns
                .iter()
                .enumerate()
                .map(|(ordinal, c)| {
                    let selection = BTreeMap::from([(table_id, BTreeSet::from([ordinal]))]);
                    let storage = match declared_columns(schema, &selection) {
                        Ok(delivered) => {
                            let ty = delivered.tables[0].columns[0].ty;
                            let text = matches!(ty, SourceType::Utf8);
                            let mut storage = json!({"storable":true,"encoding":super::sql_meaning::source_encoding(ty, &super::sql_meaning::sql_type_name(&c.ty)),
                                "abi_bytes_at_captured_rows":rows.map(|r| abi_row_bytes(ty) * (r as u64 + u64::from(text))),
                                "abi_bytes_meaning":if text { "offsets only ((rows + 1) * 8); the text bytes are unavailable" } else { "rows * element width" }});
                            if c.nullable {
                                storage["validity"] = json!({"abi_bytes_at_captured_rows":rows,"meaning":NULLABLE_COLUMN_MEANING});
                            }
                            storage
                        }
                        Err(refusal) => json!({"storable":false,"reason":refusal.to_string()}),
                    };
                    json!({"name":c.name,"ordinal":ordinal,"type":super::sql_meaning::sql_type_name(&c.ty),"nullable":c.nullable,"captured":captured.contains(&ordinal),"storage":storage})
                })
                .collect();
            let files: Vec<Value> = dataset
                .table(&t.name)
                .map(|spec| spec.locations.iter().map(|l| json!({"path":l,"bytes":fs::metadata(l).ok().map(|m| m.len())})).collect())
                .unwrap_or_default();
            json!({"table":t.name,"captured_rows":rows,"source_version":capture.source_version(&t.name),"row_order":capture.row_order_identity(&t.name),
                "source_files":files,"source_format":dataset.table(&t.name).map(|spec| format!("{:?}", spec.format)),"columns":columns})
        })
        .collect();
    json!({"format_version":1,"tables":tables,
        "captured_rows_meaning":"rows of the run's prepared capture (null: the table is not captured yet); every storage over a table relates to its canonical row order (row_order label)",
        "source_version_meaning":"file-metadata stamps and capture row-order labels (no content hash); a changed source makes assets built for the old version inapplicable",
        "capture_extension":"a storage may store a storable column the capture does not hold yet (captured: false): the first storage_build (or evaluation) that needs it imports exactly the missing columns once into a new capture root of this run and reports capture_extension (columns, bytes, time); assets over unchanged tables keep their keys and are not rebuilt",
        "unavailable":{"value_ranges":"not computed: no min/max or Parquet statistics are given here",
            "distinct_counts_and_distributions":"not computed","sortedness_and_clustering":"not computed: the capture keeps the source files' row order, which may or may not be sorted by any column",
            "text_byte_lengths":"not in the metadata given here","compressibility":"not computed",
            "how_to_measure":"read-only scripts over the source files above (at large captured_rows a full pass costs real time; Parquet footer metadata such as row-group min/max, where the files carry it, is readable without a scan; samples answer many questions), or storage_build/trial/profile over a candidate storage; never hash or fingerprint whole datasets, never write into the source or capture directories"},
        "nullable":if has_nullable_column(schema) { NULLABLE_COLUMN_MEANING } else { "only NOT NULL columns can be stored (the ABI carries no null bitmap)" }})
}

/// How a nullable column is delivered and stored (author inputs of a schema with a nullable column).
pub const NULLABLE_COLUMN_MEANING: &str = "a nullable column is delivered and stored with its validity, one byte per row (0: the row is SQL NULL, and its value bytes mean nothing): in gendb_source.rs field t{j}_f{k} has the validity t{j}_v{k} and row i is or_null(t{j}_v{k}[i], value); a flat storage has one more U8 part per nullable column (<COLUMN>_VALIDITY, read_<column>_validity), and its value readers state the value of every row that is not NULL";

/// The data facts a query author receives (`data.json`): the schema, storability and row counts of
/// [`data_facts`], without the source files and without any statistics of the source data. Query authors learn about
/// the data only from the storages' contracts and descriptions, and new storages are built from admitted
/// storages, never from the source.
pub fn query_data_facts(capture: &PreparedSource, schema: &[TableDef]) -> Value {
    let mut facts = data_facts(capture, schema);
    for table in facts["tables"].as_array_mut().into_iter().flatten() {
        if let Some(fields) = table.as_object_mut() {
            fields.remove("source_files");
            fields.remove("source_format");
        }
    }
    facts["unavailable"] = json!({"source_statistics":"query authors get no statistics of the source data: what you know about the data comes from the storages' contracts (represents, the readers' specifications) and descriptions (layout, data_policy, sizes) in storages.json",
        "how_to_measure":"trial/profile over the admitted storages (requested bytes, query time), and reading the storage contracts; never read, scan, hash or fingerprint the source files or the capture directories"});
    facts.as_object_mut().map(|fields| fields.remove("capture_extension"));
    if has_nullable_column(schema) {
        // A query crate has no gendb_source.rs and no delivered columns: say what NULL means where a query reads it.
        facts["nullable"] = json!(QUERY_NULLABLE_MEANING);
        for column in facts["tables"].as_array_mut().into_iter().flatten().flat_map(|t| t["columns"].as_array_mut().into_iter().flatten()) {
            if let Some(validity) = column["storage"].get_mut("validity") {
                validity["meaning"] = json!(QUERY_NULLABLE_MEANING);
            }
        }
    }
    facts
}

/// What a query author reads about a nullable column (`data.json`, a schema with a nullable column).
pub const QUERY_NULLABLE_MEANING: &str = "a nullable column's NULL rows are Val::Null in the database and in every storage's stored_relations; how a storage holds them is stated by its interface (represents and readers)";

/// The source data facts computed at import (min/max, estimated distinct counts, sortedness, key density per column),
/// given only to the workload storage author: the prepared root's `data-facts.json`, written once at
/// preparation (`gendb_storage::import::facts`); a root prepared before facts existed says they are unavailable.
pub fn source_data_facts(capture: &PreparedSource) -> Value {
    let path = capture.data_facts_path();
    match fs::read(&path).ok().and_then(|bytes| serde_json::from_slice::<Value>(&bytes).ok()) {
        Some(facts) => json!({"file":path,"facts":facts}),
        None => json!({"status":"unavailable","reason":"this capture was prepared without source data facts","file":path}),
    }
}

/// The storage budget as authors read it (CURRENT FACTS, Storage; the context's `storage_budget`), from the framework's own accounting
/// (`storage::budget`, the numbers registration enforces): the user's budget over all serving storage, the bytes
/// counted for each serving storage and what is left. The full accounting, with every part, is written to `file`.
pub fn storage_budget(
    store: &ObjectStore,
    capture: &PreparedSource,
    schema: &[TableDef],
    policy: &StoredDataPolicy,
    allowance: Option<u64>,
    file: &Path,
) -> Result<Value, AdmissionError> {
    let current = gendb_storage::versions::CurrentCapture::of(capture).map_err(AdmissionError::tool)?;
    let budget = crate::storage::budget::StorageBudget::of_library(store, &current, schema, policy, allowance)?;
    let mut facts = budget.facts();
    let mut meaning = "all serving storage together stays within budget_bytes (the only hard limit; null: no budget). Counted: every part file of each admitted storage's newest version and of every version an admitted query reads, once (hard-linked shared parts once); the original source files, trial assets and unverified builds do not count. Registration and builds whose measured size estimate exceeds left_bytes are refused (storage_budget_exceeded). Read from the library before this call; other sessions share the budget and may admit storages meanwhile (the catalog tool re-reads it)";
    if policy.is_fixed_flat() {
        // No author registers or builds storage under fixed_flat: the numbers only describe the fixed flat storages.
        meaning = "fixed_flat: the bytes of the fixed flat storages, prepared before this run, for information. No author registers or builds storage in this run and there is no storage budget (budget_bytes null); nothing here limits a query";
        facts["enforced"] = json!("not applicable under fixed_flat: no storage is registered or built by an author");
    }
    write(file, &facts)?;
    let used_by: Vec<Value> = budget.assets.iter().map(|a| json!({"name":a.name,"package":a.package,"counted_bytes":a.own_bytes})).collect();
    Ok(json!({"budget_bytes":allowance,"used_bytes":budget.used_bytes,"left_bytes":budget.left_bytes(),"used_by":used_by,"file":file,"meaning":meaning}))
}

/// The proof-library catalog of `files` (framework library files as they appear under `src_dir`) in
/// `<contract>/proof-library/`.
pub fn write_proof_library(contract: &Path, src_dir: &Path, files: &[FrameworkSource]) -> Result<(), AdmissionError> {
    let library = contract.join("proof-library");
    fs::create_dir_all(library.join("files")).map_err(AdmissionError::tool)?;
    let mut index = vec![];
    for f in files.iter().filter(|f| f.path != "lib.rs" && f.path.ends_with(".rs")) {
        let items = public_items(&f.path, &f.text, true);
        let catalog = library.join("files").join(format!("{}.json", f.path.replace('/', "__")));
        let doc = module_doc(&f.text);
        write(&catalog, &json!({"format_version":1,"file":src_dir.join(&f.path),"module_doc":doc,"items":items["items"]}))?;
        index.push(json!({"file":src_dir.join(&f.path),"role":library_role(&f.path),"summary":doc.chars().take(300).collect::<String>(),
            "items":items["items"].as_array().map_or(0, Vec::len),"catalog":catalog}));
    }
    write(&library.join("index.json"), &json!({"format_version":1,"files":index,
        "use":"every file is framework text of your crates and the authority; look items up in the per-file catalogs (extracted lexically: signature, requires, ensures, decreases, first doc line) and read the regions you need"}))?;
    write(&library.join("patterns.json"), &super::patterns::patterns())
}

/// The role of a framework file in the author's proof library.
pub fn library_role(path: &str) -> &'static str {
    match path {
        p if p.starts_with("spec/") => "meaning (read-only definitions)",
        "exec/relational/eval.rs" | "exec/relational/entry.rs" => "whole-statement evaluator (framework test infrastructure; naming it from agent code is refused)",
        p if p.starts_with("exec/") => "verified executable helpers (callable) and their lemmas",
        p if p.starts_with("bridge/") => "proved bridges between spec and exec forms (callable lemmas)",
        "link/query.rs" | "link/source.rs" => "generic proof toolkit; its fixed link definitions are part of the fixed meaning",
        p if p.starts_with("link/") => "optional generic proof toolkit",
        "schema.rs" => "the dataset schema (fixed; shared by every storage and query crate)",
        "query.rs" => "the emitted statement (fixed)",
        p if p.starts_with("gendb_entry") => "fixed entry and runtime (fork_join, work helpers, layout, stored parts)",
        _ => "generated parameter or ABI file",
    }
}

/// Parallelism: fork_join, worker restrictions and the stored-parts rule inside workers.
pub fn parallel(worker_counts: &[usize]) -> Value {
    let max_workers = gendb_runtime::abi::MAX_WORKERS;
    json!({"format_version":1,
        "mechanism":"gendb_entry::parallel::fork_join(&mut Dispatch, Vec<T: WorkerTask>) runs one thread per task (at most MAX_WORKERS) and joins every handle before it returns; on Ok each output satisfies its task's post; several calls per query or build are allowed",
        "max_workers":max_workers,"configured_worker_counts":worker_counts,
        "theorem_scope":format!("query/build receive workers in [1, {max_workers}]; the proof covers every such count; runs at the configured counts are tests only"),
        "author_obligations":"you choose the partition and the merge and prove coverage (every row exactly once) and the merge; fork_join guarantees only each task's own post",
        "worker_count":"workers is the MAXIMUM number of threads a call may use, not a requirement: the task count of each fork_join call is your choice, and fewer tasks, or a serial path without fork_join, is fine where it is faster",
        "worker_restriction":"WorkerTask::run and declared_rows are no_unwind (inherited): no allocation (Vec::new/push/with_capacity), no spawn, no call that may unwind. Pinned vstd: slice.len() is NOT no_unwind (carry lengths as task fields), and neither is Vec::set (v.set(i, x)); reading s[i] and Vec::len are. Fill a preallocated buffer only through the framework's verified fill helpers (preallocated_outputs)",
        "stored_parts":"extent calls need &mut StoredParts: request the extents on the calling thread and move the returned &'static slices into the tasks",
        "preallocated_outputs":"allocate each task's output on the calling thread (gendb_entry::work::filled(n, x) or a push loop), move it into the task, fill it in run with the verified no_unwind buffer writes of gendb_entry::work (work::put(&mut v, i, x), or a work::TaskBuffer from TaskBuffer::new(capacity, x) filled with push while len() < capacity() when only a bound on the count is known; see proof-library/files/gendb_entry__work.rs.json) and return it as the output; after the join use TaskBuffer::into_vec and Vec::append on the calling thread. Whether to use them is your choice",
        "result_format":"a query may answer Answer::Columns(gendb_entry::results::ResultColumns) instead of Answer::Rows: one vector per output column (Int, Num at one scale, Date, Text as offsets + bytes, or Values of EVal), no allocation per row; its rows are the fixed results::columns_view and the claim also needs results::columns_wf (every column holds rows values); results::push_text and lemma_columns_view_eq help",
        "progress_assumption":"calling_thread_progress (trusted assumption: sufficient memory, stack and threads): the calling thread returns a status only if its may-unwind calls and allocations succeed, its stack is not exhausted and thread creation succeeds; otherwise the process aborts and the call has no outcome (not Capacity)"})
}

/// How queries are timed and assets built in local trials/profiles and official evaluations, the profiling the tools
/// give and the compiler controls of both manifests: both roles' `performance.json`.
pub fn measurement_protocol(worker_counts: &[usize]) -> Value {
    json!({"execution_environment":{"timed_call":"wall time of one library query call over the mapped storage parts; storage builds, compile, process start and result decoding are excluded",
            "process":"one child process per evaluation or trial runs every binding, then every worker count, then every repetition, in sequence over the same mappings",
            "stored_parts":"read-only file mappings made lazily once per child with the kernel's normal readahead and kept for the whole child; cached pages are never dropped, so the warm call may fault pages in from the device while hot calls read pages already in the page cache and already touched by earlier calls of the same child; no cold-cache time is measured",
            "threads":"fork_join spawns fresh OS threads on every call (no pool) and joins them before returning, so thread creation is inside the timed call; the framework does no CPU pinning or NUMA placement; workers is the count the call may use and the task count of each fork_join call (1..=MAX_WORKERS) is your choice, so a serial path is allowed where it is faster (parallel.json)",
            "asset_build":format!("each storage asset (and each tiny input) is built by the storage's compiled library with workers = the largest configured worker count ({}); build_wall_ns is that build's wall time, recorded with the storage and never charged to query time", worker_counts.iter().max().map_or("none".into(), usize::to_string))},
        "profiling":{"tools":"profile: 1 warm + 1 measured call with per-call wall, dispatch ranges, process user/system CPU and calling_thread_share_permille; trial: 1 warm + hot_calls hot calls per cell (default 1; one sample has no spread estimate) with per-use storage requests (requests, elements, bytes) and process device reads",
            "local_jobs":"trial and profile run at any configured worker count and admission binding as often as useful; they never count as submissions and are never the official measurement (tools.json)",
            "external":"the compiled query library runs only inside the framework's worker child (trial, profile, evaluation); the framework supplies no hardware-counter profiler"},
        "compiler_controls":{"manifest_field":"compiler (query and storage manifests)","supported":{"opt_level":"rustc -C opt-level 0..=3 (default 3)","target_cpu":"rustc -C target-cpu (e.g. native; default rustc's)"},
            "scope":"the same choice applies to your local jobs and to the official evaluation of that manifest; no other rustc flag is exposed"}})
}

/// The source rules of every author file, rendered from the central scanner's own tables (the refusal rules and the
/// allowlists it enforces), and the evaluator rule.
pub fn rules() -> Value {
    json!({"format_version":1,
        "verus":"every crate is checked with --no-cheating (refuses assume, admit, external_body, assume_specification)",
        "refusal_list":VERUS_REFUSAL_RULES,"whole_query_evaluator":EVALUATOR_RULE,
        "supported":{"macros":SUPPORTED_MACROS.iter().map(|m| format!("{m}!")).collect::<Vec<_>>(),"derives":SUPPORTED_DERIVES,
            "attributes":ALLOWED_ATTRIBUTES,"verifier_attributes":ALLOWED_VERIFIER_ATTRIBUTES,"external_traits":ALLOWED_EXTERNAL_TRAITS,
            "meaning":"the scanner's own allowlists: every other macro, derive, attribute or external trait implementation is refused (refusal_list says why)"},
        "consequence_for_impls":"implement methods and traits only for types defined at the top level of the same file's verus! block (or your own trait for any type); the traits you may implement are the ones defined at the top level of that same file and supported.external_traits (no Drop, PartialEq, Ord, Hash, Iterator, fmt or operator impls: write a named function, or derive PartialEq/Eq); your own traits may declare associated types without bounds (no `type A: Bound;`, no where clause on the trait); write a generic parameter instead of an `impl Trait` type; for a type you do not define there (framework, std/vstd, another storage root's interface types) write a free function",
        "scope":"a lexical scan of every author file (query agent/**, storage stores/<name>/interface/** and builder/**, and every interface copy in a query crate) with comments and literals removed; framework files are generated and not scanned; the scan is enforced at freeze and again at admission"})
}

/// The pinned vstd source directory, or why there is none on this host.
fn vstd_sources(toolchain: &VerusToolchain) -> Value {
    let vstd = toolchain.home.join("verus/src").join(format!("verus-{}", toolchain.pin.verus.commit)).join("source/vstd");
    if vstd.is_dir() { json!(vstd) } else { json!("not installed on this host; the compiled vstd (libvstd.rlib, vstd.vir) is next to rust_verify") }
}

/// Where an author looks up an API without reading whole files (index.json `commands.api_lookup`): the per-file item
/// catalogs of the framework library under `contract` and the pinned vstd sources.
pub fn api_lookup(contract: &Path) -> Value {
    let vstd = VerusToolchain::from_env().map_or_else(|e| json!(format!("toolchain unavailable: {e}")), |t| vstd_sources(&t));
    json!({"framework_items":contract.join("proof-library/files"),"vstd_sources":vstd,
        "use":"look up exact signatures before reading whole files: framework_items holds one catalog per framework file (<path with / replaced by __>.json: signature, requires, ensures, decreases, first doc line of every public item); grep -rn \"fn <name>\" your crate's src and <vstd_sources>; then read the regions you need"})
}

/// The foreground direct-verification helper (`verus-tmp/direct-verus.sh`), rendered from the framework's argv.
const DIRECT_VERUS_TEMPLATE: &str = include_str!("direct_verus.sh");

/// The argv options `verus_args` would pass for a crate of `kind` in verify mode, after its crate root and without
/// the two JSON output options, so that rust_verify prints its human-readable diagnostics.
fn direct_verus_options(kind: CrateKind, out: &Path) -> Result<String, AdmissionError> {
    let krate = FrozenCrate::from_recorded_author_files(PathBuf::from("crate"), vec![], vec!["lib.rs".into()]);
    let argv = verus_args(&krate, &crate_options(kind, &CompilerChoice::default()), VerusMode::Verify, out).map_err(AdmissionError::tool)?;
    Ok(argv[1..].iter().filter(|a| !matches!(a.as_str(), "--output-json" | "--error-format=json")).map(|a| shell_word(a)).collect::<Vec<_>>().join(" "))
}

/// Write the executable direct-verification helper into `run_dir` (the directory direct runs start from) and return
/// its path.
fn write_direct_verus(run_dir: &Path, toolchain: &VerusToolchain, environment: &str) -> Result<PathBuf, AdmissionError> {
    let script = DIRECT_VERUS_TEMPLATE
        .replace("@RUN_DIR@", &shell_word(&run_dir.display().to_string()))
        .replace("@QUERY_OPTIONS@", &direct_verus_options(CrateKind::Query, run_dir)?)
        .replace("@STORAGE_OPTIONS@", &direct_verus_options(CrateKind::Storage, run_dir)?)
        .replace("@ENVIRONMENT@", environment)
        .replace("@RUST_VERIFY@", &shell_word(&toolchain.rust_verify.display().to_string()));
    let path = run_dir.join("direct-verus.sh");
    fs::write(&path, script).map_err(AdmissionError::tool)?;
    fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).map_err(AdmissionError::tool)?;
    Ok(path)
}

/// Toolchain facts and exact commands for a query crate at `query_crate` and a storage crate (with a placeholder
/// crate directory), rendered from the framework's own argv, and the foreground helper for direct runs.
pub fn toolchain_file(workspace: &Path, query_crate: &Path) -> Result<Value, AdmissionError> {
    let toolchain = VerusToolchain::from_env().map_err(AdmissionError::tool)?;
    let tmp = workspace.join("verus-tmp");
    fs::create_dir_all(&tmp).map_err(AdmissionError::tool)?;
    let environment = toolchain.environment(&tmp).iter().map(|(k, v)| shell_word(&format!("{k}={v}"))).collect::<Vec<_>>().join(" ");
    let command = |kind: CrateKind, crate_dir: &Path, mode: VerusMode, out: &Path| -> Result<String, AdmissionError> {
        let krate = FrozenCrate::from_recorded_author_files(crate_dir.to_path_buf(), vec![], vec!["lib.rs".into()]);
        let argv = verus_args(&krate, &crate_options(kind, &CompilerChoice::default()), mode, out).map_err(AdmissionError::tool)?;
        Ok(format!("env -i {environment} {} {}", shell_word(&toolchain.rust_verify.display().to_string()), argv.iter().map(|a| shell_word(a)).collect::<Vec<_>>().join(" ")))
    };
    let storage_crate = workspace.join("<storage crate_dir>");
    let query_verify = command(CrateKind::Query, query_crate, VerusMode::Verify, &tmp)?;
    let storage_verify = command(CrateKind::Storage, &storage_crate, VerusMode::Verify, &tmp)?;
    let direct = write_direct_verus(&tmp, &toolchain, &environment)?;
    let direct_query = format!("{} query {}", shell_word(&direct.display().to_string()), shell_word(&query_crate.display().to_string()));
    let direct_storage = format!("{} storage '<storage crate_dir>'", shell_word(&direct.display().to_string()));
    Ok(json!({"format_version":1,"pin":verus_pin(),
        "vstd_sources":vstd_sources(&toolchain),
        "vstd_lookup":"search the pinned vstd sources (grep -rn \"fn <name>\" <vstd_sources>) for exact API specs: seq.rs and seq_lib.rs, slice.rs, layout.rs, std_specs/{vec,slice,num,option,result}.rs, arithmetic/{mul,div_mod,power,power2}.rs, set.rs, set_lib.rs, map.rs, multiset.rs",
        "direct_profiling":format!("rust_verify --profile writes .verus-solver-log into the CURRENT WORKING DIRECTORY: run direct verification from {} (lib.rs is an absolute path in the commands) and add --log-dir {}/verus-log when you use --log options; an extra file inside a crate's author roots is refused by the file-set rule", tmp.display(), tmp.display()),
        "rust_verify":toolchain.rust_verify,"z3":toolchain.z3,"rust_lib":toolchain.rust_lib,"environment":environment,
        "query_crate":{"verify":query_verify,"compile":command(CrateKind::Query, query_crate, VerusMode::VerifyAndCompile, &tmp.join("FRESH_OUTPUT_DIRECTORY"))?,
            "framework_files":"written into the crate by the check tool for your declared storage uses"},
        "storage_crate":{"verify":storage_verify,"compile":command(CrateKind::Storage, &storage_crate, VerusMode::VerifyAndCompile, &tmp.join("FRESH_OUTPUT_DIRECTORY"))?,
            "framework_files":"written into the crate by the storage_check tool; replace <storage crate_dir> with your crate directory"},
        "commands_source":"rendered from the framework's own argv (the same function the tools and submissions use) with the default compiler choice; a manifest's compiler field changes -C opt-level and -C target-cpu",
        "direct_verus":{"script":direct,
            "usage":"direct-verus.sh query|storage CRATE_DIR [rust_verify options]: the pinned rust_verify on CRATE_DIR/src/lib.rs with the environment and options of query_crate.verify or storage_crate.verify, human-readable diagnostics instead of JSON, run from this directory",
            "completion":"it stays in the foreground until rust_verify exits, passes through all of rust_verify's output, then prints `direct-verus: rust_verify exit status N` and exits with N (0 only when rust_verify reported no error in what it checked). Every failure returns as soon as rust_verify exits, including refused options, which exit 255 after one `Error:` line and no verification summary",
            "run":"call it as an ordinary foreground Bash command and read its output and exit status when the call returns; to shorten long output, redirect it (`> <log> 2>&1`) and read the log after the call returns, never while it runs. The Bash call's timeout does not stop it (a call reaching its timeout is moved to the background and keeps running); bound it yourself below the call's timeout with `timeout -k 10 <seconds>` before the script: the TERM reaches the script, which stops rust_verify's group. Do not start it in the background and poll a log for completion text: text that never appears (for example after a refused option) makes the poll wait for its whole timeout",
            "process_group":"rust_verify runs in its own process group, recorded in direct-verus-<group>.pgid next to the script while it runs; `kill -TERM -- -<group>` stops it, and a TERM, INT or HUP to the script stops it too"},
        "scoped_verify":{"status":"DIAGNOSTIC ONLY while iterating: a scoped run checks part of the crate, so it is never a submission and never the official check (the framework verifies the whole frozen crate); the verify tool and submissions stay the primary checks",
            "query_module":format!("{direct_query} --verify-only-module agent::<module>"),
            "query_function":format!("{direct_query} --verify-only-module agent::<module> --verify-function <function>"),
            "storage_modules":format!("{direct_storage} --verify-module builder --verify-module stores::<name>::interface"),
            "flags":"--verify-module M: M and its descendants (repeatable); --verify-only-module M: M without descendants (repeatable); --verify-function F: one function (a unique name substring, or * at either end) of exactly one module named by a single --verify-only-module M, or of the crate root with --verify-root; rust_verify refuses --verify-function together with --verify-module, without either, or with more than one of them (its --help wording \"verify-module\" is inexact)",
            "same_options_elsewhere":"the same scope options can be appended to query_crate.verify or storage_crate.verify when you want JSON output; run those in the foreground as well"},
        "note":"run rust_verify directly as above or through direct_verus; its TMPDIR exists; never use /tmp",
        "compiler_control":{"manifest_field":"compiler","default":CompilerChoice::default()}}))
}

/// The failure classes of every refusal and failed evaluation.
pub fn failure_classes() -> Value {
    json!({"format_version":1,"field":"failure_class on every refused local job and failed evaluation",
        "classes":FailureClass::ALL.iter().map(|c| (c.name().to_string(), json!(c.meaning()))).collect::<serde_json::Map<_, _>>(),
        "named_reasons":{"storage_does_not_cover_demand":"missing_input: the query's storages do not store a demanded column or table; add a storage use or create a storage that stores it",
            "unknown_source_column":"missing_input: a storage manifest names a table or column the schema does not have",
            "storage_budget_exceeded":"refusal: registering (or building, when an earlier build of the same storage measured its size) would take the serving storage over the user's storage budget (data_allowance.live_bytes, the bound on all serving storage together; CURRENT FACTS, Storage)",
            "storage_coverage_incomplete":"refusal (workload storage): the submitted storages plus the usable admitted ones do not store every column of every table; the refusal lists each missing table.column",
            "storage_policy_declaration_missing":"refusal: under storage_policy physical_only a storage manifest needs data_policy, one {part, table, kind, why} entry per part",
            "storage_policy_declaration_invalid":"refusal: a data_policy entry names an unknown part or a table the storage does not store, a part has no entry or two, or (physical_only) a part is of kind query_derived_values",
            "storage_not_built_from_admitted":"refusal: a query author's new storage must be built from admitted storages (manifest built_from), never from the source files",
            "storage_content_differs":"refusal: an admitted storage's declaration (tables, ordinals, names, SQL types) does not match the run's schema, so it cannot be used",
            "closure_stale":"not a refusal: an admitted storage whose framework files changed since admission is re-verified once on first use (storages.json closure)",
            "storage_policy_ineligible":"refusal: an admitted storage was not registered under the run's storage_policy and the user did not list it",
            "storage_policy_excluded":"refusal: the user's review excluded this storage package under the run's storage_policy (a policy decision, not a failed proof); use or create a storage within the policy",
            "no_storage_asset":"serving found no asset of a storage for the current data (built offline, never while serving)"}})
}

/// What the run's validation policy checks besides the proofs, for `role` over its `statements` (`validation.json`).
pub fn validation(role: AuthorRole, statements: &[&QuerySession]) -> Value {
    let Some(first) = statements.first() else { return Value::Null };
    let validation = &first.preflight.validation;
    let proof = "every submitted crate is verified whole by Verus (--no-cheating) against its fixed entry claim: for a query the fixed final SQL claim (SQLSpec semantics of the statement for every valid database bound to its storages, every allowed binding and every worker count); for a storage the fixed storage entry (its parts represent the source rows it stores; its readers' ensures). This proof is the correctness claim; no check below replaces or weakens it";
    if !validation.formal {
        return json!({"format_version":1,"policy":validation.record(),"proof":proof,
            "tests":"tiny cases labelled by verified SQLSpec evaluators (statements/<i>/tests.json) and exact comparison with independent prepared-data references at every admission binding: tests, never proof"});
    }
    let saved: Vec<Value> = statements
        .iter()
        .map(|s| {
            let statement = s.statement();
            json!({"statement_key":statement.key_v4_id,"benchmark_bindings":statement.benchmark.iter().map(|&b| json!({"binding":statement.bindings[b].name,
                "saved_answers":s.preflight.validation.answers_at(b).iter().map(|a| &a.engine).collect::<Vec<_>>()})).collect::<Vec<_>>()})
        })
        .collect();
    let mut record = json!({"format_version":1,"policy":validation.record(),"proof":proof,
        "not_run":"no tiny (small-database) cases, no verified evaluator builds, no reference engine (DataFusion) runs, and no full-data runs at the generated domain bindings (minimum, maximum, interior): correctness is established by the proof, not by tests",
        "query_evaluation":"after the proof, the query runs on the full prepared data at every benchmark binding and configured worker count; out-of-domain parameter probes must return ParamRefused; each result is compared with the saved answers of other engines at that binding where given, and a result that agrees with none of them is not admitted (failure saved_answer_disagreement, an execution failure). Without a saved answer the result is recorded not_compared",
        "agreement_rules":{"values":"text, integers and dates exactly; other numerics equal as decimals or within the relative tolerance (other engines may return floating point, e.g. AVG, or another decimal scale)","order":"your rows must be in ORDER BY order; the ORDER BY key sequence must agree row by row, and rows inside one tie class (equal keys) may come in another order","limit":"with LIMIT, the last ORDER BY tie class may hold another choice of that class: only its count and keys are compared","engines":"each engine's verdict is recorded; agreement with at least one engine is required (saved_answers_agree when all agree, saved_answers_agree_partly otherwise)",
            "meaning":"agreement with other engines checks the trusted base and the environment; it is not a proof and is reported separately from it"},
        "diagnostics":"trial and profile apply the same comparison at the bindings they run; their timings, and builds with verification not_run, stay diagnostic only. Submitted code is always verified whole",
        "how_to_work":"there are no small-database tests to catch a logic error: let the proof find it (verify early, by module), and run the query on the full data with trial to see the saved-answer comparison",
        "saved_answers":saved});
    if role == AuthorRole::WorkloadStorage {
        record["storage_admission"] = json!("a storage submission is admitted when every storage crate verifies whole against the fixed storage entry, each stored library builds its asset over the full prepared data with status Ok, the submitted storages together store every column of every table (complete lossless coverage), and the serving bytes fit the storage budget. No query result is required and no tiny-input build runs; query authors are evaluated later in their own sessions");
    }
    record
}

/// The tools of a role: what each does, its arguments and its output.
/// `tools.json`: the tools offered to `role` (every tool, or under `fixed_flat` (`flat`) all but the storage tools).
pub fn tools_file(role: AuthorRole, statements: &[&QuerySession], worker_counts: &[usize], flat: bool) -> Value {
    let bindings: Vec<Value> = statements
        .iter()
        .map(|s| json!(s.statement().bindings.iter().map(|b| json!({"name":b.name,"origin":b.origin,"arguments":b.texts})).collect::<Vec<_>>()))
        .collect();
    let mut file = json!({"format_version":1,"server":format!("{} (typed MCP)", tools::SERVER_NAME),"role":role,
        "tools":tools::offered_actions(flat).iter().map(|a| (a.name().to_string(), json!(tool_summary(*a, flat))))
            .chain([(tools::WAIT_TOOL.to_string(), json!(tools::WAIT_SUMMARY))]).collect::<serde_json::Map<_, _>>(),
        "arguments":{"storage":"storage tools: a verus-storage.json inside the workspace","candidate":"query tools: a verus-query.json inside the workspace",
            "job_name":"1..64 portable identifier","wait_seconds":format!("wait only, optional, 0..={}: the most the call waits (default the maximum)", tools::MAX_WAIT_SECONDS),
            "statement":if role == AuthorRole::WorkloadStorage { json!("query tools: the workload statement index (workload.json) of the diagnostic query crate") } else { json!("not used: the query tools run this session's statement") },
            "workers":format!("profile: required, one of {worker_counts:?}; trial: optional (absent: every configured worker count)"),"modules":"verify/storage_verify only; crate module paths",
            "arguments":json!({"meaning":"trial/profile only, optional: the free parameters' argument texts in slot order, equal to the arguments of one admission binding (benchmark bindings, origin benchmark, are admission bindings too); default the first binding","admission_bindings":bindings}),
            "timeout_seconds":format!("trial/profile only, optional, 1..={CHILD_TIMEOUT_SECONDS}: bound of each query child of the job. {}", tools::CHILD_TIMEOUT_MEANING),
            "hot_calls":format!("trial only, optional, at least 1: hot calls per cell after the warm call; default {DEFAULT_TRIAL_HOT_CALLS} (fast feedback; one sample gives no spread estimate); official evaluations and final measurements always run 1 warm + 3 hot"),
            "verification":"trial/profile only, optional: whole_crate (default: the verify-and-compile run submissions use) or not_run (the query crate compiled with rust_verify --no-verify; see query_tool_verification)"},
        "output_schema":{"status":"completed | refused","failure_class":"one of failure-classes.json on refusal","error":"text (Verus diagnostics verbatim; for mismatches the expected and returned rows)",
            "result_record":"path of the full record","summary":"status, verification counts, per (binding, workers) real-data cells with storage requests, tiny-case count, storage sizes and build time, registration"},
        "result_fields":{
            "storage_build":"status built; package; asset {storage_bytes (stored parts), canonical_column_bytes (the stored columns at ABI widths, text offsets only), build_wall_ns, parts, built_now}; part_labels; layout; items (the declared functions as Verus reported them); tiny_builds; capture_extension (null when no column was imported); build.reused",
            "storage_register":"storage_build's fields + registration.use_as {name, admitted: package id} for a query manifest",
            "storage_budget_now":"every storage tool result: {budget_bytes, used_bytes, left_bytes, read_unix_ms, meaning}: the storage budget as it stood when the job finished (other sessions share it; a snapshot, not a reservation)",
            "trial":"matrix {cells: one line per cell, all_cells_meet_bar}; crate_version (short identity of the exact crate content); real_data.cells[] per (binding, workers): status (exact: equals the prepared reference; saved_answers_agree / saved_answers_agree_partly: agrees with every / some saved answer of other engines (per-engine verdicts in comparison); not_compared: neither exists at that binding; otherwise the recorded outcome), warm_wall_ns, hot_wall_ns, median_hot_wall_ns, min_hot_ns, max_hot_ns, target_ns, bar_ns, met_bar, speedup_over_target, storage_requests per use {requests, elements, bytes}, process_io {read_bytes}; storage[] per use {name, package, storage_bytes, build_wall_ns, asset_built_now}; boundary (tiny cases, or not_run under the validation policy formal_proofs). With verification not_run: status diagnostic_unverified, verification verification_not_run and a note; the job record (also when refused) carries verification verification_not_run and diagnostic_unverified true",
            "profile":"trial's fields with 1 measured call, plus dispatch {spawned, joined, ranges}, process user/system CPU and calling_thread_share_permille",
            "catalog":"storage_budget {budget_bytes, used_bytes, left_bytes, used_by, file}; catalog {storages: [{name, package, current, applicable, storage_bytes}], file}; refreshed_unix_ms; meaning",
            "authority":"each job's result.json (result_record) holds the full record"},
        "query_tool_verification":{"default":"trial and profile first run compile (the whole-crate verify-and-compile, cached for unchanged sources): the query crate, including a diagnostic one, must verify whole with 0 errors before it runs on data",
            "not_run":"verification \"not_run\" compiles the same frozen query crate with rust_verify --no-verify instead: no proof obligation is checked; the freeze (manifest, storage uses, coverage, composition, source rules, framework files), storages and assets, binding, worker count, result comparisons and tiny cases (as the validation policy runs them) are unchanged, and --no-cheating stays in the command. Compiler errors and refusals are returned as usual; a wrong answer is a named mismatch. Every result, including a failure, is labelled diagnostic_unverified / verification_not_run: never a submission, proof, official measurement or early-stop input, and admission refuses a build made with --no-verify. An unverified build is cached separately and never answers a verified run. A later submission of the same code is verified whole and tested from scratch",
            "limits":"an unverified storage build (storage_build with verification not_run) is a diagnostic only, never registrable, admissible or submittable; instrumentation inside the crate (clock reads, logging) needs external_body or assumptions, which the source rules and --no-cheating refuse in every job, so it stays in your own scratch builds; a module-scoped verify is for iterating only"},
        "diagnostics":"every job is a diagnostic: it never counts as a submission and is never the official measurement; jobs run one at a time in the session's framework service. storage_register admits a storage version into the library (immutable; reusable by every later query)",
        "records":"each call is a numbered job with request.json, a frozen snapshot and result.json under the call's local-jobs directory",
        "child_timeout_seconds":CHILD_TIMEOUT_SECONDS,"direct_use":"you may also run rust_verify yourself (toolchain.json)"});
    if flat {
        // The storage tools are not offered: describe only the query tools' arguments, fields and limits.
        let arguments = file["arguments"].as_object_mut().expect("arguments object");
        arguments.remove("storage");
        arguments.insert("modules".into(), json!("verify only; crate module paths"));
        let fields = file["result_fields"].as_object_mut().expect("result_fields object");
        for storage_field in ["storage_build", "storage_register", "storage_budget_now"] {
            fields.remove(storage_field);
        }
        file["output_schema"]["summary"] = json!("status, verification counts, per (binding, workers) real-data cells with storage requests, tiny-case count, storage sizes");
        file["query_tool_verification"]["limits"] = json!("instrumentation inside the crate (clock reads, logging) needs external_body or assumptions, which the source rules and --no-cheating refuse in every job, so it stays in your own scratch builds; a module-scoped verify is for iterating only");
        file["diagnostics"] = json!("every job is a diagnostic: it never counts as a submission and is never the official measurement; jobs run one at a time in the session's framework service");
    }
    file
}

/// What `action` does as tools.json states it; under `fixed_flat` (`flat`) trials use the prepared flat assets and
/// the catalog only describes them.
fn tool_summary(action: ToolAction, flat: bool) -> String {
    let trial_assets = if flat { "the prepared flat storage assets (never built)" } else { "the storage assets (built once if missing)" };
    let summary = match action {
        ToolAction::StorageCheck => "freeze a storage crate snapshot (manifest, author roots, source rules, framework files), write its framework files into your storage crate, and report which statements it covers; no Verus",
        ToolAction::StorageVerify => "storage_check + one Verus verification of the whole storage crate (or of the named modules, diagnostic only)",
        ToolAction::StorageCompile => "storage_check + the whole-crate verify-and-compile run of the storage crate",
        ToolAction::StorageBuild => "storage_compile (cached) + the checked build recorded and its asset built once over the prepared data by the stored library + tiny-input builds when the validation policy runs them (validation.json); stored bytes, canonical column bytes, build time, parts",
        ToolAction::StorageRegister => "storage_build (cached) + admission of the storage package (a new version of its name; nothing is rebuilt); returns the package id to use as {\"admitted\": id}",
        ToolAction::Check => "freeze a query crate snapshot over its storage uses (coverage, composition, source rules), write the use-specific framework files into your query crate; no Verus",
        ToolAction::Verify => "check + one Verus verification of the whole query crate (or of the named modules, diagnostic only)",
        ToolAction::Compile => "check + the single whole-crate verify-and-compile run used for submissions",
        ToolAction::Trial => return format!("compile (cached for identical crate content) + {trial_assets} + the query over the whole matrix by default (every benchmark binding x configured worker count; workers/arguments narrow it) under the host timing lease, 1 warm + hot_calls hot per cell (default 1, no spread estimate), compared with the prepared reference or the saved answers of other engines (validation.json) and reported against the user's target and early-stop bar (matrix: median, min, max, met per cell), plus the tiny cases when the validation policy runs them (skipped when identical crate content over the same assets passed them); per-use requested bytes versus stored bytes and child device reads; verification not_run builds the query crate unverified (diagnostic_unverified)"),
        ToolAction::Profile => "trial with 1 warm + 1 measured call, dispatch ranges and per-call wall, process and calling-thread CPU; verification not_run as for trial",
        ToolAction::Catalog if flat => "re-read the library now: rewrites storages.json (the flat storages with their prepared assets) and storage-budget.json (their bytes, for information; no budget applies) and returns the storage list",
        ToolAction::Catalog => "re-read the library now: rewrites storages.json (every admitted storage version, including those admitted by other sessions since this session was prepared) and storage-budget.json, returns the budget (used, left) and the storage list; a snapshot, not a reservation (registration enforces the budget)",
    };
    summary.to_string()
}

/// The accounting and guards file.
pub fn accounting(limits: &Limits) -> Value {
    json!({"format_version":1,
        "recorded":"provider-reported USD, tokens and elapsed time of every author call (including failed calls and retries), per model as reported, iteration count, every local job (internal candidate version) and every framework evaluation; framework time is never charged as provider cost; the workload storage author and each query author are accounted separately",
        "guards":limits.active(),"guard_meaning":"ceilings chosen by the user, not quotas; \"unset\" means no guard"})
}

/// The admitted storages of the library for the current capture that the storage policy allows (`storages.json`),
/// with read-only copies of their interfaces under `<workspace>/storages/`. `demands`: `(statement key, demanded
/// columns)` per statement. Excluded storages are only counted.
pub fn storages_catalog(
    store: &ObjectStore,
    capture: &PreparedSource,
    schema: &[TableDef],
    workspace: &Path,
    demands: &[(String, gendb_verification::obligations::DeclaredSource)],
    policy: &StoredDataPolicy,
) -> Result<Value, AdmissionError> {
    let current = CurrentCapture::of(capture).map_err(AdmissionError::tool)?;
    let mut storages = vec![];
    let mut excluded = 0;
    for storage in catalog::admitted_storages(store, &current, schema)? {
        if policy.ineligible(store, storage.package_id, &storage.package.name)?.is_some() {
            excluded += 1;
        } else {
            storages.push(storage);
        }
    }
    // An applicable storage is described in full (its interface copied for reading); an inapplicable one is one line.
    let views: Vec<Value> = storages
        .iter()
        .map(|storage| match &storage.applicability {
            Ok(()) => catalog::storage_view(store, storage, &workspace.join("admitted-storages").join(format!("{}@{}", storage.package.name, &storage.package_id.to_hex()[..8])), demands),
            Err(reason) => Ok(json!({"name":storage.package.name,"package":storage.package_id,"applicable":false,"not_applicable_reason":reason})),
        })
        .collect::<Result<_, _>>()?;
    // Storages that assume another declaration set (or any, in a run without declarations) are listed, never offered.
    let other_constraints = storages.iter().filter(|s| s.applicability.as_ref().is_err_and(|r| r.starts_with("storage_assumes_declared_constraints"))).count();
    let mut catalog = json!({"format_version":1,"storages":views,
        "use":"name a storage in your query manifest as {\"name\": <name>, \"admitted\": <package>} (use_as); its interface files are copied into your query crate by the framework at stores/<name>/interface/** (read-only). Applicable storages were checked over this schema; an asset for the current data is reused, a missing one is built once by the storage's admitted library at your first evaluation or trial",
        "all_versions":"every admitted version of every name the storage policy allows is listed, newest first per name",
        "excluded_by_storage_policy":excluded});
    if policy.is_fixed_flat() {
        // Flat assets are prepared before the run from the capture's column files and never built for a query.
        catalog["use"] = json!("name each flat storage your query reads in your query manifest as {\"name\": <name>, \"admitted\": <package>} (use_as), one per table it demands; each flat storage stores one table, so its own statement_coverage says covers false and lists as missing what the other flat storages of the statement supply. Its interface files are copied into your query crate by the framework at stores/<name>/interface/** (read-only). Every asset was prepared before this run from the capture's column files (prepare-flat-storage) and is reused; a use whose asset is missing is refused (flat_storage_not_prepared), never built");
        for view in catalog["storages"].as_array_mut().expect("storages list").iter_mut().filter(|view| view["applicable"] == true) {
            view["asset_note"] = json!(if view["asset_for_current_data"].is_null() {
                "not prepared for the current capture: a use is refused (flat_storage_not_prepared), never built"
            } else {
                "prepared for the current capture before this run: using it builds nothing; build_wall_ns is the preparation's publication time (hard links or copies of the capture's column files), not a builder run"
            });
        }
    }
    if other_constraints > 0 {
        catalog["not_applicable_declared_constraints"] = json!({"storages":other_constraints,
            "meaning":"admitted storages whose builders assume a declaration set other than this run's (assumed_constraints): listed with applicable false and the reason storage_assumes_declared_constraints, never offered, built or served here"});
    }
    Ok(catalog)
}
