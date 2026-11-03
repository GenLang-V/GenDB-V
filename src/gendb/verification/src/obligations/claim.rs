//! What the fixed entries claim, what an author must supply, and what the claims rely on without proof: the entry v3
//! (saved route), the storage entries v1 and v2 (v2: v1 whose builder assumes the declared integrity constraints), the
//! derived storage entry (a storage built from admitted storages), the query entry v4, the query entry v5 (v4 under
//! declared integrity constraints) and the engine entry v1 (one engine for a schema, statements as AST bytes;
//! [`ENGINE_CLAIM_V1`]). These are texts for the author contract (the brief), the claim record and the TCB record; the
//! fixed entries are the check.
//!
//! The claim is total correctness relative to each entry's outcome contract: inside the declared domains and under the
//! trusted assumptions every call terminates and returns exactly one outcome of the contract ([`TERMINATION`] lists
//! them; `WorkerFailed`, which the fixed postconditions permit without a condition, is excluded by the trusted
//! assumption `worker_failure`, as process aborts are by `calling_thread_progress`). The final theorems
//! ([`THEOREMS`], [`STORAGE_THEOREMS`], [`QUERY_THEOREMS`]) are partial-correctness statements (what a returned
//! outcome means); termination is a [`ProvedProperty`], proved by Verus's termination checks rather than stated in a
//! theorem. Both rest on the trusted base (the toolchain items and the entry's [`TrustedAssumption`]s).

use serde::Serialize;

/// Paths (relative to the crate) of the final theorems of a v3 candidate crate, named by every claim record.
pub const THEOREMS: &[&str] = &[
    "gendb_entry::theorem_end_to_end",
    "gendb_entry::corollary_inside_capacity",
    "gendb_entry::theorem_build_total",
    "gendb_entry::theorem_build_then_query",
];

/// Definitions of the `link` library module that the fixed entry and the generated source module state the claim
/// with: what "the delivered columns of a source table", "a text value" and "the answer rows" mean. They are part of
/// the fixed meaning (like `spec`), copied as framework files and compared byte for byte at admission; the rest of
/// `link` is an optional proof toolkit. Their closure outside `spec` is the executable value view `view_rows` applies
/// (`exec::value::{EVal, view_row}`, the `View` of `EVal`), library text compared byte for byte in the same way.
pub const FIXED_LINK_DEFINITIONS: &[&str] = &[
    "link::query::TextCol",
    "link::query::TextView",
    "link::query::text_wf",
    "link::query::text_at",
    "link::query::view_rows",
    "link::query::proj",
    "link::query::proj_all",
    "link::source::proj_columns",
    "link::source::rows_in_columns",
    "link::source::cols_in_table",
];

/// One item the author's `crate::agent` module must provide.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct AgentItem {
    pub name: &'static str,
    pub signature: &'static str,
    pub obligation: &'static str,
}

/// A named assumption of the fixed entry beyond Verus/vstd/rustc. The `id` is recorded as `entry_assumption:<id>`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct TrustedAssumption {
    pub id: &'static str,
    pub statement: &'static str,
    pub relied_on_by: &'static str,
}

/// A property of every call that is part of the claim but stated by no final theorem, and that is not a trusted
/// assumption: Verus proves it with checks it enforces on the whole crate. Like the theorems it rests on the trusted
/// base; `relies_on` names the entry assumptions it needs (each in every entry's list of trusted assumptions).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct ProvedProperty {
    pub id: &'static str,
    pub statement: &'static str,
    pub proved_by: &'static str,
    pub relies_on: &'static [&'static str],
}

/// The proved properties of every entry's claim, besides its final theorems (the same for every entry).
pub const PROVED_PROPERTIES: &[ProvedProperty] = &[TERMINATION];

/// Termination, and with the final theorems total correctness relative to the entry's outcome contract.
pub const TERMINATION: ProvedProperty = ProvedProperty {
    id: "termination",
    statement: "Total correctness relative to the outcome contract. For every database in the declared domains (the \
                schema, db_wf and the declared constraints) that the input is bound to by the trusted delivery, and \
                under the trusted assumptions, every call of the entry terminates and returns exactly one of these \
                outcomes, whatever its arguments and worker count. Query entries: rows allowed by ⟦Q⟧(db) (Ok: \
                ordered_ok), the spec's SQL error (SqlError(e) only when the statement's meaning is exactly the \
                error e), Capacity (only outside capacity_domain), ParamRefused (exactly when the arguments are not \
                a binding in the declared parameter domain) or Refused (exactly for a worker count outside \
                1..=MAX_WORKERS, 64); for a binding in the domain inside capacity_domain the outcome is decided: Ok \
                when the statement has a value, SqlError(e) when its meaning is the error e. Storage entries and the \
                v3 build: Ok with parts that represent the delivered relations, InvalidInput (only outside the \
                declared column domain, never on the actual source) or Refused (exactly for a worker count outside \
                1..=MAX_WORKERS or column shapes the verified binder does not accept). Derived storage entry: Ok \
                with parts that represent the stored relations of every database bound to the sources, or Refused \
                (exactly for a worker count outside 1..=MAX_WORKERS). The fixed postconditions (query_meets, \
                storage_build_meets, build_meets, derived_build_meets) also permit WorkerFailed without a condition \
                on the input; it arises only from a failed join in fork_join, and under the trusted assumption \
                worker_failure (the thread runtime reports a failed join only when a worker panics; workers are \
                verified and no_unwind) it does not occur. So a call need not return rows. The final theorems state \
                what each outcome means (partial correctness); this property adds that every call ends in one. A \
                process abort (allocation failure, stack exhaustion, failed thread creation, an unwind on the \
                calling thread) ends the call with no outcome; the trusted assumption calling_thread_progress \
                (sufficient memory, stack and threads) excludes it. No time bound.",
    proved_by: "Verus's termination checks, which the verifier enforces on the whole crate rather than states in a \
                theorem: a decreases measure on every exec loop and recursive function, and call-graph cycle checks. \
                The author-source scan refuses the forms the pinned Verus does not track (dyn_trait_object, \
                vstd_rwlock, the verifier_attribute escapes exec_allows_no_decreases_clause and assume_termination, \
                associated_type_bound, impl_trait_type, external_trait_impl).",
    relies_on: &[
        "verus_termination_checks",
        "trusted_specs_terminate",
        "fair_scheduling",
        "trusted_shim_returns",
        "os_completes_or_kills",
        "calling_thread_progress",
        "worker_failure",
    ],
};

/// What the author's `crate::agent` module of a v3 candidate must provide (text for the author inputs).
pub const AGENT_OBLIGATIONS: &[AgentItem] = &[
    AgentItem {
        name: "decode",
        signature: "pub open spec fn decode(parts: Seq<PartView>) -> Option<Seq<Seq<Row>>>  (any spec visibility; Row = crate::spec::value::Row)",
        obligation: "Abstraction function of the author's representation: which source relations (gendb_source::tables, one \
                     per distinct source table, each the declared columns of its table in delivered row order) the parts \
                     represent. Used by both entries, so builder and query are bound to one representation. It must be \
                     lossless for every relation: auxiliary data (indexes, pre-aggregates, dictionaries, zone maps) is \
                     allowed only next to data that still decodes to the relations.",
    },
    AgentItem {
        name: "build",
        signature: "pub fn build(src: &SourceRef, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)",
        obligation: "The entry provides source_wf(src@), in_domain(tables(src@)) (decided by the entry's verified \
                     gendb_source::source_in_domain before the call) and 1 <= workers <= MAX_WORKERS; any extra \
                     precondition fails the entry's verification. Its ensures must imply the fixed builder contract \
                     gendb_entry::build_meets: Ok(p) => decode(owned_parts_view(p@)) == Some(tables(src@)); \
                     Err(WorkerFailed(_)) allowed (only a real failed join produces its token); InvalidInput and \
                     Malformed never.",
    },
    AgentItem {
        name: "query",
        signature: "pub fn query(parts: &[Part], params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)",
        obligation: "The entry provides stored_asset(parts_view(parts@)), param_domain(params@) (crate::query) and \
                     1 <= workers <= MAX_WORKERS; any extra precondition fails the entry's verification. Its ensures \
                     must imply: forall|v| built_from(v, parts_view(parts@)) ==> gendb_entry::answer_meets(v, params@, r), \
                     i.e. for EVERY database db with bound_db(v, db) and oq = query_spec_at(params@): \
                     Ok(Answer::Rows(out)) => ordered_ok(db, oq, Ok(view_rows(out@))); \
                     Ok(Answer::SqlError(e)) => ordered_ok(db, oq, Err(e)) (the meaning is EXACTLY the error e: \
                     denote_body(db, oq) == Err(e)); Ok(Answer::Capacity) => !capacity_domain(db, oq); \
                     Err(WorkerFailed(_)) allowed (only a real failed join produces its token); InvalidInput/Malformed \
                     never. The author chooses every intermediate specification, lemma and bridge proof.",
    },
    PARALLELISM,
];

/// The fork/join and helper interface, the same for builders and queries of every entry.
const PARALLELISM: AgentItem = AgentItem {
    name: "parallelism",
    signature: "gendb_entry::parallel::{WorkerTask, fork_join(&mut Dispatch, Vec<T>) -> Result<Vec<T::Output>, WorkerFailure>, MAX_WORKERS}; gendb_entry::runtime::{QueryError, WorkerFailure}; gendb_entry::work::{text_bytes, text_eq, text_offsets_ok, filled, put, TaskBuffer}",
    obligation: "The only way to run work on other threads (at most MAX_WORKERS tasks per call; every thread is \
                 joined before fork_join returns; several calls per query are allowed). The author chooses the tasks \
                 (partition) and merges the outputs, and proves coverage and merge; fork_join guarantees only each \
                 task's own post on Ok. WorkerTask::run and declared_rows are no_unwind (inherited; do not restate it \
                 in the impl): a worker body cannot allocate (Vec::new/push/with_capacity), spawn or call the entry; \
                 callees must be no_unwind too. The workers argument is the maximum available, not a requirement: \
                 fewer tasks, or none (serial), is fine when faster. Preallocated output pattern: allocate each \
                 task's output on the calling thread (work::filled, or work::TaskBuffer::new for an output whose \
                 count is only bounded), move it into the task, fill it in run with work::put(&mut v, j, x) or \
                 v[j] = x (no_unwind) or TaskBuffer::push (no_unwind while len < capacity), and return it as the \
                 output; TaskBuffer::into_vec and Vec::append on the calling thread after the join. Vec::set is NOT \
                 no_unwind in the pinned vstd (refused in run). Read slices with s[i]; read text values with \
                 work::text_bytes (no_unwind).",
};

/// Named assumptions of the fixed entry v3, beyond Verus/vstd/rustc (for the TCB record).
pub const TRUSTED_ASSUMPTIONS: &[TrustedAssumption] = &[
    SQL_SEMANTICS,
    CAPACITY_DEFINITION,
    STORED_ASSET_AT_FFI,
    CANONICAL_COLUMNS,
    CANONICAL_TEXT,
    HOST_ARGUMENTS,
    THREADS,
    VERUS_TERMINATION_CHECKS,
    TRUSTED_SPECS_TERMINATE,
    FAIR_SCHEDULING,
    TRUSTED_SHIM_RETURNS,
    OS_COMPLETES_OR_KILLS,
    WORKER_FAILURE,
    CALLING_THREAD_PROGRESS,
    CHILD_LIFETIME,
    RESULT_WIRE,
];

const SQL_SEMANTICS: TrustedAssumption = TrustedAssumption {
    id: "sql_semantics",
    statement: "The SQLSpec definitions (spec/**) are the meaning of SQL, and the fixed source/answer definitions the \
                claim is stated with (link::query::{TextCol, TextView, text_wf, text_at, view_rows, proj, proj_all}, \
                link::source::{proj_columns, rows_in_columns, cols_in_table}, with the value view view_rows applies, \
                exec::value::{EVal, view_row}) are the meaning of delivered columns and answer rows; the frontend (SQLGlot + resolver + lowering, placeholder typing) and the translator \
                translate the statement and its schema into query.rs faithfully (query_spec_at, schema_spec). \
                Well-typedness at every typed binding is checked (lemma_query_wf_at), not trusted.",
    relied_on_by: "the meaning of every claim of gendb_entry",
};

const CAPACITY_DEFINITION: TrustedAssumption = TrustedAssumption {
    id: "capacity_definition",
    statement: "exec::relational::domain::fits_query (with exec::domain::fits_expr and the SUM/AVG absolute-mass \
                condition sum_mass_fits) is the definition of 'inside capacity' (gendb_entry::capacity_domain). It is \
                a checked definition, not an unchecked assumption; it is trusted as the meaning of a Capacity answer.",
    relied_on_by: "gendb_entry::outcome_ok / served (Capacity case), corollary_inside_capacity",
};

const STORED_ASSET_AT_FFI: TrustedAssumption = TrustedAssumption {
    id: "stored_asset_at_ffi",
    statement: "abi_query's precondition stored_asset(parts) is not proved: the host passes exactly the stored parts \
                of an asset that abi_build of this same build returned with status Ok for the requested source versions \
                of every source table (storage round trip, per-table source-version key, same build). Not re-checked on \
                the query path.",
    relied_on_by: "gendb_entry::abi_query; theorem_build_then_query / theorem_end_to_end take the round trip as a hypothesis",
};

const CANONICAL_COLUMNS: TrustedAssumption = TrustedAssumption {
    id: "canonical_columns",
    statement: "The columns passed to abi_build are the declared NOT NULL columns of every source table of the requested \
                source versions (gendb_source header), table by table in declaration order and each in canonical row \
                order, i.e. source_columns_are_tables(column_source(columns), db) for the database db the SQL is \
                evaluated on (the shim refuses nullable/unknown columns; the verified binder refuses count, element-type, \
                per-table row-count and text-offset mismatches; the declared SQL types are proved equal to the emitted \
                schema). For Utf8 columns the byte extent offsets[len] of the host buffer is taken from the descriptor.",
    relied_on_by: "gendb_entry::theorem_end_to_end and theorem_build_total (hypothesis bound_db)",
};

const CANONICAL_TEXT: TrustedAssumption = TrustedAssumption {
    id: "canonical_text",
    statement: "Text values of the canonical capture are the byte strings of the SQL values (valid UTF-8, canonical \
                char(n) without trailing spaces); this enters the theorem only through the hypothesis db_wf(db). The \
                verified source_in_domain checks NUL bytes, character counts and char(n) canonical form of the delivered \
                bytes of every non-NULL row; UTF-8 well-formedness is not a SQLSpec value condition.",
    relied_on_by: "gendb_entry::theorem_end_to_end (hypothesis db_wf)",
};

const HOST_ARGUMENTS: TrustedAssumption = TrustedAssumption {
    id: "host_arguments",
    statement: "The host converts the requested argument of every free parameter exactly (no rounding; inexact values \
                refused before the call) and passes them in slot order (ascending placeholder index) as ParamArg; the \
                verified bind_params decides the declared domain and the claim is stated at the decoded binding. The \
                serving record echoes the host arguments.",
    relied_on_by: "the correspondence between a user's request text and param_source(args) in theorem_end_to_end",
};

/// The query entry v4's form of [`HOST_ARGUMENTS`] (same id): arguments are `QueryArg`, including text.
const HOST_ARGUMENTS_V4: TrustedAssumption = TrustedAssumption {
    id: "host_arguments",
    statement: "The host converts the requested argument of every free parameter exactly (no rounding; inexact values \
                refused before the call) and passes them in slot order (ascending placeholder index) as QueryArg; a \
                text argument is the request string's UTF-8 bytes, which the host keeps unchanged until the calling \
                process exits (the shim reads them as a &'static slice, like stored parts). The verified bind_params \
                decides the declared domain (for text: no NUL byte) and the claim is stated at the decoded binding. The \
                serving record echoes the host arguments.",
    relied_on_by: "the correspondence between a user's request text and param_source(args) in theorem_end_to_end",
};

const THREADS: TrustedAssumption = TrustedAssumption {
    id: "threads",
    statement: "vstd spawn/join specs: the closure runs on a new std thread, join returns its value or Err if it \
                panicked, join establishes happens-before; thread-creation failure aborts the process (vstd spawn).",
    relied_on_by: "gendb_entry::parallel::fork_join",
};

/// The assumptions the proved property [`TERMINATION`] relies on (with `calling_thread_progress` and
/// `worker_failure`), beyond the toolchain items.
const VERUS_TERMINATION_CHECKS: TrustedAssumption = TrustedAssumption {
    id: "verus_termination_checks",
    statement: "The pinned Verus is sound for the termination checks it performs (a decreases measure on every exec \
                loop and recursive function, call-graph cycle checks) on the code the author-source scan admits. The \
                scan refuses the forms where the pinned release misses call-graph edges or exempts calls, its known \
                gaps (Verus PRs #3053 and #3063, issues #3138 and #3139, open): trait objects (dyn_trait_object), \
                vstd::rwlock (vstd_rwlock), the escape attributes exec_allows_no_decreases_clause and \
                assume_termination (verifier_attribute), bounds on the associated types of author traits and \
                trait-level where clauses (associated_type_bound), impl Trait types such as opaque return types \
                (impl_trait_type), and implementations of external traits other than View, WorkerTask, Clone and Copy, \
                such as Drop and PartialEq (external_trait_impl; derives only Clone, Copy, PartialEq and Eq). A gap not \
                yet found is not covered (trusted item verus).",
    relied_on_by: "the proved property termination: the decreases and cycle checks of verified code",
};

const TRUSTED_SPECS_TERMINATE: TrustedAssumption = TrustedAssumption {
    id: "trusted_specs_terminate",
    statement: "Every trusted std/vstd function that verified code calls terminates: the external_body and \
                assume_specification functions (Vec, slices, integer operations, thread spawn and join) and the \
                iterator specifications that give for loops their decreases measure. Verus checks the termination of \
                verified bodies only.",
    relied_on_by: "the proved property termination: calls from verified code into std/vstd",
};

const FAIR_SCHEDULING: TrustedAssumption = TrustedAssumption {
    id: "fair_scheduling",
    statement: "join in gendb_entry::parallel::fork_join returns once the joined worker thread finishes: every runnable \
                thread is eventually scheduled (fair OS scheduling).",
    relied_on_by: "the proved property termination: the join of every worker in fork_join",
};

const TRUSTED_SHIM_RETURNS: TrustedAssumption = TrustedAssumption {
    id: "trusted_shim_returns",
    statement: "The trusted C ABI shim (gendb_shim.rs, plain Rust that Verus never checks) and the host sinks it calls \
                return.",
    relied_on_by: "the proved property termination: the code around the verified entry",
};

const OS_COMPLETES_OR_KILLS: TrustedAssumption = TrustedAssumption {
    id: "os_completes_or_kills",
    statement: "The OS completes every page fault (of mapped parts, inputs and the library) and every write of the \
                process, or kills the process.",
    relied_on_by: "the proved property termination: memory accesses and writes",
};

const WORKER_FAILURE: TrustedAssumption = TrustedAssumption {
    id: "worker_failure",
    statement: "The fixed contracts permit WorkerFailed without a condition on the input. It is returned only with a \
                gendb_entry::runtime::WorkerFailure token, whose field is private to runtime and which only \
                runtime::join_worker creates on a failed join inside fork_join. Assumed: the thread runtime (std \
                join, under vstd's join specification) reports a failed join only when the worker panicked. Every \
                worker body is WorkerTask::run, verified and checked no_unwind by Verus, so no worker panics and \
                WorkerFailed does not occur; checked author code cannot produce it. Never a result.",
    relied_on_by: "the proved property termination (that a call returns an outcome other than WorkerFailed) and the \
                   WorkerFailed case of build_meets, storage_build_meets, derived_build_meets, outcome_ok and served",
};

const CALLING_THREAD_PROGRESS: TrustedAssumption = TrustedAssumption {
    id: "calling_thread_progress",
    statement: "Sufficient memory, stack and threads (progress, not correctness): the calling thread returns only if \
                no call there whose pinned vstd specification lacks no_unwind unwinds (Vec::new/with_capacity/push and \
                similar growth, vstd spawn inside fork_join), no allocation fails, the stack is not exhausted and thread \
                creation succeeds. Any of these aborts the process (shim catch_unwind -> abort) with no status and no \
                rows: the call then has no outcome.",
    relied_on_by: "the proved property termination: that a call ends with a status of its outcome contract rather than \
                   a process abort",
};

const CHILD_LIFETIME: TrustedAssumption = TrustedAssumption {
    id: "child_lifetime",
    statement: "The &'static slices given to verified code are valid because the child worker process keeps every \
                input, part, argument and the library mapped until the OS ends the process. No in-process serving \
                lifetime claim.",
    relied_on_by: "gendb_shim (v3)",
};

const RESULT_WIRE: TrustedAssumption = TrustedAssumption {
    id: "result_wire",
    statement: "The v3 shim encodes the verified result with the SQLSpec GSQLRS1 wire (status 0 rows, 1 SQL error + \
                code byte, 2 capacity; the code is also in the call record) and the host decodes it with \
                gendb_sqlspec::codec::decode_result; value and error-code encodings mirror the reference evaluator \
                shim sqlspec/interpreter/host/shim.rs byte for byte.",
    relied_on_by: "the rows and the SQL error code the host reports",
};

// ------------------------------------------------------------------------------------ storage entry and query entry v4

/// Paths of the final theorems of a storage crate.
/// (The lossless theorem `gendb_entry::storage::theorem_storage_lossless` lives in the generated binding module, whose
/// exact text the publication's framework-file comparison fixes; it is not an entry item.)
pub const STORAGE_THEOREMS: &[&str] = &["gendb_entry::theorem_storage_built", "gendb_entry::theorem_storage_build_total"];

/// Paths of the final theorems of a query crate of the entry v4 (the same in entry v5).
pub const QUERY_THEOREMS: &[&str] = &["gendb_entry::theorem_end_to_end", "gendb_entry::corollary_inside_capacity"];

/// What a storage author provides: the interface `crate::stores::<name>::interface` (copied into every query crate
/// that reads the storage) and the builder `crate::builder` (storage crate only), under the storage entry v1.
pub const STORAGE_AUTHOR_OBLIGATIONS: &[AgentItem] = &[REPRESENTS, LOSSLESS, READERS, BUILD, PARALLELISM];

/// What a storage author provides under the storage entry v2 (the manifest opts in with `uses_declared_constraints`):
/// the same items, the builder with the one more precondition `source_witnessed` it may require.
pub const STORAGE_V2_AUTHOR_OBLIGATIONS: &[AgentItem] = &[REPRESENTS, LOSSLESS, READERS, BUILD_V2, PARALLELISM];

/// The storage's representation relation.
const REPRESENTS: AgentItem = AgentItem {
    name: "represents",
    signature: "pub open spec fn represents(parts: Seq<PartView>, rels: Seq<Seq<Row>>) -> bool  (in stores/<name>/interface/mod.rs; \
                Row = crate::spec::value::Row)",
    obligation: "The author's representation relation: which logical relations (rels[j] = the stored columns of stored \
                 table t{j}, in canonical row order: declaration::stored_relations) the stored parts represent. Any \
                 definition: physical order, encodings, blocks, dictionaries, zone maps, indexes and pre-aggregates are \
                 the author's choice, related to rels by the author's own specifications. The builder must prove it on \
                 every in-domain source (so it must be satisfiable by real data); query authors can use only what it \
                 states. It may use the SQLSpec library, schema, gendb_abi, gendb_entry::{layout, stored, parallel, \
                 runtime, work, source_check} and stores::<name>::declaration, never builder/agent/query items.",
};

/// Complete lossless storage: the representation determines the relations.
const LOSSLESS: AgentItem = AgentItem {
    name: "lossless",
    signature: "pub proof fn lemma_represents_determines(parts: Seq<PartView>, a: Seq<Seq<Row>>, b: Seq<Seq<Row>>) \
                requires represents(parts, a), represents(parts, b) ensures a == b  (in stores/<name>/interface/**, reachable as \
                crate::stores::<name>::interface::lemma_represents_determines)",
    obligation: "The parts determine the relations they represent: every stored column of every stored table can be recovered \
                 from the parts alone, so the storage is lossless and the source data may be deleted. The fixed \
                 gendb_entry::storage::theorem_storage_lossless calls this lemma; it may require less, never more. A \
                 representation that pins each stored value of each row (row for row, or through a lossless encoding) \
                 proves it by extensional equality (=~=) of the relations; one that leaves a stored column open cannot.",
};

/// The storage's optional readers.
const READERS: AgentItem = AgentItem {
    name: "readers",
    signature: "any pub fn in stores/<name>/interface/** taking st: &mut StoredParts (optional)",
    obligation: "Optional readers and lemmas over StoredParts extents, specified over rels under represents(st@, rels): \
                 exact lookups sound and complete, candidate lookups complete (a residual filter removes extras), skipped \
                 blocks without a needed row. Verified in the storage crate and again, with the same text, in every query \
                 crate that calls them; their code is compiled into the served query library.",
};

/// The builder under the storage entry v1.
const BUILD: AgentItem = AgentItem {
    name: "build",
    signature: "pub fn build(src: &SourceRef, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)  \
                (in builder/mod.rs)",
    obligation: "The entry provides source_wf(src@), in_domain(tables(src@)) (decided by the entry's verified \
                 gendb_source::source_in_domain before the call) and 1 <= workers <= MAX_WORKERS; any extra precondition \
                 fails the entry's verification. Its ensures must imply the fixed contract storage_build_meets: \
                 Ok(p) => represents(owned_parts_view(p@), tables(src@)); Err(WorkerFailed(_)) allowed (only a real \
                 failed join produces its token); InvalidInput and Malformed never. The builder takes no statement \
                 argument: one asset serves every statement and binding that reads the storage.",
};

/// The builder under the storage entry v2: the v1 item and the precondition `source_witnessed`.
const BUILD_V2: AgentItem = AgentItem {
    name: "build",
    signature: "pub fn build(src: &SourceRef, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)  \
                (in builder/mod.rs)",
    obligation: "The entry provides source_wf(src@), in_domain(tables(src@)) (decided by the entry's verified \
                 gendb_source::source_in_domain before the call), 1 <= workers <= MAX_WORKERS and, in the storage entry \
                 v2, source_witnessed(delivered_source(..)): some full database of the schema in db_wf that satisfies the \
                 declared integrity constraints (constraints_hold(declared_db(db))) delivers the source. The builder may \
                 require source_witnessed(src@); any other extra precondition fails the entry's verification. The \
                 constraints reach the delivered columns only through that full witness (choose it; transfer facts by row \
                 position and delivered column), never as a property of the projection. Its ensures must imply the fixed \
                 contract storage_build_meets: \
                 Ok(p) => represents(owned_parts_view(p@), tables(src@)); Err(WorkerFailed(_)) allowed (only a real \
                 failed join produces its token); InvalidInput and Malformed never. The builder takes no statement \
                 argument: one asset serves every statement and binding that reads the storage.",
};

/// What a storage author provides under the derived storage entry (a manifest with `built_from`: the storage is built
/// from admitted storages): the interface as always, and the builder over the sources' stored parts.
pub const STORAGE_DERIVED_AUTHOR_OBLIGATIONS: &[AgentItem] = &[REPRESENTS, LOSSLESS, READERS, BUILD_DERIVED, STORED_READS, PARALLELISM];

/// The builder under the derived storage entry.
const BUILD_DERIVED: AgentItem = AgentItem {
    name: "build",
    signature: "pub fn build(stores: &mut Stores, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)  \
                (in builder/mod.rs; Stores = gendb_entry::sources::Stores, one StoredParts field per source)",
    obligation: "The entry provides sources_ready(old(stores)@) (some database is bound to the source parts) and \
                 1 <= workers <= MAX_WORKERS; any extra precondition fails the entry's verification. Its ensures must imply \
                 the fixed contract derived_build_meets(old(stores)@, workers, ..): Ok(p) => for EVERY database db with \
                 sources_bound(old(stores)@, db) (the schema's, db_wf, gendb_entry::derivation::assumed(db), and every source's \
                 parts represent its stored_relations(db)), represents(storage_parts(old(stores)@, owned_parts_view(p@)), \
                 stored_relations(db)), where storage_parts puts the parts inherited unchanged from the extended source \
                 (derivation::inherited; none without `extends`) before p; Err(WorkerFailed(_)) allowed; InvalidInput and \
                 Malformed never. Read the sources only through their interfaces' readers and StoredParts extents; the \
                 proof chains each source's represents (old) and the copy into the new parts (new). No source column is \
                 delivered: a derived storage never reads the original input.",
};

/// What a query author of the entry v4 provides in `crate::agent`.
pub const QUERY_AUTHOR_OBLIGATIONS: &[AgentItem] = &[QUERY, STORED_READS, PARALLELISM];

/// What a query author of the entry v5 provides in `crate::agent`: the same items, `bound_db` with the declared
/// integrity constraints.
pub const QUERY_V5_AUTHOR_OBLIGATIONS: &[AgentItem] = &[QUERY_V5, STORED_READS, PARALLELISM];

/// The query under the entry v4.
const QUERY: AgentItem = AgentItem {
    name: "query",
    signature: "pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)",
    obligation: "The entry provides stores_ready(old(stores)@) (some database is bound to the stored parts), \
                 param_domain(params@) (crate::query) and 1 <= workers <= MAX_WORKERS; any extra precondition fails the \
                 entry's verification. Its ensures must imply gendb_entry::answer_meets(old(stores)@, params@, r): for \
                 EVERY database db with bound_db(old(stores)@, db) (the schema's, db_wf, and every use's parts represent \
                 stored_relations(db)) and oq = query_spec_at(params@): Ok(Answer::Rows(out)) => ordered_ok(db, oq, \
                 Ok(view_rows(out@))); Ok(Answer::Columns(c)) (columnar, gendb_entry::results, no allocation per row) => columns_wf(c) \
                 && ordered_ok(db, oq, Ok(columns_view(c))); Ok(Answer::SqlError(e)) => the meaning is EXACTLY the error e; Ok(Answer::Capacity) \
                 => !capacity_domain(db, oq); Err(WorkerFailed(_)) allowed; InvalidInput/Malformed never. The author \
                 chooses every intermediate specification, lemma and bridge proof.",
};

/// The query under the entry v5: `bound_db` also states the declared constraints.
const QUERY_V5: AgentItem = AgentItem {
    name: "query",
    signature: "pub fn query(stores: &mut Stores, params: &Params, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)",
    obligation: "The entry provides stores_ready(old(stores)@) (some database is bound to the stored parts), \
                 param_domain(params@) (crate::query) and 1 <= workers <= MAX_WORKERS; any extra precondition fails the \
                 entry's verification. Its ensures must imply gendb_entry::answer_meets(old(stores)@, params@, r): for \
                 EVERY database db with bound_db(old(stores)@, db) (the schema's, db_wf, the declared integrity constraints \
                 constraints_hold(declared_db(db)) and every use's parts represent stored_relations(db)) and oq = \
                 query_spec_at(params@): Ok(Answer::Rows(out)) => ordered_ok(db, oq, Ok(view_rows(out@))); Ok(Answer::Columns(c)) (columnar, gendb_entry::results, no allocation per row) => columns_wf(c) \
                 && ordered_ok(db, oq, Ok(columns_view(c))); Ok(Answer::SqlError(e)) => the meaning is EXACTLY the error e; Ok(Answer::Capacity) \
                 => !capacity_domain(db, oq); Err(WorkerFailed(_)) allowed; InvalidInput/Malformed never. The author \
                 chooses every intermediate specification, lemma and bridge proof.",
};

/// How stored data is read.
const STORED_READS: AgentItem = AgentItem {
    name: "stored_reads",
    signature: "gendb_entry::stores::Stores (one pub StoredParts field per storage use); gendb_entry::stored::StoredParts::{part_count, \
                part_len, extent_i8 .. extent_u64}; the storages' interface readers",
    obligation: "Stored data is read only through StoredParts extents (directly or through interface readers): each call \
                 returns the elements [lo, hi) of one part and is counted (requests, not device I/O). Extents need &mut \
                 StoredParts, so request them on the calling thread and move the returned &'static slices into worker \
                 tasks. Metadata parts can be read first to choose the data extents; nothing requires reading whole parts.",
};

/// Named assumptions of the storage entry, beyond Verus/vstd/rustc.
pub const STORAGE_TRUSTED_ASSUMPTIONS: &[TrustedAssumption] = &[
    SQL_SEMANTICS_STORED,
    STORAGE_SOURCE_COLUMNS,
    CANONICAL_TEXT,
    THREADS,
    VERUS_TERMINATION_CHECKS,
    TRUSTED_SPECS_TERMINATE,
    FAIR_SCHEDULING,
    TRUSTED_SHIM_RETURNS,
    OS_COMPLETES_OR_KILLS,
    WORKER_FAILURE,
    CALLING_THREAD_PROGRESS,
    CHILD_LIFETIME,
];

/// Named assumptions of the storage entry v2: those of the storage entry v1 and the declared integrity constraints.
pub const STORAGE_V2_TRUSTED_ASSUMPTIONS: &[TrustedAssumption] = &[
    SQL_SEMANTICS_STORED,
    STORAGE_SOURCE_COLUMNS,
    CANONICAL_TEXT,
    THREADS,
    VERUS_TERMINATION_CHECKS,
    TRUSTED_SPECS_TERMINATE,
    FAIR_SCHEDULING,
    TRUSTED_SHIM_RETURNS,
    OS_COMPLETES_OR_KILLS,
    WORKER_FAILURE,
    CALLING_THREAD_PROGRESS,
    CHILD_LIFETIME,
    DECLARED_INTEGRITY_CONSTRAINTS_STORAGE,
];

/// Named assumptions of the derived storage entry: the storage entry's, with the sources' parts delivered as the
/// query entries deliver stored parts (their admitted builds' parts for the same capture, unchanged; the sources'
/// closures shared byte for byte), the inherited parts written as the source's own files, and, under the opt-in, the
/// declared integrity constraints. No source column is delivered.
pub const STORAGE_DERIVED_TRUSTED_ASSUMPTIONS: &[TrustedAssumption] = &[
    SQL_SEMANTICS_STORED,
    STORED_PARTS_ROUND_TRIP,
    STORAGE_SPEC_IDENTITY,
    SAME_CAPTURE,
    CANONICAL_TEXT,
    THREADS,
    VERUS_TERMINATION_CHECKS,
    TRUSTED_SPECS_TERMINATE,
    FAIR_SCHEDULING,
    TRUSTED_SHIM_RETURNS,
    OS_COMPLETES_OR_KILLS,
    WORKER_FAILURE,
    CALLING_THREAD_PROGRESS,
    CHILD_LIFETIME,
];

/// Named assumptions of the derived storage entry when its builder assumes the declared integrity constraints.
pub const STORAGE_DERIVED_V2_TRUSTED_ASSUMPTIONS: &[TrustedAssumption] = &[
    SQL_SEMANTICS_STORED,
    STORED_PARTS_ROUND_TRIP,
    STORAGE_SPEC_IDENTITY,
    SAME_CAPTURE,
    CANONICAL_TEXT,
    THREADS,
    VERUS_TERMINATION_CHECKS,
    TRUSTED_SPECS_TERMINATE,
    FAIR_SCHEDULING,
    TRUSTED_SHIM_RETURNS,
    OS_COMPLETES_OR_KILLS,
    WORKER_FAILURE,
    CALLING_THREAD_PROGRESS,
    CHILD_LIFETIME,
    DECLARED_INTEGRITY_CONSTRAINTS_STORAGE,
];

/// Named assumptions of the query entry v4, beyond Verus/vstd/rustc.
pub const QUERY_TRUSTED_ASSUMPTIONS: &[TrustedAssumption] = &[
    SQL_SEMANTICS_STORED,
    CAPACITY_DEFINITION,
    STORED_PARTS_ROUND_TRIP,
    STORAGE_SPEC_IDENTITY,
    SAME_CAPTURE,
    CANONICAL_TEXT,
    HOST_ARGUMENTS_V4,
    THREADS,
    VERUS_TERMINATION_CHECKS,
    TRUSTED_SPECS_TERMINATE,
    FAIR_SCHEDULING,
    TRUSTED_SHIM_RETURNS,
    OS_COMPLETES_OR_KILLS,
    WORKER_FAILURE,
    CALLING_THREAD_PROGRESS,
    CHILD_LIFETIME,
    RESULT_WIRE,
];

/// Named assumptions of the query entry v5: those of the entry v4 and the declared integrity constraints.
pub const QUERY_V5_TRUSTED_ASSUMPTIONS: &[TrustedAssumption] = &[
    SQL_SEMANTICS_STORED,
    CAPACITY_DEFINITION,
    STORED_PARTS_ROUND_TRIP,
    STORAGE_SPEC_IDENTITY,
    SAME_CAPTURE,
    CANONICAL_TEXT,
    HOST_ARGUMENTS_V4,
    THREADS,
    VERUS_TERMINATION_CHECKS,
    TRUSTED_SPECS_TERMINATE,
    FAIR_SCHEDULING,
    TRUSTED_SHIM_RETURNS,
    OS_COMPLETES_OR_KILLS,
    WORKER_FAILURE,
    CALLING_THREAD_PROGRESS,
    CHILD_LIFETIME,
    RESULT_WIRE,
    DECLARED_INTEGRITY_CONSTRAINTS_QUERY,
];

/// The request's declared integrity constraints, as the query entry v5 relies on them.
const DECLARED_INTEGRITY_CONSTRAINTS_QUERY: TrustedAssumption = TrustedAssumption {
    id: "declared_integrity_constraints",
    statement: "The actual database (the declared dataset's tables at the recorded source versions, every row and every \
                declared column) satisfies the request's declared constraints in SQLSpec's meaning, \
                constraints_hold(declared_db(db)): PRIMARY KEY / UNIQUE / FOREIGN KEY, and CHECK in the raise-free, \
                collation-independent subset. This is a user declaration (trust user_declared). GenDB checks the \
                declarations' form only (the frontend binder's PostgreSQL DDL rules, one constraint per declaration, the \
                CHECK subset, constraints_wf(declared_schema()) proved by Verus), and the frontend and translator are \
                trusted to translate each declaration into its SQLSpec Constraint in gendb_constraints.rs (as under \
                sql_semantics). Nothing reads the data to check that the declarations hold, and PostgreSQL never \
                validated them. If they do not hold, the claim says nothing about that data.",
    relied_on_by: "gendb_entry::bound_db / stores_ready (query entry v5): the host's link at abi_query asserts that the \
                   actual database is bound, including this conjunct; theorem_end_to_end takes bound_db as a hypothesis",
};

/// The request's declared integrity constraints, as the storage entry v2 relies on them (same id and statement as the
/// query entry v5's).
const DECLARED_INTEGRITY_CONSTRAINTS_STORAGE: TrustedAssumption = TrustedAssumption {
    id: "declared_integrity_constraints",
    statement: DECLARED_INTEGRITY_CONSTRAINTS_QUERY.statement,
    relied_on_by: "gendb_entry::abi_build_storage's precondition source_witnessed (storage entry v2): the host's link at the \
                   build asserts that the actual database, which the delivered columns come from, is a witness, including \
                   this conjunct; theorem_storage_built and theorem_storage_build_total take constraints_hold(declared_db(db)) \
                   as a premise",
};

const SQL_SEMANTICS_STORED: TrustedAssumption = TrustedAssumption {
    id: "sql_semantics",
    statement: "The SQLSpec definitions (spec/**) are the meaning of SQL, and the fixed source/answer definitions the \
                claims are stated with (link::query::{TextCol, TextView, text_wf, text_at, view_rows, proj, proj_all}, \
                link::source::{proj_columns, rows_in_columns, cols_in_table}, with the value view view_rows applies, \
                exec::value::{EVal, view_row}) are the meaning of delivered columns, stored relations and answer rows; the \
                frontend (SQLGlot + resolver + lowering, placeholder typing) and the translator translate the dataset DDL \
                into schema.rs (schema_spec) and the statement into query.rs (query_spec_at) faithfully. Well-typedness at \
                every typed binding is checked (lemma_query_wf_at) and every storage declaration is checked against the \
                schema (lemma_declared_schema), not trusted.",
    relied_on_by: "the meaning of every claim of the storage entry and the query entry v4",
};

const STORAGE_SOURCE_COLUMNS: TrustedAssumption = TrustedAssumption {
    id: "storage_source_columns",
    statement: "The columns passed to abi_build_storage are the declared columns of every table of the storage \
                declaration from the persisted canonical capture of the recorded source version (the Parquet importer \
                is trusted, not verified), table by table in declaration order and each in canonical row order, i.e. \
                source_columns_are_tables(column_source(columns), db) for the database db the SQL is evaluated on (the \
                shim storage_build.rs refuses nullable and unknown columns; the verified binder refuses count, \
                element-type, per-table row-count and text-offset mismatches; the declared SQL types are proved equal to \
                the schema). For Utf8 columns the byte extent offsets[len] of the host buffer is taken from the \
                descriptor. A declaration with a nullable column is built with the shim storage_build_nullable.rs \
                instead: it delivers each nullable column's values, then its validity (the capture's validity buffer, \
                one byte per row, 0 exactly for a NULL row of the source table) as a Utf8 column with no offsets; the \
                verified binder decides that shape and its row count, and a NULL row's value bytes are not read by the \
                meaning (or_null).",
    relied_on_by: "gendb_entry::theorem_storage_built and theorem_storage_build_total (hypothesis source_columns_are_tables)",
};

const STORED_PARTS_ROUND_TRIP: TrustedAssumption = TrustedAssumption {
    id: "stored_parts_round_trip",
    statement: "abi_query's precondition stores_ready is not proved on the query path: for every storage use the host \
                passes exactly the parts that abi_build_storage of that storage's admitted build returned with status Ok \
                for the capture named in the asset key, written once, never modified while mapped and reinterpreted with \
                the same element width and endianness. Then each storage's theorem_storage_built gives \
                represents(parts, stored_relations(db)) for the actual database, i.e. bound_db, which discharges \
                stores_ready. Not re-checked on the query path.",
    relied_on_by: "gendb_entry::abi_query (query entry v4); theorem_end_to_end takes bound_db as a hypothesis",
};

const STORAGE_SPEC_IDENTITY: TrustedAssumption = TrustedAssumption {
    id: "storage_spec_identity",
    statement: "A storage's represents and stored_relations denote the same propositions in its storage build and in the \
                query build. Admission checks mechanically that the query build carries the storage build's dependency \
                closure (the registry's shared files: SQLSpec library, schema.rs, gendb_abi.rs, the fixed entry \
                submodules with stored.rs, stores/<name>/{mod.rs, declaration.rs, interface/**}) byte for byte at the same \
                paths, that every author file of both builds passes the author-source rules (implementation ownership: \
                impl blocks only for the file's own types or traits; only the audited seq!/set!/map!/vec! macros and \
                standard derives, never rebound; no cfg), and that both builds used the same Verus/vstd/Z3 toolchain. \
                Identical text alone does not fix meaning in Rust; trusted are that lexical scan and comparison code, and \
                that rustc/Verus resolve names, methods and implementations as the toolchain documents (under those rules \
                code outside the closure cannot change resolution inside it).",
    relied_on_by: "the composition of theorem_storage_built (storage crate) with theorem_end_to_end (query crate)",
};

const SAME_CAPTURE: TrustedAssumption = TrustedAssumption {
    id: "same_capture",
    statement: "All storage assets used by one execution that store the same table were built from the same persisted \
                capture of its source version, so their stored relations are projections of one database (enforced by \
                asset resolution, trusted host code).",
    relied_on_by: "bound_db for queries that read several storages of one table",
};

// -------------------------------------------------------------------------------------------- engine entry v1
//
// The engine claim definition (fixed engine entry `gendb-verus-engine-entry-v1`, `verification/obligations/
// engine_entry.rs`): one verified engine for a schema, answering any supported statement given as AST bytes.

/// Paths of the final theorems of an engine crate.
pub const ENGINE_THEOREMS: &[&str] = &["gendb_entry::theorem_engine_end_to_end", "gendb_entry::corollary_inside_capacity"];

/// What is proved, for which inputs, with which outcomes: the engine claim in words (the entry is the check).
pub const ENGINE_CLAIM_TEXT: &str = "For the statement the AST bytes mean (decode_spec(ast), the codec's fixed definition) and EVERY \
     database db with bound_db(stores, db) (the schema's, db_wf, the request's declared integrity constraints \
     constraints_hold(declared_db(db)), and every storage use's parts represent stored_relations(db)), a call at a worker \
     count in 1..=MAX_WORKERS returns: Malformed exactly when the bytes decode to no statement; ParamRefused exactly when \
     the decoded statement oq is not supported (supported(oq) = wf_ordered(schema_spec(), oq), decided by the verified \
     checker check_ordered before any author code); otherwise Ok with rows allowed by ordered_ok(db, oq, ..) (ORDER BY \
     ties and the LIMIT boundary in any allowed way; a columnar answer also columns_wf), SqlError(e) only when \
     denote_body(db, oq) == Err(e), Capacity only when !capacity_domain(db, oq), or WorkerFailed (excluded by the trusted \
     assumption worker_failure). A worker count outside the bound is Refused. Inside capacity_domain and without a \
     worker failure the status is decided (corollary_inside_capacity). The supported set is fixed by GenDB and covers \
     every constructor of the SQLSpec fragment; the engine author cannot narrow it. Statement parameters are not part \
     of the claim: the host substitutes a binding's typed literals before encoding (host_ast_encoding). Termination: \
     the proved property termination (PROVED_PROPERTIES), relying on the assumptions it lists.";

/// The domains the engine claim quantifies over.
pub const ENGINE_DOMAINS: &str = "Statements: every OrderedQuery with wf_ordered(schema_spec(), oq) over the column schema \
     (schema.rs); literals are machine values by construction of the byte format (i64 integers, i128 numeric coefficients \
     with u32 scales, i32 date fields, u32 column/table/ORDER BY positions, u64 LIMIT/OFFSET). Databases: db.schema == \
     schema_spec(), db_wf(db), constraints_hold(declared_db(db)) and stored_ok for every storage use. Worker counts: \
     1..=MAX_WORKERS (64). Capacity: one-sided, outside capacity_domain(db, oq) = fits_query(db, [], oq.body).";

/// What an engine author provides in `crate::agent`.
pub const ENGINE_AUTHOR_OBLIGATIONS: &[AgentItem] = &[ENGINE, STORED_READS, PARALLELISM];

/// The engine function.
const ENGINE: AgentItem = AgentItem {
    name: "engine",
    signature: "pub fn engine(stores: &mut Stores, q: &EOrderedQuery, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Answer, QueryError>)  \
                (in agent/mod.rs; EOrderedQuery = crate::exec::ast::EOrderedQuery)",
    obligation: "The entry provides stores_ready(old(stores)@) (some database is bound to the stored parts), \
                 supported(view_ordered(*q)) (= wf_ordered(schema_spec(), view_ordered(*q)), decided by the verified \
                 check_ordered) and 1 <= workers <= MAX_WORKERS; any extra precondition fails the entry's verification. Its \
                 ensures must imply gendb_entry::answer_meets(old(stores)@, view_ordered(*q), r): for EVERY database db with \
                 bound_db(old(stores)@, db) (the schema's, db_wf, the declared integrity constraints and every use's parts \
                 represent stored_relations(db)) and oq = view_ordered(*q): Ok(Answer::Rows(out)) => ordered_ok(db, oq, \
                 Ok(view_rows(out@))); Ok(Answer::Columns(c)) => columns_wf(c) && ordered_ok(db, oq, Ok(columns_view(c))); \
                 Ok(Answer::SqlError(e)) => the meaning is EXACTLY the error e; Ok(Answer::Capacity) => !capacity_domain(db, \
                 oq); Err(WorkerFailed(_)) allowed; InvalidInput/Malformed never. The statement arrives at call time: the \
                 engine answers every supported statement over the schema, not a fixed list. The author chooses every \
                 intermediate specification, plan, lemma and proof.",
};

/// Named assumptions of the engine entry, beyond Verus/vstd/rustc: the query entry v5's items with the statement's
/// route replaced (no translator-emitted statement module, no statement arguments: `host_ast_encoding`,
/// `ast_decode_definition` and `engine_echo` instead of `host_arguments`).
pub const ENGINE_TRUSTED_ASSUMPTIONS: &[TrustedAssumption] = &[
    SQL_SEMANTICS_ENGINE,
    CAPACITY_DEFINITION,
    STORED_PARTS_ROUND_TRIP,
    STORAGE_SPEC_IDENTITY,
    SAME_CAPTURE,
    CANONICAL_TEXT,
    HOST_AST_ENCODING,
    AST_DECODE_DEFINITION,
    ENGINE_ECHO,
    THREADS,
    VERUS_TERMINATION_CHECKS,
    TRUSTED_SPECS_TERMINATE,
    FAIR_SCHEDULING,
    TRUSTED_SHIM_RETURNS,
    OS_COMPLETES_OR_KILLS,
    WORKER_FAILURE,
    CALLING_THREAD_PROGRESS,
    CHILD_LIFETIME,
    RESULT_WIRE,
    DECLARED_INTEGRITY_CONSTRAINTS_QUERY,
];

/// The engine entry's form of `sql_semantics` (same id): the statement reaches the claim as a translated AST document,
/// not as an emitted `query.rs`.
const SQL_SEMANTICS_ENGINE: TrustedAssumption = TrustedAssumption {
    id: "sql_semantics",
    statement: "The SQLSpec definitions (spec/**) are the meaning of SQL, and the fixed source/answer definitions the claim \
                is stated with (link::query::{TextCol, TextView, text_wf, text_at, view_rows, proj, proj_all}, \
                link::source::{proj_columns, rows_in_columns, cols_in_table}, with the value view view_rows applies, \
                exec::value::{EVal, view_row}) are the meaning of stored relations and answer rows; the frontend (SQLGlot + \
                resolver + lowering, placeholder typing) translates the SQL statement into the typed AST document \
                gendb-sql-ast-v1 faithfully, and the translator translates the dataset DDL into schema.rs (schema_spec) \
                faithfully. No statement module is emitted for an engine call: the statement reaches the claim through the \
                host encoding (host_ast_encoding) and the fixed decode_spec (ast_decode_definition). Well-typedness is \
                checked at every call (check_ordered decides supported), not trusted; storage declarations are checked \
                against the schema (lemma_declared_schema).",
    relied_on_by: "the meaning of every claim of the engine entry",
};

/// New with the engine entry: the host's binding substitution and AST encoding.
const HOST_AST_ENCODING: TrustedAssumption = TrustedAssumption {
    id: "host_ast_encoding",
    statement: "The host substitutes the requested binding into the translated AST document as typed literals AFTER the \
                frontend's constant-expression check (gendb_frontend::params::instantiate with every parameter fixed; \
                a parameter expression keeps SQLSpec's row-by-row meaning), and encodes the substituted document as the \
                AST bytes of the call (gendb_frontend::engine_encode, format gendb-engine-ast-v1), so that \
                decode_spec(bytes) is the substituted document's statement. Plain host code, not verified; checked per \
                statement by the echo (engine_echo). The host keeps the bytes unchanged until the calling process exits \
                (the shim reads them as a &'static slice, like stored parts). Serving records the bytes' digest.",
    relied_on_by: "the correspondence between a user's SQL text and binding and decode_spec(ast) in theorem_engine_end_to_end",
};

/// New with the engine entry: the fixed meaning of the AST bytes.
const AST_DECODE_DEFINITION: TrustedAssumption = TrustedAssumption {
    id: "ast_decode_definition",
    statement: "gendb_ast_codec::decode_spec (runtime/verus/engine_codec.rs) is the meaning of AST bytes: a total, \
                deterministic prefix decoding of the gendb-sql-ast-v1 constructors (SQLSpec spec::ast) in the byte format \
                documented in that file, None for every byte string that is not exactly one encoded OrderedQuery. A fixed \
                definition like the spec definitions, trusted as the format's meaning; the executable decode_query is \
                verified against it (decode_spec(ast) == Some(view_ordered(q)) exactly when it returns Some(q)).",
    relied_on_by: "engine_meets and theorem_engine_end_to_end (the statement oq = decode_spec(ast))",
};

/// New with the engine entry: the echo comparison of the encoded statement.
const ENGINE_ECHO: TrustedAssumption = TrustedAssumption {
    id: "engine_echo",
    statement: "abi_engine_echo(ast) returns render_spec(decode_spec(ast)) (verified): the canonical s-expression of the \
                evaluator's echo grammar. The host compares it byte for byte with its own rendering of the substituted AST \
                document (gendb_sqlspec::evaluator::echo_text) before relying on the call. Trusted: that grammar, the host \
                renderer and the comparison code; equal texts then mean decode_spec(ast) is the document's statement, \
                because the echo grammar renders every constructor and field of the AST. The echo is translation \
                validation of host_ast_encoding per statement, not a proof about the encoder.",
    relied_on_by: "the check of host_ast_encoding for each served statement",
};

/// The engine claim as one record: entry identity, what is proved and for which domains, the author's obligations, the
/// trusted assumptions and the proved properties.
#[derive(Clone, Copy, Debug, Serialize)]
pub struct EngineClaim {
    pub entry_identity: &'static str,
    pub theorems: &'static [&'static str],
    pub claim: &'static str,
    pub domains: &'static str,
    pub author_obligations: &'static [AgentItem],
    pub trusted_assumptions: &'static [TrustedAssumption],
    pub proved_properties: &'static [ProvedProperty],
}

/// The engine claim of the fixed engine entry v1.
pub const ENGINE_CLAIM_V1: EngineClaim = EngineClaim {
    entry_identity: gendb_artifacts::verus::VERUS_ENGINE_ENTRY_V1_IDENTITY,
    theorems: ENGINE_THEOREMS,
    claim: ENGINE_CLAIM_TEXT,
    domains: ENGINE_DOMAINS,
    author_obligations: ENGINE_AUTHOR_OBLIGATIONS,
    trusted_assumptions: ENGINE_TRUSTED_ASSUMPTIONS,
    proved_properties: PROVED_PROPERTIES,
};
