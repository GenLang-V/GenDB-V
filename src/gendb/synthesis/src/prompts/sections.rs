//! The sections of both author prompts, as Markdown text. `policy` assembles them with the call's facts, handoff,
//! ledger and feedback; nothing here is specific to a query or a dataset.
//!
//! Each role's prompt keeps "what a submission must be" (Goal, Evaluation) apart from "how to work" (How to work),
//! states the scope rules first (Key paths), and names files by their Key paths (`files.<name>`) and data by the
//! headings of CURRENT FACTS (`data_sections`), so a reader can check every statement against the contract files.
//!
//! The query role's Goal, Evaluation and How to work have one text per objective: the execution-time objective
//! (targets, selection, early stop, measure first) and the correctness objective (the simplest correct implementation;
//! the first exact verified submission ends the run; times select nothing). Its other sections are shared, and their
//! few objective-dependent phrases are placeholders (`QUERY_OBJECTIVE_PHRASES`).

use crate::controller::author::CANDIDATE_MANIFEST_RULE;

/// Placeholders of the early-stop factor (`objective.early_stop.min_speedup`, e.g. `5x` and `1/5`), replaced by `policy`.
pub const BAR: &str = "@BAR@";
pub const BAR_FRACTION: &str = "@BAR_FRACTION@";

/// Placeholder in the section texts for the role's contract directory name, replaced by `policy`.
pub const CONTRACT: &str = "@CONTRACT@";

/// Placeholders of the objective-dependent phrases in the query role's shared sections, replaced by `policy`.
pub const FIRST_STORAGE_STEP: &str = "@FIRST_STORAGE_STEP@";
pub const PERFORMANCE_FILE_INPUT: &str = "@PERFORMANCE_FILE_INPUT@";
pub const TRIAL_CELL_FIELDS: &str = "@TRIAL_CELL_FIELDS@";

/// Each objective-dependent phrase of the query role's shared sections: (placeholder, execution-time text, correctness
/// text). The correctness objective asks for no measuring, writes no `performance.json` and has no targets, so a
/// trial's target, bar and met fields are empty.
pub const QUERY_OBJECTIVE_PHRASES: [(&str, &str, &str); 3] = [
    (FIRST_STORAGE_STEP, "**First measure your query on the shared storage**", "**Start from the shared storage**"),
    (
        PERFORMANCE_FILE_INPUT,
        "\n- **`performance.json`** holds the measurement protocol, the execution environment and host, profiling, compiler controls, and the stored-data facts (CURRENT FACTS, Host and measurement repeats the key facts).",
        "",
    ),
    (TRIAL_CELL_FIELDS, "target, @BAR@ bar, median, min and max, met", "median, min and max"),
];

/// The scope rules every author reads first (prompt-only scope, no sandbox).
pub const SCOPE_RULES: &str = "\
- **Write only inside your workspace** (`files.workspace`). Scratch goes in `verus-tmp/` there; never `/tmp` or your home directory.
- **No filesystem-wide search.** Do not run `find /`, `grep -r /` or similar over the host. Every path you need is named here, in `files.author_contract`, or in the files it maps.
- **Signal only your own process groups** (appendix). Never kill by name, pattern or user.";

/// The goal shared by both roles' wording: the target, the 5x aim, and to keep improving.
pub const GOAL_TARGET: &str = "\
Write a **verified** implementation that is **significantly faster than the state-of-the-art engines**: the runtime targets in CURRENT FACTS (Targets and official results) are the fastest of DuckDB and Umbra for each binding and worker count. Aim for **at least @BAR@ faster than the target in every cell**; while any cell is below that bar, keep improving until your submissions run out.";

/// The goal sentence when every runtime target names one reference system (`RuntimeTarget::system`, `@SYSTEM@`), for
/// example a stress test against another synthesized engine: the same aim and bar, with that system's times as targets.
pub const GOAL_TARGET_SYSTEM: &str = "\
Write a **verified** implementation that is **faster than @SYSTEM@ in every cell**: the runtime targets in CURRENT FACTS (Targets and official results) are @SYSTEM@'s measured times for each binding and worker count, with their provenance and timing scope stated there. Aim for **at least @BAR@ faster than the target in every cell**; while any cell is below that bar, keep improving until your submissions run out.";

/// The workload role's goal sentence: the storage that makes the whole workload fast.
pub const WORKLOAD_GOAL_TARGET: &str = "\
Design **verified** storage that lets the **whole workload** run **significantly faster than the state-of-the-art engines**: the runtime targets in CURRENT FACTS (Statements) are the fastest of DuckDB and Umbra for each statement, binding and worker count. Query authors aim for at least @BAR@ faster than the target in every cell; your storage makes that possible.";

/// The workload role's goal sentence when every runtime target names one reference system (`RuntimeTarget::system`,
/// `@SYSTEM@`), for example DuckDB alone (`baselines/duckdb_baselines.py`).
pub const WORKLOAD_GOAL_TARGET_SYSTEM: &str = "\
Design **verified** storage that lets the **whole workload** run **faster than @SYSTEM@**: the runtime targets in CURRENT FACTS (Statements) are @SYSTEM@'s measured times for each statement, binding and worker count. Query authors aim for at least @BAR@ faster than the target in every cell; your storage makes that possible.";

/// The query role's task.
pub const QUERY_TASK: &str = "\
# Task

Write Rust code with Verus specifications and proofs that computes **this SQL query exactly** over stored data (CURRENT FACTS, Query: the SQL and its parameters).

Your query reads one or more storages:
- the workload's shared storages and other admitted storages, listed in `storages.json`;
- new storages you add with the storage tools. A new storage has its own builder, representation relation `represents` and readers, is verified and built through the same path as the workload's storages, and is **built from admitted storages** (read through their readers and contracts), never from the source data.";

/// The query role's goal under the execution-time objective: what a submission must be and what wins.
pub const QUERY_GOAL: &str = "\
# Goal

@TARGET@

1. **What a submission must be.** Every submission must be exact and verified: it passes the correctness gate (Evaluation). Performance never relaxes the proof.
2. **What wins.** Among exact verified submissions, the lowest `score_ns` wins: the geometric mean of the hot medians over every benchmark binding x configured worker count, every cell weighing equally. One submission is selected for all cells; there is never a separate winner per binding or worker count.
3. **The early stop.** Once the selected submission's official hot median is at most @BAR_FRACTION@ of the target in every cell (the @BAR@ bar in CURRENT FACTS, Targets and official results), no further submission is requested.";

/// The query role's goal under the correctness objective: the simplest correct implementation; the first exact
/// verified submission ends the run.
pub const CORRECTNESS_QUERY_GOAL: &str = "\
# Goal

Write the **simplest correct implementation**: straightforward code and proofs a reader can follow. Do no performance work: no parallelism and no extra structures unless the query or its proof needs them. The first exact verified submission (Evaluation) is admitted and ends the run; times are recorded but select nothing.";

/// The query role's storage situation: shared storage first, additions within the budget.
pub const QUERY_STORAGE: &str = "\
# Storage: shared, with a budget

- @FIRST_STORAGE_STEP@ (the workload's admitted storages in `storages.json`).
- **Then decide** whether a new storage is worth its space for this query: an index, a permutation, skip metadata, or, where the run's storage policy allows a second copy, another layout or more columns. Under `physical_only` each column's values are stored once, so a new storage adds index keys, permutations or skip metadata beside the shared copy (`extends`), never another copy. You decide; nothing is prescribed and no performance win is promised either way.
- CURRENT FACTS, Storage shows the bytes already used and the budget left; `storages.json` lists each admitted storage with its size.
- The storage budget is the only hard limit: all serving storage together stays within it. A storage you add is shared: later queries may use it.
- Other sessions share the budget and the library while you work. CURRENT FACTS, Storage is read before each call, every storage tool result carries `storage_budget_now`, and `catalog` re-reads both on demand: check what is left before you spend proof work on a large new storage. Each is a snapshot, not a reservation; the budget is enforced when a storage is registered or a submission is evaluated.
- **How to add a storage.** Its `verus-storage.json` sets `built_from`: the admitted source storages it reads, and optionally `extends` one of them to keep that source's parts unchanged (linked, never copied or rebuilt) and add new parts after them. It is checked against the fixed derived storage entry (`fixed/storage_entry_derived.rs`; `obligations.json` `storage.storage_entry_derived`): the builder reads the sources only through their readers and StoredParts extents and proves that the new parts represent the same database (old `represents` + correct copy => new `represents`). It needs a name of its own. A storage not built from admitted storages is refused (`storage_not_built_from_admitted`). The manifest's `modules` may be omitted (derived from the files); `data_policy` has one `{part, table, kind, columns, why}` entry per part.
- What you know about the data comes from the storages' contracts and descriptions (row order, bounds, density, sizes in `represents`, the readers' specifications, `layout` and `data_policy`). Query authors get no separate statistics of the source data, so nothing can conflict with the contracts.";

/// What is fixed and what the query author owns.
pub const QUERY_FIXED: &str = "\
# What is fixed and what you own

- **Fixed** (regenerated at freeze): the final SQL claim, the entry, and every framework file of your crate: `spec/**`, `exec/**`, `bridge/**`, `link/**`, `schema.rs`, `query.rs`, `stores/**` (the copied storage interfaces), `gendb_*.rs` and `gendb_entry/**`.
- **You own** only `src/agent/**` of the query crate, plus the author roots of storages you create.
- **You choose** every intermediate specification, lemma and bridge proof. The `link/**` toolkit is optional, except the fixed link definitions the final claim is stated with (`final-claim.json` `fixed_link_definitions`).
- **Never weaken, assume or bypass the fixed claim.** The source scanner and `--no-cheating` refuse bypasses (`rules.json`).";

/// The physical_only storage policy (revision 2), shared by both roles, with the user's clarifications (the current revision replaced revision 1's covering indexes).
/// `storage::policy` holds the structured wording.
pub const PHYSICAL_ONLY_POLICY: &str = "\
# Storage policy: physical_only

Store each table's data **once**, and optimize the physical organization of that one copy freely. Beside it, keep only metadata over it: own-table key indexes, permutations, skip metadata and layout offsets. Do not store a second copy of any column, query computation or cross-table correspondences before the measured call. Verus does not check this classification; your declarations and published sources are reviewed.

**Allowed**
- **One copy of each table's rows (base payload)** in any column layout, partitioning, sorting or clustering. Every row is kept. Lossless encodings and compression. One copy may span several parts (for example codes, dictionary and offsets of a text column, or disjoint partitions).
- **Co-clustering:** a table's row order may follow another table's order (for example the rows of a child table clustered by the key of the parent table it references), provided nothing cross-table is stored: keys used only to choose the order are not stored, and a query that relies on two tables lining up checks their keys at run time.
- **Indexes of one table:** its own key values to its own row positions or ranges. The key values may repeat values of the stored copy; an index carries no other column's values.
- **Permutations:** row positions only, into the one copy, giving another sort order.
- **Skip metadata** computed from one table's own rows or blocks: min/max zone maps, Bloom filters (including trigram Bloom filters for LIKE), statistics.
- **Run offsets and row counts that describe a layout**, even when the layout's groups match a query's GROUP BY: a sorted, run-length-encoded layout gives group sizes for free, as in column stores. Queries must still read and combine the actual values.
- Readers over all of these. All of it counts against the storage budget and is reported openly in `data_policy`. Rule of thumb: techniques already standard in academia and industry are allowed, as long as each table's data is stored once.

**Not allowed**
- A second copy of any column's values, full or partial, in any order or encoding, in the same or another storage (for example a re-sorted copy of a table): keep another order as a permutation.
- Covering indexes: an index carrying copies of columns other than its keys.
- Stored query-derived values (expression results such as `price*(1-discount)`), or tables holding only a predicate's matching rows.
- Materialized joins or denormalized rows: another table's values copied beside a row, or join results.
- Cross-table row locators, even position-only: join indexes, row-match maps, or another table's keys, row positions or match ranges.
- Precomputed EXISTS / NOT EXISTS / IN flags or other subquery answers.
- Stored aggregates of values: group or block sums, prefix sums, aggregate value bounds (such as revenue bounds), cubes. (Run offsets and row counts of the layout itself are allowed, above.)
- Cached answers, or any state kept across measured calls.

**Boundary.** Each column's values are stored once across the serving storage; every other stored entry is an index key with its own row positions, a row position, or metadata over one table's own rows. Filtering, joins, sorting, aggregation and temporary structures happen inside each measured call and are timed. When a structure is uncertain, choose the conservative form and say why in `data_policy`.

**Declaration.** Every storage manifest declares `data_policy` for each part: `{part, table, kind, columns, why}`. `kind` is `base_payload` (part of the one copy of `columns`; every part of a multi-part encoding lists the column), `index_keys` (`columns` are the keys), `permutation`, `own_skip_metadata` or `layout_offsets_counts`; `columns` are stored columns of `table`, required for `base_payload` and `index_keys`. A storage without a declaration is refused (`storage_policy_declaration_missing`), as is an old kind `own_source_values`/`own_index` (`storage_policy_declaration_revision`). A column that is already `base_payload` of another serving storage is refused (`storage_payload_duplicate`) before every build (unverified diagnostic builds included), at evaluation and at registration, and so is a query whose storage uses would add a second copy (an older version of a storage pinned beside its current version); parts an extension inherits through `extends` are its source's and are not declared again. Admitted storages registered before this rule are not offered (`storage_policy_revision_superseded`); a package the user's review excluded is refused (`storage_policy_excluded`).";

/// The query role's task under `storage_policy` `fixed_flat`: the stored data is fixed.
pub const FLAT_QUERY_TASK: &str = "\
# Task

Write Rust code with Verus specifications and proofs that computes **this SQL query exactly** over stored data (CURRENT FACTS, Query: the SQL and its parameters).

Your query reads the **fixed flat storages** of this run (`storages.json`): one storage `flat_<table>` per table, holding every column of the table as a plain array. You do not design, add or change storage in this run.";

/// The fixed flat storage, query role (`storage_policy` `fixed_flat`; `storage::flat` holds the structured wording).
pub const FIXED_FLAT_STORAGE: &str = "\
# Storage: fixed flat arrays

This run measures query code over **our flat-storage definition**: every table is stored once, by GenDB, as plain typed arrays, one per column, in the original source row order: stored row `i` is source row `i`. There is no sorting, partitioning, index, permutation, compression, dictionary, data-dependent encoding or skip metadata, and no statistics about the data.

- **Storages.** `flat_<table>` stores every column of `<table>`. Name the ones your query reads in `verus-query.json` by their admitted package ids (`storages.json` `use_as`). Their interfaces are copied under `admitted-storages/` and into your crate as `stores/flat_<table>/interface/mod.rs`.
- **Representation** (fixed by the declared SQL type, never by the data): bigint is an `I64` value; integer an `I32` value; date an `I32` count of days since 1970-01-01; numeric(p,s) an `I128` coefficient (value = coefficient * 10^-s); text, varchar and char two parts, `I64` offsets (rows + 1, positions in the bytes part; the first need not be 0) and `U8` UTF-8 bytes, value `i` = `bytes[offsets[i] .. offsets[i + 1]]`. One part per column, two per text column, in column order; each interface lists its part constants.
- **Readers.** Each interface defines `represents(parts, rels)` (the table is `rels[0]`, its row `i` is `row_at(parts, i)`) and verified readers: `stored_rows`, `read_<column>(s, lo, hi, Ghost(rels))` for fixed-width columns (a slice whose element `j` is row `lo + j`), `read_<column>_at(s, i, Ghost(rels))` and `read_<column>_range(s, lo, hi, Ghost(rels))` (at least one row) for text, and the generic `text_rows`. You may also read `StoredParts` extents with the part constants and prove what you need from `represents`.
- **At run time** you may build anything inside each measured call: hash tables, sorted or partitioned copies, group tables, join structures, bitmaps. They are built and discarded inside the call and timed. Nothing computed in one call may be kept for a later one: `static` items are refused in your files. Explain your data access (the columns and extents your readers request, the structures each call builds) briefly in the submission's `data_access_analysis`.
- **Not available:** the storage tools, workspace storages (`fixed_flat_workspace_storage`) and any storage other than the flat ones (`storage_policy_ineligible`).";

/// What is fixed and what the query author owns, under `fixed_flat`.
pub const FLAT_QUERY_FIXED: &str = "\
# What is fixed and what you own

- **Fixed** (regenerated at freeze): the final SQL claim, the entry, the flat storages and every framework file of your crate: `spec/**`, `exec/**`, `bridge/**`, `link/**`, `schema.rs`, `query.rs`, `stores/**` (the copied flat storage interfaces), `gendb_*.rs` and `gendb_entry/**`.
- **You own** only `src/agent/**` of the query crate.
- **You choose** every runtime algorithm, plan, parallelism and compiler control, and every intermediate specification, lemma and bridge proof. The `link/**` toolkit is optional, except the fixed link definitions the final claim is stated with (`final-claim.json` `fixed_link_definitions`).
- **Never weaken, assume or bypass the fixed claim.** The source scanner and `--no-cheating` refuse bypasses (`rules.json`).";

/// How to work, query role, under `fixed_flat`, execution-time objective: measure first, prove later; proofs; reuse;
/// parallelism.
pub const FLAT_QUERY_HOW_TO_WORK: &str = "\
# How to work

**Measure first, prove later.** Proofs are the most expensive part, so do not spend them on designs that may be too slow.
- Choose your design by measuring first with unverified trials (`verification: \"not_run\"`). Then prove the design you chose once.
- One `trial` times the whole matrix (every benchmark binding x configured worker count) and reports per cell the target, the @BAR@ bar, your median with its spread, and whether it meets the bar. Compare at least one alternative design when it is cheap to measure.
- Order of work that has worked: read the flat interfaces and sizes, measure, write a serial verified kernel, then add parallelism.
- With flat arrays every structure that speeds up a lookup (a hash table, a sorted run, a bitmap) is built inside the call: weigh its build time against what it saves, at each worker count.

@PROOF_ADVICE@

@REUSE_ADVICE@

@PARALLEL_ADVICE@

@CHECK_ECONOMY@";

/// Tools, query role, under `fixed_flat`.
pub const FLAT_QUERY_TOOLS: &str = "\
# Tools

- **Typed `gendb_local` tools** (`tools.json`):
  - query tools: `check`, `verify`, `compile`, `trial`, `profile`;
  - `catalog`: re-read the library (the flat storages and admitted query code);
  - you may also run the pinned Verus toolchain directly (`toolchain.json`).
  The storage tools are not available in this run. Use the others as often as useful. Local runs are diagnostics; only the framework's evaluation of a submission is official.
- **`trial`** times the whole benchmark matrix by default (every benchmark binding x configured worker count; `workers` or `arguments` narrow it) with 1 warm + 1 hot call per cell by default (`hot_calls` asks for more when you need the spread or less noise; one sample has no spread estimate), and reports per cell: @TRIAL_CELL_FIELDS@. It also reports per storage use the read requests, requested elements and bytes, stored bytes, the child's device reads, each cell's result comparison, and the tiny cases where the validation policy runs them. Trials hold the host's timing lease, so two timings never overlap.
- **`profile`**: one cell, 1 warm + 1 measured call, with per-call dispatch ranges, process CPU and calling-thread CPU.
- **Unverified runs.** `trial` and `profile` accept `verification: \"not_run\"`: the frozen crate is compiled with `rust_verify --no-verify` (no proof obligation checked; source rules and `--no-cheating` unchanged) and run on the real data (and tiny cases where the validation policy runs them) with the same result comparison. Every such result is labelled `diagnostic_unverified`; it never counts as a submission, proof, admission, official measurement or early-stop input. A wrong answer is still a named mismatch. Instrumentation inside the crate (clock reads, logging) needs `external_body`, which every GenDB job refuses; keep it in your own scratch builds.
- **Caching.** A proof check, compile or (where run) tiny-case test of identical crate content is reused, never rerun; results say `reused`.";

/// Placeholder of the correctness gate (`QUERY_CORRECTNESS_GATE`) in both objectives' Evaluation, replaced by `policy`.
pub const CORRECTNESS_GATE: &str = "@CORRECTNESS_GATE@";

/// The correctness gate every query submission passes, under either objective.
pub const QUERY_CORRECTNESS_GATE: &str = "\
- **Correctness gate.** Verus checks the whole frozen crate (framework files plus your `src/agent`) with `--no-cheating` against the fixed final SQL claim, for every valid input, every allowed parameter binding and every worker count. The compiled library of that same directory must then pass the checks of the run's validation policy at every configured worker count (contract `validation.json`: under `tests_and_references` exact references at every admission binding and the generated tiny cases; under `formal_proofs` the benchmark bindings on the full data, agreeing with the saved answers of other engines). A submission that fails is recorded and never promoted.";

/// The query role's evaluation under the execution-time objective: correctness gate, measurement, selection, early
/// stop and submissions.
pub const QUERY_EVALUATION: &str = "\
# Evaluation

@CORRECTNESS_GATE@
- **Measurement.** Every exact verified submission is timed at every benchmark binding (CURRENT FACTS, Query: samples of the parameter domain, never the proof domain) and every configured worker count. Each cell is the median of 3 hot runs after 1 warm-up (`performance.json`).
- **Selection.** The lowest `score_ns` wins (Goal). After the last submission, the selected one is qualified, served and measured again in timing windows of its own. A slower or failed later submission never replaces a faster one.
- **Runtime targets** are user-supplied guidance per benchmark binding and worker count, with their provenance and timing scope. They are not same-window comparisons.
- **Early stop.** Once the selected submission's official exact hot median is at most @BAR_FRACTION@ of the target in every cell, no further submission is requested, even below the submission limit. Medians of different submissions never combine; a failed or unverified submission, or a local trial, never triggers it. If your own verified local trials already reach this in every cell, submit promptly instead of polishing further.
- **Submissions.** You may submit up to the LEDGER limit. A rejected submission counts; local jobs (trials, profiles, verifies) never count. A submission whose evaluation failed **in the framework** (not your candidate; LATEST FEEDBACK says so) is **not counted**, and its verdict is never reused. An unchanged resubmission is not remeasured but still counts; it ends the search unless the targets are still unmet, and then a second consecutive unchanged resubmission ends it. Submission and cost guards are ceilings, not quotas (\"unset\" means no guard). There is no model-turn cap.";

/// The query role's evaluation under the correctness objective: correctness gate, admission of the first passing
/// submission, descriptive times and submissions.
pub const CORRECTNESS_QUERY_EVALUATION: &str = "\
# Evaluation

@CORRECTNESS_GATE@
- **Admission.** The first submission that passes the gate is qualified and served, and the run ends: no further submission is requested, even below the submission limit.
- **Times.** The gate's runs at the benchmark bindings are timed (CURRENT FACTS, Host and measurement). The times are recorded but select nothing: there are no runtime targets, no ranking and no early stop.
- **Submissions.** You may submit up to the LEDGER limit. A rejected submission counts; local jobs (trials, profiles, verifies) never count. A submission whose evaluation failed **in the framework** (not your candidate; LATEST FEEDBACK says so) is **not counted**, and its verdict is never reused. An unchanged resubmission is not evaluated again but still counts; a second consecutive unchanged resubmission ends the run. Submission and cost guards are ceilings, not quotas (\"unset\" means no guard). There is no model-turn cap.";

/// How attempts and sessions work, shared by both roles.
pub const ATTEMPTS: &str = "\
# Attempts, sessions and your notes

- **Each attempt is one fresh Claude session** that ends with your submission. The next attempt (if any) is a new session: it gets this prompt with GenDB's recorded facts (the official result of every submission in CURRENT FACTS; in HANDOFF FROM EARLIER ATTEMPTS the record paths and a log of local trials) and your notes. Your code stays on disk in the workspace and is read on demand.
- **Before you submit, write `NOTES.md`** in your workspace (`files.notes`), about one page: your design and why, what you tried and what helped (with measured numbers), untried ideas, and proof difficulties with how you solved them. GenDB's facts are authoritative; the notes are hints for the next attempt. Keep it current; replace stale content.
- If a call is interrupted before it submits, the retry continues the same session.";

/// How to work, query role, execution-time objective: measure first, prove later; proofs; reuse; parallelism.
pub const QUERY_HOW_TO_WORK: &str = "\
# How to work

**Measure first, prove later.** Proofs are the most expensive part, so do not spend them on designs that may be too slow.
- Choose your design by measuring first: unverified trials (`verification: \"not_run\"`) and unverified storage builds. Then prove the design you chose once.
- One `trial` times the whole matrix (every benchmark binding x configured worker count) and reports per cell the target, the @BAR@ bar, your median with its spread, and whether it meets the bar. Compare at least one alternative design when it is cheap to measure.
- Order of work that has worked: look at the storage contracts and sizes, measure, write a serial verified kernel, then add parallelism.
- Fast path plus general path: a fast path guarded by layout facts the storage contract states, with a verified general path behind it, keeps the proof complete.

@PROOF_ADVICE@

@REUSE_ADVICE@

@PARALLEL_ADVICE@

@CHECK_ECONOMY@";

/// How to work, query role, correctness objective (every storage policy): proofs, reuse of admitted code (the first
/// part of `REUSE_ADVICE`, without the advice to write general modules), the worker-count rule and the check economy;
/// no measuring advice.
pub const CORRECTNESS_QUERY_HOW_TO_WORK: &str = "\
# How to work

@PROOF_ADVICE@

**Reuse.**
- Search the index of all admitted code, proofs and general modules before writing a piece yourself (`files.search_index`: name, one-line description and specification of each item). Copy a module as-is or adapt it; you decide. Nothing is composed automatically, and Verus checks everything again in your crate.
- The framework's helper lemmas in `link/**` and `bridge/**` are public; call them instead of copying them.

**Parallelism.** The worker count of a cell is the **maximum** the call may use, not a requirement: fewer threads, or a serial path, is fine at every worker count (`parallel.json`).

@CHECK_ECONOMY@";

/// Proof advice for both roles.
pub const PROOF_ADVICE: &str = "\
**Proofs.**
- Decompose a proof into small lemmas, each with a narrow purpose (one row-evaluation step, one loop invariant step, one merge step).
- On an rlimit failure, profile it: `verus --profile` (through `toolchain.json` `direct_verus`, run from `verus-tmp/`; see `direct_profiling`) shows which definitions are over-expanded. Then hide those definitions (`#[verifier::opaque]` / `hide`, revealed only where needed), add one-step unfold lemmas, or split the proof. **Do not raise rlimit.**
- Verify modules or single functions while you iterate (`toolchain.json` `scoped_verify`); the official check is always the whole crate.";

/// Reuse advice for both roles: the search index and general modules.
pub const REUSE_ADVICE: &str = "\
**Reuse.**
- Search the index of all admitted code, proofs and general modules before writing a piece yourself (`files.search_index`: name, one-line description and specification of each item). Copy a module as-is or adapt it; you decide. Nothing is composed automatically, and Verus checks everything again in your crate.
- The framework's helper lemmas in `link/**` and `bridge/**` are public; call them instead of copying them.
- When a piece of your code or proof is naturally general (sort, codec, dictionary, key directory, top-k, LIKE, GROUP BY lemma, parallel split and merge), write it as a separate module under @COMMON_DIR@ with a specification that mentions no query constants and no single layout, and a one-line description in its module header (`//! <description>`). GenDB indexes it at admission for later authors. Do this when the piece is naturally general; it is not required.";

/// Parallelism advice for both roles.
pub const PARALLEL_ADVICE: &str = "\
**Parallelism.** The worker count of a cell is the **maximum** the call may use, not a requirement: fewer threads, or a serial path, is fine where it is faster (`parallel.json`).";

/// The check economy, shared by both roles.
pub const CHECK_ECONOMY: &str = "\
**Check economy.** Once a check passes, repeat it only after a meaningful code or specification change, to diagnose a concrete failure, or to settle a check that is still unresolved. Identical code is never checked twice: proof checks, compiles and (where the validation policy runs them) tiny-case tests are cached per exact crate content. Do not sweep solver settings (rlimit, seeds) or rerun passing proofs to measure margin. Trials, repairs and the measurements your design needs are not limited by this.";

/// Inputs and conduct, query role.
pub const QUERY_INPUTS: &str = "\
# Inputs and conduct

- **Read `files.author_contract` first.** It maps every input: the task and final claim; the SQL meaning with an annotated AST; the demanded columns; every admitted storage version with its interfaces, readers, contracts and measured sizes; the stored-parts read API; parameters, domains, output and tests; the proof library with its proof patterns, and parallelism; the registry of fixed definitions and the source rules; the toolchain, the tools with their result fields, failure classes and accounting.@PERFORMANCE_FILE_INPUT@
- **Look items up before reading framework files.** Use `index.json` `commands.api_lookup` (per-file item catalogs with signatures and ensures), grep inside your crate, and the vstd sources. Read the regions you need, not whole toolkit files.
- **Your inputs:** your workspace (the crate, its framework files, the admitted code under `prior-verus-code`), the files `files.author_contract` maps and the prepared data they name; the pinned toolchain including the vstd sources; standard system tools and hardware diagnostics.
- **Reusable implementations** are exactly the admitted catalogs: the search index, `files.library` (admitted query code) and `storages.json` (admitted storages). An empty catalog means you write new code from the supplied specifications and APIs. The SQLSpec library and the proof helpers in your crate are always available.
- **Not inputs:** other GenDB runs, old outputs, other libraries, scratch directories, tests, fixtures, repository source or history, host or controller source, and any binding file the framework does not give you. Do not read, list or search them; every tool call is recorded and audited.
- **Do not** alter ledger, library, reference or authority files; hash or fingerprint whole datasets; launch inference or agents.
- **Readability.** Write readable code, specifications and proofs: meaningful names, one purpose per function, units (rows, bytes, days, scales), a short header per module explaining its layout and invariants, and proof steps explained where they are not obvious. Admitted sources are published and read by people and by later authors.";

/// Tools, query role.
pub const QUERY_TOOLS: &str = "\
# Tools

- **Typed `gendb_local` tools** (`tools.json`):
  - storage tools: `storage_check`, `storage_verify`, `storage_compile`, `storage_build`, `storage_register`;
  - query tools: `check`, `verify`, `compile`, `trial`, `profile`;
  - `catalog`: re-read the library (admitted storages and the storage budget);
  - you may also run the pinned Verus toolchain directly (`toolchain.json`).
  Use them as often as useful. Local runs are diagnostics; only the framework's evaluation of a submission is official.
- **`trial`** times the whole benchmark matrix by default (every benchmark binding x configured worker count; `workers` or `arguments` narrow it) with 1 warm + 1 hot call per cell by default (`hot_calls` asks for more when you need the spread or less noise; one sample has no spread estimate), and reports per cell: @TRIAL_CELL_FIELDS@. It also reports per storage use the read requests, requested elements and bytes, stored bytes, the child's device reads, each cell's result comparison, and the tiny cases where the validation policy runs them. Trials hold the host's timing lease, so two timings never overlap.
- **`profile`**: one cell, 1 warm + 1 measured call, with per-call dispatch ranges, process CPU and calling-thread CPU.
- **`catalog`**: re-reads the library now. CURRENT FACTS, Storage and `storages.json` are read before each call; other sessions share the budget and may admit storages (or new versions of a name) meanwhile. `catalog` rewrites `storages.json` and `storage-budget.json` and returns what is used and left. It is a snapshot, not a reservation: registration enforces the budget.
- **Unverified runs.** `trial` and `profile` accept `verification: \"not_run\"`: the frozen crate is compiled with `rust_verify --no-verify` (no proof obligation checked; source rules and `--no-cheating` unchanged) and run on the real data (and tiny cases where the validation policy runs them) with the same result comparison. `storage_build` accepts the same for an unverified storage build. Every such result is labelled `diagnostic_unverified`; it never counts as a submission, proof, admission, official measurement or early-stop input, and an unverified storage can never be submitted or registered. A wrong answer is still a named mismatch. Instrumentation inside the crate (clock reads, logging) needs `external_body`, which every GenDB job refuses; keep it in your own scratch builds.
- **Caching.** A proof check, compile or (where run) tiny-case test of identical crate content is reused, never rerun; results say `reused`.
- **`storage_build`** reports stored bytes, canonical column bytes and build time. Explain your storage choice briefly in the manifest's `layout.choice` and in `data_access_analysis`.";

/// The submission rule, both roles (`@MANIFEST@` names the role's manifest file).
pub fn submission(manifest: &str) -> String {
    format!(
        "# Submission\n\nA submission is the call's structured JSON result `{{candidate_manifest, rationale, data_access_analysis}}`. The schema is enforced; `rationale` and `data_access_analysis` are short, nonempty texts. Submitting ends this session (write `NOTES.md` first).\n\n`candidate_manifest`: your `{manifest}`. {CANDIDATE_MANIFEST_RULE}."
    )
}

/// The process rules of a shared host, both roles.
pub const PROCESSES_APPENDIX: &str = "\
# Appendix: processes on a shared host

This host is shared with other sessions running the same tools. You may start, background and stop your own checks, compiles and trials whenever useful, within these rules.

- **Need a result? Run in the foreground.** A Bash call that finishes within its timeout returns only after its command and every process it started have exited, with the command's exit status.
- **A call that reaches its Bash timeout is not stopped.** The provider moves it to a background task, and its answer says so. It keeps running with every process it started. So for a long run, do one of these:
  - bound it below the call's timeout with `timeout -k 10 <seconds> <command>`: TERM goes to the command and its children in timeout's process group, then KILL 10 s later. A child that calls `setsid` leaves that group.
  - or start it in its own recorded process group: `setsid <command> > <log> 2>&1 & echo $! > <run>.pgid`. The recorded number is both its PID and its group. `ps -o pid,etime,args -g $(cat <run>.pgid)` shows it, and `kill -TERM -- -$(cat <run>.pgid)` stops it with every child.
- **Each Bash call runs in its own process group** (`$GENDB_BASH_CALL_GROUP` inside the call), and a call moved to the background keeps that group.
  - `kill -TERM -- -<that group>` stops that call, and GenDB's shell guardian then kills and reaps everything it started.
  - To recover the group of a background call, use what you recorded (for example, `echo $GENDB_BASH_CALL_GROUP > <run>.group` before a long command), or your own process tree (`pstree -p -a $GENDB_AUTHOR_PROVIDER_PID`). Then signal exactly that PID or group.
- **Do not start a run in the background and poll its log for completion text.** The poll cannot see the process exit, so text that never appears (a refused option, a crash) makes it wait out its whole timeout. For direct `rust_verify` runs, use the foreground route in `toolchain.json` (`direct_verus`).
- **Wait for a local job with the `wait` tool; never wait or poll for one inside a Bash call.** Every Bash call holds the host's shared activity lock until it ends, and a timed job (`trial`, `profile`) needs that lock alone to start, with your session's later jobs queued behind it: a Bash call that waits for a job delays that very job. `wait` holds no lock; it returns the job's result when the job ends, or its status after at most `wait_seconds`.
- **Never kill by executable name, command pattern or user.** No `pkill`, `killall`, `pgrep -f ... | xargs kill` or `ps | grep | kill`. Never signal a process outside your own tree, and never signal `gendb_local` jobs or GenDB's evaluation.
- **Crash dumps.** GenDB starts its processes and your Bash commands with Linux `coredump_filter` 0 (the value actually set is in CURRENT FACTS, Host and measurement). A crash is still reported by the host's crash handler, but its dump holds no memory contents. Keep that setting for your processes.";

/// The workload role's task.
pub const WORKLOAD_TASK: &str = "\
# Task

Design, write and prove the **shared stored data for this whole workload**: every SQL statement in CURRENT FACTS, Statements (templates with their parameters; the run's declared integrity constraints are in CURRENT FACTS, Integrity constraints). For each storage you write:
- a **builder** over the delivered source columns;
- a **representation relation** `represents(parts, rels)` that the builder proves;
- **readers** over StoredParts extents that query authors call.";

/// The workload role's goal.
pub const WORKLOAD_GOAL: &str = "\
# Goal

Your storage is the foundation for every query author of this workload. @TARGET@ Aim for a design close to the best for the whole workload:
- **Speed.** Make every statement fast. Give more weight to long-running statements (each statement's runtime targets in CURRENT FACTS, Statements), but optimize the others too.
- **Complete lossless storage.** Every column of every table is stored at least once, in some storage you submit (under `physical_only`, exactly once: see the storage policy). Columns the workload uses get layouts optimized for execution; the other columns are stored compressed for space. All of it is lossless and proved, and counted in the budget, so the original source data can be deleted afterwards. **Proved** means: each storage's interface provides `lemma_represents_determines` (the parts determine the relations they represent; `obligations.json` item `lossless`), which the fixed `theorem_storage_lossless` of every storage crate calls. The framework checks that your storages together cover every column of every table.
- **Space.** Stay within the storage budget (CURRENT FACTS, Storage). It counts the storage you serve from, not the original source files. Prefer layouts that many statements share. Space you leave free is available to query authors later.
- **Usable contracts.** Query authors use only your readers' specifications and `represents` in their proofs, and they learn about the data only from your contracts and descriptions. State everything they need: row order, the meaning of every index or directory, encodings, value bounds, density and sizes. A contract that says only \"these are the values\" makes your sort order and indexes unusable.

No layout or weighting is prescribed; you decide. The trade-off is stored size, build time, read and decode cost, and query time. Explain your choice briefly in each manifest's `layout.choice` and in the submission's `data_access_analysis`, including which statements each storage serves.";

/// How to work, workload role.
pub const WORKLOAD_HOW_TO_WORK: &str = "\
# How to work

**Measure first, prove later.** Proofs are the most expensive part.
- Read the statements and the source data facts (`data.json` `source_facts`: min/max, estimated distinct counts, sortedness, key density per column), then design.
- Build candidate layouts **unverified** (`storage_build` with `verification: \"not_run\"`) and compare their sizes and build times. Run diagnostic queries of the statements over them (`task.json` `diagnostic_query`; `trial` with `verification: \"not_run\"`) to check read cost and query time.
- Then prove the layouts you chose, and check with a verified diagnostic query that the readers' specifications are strong enough to prove the fixed SQL claims.
- Admission ends this session (Evaluation), so compare candidates first.

@PROOF_ADVICE@

@REUSE_ADVICE@

@PARALLEL_ADVICE@

@CHECK_ECONOMY@";

/// What is fixed and what the workload author owns.
pub const WORKLOAD_FIXED: &str = "\
# What is fixed and what you own

- **Fixed** (regenerated at freeze): the storage entry, the declaration, and every framework file. A storage over source columns uses the storage entry (`fixed/storage_entry.rs`); a storage built from storages already admitted (manifest `built_from`) uses the derived storage entry (`fixed/storage_entry_derived.rs`).
- **Manifest.** `modules` may be omitted (derived from the files); `data_policy` has one `{part, table, kind, columns, why}` entry per part (`stored-data.json`).
- **You own** only `src/stores/<name>/interface/**` and `src/builder/**` of each storage crate (plus a general module directory there, below), and `src/agent/**` of your diagnostic query crates. You choose every intermediate specification, lemma and proof.
- **Never weaken, assume or bypass a fixed claim.** The source scanner and `--no-cheating` refuse bypasses.";

/// The workload role's evaluation.
pub const WORKLOAD_EVALUATION: &str = "\
# Evaluation

- **Admission check.** Each submitted storage crate must verify whole with 0 errors (`--no-cheating`) against the fixed storage entry: the builder proves `represents` for the delivered source columns of every valid database. Its stored library must then build its asset over the prepared data with status Ok (under the validation policy `tests_and_references` also over every tiny input of the statements that read its tables; under `formal_proofs` nothing more: contract `validation.json`). The storages together must store every column of every table, within the storage budget.
- **First passing submission ends the session.** The first submission whose storages all pass is admitted, each storage as a new admitted version. There is no later submission to improve it.
- **Afterwards.** Admitted storages are offered to every query author of this workload. They measure on them first and may add storages built from yours within the remaining budget.
- **Submissions.** Up to the LEDGER limit. A rejected submission counts; local jobs never count. A submission whose evaluation failed **in the framework** (LATEST FEEDBACK says so) is **not counted**, and its verdict is never reused. Submission and cost guards are ceilings, not quotas (\"unset\" means no guard). There is no model-turn cap.";

/// Inputs and conduct, workload role.
pub const WORKLOAD_INPUTS: &str = "\
# Inputs and conduct

- **Read `files.author_contract` first.** It maps every input: the task with its workflow; the workload statements, and per statement the same SQL meaning, annotated AST, demand, parameters, domains, output and tests a query author reads; the union demand; the data facts (`data.json`, with the source data facts and what is unavailable); `performance.json` (each statement's objective, the user's runtime targets, how trials time a query); the fixed storage and query obligations and the final claim; the stored-parts read API and the registry of fixed definitions; admitted storages, the proof library with its proof patterns, and parallelism; source rules, the toolchain, the tools with their result fields, failure classes and accounting.
- **Your inputs:** your workspace; the files `files.author_contract` maps and the prepared data they name; the pinned toolchain including the vstd sources; standard system tools and hardware diagnostics.
- **Reusable implementations** are exactly the admitted catalogs: the search index, `files.library` where named, and `storages.json`. An empty catalog means you write new code from the supplied specifications and APIs. The SQLSpec library and the proof helpers in your crates are always available.
- **Not inputs:** other GenDB runs, old outputs, other libraries, scratch directories, tests, fixtures, repository source or history, and any binding file the framework does not give you. Do not read, list or search them; every tool call is recorded and audited.
- **Do not** alter ledger, library, reference or authority files; hash or fingerprint whole datasets; launch inference or agents.
- **Readability.** Meaningful names, one purpose per function, units (rows, bytes, days, scales), a short header per module explaining its layout and invariants, proof steps explained where they are not obvious. Admitted sources are published and read by people and by later authors.";

/// Tools, workload role.
pub const WORKLOAD_TOOLS: &str = "\
# Tools

- **Typed `gendb_local` tools** (`tools.json`): `storage_check`, `storage_verify`, `storage_compile`, `storage_build`, `storage_register` for storages; `check`, `verify`, `compile`, `trial`, `profile` for diagnostic query crates of any workload statement over your storages (`statement` names it). `catalog` re-reads the library now (storages.json and storage-budget.json; other sessions may admit storages meanwhile; a snapshot, not a reservation). You may also run the pinned Verus toolchain directly (`toolchain.json`). Use them as often as useful. Local runs are diagnostics; only the framework's evaluation of a submission is official.
- **What they report.** `storage_build`: stored bytes, canonical column bytes and build time. `trial`: the statement's whole benchmark matrix by default, per cell target, @BAR@ bar, median, min and max, met; per storage use the read requests, requested elements and bytes, stored bytes and the child's device reads; 1 warm + 1 hot call per cell by default (`hot_calls` asks for more; one sample has no spread estimate). `profile`: one cell with per-call CPU and dispatch detail.
- **Unverified runs.** `storage_build` and `trial`/`profile` accept `verification: \"not_run\"`: built without proof checks, labelled `diagnostic_unverified`, never submitted, registered or admitted.
- **Caching.** A proof check, compile or (where run) tiny-case test of identical crate content is reused, never rerun.";
