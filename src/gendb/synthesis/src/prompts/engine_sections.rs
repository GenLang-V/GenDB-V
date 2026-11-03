//! The fixed Markdown sections of the engine author's prompt, assembled by
//! `prompts::engine_policy` with the shared sections of `prompts::sections` (scope rules, the `physical_only` policy,
//! proof, reuse, parallelism and check-economy advice, the submission rule and the processes appendix) and the call's
//! data sections. Nothing here names a query, a template, a table or a column: the engine author learns the schema and
//! the training set from CURRENT FACTS and the contract files, and the sections teach the framework only.
//!
//! Placeholders replaced by the policy: `@TIMING_BINDING@` (the official binding), `@VARIANT_KINDS@` (the frozen
//! variants' transformation kinds), `@ROUND@` (this round's number) and the shared `@PROOF_ADVICE@`, `@REUSE_ADVICE@`,
//! `@PARALLEL_ADVICE@`, `@CHECK_ECONOMY@`.

/// ENGINE_TASK: one engine for every well-typed query on the schema.
pub const ENGINE_TASK: &str = "\
# Task

Write **one engine** for this schema: Rust code with Verus specifications and proofs that answers **every supported query** over the stored data. The engine is called with a query as a typed AST (`EOrderedQuery`, parameter values already substituted as literals) and a worker count. It never sees the SQL text and must not depend on which query it is given.

- **The supported set is fixed by GenDB:** every query with `wf_ordered(schema_spec(), q)`: well typed for the schema, with ORDER BY keys that name output columns, over the whole SQLSpec fragment (every query, expression, predicate and aggregate constructor, nested to any depth, correlated subqueries included). The fixed entry decides it with the verified `check_ordered` before your code runs; you cannot narrow it.
- **The training set** (CURRENT FACTS, Training set) is a representative workload of templates on this schema. Their official timings are your feedback. Speed must come from general mechanisms, so that queries outside the training set are fast too.
- You build the engine in **versions**, one round at a time (Rounds and versions). Every accepted version is complete and verified.";

/// ENGINE_GOAL: the three totals against the targets, and the stop rule.
pub const ENGINE_GOAL: &str = "\
# Goal

Make the engine's **total runtime over the training templates** lower than both state-of-the-art engines' at every worker count. For each worker count, the sum over the templates of the engine's official hot median at the timing binding `@TIMING_BINDING@` must be below Umbra's total and below DuckDB's total of the same templates, binding and worker count (CURRENT FACTS, Totals: the target is the faster engine's total).

1. **What a version must be.** Every submission must be complete, exact and verified: it passes admission (Evaluation). Performance never relaxes the proof.
2. **What counts.** The totals, one per worker count, each on its own: a strong total at one worker count does not offset another. Per-template times show where the time goes; they are not separate goals.
3. **The stop.** The run stops at the first accepted version whose official totals are below both baselines' totals at every worker count (margin 1.0; the margin reached is reported). That version is then also timed at the other visible bindings, and those totals are reported (never a stop condition).";

/// ENGINE_FIXED: the entry, the claim, the statuses' meanings, what is owned.
pub const ENGINE_FIXED: &str = "\
# What is fixed and what you own

- **Fixed** (regenerated at freeze): the engine entry `gendb-verus-engine-entry-v1` (`fixed/engine_entry.rs`), its claim and statuses, the AST codec, and every framework file of your crate: `spec/**`, `exec/**`, `bridge/**`, `link/**`, `engine_link/**` (the engine toolkit), `schema.rs`, `gendb_constraints.rs`, `stores/**` (the copied storage interfaces), `gendb_abi.rs`, `gendb_ast_codec.rs`, `gendb_entry.rs` and `gendb_entry/**`.
- **The claim** (`final-claim.json`). For every supported query and every database bound to the stored parts under the declared integrity constraints, the engine's answer is an outcome the SQL meaning allows: allowed rows (any tie order, any tie choice at a LIMIT boundary), the exact SQL error, or `Capacity` only outside `capacity_domain`. Under the trusted assumptions every call terminates with such an outcome: `worker_failure` excludes `WorkerFailed`, which the claim also permits, and `calling_thread_progress` excludes process aborts (out of memory, stack or threads).
- **Statuses the entry decides before your code:** `Refused` (a worker count outside 1..=64), `Malformed` (AST bytes that do not decode), `ParamRefused` (a decoded query that is not well typed). Your `engine` answers every supported query.
- **You own** only `src/agent/**` of the engine crate, plus the author roots of storages you create. The one author-facing signature is `crate::agent::engine` (`obligations.json` `engine`): it receives the stored parts of every storage the engine reads (`Stores`), the query, the worker count and the parallel dispatch, and its ensures must imply `answer_meets(old(stores)@, view_ordered(*q), r)`.
- **You choose** the planner, the physical plans and operators, data representations, parallelism and compiler controls, and every intermediate specification, lemma and proof.
- **Never weaken, assume or bypass the fixed claim.** The source scanner and `--no-cheating` refuse bypasses (`rules.json`).";

/// GENERALITY_RULES: the generality rules and the checks applied.
pub const GENERALITY_RULES: &str = "\
# Generality rules

The engine must be fast through general mechanisms only. **Allowed:** the storage contracts; schema facts (types, NOT NULL, primary and foreign keys); stored statistics and flags a storage builder checks; general physical operators; global cost constants; reuse of admitted code.

**Not allowed, and how it is checked:**
1. **No whole-query dispatch** (review): no decision on a whole query's shape or constants (\"if this is that template, run that code\"), no per-query tuning tables, no rule keyed to literal values, no state kept between calls.
2. **Template constants** (gating, at freeze): your `agent/` files may not contain the text and date constants of the training templates' SQL texts, nor a table of AST fragments with fixed table or column indices (`rules.json`, engine rules).
3. **Not the interpreter** (gating, at freeze and again at admission; `rules.json` `whole_query_evaluator`): your engine is its own planner, operators and general expression path, not the verified reference interpreter.
   - **Refused** in your `agent/` code: the modules `exec::relational::eval` and `exec::relational::entry` (any path, or a `relational::{..}` group naming them); a glob import of `exec::relational` itself (globs of its other submodules, such as `domain`, stay allowed); an alias of `relational`; and these functions by name, whatever path, alias or glob they come through, because each can call the evaluator with a query, condition or expression you pass it: `exec_query`, `exec_pred`, `exec_ordered`, `evaluate`; `exec_expr`, `exec_expr_node`, `exec_expr_if`, `exec_exprs` (`exec::expr`); `exec_filter`, `exec_project`, `exec_left_join`, `exec_left_join_row` (`exec::relational::ops`); `exec_agg_arg`, `exec_agg_args`, `exec_aggregate`, `exec_group_by` (`exec::relational::group`); `check_constraints_exec` (`exec::relational::constraints`). A function of your own with one of these names must be renamed.
   - **Allowed**: every other executable helper, among them the scalar primitives (`exec::{value, numeric, datetime, text, chars, scalar, equality, fns, aggs}`: arithmetic, division, casts, dates, text, LIKE, comparison, aggregate accumulators), `exec::expr::{lit_exec, subquery_value_exec}`, `exec::relational::ops::{exec_table, product_rows_exec, query_arity_exec}`, `exec::relational::aggregate` (aggregate values over computed arguments, such as `exec_agg_value`, `exec_agg_row`), `exec::relational::{order, rows, check}`, `check_constraints_wf_exec`, and the toolkit's class checkers (`pred_total_exec`, `query_info_exec`, ...: they evaluate only closed constant expressions, over an empty database). `rules.json` lists both sets with reasons.
4. **Variants** (gating): frozen rewrites of each template that keep its meaning exactly, of these kinds: @VARIANT_KINDS@. Each must return its template's saved answers. Each variant's time relative to its template is reported to you and to the reviewer, with no threshold; a large ratio is a reason for review.
5. **Planner rules are local patterns** (review): a rule must fire on any query with the same local pattern, over any tables or columns that meet its stated facts. Whole-query shapes are forbidden; fusing a chain such as scan, filter and aggregate is fine. Cost constants are global.
6. **Other bindings** (reported): the stopping version's totals at the other visible bindings show whether its speed depends on the timing binding's selectivities.
7. **State your reasons.** Each submission's `rationale` names which query classes each change speeds up. Each part of a storage you add carries a `data_policy.why` naming its general use, not one query.";

/// ENGINE_STORAGE: seeded storages, budget, one-copy rule, the derived route, the flags pattern.
pub const ENGINE_STORAGE: &str = "\
# Storage: seeded, with a budget

- **Seeded storages.** The engine library starts with admitted, verified storages of every table (`storages.json`: their interfaces, readers, contracts, layouts and measured sizes). Together they store every column of every table once.
- **Uses.** `verus-engine.json` names the storages the engine reads; together they must store every column of every table (`engine_storage_coverage_incomplete`). Their interfaces are copied into your crate as `stores/<name>/interface/**`.
- **Changing storage.** You may add a storage **built from admitted storages** (`built_from`; with `extends` it keeps a source's parts, linked and never rebuilt, and adds parts after them) within the storage budget (CURRENT FACTS, Storage) and the storage policy below. A storage built from source columns is refused (`storage_not_built_from_admitted`). Only the storages the selected engine version reads count against the budget and the single-copy rule: a new storage may re-lay out columns the current version reads when your submission stops reading the storage that holds them now. So the single-copy check of the policy below is made over your submission's storage uses (at evaluation and, under the library's budget lock, at admission); before a build it checks only the storage itself.
- **Data facts as checked flags.** The engine is proved for every bound database, so a fact that holds only for this data (key density, sortedness, clustering) must be a stored flag that the storage builder checks, with its meaning stated in `represents`, guarding a fast path at run time with the general path behind it.
- **What you know about the data** comes from the storages' contracts and descriptions and from the data facts (`data.json`).";

/// How rounds and versions work, in place of the shared attempts section.
pub const ENGINE_ROUNDS: &str = "\
# Rounds and versions

- **This is round @ROUND@.** Each round is one fresh Claude session that ends with one submission. The next round is a new session with this prompt, GenDB's recorded facts and your notes.
- **Versions.** A submission that passes admission becomes the next version (`v1`, `v2`, ...), then is timed officially. Every version is kept whole: code, proofs, admission record, per-template cells, totals, variant results and notes.
- **Your workspace** holds the latest version's sources (`files.engine_crate`, `files.engine_manifest`), your `NOTES.md`, and read-only copies of every earlier version (`files.versions`). Until `v1` exists, a round continues from the previous round's workspace. After a round whose submission was not accepted, the next round starts again from the latest version; that round's workspace stays on disk (CURRENT FACTS, Rounds) and its result is in CURRENT FACTS.
- **Before you submit, write `NOTES.md`** in your workspace (`files.notes`), about one page: your design and why, what you tried and what helped (with measured numbers), untried ideas, and proof difficulties with how you solved them. GenDB's facts are authoritative; the notes are hints for the next round. Keep it current; replace stale content.
- If a call is interrupted before it submits, the retry continues the same session.";

/// ENGINE_HOW_TO_WORK: complete verified versions, measure first, planner plus operators, H1-H5 and the toolkit.
pub const ENGINE_HOW_TO_WORK: &str = "\
# How to work

**Keep every version complete and verified.** A version answers every supported query: every AST constructor has a verified general path, even a slow one, and fast paths sit in front of it. A round that cannot finish a large change can still submit the complete engine it has.

**Measure first, prove later.** Proofs are the most expensive part, so do not spend them on designs that may be too slow.
- `trial` with `verification: \"not_run\"` times an unverified build over the whole training matrix (every template x worker count), or your own SQL statements; compare alternatives where it is cheap.
- Then prove the design you chose once, iterating with module-scoped checks.

**Planner plus operators.** A structure that suits a verified engine: a planner that turns the AST into a physical plan by local rules, each rule justified by one generic equivalence lemma with its side conditions; physical operators, each proved to refine its plan node's meaning; scans proved against each storage's `represents`. Heuristic choices (access path, join order and algorithm) need no proof; only the rewrites do.

**Semantic side conditions.** SQLSpec's exact meaning decides which rewrites are sound:
- **H1, strict evaluation and the first error.** AND and OR evaluate both sides; Filter and Project report the first error in canonical row order. A plan that skips rows or evaluates an expression on other rows needs the expression total there (it never errs and stays in the machine domain); a plan that only reorders rows needs its possible errors uniform or total.
- **H2, representatives.** GROUP BY and DISTINCT keep the first member's key; MIN, MAX and DISTINCT aggregates pick among SQL-equal values; equal numerics of different display scales are different outputs. Order independence needs scale-exact keys and arguments.
- **H3, capacity.** A plan may not need a machine intermediate wider than the canonical evaluation's.
- **H4, correlation.** A subquery sees the outer row; evaluating it once needs context independence, and decorrelation needs equality-correlation lemmas with column-shift bookkeeping.
- **H5, row order.** Order is observable only through H1, H2 and the top-level LIMIT; `ordered_ok` allows any tie order.

**The engine toolkit** (`engine_link/**` in your crate) holds generic lemmas for these conditions; `files.toolkit` indexes each of its modules with its header and items. Use them or write your own.

**Orient yourself first.** `files.engine_map` lists every module of your current crate with its header and items; a fresh round reads it before the sources.

@PROOF_ADVICE@

@REUSE_ADVICE@

@PARALLEL_ADVICE@

@CHECK_ECONOMY@";

/// The engine's evaluation: admission, official timing, variants, failures.
pub const ENGINE_EVALUATION: &str = "\
# Evaluation

- **Admission** decides acceptance. The frozen crate (framework files plus your `src/agent`) must verify whole with `--no-cheating` against the fixed engine entry with 0 errors; pass the source rules (the central scan, no `static` items, the engine rules); compose with every storage it reads; store every column of every table through them; and keep the storage policy and budget. Then every training template is called once at every visible binding (64 workers) and compared with the saved answers of other engines (`validation.json`), and the AST echo is checked; every timed variant (64 workers, 1 warm + 1 hot call) must return its template's saved answers. A submission that passes is admitted and becomes the next version, however fast it is.
- **Official timing** of the admitted version, which records and never gates: every template at the timing binding `@TIMING_BINDING@` and every configured worker count, one fresh child per cell under the host's timing lease: 1 warm + 3 hot calls, the cell's time is the median hot call. Planning happens inside the call, so it is timed; translating and encoding the SQL is not. The totals per worker count are the sums of the template medians. A cell that fails (its child fails or exceeds its bound, or its answer is not allowed) is recorded as failed; that worker count then has no total, so the stop cannot hold, and the version stays admitted.
- **Variant ratios** (report only): each timed variant's hot call as a ratio to its template's official median at 64 workers.
- **Failures.** A submission that fails admission is recorded as that round's attempt and never becomes a version. A submission whose evaluation failed **in the framework** (CURRENT FACTS says so) is not counted and is evaluated again.
- **Guards.** The user's rounds and cost guards are ceilings, not quotas (\"unset\" means none). There is no model-turn cap.";

/// Inputs and conduct, engine role.
pub const ENGINE_INPUTS: &str = "\
# Inputs and conduct

- **Read `files.author_contract` first.** It maps every input: the task and the fixed claim; the training templates with their SQL, parameters, visible bindings and saved baseline times (`files.templates`); the versions so far; the storages with their interfaces, readers, contracts and sizes; the stored-parts read API; the schema and the declared integrity constraints; the data facts; the engine toolkit index and the proof library; parallelism; the registry of fixed definitions and the source rules; the toolchain, the tools with their result fields, failure classes and accounting; the timing protocol.
- **Look items up before reading framework files.** Use `index.json` `commands.api_lookup`, `files.toolkit`, `files.engine_map`, grep inside your crate, and the vstd sources. Read the regions you need, not whole toolkit files.
- **Your inputs:** your workspace (the engine crate, its framework files, the read-only earlier versions, the admitted code under `admitted-code/`), the files `files.author_contract` maps and the prepared data they name; the pinned toolchain including the vstd sources; standard system tools and hardware diagnostics.
- **Reusable implementations** are exactly the admitted catalogs: the search index (`files.search_index`) and `storages.json`. The index and `admitted-code/` also hold the admitted code of the read-only reuse libraries the run offers (entries whose `origin.reuse_library` is set, module lines marked `reuse`): earlier admitted per-query programs, their general modules and their storages' code, for reading and adapting only; that code is not admitted in your library, never served and never counted in your budget, and copied code passes your rules like any other (a per-query program may spell its query's constants). The SQLSpec library, the proof helpers and the engine toolkit in your crate are always available.
- **Not inputs:** other GenDB runs, old outputs, other libraries, scratch directories, tests, fixtures, repository source or history, host or controller source, and any statement or binding file the framework does not give you. Do not read, list or search them; every tool call is recorded and audited.
- **Do not** alter ledger, library, reference or authority files; hash or fingerprint whole datasets; launch inference or agents.
- **Readability.** Write readable code, specifications and proofs: meaningful names, one purpose per function, units (rows, bytes, days, scales), a short header per module (`//!`, its first sentence becomes the module's line in `ENGINE_MAP.md`), and proof steps explained where they are not obvious. Versions are published and read by people and by later rounds.";

/// Tools, engine role.
pub const ENGINE_TOOLS: &str = "\
# Tools

- **Typed `gendb_local` tools** (`tools.json`):
  - engine tools over a `verus-engine.json`: `check`, `verify`, `compile`, `trial`, `profile`;
  - storage tools: `storage_check`, `storage_verify`, `storage_compile`, `storage_build`, `storage_register`;
  - `catalog`: re-read the library (admitted storages and the storage budget);
  - you may also run the pinned Verus toolchain directly (`toolchain.json`).
  Use them as often as useful. Local runs are diagnostics; only the framework's evaluation of a submission is official.
- **`trial`** times the training matrix by default: every template at the timing binding x every configured worker count (`templates`, `binding` or `workers` narrow it), 1 warm + 1 hot call per cell by default (`hot_calls` asks for more), each answer compared with the saved answers, and reports per cell your median, the faster baseline's time and the ratio, plus the totals per worker count when every template ran. With `sql` it runs your own statements instead (each translated by the frontend and encoded like the templates; no saved answer, so only the status and rows are reported). Trials hold the host's timing lease, so two timings never overlap.
- **`profile`**: one cell (`workers`, and one template or one `sql` statement), 1 warm + 1 measured call, with per-call dispatch ranges, process CPU and calling-thread CPU.
- **Unverified runs.** `trial` and `profile` accept `verification: \"not_run\"`: the frozen crate is compiled with `rust_verify --no-verify` (no proof obligation checked; source rules and `--no-cheating` unchanged) and run on the real data with the same comparisons. `storage_build` accepts the same for an unverified storage build. Every such result is labelled `diagnostic_unverified`; it never counts as a submission, proof, admission or official measurement. Instrumentation inside the crate (clock reads, logging) needs `external_body`, which every GenDB job refuses; keep it in your own scratch builds.
- **Caching.** A proof check or compile of identical crate content is reused, never rerun; results say `reused`.
- **`catalog`** re-reads the library now: other sessions may admit storages meanwhile. It is a snapshot, not a reservation: registration enforces the budget.";
