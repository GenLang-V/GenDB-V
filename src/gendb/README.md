# src/gendb

The GenDB-V system, one Cargo workspace. This file is for developers: the source map, the build and the tests. The user guide is [`GUIDE.md`](../../GUIDE.md).

## Crates

| Folder | Crate | Start reading at |
|---|---|---|
| `frontend/` | `gendb-frontend` | `src/lib.rs`; Python parser `parser/gendb_sql_frontend/`; AST schema `ast/ast_schema.json`; `src/engine_encode.rs` (a statement at one binding as the AST bytes of an engine call) |
| `sqlspec/` | `gendb-sqlspec` | `library.rs` (Verus library root), `semantics/`, `proofs/link/`; host side `src/lib.rs`; `engine_link/` (the verified toolkit an engine author's planner and operators use, with checked examples) |
| `registry/` | `gendb-registry` | `src/lib.rs` (definition index); `verus/stored.rs` (stored-parts read handle) |
| `artifacts/` | `gendb-artifacts` | `src/lib.rs`, `src/object_store.rs`, `src/asset_directory.rs`, `src/verus/` (records) |
| `storage/` | `gendb-storage` | `src/import.rs` (trusted Parquet import), `src/io.rs`, `src/versions.rs` |
| `runtime/` | `gendb-runtime` | `src/lib.rs`, `src/serve.rs` (`serve/engine.rs`: serving from an admitted engine version), `src/worker.rs` (per-call limits `worker/watchdog.rs`, profile sampling `worker/sampler.rs`), `src/process_stop.rs`; Verus shims `verus/` (engine: `engine_shim.rs`, `engine_codec.rs`), `verus/shim_v4/` |
| `verification/` | `gendb-verification` | `src/obligations.rs` and fixed entries in `obligations/` (`storage_entry.rs`, `query_entry.rs`; with declared integrity constraints `query_entry_v5.rs` and the opt-in `storage_entry_v2.rs`); `src/admission.rs` (`admission/integrity_constraints.rs`, tiny cases `admission/cases/`, the request's validation policy and saved-answer agreement `admission/validation.rs`); `src/obligations/claim.rs` (trusted assumptions, author obligations); engine crates: the fixed entry `obligations/engine_entry.rs`, `src/obligations/engine_crate.rs`, version 0 `src/obligations/interpreter_engine.rs`, admission `src/admission/engine.rs`, the engine source rules `src/verus/refusal/engine_rules.rs` |
| `synthesis/` | `gendb-synthesis` | `src/controller/workload_run.rs` (one workload run), `src/controller/request.rs` (request format 2, its `engine` section), `src/workload/`, `src/query/`, `src/storage/` (storage families `storage/family.rs`), `src/tools.rs`; the engine target `src/engine.rs` (schema line `engine/rounds.rs`, general line `engine/branches.rs`, runs of several workloads `engine/stage.rs`) |
| `cli/` | `gendb` (binary) | `src/main.rs` |

Dependency order (each depends only on crates to its left): `frontend`, `registry`, `artifacts` → `sqlspec` (frontend), `storage` (artifacts, frontend) → `runtime` → `verification` → `synthesis` → `cli`. Trusted code is named in each crate's `lib.rs` header and in `verification/src/obligations/claim.rs`; folder names do not mark trust.

## Build and run

```sh
cargo build --release -p gendb    # run from src/gendb
./target/release/gendb --help
```

The [guide](../../GUIDE.md) shows the user commands: `gendb run FOLDER` and the folder forms of `serve`, `evaluate`, `import` and `serve-engine`. The request-level commands:

- `gendb synthesize|preflight|serve REQUEST.json RUN_DIR` runs the controller; with the request's optional `output_home` it also writes the readable output folders as sessions close.
- `gendb prepare-flat-storage REQUEST.json RUN_DIR` prepares, once, the fixed plain-array (flat) storages of a request with `storage_policy` `fixed_flat`.
- `gendb benchmark-inputs` adds visible bindings and targets to a request; `gendb evaluate REQUEST.json BINDINGS.json HOME` times the admitted packages at named bindings.
- `gendb import REQUEST.json PUBLISHED_DIR RUN_DIR` admits a published run's packages without an agent ([guide](../../GUIDE.md#run-our-published-packages)).
- `gendb output ...` and `gendb rebuild QUERY` write and reassemble the readable output home (`synthesis/src/output.rs`); `gendb sql --help` lists the SQLSpec reference workflow.

The request format is documented on `WorkloadRequest` in `synthesis/src/controller/request.rs`, with its optional `integrity_constraints` (declared keys, foreign keys and named CHECKs, trusted as the user's declaration; the `ALTER TABLE` lines of `benchmarks/tpc-h/schema.sql` are the TPC-H list). Verus comes from `GENDB_VERUS_HOME` (default `<repository>/toolchains`, pinned in `verification/verus/toolchain.json`); the SQL parser interpreter is pinned in `frontend/parser/toolchain.json`.

## Tests

Tests are per crate. Tests that need the pinned Verus, the Python frontend or the `gendb` worker are `#[ignore]`d and run with `-- --ignored`. The public-controller fixture also needs `GENDB_WORKER=<path to gendb>`, built from the same source and build profile as the test (a debug `cargo test` needs `target/debug/gendb`), and a short `TMPDIR` path (long paths exceed the Unix socket path limit).

## The general engine

`gendb engine synthesize|prepare REQUEST.json RUN_DIR` runs the engine target: one verified engine for every well-typed query of a schema, its statements given at call time as AST bytes. The general line (`engine.line: "general"`) starts from version 0 (the verified SQLSpec interpreter over the plain storage) and accepts a version only when it beats its parent; a run may continue from an accepted version of another run (`engine.seed_version`), or serve several workloads with one engine (`engine.stage`, `engine.workloads`). `gendb engine check-request`, `export`, `final-evaluation`, `re-evaluate`, `operator-note` and `operator-resume`, `gendb serve-engine` and `gendb seed-engine-library` are listed in `gendb help`. The user side of a run over several workloads (`mode = "engine"`, `[[members]]`, `start_from`) is in the [guide](../../GUIDE.md#engine-mode); [`benchmarks/anyschema/`](../../benchmarks/anyschema/README.md) is its check workload and a template for a new schema.

**Runs of several workloads.** One engine crate is shared by every workload (schema, data and query templates): for each workload GenDB composes and verifies one crate, and a version is accepted only when it is faster in total on the workloads it is tuned for.

### Concepts

- **Workload.** One schema with its data, its training templates (SQL with typed `$n` parameters), their visible bindings and the saved answers of another engine at each binding; for a timed workload also saved baselines (`targets.json`: DuckDB and Umbra times per cell). A workload is one folder ([guide](../../GUIDE.md#your-own-workload)); `gendb run` writes from it one complete general-line request (`WorkloadRequest` with `engine.line: "general"`, `synthesis/src/controller/request.rs`), with its own library.
- **Role** (`controller::request::MemberRole`):
  - `counted`: timed against the parent on every submission; its score is part of the combined score that decides.
  - `check`: verified whole and every template answered at every visible binding by every submission, before any timing; a wrong answer or a failed proof refuses the submission. Never timed, not in the score, no storage budget, no baselines needed. This is the **generality check**: shared code that depends on another workload's schema does not compile, verify or answer here.
  - `kept`: timed and shown for every accepted version, never deciding.
- **The primary workload** is the run's own request; the other workloads are `engine.workloads.members`. The primary is always counted.
- **One engine, one crate per workload.** The author owns `src/agent/**` (the engine, shared) and, per workload, a module copied into that workload's crate as `src/agent/workload/**`: the shared **default module** `<crate_dir>/workloads/default/**`, or a workload's own `<crate_dir>/workloads/<name>/**` (allowed only beside an inherited storage, rule R5). GenDB generates every framework file of a crate for its workload's schema, storages and declared integrity constraints (`engine::submission::freeze_member_crate`, `engine::submission::members`).
- **Storage families.** New storage is written once as a family under `storages/<family>/` (`verus-family.json`, a builder `<crate_dir>/src/builder/**`, an interface `<crate_dir>/src/stores/<family>/interface/**`, `default_plan.rs`; `storage::family`). For each workload that reads it, GenDB composes an instance over that workload's whole schema (`storage::family::compose_instance`): every table and column, built from the workload's plain flat storages, its parts expanded from the family's part template (`storage::family::expand_parts`), and two generated files checked by Verus, `schema_exec.rs` and `whole_schema.rs` (`verification/src/obligations/whole_schema.rs`), so the builder and the opening are written by table id for any schema. The instance's `crate::sources_flat` (its flat sources by table and column id) always carries the nullable items (`nullable_column(t, c)` false over a schema without nullable columns), so one builder text compiles in every instance. An instance is then an ordinary storage: verified, built in the workload's library, checked against the storage policy and the budget, admitted.
- **Plans.** A workload tunes a family only through `<crate_dir>/plans/<workload>/<family>.rs` (else the family's `default_plan.rs`): data only (rule R4), checked by the builder at run time and never read by the engine. A new schema needs no code, only an optional plan.
- **Inherited storages.** A seed's workload-specific storages (for example a per-table encoding written for one benchmark) stay usable, opened by that workload's own module, until a family replaces them. A version is **one engine** when no workload has its own module or an inherited storage (`version.json` `general.one_engine`). With `engine.workloads.require_one_engine` (below) only versions that are one engine are accepted.
- **The root and its sides.** The run's root `v000` has one side per workload: a workload with a seed gets that seed's code, module and storages (`engine::submission::members::write_side_root` from an accepted version, `write_source_root` from an exported engine), verified whole and timed alone (a check workload: answered) when the run is prepared; a workload without a seed gets the primary seed's code where it verifies there, else GenDB's version 0 (the verified SQLSpec interpreter over the plain storage). The first submission is judged on each workload against its side.
- **The combined score.** Per counted workload, F = its finished cells and G = the sum over the worker counts of the engine's total over the faster baseline's total (an unfinished cell counts the call limit). The combined F and G are the sums over the counted workloads; better means a larger F, or the same F and a smaller G. There is no guard per workload: a loss on one workload that a larger gain on another outweighs is accepted, and every race is shown.

### The rules (checked at freeze and again at admission)

`gendb_verification::verus::engine_rules` (`MEMBER_ENGINE_RULES`; the general line's rules plus):

| Id | Rule | Kind |
|---|---|---|
| `schema_name` (stage form) | engine code names no table or column of any workload's schema (a one-word column name only refused inside a literal) | gating |
| `template_constant` | no text or date constant of any workload's templates in `agent/` files | gating |
| `workload_module_statement` | a workload module (the default module included) names no statement type or AST path | gating |
| `storage_family_required` (R3) | every storage a submission adds is a family use; inherited admitted packages stay allowed | gating |
| `plan_is_data` (R4) | a plan is one `pub fn plan()` whose body is data (no call, operator, `if`, `match`, loop, text literal) | gating |
| `workload_module_scope` (R5) | an own module only beside an inherited storage that is neither a family instance nor a plain flat storage | gating |
| check workloads (R6) | every check workload verifies whole and answers every template at every visible binding | gating |
| `workload_module_report` | each workload's module size, inherited storages and plans, per version | reported |

R3 and R5 are structural (where a file sits, where a storage comes from), so they cannot misfire on a technique; the check workloads are the semantic check of generality.

### The request

A run is the primary workload's general-line request with one more field (`controller::request::EngineWorkloads`). `gendb run` writes it from the folders (`WORK/requests/engine.json` and `WORK/requests/members/`):

```json
"engine": {
  "line": "general",
  "workloads": {
    "name": "tpch",
    "seed": {"run": "/runs/earlier/run", "version": "v004"},
    "members": [
      {"name": "sec", "role": "counted", "request": "sec.json", "seed": {"run": "/runs/other/run", "version": "v001", "workload": "sec"}},
      {"name": "anyschema", "role": "check", "request": "anyschema.json"}
    ]
  }
}
```

- A **seed** is an accepted version of another general-line run (`{"run", "version"}`, with `"workload"` for a version of several workloads) or an engine folder written by `gendb engine export` (`{"source": "<folder>"}`). A member without a seed starts from the primary seed's code where it verifies, else version 0.
- A **member request** is a complete general-line request (`WorkloadRequest::validate_member`): dataset, templates, scales, library (its own: libraries are distinct), saved answers; no `output_home`; its limits are not used. A check member's scales may omit `targets`.
- The fields every workload shares must be equal: `hardware.threads`, `barriers`, `author_executable` and `engine.{call_limit_seconds, anon_memory_limit_bytes, branches}`.
- Names follow `EngineStage::NAME_RULE`; `default` is reserved (`RESERVED_WORKLOAD_NAME`, the default module's directory). `engine.workloads` excludes `engine.stage` and `engine.seed_version`; `WorkloadRequest::workload_set` maps all three forms onto one `WorkloadSet`.
- A run of several workloads has one branch (`engine.branches: 1`; more is refused by name at preparation).
- **Only one engine** (optional): `"require_one_engine": true` in `engine.workloads` accepts only versions that are one engine (`engine::stage::one_engine`). A submission that is not one engine is refused right after its freeze, before any build or timing (`not_one_engine`, naming its own modules and inherited storages). While the head is not one engine, the first one-engine submission is accepted when it is correct (every crate verified whole, its storages built, every check workload's answers and every counted cell finished with agreeing answers) even if its combined score is worse (`one_engine_transition` in the evaluation's `combined.json`, the version's `version.json` and the main line, with the races for reporting); from then on the combined score decides as usual. The prompt states the rule. A relaunch of a run may set the field (never unset it): GenDB records `<run>/request-change.json`, like a budget raise (`<run>/budget-raise.json`). Absent, nothing changes.
- Each workload's library must hold its seed's storage packages admitted (seed it by hard links with `gendb seed-engine-library`) and the flat packages its request's `engine.storage_seed` lists; a run's library starts without engine versions. `gendb engine check-request` checks all of this before `gendb engine prepare`.

### What `gendb run` does

Each step is skipped when its record exists:

```text
1. per workload and scale: the data (setup_data.sh when missing) and its Parquet check
2. the baselines (DuckDB) at every scale: every template at the timing binding x threads; the saved answers at every
   binding (a check member: the answers only)
3. per workload and scale: gendb prepare-flat-storage   the capture and the plain flat storage of every table
   then the run request and one request per member (WORK/requests/)
4. with start_from RUN:VERSION: gendb seed-engine-library from the seed run's library
5. gendb engine check-request                         every member at every scale: inputs, libraries, assets, seeds
                                                       (no data, engine or timing); problems stop the run here
   gendb engine prepare                               the root v000: one side per workload
   gendb engine synthesize                            the author loop under the budget
```

Then, with the run's request and run folder (`WORK/requests/engine.json`, `WORK/steps/engine`):

```text
gendb engine final-evaluation RUN.json RUN_DIR VERSION [SCALE [WORKLOAD]]   the full protocol of one version
gendb engine export RUN_DIR VERSION OUT               the engine source: agent/**, workloads/default/**, the families,
                                                       plans/**, a manifest and a README with every workload's proof and
                                                       admission digests
```

### What is proved, recorded, tested and trusted

- **Proved.** For each workload and each accepted version, that workload's engine crate and its family instances are verified whole with `--no-cheating` against the fixed entry `gendb-verus-engine-entry-v1` and the derived storage entry, over that workload's schema, storages and declared constraints: for every supported query (`wf_ordered` over the schema) and every database bound to the stored parts, the answer is an outcome the SQL meaning allows. The claim is per schema.
- **Recorded, not proved.** "One engine": the shared sources (`agent/**`, `workloads/default/**`, the families) are the same bytes in every crate (`engine::submission::members::shared_sources_digest`, `version.json` `general.shared_digest`).
- **Tested.** Agreement with the saved answers at every timed or checked call; every check workload on every submission.
- **Trusted.** No addition in proofs. The composition, the part-template expansion, the rules R3 to R5 and the records are host code that decides refusals and writes records; every generated file is checked by Verus in its crate.

## Outputs

Generated runs go to a run directory and an output home (`results/` holds the published ones); admitted packages and stored assets go to a library root.
