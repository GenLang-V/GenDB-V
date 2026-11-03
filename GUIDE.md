# GenDB-V guide

Install GenDB-V, run a first query, then run your own workload or our published packages. Run every command from the repository root.

## Install

Tested on Linux. You need these tools:

| Tool | Version | For |
|---|---|---|
| Rust with Cargo and rustup, and a C compiler | Rust 1.88 or newer | building `gendb` |
| Verus, its Rust toolchain, Z3 | Verus `0.2026.09.13.671956e`, Rust `1.98.1`, Z3 `4.16.0` | checking proofs |
| Python | 3.12, with `sqlglot` 27.0.0, `pyarrow` and `duckdb` 1.5.6 | the SQL parser, the data scripts and the DuckDB baselines |
| Claude Code | 2.1.280, 2.1.283 or 2.1.286, signed in | the agent (only `gendb run`) |

**1. Install the proof tools.** GenDB-V looks for them in `toolchains/` at the repository root. To use another folder, set `GENDB_VERUS_HOME`.

```sh
H=$PWD/toolchains
mkdir -p $H/verus/0.2026.09.13.671956e $H/z3/4.16.0-manylinux_2_27 $H/downloads
curl -L -o $H/downloads/verus.zip https://github.com/verus-lang/verus/releases/download/release/0.2026.09.13.671956e/verus-0.2026.09.13.671956e-x86-linux.zip
unzip $H/downloads/verus.zip -d $H/verus/0.2026.09.13.671956e
RUSTUP_HOME=$H/rustup CARGO_HOME=$H/cargo rustup toolchain install 1.98.1 --profile minimal --component rustfmt,rustc-dev,llvm-tools
curl -L -o $H/downloads/z3.whl https://github.com/Z3Prover/z3/releases/download/z3-4.16.0/z3_solver-4.16.0.0-py3-none-manylinux_2_27_x86_64.whl
unzip $H/downloads/z3.whl -d $H/z3/4.16.0-manylinux_2_27
chmod +x $H/z3/4.16.0-manylinux_2_27/z3_solver-4.16.0.0.data/data/bin/z3
```

**2. Install the Python packages.** GenDB-V runs `python3` from your `PATH`. To use another interpreter, set `GENDB_SQL_FRONTEND_PYTHON`.

```sh
python3 -m pip install sqlglot==27.0.0 pyarrow duckdb==1.5.6
```

**3. Build `gendb`.** Build it in place: the binary finds the SQL parser and `toolchains/` in this tree.

```sh
cd src/gendb && cargo build --release -p gendb && cd ../..
export PATH=$PWD/src/gendb/target/release:$PATH
gendb --help
```

**4. Check a published proof (free).** Verus checks the whole crate again. Any crate under `results/**/crates/` works.

```sh
GENDB_VERUS_HOME=$PWD/toolchains scripts/verus-check.sh results/example-readings-count/crates/example-readings-count
```

## First run

The workload [`readings-count`](benchmarks/readings-count/README.md) has one table with 4 rows: 5, 5, 9 and 0. Its template is `SELECT COUNT(*) AS n FROM readings WHERE value > $1`.

```sh
gendb run benchmarks/readings-count --until preflight   # free: the data, the verified storage, the proof obligation
gendb run benchmarks/readings-count                     # the agent writes and proves the query (paid)
gendb serve benchmarks/readings-count                   # run the verified query at $1 = 4
```

The last step prints a JSON record. Its answer is `{"rows": [[3]], "status": "ok"}`. For another value, run `gendb serve benchmarks/readings-count --query readings-count --args 9` (the answer is `[[0]]`).

Only `gendb run` calls Claude Code and costs money: one call, \$2.35, in our run. It runs the `claude` on your `PATH`. To use another, write `author = "PATH"` in `~/.gendb/config.toml` (or `$GENDB_HOME/config.toml`).

## Your own workload

A workload is one folder: a schema, one SQL file per query, the data, and optional bindings and settings. `gendb run FOLDER` reads it, prepares the data, measures DuckDB, lets the agent write and prove the code, and writes the results. The folders in [`benchmarks/`](benchmarks/) are workloads.

### The folder

```text
<folder>/
  schema.sql            the tables, column types, NOT NULL, keys and named CHECKs
  queries/<name>.sql    one SQL statement per file; its parameters $1, $2, ... declared in header lines
  data/<scale>/         <table>.parquet (or <table>/*.parquet), and optionally MANIFEST.json
  setup_data.sh         optional: `setup_data.sh SCALE` writes data/SCALE/ (gendb run calls it when data is missing)
  bindings.json         optional: example parameter values; bindings/<scale>.json wins for its scale
  gendb.toml            optional: settings (below); each has a default
  runs/                 written by GenDB: one folder per run
```

A query's name is its file stem (`Q01.sql` is `Q01`).

### The schema

```sql
CREATE TABLE readings (
    value bigint NOT NULL
);
ALTER TABLE readings ADD CONSTRAINT value_nonnegative CHECK (value >= 0);
```

- Types: `integer` (also `int`, `int4`), `bigint` (`int8`), `numeric(p,s)` or `decimal(p,s)` with p ≤ 38, `date`, `text`, `boolean`. A column is nullable unless it says `NOT NULL`. `varchar(n)`, `char(n)`, a `numeric` without `(p,s)` and `DEFAULT` are refused, with the fix.
- Keys and checks: `PRIMARY KEY (...)`, `UNIQUE (...)`, `FOREIGN KEY (...) REFERENCES t (...)` and `CONSTRAINT name CHECK (...)`, either in `CREATE TABLE` or as `ALTER TABLE t ADD ...` after all tables. Declare a key before the foreign keys that reference it. The proof may assume them. GenDB never checks them on your data.
- The table order is the tables' identity: keep it when you rerun.
- Each Parquet file must have exactly the declared columns, types and nullability (Arrow `int32`, `int64`, `decimal128(p,s)`, `date32`, `string`, `bool`); `gendb run` checks this first and lists every difference.

### A query file

```sql
-- $1 date date
-- $2 discount numeric(15,2)
-- $3 quantity integer min 1 max 50
SELECT SUM(l_extendedprice * l_discount) AS revenue
FROM lineitem
WHERE l_shipdate >= $1 AND l_discount BETWEEN $2 - 0.01 AND $2 + 0.01 AND l_quantity < $3;
```

- Each header line is `-- $<n> <name> <type>`, with the types `integer`, `bigint`, `numeric(p,s)`, `date` and `text`. Every `$n` of the statement needs one; GenDB does not guess types.
- A parameter is free over its whole type: the proof covers every value. Add `min <v>` and `max <v>` to narrow it to what you need (the agent may then use the bound), or `= <v>` to fix it. Serving refuses an argument outside the domain by name. A `text` parameter has no bounds.
- The statement is the rest of the file. A file without header lines is one concrete statement.

### Bindings

```json
{"queries": {"Q06": [{"binding_id": "v0", "arguments": ["1994-01-01", "0.06", "24"]}]}}
```

The argument texts are in parameter order (dates `YYYY-MM-DD`, decimals as text). GenDB runs every submission on the data at these bindings and compares the answer with DuckDB's. With `goal = "fast"` (the default) every query with parameters needs bindings, and GenDB times them. With `goal = "correct"` they are optional: the proof is the check.

### Settings (`gendb.toml`)

| Setting | Default | Meaning |
|---|---|---|
| `name` | the folder name (lowercase, other characters `_`) | the workload's name in an engine run |
| `mode` | `"templates"` | `templates`: one verified package per query; `engine`: one verified engine for every query (both below) |
| `goal` | `"fast"` | `fast`: time each submission against the baselines and keep the fastest verified one; `correct`: admit the first verified one |
| `storage` | `"designed"` | `designed`: an agent designs one storage for all queries; `plain`: GenDB's plain arrays, one per column |
| `scale` / `scales` | the folder's one `data/` scale / all of them | which `data/<scale>/` to run (engine mode: smallest first) |
| `queries` | every file | the queries to run, in this order |
| `threads` | `[1]` | the worker counts each query is verified, tested and timed at |
| `compare_with` | `"duckdb"` | `"duckdb"`: DuckDB's times are the targets and its answers the saved answers ([DuckDB baselines](src/gendb/baselines/README.md): DuckDB 1.5.6 with PostgreSQL's meaning); `"none"`: no other engine |
| `speedup` | `5` | with targets: stop a query's session once it is this many times faster than the target |
| `max_submissions` | `3` | submissions per agent session |
| `session_budget_usd` | none | a dollar limit per agent session |
| `budget_usd` | none (required in engine mode) | the dollar limit of an engine run |
| `storage_budget_bytes` | the data size | the most bytes a designed storage may hold; the default is `original_data_bytes` of `data/<scale>/MANIFEST.json`, else the Parquet files' uncompressed size |
| `numeric_tolerance` | `"1e-9"` | relative tolerance when decimals are compared with saved answers |
| `parallel_queries` / `parallel_preparations` | `5` / `1` | query sessions / storage preparations at a time |
| `model` | Opus 5.5 | the agent's model |
| `baselines` | none | a saved baselines folder (its `baselines.json`), used instead of measuring DuckDB |
| `capture` | the run's own | the prepared data of another run, to reuse it |
| `start_from` | none | engine: an accepted version (`RUN:VERSION`) or an exported engine folder; templates: an earlier run folder to continue |
| `[[members]]` | none | engine: the other workloads of the run (`folder`, `role` `counted` or `check`, `start_from`) |
| `timing_binding` | `"v0"` | engine: the binding the engine is timed at |
| `branches` | `1` | engine: the lines of versions the agents search at once (one when the run has members) |
| `call_limit_seconds` | `60` | engine: the time limit of one engine call |
| `memory_limit_bytes` | the host's memory | engine: the memory limit of one engine call |
| `emphasis` | none | engine: `"co_optimization"`: the agent designs the storage and the operators together from the first version |
| `one_engine` | `false` | engine: accept only versions in which every workload runs the same code |
| `reuse` | none | engine: libraries whose admitted code the agent may read and reuse |

The command line wins over `gendb.toml`: `--config FILE`, then `--mode`, `--storage`, `--scale`, `--threads 1,8`, `--queries Q01,Q06`. A path in a settings file (`[[members]] folder`, `baselines`, `capture`, `start_from`, `reuse`) is relative to that file's folder.

### Template mode

With `mode = "templates"` (the default), GenDB synthesizes one verified package for each query file. A package answers its query for every parameter value in the declared domain.

1. **Storage.** With `storage = "designed"` (the default), an agent first designs one storage that all queries share, and a verified builder writes it. With `plain`, GenDB uses plain arrays, one per column.
2. **Queries.** Then GenDB starts one agent session per query, up to `parallel_queries` at a time. In each submission the agent writes the code and its proof. GenDB checks the proof with Verus, tests the answers at the bindings, and times the code.
3. **Result.** GenDB admits the fastest verified submission (with `goal = "correct"`, the first one). `gendb serve FOLDER` runs the admitted packages.

### Engine mode

With `mode = "engine"`, GenDB synthesizes one verified engine that answers every supported query over the schema. The engine gets each statement when it is called. The first version is version 0: the verified SQLSpec interpreter over plain arrays. The agent then writes new versions. A version is accepted only when it is faster in total on the workloads it is tuned for.

One engine can serve several workloads. The `gendb.toml` of the primary workload names the others:

```toml
name = "tpch"
mode = "engine"
budget_usd = "1000"
start_from = "RUN:v004"            # optional: an accepted version of another run, or an exported engine folder

[[members]]
folder = "../sec-edgar"
role = "counted"

[[members]]
folder = "../anyschema"
role = "check"
```

- **`counted`**: GenDB times the engine on this workload, and the times count when GenDB accepts a version.
- **`check`**: every version must verify on this workload and answer every query at every binding. GenDB never times it. Code that depends on the schema of another workload fails here. [`anyschema`](benchmarks/anyschema/README.md) is such a workload.

**A new schema.** Write its folder with `mode = "engine"`, and set `start_from` to an exported engine folder (`gendb engine export`, below). `gendb run` then shows whether the engine verifies and answers on that schema. You write no code. Use `anyschema` as a template for the folder.

## Run our published packages

`gendb import FOLDER PUBLISHED_DIR --out W` admits the packages of a published run folder (`results/<workload>/<run>/`) into your library, over the data of the workload folder at any scale. No agent is called. GenDB takes only the author files of each published crate (a query's `agent/`, a storage's interface and builder) and generates every fixed file again. Verus checks each crate whole, each storage is built from your data, and each query is evaluated and admitted like any submission. A package that does not verify under your GenDB is refused, with the reason. A rerun resumes. Then `gendb serve` and `gendb evaluate`, with the same `--out W`, run the packages.

TPC-H at scale factor 1:

```sh
bash benchmarks/tpc-h/setup_data.sh sf1                  # the data: benchmarks/tpc-h/data/sf1/<table>.parquet
W=$HOME/tpch-sf1                                          # a new folder: every step writes only here
gendb import benchmarks/tpc-h results/tpch-sf100/gendb-v-agent-designed-storage --out $W
gendb serve benchmarks/tpc-h --out $W                     # every query at every binding of bindings/sf1.json
```

- The plain-array run (`results/<workload>/gendb-v-plain-array-storage`) imports the same way; GenDB prepares its plain storage first.
- SEC-EDGAR: `benchmarks/sec-edgar` (its data: `benchmarks/sec-edgar/setup_data.sh`) and `results/sec-edgar-sf3/<run>`.
- The example: `gendb import benchmarks/readings-count results/example-readings-count --out $W`, then `gendb serve benchmarks/readings-count --out $W` (answer `[[3]]`).

Each published crate's `compile.json` holds the compiler options of its admitted build (`opt_level`, `target_cpu`); the import compiles the crate with them. A crate without the file compiles at opt-level 3 for rustc's default CPU.

## Commands

| Command | What it does |
|---|---|
| `gendb run FOLDER --until preflight` | Every free step: the data check, the storage, DuckDB, and the check of every query's proof obligation with Verus. It writes the first query's agent prompt (`steps/render/rendered/prompt.md`). |
| `gendb run FOLDER` | The whole run. The agent sessions cost money. A rerun resumes. |
| `gendb run FOLDER --until STEP` | Stop after the step `data`, `requests`, `baselines` or `prepare`. |
| `gendb serve FOLDER` | Run every query at every binding. `--query Q --args a,b` runs one call; `--binding ID` uses a binding of the bindings file. |
| `gendb evaluate FOLDER` | Time every query at every binding (1 warm and 3 hot calls). `--bindings FILE` uses other bindings. |
| `gendb import FOLDER PUBLISHED_DIR --out W` | Admit our published packages, with no agent ([above](#run-our-published-packages)). |
| `gendb serve-engine FOLDER` | Engine mode: run every query at every binding on the accepted engine. |
| `gendb engine export RUN_DIR VERSION OUT` | Engine mode: write the source of an accepted version to the folder `OUT`. `RUN_DIR` is `steps/engine` in the run folder. Another run can start from `OUT`. |
| `gendb help` | Every command, also the developer commands. |

Each run writes one folder: `FOLDER/runs/templates-<storage>-<scale>/` (for example `runs/templates-designed-sf1/`), `runs/engine-<scales>/` in engine mode, or the folder `--out WORK`. When the run has `--out WORK`, give the same `--out WORK` to `serve`, `evaluate` and `serve-engine`. The run folder holds `run.json` (the steps done), the requests GenDB wrote, the baselines, the library of admitted packages and, in `output/`, per query its SQL, its SQLSpec statement, the code, the proof and its times.

The steps, in order: `data` (`setup_data.sh` when the data is missing, then the Parquet check), `requests`, `baselines` (DuckDB), `prepare` (the data import and the storage preparation), then the synthesis. In engine mode, GenDB also checks the request of every workload and prepares version 0 before the synthesis.

## What is proved, and what is trusted

For each served query package, GenDB-V claims **total correctness** relative to a fixed outcome contract. The database must meet the schema and the declared constraints, and the admitted storage must hold it. Then, under the trusted base below, every call of the verified entry ends and returns exactly one of:

- rows that are an allowed answer of the statement's SQLSpec meaning ⟦Q⟧(db);
- the SQL error of that meaning, only when the meaning on this database is exactly that error;
- `Capacity`, only when an intermediate value of the SQL evaluation does not fit the machine's number or size types;
- `ParamRefused`, exactly when an argument is outside the declared parameter domain;
- `Refused`, exactly when the worker count is outside 1 to 64.

Verus proves this claim. The final theorem `theorem_end_to_end` says what each outcome means. The termination checks of Verus prove that every loop and every recursion ends. **Performance is not proved.**

`Capacity` is about number and size types, not about memory. If memory, stack or threads run out, the process stops. It never returns a wrong answer. The trusted shim around the entry adds two answers. `AbiRefused`: it cannot read the call, or the worker count is outside 1 to 64. `SinkFailed`: the host refuses the result.

The trusted base follows. The named assumptions of each entry are in [`src/gendb/verification/src/obligations/claim.rs`](src/gendb/verification/src/obligations/claim.rs).

- **SQL meaning.** The SQLSpec semantics, its capacity domain and the SQL-to-Verus translator. Verus checks that a translated statement is well typed, not that it means the SQL text.
- **Verification and compilation.** Verus, vstd and Z3 at the pinned release, the Rust compiler, the OS and the hardware. GenDB-V refuses the code forms where this Verus release has known termination gaps.
- **Initial import.** The Parquet import gives exactly the declared columns and values in row order. For plain-array storage, the trusted step `flat_capture_parts` links or copies the captured column files as the stored parts.
- **Runtime pieces.** A query reads exactly the stored parts that the admitted build wrote. All storages of a table come from the same import. Argument delivery, the result wire, threads, the C ABI and child processes are trusted.
- **Composition.** Equal shared source text means equal propositions in the storage and query crates. GenDB-V compares the text byte for byte.
- **Termination and outcomes.** Trusted std and vstd functions, the C shim, the host sinks and the OS return. Threads are scheduled fairly. Memory, stack and threads suffice, and a failed thread join means that a worker panicked.
- **Declared integrity constraints.** The runs declare the primary and foreign keys of each schema (TPC-H: 8 and 7; SEC-EDGAR: 3 and 4). GenDB assumes them and never checks them against the data.

For your workload, the declared constraints are the keys and checks of its `schema.sql`.

In engine mode, Verus checks the engine crate of each workload whole, against a fixed engine entry. For every supported query over that schema and every database in its stored parts, the answer is an outcome that the SQL meaning allows. The claim holds for each schema.

GenDB also tests every submission: its answers at the bindings must agree with DuckDB's.

### How GenDB-V keeps the claim

- **A fixed claim.** GenDB-V translates the SQL into SQLSpec, a formal meaning of SQL modeled on PostgreSQL. It also fixes the entry point and the final theorem of each crate.
- **Free code and proofs.** The agent writes the algorithms, data layouts, intermediate specifications and proofs.
- **Everything is checked.** Verus checks every crate whole with `--no-cheating`: the query or engine code, the storage and its readers, and every proof. Agent code has no `assume`, `admit` or `external_body`.
- **Shared storage.** A workload agent can design one storage that all queries share. A verified builder writes it, and query code reads it only through verified readers.
- **Serving.** GenDB-V runs only admitted packages. It never runs the agent or the proofs again, and it has no fallback to another engine.
