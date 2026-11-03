# `readings-count`: a first GenDB run

The smallest complete run of GenDB. You give a table, its data and one SQL template. An agent writes the code of the query and its proof. Verus checks the proof, GenDB admits the code, and then GenDB runs it.

| | |
|---|---|
| Table | `readings (value bigint NOT NULL, CONSTRAINT value_nonnegative CHECK (value >= 0))` |
| Rows | 5, 5, 9, 0 |
| Template | `SELECT COUNT(*) AS n FROM readings WHERE value > $1`, where `$1` is any `bigint` |
| Answer at `$1 = 4` | 3 |

## Before you start

Build `gendb` and install its tools ([install](../../GUIDE.md#install)): the pinned Verus, Python 3.12 with `sqlglot` 27.0.0 for the SQL parser and `pyarrow` for the data script, and Claude Code 2.1.280, 2.1.283 or 2.1.286 (signed in).

## Run it

From the repository root, with `gendb` on your `PATH`:

```sh
gendb run benchmarks/readings-count --until preflight   # free: the data, the storage, the proof obligation
gendb run benchmarks/readings-count                     # the agent writes and proves the query (paid)
gendb serve benchmarks/readings-count                   # run the admitted code at $1 = 4
```

1. `gendb run` reads the folder, runs `setup_data.sh` (the four rows as `data/tiny/readings.parquet`), imports the file and stores the table as plain arrays, one per column, in row order. GenDB writes this storage code itself, and Verus checks it. `--until preflight` stops here, after GenDB has translated the template and checked its statement with Verus.
2. Then one agent session (Claude Code, Opus 5.5). The agent writes the query's code and its proof in Verus (Rust). For each submission, GenDB checks the whole crate with Verus against the fixed claim, runs it on the data at `$1 = 4`, and admits the first submission that passes (at most 3). This step costs money: one call, \$2.35, when we ran it.
3. `gendb serve` runs the admitted package and prints a JSON record. Its answer is `{"rows": [[3]], "status": "ok"}`. Other values: `gendb serve benchmarks/readings-count --query readings-count --args 9` (the answer is 0).

Everything is written to `runs/templates-plain-tiny/` in this folder: the library of admitted packages, and in `output/queries/readings-count/` the query's SQL, its SQLSpec statement, the code and the proof.

## The folder

| File | Content | Meaning |
|---|---|---|
| `schema.sql` | the table and its `CHECK` | the proof may assume `value >= 0`; GenDB never checks it on the data |
| `queries/readings-count.sql` | the header `-- $1 k bigint`, then the template | `$1` is free over the whole type: the proof covers every value |
| `bindings.json` | `v0`: `$1 = 4` | where GenDB runs each submission on the data |
| `gendb.toml` | `scale = "tiny"` | the one scale, which `setup_data.sh` writes when `data/tiny/` is missing |
| | `storage = "plain"` | GenDB's plain arrays; nobody designs storage |
| | `goal = "correct"`, `compare_with = "none"`, `numeric_tolerance = "0"` | the first verified submission is admitted; the Verus proof is the correctness check, and no other database is needed |
| `setup_data.sh`, `make_data.py` | the data script | writes `data/tiny/readings.parquet` |

The run of this example that we published is in [`results/example-readings-count/`](../../results/example-readings-count/README.md).
