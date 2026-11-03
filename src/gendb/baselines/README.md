# DuckDB baselines

`duckdb_baselines.py` gives a workload its runtime targets and saved answers from DuckDB. `gendb run` calls it when the folder's `compare_with` is `"duckdb"` (the default); you do not run it yourself. It needs the Python package `duckdb` 1.5.6 (`pip install duckdb==1.5.6`) in the interpreter of GenDB's SQL parser (`GENDB_SQL_FRONTEND_PYTHON`, default the one in `frontend/parser/toolchain.json`).

```sh
python3 duckdb_baselines.py REQUEST.json BINDINGS.json OUT_DIR [--timed all|none|BINDING] [--threads 1,8]
```

- **Store.** One DuckDB database per scale, `OUT_DIR/duckdb.db`, loaded once from the workload's Parquet files. Every declared key and CHECK is a table constraint, so the load also checks them on the data.
- **Meaning.** DuckDB runs with PostgreSQL's meaning, which GenDB's SQL semantics follow: `integer_division`, `default_null_order = 'postgres'` and `default_collation = 'nfc'` (text compares by its bytes when it is in NFC form). The same settings hold for the times and for the answers.
- **Times.** Per query, binding and thread count: a fresh connection, 1 warm and 3 hot calls, the median of the hot calls, under the host's timing lease (GenDB's lock files from the request's `barriers`).
- **Answers.** The warm result at each binding, in GenDB's value encoding.
- **Output.** `targets.json` (DuckDB's medians as the targets), `answers/duckdb/<query>/<binding>.json`, `blocks/duckdb/...` and `baselines.json`, the file a `baselines` setting can name for a saved baselines folder:

```json
{"targets": "targets.json",
 "engines": [{"name": "duckdb", "description": "...", "answers": "answers/duckdb/{query}/{binding}.json"}]}
```

Paths in `baselines.json` are relative to its folder (or absolute); `{query}` is the query's file stem and `{binding}` its binding id; the rows of an answer file are at `/run/result`. `targets` is optional (answers only). A rerun keeps every finished block and answer.

A saved answer also tests GenDB: a result that agrees with no saved answer is not admitted, and the run shows the difference. A query DuckDB cannot run is listed and the helper exits 1; set `compare_with = "none"` to run without DuckDB (the proof is then the only correctness check).
