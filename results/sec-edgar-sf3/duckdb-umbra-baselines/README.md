# SEC-EDGAR SF3: DuckDB and Umbra

DuckDB 1.5.6 and Umbra, each with the 7 keys of [`benchmarks/sec-edgar/schema.sql`](../../../benchmarks/sec-edgar/schema.sql) declared. Each cell is the median of 3 hot executions after 1 warm execution, in ms, at 1 / 32 / 64 threads.

## DuckDB

| Query | `v0` | `v1` | `v2` |
|---|---:|---:|---:|
| Q1 | 476.574 / 66.733 / 58.427 | — | — |
| Q2 | 4283.558 / 202.909 / 176.645 | 4083.750 / 250.049 / 173.126 | 4989.182 / 320.042 / 230.961 |
| Q3 | 5047.723 / 270.271 / 248.925 | 5522.673 / 344.477 / 239.052 | 3503.923 / 175.845 / 162.185 |
| Q4 | 4672.021 / 366.321 / 291.771 | 6231.895 / 401.843 / 365.693 | 3490.931 / 347.908 / 323.923 |
| Q6 | 7948.230 / 565.152 / 452.438 | 7490.354 / 575.049 / 464.163 | 6214.471 / 470.670 / 368.042 |
| Q24 | 5497.865 / 358.991 / 364.802 | 2724.949 / 230.059 / 198.746 | 7029.634 / 528.473 / 429.979 |

## Umbra

| Query | `v0` | `v1` | `v2` |
|---|---:|---:|---:|
| Q1 | 447.843 / 30.014 / 61.847 | — | — |
| Q2 | 237.170 / 19.299 / 75.496 | 232.309 / 19.306 / 96.284 | 992.632 / 63.696 / 132.011 |
| Q3 | 1464.154 / 110.035 / 171.964 | 1542.623 / 110.307 / 170.163 | 218.393 / 18.710 / 51.486 |
| Q4 | 1867.447 / 138.814 / 206.059 | 2939.285 / 257.403 / 407.643 | 564.436 / 55.396 / 144.589 |
| Q6 | 3417.172 / 225.468 / 317.285 | 4167.839 / 267.084 / 359.590 | 2939.967 / 192.548 / 291.517 |
| Q24 | 3977.008 / 248.467 / 298.104 | 2021.944 / 126.247 / 173.941 | 4893.753 / 295.033 / 347.704 |

## Files

| File | Content |
|---|---|
| [`times.json`](times.json) | The time of every cell (ms), per query, binding and thread count |
| [`run_sec_timing.sh`](run_sec_timing.sh) | The timing run: `sec_baselines_runner.py` (with `run_sec_baselines.py`, the TPC-H runner with the SEC-EDGAR parameter types), then the TPC-H `aggregate.py` |
| [`load/`](load/) | The DuckDB schema and load (`duckdb-create.sql`, `load_duckdb_canonical.py`), the Umbra export, schema and load (`export_for_umbra.py`, `make_umbra_sql.py`, `umbra-create-load.sql`, `umbra_load.sh`) and the Umbra server (`umbra_server.sh`) |
