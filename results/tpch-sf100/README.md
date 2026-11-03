# TPC-H SF100

GenDB-V, DuckDB 1.5.6 and Umbra on the 22 TPC-H query templates at scale factor 100. Each template runs at 3 parameter bindings (`v0`, `v1`, `v2`) with 1, 32 and 64 workers: 198 cells per system. Each cell is the median of 3 hot calls after 1 warm call. The faster baseline is the faster of DuckDB and Umbra in each cell.

| | GenDB-V, agent-designed storage | GenDB-V, plain-array storage | DuckDB 1.5.6 | Umbra |
|---|---:|---:|---:|---:|
| Sum of medians, binding `v0`, 1 / 32 / 64 workers (s) | 10.525 / 0.886 / 0.736 | 50.750 / 4.496 / 3.975 | 375.456 / 21.566 / 16.353 | 165.849 / 9.987 / 11.647 |
| Sum of medians, all 3 bindings, 1 / 32 / 64 workers (s) | 31.141 / 2.532 / 2.248 | 150.402 / 13.355 / 11.859 | 1103.523 / 63.774 / 50.219 | 510.310 / 30.628 / 35.938 |
| Cells faster than the faster baseline | 198/198 | 165/198 | | |
| Cells at least 5x faster than the faster baseline | 190/198 | 33/198 | | |
| Queries at least 5x faster in all nine cells | 19/22 | 1/22 (Q18) | | |
| Stored bytes | 102.70 GB | 158.62 GB | 108.3 GB | 113 GB |
| Packages verified whole crate (Verus, 0 errors) | 22/22 | 22/22 | | |
| Provider-reported cost of the agents | \$1,867.92 | \$1,284.80 | | |

| Folder | Content |
|---|---|
| [`benchmarks/tpc-h/bindings/`](../../benchmarks/tpc-h/README.md#bindings) | The 3 parameter bindings of each template and their generator |
| [`duckdb-umbra-baselines/`](duckdb-umbra-baselines/README.md) | DuckDB and Umbra: the time of every cell, and the load and timing scripts |
| [`gendb-v-agent-designed-storage/`](gendb-v-agent-designed-storage/README.md) | GenDB-V with agent-designed storage: the time of every cell, and per query the template, its SQLSpec statement, the verified code and the complete crate, with the storages |
| [`gendb-v-plain-array-storage/`](gendb-v-plain-array-storage/README.md) | GenDB-V with plain-array storage: the same contents |
