# SEC-EDGAR SF3

GenDB-V, DuckDB 1.5.6 and Umbra on the 6 SEC-EDGAR query templates ([`benchmarks/sec-edgar/`](../../benchmarks/sec-edgar/README.md)) at scale factor 3. Q1 runs at one binding and the other templates at 3, each with 1, 32 and 64 workers: 48 cells per system. Each cell is the median of 3 hot calls after 1 warm call. The total is per template the mean over its bindings, summed over the 6 templates. The faster baseline is the faster of DuckDB and Umbra in each cell.

| | GenDB-V, agent-designed storage | GenDB-V, plain-array storage | DuckDB 1.5.6 | Umbra |
|---|---:|---:|---:|---:|
| Total, 1 / 32 / 64 workers (s) | 0.296 / 0.078 / 0.076 | 7.043 / 0.837 / 0.731 | 26.720 / 1.869 / 1.555 | 10.940 / 0.746 / 1.143 |
| Cells faster than the faster baseline | 48/48 | 36/48 | | |
| Cells at least 5x faster than the faster baseline | 47/48 | 4/48 | | |
| Stored bytes | 2.69 GB | 7.75 GB | 3.76 GB | 7.34 GB |
| Packages verified whole crate (Verus, 0 errors) | 6/6 | 6/6 | | |
| Provider-reported cost of the agents | \$442.36 | \$389.97 | | |

| Folder | Content |
|---|---|
| [`benchmarks/sec-edgar/bindings.json`](../../benchmarks/sec-edgar/README.md#bindings) | The parameter bindings of each template |
| [`duckdb-umbra-baselines/`](duckdb-umbra-baselines/README.md) | DuckDB and Umbra: the time of every cell, and the load and timing scripts |
| [`gendb-v-agent-designed-storage/`](gendb-v-agent-designed-storage/README.md) | GenDB-V with agent-designed storage: the time of every cell, and per query the template, its SQLSpec statement, the verified code and the complete crate, with the storages |
| [`gendb-v-plain-array-storage/`](gendb-v-plain-array-storage/README.md) | GenDB-V with plain-array storage: the same contents |
