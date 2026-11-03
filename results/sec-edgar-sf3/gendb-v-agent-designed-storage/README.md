# SEC-EDGAR SF3: GenDB-V with agent-designed storage

A workload agent designed the shared storage. For each template a query agent wrote the verified query code and could add storages built from the shared ones.

Total: per template the mean over its bindings, summed over the 6 templates.

| | |
|---|---:|
| Total, 1 / 32 / 64 workers (s) | 0.296 / 0.078 / 0.076 |
| Stored bytes | 2.69 GB |
| Packages verified whole crate (Verus, 0 errors) | 6/6 |
| Provider-reported cost of the agents | \$442.36 |

Per query: the items Verus verified in the complete crate, and the median of 3 hot calls (ms) per binding at 1 / 32 / 64 workers.

| Query | Verified items | `v0` | `v1` | `v2` |
|---|---:|---:|---:|---:|
| [Q1](queries/q1/) | 1053 | 9.460 / 2.126 / 2.202 | — | — |
| [Q2](queries/q2/) | 1171 | 0.891 / 0.620 / 0.595 | 0.660 / 0.674 / 0.608 | 0.332 / 0.414 / 0.417 |
| [Q3](queries/q3/) | 1283 | 39.954 / 6.486 / 6.097 | 42.477 / 6.203 / 7.831 | 8.968 / 3.503 / 3.461 |
| [Q4](queries/q4/) | 1550 | 25.714 / 14.478 / 12.687 | 77.525 / 32.928 / 32.880 | 68.605 / 19.608 / 18.773 |
| [Q6](queries/q6/) | 1441 | 141.673 / 29.404 / 24.347 | 160.558 / 27.996 / 30.515 | 148.132 / 27.098 / 21.210 |
| [Q24](queries/q24/) | 1307 | 54.914 / 22.243 / 21.009 | 32.927 / 16.350 / 19.452 | 55.841 / 19.850 / 20.484 |

| Path | Content |
|---|---|
| [`times.json`](times.json) | The median of every cell (ms), per query, binding and worker count |
| `queries/<query>/` | `query.sql` (the template), `spec.rs` (its SQLSpec statement), `code/` (the verified query code) |
| [`storage/`](storage/README.md) | The storages the queries read: layout, `interface/` (the `represents` relation and the readers) and `builder/` |
| [`crates/`](crates/README.md) | The complete crates Verus checked |
