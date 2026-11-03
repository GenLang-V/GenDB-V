# TPC-H SF100: GenDB-V with agent-designed storage

A workload agent designed the shared storage. For each template a query agent wrote the verified query code and could add storages built from the shared ones.

| | |
|---|---:|
| Sum of medians, binding `v0`, 1 / 32 / 64 workers (s) | 10.525 / 0.886 / 0.736 |
| Sum of medians, all 3 bindings, 1 / 32 / 64 workers (s) | 31.141 / 2.532 / 2.248 |
| Stored bytes | 102.70 GB |
| Packages verified whole crate (Verus, 0 errors) | 22/22 |
| Provider-reported cost of the agents | \$1,867.92 |

Per query: the items Verus verified in the complete crate, and the median of 3 hot calls (ms) per binding at 1 / 32 / 64 workers.

| Query | Verified items | `v0` | `v1` | `v2` |
|---|---:|---:|---:|---:|
| [Q01](queries/q01/) | 1413 | 632.622 / 92.410 / 84.190 | 650.512 / 79.240 / 81.605 | 651.059 / 81.199 / 89.128 |
| [Q02](queries/q02/) | 1500 | 0.726 / 0.790 / 0.752 | 0.707 / 0.762 / 0.718 | 0.753 / 1.107 / 1.027 |
| [Q03](queries/q03/) | 1467 | 132.307 / 16.806 / 11.608 | 134.113 / 14.726 / 11.196 | 132.577 / 15.460 / 13.345 |
| [Q04](queries/q04/) | 1234 | 17.731 / 6.372 / 5.800 | 17.707 / 7.252 / 7.266 | 17.204 / 5.706 / 6.390 |
| [Q05](queries/q05/) | 1637 | 597.355 / 43.146 / 31.895 | 576.453 / 28.803 / 34.956 | 579.487 / 40.977 / 30.827 |
| [Q06](queries/q06/) | 1215 | 61.315 / 10.516 / 10.607 | 61.392 / 10.735 / 10.646 | 60.573 / 9.982 / 10.201 |
| [Q07](queries/q07/) | 1661 | 812.680 / 49.608 / 38.521 | 817.422 / 43.856 / 37.950 | 809.767 / 54.162 / 42.306 |
| [Q08](queries/q08/) | 1718 | 217.376 / 12.306 / 11.343 | 214.489 / 16.243 / 12.937 | 210.966 / 12.842 / 11.222 |
| [Q09](queries/q09/) | 1922 | 4547.630 / 294.533 / 228.875 | 4431.398 / 285.188 / 248.328 | 4419.250 / 281.310 / 236.830 |
| [Q10](queries/q10/) | 1681 | 331.494 / 45.087 / 42.820 | 331.385 / 37.780 / 43.133 | 331.585 / 45.725 / 40.860 |
| [Q11](queries/q11/) | 1361 | 173.674 / 28.282 / 30.402 | 169.105 / 30.189 / 27.796 | 159.012 / 26.295 / 28.180 |
| [Q12](queries/q12/) | 1396 | 97.070 / 13.843 / 12.382 | 99.665 / 12.456 / 10.616 | 100.120 / 13.509 / 10.935 |
| [Q13](queries/q13/) | 1590 | 1437.907 / 101.185 / 74.628 | 1346.218 / 90.777 / 73.464 | 1396.845 / 91.664 / 81.219 |
| [Q14](queries/q14/) | 1403 | 192.718 / 21.916 / 13.323 | 186.401 / 20.454 / 13.130 | 187.376 / 16.317 / 13.536 |
| [Q15](queries/q15/) | 1412 | 195.871 / 26.174 / 26.694 | 196.104 / 27.498 / 26.279 | 197.636 / 26.108 / 25.771 |
| [Q16](queries/q16/) | 1775 | 143.725 / 17.512 / 18.665 | 140.909 / 17.746 / 18.963 | 140.564 / 16.820 / 18.957 |
| [Q17](queries/q17/) | 1295 | 15.364 / 2.168 / 1.868 | 16.144 / 1.914 / 2.449 | 15.883 / 1.884 / 2.364 |
| [Q18](queries/q18/) | 1428 | 190.494 / 24.551 / 23.711 | 186.394 / 21.866 / 23.418 | 186.352 / 22.933 / 23.567 |
| [Q19](queries/q19/) | 1577 | 20.199 / 2.593 / 2.569 | 19.880 / 3.437 / 3.090 | 20.099 / 2.487 / 3.255 |
| [Q20](queries/q20/) | 1366 | 72.364 / 9.581 / 9.777 | 70.383 / 8.226 / 10.065 | 70.351 / 9.302 / 8.358 |
| [Q21](queries/q21/) | 1533 | 600.795 / 54.533 / 43.761 | 597.765 / 44.153 / 43.895 | 595.020 / 43.160 / 45.905 |
| [Q22](queries/q22/) | 1320 | 33.983 / 11.851 / 11.756 | 33.553 / 12.235 / 14.377 | 34.726 / 11.442 / 11.817 |

| Path | Content |
|---|---|
| [`times.json`](times.json) | The median of every cell (ms), per query, binding and worker count |
| `queries/<query>/` | `query.sql` (the template), `spec.rs` (its SQLSpec statement), `code/` (the verified query code) |
| [`storage/`](storage/README.md) | The storages the queries read: layout, `interface/` (the `represents` relation and the readers) and `builder/` |
| [`crates/`](crates/README.md) | The complete crates Verus checked |
