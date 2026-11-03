# Test fixtures

Files the tests of this workspace read. Paths in the tests are relative to the repository root.

| Folder | Content | Read by |
|---|---|---|
| `tpch/templates/` | the 22 TPC-H templates (`q01.sql` ... `q22.sql`) and `templates.json` (each one's typed parameters and the TPC-H validation values) | the engine and storage tests of `synthesis` and `verification` |
| `tpch/integrity-constraints.json` | the 15 TPC-H keys as a request's `integrity_constraints` | the same tests, the SQL frontend's constraint tests |
| `tpch/engine-variants/` | 107 frozen meaning-preserving variants of the templates and their `manifest.json` (file and SHA-256 of each) | the engine tests of `synthesis` |
| `tpch-spec/` | a TPC-H DDL with inline keys (`schema.sql`) and the 22 queries with their validation values (`queries.sql`) | the SQL frontend tests, SQLSpec's PostgreSQL reference fixtures |

The TPC-H workload itself is the folder `benchmarks/tpc-h/` (its `schema.sql`, `queries/` and bindings); these files are self-contained copies in the forms the tests read.
