# Crates

The complete crates Verus checked, whole: `queries/<query>/` for each query package and `storages/<storage>-v1/` for each storage the queries read. A query crate holds the agent's code (`src/agent/`), the statement (`src/query.rs`, the same text as the query's `spec.rs`), the interfaces of the storages it reads (`src/stores/`), the fixed entry (`src/gendb_entry.rs`) with the other fixed and generated files, and the SQLSpec library (`src/spec/`, `src/exec/`, `src/bridge/`, `src/link/`). A storage crate holds the storage's builder (`src/builder/`) and interface instead of query code.

Each crate's `compile.json` holds the compiler options of its admitted build (`opt_level`, and `target_cpu` when one was set); `gendb import` compiles the crate with them.

To check one with the pinned Verus:

```sh
GENDB_VERUS_HOME=/path/to/toolchains scripts/verus-check.sh results/tpch-sf100/gendb-v-agent-designed-storage/crates/queries/q06
```
