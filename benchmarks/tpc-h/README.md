# TPC-H

The 22 queries of the TPC-H decision-support benchmark as GenDB SQL templates, over the 8 TPC-H tables with their 8 primary keys and 7 foreign keys. Each parameter `$n` is free over its whole SQL type. A GenDB workload folder ([layout](../../GUIDE.md#your-own-workload)).

## Files

| File | Content |
|---|---|
| `schema.sql` | The 8 tables (`bigint`, `numeric(15,2)`, `date`, `text`, every column `NOT NULL`) and the 15 keys |
| `queries/` | `Q01.sql` ... `Q22.sql`: one template each, its typed parameters in the header lines |
| `bindings/` | `sf100.json` (3 bindings per template), `sf1.json` (`v0` per template) and their generator |
| `gendb.toml` | The workload's name, `tpch` |
| `setup_data.sh` | Makes the data of one scale: dbgen text, then Parquet |
| `tbl-to-parquet/` | The converter `setup_data.sh` runs: dbgen `.tbl` text to one Parquet file per table, every value checked back against the text |

## Make the data

```sh
bash benchmarks/tpc-h/setup_data.sh sf1
```

It builds dbgen ([electrum/tpch-dbgen](https://github.com/electrum/tpch-dbgen)), writes the text to `raw/sf1/<table>.tbl`, then builds and runs `tbl-to-parquet`, which writes `data/sf1/<table>.parquet` and a `MANIFEST.json` (rows per table and `original_data_bytes`, the size of the text). It needs git, make, a C compiler, cargo (Rust 1.88 or later) and python3. `gendb run` runs it when the data of its scale is missing.

## Run it

```sh
gendb run benchmarks/tpc-h --scale sf1                   # agent-designed storage (paid)
gendb run benchmarks/tpc-h --scale sf1 --storage plain   # plain-array storage (paid)
```

Or run the published packages over your own data, with no agent (Verus checks every crate again):

```sh
gendb import benchmarks/tpc-h results/tpch-sf100/gendb-v-agent-designed-storage --out $HOME/tpch-import
gendb serve benchmarks/tpc-h --out $HOME/tpch-import
```

The published results are in [`results/tpch-sf100/`](../../results/tpch-sf100/README.md).

## Bindings

`v0` is the TPC-H validation binding, `v1` and `v2` are drawn by the TPC-H qgen rules. At SF1, `sf1.json` has `v0` only, with Q11's fraction 0.0001/SF = 0.0001.

| File | Content |
|---|---|
| `sf100.json`, `sf1.json` | Per query and binding: `binding_id`, `source` (`validation` or `qgen-random`), `spec_params` (the TPC-H names), `arguments` (in parameter order) and `params` (by parameter name) |
| `generate_bindings.py` | The generator: each parameter drawn from its TPC-H clause 2.4 domain with a fixed seed |
| `param_names.json` | Per query, TPC-H parameter name to the query's parameter name |
| `param_forms.json` | How each query parameter's value is formed from the TPC-H parameters |

## The data at scale factor 100

| Table | Rows |
|---|---:|
| lineitem | 600,037,902 |
| orders | 150,000,000 |
| partsupp | 80,000,000 |
| part | 20,000,000 |
| customer | 15,000,000 |
| supplier | 1,000,000 |
| nation | 25 |
| region | 5 |
