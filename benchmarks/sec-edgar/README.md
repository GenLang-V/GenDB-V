# SEC-EDGAR

Six query templates over the SEC Financial Statement Data Sets of 2022q1–2024q4 (12 quarters, published by the SEC on sec.gov; "SF3" = three years): 4 tables, 48 columns, 7 keys. The selective constants are typed parameters, free over their whole SQL type, and the queries' original constants are the bindings `v0`; thresholds, flags and `LIMIT`s stay literal. A GenDB workload folder ([layout](../../GUIDE.md#your-own-workload)).

| Query | Tables | Parameters |
|---|---|---|
| Q1 | pre | none (a concrete statement) |
| Q2 | num, sub | uom text (used twice), fy integer |
| Q3 | num, sub | uom text, fy integer (each used twice) |
| Q4 | num, sub, tag, pre | uom, stmt text; sic_low, sic_high integer |
| Q6 | num, sub, pre | uom, stmt text; fy integer |
| Q24 | num, pre | uom text; ddate_low, ddate_high integer |

## Files

| File | Content |
|---|---|
| `schema.sql` | The 4 tables (`integer`, `text`, `numeric(28,4)`, each column's nullability) and the 7 keys |
| `queries/` | `Q1.sql`, `Q2.sql`, `Q3.sql`, `Q4.sql`, `Q6.sql`, `Q24.sql`: one template each, its typed parameters in the header lines |
| `bindings.json` | 3 bindings per template (Q1: one), and the value domains `v1` and `v2` were drawn from |
| `gendb.toml` | The workload's name, `sec` |
| `setup_data.sh` | Downloads the 12 quarters, runs `make_canonical.py`, compares the result with `MANIFEST.json` |
| `make_canonical.py`, `sec_schema.py` | The cleaning step (raw text → one Parquet file per table) and the schema definition it reads |
| `MANIFEST.json` | Rows, row groups, bytes and Arrow schema per table of the canonical data, and its size as text |

## Make the data

```sh
bash benchmarks/sec-edgar/setup_data.sh
```

It downloads the raw text into `raw/<quarter>/`, writes `data/sf3/<table>.parquet` with `make_canonical.py`, and checks that the rows and schema equal `MANIFEST.json`. It needs curl, unzip and Python 3 with pyarrow. The cleaning rules (tab-split fields, malformed lines rejected, strict types, NULL values of num dropped, tag deduplicated, source order) are stated in full in `make_canonical.py`. `gendb run` runs it when `data/sf3/` is missing.

## Run it

```sh
gendb run benchmarks/sec-edgar                    # agent-designed storage (paid)
gendb run benchmarks/sec-edgar --storage plain    # plain-array storage (paid)
```

Or run the published packages over your own data, with no agent (Verus checks every crate again):

```sh
gendb import benchmarks/sec-edgar results/sec-edgar-sf3/gendb-v-agent-designed-storage --out $HOME/sec-import
gendb serve benchmarks/sec-edgar --out $HOME/sec-import
```

The published results are in [`results/sec-edgar-sf3/`](../../results/sec-edgar-sf3/README.md).

## Bindings

`bindings.json`: per query `binding_id`, `source` (`original`: the query's own constants; `value_domains`: other values of the value domains in the same file), `arguments` (in parameter order), `params` (by parameter name) and `rows` (the number of answer rows).

| Query | Binding | Arguments | Rows |
|---|---|---|---:|
| Q1 | v0 | — | 14 |
| Q2 | v0 | pure, 2022 | 100 |
| Q2 | v1 | pure, 2023 | 100 |
| Q2 | v2 | shares, 2024 | 100 |
| Q3 | v0 | USD, 2022 | 100 |
| Q3 | v1 | USD, 2023 | 100 |
| Q3 | v2 | shares, 2022 | 9 |
| Q4 | v0 | USD, EQ, 4000, 4999 | 500 |
| Q4 | v1 | USD, BS, 2000, 2999 | 500 |
| Q4 | v2 | shares, EQ, 6000, 6999 | 500 |
| Q6 | v0 | USD, IS, 2023 | 200 |
| Q6 | v1 | USD, BS, 2022 | 200 |
| Q6 | v2 | USD, CF, 2024 | 200 |
| Q24 | v0 | USD, 20230101, 20231231 | 2 |
| Q24 | v1 | USD, 20240101, 20241231 | 3 |
| Q24 | v2 | USD, 20230101, 20241231 | 12 |

## The data

| Table | Columns | Rows | Content |
|---|---:|---:|---|
| sub | 20 | 86,135 | submissions (one per filing) |
| num | 9 | 39,401,761 | numeric facts |
| tag | 9 | 1,070,662 | tags, one per (tag, version) |
| pre | 10 | 9,600,799 | where a fact appears in a statement |

Integers are `INTEGER` (Int32), text is text without a length (Utf8), `num.value` is `NUMERIC(28,4)` (Decimal128(28,4)); 18 columns are nullable. Keys: `PRIMARY KEY` sub(adsh), tag(tag, version), pre(adsh, report, line); `FOREIGN KEY` num(adsh) and pre(adsh) → sub, num(tag, version) and pre(tag, version) → tag; num has no key.
