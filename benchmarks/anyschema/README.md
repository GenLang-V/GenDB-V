# `anyschema`: the check workload of the general engine

A small schema of its own with tiny data and 31 templates over the SQLSpec features. As a member of a run of several workloads with role `check` ([engine mode](../../GUIDE.md#engine-mode)), every submission must verify its crate whole and answer every template at every binding with the saved answers, before any timing; it is never timed. Shared engine code that depends on another workload's schema does not compile, verify or answer here, so it is the run's check of generality. It is also a template for a new schema: a GenDB workload folder ([layout](../../GUIDE.md#your-own-workload)) with tables, data, templates and bindings, and no code.

## Files

| File | Content |
|---|---|
| `schema.sql` | the 5 tables (SQL types, NULL or NOT NULL) and the 8 declared keys |
| `queries/` | `X01.sql` ... `X31.sql`: one template each, its typed parameters in the header lines |
| `bindings.json` | two bindings per template, `v0` and `v1` |
| `gendb.toml` | the workload's name, `anyschema`, `mode = "engine"` and its one scale, `scales = ["tiny"]` |
| `setup_data.sh`, `generate.py` | the data: `data/tiny/<table>.parquet` and `data/tiny/MANIFEST.json` (row counts, the original data size) |

## Use it

As the check member of an engine run, in the `gendb.toml` of the run's primary workload:

```toml
[[members]]
folder = "../anyschema"
role = "check"
```

`gendb run` then makes its data, its plain storage and its saved answers (DuckDB, below), and checks every submission on it.

## The schema

Five tables (every table name starts with `ax_`, every column name has two segments, so the general line's schema-name rule checks them as identifiers):

| Table | Columns | Keys | Rows |
|---|---|---|---:|
| `ax_owner` | `ow_id bigint`, `ow_name text`, `ow_rank integer NULL`, `ow_born date NULL`, `ow_credit numeric(15,2)`, `ow_weight numeric(38,6) NULL`, `ow_note text NULL`, `ow_code text` | PK `ow_id` | 100 |
| `ax_kind` | `kd_code text`, `kd_group text`, `kd_weight integer NULL` | PK `kd_code` (a text key) | 12 |
| `ax_item` | `it_owner bigint`, `it_line integer`, `it_kind text`, `it_qty numeric(12,4)`, `it_price numeric(28,4) NULL`, `it_day date`, `it_flag text`, `it_tiny numeric(3,0) NULL` | PK (`it_owner`, `it_line`); FK `it_owner` → `ax_owner`, FK `it_kind` → `ax_kind` (text) | 400 |
| `ax_event` | `ev_seq bigint`, `ev_owner bigint NULL`, `ev_line integer NULL`, `ev_at date NULL`, `ev_amount numeric(18,9) NULL`, `ev_memo text NULL` (every row NULL) | PK `ev_seq`; composite FK (`ev_owner`, `ev_line`) → `ax_item` with NULL key columns | 300 |
| `ax_void` | `vd_id integer`, `vd_text text NULL` | PK `vd_id` | 0 |

The column types are every stored type GenDB reads (`integer`, `bigint`, `date`, `text`, `numeric(p,s)`). SQLSpec's `varchar(n)` and `char(n)` have no stored type of their own, so short codes and flags are `text`. The data holds the edge values: int4 and int8 minimum and maximum, negative numerics, `numeric(38,6)` values with 128-bit coefficients (up to 10^37 - 1), dates before 1970, on 1970-01-01, 2000-01-01 and leap days, empty text, multibyte UTF-8, trailing spaces, duplicate keys, NULLs in nullable foreign-key children, an all-NULL column and an empty table. The largest product a template's FROM list builds is 480,000 rows, so GenDB's version 0 (the verified interpreter) answers every template within the call limit.

## The templates

Every value is a parameter `$n` free over its SQL type, so the templates hold few constants (LIMITs stay literal: a LIMIT parameter is refused by design). Groups:

- filters and expressions (X01-X10): every type with a parameter; IS [NOT] NULL; arithmetic across numeric scales; integer and numeric division; CAST (int4 to int8, the fragment's widening cast), CASE, COALESCE, NULLIF; LIKE with a parameter pattern; SUBSTRING; text comparison; EXTRACT; a date plus an interval; `numeric(38,6)` with LIMIT;
- grouping (X11-X18): nullable integer, text, date and expression keys; COUNT(*), COUNT(column), COUNT(DISTINCT); SUM, AVG, MIN and MAX of numerics, dates and text; HAVING; global aggregates over an empty input and the empty table; ORDER BY a nullable key DESC with LIMIT;
- joins (X19-X24): a bigint key in WHERE form; a JOIN ... ON chain with a text key; a composite key; LEFT JOIN anti-join and LEFT JOIN with COUNT; a LEFT JOIN with the empty table;
- subqueries (X25-X28): correlated EXISTS and NOT EXISTS; IN and NOT IN with NULLs and over an empty set; scalar subqueries, uncorrelated and correlated; `= ANY` and `> ALL`;
- shape (X29-X31): WITH and a derived table; HAVING with a scalar subquery over a derived table; SELECT DISTINCT with NULLs.

The templates avoid SQLSpec's documented differences from PostgreSQL that would make an answer plan-dependent (grouping equal numerics of different scales; int4 SUM overflow).

## The answers

GenDB's DuckDB helper (`compare_with = "duckdb"`, the default) runs DuckDB with three settings that give it PostgreSQL's meaning in the `C` collation, which SQLSpec follows: `integer_division` (`/` of two integers truncates), `default_null_order = 'postgres'` (NULLs last ascending, first descending) and `default_collation = 'nfc'` (text ordered by its bytes, as SQLSpec's `lex_cmp` in `sqlspec/semantics/text.rs` orders it; every text of this data and of these bindings is in NFC, where `nfc` is the byte order). It binds each binding with each `$k` replaced by its typed literal and writes the rows in GenDB's value encoding, which GenDB compares with its own answers. When a run is prepared, the root's side of a check workload is checked against them too: where that side is version 0, the verified interpreter and DuckDB must agree before the run starts.
