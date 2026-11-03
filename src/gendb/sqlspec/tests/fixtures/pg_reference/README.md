# PostgreSQL reference fixtures

Input for `../../postgres_reference.py`, which runs them on a private PostgreSQL 18 cluster (C locale, UTF8, UTC) and writes PostgreSQL's answers as JSON evidence. The format is documented in the module docstring.

| File | Contents |
|---|---|
| `tpch_tiny.json` | `src/gendb/fixtures/tpch-spec/schema.sql` + ~40 hand-written rows; standard Q6, Q3, Q4 from `src/gendb/fixtures/tpch-spec/queries.sql`, plus Q6 with no matching rows, a Q3-shape join + GROUP BY + SUM + COUNT (bag) and Q3 with `LIMIT 2` cutting through a tie |
| `core_nulls.json` | two nullable tables: 3VL filter with duplicates, empty and grouped SUM/COUNT with NULL keys, join on NULL keys, LEFT JOIN + COUNT, `NOT IN` with NULL, correlated `EXISTS`, result types and numeric scales, `char(n)` and C collation, one expected run-time error |
| `copy_text_edges.json` | no tables: one empty-string row (COPY blank line) vs empty result, duplicate `''`, NULL vs `''` vs text `\N`, embedded newline/tab/backslash, two empty columns, one expected `22012` |
| `final_validation.json` | `one` (1 row) and `t(v text)`: IN lists of PostgreSQL common type bpchar / numeric, and a table-backed bag of `''`, NULL, `\N`, newline, tab, backslash and blank text |
| `scalar_pins.json` | one-row table `one`: numeric result scales, int4 overflow and int4/int8 promotion, cross-type numeric comparison, date + interval with month-end clamping, date vs timestamp comparison, timestamp range overflow |
| `cov_s.json` | CASE (lazy), COALESCE, NULLIF, scalar subqueries (21000), IN / NOT IN / ANY / ALL subqueries (3VL), SELECT DISTINCT, WITH |
| `cov_n.json` | integer and numeric division (`select_div_scale`, rounding, 22012, 22003), AVG |
| `cov_l.json` | LIKE (escape, bpchar padding, lazy trailing escape), SUBSTRING, EXTRACT; the 5 column-`ESCAPE` cases are parse refusals |
| `cov_a.json` | MIN / MAX, DISTINCT aggregates |
| `cov_c.json` | a constraint-valid instance of `../constraints/cov_c_schema.sql` (PK, UNIQUE [NULLS NOT DISTINCT], FK SIMPLE / FULL / self / cross-type, CHECK Unknown) |
| `cov_review.json` | NULLIF over text types, simple CASE with an untyped operand |
| `tpch_all22_cases/qNN.json` | the 22 TPC-H queries, one tiny FK-closed database each (`make_cases.py`) |
| `tpch_all22.json` | the shared all-22 database: PostgreSQL reference only. **Do not evaluate it with GenDB**: the evaluator materializes the FROM product (Q9 alone ≈ 5·10^8 rows) |

Constraint-violating instances cannot be loaded into PostgreSQL. They live in `../constraints/` and run through the verified evaluator only (`gendb sql run` / `eval`):
- `cov_c_violations/*.json`, indexed by `INDEX.json` with each `expect_evaluator` status;
- `cov_c_strict_or/`: PostgreSQL stores a row that the semantics' strict `OR` inside a CHECK rejects (`constraint_violation`); the lazy `CASE` form is the control.

Record evidence (starts and stops its own server):

    python3 src/gendb/sqlspec/tests/postgres_reference.py run \
        src/gendb/sqlspec/tests/fixtures/pg_reference/tpch_tiny.json \
        src/gendb/sqlspec/tests/fixtures/pg_reference/core_nulls.json

Compare a candidate (`{"cases": {name: {"status": "rows", "rows": [[...]]} | {"status": "sql_error", "sqlstate": "22012" | "error_kind": "division_by_zero"} | {"status": "unsupported" | "capacity" | "refused"}}}`). `sql_error` must match PostgreSQL's SQLSTATE exactly; refusals are always a mismatch; any other status is a harness failure (exit 4). Fixtures must satisfy the order/limit contract in the module docstring (top-level `ORDER BY` ⇔ `order_keys`; `limit` needs `order_keys` and a trailing `LIMIT n`; no `OFFSET`/`FETCH`/other `LIMIT`).

    python3 src/gendb/sqlspec/tests/postgres_reference.py compare EVIDENCE.json CANDIDATE.json

Each case says in `note` what it is for.
