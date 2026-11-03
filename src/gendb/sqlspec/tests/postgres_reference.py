#!/usr/bin/env python3
"""PostgreSQL reference outputs for SQLSpec differential tests.

Runs tiny SQL fixtures on a private, throwaway PostgreSQL 18 cluster and records
PostgreSQL's answers as canonical, typed evidence; compares a candidate answer
(e.g. the Verus evaluator's) against that evidence. It executes nothing itself:
every result comes from the real server through ``psql``.

Cluster: ``<work-dir>/cluster/{data,sock,server.log}``; C locale, UTF8, UTC,
ISO dates, no TCP listener, unix socket and TMPDIR inside the work dir. Only the
server started from ``<work-dir>/cluster/data`` is ever started or stopped.

Fixture format (JSON, documented in ``fixtures/pg_reference/README.md``)::

    {"fixture": "id", "description": "...",
     "ddl": [{"path": "src/gendb/fixtures/tpch-spec/schema.sql"} | {"sql": "CREATE ..."}],
     "tables": [{"name": "t", "columns": ["a", "b"], "defaults": {"c": "x"},
                 "rows": [[1, "2.50"], [null, "0.00"]]}],
     "cases": [{"name": "q", "sql": "SELECT ..." | "query": {"path": "...", "label": "Q6"},
                "expect": "rows" | "error",
                "order_keys": [{"column": "revenue", "descending": true}],
                "limit": 2, "value_only_columns": ["x"], "note": "..."}]}

Values are JSON strings, integers, booleans or null; JSON floats are refused so
decimals stay exact. Paths are relative to the repository root.

Result comparison:
* no ``order_keys``: multiset (bag) equality of canonical rows;
* ``order_keys`` (output columns): PostgreSQL's rows are split into runs of
  equal sort keys; a candidate must have the same key sequence and the same bag
  inside each run, so any order within a tie run is accepted and none is
  invented. With ``limit`` the harness also runs the query without its final
  ``LIMIT n`` to learn the full tie run at the cut; the candidate's last run
  may be any sub-bag of it of the right size.

Order/limit contract (checked before PostgreSQL runs; a violation is a harness
failure, never a silent bag comparison): a top-level ``ORDER BY`` requires
``order_keys`` and ``order_keys`` requires a top-level ``ORDER BY``; ``limit``
requires ``order_keys`` and the SQL must end in exactly that ``LIMIT n``; any
other ``LIMIT`` (nested, ``LIMIT ALL``, undeclared) and any ``OFFSET`` or
``FETCH`` is refused. The check is a small lexical scan (literals, quoted
identifiers, comments, parentheses) of fixture SQL, not a SQL parser; it is
only meant to reject fixtures whose order contract the harness cannot state.

Candidate statuses (``compare``): ``rows`` with ``rows``; ``sql_error`` with a
5-character ``sqlstate`` or an ``error_kind`` from ``ERROR_KINDS`` (compared
with PostgreSQL's SQLSTATE exactly); ``unsupported`` / ``capacity`` /
``refused`` are framework refusals and always a mismatch, never a SQL error.
Any other status (including the former generic ``error``) is a harness failure.

Canonical values keep PostgreSQL's text except: integers normalised through
``int``; numerics through ``Decimal`` keeping the scale (``1.50`` != ``1.5``);
``character(n)`` right-trimmed (trailing blanks are insignificant in bpchar).
A case may declare ``value_only_columns`` (numeric output columns): there the
scale is dropped (``1.0`` == ``1.00`` == ``1``). Only for columns whose displayed
scale is a plan-dependent representative (GROUP BY / DISTINCT / MIN / MAX over
equal values of different scales, reference choice R1); it is recorded in the
evidence and applied to both sides.

Exit statuses (``run``): 0 every case matched its declared ``expect``;
3 some case's SQL outcome differed from ``expect`` (unexpected SQLSTATE, or rows
where an error was expected); 4 harness failure (cluster, psql, fixture, parse).
``compare``: 0 match, 1 mismatch, 4 harness failure. Usage errors: 2.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass
from decimal import Decimal, InvalidOperation
from pathlib import Path
from typing import Any

PG_BIN = Path("/usr/lib/postgresql/18/bin")
REPO_ROOT = Path(__file__).resolve().parents[4]  # <repo>/src/gendb/sqlspec/tests/postgres_reference.py
DEFAULT_WORK_DIR = REPO_ROOT / "target" / "pg-evidence" / "verus-sql-pg"
PORT = "5432"  # only names the socket file inside our private socket directory
SUPERUSER = "postgres"

EXIT_OK, EXIT_MISMATCH, EXIT_USAGE, EXIT_SQL, EXIT_HARNESS = 0, 1, 2, 3, 4

INTEGER_TYPES = {"smallint", "integer", "bigint"}
SEP = "\x1f"

# Documented candidate error kinds -> the SQLSTATE PostgreSQL raises for them.
ERROR_KINDS = {"division_by_zero": "22012", "numeric_value_out_of_range": "22003"}
REFUSAL_STATUSES = {"unsupported", "capacity", "refused"}


class HarnessError(Exception):
    """The harness, cluster or fixture failed; says nothing about the SQL."""


@dataclass(frozen=True)
class SqlError:
    sqlstate: str
    message: str


# ---------------------------------------------------------------- cluster


class PgCluster:
    """A private PostgreSQL cluster under ``work_dir/cluster``; use as a context manager."""

    def __init__(self, work_dir: Path = DEFAULT_WORK_DIR):
        self.root = Path(work_dir).resolve() / "cluster"
        self.data = self.root / "data"
        self.sock = self.root / "sock"
        self.tmp = self.root / "tmp"
        self.log = self.root / "server.log"

    def env(self) -> dict[str, str]:
        env = {k: v for k, v in os.environ.items() if not k.startswith("PG")}
        env.update(PGHOST=str(self.sock), PGPORT=PORT, PGUSER=SUPERUSER, PGTZ="UTC",
                   PGCLIENTENCODING="UTF8", LC_ALL="C", LANG="C", TZ="UTC",
                   TMPDIR=str(self.tmp), PSQLRC=os.devnull)
        return env

    def _tool(self, name: str, *args: str, stdin: str | None = None) -> subprocess.CompletedProcess:
        return subprocess.run([str(PG_BIN / name), *args], input=stdin, env=self.env(),
                              capture_output=True, text=True)

    def running(self) -> bool:
        return self._tool("pg_ctl", "status", "-D", str(self.data)).returncode == 0

    def start(self) -> None:
        for d in (self.sock, self.tmp):
            d.mkdir(parents=True, exist_ok=True)
        if not (self.data / "PG_VERSION").exists():
            r = self._tool("initdb", "-D", str(self.data), "--locale=C", "--encoding=UTF8",
                           "-U", SUPERUSER, "--auth=trust", "--no-instructions")
            if r.returncode != 0:
                raise HarnessError(f"initdb failed: {r.stderr.strip()}")
        if self.running():
            raise HarnessError(f"own cluster at {self.data} is already running; "
                               f"run the 'stop' command first")
        opts = (f"-c listen_addresses='' -c unix_socket_directories='{self.sock}' -p {PORT} "
                f"-c TimeZone=UTC -c DateStyle=ISO,YMD -c lc_messages=C -c fsync=off "
                f"-c statement_timeout=60s")
        r = self._tool("pg_ctl", "start", "-D", str(self.data), "-l", str(self.log), "-w",
                       "-o", opts)
        if r.returncode != 0:
            raise HarnessError(f"pg_ctl start failed: {r.stderr.strip()} (see {self.log})")

    def stop(self) -> None:
        if (self.data / "postmaster.pid").exists() and self.running():
            r = self._tool("pg_ctl", "stop", "-D", str(self.data), "-m", "fast", "-w")
            if r.returncode != 0:
                raise HarnessError(f"pg_ctl stop failed: {r.stderr.strip()}")

    def __enter__(self) -> "PgCluster":
        self.start()
        return self

    def __exit__(self, *exc: object) -> None:
        self.stop()

    def psql(self, database: str, script: str, single_transaction: bool = False) -> str | SqlError:
        """Run a psql script; stdout on success, the SQL error, or HarnessError."""
        args = ["-X", "-q", "-A", "-t", "-F", SEP, "-v", "ON_ERROR_STOP=1",
                "-d", database, "-f", "-"]
        if single_transaction:
            args.insert(0, "-1")
        r = self._tool("psql", *args, stdin="\\set VERBOSITY verbose\n" + script)
        if r.returncode == 0:
            return r.stdout
        m = re.search(r"ERROR:\s+([0-9A-Z]{5}):\s*(.*)", r.stderr)
        if r.returncode == 3 and m:
            return SqlError(m.group(1), m.group(2).strip())
        raise HarnessError(f"psql exit {r.returncode}: {r.stderr.strip()}")

    def fresh_database(self, name: str) -> None:
        for stmt in (f'DROP DATABASE IF EXISTS "{name}"', f'CREATE DATABASE "{name}"'):
            out = self.psql("postgres", stmt + ";\n")
            if isinstance(out, SqlError):
                raise HarnessError(f"{stmt}: {out.sqlstate} {out.message}")


# ---------------------------------------------------------------- fixtures


def _no_float(text: str) -> Any:
    raise HarnessError(f"JSON float {text} refused; write decimals as strings")


def load_json(path: Path) -> Any:
    try:
        return json.loads(Path(path).read_text(), parse_float=_no_float)
    except (OSError, json.JSONDecodeError) as e:
        raise HarnessError(f"cannot read {path}: {e}") from e


def query_from_file(path: str, label: str) -> str:
    """The statement headed ``-- <label>:`` in a query file such as src/gendb/fixtures/tpch-spec/queries.sql."""
    text = (REPO_ROOT / path).read_text()
    m = re.search(rf"^-- {re.escape(label)}:.*?\n(.*?)(?=^-- Q\d+:|\Z)", text, re.S | re.M)
    if not m:
        raise HarnessError(f"no '-- {label}:' block in {path}")
    return strip_statement(m.group(1))


def strip_statement(sql: str) -> str:
    sql = sql.strip().rstrip(";").strip()
    if not sql or ";" in sql:
        raise HarnessError("a case must be exactly one statement")
    return sql


def sql_literal(value: Any) -> str:
    if value is None:
        return "NULL"
    if isinstance(value, bool):
        return "TRUE" if value else "FALSE"
    if isinstance(value, int):
        return str(value)
    if isinstance(value, str):
        return "'" + value.replace("'", "''") + "'"
    raise HarnessError(f"unsupported fixture value {value!r}")


def load_script(fixture: dict) -> str:
    parts = []
    for item in fixture.get("ddl", []):
        parts.append((REPO_ROOT / item["path"]).read_text() if "path" in item else item["sql"])
    for table in fixture.get("tables", []):
        defaults = table.get("defaults", {})
        columns = list(table["columns"]) + [c for c in defaults if c not in table["columns"]]
        rows = []
        for row in table["rows"]:
            if len(row) != len(table["columns"]):
                raise HarnessError(f"{table['name']}: row {row} does not match columns")
            values = list(row) + [defaults[c] for c in columns[len(row):]]
            rows.append("(" + ", ".join(map(sql_literal, values)) + ")")
        if rows:
            parts.append(f"INSERT INTO {table['name']} ({', '.join(columns)}) VALUES\n  "
                         + ",\n  ".join(rows) + ";")
    return "\n".join(parts) + "\n"


# ---------------------------------------------------------------- canonical values


def decode_copy_text(field: str) -> str | None:
    """One field of COPY ... TO STDOUT text format."""
    if field == "\\N":
        return None
    escapes = {"b": "\b", "f": "\f", "n": "\n", "r": "\r", "t": "\t", "v": "\v"}
    return re.sub(r"\\(.)", lambda m: escapes.get(m.group(1), m.group(1)), field)


def canonical_value(pg_type: str, value: Any) -> str | None:
    """PostgreSQL output text (or a candidate's value) in canonical form for ``pg_type``."""
    if value is None:
        return None
    if isinstance(value, float):
        raise HarnessError(f"float value {value!r} refused; exact decimals must be strings")
    text = str(value).lower() if isinstance(value, bool) else str(value)
    try:
        if pg_type in INTEGER_TYPES:
            return str(int(text))
        if pg_type.startswith("numeric"):
            return format(Decimal(text), "f")
    except (ValueError, InvalidOperation) as e:
        raise HarnessError(f"{text!r} is not a {pg_type}") from e
    if pg_type.startswith("character(") or pg_type == "bpchar":
        return text.rstrip(" ")
    if pg_type == "boolean":
        return {"true": "t", "false": "f"}.get(text, text)
    return text


def sort_key(pg_type: str, value: str) -> Any:
    """Ordering value of a canonical non-NULL value (C collation: byte order)."""
    if pg_type in INTEGER_TYPES:
        return int(value)
    if pg_type.startswith("numeric"):
        return Decimal(value)
    if pg_type == "date" or pg_type.startswith(("character", "text", "bpchar")):
        return value.encode()
    raise HarnessError(f"order key type {pg_type} is not supported by this harness")


def canonical_rows(columns: list[dict], rows: list[list[Any]], value_only: list[str] | None = None) -> list[tuple]:
    value_only = set(value_only or ())
    for name in value_only:
        hits = [c for c in columns if c["name"] == name]
        if len(hits) != 1 or not hits[0]["type"].startswith("numeric"):
            raise HarnessError(f"value_only_columns: {name!r} is not exactly one numeric output column")
    out = []
    for row in rows:
        if len(row) != len(columns):
            raise HarnessError(f"row {row} has {len(row)} values, expected {len(columns)}")
        vals = []
        for c, v in zip(columns, row):
            text = canonical_value(c["type"], v)
            if c["name"] in value_only and text is not None:
                text = format(Decimal(text).normalize(), "f")
            vals.append(text)
        out.append(tuple(vals))
    return out


def bag_of(rows: list[tuple]) -> list[dict]:
    """Deterministic multiset listing: distinct rows sorted, NULL before values."""
    counts = Counter(rows)
    order = sorted(counts, key=lambda r: [(v is not None, v or "") for v in r])
    return [{"row": list(r), "count": counts[r]} for r in order]


def _bag_counter(bag: list[dict]) -> Counter:
    return Counter({tuple(e["row"]): e["count"] for e in bag})


# ---------------------------------------------------------------- ordering


def _key_resolver(columns: list[dict], order_keys: list[dict]):
    names = [c["name"] for c in columns]
    specs = []
    for k in order_keys:
        if names.count(k["column"]) != 1:
            raise HarnessError(f"order key {k['column']!r} must name exactly one output column")
        i = names.index(k["column"])
        desc = bool(k.get("descending", False))
        nulls_first = k.get("nulls", "first" if desc else "last") == "first"
        specs.append((i, columns[i]["type"], desc, nulls_first))

    def key_of(row: tuple) -> tuple:
        return tuple(None if row[i] is None else sort_key(t, row[i]) for i, t, _, _ in specs)

    def in_order(a: tuple, b: tuple) -> bool:
        for (_, _, desc, nulls_first), x, y in zip(specs, a, b):
            if x == y:
                continue
            if x is None or y is None:
                return (x is None) == nulls_first
            return (x > y) if desc else (x < y)
        return True

    return key_of, in_order


def tie_runs(rows: list[tuple], key_of) -> list[list[tuple]]:
    runs: list[list[tuple]] = []
    for row in rows:
        if runs and key_of(runs[-1][0]) == key_of(row):
            runs[-1].append(row)
        else:
            runs.append([row])
    return runs


# ---------------------------------------------------------------- running cases


def _describe(pg: PgCluster, db: str, sql: str) -> list[dict] | SqlError:
    out = pg.psql(db, sql + "\n\\gdesc\n")
    if isinstance(out, SqlError):
        return out
    return [dict(zip(("name", "type"), line.split(SEP))) for line in out.splitlines() if line]


def _fetch(pg: PgCluster, db: str, sql: str, width: int) -> list[list[str | None]] | SqlError:
    if width == 0:
        raise HarnessError("zero-column results are not supported (COPY rows would be indistinguishable)")
    out = pg.psql(db, f"COPY ({sql}) TO STDOUT;\n")
    if isinstance(out, SqlError):
        return out
    # Every COPY row ends in "\n" and embedded newlines are escaped, so "" is the
    # empty result and a blank line is a real row (e.g. one empty-string column).
    if out == "":
        return []
    if not out.endswith("\n"):
        raise HarnessError("COPY output is not newline-terminated")
    rows = [[decode_copy_text(f) for f in line.split("\t")] for line in out[:-1].split("\n")]
    if any(len(r) != width for r in rows):
        raise HarnessError("COPY output width differs from \\gdesc")
    return rows


def _sql_words(sql: str) -> list[tuple[int, str, int]]:
    """``(paren depth, upper-case bare word, offset)`` outside literals, quoted identifiers and comments."""
    words, depth, i, n = [], 0, 0, len(sql)
    while i < n:
        c = sql[i]
        if sql.startswith("--", i):
            j = sql.find("\n", i)
            i = n if j < 0 else j + 1
        elif sql.startswith("/*", i):
            level, i = 1, i + 2
            while level:
                if i >= n:
                    raise HarnessError("unterminated comment in case SQL")
                if sql.startswith("/*", i):
                    level, i = level + 1, i + 2
                elif sql.startswith("*/", i):
                    level, i = level - 1, i + 2
                else:
                    i += 1
        elif c in "'\"":
            backslash = c == "'" and bool(words) and words[-1][1] == "E" and words[-1][2] + 1 == i
            if backslash:
                words.pop()
            i += 1
            while True:
                if i >= n:
                    raise HarnessError("unterminated literal in case SQL")
                if backslash and sql[i] == "\\":
                    i += 2
                elif sql[i] == c:
                    if sql.startswith(c * 2, i):
                        i += 2
                    else:
                        i += 1
                        break
                else:
                    i += 1
        elif (m := re.match(r"\$([A-Za-z_][A-Za-z0-9_]*)?\$", sql[i:])):
            j = sql.find(m.group(0), i + len(m.group(0)))
            if j < 0:
                raise HarnessError("unterminated dollar-quoted literal in case SQL")
            i = j + len(m.group(0))
        elif (m := re.match(r"[A-Za-z_][A-Za-z0-9_$]*", sql[i:])):
            words.append((depth, m.group(0).upper(), i))
            i += len(m.group(0))
        else:
            depth += (c == "(") - (c == ")")
            i += 1
    return words


def check_order_contract(case: dict, sql: str) -> None:
    """Refuse cases whose ORDER BY / LIMIT / OFFSET the comparator cannot state (module docstring)."""
    name = case["name"]
    words = _sql_words(sql)
    for depth, word, _ in words:
        if word in ("OFFSET", "FETCH"):
            raise HarnessError(f"{name}: {word} is not supported by this harness")
    top_order = any(d == 0 and w == "ORDER" and nxt[0] == 0 and nxt[1] == "BY"
                    for (d, w, _), nxt in zip(words, words[1:]))
    has_keys = bool(case.get("order_keys"))
    if top_order and not has_keys:
        raise HarnessError(f"{name}: top-level ORDER BY without declared order_keys")
    if has_keys and not top_order:
        raise HarnessError(f"{name}: order_keys declared but the SQL has no top-level ORDER BY")
    limits = [(d, pos) for d, w, pos in words if w == "LIMIT"]
    limit = case.get("limit")
    if limit is None:
        if limits:
            raise HarnessError(f"{name}: LIMIT in SQL without a declared limit")
        return
    if not has_keys:
        raise HarnessError(f"{name}: limit declared without order_keys")
    if isinstance(limit, bool) or not isinstance(limit, int) or limit < 0:
        raise HarnessError(f"{name}: limit must be a non-negative integer")
    m = re.search(rf"\bLIMIT\s+{limit}\s*$", sql, re.I)
    if not m or limits != [(0, m.start())]:
        raise HarnessError(f"{name}: SQL must end in 'LIMIT {limit}' and contain no other LIMIT")


def run_case(pg: PgCluster, db: str, case: dict) -> dict:
    if "query" in case:
        sql = query_from_file(case["query"]["path"], case["query"]["label"])
        provenance = f"{case['query']['path']} {case['query']['label']}"
    else:
        sql = strip_statement(case["sql"])
        provenance = "inline"
    check_order_contract(case, sql)
    result: dict[str, Any] = {"name": case["name"], "expect": case.get("expect", "rows"),
                              "provenance": provenance, "sql": sql}
    if case.get("note"):
        result["note"] = case["note"]
    if case.get("value_only_columns"):
        result["value_only_columns"] = list(case["value_only_columns"])
    columns = _describe(pg, db, sql)
    raw = columns if isinstance(columns, SqlError) else _fetch(pg, db, sql, len(columns))
    if isinstance(raw, SqlError):
        result.update(status="sql_error", sqlstate=raw.sqlstate, message=raw.message)
        return result
    rows = canonical_rows(columns, raw, case.get("value_only_columns"))
    result.update(status="rows", columns=columns, rows=raw, bag=bag_of(rows))
    if "order_keys" in case:
        result["ordering"] = _ordering_evidence(pg, db, case, sql, columns, rows)
    return result


def _ordering_evidence(pg, db, case, sql, columns, rows) -> dict:
    key_of, in_order = _key_resolver(columns, case["order_keys"])
    keys = [key_of(r) for r in rows]
    if not all(in_order(a, b) for a, b in zip(keys, keys[1:])):
        raise HarnessError(f"{case['name']}: PostgreSQL output is not sorted by the declared order_keys")
    runs = tie_runs(rows, key_of)
    evidence = {"order_keys": case["order_keys"], "run_sizes": [len(r) for r in runs],
                "boundary_run": None}
    limit = case.get("limit")
    if limit is not None and runs:
        m = re.search(rf"\bLIMIT\s+{limit}\s*$", sql, re.I)  # shape checked by check_order_contract
        full = _fetch(pg, db, sql[:m.start()], len(columns))
        if isinstance(full, SqlError):
            raise HarnessError(f"{case['name']}: unlimited query failed: {full.sqlstate}")
        last = key_of(runs[-1][0])
        whole = [r for r in canonical_rows(columns, full, case.get("value_only_columns")) if key_of(r) == last]
        if len(whole) > len(runs[-1]):
            evidence["boundary_run"] = {"taken": len(runs[-1]), "full_bag": bag_of(whole)}
    return evidence


def run_fixture(pg: PgCluster, fixture_path: Path) -> dict:
    """Load one fixture into a fresh database of a running cluster; evidence for every case."""
    fixture = load_json(fixture_path)
    db = "fx_" + re.sub(r"\W", "_", fixture["fixture"])
    pg.fresh_database(db)
    loaded = pg.psql(db, load_script(fixture), single_transaction=True)
    if isinstance(loaded, SqlError):
        raise HarnessError(f"loading {fixture_path} failed: {loaded.sqlstate} {loaded.message}")
    settings = pg.psql(db, "SELECT version(), datcollate, current_setting('TimeZone'), "
                           "current_setting('DateStyle') FROM pg_database "
                           "WHERE datname = current_database();\n")
    if isinstance(settings, SqlError):
        raise HarnessError(f"server settings query failed: {settings.sqlstate} {settings.message}")
    server = dict(zip(("version", "collation", "timezone", "datestyle"), settings.strip().split(SEP)))
    return {"fixture": fixture["fixture"], "path": _display(fixture_path), "server": server,
            "cases": [run_case(pg, db, c) for c in fixture["cases"]]}


def _display(path: Path) -> str:
    p = Path(path).resolve()
    return str(p.relative_to(REPO_ROOT)) if p.is_relative_to(REPO_ROOT) else str(p)


def outcome_ok(case: dict) -> bool:
    return (case["status"] == "sql_error") == (case["expect"] == "error")


# ---------------------------------------------------------------- comparison


def candidate_sqlstate(candidate: dict) -> str:
    """The SQLSTATE a ``sql_error`` candidate claims: ``sqlstate`` or a documented ``error_kind``."""
    if "sqlstate" in candidate:
        state = candidate["sqlstate"]
        if not (isinstance(state, str) and re.fullmatch(r"[0-9A-Z]{5}", state)):
            raise HarnessError(f"candidate sqlstate {state!r} is not a 5-character SQLSTATE")
        return state
    kind = candidate.get("error_kind")
    if kind not in ERROR_KINDS:
        raise HarnessError(f"sql_error candidate needs a sqlstate or an error_kind in {sorted(ERROR_KINDS)}; "
                           f"got {kind!r}")
    return ERROR_KINDS[kind]


def declared_value_only(reference: dict, candidate: dict) -> list[str] | None:
    """The case's ``value_only_columns``: recorded in the evidence, or (for evidence recorded before the key
    existed) passed with the candidate from the fixture. Both present must agree."""
    ref, cand = reference.get("value_only_columns"), candidate.get("value_only_columns")
    if ref is not None and cand is not None and sorted(ref) != sorted(cand):
        raise HarnessError(f"value_only_columns differ: evidence {ref} vs fixture {cand}")
    return ref if ref is not None else cand


def compare_case(reference: dict, candidate: dict) -> tuple[bool, str]:
    """A candidate case (statuses in the module docstring) vs PG evidence.

    Refusals never match; ``sql_error`` matches only PostgreSQL's exact SQLSTATE.
    """
    status = candidate.get("status")
    if status in REFUSAL_STATUSES:
        return False, f"candidate refused ({status}); a refusal is not a SQL outcome"
    if status == "sql_error":
        state = candidate_sqlstate(candidate)
        if reference["status"] != "sql_error":
            return False, f"candidate sql_error {state} vs PostgreSQL rows"
        ok = state == reference["sqlstate"]
        return ok, (f"both sql_error {state}" if ok
                    else f"sql_error {state} vs PostgreSQL {reference['sqlstate']}")
    if status != "rows":
        raise HarnessError(f"candidate status {status!r} unknown; use rows | sql_error | "
                           f"{' | '.join(sorted(REFUSAL_STATUSES))}")
    if reference["status"] == "sql_error":
        return False, f"candidate rows vs PostgreSQL sql_error {reference['sqlstate']}"
    columns = reference["columns"]
    value_only = declared_value_only(reference, candidate)
    rows = canonical_rows(columns, candidate["rows"], value_only)
    if "ordering" not in reference:
        # With value-only columns the reference bag is recomputed from PostgreSQL's rows (older evidence
        # recorded its bag with scales).
        expected = Counter(canonical_rows(columns, reference["rows"], value_only)) if value_only \
            else _bag_counter(reference["bag"])
        ok = Counter(rows) == expected
        return ok, "bag equal" if ok else "bag differs"
    ordering = reference["ordering"]
    key_of, _ = _key_resolver(columns, ordering["order_keys"])
    ref_rows = canonical_rows(columns, reference["rows"], value_only)
    if len(rows) != len(ref_rows):
        return False, f"{len(rows)} rows, expected {len(ref_rows)}"
    start = 0
    sizes = ordering["run_sizes"]
    for n, size in enumerate(sizes):
        ref_run, got = ref_rows[start:start + size], rows[start:start + size]
        start += size
        if any(key_of(r) != key_of(ref_run[0]) for r in got):
            return False, f"tie run {n}: sort keys differ"
        boundary = ordering["boundary_run"]
        if n == len(sizes) - 1 and boundary:
            full = _bag_counter(boundary["full_bag"])
            if value_only:
                full = Counter({tuple(format(Decimal(v).normalize(), "f")
                                      if v is not None and c["name"] in value_only else v
                                      for c, v in zip(columns, r)): n for r, n in full.items()})
            if Counter(got) - full:
                return False, f"tie run {n}: rows outside the boundary tie run"
        elif Counter(got) != Counter(ref_run):
            return False, f"tie run {n}: bag differs"
    return True, "order equal up to ties"


def compare_evidence(evidence: dict, candidate: dict) -> dict:
    """``candidate = {"cases": {name: {...}}}``; one verdict per reference case."""
    verdicts = {}
    for ref in evidence["cases"]:
        got = candidate["cases"].get(ref["name"])
        verdicts[ref["name"]] = ((False, "missing in candidate") if got is None
                                 else compare_case(ref, got))
    return {name: {"match": ok, "detail": d} for name, (ok, d) in verdicts.items()}


# ---------------------------------------------------------------- CLI


def _cmd_run(args) -> int:
    out_dir = Path(args.out) if args.out else Path(args.work_dir) / "evidence"
    out_dir.mkdir(parents=True, exist_ok=True)
    status = EXIT_OK
    with PgCluster(args.work_dir) as pg:
        for path in args.fixtures:
            evidence = run_fixture(pg, Path(path))
            target = out_dir / f"{evidence['fixture']}.reference.json"
            target.write_text(json.dumps(evidence, indent=1) + "\n")
            for case in evidence["cases"]:
                shown = case.get("sqlstate") or f"{len(case.get('rows', []))} rows"
                flag = "ok " if outcome_ok(case) else "BAD"
                print(f"{flag} {evidence['fixture']}/{case['name']}: {case['status']} {shown}")
                if not outcome_ok(case):
                    status = EXIT_SQL
            print(f"wrote {_display(target)}")
    return status


def _cmd_compare(args) -> int:
    verdicts = compare_evidence(load_json(Path(args.reference)), load_json(Path(args.candidate)))
    for name, v in verdicts.items():
        print(f"{'match   ' if v['match'] else 'MISMATCH'} {name}: {v['detail']}")
    return EXIT_OK if all(v["match"] for v in verdicts.values()) else EXIT_MISMATCH


def _cmd_stop(args) -> int:
    PgCluster(args.work_dir).stop()
    return EXIT_OK


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--work-dir", default=str(DEFAULT_WORK_DIR))
    sub = parser.add_subparsers(dest="command", required=True)
    run = sub.add_parser("run", help="record PostgreSQL evidence for fixtures")
    run.add_argument("fixtures", nargs="+")
    run.add_argument("--out", help="evidence directory (default <work-dir>/evidence)")
    run.set_defaults(func=_cmd_run)
    cmp_ = sub.add_parser("compare", help="compare a candidate answer with evidence")
    cmp_.add_argument("reference")
    cmp_.add_argument("candidate")
    cmp_.set_defaults(func=_cmd_compare)
    stop = sub.add_parser("stop", help="stop the private cluster if it is running")
    stop.set_defaults(func=_cmd_stop)
    args = parser.parse_args(argv)
    try:
        return args.func(args)
    except (HarnessError, KeyError, OSError) as e:
        print(f"harness failure: {type(e).__name__}: {e}", file=sys.stderr)
        return EXIT_HARNESS


if __name__ == "__main__":
    sys.exit(main())
