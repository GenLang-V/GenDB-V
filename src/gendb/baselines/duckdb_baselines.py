#!/usr/bin/env python3
"""DuckDB baselines of a GenDB workload: runtime targets and saved answers (`compare_with = "duckdb"`, README.md).

Usage: duckdb_baselines.py REQUEST.json BINDINGS.json OUT_DIR [--timed all|none|BINDING] [--threads 1,8]

REQUEST.json is a GenDB request (format 2): its `dataset` (tables, column types, NOT NULL, Parquet `locations`), its
`integrity_constraints` (declared keys and CHECKs), its `queries` (`name`, `sql`, `parameters`), `hardware.threads`
(unless `--threads`) and `barriers` (the host's three lock files). BINDINGS.json lists the example bindings per query
name (`{"queries": {NAME: [{"binding_id": "v0", "arguments": [...]}]}}`, argument texts of the free parameters in
`$n` order); a statement without parameters needs no entry (its one binding is `v0`, without arguments).

`--timed` says which bindings are timed: `all` (default), `none` (answers only) or one binding name (the engine's
timing binding). Each timed (query, binding, thread count) is one block: a fresh read-only connection, `SET threads`,
`PREPARE`, 1 warm and 3 hot `EXECUTE` + fetch, the median of the hot calls, all under the host's exclusive timing
lease (GenDB's protocol: the activity, build and race locks, with the activity lock's timing gate). Loading and
untimed answers hold the shared activity lease.

Writes, in OUT_DIR (existing blocks and answers are kept, so a rerun only does what is missing):
- duckdb.db and load.json: the store (deletable; loaded again when load.json is missing);
- blocks/duckdb/<query>/<binding>-t<threads>.json: one block's times and warm result;
- answers/duckdb/<query>/<binding>.json: the answer at each binding (rows at `/run/result`), the warm result of its
  first block or one untimed run;
- targets.json: `{query: {binding: {threads: {duckdb_ms, target_ms, agreement: "single_engine"}}}}` and
  `baseline_setting`, the form `gendb benchmark-inputs` reads;
- baselines.json: the targets file and, per engine, its name, description and answers path pattern (the form GenDB's
  workload folders read, `workload_folder::requests::Baselines`).

Exit 0 when every query ran at every binding, 1 when DuckDB refused some (each listed on stderr, its record kept with
`ok: false`), 2 for a usage error. Requires the Python package duckdb 1.5.6 exactly.
"""
import argparse
import datetime as dt
import decimal
import fcntl
import json
import os
import statistics
import sys
import time

DUCKDB_VERSION = "1.5.6"
# PostgreSQL's meaning, which SQLSpec follows: `/` of two integers truncates, NULLs sort last ascending and first
# descending, and text compares by its bytes (`nfc`: the NFC normal form's bytes; equal to the byte order on NFC text).
SETTINGS = {"integer_division": "true", "default_null_order": "'postgres'", "default_collation": "'nfc'"}
SETTING_TEXT = f"DuckDB {DUCKDB_VERSION} (integer_division, default_null_order postgres, default_collation nfc), keys declared"
DESCRIPTION = (f"DuckDB {DUCKDB_VERSION} (Python), integer_division, default_null_order 'postgres', default_collation 'nfc', "
               "declared keys, tables loaded from the workload's Parquet files; warm result of a block "
               "(GenDB baselines/duckdb_baselines.py)")
HOT_CALLS = 3
GATE_AFTER_SECONDS = 60
SQL_TYPES = {"I32": "INTEGER", "I64": "BIGINT", "Date32": "DATE", "Utf8": "VARCHAR", "Bool": "BOOLEAN"}


class Refused(Exception):
    """An input this helper cannot use, with the reason."""


# ---------------------------------------------------------------- host leases (GenDB's `query::host_locks`) --------

class Lease:
    """Held flock locks; released on exit."""

    def __init__(self, barriers, exclusive):
        self.barriers, self.exclusive, self.files = barriers, exclusive, []

    def _lock(self, path, mode):
        os.makedirs(os.path.dirname(path), exist_ok=True)
        f = open(path, "a+")
        fcntl.flock(f.fileno(), mode)
        self.files.append(f)
        return f

    def __enter__(self):
        activity, gate = self.barriers["activity_lock"], self.barriers["activity_lock"] + ".gate"
        if not self.exclusive:
            gate_file = self._lock(gate, fcntl.LOCK_SH)
            self._lock(activity, fcntl.LOCK_SH)
            self.files.remove(gate_file)
            gate_file.close()
            return self
        started = time.monotonic()
        while True:  # wait for the machine without the gate first, then close the gate
            f = open(activity, "a+")
            try:
                fcntl.flock(f.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                self.files.append(f)
                break
            except BlockingIOError:
                f.close()
            if time.monotonic() - started >= GATE_AFTER_SECONDS:
                self._lock(gate, fcntl.LOCK_EX)
                self._lock(activity, fcntl.LOCK_EX)
                break
            time.sleep(0.05)
        self._lock(self.barriers["build_lock"], fcntl.LOCK_EX)
        self._lock(self.barriers["race_lock"], fcntl.LOCK_EX)
        return self

    def __exit__(self, *_):
        for f in reversed(self.files):
            f.close()


# ---------------------------------------------------------------- the store ----------------------------------------

def column_type(ty):
    if isinstance(ty, dict) and "Decimal" in ty:
        return f"DECIMAL({ty['Decimal']['p']},{ty['Decimal']['s']})"
    if ty in SQL_TYPES:
        return SQL_TYPES[ty]
    raise Refused(f"column type {ty!r} has no DuckDB type here")


def references(clause):
    """The table a FOREIGN KEY clause references (None for other clauses)."""
    words = clause.replace("(", " ( ").split()
    upper = [w.upper() for w in words]
    return words[upper.index("REFERENCES") + 1] if "FOREIGN" in upper and "REFERENCES" in upper else None


def create_statements(request):
    """CREATE TABLE per table with its declared clauses as table constraints, every referenced table first (DuckDB
    accepts foreign keys only in CREATE TABLE)."""
    tables = request["dataset"]["tables"]
    clauses = {t["name"]: [] for t in tables}
    for declaration in (request.get("integrity_constraints") or {}).get("declarations", []):
        if declaration["table"] not in clauses:
            raise Refused(f"integrity constraint on unknown table {declaration['table']}")
        clauses[declaration["table"]].append(declaration["sql"])
    ordered, placed = [], set()
    while len(ordered) < len(tables):
        ready = [t for t in tables if t["name"] not in placed
                 and all(r in placed or r == t["name"] for r in filter(None, map(references, clauses[t["name"]])))]
        if not ready:
            raise Refused("the foreign keys form a cycle; DuckDB needs every referenced table created first")
        for t in ready:
            placed.add(t["name"])
            ordered.append(t)
    statements = []
    for t in ordered:
        columns = [f"{f['name']} {column_type(f['ty'])}{'' if f['nullable'] else ' NOT NULL'}" for f in t["fields"]]
        statements.append((t, f"CREATE TABLE {t['name']} ({', '.join(columns + clauses[t['name']])})"))
    return statements


def configure(connection, threads):
    connection.execute(f"SET threads = {threads}")
    connection.execute("SET enable_progress_bar = false")
    for name, value in SETTINGS.items():
        connection.execute(f"SET {name} = {value}")


def load(duckdb, request, out):
    """The store OUT/duckdb.db, loaded once (load.json written last marks it complete)."""
    store, record = os.path.join(out, "duckdb.db"), os.path.join(out, "load.json")
    if os.path.exists(record) and os.path.exists(store):
        return store
    for stale in (store, store + ".wal"):
        if os.path.exists(stale):
            os.remove(stale)
    os.makedirs(out, exist_ok=True)
    started = time.time()
    connection = duckdb.connect(store)
    try:
        configure(connection, os.cpu_count() or 1)
        rows = {}
        for table, create in create_statements(request):
            connection.execute(create)
            names = ", ".join(f["name"] for f in table["fields"])
            files = ", ".join("'" + p.replace("'", "''") + "'" for p in table["locations"])
            connection.execute(f"INSERT INTO {table['name']} ({names}) SELECT {names} FROM read_parquet([{files}])")
            rows[table["name"]] = connection.execute(f"SELECT COUNT(*) FROM {table['name']}").fetchone()[0]
        connection.execute("CHECKPOINT")
    finally:
        connection.close()
    write_json(record, {"engine": "duckdb", "version": duckdb.__version__, "rows": rows, "seconds": round(time.time() - started, 3)})
    return store


# ---------------------------------------------------------------- statements and bindings --------------------------

def literal(text, sql_type):
    """The SQL literal of one argument text of a parameter of `sql_type`."""
    sql_type = sql_type.lower()
    if sql_type == "date":
        dt.date.fromisoformat(text)
        return f"DATE '{text}'"
    if sql_type in ("integer", "int", "int4", "bigint", "int8"):
        value = str(int(text))
    elif sql_type.startswith(("numeric", "decimal")):
        decimal.Decimal(text)
        value = text
    elif sql_type == "text":
        return "'" + text.replace("'", "''") + "'"
    else:
        raise Refused(f"parameter type {sql_type} is not supported")
    return f"({value})" if value.startswith("-") else value


def bind(sql, parameters, arguments):
    """`sql` with every `$k` outside quotes replaced by the typed literal of its value: a fixed parameter's own value,
    a free one's argument (free parameters in ascending `$k` order)."""
    by_index = {p["index"]: p for p in parameters}
    free = sorted(i for i, p in by_index.items() if "free" in p["binding"])
    if len(free) != len(arguments):
        raise Refused(f"{len(arguments)} arguments for {len(free)} free parameters")
    values = {i: arguments[free.index(i)] if i in free else by_index[i]["binding"]["fixed"] for i in by_index}
    out, i, quote = [], 0, None
    while i < len(sql):
        c = sql[i]
        if quote:
            out.append(c)
            quote = None if c == quote else quote
            i += 1
        elif c in "'\"":
            quote = c
            out.append(c)
            i += 1
        elif c == "$" and i + 1 < len(sql) and sql[i + 1].isdigit():
            j = i + 1
            while j < len(sql) and sql[j].isdigit():
                j += 1
            k = int(sql[i + 1:j])
            if k not in values:
                raise Refused(f"${k} is not a declared parameter")
            out.append(literal(values[k], by_index[k]["type"]))
            i = j
        else:
            out.append(c)
            i += 1
    return "".join(out).strip().rstrip(";")


def encoded(value):
    """A DuckDB value in GenDB's saved-answer encoding."""
    if isinstance(value, decimal.Decimal):
        return {"dec": str(value)}
    if isinstance(value, float):
        return {"f64": repr(value)}
    if isinstance(value, (dt.date, dt.datetime)):
        return {"date": value.isoformat()}
    return value


def bindings_of(query, listed):
    if query["name"] in listed:
        return listed[query["name"]]
    if not any("free" in p["binding"] for p in query.get("parameters", [])):
        return [{"binding_id": "v0", "arguments": []}]
    raise Refused(f"no bindings for {query['name']} in the bindings file")


# ---------------------------------------------------------------- runs ---------------------------------------------

def block(duckdb, store, sql, threads):
    """One timed block: (session, warm_ms, hot_ms, warm rows)."""
    connection = duckdb.connect(store, read_only=True)
    try:
        configure(connection, threads)
        connection.execute("PREPARE q AS " + sql)
        times, rows = [], None
        for call in range(1 + HOT_CALLS):
            started = time.perf_counter_ns()
            result = connection.execute("EXECUTE q").fetchall()
            times.append((time.perf_counter_ns() - started) / 1e6)
            if call == 0:
                rows = [[encoded(v) for v in row] for row in result]
        return times[0], times[1:], rows
    finally:
        connection.close()


def untimed(duckdb, store, sql, threads):
    connection = duckdb.connect(store, read_only=True)
    try:
        configure(connection, threads)
        return [[encoded(v) for v in row] for row in connection.execute(sql).fetchall()]
    finally:
        connection.close()


def write_json(path, doc):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    partial = path + ".partial"
    with open(partial, "w") as f:
        json.dump(doc, f, ensure_ascii=False)
        f.write("\n")
    os.replace(partial, path)


def read_ok(path):
    """An existing record with `ok: true`, else None (a missing or refused record is done again)."""
    try:
        with open(path) as f:
            doc = json.load(f)
        return doc if doc.get("ok") else None
    except FileNotFoundError:
        return None


def main(argv):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("request")
    parser.add_argument("bindings")
    parser.add_argument("out")
    parser.add_argument("--timed", default="all")
    parser.add_argument("--threads")
    args = parser.parse_args(argv)
    try:
        import duckdb
    except ImportError:
        print(f"duckdb_baselines: the Python package duckdb {DUCKDB_VERSION} is missing (pip install duckdb=={DUCKDB_VERSION})", file=sys.stderr)
        return 2
    if duckdb.__version__ != DUCKDB_VERSION:
        print(f"duckdb_baselines: duckdb {duckdb.__version__} found, {DUCKDB_VERSION} required (pip install duckdb=={DUCKDB_VERSION})", file=sys.stderr)
        return 2
    with open(args.request) as f:
        request = json.load(f)
    with open(args.bindings) as f:
        listed = json.load(f)["queries"]
    threads = [int(t) for t in args.threads.split(",")] if args.threads else request["hardware"]["threads"]
    out = os.path.abspath(args.out)
    barriers = request["barriers"]
    session = {"engine": "duckdb", "version": duckdb.__version__, "settings": SETTINGS}
    with Lease(barriers, exclusive=False):
        store = load(duckdb, request, out)
    targets, failures = {"baseline_setting": SETTING_TEXT}, []
    for query in request["queries"]:
        name = query["name"]
        for binding in bindings_of(query, listed):
            b = binding["binding_id"]
            answer_path = os.path.join(out, "answers", "duckdb", name, f"{b}.json")
            base = {"engine": "duckdb", "query": name, "binding_id": b, "arguments": binding["arguments"], "session": session}
            try:
                sql = bind(query["sql"], query.get("parameters", []), binding["arguments"])
            except (Refused, ValueError) as error:
                failures.append(f"{name} {b}: {error}")
                continue
            base["sql"] = sql
            timed = args.timed == "all" or args.timed == b
            for workers in threads if timed else []:
                path = os.path.join(out, "blocks", "duckdb", name, f"{b}-t{workers}.json")
                record = read_ok(path)
                if record is None:
                    try:
                        with Lease(barriers, exclusive=True):
                            warm, hot, rows = block(duckdb, store, sql, workers)
                        record = {**base, "threads": workers, "ok": True, "error": None, "warm_ms": round(warm, 3),
                                  "hot_ms": [round(t, 3) for t in hot], "median_ms": round(statistics.median(hot), 3), "run": {"result": rows}}
                    except duckdb.Error as error:
                        record = {**base, "threads": workers, "ok": False, "error": str(error)}
                    write_json(path, record)
                if not record["ok"]:
                    failures.append(f"{name} {b} at {workers} threads: {record['error']}")
                    continue
                cell = {"duckdb_ms": record["median_ms"], "target_ms": record["median_ms"], "agreement": "single_engine"}
                targets.setdefault(name, {}).setdefault(b, {})[str(workers)] = cell
                if read_ok(answer_path) is None:
                    write_json(answer_path, {**base, "ok": True, "error": None, "threads": workers, "run": record["run"]})
            if not timed and read_ok(answer_path) is None:
                try:
                    with Lease(barriers, exclusive=False):
                        rows = untimed(duckdb, store, sql, threads[0])
                    write_json(answer_path, {**base, "ok": True, "error": None, "threads": threads[0], "run": {"result": rows}})
                except duckdb.Error as error:
                    write_json(answer_path, {**base, "ok": False, "error": str(error)})
                    failures.append(f"{name} {b}: {error}")
    write_json(os.path.join(out, "targets.json"), targets)
    write_json(os.path.join(out, "baselines.json"), {
        "targets": "targets.json", "engines": [{"name": "duckdb", "description": DESCRIPTION, "answers": "answers/duckdb/{query}/{binding}.json"}]})
    for failure in failures:
        print(f"duckdb_baselines: {failure}", file=sys.stderr)
    print(json.dumps({"out": out, "queries": len(request["queries"]), "failures": len(failures)}))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.dont_write_bytecode = True
    try:
        sys.exit(main(sys.argv[1:]))
    except Refused as error:
        print(f"duckdb_baselines: {error}", file=sys.stderr)
        sys.exit(2)
