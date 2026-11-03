#!/usr/bin/env python3
"""Generate the data of the workload `anyschema` (the tables, columns and keys of `schema.sql` beside this script).

Usage: python3 generate.py DIR      (setup_data.sh runs it with DIR = data/tiny)

Writes, refusing an existing DIR:
- DIR/<table>.parquet: the rows GenDB imports, one file per table;
- DIR/MANIFEST.json: row counts, files and `original_data_bytes`: the size of the same rows as '|'-delimited text (a
  NULL as an empty field, every line ending in '|'; the form of TPC-H's generator text), which GenDB takes as the
  default storage budget.

Deterministic: the rows come from this script's own pseudo-random generator (splitmix64, fixed seed), and the Parquet
files from fixed writer options, so two runs with the same pyarrow version write the same bytes. The rows hold the
fixture's edge values: int4 and int8 minimum and maximum, negative numerics, numeric(38,6) values with 128-bit
coefficients (up to 10^37 - 1), dates before 1970, on 1970-01-01, 2000-01-01 and leap days, empty text, multibyte
UTF-8, trailing spaces, duplicate keys for grouping, NULLs in nullable foreign-key children, an all-NULL column
(`ev_memo`) and an empty table (`ax_void`). The declared keys hold (checked before writing). Products stay small
(`ax_item` x `ax_kind` x `ax_owner` = 480,000 tuples), so GenDB's version 0 (the verified interpreter) answers every
template within the call limit.
"""
import datetime as dt
import decimal
import json
import os
import re
import sys

import pyarrow as pa
import pyarrow.parquet as pq



def read_schema(path):
    """The tables of `schema.sql` as (table, [(column, SQL type, nullable)]) in table and column order, and its keys
    as (table, clause) in file order: `CREATE TABLE t (col type [NOT NULL], ...);` then `ALTER TABLE t ADD clause;`."""
    schema, constraints = [], []
    with open(path) as f:
        statements = [s.strip() for s in f.read().split(";") if s.strip()]
    for statement in statements:
        create = re.fullmatch(r"CREATE TABLE (\w+) \((.*)\)", statement, re.S)
        alter = re.fullmatch(r"ALTER TABLE (\w+) ADD (.*)", statement, re.S)
        if create:
            columns = [re.fullmatch(r"(\w+) (\S+)( NOT NULL)?", c.strip()).groups() for c in create[2].split(",\n")]
            schema.append((create[1], [(name, sql_type, not_null is None) for name, sql_type, not_null in columns]))
        elif alter:
            constraints.append((alter[1], alter[2]))
        else:
            sys.exit(f"schema.sql: {statement[:60]!r} is neither CREATE TABLE nor ALTER TABLE ... ADD")
    return schema, constraints


SCHEMA, CONSTRAINTS = read_schema(os.path.join(os.path.dirname(os.path.abspath(__file__)), "schema.sql"))


def numeric_precision_scale(sql_type):
    """(p, s) of `numeric(p,s)`; None for every other type."""
    if not sql_type.startswith("numeric("):
        return None
    p, s = sql_type[len("numeric("):-1].split(",")
    return int(p), int(s)

SEED = 0x6E64_6162_7365_6378  # fixed; changing it changes every row
MASK = (1 << 64) - 1
INT4 = (-(1 << 31), (1 << 31) - 1)
INT8 = (-(1 << 63), (1 << 63) - 1)
EPOCH = dt.date(1970, 1, 1)


class Rand:
    """splitmix64: a small, portable, deterministic generator (no dependence on Python's `random`)."""

    def __init__(self, seed):
        self.state = seed & MASK

    def next(self):
        self.state = (self.state + 0x9E3779B97F4A7C15) & MASK
        z = self.state
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK
        return z ^ (z >> 31)

    def below(self, n):
        """An integer in [0, n), from as many 64-bit words as n needs (so 128-bit coefficients are reached)."""
        value, bits = 0, 0
        while (1 << bits) < n:
            value, bits = (value << 64) | self.next(), bits + 64
        return value % n

    def between(self, low, high):
        """An integer in [low, high]."""
        return low + self.below(high - low + 1)

    def pick(self, values):
        return values[self.below(len(values))]

    def signed(self):
        return -1 if self.below(2) else 1


def decimal_of(coefficient, scale):
    """The exact decimal `coefficient` x 10^-scale (a context wide enough that 38 digits are never rounded)."""
    return decimal.Decimal(coefficient).scaleb(-scale, decimal.Context(prec=80))


def day(r, low=dt.date(1900, 1, 1), high=dt.date(2030, 12, 31)):
    return low + dt.timedelta(days=r.between(0, (high - low).days))


def owners(r):
    ids = [INT8[0]] + list(range(1, 99)) + [INT8[1]]
    names = {1: "", 2: "Zürich", 3: "λ猫", 4: "ab  ", 5: "dup", 6: "dup", 7: "dup", 8: "ab"}
    born = {10: dt.date(1970, 1, 1), 11: dt.date(2000, 1, 1), 12: dt.date(2000, 2, 29), 13: dt.date(2024, 2, 29), 14: dt.date(1969, 12, 31), 15: dt.date(1900, 3, 1)}
    credit = {20: 999999999999999, 21: -999999999999999, 22: 0, 23: -1}  # in cents: numeric(15,2) extremes, zero, -0.01
    codes = {30: "AB  ", 31: "AB", 32: "", 33: "C007", 34: "C007"}
    rows = []
    for i, owner_id in enumerate(ids):
        rank = None if i % 7 == 3 else r.between(-50, 50)
        rank = {40: INT4[0], 41: INT4[1]}.get(i, rank)
        birth = None if i % 9 == 4 else born.get(i, day(r))
        cents = credit.get(i, r.between(-100_000_000, 100_000_000))
        if i % 5 == 2:
            weight = None
        elif i == 50:
            weight = decimal_of(10**37 - 1, 6)  # the largest numeric(38,6) coefficient
        elif i == 51:
            weight = decimal_of(-(10**36 + 7), 6)
        elif birth is None:
            weight = decimal_of(r.below(10**35), 6)  # the NULL-born group's weights are positive: no cancellation in AVG
        elif i % 3 == 0:
            weight = decimal_of(r.signed() * r.below(10**35), 6)
        else:
            weight = decimal_of(r.signed() * r.below(10**9), 6)
        note = None if i % 3 == 1 else r.pick(["", "note", "Ünïcode note", "trailing  ", "dup"])
        rows.append([owner_id, names.get(i, f"owner {i:03d}"), rank, birth, decimal_of(cents, 2), weight, note, codes.get(i, f"C{r.below(40):03d}")])
    return rows


KINDS = ["k00", "k01", "k02", "k03", "k04", "k05", "k06", "k07", "k08", "k09", "", "λ猫"]


def kinds(_r):
    groups = ["g1", "g2", "g3", "g1", "", "g2", "g3", "g1", "g4", "g2", "g3", "g1"]
    weights = [5, None, 7, 5, -3, None, INT4[1], 0, 7, INT4[0], None, 12]
    return [[code, group, weight] for code, group, weight in zip(KINDS, groups, weights)]


def items(r, owner_rows):
    """400 items over the owners from the 11th on (the first ten have none: LEFT JOIN anti matches); `k09` is never
    used (a kind without items)."""
    owner_ids = [row[0] for row in owner_rows]
    counts = [0] * len(owner_ids)
    while sum(counts) < 400:
        i = r.between(10, len(owner_ids) - 1)
        if counts[i] < 9:
            counts[i] += 1
    leap_days = [dt.date(2000, 2, 29), dt.date(2004, 2, 29), dt.date(2024, 2, 29), dt.date(1970, 1, 1), dt.date(2000, 1, 1)]
    rows, n = [], 0
    for i, count in enumerate(counts):
        for line in range(1, count + 1):
            line_no = {(50, 1): INT4[1], (51, 1): INT4[0]}.get((i, line), line)
            qty = decimal_of(r.signed() * r.below(10**10), 4) if n % 17 else decimal_of(1, 4)
            price = None if n % 6 == 5 else decimal_of(r.signed() * r.below(10**20), 4)
            when = leap_days[n % len(leap_days)] if n % 37 == 0 else day(r, dt.date(1970, 1, 1))
            tiny = None if n % 4 == 3 else decimal_of(r.between(-999, 999), 0)
            rows.append([owner_ids[i], line_no, r.pick(KINDS[:9] + KINDS[10:]), qty, price, when, r.pick(["A", "B", "N", "R", "", "é"]), tiny])
            n += 1
    return rows


def events(r, item_rows):
    keys = [(row[0], row[1]) for row in item_rows]
    rows = []
    for i in range(300):
        owner, line = r.pick(keys)
        shape = i % 10
        if shape == 0:
            owner, line = None, None  # both key columns NULL: exempt from the foreign key
        elif shape == 1:
            line = None  # one key column NULL: exempt too (MATCH SIMPLE)
        elif shape == 2:
            owner = None
        at = None if i % 4 == 1 else day(r, dt.date(1990, 1, 1))
        amount = None if i % 3 == 2 else decimal_of(r.signed() * r.below(10**17), 9)
        rows.append([3 * i + 1, owner, line, at, amount, None])
    return rows


def check_keys(tables):
    """The declared keys hold: primary keys unique and NOT NULL, every foreign key with no NULL column matches."""
    columns = {t: [c[0] for c in cs] for t, cs in SCHEMA}
    for table, sql in CONSTRAINTS:
        kind, rest = sql.split(" KEY (", 1)
        key = [c.strip() for c in rest.split(")", 1)[0].split(",")]
        at = [columns[table].index(c) for c in key]
        values = [tuple(row[i] for i in at) for row in tables[table]]
        if kind == "PRIMARY":
            assert all(None not in v for v in values) and len(set(values)) == len(values), sql
        else:
            target, target_columns = rest.split("REFERENCES ", 1)[1].split(" (", 1)
            target_at = [columns[target].index(c.strip()) for c in target_columns.rstrip(")").split(",")]
            present = {tuple(row[i] for i in target_at) for row in tables[target]}
            assert all(None in v or v in present for v in values), sql


def arrow_type(sql_type):
    numeric = numeric_precision_scale(sql_type)
    if numeric:
        return pa.decimal128(*numeric)
    return {"integer": pa.int32(), "bigint": pa.int64(), "date": pa.date32(), "text": pa.string()}[sql_type]


def text_field(value):
    if value is None:
        return ""
    if isinstance(value, dt.date):
        return value.isoformat()
    return str(value)


def main():
    (data,) = sys.argv[1:]
    if os.path.exists(data):
        sys.exit(f"{data} exists: the generator never overwrites data")
    r = Rand(SEED)
    tables = {"ax_owner": owners(r), "ax_kind": kinds(r)}
    tables["ax_item"] = items(r, tables["ax_owner"])
    tables["ax_event"] = events(r, tables["ax_item"])
    tables["ax_void"] = []
    check_keys(tables)
    os.makedirs(data)
    manifest = {"format": "gendb.anyschema.data.v1", "generator": "generate.py", "seed": hex(SEED), "pyarrow": pa.__version__, "tables": {}}
    for table, columns in SCHEMA:
        rows = tables[table]
        schema = pa.schema([pa.field(name, arrow_type(sql_type), nullable) for name, sql_type, nullable in columns])
        arrays = [pa.array([row[i] for row in rows], type=schema.field(i).type) for i in range(len(columns))]
        parquet = os.path.join(data, f"{table}.parquet")
        pq.write_table(pa.Table.from_arrays(arrays, schema=schema), parquet, compression="zstd", version="2.6", write_statistics=True, use_dictionary=True)
        lines = "".join("|".join(text_field(v) for v in row) + "|\n" for row in rows)
        manifest["tables"][table] = {"rows": len(rows), "parquet": f"{table}.parquet", "text_bytes": len(lines.encode("utf-8"))}
    manifest["original_data_bytes"] = sum(t["text_bytes"] for t in manifest["tables"].values())
    manifest["meaning"] = ("the data of anyschema: its rows as Parquet (what GenDB imports); original_data_bytes is the size of the same rows as "
                           "'|'-delimited text (text_bytes per table)")
    with open(os.path.join(data, "MANIFEST.json"), "w") as f:
        json.dump(manifest, f, indent=1, sort_keys=True)
        f.write("\n")
    print(json.dumps({t: m["rows"] for t, m in manifest["tables"].items()}), manifest["original_data_bytes"])


if __name__ == "__main__":
    main()
