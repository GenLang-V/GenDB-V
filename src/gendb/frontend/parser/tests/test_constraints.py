"""Integrity constraints in the schema DDL (``features/constraints.py``, ``schema.py``)."""

from __future__ import annotations

import json

import pytest

from gendb_sql_frontend.api import dumps, translate
from gendb_sql_frontend.refusal import Refusal
from gendb_sql_frontend.schema import load_schema
from support import FIXTURES, REPO, TPCH_SCHEMA

CONSTRAINTS_DDL = (FIXTURES / "constraints/cov_c_schema.sql").read_text()


def constraints(ddl: str) -> dict[str, list[dict]]:
    return {t["name"]: t["constraints"] for t in load_schema(ddl, "postgres").to_json()["tables"]}


def brief(c: dict) -> tuple:
    if c["kind"] == "key":
        return ("pk" if c["primary"] else "unique", tuple(c["columns"]), c["nulls_distinct"])
    if c["kind"] == "foreign_key":
        return ("fk", tuple(c["columns"]), c["table"], tuple(c["ref_columns"]), c["match_full"])
    return ("check", c["nodes"][c["root"]]["tag"])


def test_tpch_keys_and_references_are_recorded():
    cs = {t: [brief(c) for c in v] for t, v in constraints(TPCH_SCHEMA).items()}
    assert cs["nation"] == [("pk", (0,), True)]
    assert cs["supplier"] == [("pk", (0,), True), ("fk", (3,), 0, (0,), False)]
    assert cs["partsupp"] == [("fk", (0,), 3, (0,), False), ("fk", (1,), 2, (0,), False), ("pk", (0, 1), True)]
    # lineitem: FK to orders, composite PK, composite FK to partsupp's composite PK.
    assert cs["lineitem"] == [("fk", (0,), 6, (0,), False), ("pk", (0, 3), True), ("fk", (1, 2), 4, (0, 1), False)]
    assert sum(len(v) for v in cs.values()) == 15  # 8 primary keys, 7 foreign keys


def test_primary_key_columns_become_not_null():
    t = load_schema("CREATE TABLE t (a integer, b integer, c integer, PRIMARY KEY (b, a))", "postgres").tables[0]
    assert [c.ty.nullable for c in t.columns] == [False, False, True]
    assert brief(t.constraints[0].to_json()) == ("pk", (1, 0), True)


def test_fixture_schema_constraints():
    cs = {t: [brief(c) for c in v] for t, v in constraints(CONSTRAINTS_DDL).items()}
    assert cs["uq"][1] == ("unique", (1, 2), True)
    assert cs["uqn"][1] == ("unique", (1, 2), False)  # NULLS NOT DISTINCT
    assert cs["fkf"][1] == ("fk", (2, 1), 0, (1, 0), True)  # (y, x) -> pk2 (b, a) MATCH FULL
    assert cs["emp"][1] == ("fk", (1,), 6, (0,), False)  # self reference to its own primary key
    assert [c[0] for c in cs["ck"]] == ["pk", "check", "check", "check"]
    raw = constraints(CONSTRAINTS_DDL)
    fkf = raw["fkf"][1]
    assert (fkf["name"], fkf["on_delete"], fkf["on_update"]) == ("fkf_full", "cascade", "no_action")
    emp = raw["emp"][1]
    assert (emp["deferrable"], emp["initially_deferred"]) == (True, True)


def test_check_is_a_pred_arena_over_the_row():
    t = load_schema("CREATE TABLE t (a integer CHECK (a > b), b integer, CHECK (t.b IS NOT NULL OR a < 3))",
                    "postgres").to_json()["tables"][0]
    c1, c2 = t["constraints"]
    assert c1["nodes"][c1["root"]] == {"id": c1["root"], "tag": "Cmp", "op": "Gt", "a": 0, "b": 1}
    assert [n["index"] for n in c1["nodes"] if n["tag"] == "Col"] == [0, 1]
    assert c2["nodes"][c2["root"]]["tag"] == "Or"


def test_documents_carry_constraints_deterministically():
    q = "SELECT a, b, v FROM pk2"
    d1, d2 = translate(q, CONSTRAINTS_DDL, "postgres"), translate(q, CONSTRAINTS_DDL, "postgres")
    assert d1["status"] == "ok" and dumps(d1) == dumps(d2)
    assert d1["frontend"]["identity"] == "gendb-sql-frontend-v4"
    assert all("constraints" in t for t in d1["schema"]["tables"])


@pytest.mark.parametrize("ddl,reason", [
    ("CREATE TABLE p (a int PRIMARY KEY); CREATE TABLE c (x int REFERENCES p MATCH PARTIAL)", "fk_match_partial"),
    ("CREATE TABLE p (a char(3) PRIMARY KEY); CREATE TABLE c (x varchar(3) REFERENCES p)", "fk_bpchar_coercion"),
    ("CREATE TABLE p (a char(3) PRIMARY KEY); CREATE TABLE c (x text REFERENCES p)", "fk_bpchar_coercion"),
    ("CREATE TABLE p (a int PRIMARY KEY); CREATE TABLE c (x numeric(5,0) REFERENCES p)", "fk_type_mismatch"),
    ("CREATE TABLE p (a int PRIMARY KEY); CREATE TABLE c (x date REFERENCES p)", "fk_type_mismatch"),
    ("CREATE TABLE p (a int, b int PRIMARY KEY); CREATE TABLE c (x int REFERENCES p (a))", "fk_no_matching_key"),
    ("CREATE TABLE p (a int UNIQUE); CREATE TABLE c (x int REFERENCES p)", "fk_no_matching_key"),
    ("CREATE TABLE p (a int, b int, UNIQUE (a, b)); CREATE TABLE c (x int, FOREIGN KEY (x, x) REFERENCES p (a, a))", "fk_no_matching_key"),
    ("CREATE TABLE p (a int, b int, PRIMARY KEY (a, b)); CREATE TABLE c (x int REFERENCES p)", "fk_arity"),
    # PostgreSQL 18.3 (target/pg-evidence/verus-sql-cov-c-review/probe.result.json): 55000.
    ("CREATE TABLE p (k integer NOT NULL, UNIQUE (k) DEFERRABLE); CREATE TABLE c (k integer REFERENCES p (k))", "fk_deferrable_key"),
    ("CREATE TABLE p (k integer PRIMARY KEY DEFERRABLE INITIALLY DEFERRED); CREATE TABLE c (k integer REFERENCES p)", "fk_deferrable_key"),
    ("CREATE TABLE c (x int REFERENCES p); CREATE TABLE p (a int PRIMARY KEY)", "fk_unknown_table"),
    ("CREATE TABLE p (a int PRIMARY KEY); CREATE TABLE c (x int REFERENCES p (z))", "unknown_column"),
    ("CREATE TABLE t (a int PRIMARY KEY, b int, PRIMARY KEY (b))", "multiple_primary_keys"),
    ("CREATE TABLE t (a int, UNIQUE (a, a))", "duplicate_key_column"),
    ("CREATE TABLE t (a int NULL PRIMARY KEY)", "invalid_schema"),
    ("CREATE TABLE t (a int NULL NOT NULL)", "invalid_schema"),
    ("CREATE TABLE t (a int, PRIMARY KEY (a DESC))", "unsupported_constraint"),
    ("CREATE TABLE t (a int DEFAULT 1)", "unsupported_constraint"),
    ("CREATE TABLE p (a int PRIMARY KEY); CREATE TABLE c (x int REFERENCES p NOT ENFORCED)", "constraint_not_enforced"),
    ("CREATE TABLE t (a int CHECK (a IN (SELECT 1)))", "check_subquery"),
    ("CREATE TABLE t (a int CHECK (EXISTS (SELECT 1)))", "check_subquery"),
    ("CREATE TABLE t (a int CHECK (a > (SELECT 1)))", "check_subquery"),
    ("CREATE TABLE t (a int CHECK (count(*) > 0))", "aggregate_misplaced"),
    ("CREATE TABLE t (a int CHECK (a + 1))", "type_mismatch"),
    ("CREATE TABLE t (a int CHECK (b > 0))", "unknown_column"),
    ("CREATE TABLE t (a int, UNIQUE (a) INCLUDE (a))", "parse_error"),
    ("CREATE TABLE t (a int CHECK (a > 0) NO INHERIT)", "parse_error"),
])
def test_unsupported_or_invalid_constraints_are_named_refusals(ddl, reason):
    with pytest.raises(Refusal) as e:
        load_schema(ddl, "postgres")
    assert e.value.reason == reason


def test_accepted_forms_postgres_also_accepts():
    # Probe target/pg-evidence/verus-sql-cov-c/probe/pg_probe.result.json: repeated referencing columns, permuted referenced
    # columns, a key of NULLS NOT DISTINCT referenced, date -> timestamp, char -> varchar, int -> numeric.
    ddl = ("CREATE TABLE p (a int, b int, d date, n numeric(6,2), s varchar(4), PRIMARY KEY (a, b),"
           " UNIQUE NULLS NOT DISTINCT (d), UNIQUE (n), UNIQUE (s));"
           " CREATE TABLE c (x int, t timestamp, k bigint, s char(4), FOREIGN KEY (x, x) REFERENCES p (b, a),"
           " FOREIGN KEY (t) REFERENCES p (d), FOREIGN KEY (k) REFERENCES p (n), FOREIGN KEY (s) REFERENCES p (s))")
    cs = [brief(c) for c in constraints(ddl)["c"]]
    assert cs == [("fk", (0, 0), 0, (1, 0), False), ("fk", (1,), 0, (2,), False), ("fk", (2,), 0, (3,), False),
                  ("fk", (3,), 0, (4,), False)]


def test_foreign_key_uses_an_immediate_key_beside_a_deferrable_one():
    # PostgreSQL's transformFkeyCheckAttrs accepts any immediate unique index on the referenced columns; a deferrable
    # key on the same columns is then irrelevant (55000 only when every matching key is deferrable).
    ddl = ("CREATE TABLE p (k integer PRIMARY KEY DEFERRABLE, UNIQUE (k));"
           " CREATE TABLE c (x integer REFERENCES p (k))")
    assert [brief(c) for c in constraints(ddl)["c"]] == [("fk", (0,), 0, (0,), False)]


# ------------------------------------------------------------------------------------------------------------
# ALTER TABLE ... ADD <table constraint> after the CREATE TABLEs (the request's declared integrity constraints).

CANONICAL_TPCH = json.loads((REPO / "src/gendb/fixtures/tpch/integrity-constraints.json").read_text())


def named(schema: dict) -> set[tuple]:
    """Every key and foreign key of a schema document by table and column names (independent of table and column
    positions)."""
    tables = schema["tables"]
    out = set()
    for t in tables:
        cols = [c["name"] for c in t["columns"]]
        for c in t["constraints"]:
            if c["kind"] == "key":
                out.add((t["name"], "pk" if c["primary"] else "unique", tuple(cols[i] for i in c["columns"])))
            elif c["kind"] == "foreign_key":
                ref = tables[c["table"]]
                ref_cols = [x["name"] for x in ref["columns"]]
                out.add((t["name"], "fk", tuple(cols[i] for i in c["columns"]), ref["name"],
                         tuple(ref_cols[i] for i in c["ref_columns"])))
    return out


def test_alter_adds_one_constraint_per_statement_with_forward_references():
    ddl = ("CREATE TABLE c (x int NOT NULL, y int);\nCREATE TABLE p (a int NOT NULL, b int);\n"
           "ALTER TABLE p ADD PRIMARY KEY (a);\n"
           "ALTER TABLE c ADD CONSTRAINT c_fk FOREIGN KEY (x) REFERENCES p (a) MATCH FULL ON DELETE CASCADE;\n"
           "ALTER TABLE c ADD CONSTRAINT c_ck CHECK (y BETWEEN 0 AND 10 OR y IS NULL);\n"
           "ALTER TABLE c ADD UNIQUE NULLS NOT DISTINCT (y);\n"
           "ALTER TABLE p ADD CONSTRAINT p_self FOREIGN KEY (b) REFERENCES p;\n")
    cs = constraints(ddl)
    assert [brief(c) for c in cs["c"]] == [("fk", (0,), 1, (0,), True), ("check", "Or"), ("unique", (1,), False)]
    assert [brief(c) for c in cs["p"]] == [("pk", (0,), True), ("fk", (1,), 1, (0,), False)]
    assert (cs["c"][0]["name"], cs["c"][0]["on_delete"], cs["c"][1]["name"]) == ("c_fk", "cascade", "c_ck")
    # The columns are unchanged (ALTER adds constraints only).
    created = load_schema("CREATE TABLE c (x int NOT NULL, y int); CREATE TABLE p (a int NOT NULL, b int)", "postgres")
    assert [t["columns"] for t in load_schema(ddl, "postgres").to_json()["tables"]] == \
        [t["columns"] for t in created.to_json()["tables"]]


def test_canonical_tpch_declarations_are_the_benchmark_schema_constraints():
    # The canonical list over the request's dataset order (lineitem first, every key column NOT NULL) declares exactly
    # the 8 primary keys and 7 foreign keys of src/gendb/fixtures/tpch-spec/schema.sql, keys before the foreign keys using them.
    tables = {"lineitem": ["l_orderkey", "l_partkey", "l_suppkey", "l_linenumber"],
              "orders": ["o_orderkey", "o_custkey"], "customer": ["c_custkey", "c_nationkey"], "part": ["p_partkey"],
              "partsupp": ["ps_partkey", "ps_suppkey"], "supplier": ["s_suppkey", "s_nationkey"],
              "nation": ["n_nationkey"], "region": ["r_regionkey"]}
    ddl = "".join(f"CREATE TABLE {t} ({', '.join(f'{c} bigint NOT NULL' for c in cols)});\n"
                  for t, cols in tables.items())
    assert CANONICAL_TPCH["trust"] == "user_declared"
    ddl += "".join(f"ALTER TABLE {d['table']} ADD {d['sql']};\n" for d in CANONICAL_TPCH["declarations"])
    declared = load_schema(ddl, "postgres").to_json()
    assert sum(len(t["constraints"]) for t in declared["tables"]) == len(CANONICAL_TPCH["declarations"]) == 15
    assert named(declared) == named(load_schema(TPCH_SCHEMA, "postgres").to_json())


def test_ddl_without_alter_is_unchanged():
    q = "SELECT a, b, v FROM pk2"
    assert dumps(translate(q, CONSTRAINTS_DDL, "postgres")) == dumps(translate(q, CONSTRAINTS_DDL + "\n", "postgres"))
    assert load_schema(TPCH_SCHEMA, "postgres") == load_schema(TPCH_SCHEMA + ";", "postgres")


@pytest.mark.parametrize("ddl,reason", [
    ("CREATE TABLE t (a int); ALTER TABLE t ADD PRIMARY KEY (a)", "alter_primary_key_nullable_column"),
    ("CREATE TABLE p (a int PRIMARY KEY); CREATE TABLE c (x int);"
     " ALTER TABLE c ADD CONSTRAINT f FOREIGN KEY (x) REFERENCES p NOT VALID", "constraint_not_valid"),
    ("CREATE TABLE t (a int NOT NULL); ALTER TABLE t ADD CONSTRAINT k CHECK (a > 0) NOT VALID", "constraint_not_valid"),
    # sqlglot 27 parses an unnamed ADD CHECK and several actions only as an opaque command.
    ("CREATE TABLE t (a int NOT NULL); ALTER TABLE t ADD CHECK (a > 0)", "parse_error"),
    ("CREATE TABLE t (a int NOT NULL, b int); ALTER TABLE t ADD PRIMARY KEY (a), ADD UNIQUE (b)", "parse_error"),
    ("CREATE TABLE t (a int NOT NULL); ALTER TABLE t ADD COLUMN b int", "invalid_schema"),
    ("CREATE TABLE t (a int NOT NULL); ALTER TABLE t DROP COLUMN a", "invalid_schema"),
    ("CREATE TABLE t (a int NOT NULL); ALTER TABLE t ADD PRIMARY KEY (a); CREATE TABLE u (b int)", "invalid_schema"),
    ("CREATE TABLE t (a int NOT NULL); ALTER TABLE u ADD PRIMARY KEY (a)", "unknown_table"),
    ("CREATE TABLE t (a int NOT NULL); ALTER TABLE IF EXISTS t ADD PRIMARY KEY (a)", "unsupported_syntax"),
    ("CREATE TABLE t (a int NOT NULL); ALTER TABLE ONLY t ADD PRIMARY KEY (a)", "unsupported_syntax"),
    ("CREATE TABLE t (a int NOT NULL, b int PRIMARY KEY); ALTER TABLE t ADD PRIMARY KEY (a)", "multiple_primary_keys"),
    ("CREATE TABLE t (a int NOT NULL); ALTER TABLE t ADD UNIQUE (a, a)", "duplicate_key_column"),
    ("CREATE TABLE t (a int NOT NULL); ALTER TABLE t ADD UNIQUE (z)", "unknown_column"),
    ("CREATE TABLE c (x int); CREATE TABLE p (a int NOT NULL);"
     " ALTER TABLE c ADD FOREIGN KEY (x) REFERENCES p (a); ALTER TABLE p ADD PRIMARY KEY (a)", "fk_no_matching_key"),
    ("CREATE TABLE c (x int); CREATE TABLE p (a int PRIMARY KEY);"
     " ALTER TABLE c ADD FOREIGN KEY (x) REFERENCES q (a)", "fk_unknown_table"),
    ("CREATE TABLE c (x int); CREATE TABLE p (a int PRIMARY KEY);"
     " ALTER TABLE c ADD FOREIGN KEY (x) REFERENCES p MATCH PARTIAL", "fk_match_partial"),
    ("CREATE TABLE c (x date); CREATE TABLE p (a int PRIMARY KEY);"
     " ALTER TABLE c ADD FOREIGN KEY (x) REFERENCES p", "fk_type_mismatch"),
    ("CREATE TABLE c (x int); CREATE TABLE p (a int NOT NULL);"
     " ALTER TABLE p ADD PRIMARY KEY (a) DEFERRABLE; ALTER TABLE c ADD FOREIGN KEY (x) REFERENCES p",
     "fk_deferrable_key"),
    ("CREATE TABLE t (a int NOT NULL); ALTER TABLE t ADD CONSTRAINT k CHECK (a IN (SELECT 1))", "check_subquery"),
    ("CREATE TABLE t (a int NOT NULL); ALTER TABLE t ADD CONSTRAINT k CHECK (b > 0)", "unknown_column"),
])
def test_alter_refusals_are_named(ddl, reason):
    with pytest.raises(Refusal) as e:
        load_schema(ddl, "postgres")
    assert e.value.reason == reason
