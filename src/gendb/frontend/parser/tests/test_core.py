"""Core fragment: TPC-H Q6/Q3/Q4, the tiny PostgreSQL reference fixtures, EXISTS select lists, char(n) comparisons
and named refusals.

The oracle for names, result types and numeric scales is PostgreSQL itself (``support`` describes the evidence;
``GENDB_SQL_PG_EVIDENCE`` overrides its directory).
"""

from __future__ import annotations

import json
import unittest

from gendb_sql_frontend import dumps, load_document, translate
from gendb_sql_frontend.ast import encode_arena
from support import (TPCH_SCHEMA, case_sql, evidence_cases, evidence_dir, fixture_ddl, reference_fixture,
                     refusal_reason, tpch, translated)

EVIDENCE = evidence_dir("GENDB_SQL_PG_EVIDENCE", "target/pg-evidence/verus-sql-pg/evidence")
CORE_DDL = "CREATE TABLE r (k integer, v numeric(10,2), tag text);\nCREATE TABLE s (k integer, w integer);"


class TpchCoreQueries(unittest.TestCase):
    def test_deterministic_and_round_trip(self):
        for label in ("Q6", "Q3", "Q4"):
            text = dumps(translate(tpch(label), TPCH_SCHEMA, "postgres"))
            self.assertEqual(text, dumps(translate(tpch(label), TPCH_SCHEMA, "postgres")))
            doc = json.loads(text)
            _, root = load_document(doc)
            self.assertEqual(encode_arena(root), (doc["nodes"], doc["root"]))

    def test_names_scopes_and_aliases(self):
        std = translated(tpch("Q3"), TPCH_SCHEMA)
        # Aliases, qualified names, ordinals and an output-name ORDER BY key mean the same query: same AST.
        aliased = translated("""SELECT l.l_orderkey, SUM(l.l_extendedprice * (1 - l.l_discount)) AS revenue,
                                       o.o_orderdate, o.o_shippriority
                                FROM customer AS c, orders o, lineitem l
                                WHERE c.c_mktsegment = 'BUILDING   ' AND c.c_custkey = o.o_custkey
                                  AND l.l_orderkey = o.o_orderkey AND o.o_orderdate < DATE '1995-03-15'
                                  AND l.l_shipdate > '1995-03-15'
                                GROUP BY 1, 3, 4 ORDER BY revenue DESC, 3 LIMIT 10""", TPCH_SCHEMA)
        # ('BUILDING   ' vs char(10): bpchar ignores trailing blanks; '1995-03-15' vs date: untyped literal.)
        self.assertEqual(aliased["nodes"], std["nodes"])
        # Q4: the correlated o_orderkey inside EXISTS is the outer row's column; lineitem follows the context.
        q4 = translated(tpch("Q4"), TPCH_SCHEMA)
        orders = [c["name"] for c in q4["schema"]["tables"][6]["columns"]]
        lineitem = [c["name"] for c in q4["schema"]["tables"][7]["columns"]]
        nodes = q4["nodes"]
        cmp = next(n for n in nodes if n["tag"] == "Cmp" and n["op"] == "Eq")
        self.assertEqual((nodes[cmp["a"]]["index"], nodes[cmp["b"]]["index"]),
                         (len(orders) + lineitem.index("l_orderkey"), orders.index("o_orderkey")))
        # PostgreSQL folds unquoted identifiers; a quoted upper-case name is a different identifier.
        self.assertEqual(translated("SELECT O_ORDERKEY FROM ORDERS", TPCH_SCHEMA)["output"]["names"], ["o_orderkey"])
        self.assertEqual(refusal_reason('SELECT "O_ORDERKEY" FROM orders', TPCH_SCHEMA), "unknown_column")


class PostgresReferenceFixtures(unittest.TestCase):
    """Output names, PostgreSQL result types and numeric scales agree with PostgreSQL 18."""

    REFUSED = {"text_bpchar_c_collation": "unsupported_syntax"}

    def test_types_and_scales_match_postgres(self):
        translated_cases = 0
        for name in ("tpch_tiny", "core_nulls"):
            fixture = reference_fixture(name)
            evidence = evidence_cases(EVIDENCE / f"{name}.reference.json")
            ddl = fixture_ddl(fixture)
            for case in fixture["cases"]:
                doc, pg = translate(case_sql(case), ddl, "postgres"), evidence[case["name"]]
                with self.subTest(case=case["name"]):
                    if case["name"] in self.REFUSED:
                        self.assertEqual(doc["refusal"]["reason"], self.REFUSED[case["name"]])
                        continue
                    if pg["status"] == "sql_error":  # a run-time error: the query itself translates
                        self.assertEqual(doc["status"], "ok", doc.get("refusal"))
                        translated_cases += 1
                        continue
                    self.assertEqual(pg["status"], "rows")
                    self.assertEqual(doc["output"]["names"], [c["name"] for c in pg["columns"]])
                    self.assertEqual(doc["output"]["pg_types"], [c["type"] for c in pg["columns"]])
                    for i, col in enumerate(doc["output"]["columns"]):
                        if col["dscale"] is None:
                            continue
                        for row in pg["rows"]:
                            if row[i] is not None:  # PostgreSQL prints numerics with their display scale
                                frac = row[i].partition(".")[2]
                                self.assertEqual(len(frac), col["dscale"], (pg["columns"][i], row[i]))
                    translated_cases += 1
        self.assertEqual(translated_cases, 16)

    def test_untyped_null_takes_the_operand_type(self):
        doc = translated("SELECT k + NULL AS x FROM r", CORE_DDL)
        self.assertEqual(doc["output"]["pg_types"], ["integer"])
        self.assertTrue(doc["output"]["columns"][0]["nullable"])


class ExistsSelectList(unittest.TestCase):
    """PostgreSQL does not evaluate the select list of a non-aggregated EXISTS subquery, but does evaluate it (for a
    plan-dependent first row) when the subquery aggregates (evidence
    ``target/pg-evidence/verus-sql-t4/pg/evidence/exists_select_list.reference.json``: rows, rows, error 22003)."""

    def test_exists_select_list(self):
        def exists_body(sql: str) -> str:
            nodes = translated(sql, CORE_DDL)["nodes"]
            return nodes[next(n for n in nodes if n["tag"] == "Exists")["q"]]["tag"]
        # 10 * 2147483647 would overflow int4: the select list is bound but not applied.
        self.assertEqual(exists_body("SELECT k FROM s WHERE EXISTS (SELECT w * 2147483647 FROM s AS s2 WHERE s2.w = 10)"),
                         "Filter")
        # A scalar aggregate over no rows is still one row: the aggregation stays.
        self.assertEqual(exists_body("SELECT k FROM s WHERE EXISTS (SELECT SUM(w) FROM s AS s2 WHERE s2.w > 1000)"),
                         "Aggregate")
        self.assertEqual(refusal_reason("SELECT k FROM s WHERE EXISTS (SELECT COUNT(*) * 9223372036854775807 FROM s AS s2)",
                                        CORE_DDL), "exists_select_list")
        # The ignored select list is still resolved: an unknown column is an error.
        self.assertEqual(refusal_reason("SELECT k FROM s WHERE EXISTS (SELECT nope FROM s AS s2)", CORE_DDL),
                         "unknown_column")


class CharComparisons(unittest.TestCase):
    """VERUS_SQL review M1 (PostgreSQL 18 evidence
    ``target/pg-evidence/verus-sql-review/pg/evidence/verus_sql_review_probe.reference.json`` on s = {('a', 'a ')}: ``c = v`` 1,
    ``c IN ('z', 'a '::text)`` 1, control ``c = 'a '::text`` 0)."""

    DDL = "CREATE TABLE s (c char(3), v varchar(3), t text, k integer);"

    def texts(self, sql: str) -> list[str]:
        return [n["bytes"] for n in translated(sql, self.DDL)["nodes"] if n["tag"] == "Text"]

    def test_bpchar_varchar_refused_both_directions(self):
        for where in ("c = v", "v = c", "c = 'a '::varchar(3)", "v = 'a '::char(3)", "'a '::char(3) <> v",
                      "c BETWEEN v AND 'z'", "c IN (v, 'a')"):
            with self.subTest(where=where):
                self.assertEqual(refusal_reason(f"SELECT count(*) FROM s WHERE {where}", self.DDL),
                                 "bpchar_varchar_comparison")

    def test_in_list_common_type(self):
        # Common type bpchar: the text item would be compared blank-insensitively.
        self.assertEqual(refusal_reason("SELECT count(*) FROM s WHERE c IN ('z', 'a '::text)", self.DDL),
                         "in_list_bpchar_coercion")
        # One non-Var item: per element, bpchar = text is texteq on the right-trimmed value.
        self.assertEqual(self.texts("SELECT count(*) FROM s WHERE c IN ('a '::text)"), ["a "])
        # Common type varchar: the char(3) item is right-trimmed (bpchar -> varchar), then text equality.
        self.assertEqual(self.texts("SELECT count(*) FROM s WHERE v IN ('z', 'a '::char(3))"), ["z", "a"])
        # An untyped left side takes the common type: bpchar, so both literals are right-trimmed; numeric.
        self.assertEqual(self.texts("SELECT count(*) FROM s WHERE 'a' IN ('b'::char(1), 'a ')"), ["a", "b", "a", "a"])
        nodes = translated("SELECT count(*) FROM s WHERE '1.0' IN (2.5, '1')", self.DDL)["nodes"]
        self.assertEqual([(n["coeff"], n["scale"]) for n in nodes if n["tag"] == "Num"],
                         [("10", 1), ("25", 1), ("10", 1), ("1", 0)])
        # Numeric mixes keep exact casts ('1.5' is numeric because 2.5 makes the common type numeric).
        translated("SELECT count(*) FROM s WHERE k IN (1, '1.5', 2.5, NULL)", self.DDL)

    def test_bpchar_text_and_unknown_controls(self):
        self.assertEqual(self.texts("SELECT count(*) FROM s WHERE c = 'a '::text"), ["a "])
        self.assertEqual(self.texts("SELECT count(*) FROM s WHERE c IN ('z', 'a ')"), ["z", "a"])

    def test_interval_negation_range(self):
        self.assertEqual(refusal_reason("SELECT count(*) FROM orders WHERE o_orderdate - INTERVAL '-2147483648' DAY > o_orderdate",
                                        TPCH_SCHEMA), "interval_negation_range")
        translated("SELECT count(*) FROM orders WHERE o_orderdate + INTERVAL '-2147483648' DAY > o_orderdate", TPCH_SCHEMA)


class Refusals(unittest.TestCase):
    def test_named_refusals(self):
        self.assertEqual(refusal_reason("SELECT k FROM r, s", CORE_DDL), "ambiguous_column")
        self.assertEqual(refusal_reason("SELECT orders.o_orderkey FROM orders o", TPCH_SCHEMA), "unknown_table")
        self.assertEqual(refusal_reason("SELECT o_orderpriority, o_orderdate, COUNT(*) FROM orders GROUP BY o_orderpriority",
                                        TPCH_SCHEMA), "ungrouped_column")
        self.assertEqual(refusal_reason("SELECT STDDEV(l_quantity) FROM lineitem", TPCH_SCHEMA), "unsupported_aggregate")
        # Constructs sqlglot would otherwise drop or reinterpret.
        self.assertEqual(refusal_reason("SELECT o_orderkey FROM orders TABLESAMPLE SYSTEM (10)", TPCH_SCHEMA),
                         "unsupported_syntax")
        self.assertEqual(refusal_reason("SELECT o_orderkey FROM orders JOIN lineitem", TPCH_SCHEMA),
                         "join_without_condition")
        self.assertEqual(refusal_reason("SELECT 1", CORE_DDL, dialect="mysql"), "unsupported_dialect")


if __name__ == "__main__":
    unittest.main()
