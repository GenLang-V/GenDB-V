"""Division and AVG (``features/div.py``, ``features/avg.py``).

The oracle for output names and ``\\gdesc`` types is PostgreSQL's evidence for ``cov_n.json``
(``GENDB_SQL_COV_N_EVIDENCE`` overrides its directory).  Values are compared by the verified SQLSpec evaluator
(``gendb sql diff``), not here.
"""

from __future__ import annotations

import json
import unittest

from gendb_sql_frontend import dumps, load_document, translate
from support import (TPCH_SCHEMA, evidence_cases, evidence_dir, fixture_ddl, reference_fixture, refusal_reason, tpch,
                     translated)

EVIDENCE = evidence_dir("GENDB_SQL_COV_N_EVIDENCE", "target/pg-evidence/verus-sql-cov-n/pg/evidence-v2")
DDL = "CREATE TABLE t (i integer, j integer NOT NULL, b bigint, n numeric(10,2), s text);"


def nodes(sql: str) -> list[dict]:
    return translated(sql, DDL)["nodes"]


class Division(unittest.TestCase):
    def test_operator_resolution(self):
        # int4 / int4: DivInt4, no cast; int8 / int4: the int4 side cast to int8; numeric / int: IntToNumeric.
        ns = nodes("SELECT i / j FROM t")
        call = next(n for n in ns if n["tag"] == "Call")
        self.assertEqual((call["f"], call["type"]["type"]["kind"], call["type"]["nullable"]), ("DivInt4", "int4", True))
        ns = nodes("SELECT b / j FROM t")
        self.assertEqual([n["f"] for n in ns if n["tag"] == "Call"], ["DivInt8"])
        self.assertEqual([n["cast"] for n in ns if n["tag"] == "Cast"], ["Int4ToInt8"])
        ns = nodes("SELECT n / j FROM t")
        call = next(n for n in ns if n["tag"] == "Call")
        self.assertEqual([n["cast"] for n in ns if n["tag"] == "Cast"], ["IntToNumeric"])
        # numeric result: display-scale bound 1000, value-dependent (not exact), numeric without typmod.
        self.assertEqual(call["f"], "DivNumeric")
        self.assertEqual(call["type"], {"type": {"kind": "numeric", "typmod": None}, "nullable": True,
                                        "dscale": 1000, "dscale_exact": False})
        # An untyped literal takes the other operand's type (PostgreSQL: '7' / 2 is int4 division).
        self.assertEqual([n["f"] for n in nodes("SELECT '7' / j FROM t") if n["tag"] == "Call"], ["DivInt4"])

    def test_refusals(self):
        for sql in ("SELECT s / 2 FROM t", "SELECT '1' / '2' FROM t", "SELECT AVG(s) FROM t", "SELECT AVG('1') FROM t"):
            with self.subTest(sql=sql):
                self.assertEqual(refusal_reason(sql, DDL), "type_mismatch")


class Avg(unittest.TestCase):
    def test_kinds_and_type(self):
        doc = translate("SELECT AVG(i), AVG(b), AVG(n) FROM t", DDL, "postgres")
        self.assertEqual([n["kind"] for n in doc["nodes"] if n["tag"] == "Avg"], ["Int4", "Int8", "Numeric"])
        for c in doc["output"]["columns"]:
            self.assertEqual(c, {"type": {"kind": "numeric", "typmod": None}, "nullable": True, "dscale": 1000,
                                 "dscale_exact": False})

    def test_tpch_q1_deterministic_round_trip(self):
        text = dumps(translate(tpch("Q1"), TPCH_SCHEMA, "postgres"))
        self.assertEqual(text, dumps(translate(tpch("Q1"), TPCH_SCHEMA, "postgres")))
        doc = json.loads(text)
        self.assertEqual(doc["status"], "ok")
        load_document(doc)
        self.assertEqual(sum(1 for n in doc["nodes"] if n["tag"] == "Avg"), 3)


class DivisionAndAvgFixture(unittest.TestCase):
    def test_names_and_types_match_postgres(self):
        fixture = reference_fixture("cov_n")
        ddl = fixture_ddl(fixture)
        evidence = evidence_cases(EVIDENCE / "cov_n.reference.json")
        for case in fixture["cases"]:
            with self.subTest(case=case["name"]):
                doc = translate(case["sql"], ddl, "postgres")
                self.assertEqual(doc["status"], "ok", doc.get("refusal"))
                pg = evidence[case["name"]]
                if pg["status"] == "rows":
                    self.assertEqual(doc["output"]["names"], [c["name"] for c in pg["columns"]])
                    self.assertEqual(doc["output"]["pg_types"], [c["type"] for c in pg["columns"]])


if __name__ == "__main__":
    unittest.main()
