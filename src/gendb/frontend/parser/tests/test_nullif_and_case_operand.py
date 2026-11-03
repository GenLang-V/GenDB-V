"""NULLIF's result type and a simple CASE's untyped operand (VERUS_SQL_COVERAGE review fixes M1 and M2).

The oracle for output names and types is PostgreSQL 18 (evidence for ``pg_reference/cov_review.json``;
``GENDB_SQL_COV_REVIEW_EVIDENCE`` overrides its directory).
"""

from __future__ import annotations

import unittest

from gendb_sql_frontend import translate
from support import evidence_cases, evidence_dir, fixture_ddl, reference_fixture, translated

EVIDENCE = evidence_dir("GENDB_SQL_COV_REVIEW_EVIDENCE", "target/pg-evidence/verus-sql-cov-fix/pg/evidence")
FIXTURE = reference_fixture("cov_review")
DDL = fixture_ddl(FIXTURE)


class NullifCaseFixture(unittest.TestCase):
    """Row cases translate with PostgreSQL's output names and types; PostgreSQL's parse-time errors are refused."""

    def test_types_match_postgres_and_errors_are_refused(self):
        evidence = evidence_cases(EVIDENCE / "cov_review.reference.json")
        for case in FIXTURE["cases"]:
            doc, pg = translate(case["sql"], DDL, "postgres"), evidence[case["name"]]
            with self.subTest(case=case["name"]):
                if pg["status"] == "sql_error":
                    self.assertEqual(pg["sqlstate"], "42883")
                    self.assertEqual(doc["status"], "refused")
                    self.assertEqual(doc["refusal"]["reason"], "type_mismatch")
                    continue
                self.assertEqual(doc["status"], "ok", doc.get("refusal"))
                self.assertEqual(doc["output"]["names"], [c["name"] for c in pg["columns"]])
                self.assertEqual(doc["output"]["pg_types"], [c["type"] for c in pg["columns"]])


class EnclosingOperators(unittest.TestCase):
    """A text NULLIF / text CASE operand keeps its literal and subject unchanged (no bpchar trim or padding)."""

    def nodes(self, sql: str) -> list[dict]:
        return translated(sql, DDL)["nodes"]

    def test_text_nullif_under_eq_and_like(self):
        nodes = self.nodes("SELECT i4 FROM t WHERE nullif(c4, t) = 'ab '")
        self.assertIn("ab ", [n.get("bytes") for n in nodes if n["tag"] == "Text"])
        nodes = self.nodes("SELECT i4 FROM t WHERE nullif(c4, t) LIKE 'ab__'")
        like = next(n for n in nodes if n.get("f") == "Like")
        self.assertEqual(nodes[like["args"][0]]["tag"], "If")  # no PadBpchar around the text subject
        self.assertIn("PadBpchar", [n.get("f") for n in self.nodes("SELECT i4 FROM t WHERE nullif(c4, 'x') LIKE 'ab__'")])

    def test_simple_case_untyped_operand_is_text(self):
        nodes = self.nodes("SELECT CASE 'ab ' WHEN c4 THEN 'hit' ELSE 'miss' END AS r FROM t")
        self.assertIn("ab ", [n.get("bytes") for n in nodes if n["tag"] == "Text"])


if __name__ == "__main__":
    unittest.main()
