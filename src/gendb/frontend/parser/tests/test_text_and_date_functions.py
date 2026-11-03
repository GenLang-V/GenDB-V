"""LIKE / SUBSTRING / EXTRACT (``features/like.py``, ``features/substring.py``, ``features/extract.py``): translation,
result types against the PostgreSQL 18 evidence of ``pg_reference/cov_l.json`` and the named refusals.

``GENDB_SQL_COV_L_EVIDENCE`` overrides the evidence file.
"""

from __future__ import annotations

import unittest

from gendb_sql_frontend import dumps, translate
from support import evidence_cases, evidence_dir, reference_fixture, refusal_reason, translated

EVIDENCE = evidence_dir("GENDB_SQL_COV_L_EVIDENCE", "target/pg-evidence/verus-sql-cov-l/pg/evidence/cov_l.reference.json")
DDL = ("CREATE TABLE bp (id integer NOT NULL, c char(4), v varchar(30), t text, n bigint, d date, "
       "ts timestamp);")
# The pinned sqlglot 27.0.0 accepts only a string literal after ESCAPE; these fixture cases are PostgreSQL evidence
# only (the frontend refuses them with parse_error, which is never counted as a match).
COLUMN_ESCAPE_CASES = {"like_escape", "like_escape_too_long", "like_escape_too_long_null_subject",
                       "like_escape_too_long_null_pattern", "like_escape_trailing"}


def nodes(doc: dict, tag: str) -> list[dict]:
    return [n for n in doc["nodes"] if n["tag"] == tag]


class TextAndDateFunctions(unittest.TestCase):
    def test_fixture_cases_translate_with_postgres_types(self):
        fixture = reference_fixture("cov_l")
        ddl = fixture["ddl"][0]["sql"]
        evidence = evidence_cases(EVIDENCE) if EVIDENCE.exists() else {}
        for case in fixture["cases"]:
            with self.subTest(case=case["name"]):
                doc = translate(case["sql"], ddl, "postgres")
                if case["name"] in COLUMN_ESCAPE_CASES:
                    self.assertEqual(doc["refusal"]["reason"], "parse_error")
                    continue
                self.assertEqual(doc["status"], "ok", doc.get("refusal"))
                self.assertEqual(dumps(doc), dumps(translate(case["sql"], ddl, "postgres")))
                pg = evidence.get(case["name"])
                if pg is not None and pg["status"] == "rows":
                    self.assertEqual(doc["output"]["pg_types"], [c["type"] for c in pg["columns"]])

    def test_like_bpchar_subject_is_padded_and_default_escape(self):
        doc = translated("SELECT c LIKE 'ab' AS a FROM bp", DDL)
        calls = {n["f"]: n for n in nodes(doc, "Call")}
        self.assertEqual(set(calls), {"Like", "PadBpchar"})
        self.assertEqual(calls["Like"]["args"][0], calls["PadBpchar"]["id"])
        self.assertIn({"id": calls["Like"]["args"][2] - 1, "tag": "Text", "bytes": "\\"}, doc["nodes"])
        # varchar / text subjects and a char(n) pattern are not padded
        doc = translated("SELECT v LIKE c AS a, t LIKE 'x' ESCAPE '' AS b FROM bp", DDL)
        self.assertEqual([n["f"] for n in nodes(doc, "Call")], ["Like", "Like"])

    def test_not_like_is_not_of_bool(self):
        doc = translated("SELECT id FROM bp WHERE v NOT LIKE '%BRASS'", DDL)
        self.assertTrue(nodes(doc, "Not") and nodes(doc, "OfBool"))

    def test_substring_and_extract_types(self):
        doc = translated("SELECT SUBSTRING(c FROM 1 FOR 2) AS a, substr(t, 2) AS b, EXTRACT(YEAR FROM d) AS y, "
                         "EXTRACT(DAY FROM ts) AS z FROM bp", DDL)
        self.assertEqual(doc["output"]["pg_types"], ["text", "text", "numeric", "numeric"])
        self.assertEqual([n["f"] for n in nodes(doc, "Call")], ["Substring3", "Substring2", "ExtractYear", "ExtractDay"])
        self.assertEqual([c["dscale"] for c in doc["output"]["columns"][2:]], [0, 0])

    def test_named_refusals(self):
        for sql, reason in (("SELECT id FROM bp WHERE t ILIKE 'a'", "unsupported_operator"),
                            ("SELECT id FROM bp WHERE t SIMILAR TO 'a'", "unsupported_operator"),
                            ("SELECT id FROM bp WHERE id LIKE '1'", "type_mismatch"),
                            ("SELECT EXTRACT(DOW FROM d) FROM bp", "unsupported_extract_field"),
                            ("SELECT EXTRACT(YEAR FROM '2000-01-01') FROM bp", "type_mismatch"),
                            ("SELECT SUBSTRING(t FROM 'a.') FROM bp", "substring_regex"),
                            ("SELECT SUBSTRING(t FROM n) FROM bp", "type_mismatch")):
            with self.subTest(sql=sql):
                self.assertEqual(refusal_reason(sql, DDL), reason)


if __name__ == "__main__":
    unittest.main()
