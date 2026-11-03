"""CASE / COALESCE / NULLIF, scalar and IN / ANY / ALL subqueries, SELECT DISTINCT, WITH and the view script.

The oracle for names, result types and numeric scales is PostgreSQL 18 (evidence for ``pg_reference/cov_s.json``;
``GENDB_SQL_COV_S_EVIDENCE`` overrides its directory).
"""

from __future__ import annotations

import json
import unittest

from gendb_sql_frontend import dumps, load_document, translate
from gendb_sql_frontend.ast import encode_arena
from support import evidence_cases, evidence_dir, fixture_ddl, reference_fixture, refusal_reason, tags, translated

EVIDENCE = evidence_dir("GENDB_SQL_COV_S_EVIDENCE", "target/pg-evidence/verus-sql-cov-s/evidence")
FIXTURE = reference_fixture("cov_s")
DDL = fixture_ddl(FIXTURE)


def ok(sql: str) -> dict:
    return translated(sql, DDL)


def reason(sql: str) -> str:
    return refusal_reason(sql, DDL)


class FixtureTypesAndScales(unittest.TestCase):
    """Every fixture case translates; names, PostgreSQL types and numeric scales agree with PostgreSQL."""

    def test_types_and_scales_match_postgres(self):
        evidence = evidence_cases(EVIDENCE / "cov_s.reference.json")
        for case in FIXTURE["cases"]:
            doc, pg = translate(case["sql"], DDL, "postgres"), evidence[case["name"]]
            with self.subTest(case=case["name"]):
                self.assertEqual(doc["status"], "ok", doc.get("refusal"))
                text = dumps(doc)
                self.assertEqual(text, dumps(translate(case["sql"], DDL, "postgres")))
                _, root = load_document(json.loads(text))
                self.assertEqual(encode_arena(root), (doc["nodes"], doc["root"]))
                if pg["status"] != "rows":
                    continue  # run-time SQL errors (22003, 21000): the query itself translates
                self.assertEqual(doc["output"]["names"], [c["name"] for c in pg["columns"]])
                self.assertEqual(doc["output"]["pg_types"], [c["type"] for c in pg["columns"]])
                for i, col in enumerate(doc["output"]["columns"]):
                    if col["dscale"] is None:
                        continue
                    exact = col.get("dscale_exact", True)
                    for row in pg["rows"]:
                        if row[i] is None:
                            continue
                        scale = len(row[i].partition(".")[2])
                        if exact:
                            self.assertEqual(scale, col["dscale"], (pg["columns"][i], row[i]))
                        else:
                            self.assertLessEqual(scale, col["dscale"], (pg["columns"][i], row[i]))


class Normalizations(unittest.TestCase):
    def test_case_coalesce_nullif_are_lazy_ifs(self):
        doc = ok("SELECT CASE k WHEN 1 THEN 'one' WHEN 2 THEN 'two' END AS x FROM r")
        self.assertEqual(tags(doc).count("If"), 2)
        self.assertIn("Null", tags(doc))  # the implicit ELSE NULL
        doc = ok("SELECT COALESCE(v, 0) AS x FROM r")
        self.assertEqual(doc["output"]["columns"][0], {"type": {"kind": "numeric", "typmod": None}, "nullable": True,
                                                       "dscale": 2, "dscale_exact": False})
        doc = ok("SELECT NULLIF(k, 1.5) AS x FROM r")
        self.assertEqual(doc["output"]["pg_types"], ["numeric"])  # the left operand after the int -> numeric cast
        # Same-typmod results keep it (select_common_typmod); mixed ones drop it.
        self.assertEqual(ok("SELECT CASE WHEN k > 0 THEN v ELSE v END AS x FROM r")["output"]["pg_types"],
                         ["numeric(10,2)"])

    def test_quantified_subqueries(self):
        nodes = ok("SELECT k FROM r WHERE k NOT IN (SELECT k FROM s)")["nodes"]
        self.assertTrue(any(n["tag"] == "Not" and nodes[n["p"]]["tag"] == "AnyCmp" for n in nodes))
        doc = ok("SELECT k FROM r WHERE v > ALL (SELECT w FROM s)")
        anycmp = next(n for n in doc["nodes"] if n["tag"] == "AnyCmp")
        self.assertEqual(anycmp["op"], "Le")  # NOT (v <= ANY ...)
        # The subquery's integer column is cast to numeric by a Project over the subquery.
        self.assertEqual(doc["nodes"][anycmp["q"]]["tag"], "Project")
        self.assertEqual(reason("SELECT k FROM r WHERE (k, k) IN (SELECT k, w FROM s)"), "row_subquery")
        self.assertEqual(reason("SELECT k FROM r WHERE k IN (SELECT k, w FROM s)"), "subquery_columns")
        self.assertEqual(reason("SELECT (SELECT k, w FROM s) AS x FROM r"), "subquery_columns")
        self.assertEqual(reason("SELECT k FROM r WHERE k = ANY (ARRAY[1, 2])"), "quantified_array")
        # A grouped query may use only grouped columns inside a correlated subquery.
        self.assertEqual(reason("SELECT k FROM r GROUP BY k HAVING COUNT(*) > (SELECT COUNT(*) FROM s WHERE s.w = r.d)"),
                         "ungrouped_column")

    def test_distinct(self):
        self.assertIn("Distinct", tags(ok("SELECT DISTINCT k FROM r")))
        self.assertEqual(reason("SELECT DISTINCT ON (k) k FROM r"), "distinct_on")
        self.assertEqual(reason("SELECT DISTINCT k FROM r ORDER BY tag"), "hidden_order_key")

    def test_with_is_inlined_in_its_definition_scope(self):
        # A WITH item referenced inside a subquery means the same as the derived table written there.
        with_form = ok("WITH t AS (SELECT k, w FROM s) SELECT r.k FROM r WHERE r.d < (SELECT COUNT(*) FROM t WHERE t.k = r.k)")
        derived = ok("SELECT r.k FROM r WHERE r.d < (SELECT COUNT(*) FROM (SELECT k, w FROM s) AS t WHERE t.k = r.k)")
        self.assertEqual(with_form["nodes"], derived["nodes"])
        # Names inside a WITH item bind where it is defined, never at the referencing level (`d` is r.d there).
        self.assertEqual(reason("WITH t AS (SELECT w FROM s WHERE w > d) SELECT r.k FROM r WHERE r.k IN (SELECT w FROM t)"),
                         "unknown_column")
        # An inner WITH shadows an outer one; a WITH item does not see itself (no RECURSIVE).
        inner = ok("WITH t AS (SELECT k FROM r) SELECT k FROM (WITH t AS (SELECT w AS k FROM s) SELECT k FROM t) AS x")
        self.assertEqual(inner["nodes"], ok("SELECT k FROM (SELECT w AS k FROM s) AS x")["nodes"])
        self.assertEqual(reason("WITH RECURSIVE t AS (SELECT k FROM r) SELECT k FROM t"), "recursive_cte")
        self.assertEqual(reason("WITH t AS (SELECT k FROM r), t AS (SELECT k FROM s) SELECT k FROM t"), "duplicate_cte")
        self.assertEqual(reason("WITH t (a, b) AS (SELECT k FROM r) SELECT a FROM t"), "cte_columns")
        self.assertEqual(reason("WITH t AS (SELECT kk FROM r) SELECT 1 AS one FROM r"), "unknown_column")  # bound even if unused

    def test_view_script_is_the_with_form(self):
        script = ("CREATE VIEW v (kk, total) AS SELECT k, SUM(v) FROM r GROUP BY k;\n"
                  "SELECT kk FROM v WHERE total = (SELECT SUM(total) FROM v);\nDROP VIEW v;")
        with_form = ("WITH v (kk, total) AS (SELECT k, SUM(v) FROM r GROUP BY k) "
                     "SELECT kk FROM v WHERE total = (SELECT SUM(total) FROM v)")
        self.assertEqual(ok(script)["nodes"], ok(with_form)["nodes"])
        self.assertEqual(reason("CREATE VIEW v AS SELECT k FROM r; SELECT k FROM v; DROP VIEW w;"), "view_script")
        self.assertEqual(reason("SELECT 1 AS a FROM r; SELECT 2 AS b FROM r"), "multiple_statements")


if __name__ == "__main__":
    unittest.main()
