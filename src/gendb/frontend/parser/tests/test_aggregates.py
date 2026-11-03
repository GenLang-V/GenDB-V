"""MIN / MAX and DISTINCT aggregates (``features/minmax.py``, ``features/distinct_agg.py``).

The oracle for output names and ``\\gdesc`` types is PostgreSQL's evidence for ``cov_a.json``
(``GENDB_SQL_COV_A_EVIDENCE`` overrides its directory).  Values are compared by the verified SQLSpec evaluator
(``gendb sql diff``), not here.
"""

from __future__ import annotations

import unittest

from gendb_sql_frontend import translate
from support import evidence_cases, evidence_dir, fixture_ddl, reference_fixture, refusal_reason, translated

EVIDENCE = evidence_dir("GENDB_SQL_COV_A_EVIDENCE", "target/pg-evidence/verus-sql-cov-a/pg/evidence")
DDL = "CREATE TABLE t (i integer, n numeric(10,2), s text, v varchar(5), c char(4), f boolean);"


class MinMax(unittest.TestCase):
    def test_result_types(self):
        # Always nullable; numeric keeps the argument's scale bound without the typmod; varchar is min(text).
        cols = translated("SELECT MIN(i), MAX(n), MIN(v), MAX(c) FROM t", DDL)["output"]["columns"]
        self.assertEqual(cols, [
            {"type": {"kind": "int4"}, "nullable": True, "dscale": None},
            {"type": {"kind": "numeric", "typmod": None}, "nullable": True, "dscale": 2},
            {"type": {"kind": "text"}, "nullable": True, "dscale": None},
            {"type": {"kind": "bpchar", "n": None}, "nullable": True, "dscale": None},
        ])

    def test_boolean_refused(self):
        self.assertEqual(refusal_reason("SELECT MIN(f) FROM t", DDL), "type_mismatch")


class DistinctAgg(unittest.TestCase):
    def test_wrapping_and_normalization(self):
        nodes = translated("SELECT COUNT(DISTINCT n), SUM(DISTINCT i), AVG(DISTINCT n), MIN(DISTINCT s), "
                           "MAX(DISTINCT n) FROM t", DDL)["nodes"]
        by_id = {n["id"]: n for n in nodes}
        wrapped = [by_id[n["inner"]]["tag"] for n in nodes if n["tag"] == "DistinctAgg"]
        self.assertEqual(wrapped, ["Count", "Sum", "Avg"])
        # MIN/MAX(DISTINCT x) is MIN/MAX(x).
        self.assertEqual(sum(1 for n in nodes if n["tag"] in ("Min", "Max")), 2)

    def test_count_distinct_star_refused(self):
        self.assertEqual(refusal_reason("SELECT COUNT(DISTINCT *) FROM t", DDL), "unsupported_syntax")


class AggregateFixture(unittest.TestCase):
    def test_names_and_types_match_postgres(self):
        fixture = reference_fixture("cov_a")
        ddl = fixture_ddl(fixture)
        evidence = evidence_cases(EVIDENCE / "cov_a.reference.json")
        for case in fixture["cases"]:
            with self.subTest(case=case["name"]):
                doc = translate(case["sql"], ddl, "postgres")
                self.assertEqual(doc["status"], "ok", doc.get("refusal"))
                pg = evidence[case["name"]]
                self.assertEqual(pg["status"], "rows")
                self.assertEqual(doc["output"]["names"], [c["name"] for c in pg["columns"]])
                self.assertEqual(doc["output"]["pg_types"], [c["type"] for c in pg["columns"]])


if __name__ == "__main__":
    unittest.main()
