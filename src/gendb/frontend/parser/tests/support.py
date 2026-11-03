"""Shared inputs of the parser tests: repository paths, PostgreSQL reference fixtures and evidence, and helpers.

Run from the parser directory with the pinned interpreter (``toolchain.json``):

    <python> -m pytest -p no:cacheprovider tests

The reference fixtures (SQL cases and their DDL) live with SQLSpec's tests; ``GENDB_SQL_FIXTURES`` overrides their
directory.  The PostgreSQL 18 evidence for them (output names, ``\\gdesc`` types, returned values, recorded by
SQLSpec's ``postgres_reference.py``) is kept under ``target/pg-evidence``; each ``GENDB_SQL_*_EVIDENCE`` variable overrides one
evidence location.
"""

from __future__ import annotations

import json
import os
from pathlib import Path

from gendb_sql_frontend import translate
from gendb_sql_frontend.__main__ import labelled_query

REPO = Path(__file__).resolve().parents[5]
TPCH_SCHEMA = (REPO / "src/gendb/fixtures/tpch-spec/schema.sql").read_text()
TPCH_QUERIES = REPO / "src/gendb/fixtures/tpch-spec/queries.sql"
FIXTURES = Path(os.environ.get("GENDB_SQL_FIXTURES", REPO / "src/gendb/sqlspec/tests/fixtures"))
# Fixture files name their DDL files by repository path; older fixtures use the pre-refactor fixture directory.
_PRE_REFACTOR_FIXTURES = "src/gendb/tcb/sql-semantics/tests/fixtures/"


def evidence_dir(env: str, default: str) -> Path:
    """An evidence location: ``$env`` if set, else ``default`` relative to the repository."""
    return Path(os.environ.get(env, REPO / default))


def fixture_file(repo_path: str) -> Path:
    if repo_path.startswith(_PRE_REFACTOR_FIXTURES):
        return FIXTURES / repo_path[len(_PRE_REFACTOR_FIXTURES):]
    return REPO / repo_path


def reference_fixture(name: str) -> dict:
    """``pg_reference/<name>.json``: ``ddl`` (inline SQL or a file) and ``cases``."""
    return json.loads((FIXTURES / "pg_reference" / f"{name}.json").read_text())


def fixture_ddl(fixture: dict) -> str:
    return "\n".join(fixture_file(d["path"]).read_text() if "path" in d else d["sql"] for d in fixture["ddl"])


def case_sql(case: dict) -> str:
    """A fixture case's statement: inline ``sql`` or a labelled query of a file."""
    return case.get("sql") or labelled_query(fixture_file(case["query"]["path"]), case["query"]["label"])


def evidence_cases(path: Path) -> dict[str, dict]:
    """PostgreSQL's results of a fixture, by case name."""
    return {c["name"]: c for c in json.loads(path.read_text())["cases"]}


def tpch(label: str) -> str:
    return labelled_query(TPCH_QUERIES, label)


def translated(sql: str, ddl: str) -> dict:
    doc = translate(sql, ddl, "postgres")
    assert doc["status"] == "ok", doc.get("refusal")
    return doc


def refusal_reason(sql: str, ddl: str, dialect: str = "postgres") -> str:
    doc = translate(sql, ddl, dialect)
    assert doc["status"] == "refused", "expected a refusal"
    assert doc["refusal"]["detail"] and doc["refusal"]["meaning"]
    return doc["refusal"]["reason"]


def tags(doc: dict) -> list[str]:
    return [n["tag"] for n in doc["nodes"]]
