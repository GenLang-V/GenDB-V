"""Command line: ``python -m gendb_sql_frontend translate --schema DDL (--sql FILE | --query-file FILE --label Q6)
--dialect postgres [--params JSON]`` (``JSON``: the placeholder declaration ``[{"index": 1, "type": "date"}, ...]``).

Writes the AST document (or the refusal document) as JSON to stdout or ``--out``.
Exit status: 0 translated, 1 refused, 2 usage error.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

from .api import dumps, translate


def labelled_query(path: Path, label: str) -> str:
    """The statement after a ``-- <label>:`` header (the layout of src/gendb/fixtures/tpch-spec/queries.sql)."""
    text = path.read_text(encoding="utf-8")
    m = re.search(rf"^--\s*{re.escape(label)}:.*?$\n(.*?)(?=^--\s*Q\d+:|\Z)", text, re.S | re.M)
    if not m:
        raise SystemExit(f"no query labelled {label!r} in {path}")
    return m.group(1).strip()


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="gendb_sql_frontend")
    sub = ap.add_subparsers(dest="cmd", required=True)
    t = sub.add_parser("translate", help="SQL + schema DDL -> AST JSON or named refusal")
    t.add_argument("--schema", required=True, type=Path, help="file of CREATE TABLE statements")
    source = t.add_mutually_exclusive_group(required=True)
    source.add_argument("--sql", type=Path, help="file holding one SELECT statement")
    source.add_argument("--query-file", type=Path, help="file of labelled queries (-- Q6: ...)")
    t.add_argument("--label", help="query label for --query-file")
    t.add_argument("--dialect", required=True, help="source dialect (explicit; 'postgres')")
    t.add_argument("--params", help="placeholder declaration (JSON list of {index, type})")
    t.add_argument("--out", type=Path, help="write here instead of stdout")
    args = ap.parse_args(argv)
    if args.query_file is not None and not args.label:
        ap.error("--query-file needs --label")
    sql = (args.sql.read_text(encoding="utf-8") if args.sql is not None
           else labelled_query(args.query_file, args.label))
    try:
        params = None if args.params is None else json.loads(args.params)
    except json.JSONDecodeError as e:
        ap.error(f"--params is not JSON: {e}")
    doc = translate(sql, args.schema.read_text(encoding="utf-8"), args.dialect, params)
    text = dumps(doc)
    if args.out is not None:
        args.out.write_text(text, encoding="utf-8")
    else:
        sys.stdout.write(text)
    return 0 if doc["status"] == "ok" else 1


if __name__ == "__main__":
    sys.exit(main())
