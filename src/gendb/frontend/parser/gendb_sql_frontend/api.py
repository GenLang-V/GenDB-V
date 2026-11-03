"""Public frontend API: SQL text + schema DDL + explicit dialect -> AST document or named refusal."""

from __future__ import annotations

import json
from typing import Any

from .ast import FORMAT, AstError, Node, decode_arena, encode_arena
from .features.params import ParamDecls
from .lower import Lowerer
from .parse import parse_query
from .refusal import Refusal
from .schema import Schema, load_schema
from .toolchain import TOOLCHAIN, check_dialect, check_toolchain

# The identity of the translation, recorded in every document; documents of different identities may differ.  The
# human-facing refusal meanings (`refusal.REASONS` values) are descriptions, not translation behavior: rewording them
# does not move the identity (reason codes, AST and schema content do).
# v2 (VERUS_SQL review M1): bpchar/varchar comparisons and IN lists coercing text to bpchar are refused, IN lists use
# PostgreSQL's common type, and a negated interval is range-checked.
# v3 (VERUS_SQL_COVERAGE C): the schema records PRIMARY KEY / UNIQUE / FOREIGN KEY / CHECK constraints
# (`schema.tables[].constraints`) instead of ignoring them.
# v4: typed placeholders `$n` from a parameter declaration (`features/params.py`): `Param`
# literal nodes and a `params` section.  Documents of statements without a declaration differ from v3 only here.
# Within v4, the schema DDL may add table constraints by `ALTER TABLE ... ADD` after its CREATE TABLEs (`schema.py`; the
# request's declared integrity constraints).  That DDL was refused before; every previously accepted input translates
# to the same document, so the identity (part of every statement key) stays v4.
# Also within v4, the Rust host refuses a document with a literal-only constant subexpression whose SQLSpec evaluation
# raises an SQL error (`gendb_frontend::constants`); every other document is unchanged, so the identity stays v4.
IDENTITY = "gendb-sql-frontend-v4"


def translate(sql: str, schema_ddl: str, dialect: str, params: list | None = None) -> dict:
    """Translate one query.  Deterministic: equal inputs give byte-equal ``dumps`` output.

    ``params``: the declared placeholder types ``[{"index": n, "type": "<SQL type>"}, ...]`` (``features/params.py``);
    ``None`` means the statement has no placeholders."""
    try:
        check_toolchain()
        check_dialect(dialect)
        schema = load_schema(schema_ddl, dialect)
        decls = None if params is None else ParamDecls.parse(params, dialect)
        root, names = Lowerer(schema, dialect, decls).top(parse_query(sql, dialect))
        if decls is not None:
            decls.check_all_used()
    except Refusal as r:
        return _refusal_document(sql, dialect, r)
    except RecursionError:
        return _refusal_document(sql, dialect, Refusal("frontend_resource_limit",
                                                       "Python recursion limit reached while parsing or resolving"))
    return document(sql, dialect, schema, root, names, decls)


def _frontend_record(dialect: str) -> dict:
    return {"identity": IDENTITY, "sqlglot": TOOLCHAIN["sqlglot"], "dialect": dialect, "target": TOOLCHAIN["target"]}


def _refusal_document(sql: str, dialect: str, refusal: Refusal) -> dict:
    return {"format": FORMAT, "status": "refused", "frontend": _frontend_record(dialect), "sql": sql,
            "refusal": refusal.to_json()}


def document(sql: str, dialect: str, schema: Schema, root: Node, names: list[str],
             decls: ParamDecls | None = None) -> dict:
    """The ``ok`` document of a translated statement (key order is part of the ``dumps`` text)."""
    nodes, root_id = encode_arena(root)
    columns = root.body.ann
    doc = {"format": FORMAT, "status": "ok", "frontend": _frontend_record(dialect), "sql": sql,
           "schema": schema.to_json(),
           "output": {"names": names, "columns": [c.to_json() for c in columns],
                      "pg_types": [c.ty.pg_name() for c in columns]}}
    if decls is not None and decls.types:
        doc["params"] = decls.to_json()
    doc.update({"root": root_id, "nodes": nodes})
    return doc


def dumps(doc: dict) -> str:
    """Deterministic text: fixed key order, ASCII escapes, one line per top-level key and per node."""
    def one(v: Any) -> str:
        return json.dumps(v, ensure_ascii=True, separators=(", ", ": "))
    parts = []
    for key, value in doc.items():
        if key == "nodes":
            body = ",\n".join("  " + one(n) for n in value)
            parts.append(f' "nodes": [\n{body}\n ]')
        else:
            parts.append(f" {one(key)}: {one(value)}")
    return "{\n" + ",\n".join(parts) + "\n}\n"


def load_document(doc: Any) -> tuple[dict, Node]:
    """Validate an ``ok`` AST document; returns (schema JSON, root node)."""
    if not isinstance(doc, dict) or doc.get("format") != FORMAT or doc.get("status") != "ok":
        raise AstError(f"not an ok {FORMAT} document")
    root = decode_arena(doc.get("nodes"), doc.get("root"))
    tables = doc.get("schema", {}).get("tables")
    if not isinstance(tables, list):
        raise AstError("schema.tables must be a list")
    stack = [root]
    while stack:
        n = stack.pop()
        if n.tag == "Table" and n.table >= len(tables):
            raise AstError(f"Table {n.table} is not in the schema")
        stack.extend(n.children())
    output = doc.get("output", {})
    if len(output.get("names", [])) != len(root.body.ann):
        raise AstError("output names disagree with the root arity")
    return doc["schema"], root
