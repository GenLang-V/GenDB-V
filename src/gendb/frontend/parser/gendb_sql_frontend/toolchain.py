"""The pinned frontend toolchain (``toolchain.json`` of the parser directory) and the checks against it.

Deployment policy: the package runs from source, and no GenDB binary embeds it.  A host runs ``<python> -m
gendb_sql_frontend translate`` with the parser directory as working directory.  ``toolchain.json`` names this host's
default interpreter and the environment variables a host may use to pick another interpreter or parser directory.
The frontend checks what it actually runs on, so a document can only come from the pinned Python minor version and
sqlglot version (otherwise the refusal ``toolchain_mismatch``).
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import sqlglot

from .refusal import Refusal

# The parser directory: it holds this package and toolchain.json; the AST schema is ../ast/ast_schema.json.
PARSER_DIR = Path(__file__).resolve().parents[1]
TOOLCHAIN: dict = json.loads((PARSER_DIR / "toolchain.json").read_text(encoding="utf-8"))


def check_toolchain() -> None:
    version = f"{sys.version_info.major}.{sys.version_info.minor}"
    if sqlglot.__version__ != TOOLCHAIN["sqlglot"] or version != TOOLCHAIN["python_version"]:
        raise Refusal("toolchain_mismatch",
                      f"sqlglot {sqlglot.__version__} / python {version}; pinned sqlglot {TOOLCHAIN['sqlglot']} / "
                      f"python {TOOLCHAIN['python_version']} ({TOOLCHAIN['python']})")


def check_dialect(dialect: str) -> None:
    if dialect not in TOOLCHAIN["dialects"]:
        raise Refusal("unsupported_dialect", f"dialect {dialect!r}; supported: {TOOLCHAIN['dialects']}")
