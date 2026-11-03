"""``EXTRACT(YEAR | MONTH | DAY FROM x)`` for ``x`` a ``date`` or ``timestamp``: PostgreSQL 18 ``extract_date`` /
``extract_timestamp``.

The result is ``Call(ExtractYear | ExtractMonth | ExtractDay, [x])`` of type ``numeric`` (no typmod) with the exact
display scale 0, nullable if ``x`` is; meaning Verus ``spec::fns::extract`` (the civil date of the proleptic
Gregorian calendar; no year 0: 1 BC is -1).  Other fields are refused (``unsupported_extract_field``); an untyped
literal operand is ambiguous in PostgreSQL (``type_mismatch``).
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from sqlglot import exp

from ..ast import Node
from ..parse import check_args
from ..refusal import Refusal
from ..sqltypes import ColTy, numeric
from ..values import Unknown

if TYPE_CHECKING:
    from ..bind import Binder, ExprScope

FIELDS = {"YEAR": "ExtractYear", "MONTH": "ExtractMonth", "DAY": "ExtractDay"}


def bind_extract(b: Binder, node: exp.Extract, sc: ExprScope, path: str) -> Node:
    check_args(node, {"this", "expression"}, path)
    field = node.this
    name = field.name.upper() if isinstance(field, (exp.Var, exp.Identifier)) else None
    if name not in FIELDS:
        raise Refusal("unsupported_extract_field", f"EXTRACT field {field.sql()!r}", path, b.sql(node))
    x = b.value(node.expression, sc, path)
    if isinstance(x, Unknown) or x.ann.ty.kind not in ("date", "timestamp"):
        what = "an untyped literal" if isinstance(x, Unknown) else x.ann.ty.pg_name()
        raise Refusal("type_mismatch", f"EXTRACT from {what} (date or timestamp only)", path, b.sql(node))
    return Node("Call", ColTy(numeric(), x.ann.nullable, 0), f=FIELDS[name], args=(x,))
