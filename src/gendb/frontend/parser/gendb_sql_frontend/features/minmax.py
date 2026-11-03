"""``MIN(x)`` / ``MAX(x)``: PostgreSQL 18 ``min``/``max`` over int4, int8, numeric, date, timestamp, text and
char(n) (Verus ``spec::aggs::minmax``).

NULLs are ignored and no non-NULL input gives NULL, so the result is always nullable.  The value is one of the
argument values (the first of equal extreme values, reference choice R1), so a numeric result keeps its own display
scale: the static bound and ``dscale_exact`` are the argument's.  Result types are PostgreSQL's: the aggregate's
declared type drops the typmod (``numeric``, ``bpchar``), and varchar resolves to ``min(text)`` (binary-coercible,
one Verus ``Text`` family).  An untyped literal resolves to text, as in PostgreSQL.  There is no ``min(boolean)`` in
PostgreSQL: refused as ``type_mismatch``.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from sqlglot import exp

from ..ast import Node
from ..refusal import Refusal
from ..sqltypes import TEXT, ColTy, SqlType, numeric
from ..values import Unknown, default_type

if TYPE_CHECKING:
    from ..bind import Binder


def bind_min(b: Binder, node: exp.Min, arg: Node | Unknown, path: str) -> tuple[Node, ColTy]:
    return _bind_extreme("Min", b, node, arg, path)


def bind_max(b: Binder, node: exp.Max, arg: Node | Unknown, path: str) -> tuple[Node, ColTy]:
    return _bind_extreme("Max", b, node, arg, path)


def _bind_extreme(tag: str, b: Binder, node: exp.AggFunc, arg: Node | Unknown, path: str) -> tuple[Node, ColTy]:
    e = default_type(arg, path)
    t = e.ann
    kind = t.ty.kind
    if kind == "bool":
        raise Refusal("type_mismatch", f"no function {tag.lower()}(boolean)", path, b.sql(node))
    if kind == "numeric":
        ty = ColTy(numeric(), True, t.dscale, t.dscale_exact)
    elif kind == "bpchar":
        ty = ColTy(SqlType("bpchar"), True)
    elif kind == "varchar":
        ty = ColTy(TEXT, True)
    else:
        ty = ColTy(t.ty, True)
    return Node(tag, e=e), ty
