"""Typed statement parameters ``$n``.

A statement may contain PostgreSQL placeholders ``$1 .. $n``; each one used must be declared with a type
(``[{"index": 1, "type": "date"}, ...]``).  A placeholder is bound exactly like a non-NULL constant of its declared
type: the same operator resolution and implicit casts as a literal of that type, e.g. ``$1 + INTERVAL '1' YEAR`` for
a ``date`` and ``l_quantity < $3`` for an ``integer`` (``int4`` cast to ``numeric``).  In the AST it is the
literal-sort node ``Param { index }`` under ``Lit``, annotated with the declared type the way a literal of that type
is (``numeric(p, s)`` as a ``numeric`` constant of scale ``s``, as a PostgreSQL parameter's typmod is not part of
its type); the document lists the declarations in ``params``.  Values are not the frontend's concern: the host
substitutes fixed ones and quantifies over free ones (the Rust frontend's parameter module).

Declared types: ``integer``, ``bigint``, ``numeric(p, s)`` with ``p <= 38`` (an ``i128`` coefficient), ``date`` and
``text`` (a non-NULL ``text`` constant: ``p_brand <> $1`` resolves like ``p_brand <> 'x'::text``, ``s LIKE $2`` like
``textlike``).  Everything else is a named refusal, as are placeholders without a declaration, declarations without a
placeholder and placeholders in LIMIT / OFFSET.  ``varchar(n)`` and ``char(n)`` parameters are refused: the meaning of
a length type modifier on a parameter is not designed (PostgreSQL ignores it on ``$n``, a CAST would truncate).
"""

from __future__ import annotations

from typing import TYPE_CHECKING, Any

from sqlglot import exp
from sqlglot.errors import ParseError, TokenError

from ..ast import Node
from ..parse import check_args
from ..refusal import Refusal
from ..sqltypes import ColTy, SqlType, numeric, sql_type

if TYPE_CHECKING:
    from ..bind import Binder, ExprScope

# numeric(p, s) parameters carry an i128 coefficient: |coeff| < 10^38.
NUMERIC_PARAM_MAX_PRECISION = 38


def param_coltype(ty: SqlType) -> ColTy:
    """The static type of a placeholder of declared type ``ty``: that of a non-NULL constant of the type."""
    if ty.kind == "numeric":
        return ColTy(numeric(), False, ty.scale)
    return ColTy(ty, False)


class ParamDecls:
    """The declared placeholders of one statement, and which of them the statement uses."""

    def __init__(self, types: dict[int, SqlType]):
        self.types = dict(sorted(types.items()))
        self.used: set[int] = set()

    @staticmethod
    def parse(decls: Any, dialect: str) -> "ParamDecls":
        if not isinstance(decls, list):
            raise Refusal("invalid_parameter_declaration", "the declaration must be a list", "params")
        types: dict[int, SqlType] = {}
        for d in decls:
            index = d.get("index") if isinstance(d, dict) else None
            if (not isinstance(d, dict) or set(d) != {"index", "type"} or not isinstance(index, int)
                    or isinstance(index, bool) or index < 1 or not isinstance(d["type"], str)):
                raise Refusal("invalid_parameter_declaration", f"entry {d!r}: expected {{\"index\": n >= 1, \"type\": text}}", "params")
            if index in types:
                raise Refusal("invalid_parameter_declaration", f"${index} is declared twice", "params")
            types[index] = _declared_type(d["type"], index, dialect)
        return ParamDecls(types)

    def bind(self, node: exp.Parameter, path: str, sql: str) -> Node:
        check_args(node, {"this"}, path)
        token = node.this
        if not (isinstance(token, exp.Literal) and not token.is_string and token.this.isdigit()):
            raise Refusal("unsupported_syntax", "only positional placeholders $1, $2, ...", path, sql)
        index = int(token.this)
        if index not in self.types:
            raise Refusal("undeclared_parameter", f"${index} has no declared type", path, sql)
        self.used.add(index)
        return Node("Lit", param_coltype(self.types[index]), lit=Node("Param", index=index))

    def check_all_used(self) -> None:
        unused = [i for i in self.types if i not in self.used]
        if unused:
            raise Refusal("unused_parameter", f"declared but not used: {', '.join(f'${i}' for i in unused)}", "params")

    def to_json(self) -> list[dict]:
        return [{"index": i, "type": t.to_json()} for i, t in self.types.items()]


def _declared_type(text: str, index: int, dialect: str) -> SqlType:
    where = f"params/${index}"
    try:
        ty = sql_type(exp.DataType.build(text, dialect=dialect), where)
    except (ParseError, TokenError, ValueError):
        raise Refusal("unsupported_parameter_type", f"${index}: type {text!r} does not parse", where) from None
    except Refusal as r:
        raise Refusal("unsupported_parameter_type", f"${index}: {r.detail}", where, text) from None
    supported = ty.kind in ("int4", "int8", "date", "text") or (ty.kind == "numeric" and ty.precision <= NUMERIC_PARAM_MAX_PRECISION)
    if not supported:
        raise Refusal("unsupported_parameter_type", f"${index}: {ty.pg_name()} (supported: integer, bigint, "
                      f"numeric(p, s) with p <= {NUMERIC_PARAM_MAX_PRECISION}, date, text)", where, text)
    return ty


def bind_parameter(b: Binder, node: exp.Parameter, sc: ExprScope, path: str) -> Node:
    """A placeholder ``$n`` as a value."""
    if b.params is None:
        raise Refusal("undeclared_parameter", "placeholders need a parameter declaration", path, b.sql(node))
    return b.params.bind(node, path, b.sql(node))
