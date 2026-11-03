"""Division ``a / b``: PostgreSQL 18 operator resolution for ``int4div``, ``int8div`` and ``numeric_div``.

The operands resolve like the other arithmetic operators (``Binder._arith``): an untyped literal takes the other
operand's type, both operands must be numbers, and PostgreSQL's implicit casts are explicit nodes (int4 -> int8 when
the other side is int8, an integer -> numeric when the other side is numeric).  The result is
``Call(DivInt4 | DivInt8 | DivNumeric, [a, b])``:

* ``int4 / int4`` is int4 and ``int8 / int8`` int8: truncation toward zero, 22012 for a zero divisor, 22003 for
  ``MIN / -1`` (Verus ``spec::fns::div::int_div``);
* ``numeric / numeric`` is ``numeric`` without a typmod whose display scale depends on the operand values
  (``select_div_scale``, at most 1000): static scale bound 1000, ``dscale_exact=False``.

Nullable if an operand is.  Division by an untyped NULL is ``NULL`` of the other operand's type, as in PostgreSQL.
sqlglot marks PostgreSQL's ``/`` as ``typed`` (integer division for integer operands); any other form is refused.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from sqlglot import exp

from ..ast import Node
from ..parse import check_args
from ..refusal import Refusal
from ..sqltypes import ColTy, numeric_bound
from ..values import Unknown, coerce_unknown, unify_numbers

if TYPE_CHECKING:
    from ..bind import Binder, ExprScope

DIV_FN = {"int4": "DivInt4", "int8": "DivInt8", "numeric": "DivNumeric"}


def bind_div(b: Binder, node: exp.Div, sc: ExprScope, path: str) -> Node:
    check_args(node, {"this", "expression", "typed"}, path)
    if not node.args.get("typed"):
        raise Refusal("unsupported_syntax", "division without PostgreSQL's typed (integer) semantics", path, b.sql(node))
    x, y = b.value(node.this, sc, path), b.value(node.expression, sc, path)
    if isinstance(x, Unknown) and isinstance(y, Unknown):
        raise Refusal("type_mismatch", "operator / has two untyped operands", path, b.sql(node))
    if isinstance(x, Unknown):
        x = coerce_unknown(x, y.ann, path)
    if isinstance(y, Unknown):
        y = coerce_unknown(y, x.ann, path)
    tx, ty = x.ann.ty, y.ann.ty
    if tx.family != "number" or ty.family != "number":
        reason = "unsupported_operator" if {tx.family, ty.family} <= {"datetime", "number"} else "type_mismatch"
        raise Refusal(reason, f"no operator {tx.pg_name()} / {ty.pg_name()} in the fragment", path, b.sql(node))
    x, y = unify_numbers(x, y)
    kind = x.ann.ty.kind
    nullable = x.ann.nullable or y.ann.nullable
    out = numeric_bound(nullable) if kind == "numeric" else ColTy(x.ann.ty, nullable)
    return Node("Call", out, f=DIV_FN[kind], args=(x, y))
