"""``AVG(x)``: PostgreSQL 18 ``avg(int4)``, ``avg(int8)``, ``avg(numeric)``.

NULLs are ignored and no non-NULL input gives NULL; otherwise the exact sum divided by the count with
``numeric_div`` (Verus ``spec::aggs::avg::avg_value``).  The result is ``numeric`` without a typmod whose display
scale depends on the sum and the count: static scale bound 1000, ``dscale_exact=False``, always nullable.  The
argument must be int4, int8 or numeric; PostgreSQL has no ``avg(unknown)`` resolution for an untyped literal
(``function avg(unknown) is not unique``), so it is refused.  PostgreSQL's int4 transition adds in int64 without an
overflow check (deviation D3, only at 2^32 rows or more); the Verus meaning is exact.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from sqlglot import exp

from ..ast import Node
from ..refusal import Refusal
from ..sqltypes import ColTy, numeric_bound
from ..values import NUM_KIND, Unknown

if TYPE_CHECKING:
    from ..bind import Binder


def bind_avg(b: Binder, node: exp.Avg, arg: Node | Unknown, path: str) -> tuple[Node, ColTy]:
    if isinstance(arg, Unknown) or arg.ann.ty.family != "number":
        shown = "unknown" if isinstance(arg, Unknown) else arg.ann.ty.pg_name()
        raise Refusal("type_mismatch", f"no function avg({shown})", path, b.sql(node))
    return Node("Avg", kind=NUM_KIND[arg.ann.ty.kind], arg=arg), numeric_bound(True)
