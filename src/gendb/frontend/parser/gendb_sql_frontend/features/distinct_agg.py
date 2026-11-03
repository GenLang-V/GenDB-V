"""``agg(DISTINCT x)``: ``COUNT``, ``SUM`` and ``AVG`` over the non-NULL values, one per SQL not-distinct class
(Verus ``spec::equality::distinct_vals``: ``1.0`` and ``1.00`` are one value, the first occurrence represents it,
reference choice R1).  The node is ``DistinctAgg(inner)`` with the inner aggregate's type.  ``MIN``/``MAX(DISTINCT
x)`` equal ``MIN``/``MAX(x)`` and are normalized to them.
"""

from __future__ import annotations

from ..ast import Node
from ..refusal import Refusal
from ..sqltypes import ColTy


def bind_distinct_agg(name: str, agg: Node, ty: ColTy, path: str, sql: str) -> tuple[Node, ColTy]:
    if agg.tag in ("Min", "Max"):
        return agg, ty
    if agg.tag not in ("Count", "Sum", "Avg"):
        raise Refusal("unsupported_aggregate", f"{name}(DISTINCT ...)", path, sql)
    return Node("DistinctAgg", inner=agg), ty
