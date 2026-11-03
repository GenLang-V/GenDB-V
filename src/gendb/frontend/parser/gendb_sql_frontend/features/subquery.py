"""Subqueries: scalar subqueries, ``IN`` / ``NOT IN`` (subquery) and ``op ANY | SOME | ALL`` (subquery).

* ``(q)`` as a value -> ``Subquery(q)``: exactly one output column, nullable; the semantics gives NULL for no row and
  raises 21000 (``CardinalityViolation``) for more than one.
* ``x IN (q)`` -> ``AnyCmp(Eq, x, q)``; ``x NOT IN (q)`` is the binder's ``Not`` of it.
* ``x op ANY (q)`` / ``SOME`` -> ``AnyCmp(op, x, q)``.
* ``x op ALL (q)`` -> ``Not(AnyCmp(op', x, q))`` with ``op'`` the complement of ``op`` (``=``/``<>``, ``<``/``>=``,
  ``<=``/``>``). Exact under three-valued logic: ``x op' v`` is ``NOT (x op v)`` for non-NULL operands and Unknown
  otherwise, and ``AND`` over the rows is ``NOT`` of ``OR`` of the negations (empty: True).

The comparison ``x op col`` is resolved like any comparison (``Binder.cmp``) against the subquery's column; an
implicit cast on the column side becomes a ``Project`` over ``q``. The subquery sees the current environment
(correlation); it is lowered by the Lowerer, so ORDER BY / LIMIT inside it stays refused.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from sqlglot import exp

from ..ast import Node
from ..parse import check_args
from ..refusal import Refusal
from ..values import col

if TYPE_CHECKING:
    from ..bind import Binder, ExprScope

COMPLEMENT = {"Eq": "Ne", "Ne": "Eq", "Lt": "Ge", "Ge": "Lt", "Le": "Gt", "Gt": "Le"}


def bind_scalar_subquery(b: Binder, node: exp.Subquery, sc: ExprScope, path: str) -> Node:
    q, _ = b.lower_subquery(node, sc.level, f"{path}/subquery")
    _check_one_column(q, path, b.sql(node))
    return Node("Subquery", q.ann[0].with_nullable(True), q=q)


def bind_in_subquery(b: Binder, node: exp.In, sc: ExprScope, path: str) -> Node:
    """``x IN (subquery)``."""
    check_args(node, {"this", "query"}, path)
    return _any_cmp(b, "Eq", node.this, node.args["query"], sc, path, b.sql(node))


def bind_quantified(b: Binder, op: str, node: exp.Expression, sc: ExprScope, path: str) -> Node:
    """``x op ANY|SOME|ALL (subquery)`` (``node`` is the comparison)."""
    sql = b.sql(node)
    check_args(node, {"this", "expression"}, path)
    quantifier = node.expression
    if isinstance(node.this, (exp.Any, exp.All)):
        raise Refusal("unsupported_syntax", "a quantified subquery on the left of a comparison", path, sql)
    check_args(quantifier, {"this"}, path)
    body = quantifier.this
    while isinstance(body, exp.Paren):
        body = body.this
    if not isinstance(body, (exp.Subquery, exp.Select)):
        raise Refusal("quantified_array", f"{type(quantifier).__name__.upper()} over {type(body).__name__}", path, sql)
    if isinstance(quantifier, exp.Any):
        return _any_cmp(b, op, node.this, body, sc, path, sql)
    return Node("Not", p=_any_cmp(b, COMPLEMENT[op], node.this, body, sc, path, sql))


def _any_cmp(b: Binder, op: str, lhs_node: exp.Expression, query_node: exp.Expression, sc: ExprScope, path: str,
             sql: str) -> Node:
    """``lhs op ANY (query)`` as an ``AnyCmp`` predicate."""
    if isinstance(lhs_node, exp.Tuple):
        raise Refusal("row_subquery", "row-valued comparison with a subquery", path, sql)
    lhs = b.value(lhs_node, sc, path)
    q, _ = b.lower_subquery(query_node, sc.level, f"{path}/subquery")
    _check_one_column(q, path, sql)
    # The subquery's column, as the comparison sees it: position env_len of the subquery's environment.
    column = col(sc.level.env_len, q.ann[0])
    c = b.cmp(op, lhs, column, path, sql)
    if c.b != column:
        q = Node("Project", (c.b.ann,), exprs=(c.b,), input=q)
    return Node("AnyCmp", op=op, e=c.a, q=q)


def _check_one_column(q: Node, path: str, sql: str) -> None:
    if len(q.ann) != 1:
        raise Refusal("subquery_columns", f"the subquery returns {len(q.ann)} columns", path, sql)
