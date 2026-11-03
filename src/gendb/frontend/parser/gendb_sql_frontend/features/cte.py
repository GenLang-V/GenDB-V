"""Non-recursive WITH queries: frontend normalization, no new semantics.

``WITH n [(cols)] AS (q) body`` means ``body`` with every reference to ``n`` replaced by the derived table
``(q) AS n (cols)``. Scope follows PostgreSQL: a WITH item sees the items before it and the enclosing query levels
(not the level of the reference: its names are bound where it is defined), later items and nested subqueries see
it, and an inner WITH item of the same name shadows it. Each reference is lowered separately (TPC-H Q15 uses
``revenue0`` twice); evaluation is deterministic without volatile functions, so this has the meaning of a
materialized WITH query, and ``[NOT] MATERIALIZED`` changes nothing. Every item is also bound once at its
definition, as PostgreSQL analyzes unreferenced items too. RECURSIVE is refused.  (The TPC-H view script is turned
into this form by ``parse.view_script_as_with``.)
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from sqlglot import exp

from ..parse import check_args, ident
from ..refusal import Refusal

if TYPE_CHECKING:
    from ..lower import Lowerer
    from ..scope import Level


@dataclass(frozen=True)
class CteDef:
    name: str
    select: exp.Select
    columns: tuple[str, ...]  # column aliases (possibly fewer than the output columns)
    parent: Level | None  # the query level the WITH belongs to: this item sees its outer levels
    scope: tuple[CteDef, ...]  # the WITH items visible to this item's query


def bind_with(lowerer: Lowerer, with_: exp.With, parent: Level | None, ctx_len: int,
              path: str) -> tuple[CteDef, ...]:
    """The WITH items of one query level added to the visible scope (each one bound once, at its definition)."""
    check_args(with_, {"expressions", "recursive"}, path)
    if with_.args.get("recursive"):
        raise Refusal("recursive_cte", "WITH RECURSIVE", path, with_.sql("postgres")[:200])
    scope = lowerer.ctes
    names: set[str] = set()
    for item in with_.expressions:
        check_args(item, {"this", "alias", "materialized"}, path)
        alias = item.args["alias"]
        check_args(alias, {"this", "columns"}, path)
        name = ident(alias.this)
        if name in names:
            raise Refusal("duplicate_cte", f"WITH query name {name!r} specified more than once", path)
        names.add(name)
        d = CteDef(name, lowerer.subquery_select(item.this, path),
                   tuple(ident(c) for c in alias.args.get("columns") or []), parent, scope)
        q, _ = lowerer.lower_cte(d, ctx_len, path)
        if len(d.columns) > len(q.ann):
            raise Refusal("cte_columns", f"WITH query {name!r} has {len(q.ann)} columns available but "
                          f"{len(d.columns)} columns specified", path)
        scope = scope + (d,)
    return scope
