"""CASE, COALESCE and NULLIF, normalized to the lazy ``If`` constructor.

* searched ``CASE WHEN c1 THEN r1 ... ELSE d END`` -> ``If(c1, r1, If(..., d))``; a missing ELSE is a typed NULL;
* simple ``CASE x WHEN v THEN r ...`` -> the searched form with ``x = v`` (re-evaluating ``x`` gives the same value or
  the same first error: evaluation is deterministic).  As in PostgreSQL's ``transformCaseExpr``, an untyped ``x`` (a
  string literal or NULL) is first resolved to ``text``, then compared, so ``CASE 'ab ' WHEN c4`` is
  ``text = bpchar`` and ``CASE NULL WHEN i4`` has no operator;
* ``COALESCE(a, rest)`` -> ``If(NOT (a IS NULL), a, COALESCE(rest))``, ``COALESCE(a)`` -> ``a``;
* ``NULLIF(a, b)`` -> ``If(a' = b', NULL, a')`` where ``a' = b'`` is PostgreSQL's resolution of ``a = b``; its result
  type is that operator's left input type (``values.eq_left_input_type``: ``text`` for every text-family pair except
  bpchar = bpchar).

Result type: PostgreSQL's ``select_common_type`` over the results (CASE: ELSE first, then the THENs; COALESCE: the
arguments), each result coerced to it with the fragment's exact implicit casts; the type modifier is kept only when
every result has exactly that type and modifier (``select_common_typmod``). A numeric result's scale bound is the
largest branch scale; it is exact only when every non-NULL branch has the same exact scale.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from sqlglot import exp

from ..ast import Node
from ..parse import check_args
from ..refusal import Refusal
from ..sqltypes import ColTy, SqlType
from ..values import Unknown, cast, coerce_unknown, common_type, eq_left_input_type, null_of

if TYPE_CHECKING:
    from ..bind import Binder, ExprScope


def bind_case(b: Binder, node: exp.Case, sc: ExprScope, path: str) -> Node:
    sql = b.sql(node)
    check_args(node, {"this", "ifs", "default"}, path)
    operand = node.args.get("this")
    x = b.expr(operand, sc, path) if operand is not None else None
    conds, thens = [], []
    for i, w in enumerate(node.args.get("ifs") or []):
        check_args(w, {"this", "true"}, path)
        p = f"{path}/when{i}"
        if x is None:
            conds.append(b.pred(w.this, sc, p))
        else:
            conds.append(b.cmp("Eq", x, b.value(w.this, sc, p), p, sql))
        thens.append(b.value(w.args["true"], sc, p))
    default = node.args.get("default")
    else_value = b.value(default, sc, f"{path}/else") if default is not None else Unknown(None, "NULL")
    nodes, result = _coerce_to_common_type([else_value, *thens], "CASE", path, sql)
    return _if_chain(conds, nodes[1:], nodes[0], result)


def bind_coalesce(b: Binder, node: exp.Coalesce, sc: ExprScope, path: str) -> Node:
    sql = b.sql(node)
    check_args(node, {"this", "expressions"}, path)
    args = [node.this, *(node.expressions or [])]
    values = [b.value(a, sc, f"{path}/coalesce{i}") for i, a in enumerate(args)]
    nodes, result = _coerce_to_common_type(values, "COALESCE", path, sql)
    conds = [Node("Not", p=Node("IsNull", e=n)) for n in nodes[:-1]]
    return _if_chain(conds, nodes[:-1], nodes[-1], result)


def bind_nullif(b: Binder, node: exp.Nullif, sc: ExprScope, path: str) -> Node:
    sql = b.sql(node)
    check_args(node, {"this", "expression"}, path)
    a = b.value(node.this, sc, path)
    eq = b.cmp("Eq", a, b.value(node.expression, sc, path), path, sql)
    ty = eq_left_input_type(a, eq)
    return _if_node(eq, null_of(ty, path, sql), eq.a, ty.ty)


def _coerce_to_common_type(values: list[Node | Unknown], what: str, path: str,
                           sql: str) -> tuple[list[Node], SqlType]:
    """(coerced nodes, result SqlType) for the results ``values`` in PostgreSQL's order."""
    common = common_type(values[0], list(values[1:]))
    if common is None:
        shown = ", ".join(v.ann.ty.pg_name() for v in values if not isinstance(v, Unknown))
        raise Refusal("type_mismatch", f"{what} types {shown} cannot be matched", path, sql)
    typed = [v for v in values if not isinstance(v, Unknown)]
    keep_typmod = bool(typed) and len(typed) == len(values) and all(v.ann.ty == typed[0].ann.ty for v in typed) \
        and typed[0].ann.ty.kind == common.kind
    result = typed[0].ann.ty if keep_typmod else common
    coerced: list[Node | None] = []  # None: an untyped NULL, typed below once the scale bound is known
    for v in values:
        if isinstance(v, Unknown):
            coerced.append(None if v.text is None else coerce_unknown(v, ColTy(common, False), path))
            continue
        k = v.ann.ty.kind
        if k != common.kind:
            if common.kind == "int8" and k == "int4":
                v = cast(v, "Int4ToInt8")
            elif common.kind == "numeric" and k in ("int4", "int8"):
                v = cast(v, "IntToNumeric")
            elif common.kind == "timestamp" and k == "date":
                v = cast(v, "DateToTimestamp")
            elif common.kind == "bpchar":
                raise Refusal("case_bpchar_coercion", f"{what} common type is bpchar; a {v.ann.ty.pg_name()} result would be coerced blank-insensitively", path, sql)
            # text/varchar results under a text/varchar common type, and bpchar under text/varchar (the rtrim
            # cast, the identity on canonical char(n) values), are the same value.
        coerced.append(v)
    scales = [n.ann.dscale for n in coerced if n is not None and common.kind == "numeric"]
    bound = max(scales) if scales else (0 if common.kind == "numeric" else None)
    nodes = [null_of(ColTy(common, True, bound), path, sql) if n is None else n for n in coerced]
    return nodes, result


def _if_node(cond: Node, a: Node, b: Node, result: SqlType) -> Node:
    """``If`` with its annotation: PostgreSQL result type ``result``; numeric bound = max, exact iff both exact with
    the same scale (a typed NULL branch has no value, so it does not affect exactness)."""
    ta, tb = a.ann, b.ann
    if result.kind == "numeric":
        exacts = [t for n, t in ((a, ta), (b, tb)) if not _is_null_literal(n)]
        exact = all(t.dscale_exact for t in exacts) and len({t.dscale for t in exacts}) <= 1
        ann = ColTy(result, ta.nullable or tb.nullable, max(ta.dscale, tb.dscale), exact)
    else:
        ann = ColTy(result, ta.nullable or tb.nullable)
    return Node("If", ann, cond=cond, then_e=a, else_e=b)


def _is_null_literal(n: Node) -> bool:
    return n.tag == "Lit" and n.lit.tag == "Null"


def _if_chain(conds: list[Node], results: list[Node], default: Node, result: SqlType) -> Node:
    """``If(c1, r1, If(c2, r2, ... default))``."""
    out = default
    for c, r in reversed(list(zip(conds, results))):
        out = _if_node(c, r, out, result)
    return out
