"""``s [NOT] LIKE p [ESCAPE e]``: PostgreSQL 18 operator resolution for ``textlike`` / ``bpcharlike`` and
``like_escape``.

The result is ``Call(Like, [s, p, e])`` of type ``boolean`` (nullable if an operand is); as a condition the binder
wraps it in ``OfBool``, and ``NOT LIKE`` is ``Not(OfBool(...))`` (both done by ``bind.py``).  The meaning is Verus
``spec::fns::like``: PostgreSQL's ``like_escape`` (22025 for an escape of more than one character) followed by its
matcher ``MatchText`` over characters.

* Every operand must be in the text family (``text``, ``varchar(n)``, ``char(n)``) or an untyped literal / NULL,
  which is ``text`` (PostgreSQL resolves ``unknown ~~ unknown`` to ``text ~~ text``; a literal subject is never
  blank-trimmed).  Other types have no ``~~`` operator (PostgreSQL 42883): ``type_mismatch``.
* Without ``ESCAPE`` the escape is ``'\\'`` (PostgreSQL's default); ``ESCAPE ''`` disables escaping.
* A ``char(n)`` subject resolves to ``bpcharlike``, which matches the stored blank-padded value (confirmed on
  PostgreSQL 18: ``'ab'::char(4) LIKE 'ab'`` is false): it becomes ``PadBpchar(s, n)``.  A ``char(n)`` pattern or
  escape goes through the implicit ``bpchar -> text`` cast, which strips trailing blanks: the identity on canonical
  stored values, so it is passed unchanged.
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from sqlglot import exp

from ..ast import Node
from ..parse import check_args
from ..refusal import Refusal
from ..sqltypes import BOOL, TEXT, ColTy
from ..values import Unknown, coerce_unknown, int_literal

if TYPE_CHECKING:
    from ..bind import Binder, ExprScope


def bind_like(b: Binder, node: exp.Like | exp.Escape, sc: ExprScope, path: str) -> Node:
    check_args(node, {"this", "expression"}, path)
    if isinstance(node, exp.Escape):
        like, escape_node = node.this, node.expression
        if not isinstance(like, exp.Like):
            raise Refusal("unsupported_operator", f"ESCAPE on {type(like).__name__}", path, b.sql(node))
        check_args(like, {"this", "expression"}, path)
    else:
        like, escape_node = node, None
    subject = _text_operand(b, like.this, sc, path, "subject", node)
    pattern = _text_operand(b, like.expression, sc, path, "pattern", node)
    if escape_node is None:
        escape = Node("Lit", ColTy(TEXT, False), lit=Node("Text", bytes="\\"))
    else:
        escape = _text_operand(b, escape_node, sc, path, "escape", node)
    if subject.ann.ty.kind == "bpchar":
        width = subject.ann.ty.length
        if width is None:
            raise Refusal("like_bpchar_without_length", "char subject without a length", path, b.sql(node))
        subject = Node("Call", ColTy(TEXT, subject.ann.nullable), f="PadBpchar", args=(subject, int_literal(width)))
    nullable = subject.ann.nullable or pattern.ann.nullable or escape.ann.nullable
    return Node("Call", ColTy(BOOL, nullable), f="Like", args=(subject, pattern, escape))


def _text_operand(b: Binder, node: exp.Expression, sc: ExprScope, path: str, what: str,
                  whole: exp.Expression) -> Node:
    v = b.value(node, sc, path)
    if isinstance(v, Unknown):
        return coerce_unknown(v, ColTy(TEXT, False), path)
    if v.ann.ty.family != "text":
        raise Refusal("type_mismatch", f"LIKE {what} of type {v.ann.ty.pg_name()} (no ~~ operator)", path, b.sql(whole))
    return v
