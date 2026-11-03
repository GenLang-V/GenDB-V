"""``SUBSTRING(s FROM start [FOR len])`` / ``substring(s, start [, len])`` / ``substr``: PostgreSQL 18
``text_substr`` / ``text_substr_no_len``.

The result is ``Call(Substring3, [s, start, len])`` or ``Call(Substring2, [s, start])`` of type ``text`` (nullable if
an argument is); meaning Verus ``spec::fns::substring`` (character positions, 22011 for a negative length, int4
overflow of ``start + len`` means "to the end").

* ``s`` must be in the text family or an untyped literal (``text``).  A ``char(n)`` argument goes through the
  implicit ``bpchar -> text`` cast (trailing blanks stripped): the identity on canonical stored values, so it is
  passed unchanged.
* ``start`` and ``len`` must be ``integer``: PostgreSQL has no ``bigint`` or ``numeric`` variant (42883,
  ``type_mismatch``).  An untyped literal ``len`` is an integer literal.  An untyped (string) ``start`` selects the
  regular-expression form ``substring(text, text)``: refused (``substring_regex``).
"""

from __future__ import annotations

from typing import TYPE_CHECKING

from sqlglot import exp

from ..ast import Node
from ..parse import check_args
from ..refusal import Refusal
from ..sqltypes import INT4, TEXT, ColTy
from ..values import Unknown, coerce_unknown

if TYPE_CHECKING:
    from ..bind import Binder, ExprScope


def bind_substring(b: Binder, node: exp.Substring, sc: ExprScope, path: str) -> Node:
    check_args(node, {"this", "start", "length"}, path)
    if node.args.get("start") is None:
        raise Refusal("unsupported_syntax", "SUBSTRING without FROM", path, b.sql(node))
    s = b.value(node.this, sc, path)
    if isinstance(s, Unknown):
        s = coerce_unknown(s, ColTy(TEXT, False), path)
    elif s.ann.ty.family != "text":
        raise Refusal("type_mismatch", f"SUBSTRING of {s.ann.ty.pg_name()}", path, b.sql(node))
    start = b.value(node.args["start"], sc, path)
    if isinstance(start, Unknown):
        raise Refusal("substring_regex", "an untyped FROM operand selects substring(text, text)", path, b.sql(node))
    args = [s, start]
    if node.args.get("length") is not None:
        length = b.value(node.args["length"], sc, path)
        if isinstance(length, Unknown):
            length = coerce_unknown(length, ColTy(INT4, False), path)
        args.append(length)
    for a in args[1:]:
        if a.ann.ty.kind != "int4":
            raise Refusal("type_mismatch", f"SUBSTRING position/length of type {a.ann.ty.pg_name()} "
                          "(PostgreSQL has only integer)", path, b.sql(node))
    nullable = any(a.ann.nullable for a in args)
    return Node("Call", ColTy(TEXT, nullable), f="Substring3" if len(args) == 3 else "Substring2", args=tuple(args))
