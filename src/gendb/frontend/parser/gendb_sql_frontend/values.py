"""Typed value nodes and PostgreSQL's value typing rules, shared by the binder and the feature modules.

* constructors of annotated AST value nodes: column references, literals, typed NULLs and the exact casts;
* untyped literals (PostgreSQL's ``unknown``: a string literal or NULL) and their coercion to a context type;
* PostgreSQL's implicit numeric casts and ``select_common_type`` for the fragment's types.

String and date literals become source components: the frontend never does calendar or decimal arithmetic.
"""

from __future__ import annotations

import re
from dataclasses import dataclass

from sqlglot import exp

from .ast import NUMERIC_DSCALE_MAX, NUMERIC_INT_DIGITS_MAX, Node, valid_ymd
from .refusal import Refusal
from .sqltypes import (DATE, INT4, INT4_MAX, INT4_MIN, INT8, INT8_MAX, INT8_MIN, TEXT, TIMESTAMP, ColTy,
                       SqlType, numeric)

UNSIGNED_INT_TEXT = re.compile(r"[0-9]+\Z")
UNSIGNED_DECIMAL_TEXT = re.compile(r"(?P<i>[0-9]*)(?:\.(?P<f>[0-9]*))?\Z")
SIGNED_INT_TEXT = re.compile(r"[+-]?[0-9]+\Z")
SIGNED_DECIMAL_TEXT = re.compile(r"(?P<s>[+-]?)(?P<i>[0-9]*)(?:\.(?P<f>[0-9]*))?\Z")
ISO_DATE_TEXT = re.compile(r"(?P<y>[0-9]{4})-(?P<m>[0-9]{2})-(?P<d>[0-9]{2})\Z")

# The AST's NumKind of each number type.
NUM_KIND = {"int4": "Int4", "int8": "Int8", "numeric": "Numeric"}


# ---------------------------------------------------------------------------------------------
# Typed node constructors (Verus AST constructors, annotated with PostgreSQL-level types).

def col(index: int, ty: ColTy) -> Node:
    return Node("Col", ty, index=index)


def lit(literal: Node, ty: ColTy) -> Node:
    return Node("Lit", ty, lit=literal)


def null_of(ty: ColTy, path: str, sql: str) -> Node:
    """A typed NULL; numeric needs a static scale (the Verus ``ScalarTy::Numeric { scale }``)."""
    t = ty.with_nullable(True)
    if ty.ty.kind == "numeric" and ty.dscale is None:
        raise Refusal("unsupported_cast", "NULL of numeric without a static scale", path, sql)
    return lit(Node("Null", ty=t.scalar()), t)


def int_literal(value: int) -> Node:
    """PostgreSQL integer constant typing: int4 if it fits, else int8, else numeric."""
    if INT4_MIN <= value <= INT4_MAX:
        return lit(Node("Int", v=value, kind="Int4"), ColTy(INT4, False))
    if INT8_MIN <= value <= INT8_MAX:
        return lit(Node("Int", v=value, kind="Int8"), ColTy(INT8, False))
    return num_literal(value, 0, "", str(value))


def num_literal(coeff: int, scale: int, path: str, sql: str) -> Node:
    """The numeric constant ``coeff * 10^-scale`` with its exact display scale."""
    if scale > NUMERIC_DSCALE_MAX:
        raise Refusal("numeric_scale_limit", f"literal scale {scale} > {NUMERIC_DSCALE_MAX}", path, sql)
    if len(str(abs(coeff))) - scale > NUMERIC_INT_DIGITS_MAX:
        raise Refusal("invalid_literal", "literal overflows PostgreSQL's numeric format", path, sql)
    return lit(Node("Num", coeff=coeff, scale=scale), ColTy(numeric(), False, scale))


def cast(e: Node, conversion: str) -> Node:
    """One of the exact casts of the AST (``CastOp``)."""
    t = e.ann
    out = {"Int4ToInt8": ColTy(INT8, t.nullable),
           "IntToNumeric": ColTy(numeric(), t.nullable, 0),
           "DateToTimestamp": ColTy(TIMESTAMP, t.nullable)}[conversion]
    return Node("Cast", out, cast=conversion, arg=e)


def _decimal_digits(m: re.Match) -> tuple[int, int]:
    """(unsigned coefficient, scale) of a matched ``[digits][.digits]`` text."""
    frac = m["f"] or ""
    return int((m["i"] or "0") + frac), len(frac)


# ---------------------------------------------------------------------------------------------
# Untyped literals.

@dataclass(frozen=True)
class Unknown:
    """A string literal or NULL whose type comes from its context (PostgreSQL's ``unknown``)."""
    text: str | None  # None for NULL
    sql: str


def coerce_unknown(u: Unknown, target: ColTy, path: str, explicit: bool = False) -> Node:
    """Give an untyped literal a type: the other operand's type for implicit coercion (so a literal compared with
    char(n) is right-trimmed), the declared type for an explicit cast."""
    ty = target.ty
    if u.text is None:
        return null_of(target, path, u.sql)
    s = u.text
    if ty.kind in ("int4", "int8"):
        if not SIGNED_INT_TEXT.match(s):
            raise Refusal("unsupported_literal", f"{s!r} as {ty.pg_name()} (plain decimal digits only)", path, u.sql)
        v = int(s)
        lo, hi = (INT4_MIN, INT4_MAX) if ty.kind == "int4" else (INT8_MIN, INT8_MAX)
        if not lo <= v <= hi:
            raise Refusal("invalid_literal", f"{s!r} is out of range for {ty.pg_name()}", path, u.sql)
        return lit(Node("Int", v=v, kind=NUM_KIND[ty.kind]), ColTy(ty, False))
    if ty.kind == "numeric":
        m = SIGNED_DECIMAL_TEXT.match(s)
        if not m or not (m["i"] or m["f"]):
            raise Refusal("unsupported_literal", f"{s!r} as numeric (plain decimal notation only)", path, u.sql)
        if explicit and ty.precision is not None:
            raise Refusal("unsupported_cast", f"literal cast to {ty.pg_name()} (rounding to a typmod is not in the fragment)", path, u.sql)
        coeff, scale = _decimal_digits(m)
        return num_literal(-coeff if m["s"] == "-" else coeff, scale, path, u.sql)
    if ty.kind == "date":
        m = ISO_DATE_TEXT.match(s)
        if not m:
            raise Refusal("unsupported_literal", f"date {s!r} (only YYYY-MM-DD)", path, u.sql)
        y, mo, d = int(m["y"]), int(m["m"]), int(m["d"])
        if y < 1 or not valid_ymd(y, mo, d):
            raise Refusal("invalid_literal", f"date {s!r} is not a calendar date", path, u.sql)
        return lit(Node("Date", y=y, m=mo, d=d), ColTy(DATE, False))
    if ty.family == "text":
        if "\x00" in s:
            raise Refusal("invalid_literal", "text literal contains NUL", path, u.sql)
        if not explicit:
            # The operator's argument type: bpchar (no length) for char(n), text for varchar(n) and text.
            ty = SqlType("bpchar") if ty.kind == "bpchar" else TEXT
        value = s.rstrip(" ") if ty.kind == "bpchar" else s
        if ty.length is not None and len(value) > ty.length:
            raise Refusal("unsupported_cast", f"literal longer than {ty.pg_name()} (PostgreSQL would truncate)", path, u.sql)
        return lit(Node("Text", bytes=value), ColTy(ty, False))
    raise Refusal("unsupported_literal", f"literal {s!r} of type {ty.pg_name()}", path, u.sql)


def default_type(v: Node | Unknown, path: str) -> Node:
    """An untyped literal with no context resolves to text (PostgreSQL 10+)."""
    return coerce_unknown(v, ColTy(TEXT, False), path) if isinstance(v, Unknown) else v


def numeric_token(node: exp.Expression) -> tuple[int, int, bool] | None:
    """(coefficient, scale, is_integer_token) of a possibly negated numeric constant, None if ``node`` is none.

    PostgreSQL's grammar folds unary minus into a numeric constant (``doNegate``), also through parentheses, so
    ``-2147483648`` is an int4 constant."""
    sign = 1
    while True:
        if isinstance(node, exp.Paren):
            node = node.this
        elif isinstance(node, exp.Neg):
            sign, node = -sign, node.this
        else:
            break
    if not (isinstance(node, exp.Literal) and not node.is_string):
        return None
    text = node.this
    if UNSIGNED_INT_TEXT.match(text):
        return sign * int(text), 0, True
    m = UNSIGNED_DECIMAL_TEXT.match(text)
    if not m or not (m["i"] or m["f"]):
        raise Refusal("unsupported_literal", f"numeric literal {text!r} (plain decimal notation only)", "", text)
    coeff, scale = _decimal_digits(m)
    return sign * coeff, scale, False


# ---------------------------------------------------------------------------------------------
# Implicit casts and common types.

def unify_numbers(a: Node, b: Node) -> tuple[Node, Node]:
    """PostgreSQL's implicit numeric casts: int4 -> int8 -> numeric."""
    ka, kb = a.ann.ty.kind, b.ann.ty.kind
    if ka == kb:
        return a, b
    if "numeric" in (ka, kb):
        return (a if ka == "numeric" else cast(a, "IntToNumeric"), b if kb == "numeric" else cast(b, "IntToNumeric"))
    return (cast(a, "Int4ToInt8") if ka == "int4" else a, cast(b, "Int4ToInt8") if kb == "int4" else b)


# Implicit-cast order inside a family: a later type absorbs an earlier one (int4 -> int8 -> numeric,
# date -> timestamp).
_IMPLICIT_CAST_RANK = {"int4": 0, "int8": 1, "numeric": 2, "date": 0, "timestamp": 1}


def common_type(first: Node | Unknown, rest: list[Node | Unknown]) -> SqlType | None:
    """PostgreSQL's ``select_common_type([first] + rest)`` without a context: the first typed input decides, a later
    type replaces it only if the cast to it is implicit and the reverse is not (int4 -> int8 -> numeric,
    date -> timestamp; text, varchar and bpchar cast implicitly both ways, so the first string type wins); all
    untyped gives text; mixed families give None.  Type modifiers are dropped, as in ``coerce_to_common_type``."""
    types = [v.ann.ty for v in (first, *rest) if isinstance(v, Node)]
    if not types:
        return TEXT
    if len({t.family for t in types}) > 1:
        return None
    chosen = types[0]
    if chosen.kind in _IMPLICIT_CAST_RANK:
        chosen = max(types, key=lambda t: _IMPLICIT_CAST_RANK[t.kind])
    return numeric() if chosen.kind == "numeric" else SqlType(chosen.kind)


def eq_left_input_type(a: Node | Unknown, eq: Node) -> ColTy:
    """The type of the left argument of PostgreSQL's operator for ``a = b``, where ``eq`` is ``Binder.cmp``'s
    resolution of it (NULLIF's result type is this type).

    ``cmp`` casts numbers explicitly, so ``eq.a`` already has the input type there.  Text-family operands get no
    node: every text-family ``=`` except bpchar = bpchar is ``texteq(text, text)``, whose left input is ``text``
    (varchar relabelled, char(n) through the rtrim cast, which is the identity on the core's right-trimmed char(n)
    values).  An untyped operand is coerced to the input type without a type modifier."""
    left = eq.a.ann
    if left.ty.family == "text" and not (left.ty.kind == "bpchar" and eq.b.ann.ty.kind == "bpchar"):
        return ColTy(TEXT, left.nullable)
    ty = left.ty
    if isinstance(a, Unknown):
        ty = numeric() if ty.kind == "numeric" else SqlType(ty.kind)
    return ColTy(ty, left.nullable, left.dscale, left.dscale_exact)

