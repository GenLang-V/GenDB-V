"""Scalar expressions and predicates: name binding and PostgreSQL type resolution.

Each handler accepts one sqlglot node class, consumes exactly the arguments it understands (``check_args``) and
returns a typed AST node.  Operator resolution follows PostgreSQL's choice of operator and implicit casts for the
fragment:

* numbers: int4 op int4 -> int4, int8 op int8 -> int8, int4 with int8 -> the int4 side cast to int8, an integer with
  numeric -> the integer side cast to numeric (exact).  Comparisons between int4 and int8 use PostgreSQL's
  cross-type operators and get no cast;
* date/timestamp comparisons use the exact cross-type operators (no cast); ``date +/- INTERVAL`` is a timestamp
  (``DateToTimestamp`` then ``AddInterval``);
* text, varchar and char(n) compare as one family (bytes, C collation).  char(n) values are stored right-trimmed, so
  this is PostgreSQL's result for bpchar op bpchar, bpchar op unknown and bpchar op text (texteq on the
  right-trimmed value) and for text/varchar among themselves.  bpchar op varchar resolves to the blank-insensitive
  bpchar operator, which needs an rtrim cast the core does not have: refused (``bpchar_varchar_comparison``);
* untyped literals (``'...'``, ``NULL``) take the type of the other operand (a literal compared with char(n) is
  right-trimmed, as bpchar input is; ``values.coerce_unknown``);
* ``IN`` lists follow ``transformAExprIn``, including the common type of two or more items without current-level
  columns (``Binder._in_list``).

``INTERVAL 'n' YEAR`` becomes ``12 n`` months by the definition of the unit.  Constructs with their own rules live
in ``features/`` and are dispatched from the tables below.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable

from sqlglot import exp

from .ast import NUMERIC_DSCALE_MAX, Node
from .features import avg, case, distinct_agg, div, extract, like, minmax, subquery, substring
from .features.params import ParamDecls, bind_parameter
from .parse import check_args, ident
from .refusal import Refusal
from .scope import Level
from .sqltypes import BOOL, INT4_MAX, INT4_MIN, INT8, TIMESTAMP, ColTy, numeric, sql_type
from .values import (NUM_KIND, SIGNED_INT_TEXT, Unknown, cast, coerce_unknown, col, common_type, default_type,
                     int_literal, lit, null_of, num_literal, numeric_token, unify_numbers)

CMP_OPS = {exp.EQ: "Eq", exp.NEQ: "Ne", exp.LT: "Lt", exp.LTE: "Le", exp.GT: "Gt", exp.GTE: "Ge"}
ARITH_OPS = {exp.Add: "Add", exp.Sub: "Sub", exp.Mul: "Mul"}
PRED_CLASSES = (*CMP_OPS, exp.And, exp.Or, exp.Not, exp.Is, exp.In, exp.Exists, exp.Between)
INTERVAL_UNITS = {"YEAR": ("months", 12), "MONTH": ("months", 1), "DAY": ("days", 1)}
# Operators without a rule in the fragment (division and LIKE have features; see FEATURE_VALUES).
UNSUPPORTED_OPERATORS = (exp.Mod, exp.IntDiv, exp.Pow, exp.DPipe, exp.BitwiseAnd, exp.BitwiseOr, exp.BitwiseXor,
                         exp.BitwiseNot, exp.BitwiseLeftShift, exp.BitwiseRightShift, exp.ILike, exp.SimilarTo,
                         exp.Any, exp.All)


@dataclass
class AggCollector:
    """Aggregates of one grouped query level, in first-binding order (equal calls share a slot)."""
    level: Level
    aggs: list[Node] = field(default_factory=list)
    types: list[ColTy] = field(default_factory=list)

    def slot(self, agg: Node, ty: ColTy) -> Node:
        """The ``AggSlot`` placeholder of ``agg`` (grouping later maps it to the aggregate's column)."""
        if agg not in self.aggs:
            self.aggs.append(agg)
            self.types.append(ty)
        i = self.aggs.index(agg)
        return Node("AggSlot", self.types[i], slot=i)


@dataclass(frozen=True)
class ExprScope:
    level: Level
    clause: str  # for diagnostics: WHERE, JOIN ON, SELECT, HAVING, GROUP BY, ORDER BY, CHECK
    aggs: AggCollector | None = None  # None: aggregates are not allowed here
    in_aggregate: bool = False


# A subquery of EXISTS, evaluated in the environment of a level: its query below the select list.
ExistsLowering = Callable[[exp.Expression, Level, str], Node]
# A scalar or IN / ANY / ALL subquery, evaluated in the environment of a level: (query, output names).
SubqueryLowering = Callable[[exp.Expression, Level, str], tuple[Node, list[str]]]


class Binder:
    """Binds the expressions and predicates of one statement (or one CHECK constraint).

    Subqueries are lowered by the callbacks ``lower_exists`` / ``lower_subquery`` (the ``Lowerer``'s); ``params``
    are the statement's declared placeholders (None: the statement has none)."""

    def __init__(self, dialect: str, lower_exists: ExistsLowering, lower_subquery: SubqueryLowering,
                 params: ParamDecls | None = None):
        self.dialect = dialect
        self.params = params
        self.lower_exists = lower_exists
        self.lower_subquery = lower_subquery

    def sql(self, node: exp.Expression) -> str:
        """Diagnostic SQL text of a node (the ``sql`` of a refusal)."""
        return node.sql(self.dialect)[:200]

    # -- values ------------------------------------------------------------------------------

    def expr(self, node: exp.Expression, sc: ExprScope, path: str) -> Node:
        """A value with a type (an untyped literal without context is text)."""
        return default_type(self.value(node, sc, path), path)

    def value(self, node: exp.Expression, sc: ExprScope, path: str) -> Node | Unknown:
        """A value; untyped literals stay ``Unknown`` so that the enclosing operator can type them."""
        if isinstance(node, exp.Paren):
            check_args(node, {"this"}, path)
            return self.value(node.this, sc, path)
        if isinstance(node, exp.Column):
            return self._column(node, sc, path)
        if isinstance(node, (exp.Literal, exp.Neg)) and (token := numeric_token(node)) is not None:
            coeff, scale, is_int = token
            return int_literal(coeff) if is_int else num_literal(coeff, scale, path, self.sql(node))
        if isinstance(node, exp.Literal):
            check_args(node, {"this", "is_string"}, path)
            return Unknown(node.this, self.sql(node))
        if isinstance(node, exp.Null):
            return Unknown(None, "NULL")
        if isinstance(node, exp.Boolean):
            return lit(Node("Bool", value=bool(node.this)), ColTy(BOOL, False))
        if isinstance(node, exp.Neg):
            return self._negation(node, sc, path)
        if type(node) in ARITH_OPS:
            return self._arith(node, sc, path)
        if type(node) is exp.Cast:
            return self._cast(node, sc, path)
        if (feature := FEATURE_VALUES.get(type(node))) is not None:
            return feature(self, node, sc, path)
        if isinstance(node, PRED_CLASSES):
            raise Refusal("boolean_value", "a condition used as a value (outside WHERE/ON/HAVING)", path, self.sql(node))
        if isinstance(node, exp.AggFunc):
            return self._aggregate(node, sc, path)
        if isinstance(node, exp.Interval):
            raise Refusal("unsupported_interval", "an interval is only supported as an operand of date/timestamp + or -", path, self.sql(node))
        if isinstance(node, UNSUPPORTED_OPERATORS):
            raise Refusal("unsupported_operator", f"{type(node).__name__} is not in the fragment", path, self.sql(node))
        if isinstance(node, exp.Func):
            raise Refusal("unsupported_function", f"function {type(node).__name__}", path, self.sql(node))
        raise Refusal("unsupported_syntax", f"{type(node).__name__} is outside the fragment", path, self.sql(node))

    def _column(self, node: exp.Column, sc: ExprScope, path: str) -> Node:
        check_args(node, {"this", "table"}, path)
        if not isinstance(node.this, exp.Identifier):
            raise Refusal("unsupported_syntax", "a star is only supported as a select-list item", path, self.sql(node))
        qualifier = ident(node.args["table"]) if node.args.get("table") is not None else None
        index, ty = sc.level.resolve(qualifier, ident(node.this), path, self.sql(node))
        return col(index, ty)

    def _negation(self, node: exp.Neg, sc: ExprScope, path: str) -> Node:
        check_args(node, {"this"}, path)
        e = self.value(node.this, sc, path)
        if isinstance(e, Unknown) or e.ann.ty.family != "number":
            raise Refusal("type_mismatch", "unary minus needs an int4, int8 or numeric operand", path, self.sql(node))
        return Node("Neg", e.ann, kind=NUM_KIND[e.ann.ty.kind], arg=e)

    def _arith(self, node: exp.Expression, sc: ExprScope, path: str) -> Node:
        check_args(node, {"this", "expression"}, path)
        op = ARITH_OPS[type(node)]
        if isinstance(node.expression, exp.Interval) or isinstance(node.this, exp.Interval):
            return self._interval_arith(node, op, sc, path)
        a, b = self.value(node.this, sc, path), self.value(node.expression, sc, path)
        if isinstance(a, Unknown) and isinstance(b, Unknown):
            raise Refusal("type_mismatch", f"operator {op} has two untyped operands", path, self.sql(node))
        if isinstance(a, Unknown):
            a = coerce_unknown(a, b.ann, path)
        if isinstance(b, Unknown):
            b = coerce_unknown(b, a.ann, path)
        ta, tb = a.ann.ty, b.ann.ty
        if ta.family != "number" or tb.family != "number":
            reason = "unsupported_operator" if {ta.family, tb.family} <= {"datetime", "number"} else "type_mismatch"
            raise Refusal(reason, f"no operator {ta.pg_name()} {op} {tb.pg_name()} in the fragment", path, self.sql(node))
        a, b = unify_numbers(a, b)
        kind = NUM_KIND[a.ann.ty.kind]
        if kind == "Numeric":
            scale = a.ann.dscale + b.ann.dscale if op == "Mul" else max(a.ann.dscale, b.ann.dscale)
            if scale > NUMERIC_DSCALE_MAX:
                raise Refusal("numeric_scale_limit", f"result scale {scale} > {NUMERIC_DSCALE_MAX}", path, self.sql(node))
            ty = ColTy(numeric(), a.ann.nullable or b.ann.nullable, scale, a.ann.dscale_exact and b.ann.dscale_exact)
        else:
            ty = ColTy(a.ann.ty, a.ann.nullable or b.ann.nullable)
        return Node("Arith", ty, op=op, kind=kind, a=a, b=b)

    def _interval_arith(self, node: exp.Expression, op: str, sc: ExprScope, path: str) -> Node:
        """``date/timestamp +/- INTERVAL`` and ``INTERVAL + date/timestamp`` as ``AddInterval`` on a timestamp."""
        if isinstance(node.this, exp.Interval):
            if op != "Add" or isinstance(node.expression, exp.Interval):
                raise Refusal("unsupported_interval", "only date/timestamp +/- interval and interval + date/timestamp", path, self.sql(node))
            base_node, interval = node.expression, node.this
        else:
            base_node, interval = node.this, node.expression
        if op not in ("Add", "Sub"):
            raise Refusal("unsupported_interval", f"{op} with an interval", path, self.sql(node))
        field_name, amount = self._interval(interval, path)
        if op == "Sub":
            amount = -amount
            if not INT4_MIN <= amount <= INT4_MAX:  # the AST's interval fields are i32
                raise Refusal("interval_negation_range", f"negated interval field {amount} is outside int32", path, self.sql(node))
        base = self.value(base_node, sc, path)
        if isinstance(base, Unknown) or base.ann.ty.kind not in ("date", "timestamp"):
            raise Refusal("type_mismatch", "interval arithmetic needs a date or timestamp operand", path, self.sql(node))
        if base.ann.ty.kind == "date":
            base = cast(base, "DateToTimestamp")  # date + interval is timestamp + interval
        parts = {"months": 0, "days": 0, "micros": 0, field_name: amount}
        return Node("AddInterval", ColTy(TIMESTAMP, base.ann.nullable), arg=base, **parts)

    def _interval(self, node: exp.Interval, path: str) -> tuple[str, int]:
        """(AddInterval field, amount) of ``INTERVAL '<integer>' YEAR | MONTH | DAY``."""
        check_args(node, {"this", "unit"}, path)
        unit = node.args.get("unit")
        quantity = node.this
        unit_name = unit.name.upper() if isinstance(unit, exp.Var) else None
        if (unit_name not in INTERVAL_UNITS or not isinstance(quantity, exp.Literal) or not quantity.is_string
                or not SIGNED_INT_TEXT.match(quantity.this)):
            raise Refusal("unsupported_interval", "only INTERVAL '<integer>' YEAR | MONTH | DAY", path, self.sql(node))
        field_name, factor = INTERVAL_UNITS[unit_name]
        amount = int(quantity.this) * factor
        if not INT4_MIN <= amount <= INT4_MAX:
            raise Refusal("invalid_literal", "interval field value out of range", path, self.sql(node))
        return field_name, amount

    def _cast(self, node: exp.Cast, sc: ExprScope, path: str) -> Node:
        check_args(node, {"this", "to"}, path)
        target = sql_type(node.args["to"], path)
        v = self.value(node.this, sc, path)
        if isinstance(v, Unknown):
            dscale = target.scale if target.kind == "numeric" else None
            return coerce_unknown(v, ColTy(target, False, dscale), path, explicit=True)
        source = v.ann.ty
        if source == target:
            return v
        conversion = None
        if source.kind == "int4" and target == INT8:
            conversion = "Int4ToInt8"
        elif source.is_int and target == numeric():
            conversion = "IntToNumeric"
        elif source.kind == "date" and target == TIMESTAMP:
            conversion = "DateToTimestamp"
        if conversion is None:
            raise Refusal("unsupported_cast", f"cast {source.pg_name()} -> {target.pg_name()} is not in the fragment", path, self.sql(node))
        return cast(v, conversion)

    # -- aggregates --------------------------------------------------------------------------

    def _aggregate(self, node: exp.AggFunc, sc: ExprScope, path: str) -> Node:
        """An aggregate call as the ``AggSlot`` of the level that owns the scope's collector."""
        name = type(node).__name__.upper()
        if sc.aggs is None or sc.in_aggregate:
            where = "inside another aggregate" if sc.in_aggregate else f"in {sc.clause}"
            raise Refusal("aggregate_misplaced", f"aggregate {name} {where}", path, self.sql(node))
        bind_call = AGGREGATES.get(type(node))
        if bind_call is None:
            raise Refusal("unsupported_aggregate", f"aggregate {name}", path, self.sql(node))
        check_args(node, {"this", "big_int"} if isinstance(node, exp.Count) else {"this"}, path)
        arg, distinct = self._aggregate_argument(node, name, path)
        # Arguments are bound at the level that owns the collector, where aggregates may not nest.
        inner = ExprScope(sc.aggs.level, sc.clause, sc.aggs, in_aggregate=True)
        if isinstance(node, exp.Count) and isinstance(arg, exp.Star):
            if distinct:
                raise Refusal("unsupported_syntax", "COUNT(DISTINCT *)", path, self.sql(node))
            agg, ty = Node("CountStar"), ColTy(INT8, False)
        else:
            if arg is None:
                raise Refusal("unsupported_aggregate", f"{name} without argument", path, self.sql(node))
            bound = self.value(arg, inner, f"{path}/{name.lower()}")
            agg, ty = bind_call(self, node, bound, path)
            if distinct:
                agg, ty = distinct_agg.bind_distinct_agg(name, agg, ty, path, self.sql(node))
            _check_aggregate_level(agg, sc.aggs.level, path, self.sql(node))
        return sc.aggs.slot(agg, ty)

    def _aggregate_argument(self, node: exp.AggFunc, name: str, path: str) -> tuple[exp.Expression | None, bool]:
        """(the argument expression, whether it is ``DISTINCT``) of an aggregate call."""
        arg = node.this
        if not isinstance(arg, exp.Distinct):
            return arg, False
        check_args(arg, {"expressions"}, path)
        if len(arg.expressions) != 1:
            raise Refusal("unsupported_aggregate", f"{name}(DISTINCT ...) needs exactly one argument", path, self.sql(node))
        return arg.expressions[0], True

    # -- predicates --------------------------------------------------------------------------

    def pred(self, node: exp.Expression, sc: ExprScope, path: str) -> Node:
        if isinstance(node, exp.Paren):
            check_args(node, {"this"}, path)
            return self.pred(node.this, sc, path)
        if type(node) in CMP_OPS and (isinstance(node.expression, (exp.Any, exp.All))
                                      or isinstance(node.this, (exp.Any, exp.All))):
            return subquery.bind_quantified(self, CMP_OPS[type(node)], node, sc, path)
        if type(node) in CMP_OPS:
            check_args(node, {"this", "expression"}, path)
            return self.cmp(CMP_OPS[type(node)], self.value(node.this, sc, path),
                            self.value(node.expression, sc, path), path, self.sql(node))
        if isinstance(node, (exp.And, exp.Or)):
            check_args(node, {"this", "expression"}, path)
            return Node("And" if isinstance(node, exp.And) else "Or",
                        a=self.pred(node.this, sc, path), b=self.pred(node.expression, sc, path))
        if isinstance(node, exp.Not):
            check_args(node, {"this"}, path)
            return Node("Not", p=self.pred(node.this, sc, path))
        if isinstance(node, exp.Is):
            check_args(node, {"this", "expression"}, path)
            if not isinstance(node.expression, exp.Null):
                raise Refusal("unsupported_operator", "only IS [NOT] NULL", path, self.sql(node))
            return Node("IsNull", e=self.expr(node.this, sc, path))
        if isinstance(node, exp.Between):
            # SQL defines x BETWEEN a AND b as x >= a AND x <= b (PostgreSQL's parser does the same).
            check_args(node, {"this", "low", "high"}, path)
            sql = self.sql(node)
            low = self.cmp("Ge", self.value(node.this, sc, path), self.value(node.args["low"], sc, path), path, sql)
            high = self.cmp("Le", self.value(node.this, sc, path), self.value(node.args["high"], sc, path), path, sql)
            return Node("And", a=low, b=high)
        if isinstance(node, exp.In):
            return self._in_list(node, sc, path)
        if isinstance(node, exp.Exists):
            check_args(node, {"this"}, path)
            return Node("Exists", q=self.lower_exists(node.this, sc.level, f"{path}/exists"))
        return self._boolean_value(node, sc, path)

    def _boolean_value(self, node: exp.Expression, sc: ExprScope, path: str) -> Node:
        """A boolean-typed value used as a condition (``OfBool``); an untyped NULL is a boolean NULL."""
        v = self.value(node, sc, path)
        if isinstance(v, Unknown):
            if v.text is not None:
                raise Refusal("unsupported_literal", "a string literal used as a condition", path, v.sql)
            v = null_of(ColTy(BOOL, True), path, v.sql)
        if v.ann.ty.kind != "bool":
            raise Refusal("type_mismatch", f"argument of {sc.clause} must be boolean, not {v.ann.ty.pg_name()}", path, self.sql(node))
        return Node("OfBool", e=v)

    def _in_list(self, node: exp.In, sc: ExprScope, path: str) -> Node:
        """``x IN (a, b, ...)`` as PostgreSQL's ``transformAExprIn`` resolves it.

        With at most one item free of current-level columns PostgreSQL builds ``x = a OR x = b OR ...`` (left-nested)
        with each operator resolved per element.  With two or more such items it compares ``x`` with an array of
        those items coerced to ``select_common_type(x, items)`` (the remaining items stay per element).  The common
        type is computed and applied here: untyped literals take it, and a text/varchar item that PostgreSQL would
        coerce to bpchar (blank-insensitive) is refused because the core has no rtrim cast.  Every other coercion
        inside a family is exact on the core's values (int4 -> int8 -> numeric, date -> timestamp, and bpchar -> text
        is the right-trim the core's char(n) values already have), so comparing element by element has PostgreSQL's
        truth value."""
        check_args(node, {"this", "expressions", "query"}, path)
        sql = self.sql(node)
        if node.args.get("query") is not None:
            return subquery.bind_in_subquery(self, node, sc, path)
        if isinstance(node.this, exp.Tuple):
            raise Refusal("unsupported_syntax", "row-value IN", path, sql)
        lhs = self.value(node.this, sc, path)
        items = [self.value(item, sc, path) for item in node.expressions]
        constant_items = [i for i, v in enumerate(items) if not self._has_level_column(v, sc)]
        common = common_type(lhs, [items[i] for i in constant_items]) if len(constant_items) > 1 else None
        lhs_common = lhs
        if common is not None and isinstance(lhs, Unknown) and lhs.text is not None:
            lhs_common = coerce_unknown(lhs, ColTy(common, False), path)
        out = None
        for i, item in enumerate(items):
            if common is None or i not in constant_items:
                eq = self.cmp("Eq", lhs, item, path, sql)
            else:
                if isinstance(item, Unknown) and item.text is not None:
                    item = coerce_unknown(item, ColTy(common, False), path)
                elif isinstance(item, Node) and common.kind == "bpchar" and item.ann.ty.kind in ("text", "varchar"):
                    raise Refusal("in_list_bpchar_coercion",
                                  f"IN list common type is bpchar; the {item.ann.ty.pg_name()} item would be compared ignoring trailing blanks",
                                  path, sql)
                eq = self.cmp("Eq", lhs_common, item, path, sql, in_common=True)
            out = eq if out is None else Node("Or", a=out, b=eq)
        return out

    @staticmethod
    def _has_level_column(v: Node | Unknown, sc: ExprScope) -> bool:
        """PostgreSQL's ``contain_vars_of_level(item, 0)``: a column of this query level, also inside an aggregate's
        arguments (``COUNT(*)`` has none)."""
        if isinstance(v, Unknown):
            return False
        level = sc.level
        stack = [v]
        while stack:
            n = stack.pop()
            if n.tag == "Col" and level.ctx_len <= n.index < level.env_len:
                return True
            if n.tag == "AggSlot" and sc.aggs is not None:
                stack.append(sc.aggs.aggs[n.slot])
            stack.extend(n.children())
        return False

    def cmp(self, op: str, a: Node | Unknown, b: Node | Unknown, path: str, sql: str, in_common: bool = False) -> Node:
        """A comparison with PostgreSQL's operand resolution (implicit casts where PostgreSQL has them).

        ``in_common``: the operands are an IN-list left side and an item already coerced to the list's common type
        (``_in_list``), so PostgreSQL's operator is text = text on the right-trimmed item."""
        if isinstance(a, Unknown) and isinstance(b, Unknown):
            a, b = default_type(a, path), default_type(b, path)
        elif isinstance(a, Unknown):
            a = coerce_unknown(a, b.ann, path)
        elif isinstance(b, Unknown):
            b = coerce_unknown(b, a.ann, path)
        ta, tb = a.ann.ty, b.ann.ty
        if ta.family != tb.family:
            raise Refusal("type_mismatch", f"no operator {ta.pg_name()} {op} {tb.pg_name()}", path, sql)
        if {ta.kind, tb.kind} == {"bpchar", "varchar"} and not in_common:
            # PostgreSQL resolves bpchar op varchar to the bpchar operator (varchar -> bpchar is implicit), which
            # ignores trailing blanks of the varchar value too; the core has no rtrim cast.
            raise Refusal("bpchar_varchar_comparison", f"{ta.pg_name()} {op} {tb.pg_name()} resolves to a bpchar operator", path, sql)
        if ta.family == "number" and (ta.kind == "numeric") != (tb.kind == "numeric"):
            a, b = unify_numbers(a, b)  # int vs numeric: the int side is cast; int4 vs int8 is cross-type
        return Node("Cmp", op=op, a=a, b=b)


def _bind_count(b: Binder, node: exp.Count, arg: Node | Unknown, path: str) -> tuple[Node, ColTy]:
    return Node("Count", e=default_type(arg, path)), ColTy(INT8, False)


def _bind_sum(b: Binder, node: exp.Sum, arg: Node | Unknown, path: str) -> tuple[Node, ColTy]:
    if isinstance(arg, Unknown) or arg.ann.ty.family != "number":
        shown = "unknown" if isinstance(arg, Unknown) else arg.ann.ty.pg_name()
        raise Refusal("type_mismatch", f"no function sum({shown})", path, b.sql(node))
    kind = arg.ann.ty.kind
    # SUM is NULL on empty input or all-NULL input: nullable, as in the Verus typing.
    if kind == "int4":
        ty = ColTy(INT8, True)
    elif kind == "int8":
        ty = ColTy(numeric(), True, 0)
    else:
        ty = ColTy(numeric(), True, arg.ann.dscale, arg.ann.dscale_exact)
    return Node("Sum", kind=NUM_KIND[kind], arg=arg), ty


def _check_aggregate_level(agg: Node, level: Level, path: str, sql: str) -> None:
    """PostgreSQL assigns an aggregate to the innermost level its arguments reference; arguments that reference only
    outer levels would make it an outer aggregate."""
    refs = [i for e in agg.children() for i in column_indices(e)]
    local = [i for i in refs if level.ctx_len <= i < level.env_len]
    if refs and not local and any(i < level.ctx_len for i in refs):
        raise Refusal("outer_level_aggregate", "aggregate arguments reference only outer queries", path, sql)


def column_indices(node: Node) -> list[int]:
    """Environment positions of every column reference in ``node``."""
    out: list[int] = []
    stack = [node]
    while stack:
        n = stack.pop()
        if n.tag == "Col":
            out.append(n.index)
        stack.extend(n.children())
    return out


# Value forms with a feature module: exact sqlglot class -> f(binder, node, scope, path) -> Node.
FEATURE_VALUES: dict[type, Callable] = {
    exp.Div: div.bind_div,
    exp.Like: like.bind_like,
    exp.Escape: like.bind_like,
    exp.Substring: substring.bind_substring,
    exp.Extract: extract.bind_extract,
    exp.Case: case.bind_case,
    exp.Coalesce: case.bind_coalesce,
    exp.Nullif: case.bind_nullif,
    exp.Subquery: subquery.bind_scalar_subquery,
    exp.Parameter: bind_parameter,
}
# Supported aggregates: exact sqlglot class -> f(binder, node, bound argument, path) -> (agg node, result type).
AGGREGATES: dict[type, Callable] = {
    exp.Count: _bind_count,
    exp.Sum: _bind_sum,
    exp.Avg: avg.bind_avg,
    exp.Min: minmax.bind_min,
    exp.Max: minmax.bind_max,
}
