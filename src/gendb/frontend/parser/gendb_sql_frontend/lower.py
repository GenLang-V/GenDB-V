"""SELECT blocks to relational constructors.

    FROM a, b JOIN c ON p, d LEFT JOIN e ON r
        -> Product(Product(Table a, Filter(p, Product(b, c))), LeftJoin(d, e, r))
    WHERE w                      -> Filter(w, from)
    GROUP BY keys / aggregates   -> GroupBy(keys, aggs, where) or Aggregate(aggs, where)
    HAVING h                     -> Filter(h, grouped)
    SELECT list                  -> Project(exprs, ...)
    DISTINCT                     -> Distinct(project)
    ORDER BY / LIMIT / OFFSET    -> OrderedQuery (top level only; keys are output columns)

Grouping is resolved in two steps.  Select-list, HAVING and ORDER BY expressions are first bound against the FROM
row, with aggregates as ``AggSlot`` placeholders.  Then every subtree equal to a GROUP BY key becomes a reference to
the key's column, every ``AggSlot`` a reference to its aggregate column, and any remaining reference to the FROM row
is ``ungrouped_column`` (PostgreSQL's rule, without the primary-key functional-dependency allowance).  Positions
deeper than the FROM row belong to subqueries and move with the row-width change.

SELECT DISTINCT is ``Distinct`` over the select list's output rows: rows are compared with SQL value equality
(``IS NOT DISTINCT FROM``: NULLs together, numerics by value) and the first occurrence represents a class (reference
choice R1).  DISTINCT ON is refused.
"""

from __future__ import annotations

from contextlib import contextmanager
from dataclasses import dataclass
from typing import Iterator

from sqlglot import exp

from .ast import Node
from .bind import AggCollector, Binder, ExprScope
from .features import cte
from .features.params import ParamDecls
from .parse import check_args, ident
from .refusal import Refusal
from .schema import Schema
from .scope import Frame, Level, RangeItem
from .values import col, default_type


@dataclass
class SelectItem:
    name: str
    source: exp.Expression | None  # None when expanded from a star (``bound`` is set)
    bound: Node | None = None


class Lowerer:
    """Lowers one statement.  ``ctes`` are the WITH items visible where lowering currently is (innermost last)."""

    def __init__(self, schema: Schema, dialect: str, params: ParamDecls | None = None):
        self.schema = schema
        self.dialect = dialect
        self.binder = Binder(dialect, self.exists_subquery, self.subquery, params)
        self.ctes: tuple[cte.CteDef, ...] = ()

    def _sql(self, node: exp.Expression) -> str:
        return node.sql(self.dialect)[:200]

    # -- entry points --------------------------------------------------------------------------

    def top(self, sel: exp.Select) -> tuple[Node, list[str]]:
        """The statement: an ``OrderedQuery`` and its output column names."""
        return self.select(sel, None, 0, "query", top=True)

    def exists_subquery(self, node: exp.Expression, level: Level, path: str) -> Node:
        """The subquery of ``EXISTS``, evaluated in the environment of ``level``.

        EXISTS observes only whether a row exists. The select list is bound and checked like any other (names, types,
        grouping) and then not applied: the result is the query below the select-list ``Project``, which has exactly
        the same number of rows (scalar aggregation still yields one row on empty input; GROUP BY and HAVING are
        kept). Without aggregates or HAVING this matches PostgreSQL, whose ``simplify_EXISTS_query`` drops the select
        list, and also any GROUP BY (grouping cannot turn a nonempty input into zero groups or back). The frontend
        keeps that GROUP BY and, as for every grouped level, requires a select list that cannot raise
        (``exists_select_list``): row existence is the same, and the kept GROUP BY keys can only make the semantics
        raise where PostgreSQL does not evaluate them, or refuse (the declared direction). With aggregates or HAVING
        PostgreSQL keeps the select list and evaluates it for the first row it produces (plan-dependent), so the
        select list must be unable to raise an error, else the refusal ``exists_select_list``."""
        return self.select(self.subquery_select(node, path), level, level.env_len, path, top=False, exists=True)[0]

    def subquery(self, node: exp.Expression, level: Level, path: str) -> tuple[Node, list[str]]:
        """A scalar or IN / ANY / ALL subquery, evaluated in the environment of ``level`` (correlation)."""
        return self.select(self.subquery_select(node, path), level, level.env_len, path, top=False)

    def subquery_select(self, node: exp.Expression, path: str) -> exp.Select:
        """The SELECT of a (possibly parenthesized) subquery body."""
        while isinstance(node, exp.Subquery) and not node.args.get("alias"):
            check_args(node, {"this"}, path)
            node = node.this
        if isinstance(node, (exp.Union, exp.Intersect, exp.Except)):
            raise Refusal("set_operation", "set operations are outside the fragment", path, self._sql(node))
        if not isinstance(node, exp.Select):
            raise Refusal("unsupported_syntax", f"subquery body {type(node).__name__}", path, self._sql(node))
        return node

    def lower_cte(self, d: cte.CteDef, ctx_len: int, path: str) -> tuple[Node, list[str]]:
        """The query of WITH item ``d`` at a reference whose context has length ``ctx_len``: bound in the scope of its
        definition (its outer levels and the WITH items before it), with its own row after ``ctx_len``."""
        with self._visible_ctes(d.scope):
            q, names = self.select(d.select, d.parent, ctx_len, f"{path}/with:{d.name}", top=False)
        return q, list(d.columns) + names[len(d.columns):]

    @contextmanager
    def _visible_ctes(self, ctes: tuple[cte.CteDef, ...]) -> Iterator[None]:
        saved = self.ctes
        self.ctes = ctes
        try:
            yield
        finally:
            self.ctes = saved

    # -- SELECT --------------------------------------------------------------------------------

    def select(self, sel: exp.Select, parent: Level | None, ctx_len: int, path: str, top: bool,
               exists: bool = False) -> tuple[Node, list[str]]:
        """One SELECT block in the environment ``ctx`` of length ``ctx_len`` (of the ``parent`` level): the query
        and its output names.  ``top``: the statement itself (ORDER BY / LIMIT allowed); ``exists``: the body of
        EXISTS (the query below the select list)."""
        with_ = sel.args.get("with")
        # WITH queries are inlined at each reference (``features/cte.py``).
        ctes = cte.bind_with(self, with_, parent, ctx_len, path) if with_ is not None else self.ctes
        with self._visible_ctes(ctes):
            return self._select_block(sel, parent, ctx_len, path, top, exists)

    def _select_block(self, sel: exp.Select, parent: Level | None, ctx_len: int, path: str, top: bool,
                      exists: bool) -> tuple[Node, list[str]]:
        distinct = self._check_clauses(sel, path, top)
        body, frame = self._from(sel, parent, ctx_len, path)
        level = Level(parent, ctx_len, frame)
        where = sel.args.get("where")
        if where is not None:
            check_args(where, {"this"}, path)
            pred = self.binder.pred(where.this, ExprScope(level, "WHERE"), f"{path}/where")
            body = Node("Filter", body.ann, pred=pred, input=body)

        items = self._select_items(sel, level, path)
        names = [i.name for i in items]
        group = sel.args.get("group")
        having = sel.args.get("having")
        order = sel.args.get("order")
        order_items = list(order.expressions) if order is not None else []
        if order is not None:
            check_args(order, {"expressions"}, path)
        grouped = (group is not None or having is not None
                   or any(_has_local_aggregate(e) for e in [i.source for i in items if i.source] + order_items))

        collector = AggCollector(level) if grouped else None
        select_scope = ExprScope(level, "SELECT", collector)
        keys = self._group_keys(group, items, level, path) if group is not None else []
        exprs = [i.bound if i.bound is not None else self.binder.expr(i.source, select_scope, f"{path}/select/{i.name}")
                 for i in items]
        having_pred = None
        if having is not None:
            check_args(having, {"this"}, path)
            having_pred = self.binder.pred(having.this, ExprScope(level, "HAVING", collector), f"{path}/having")
        positions = [self._order_position(o, items, select_scope, path) for o in order_items]

        if grouped:
            regroup = Regroup(level, keys, collector, path)
            body = regroup.grouped_query(body, group is not None)
            if having_pred is not None:
                body = Node("Filter", body.ann, pred=regroup.apply(having_pred), input=body)
            exprs = [regroup.apply(e) for e in exprs]
            positions = [regroup.apply(p) if isinstance(p, Node) else p for p in positions]
        if exists:
            if (grouped or distinct) and not all(_cannot_fail(e) for e in exprs):
                raise Refusal("exists_select_list", "an aggregated EXISTS subquery whose select list can raise an "
                              "error (PostgreSQL evaluates it for a plan-dependent first row)", path, self._sql(sel))
            return body, names
        output = _project(body, exprs, ctx_len)
        if distinct:
            output = Node("Distinct", output.ann, input=output)
        if not top:
            return output, names
        return self._ordered_query(sel, output, exprs, order_items, positions, path), names

    def _check_clauses(self, sel: exp.Select, path: str, top: bool) -> bool:
        """Refuse clauses outside the fragment; returns whether the block is SELECT DISTINCT."""
        distinct = sel.args.get("distinct")
        if distinct is not None:
            if distinct.args.get("on") is not None:
                raise Refusal("distinct_on", "SELECT DISTINCT ON", path, self._sql(sel))
            check_args(distinct, set(), path)
        if not top and any(sel.args.get(k) for k in ("order", "limit", "offset")):
            raise Refusal("subquery_order_or_limit", "ORDER BY / LIMIT / OFFSET inside a subquery", path, self._sql(sel))
        check_args(sel, {"expressions", "from", "joins", "where", "group", "having", "order", "limit", "offset",
                         "with", "distinct"}, path)
        if sel.args.get("from") is None:
            raise Refusal("unsupported_syntax", "SELECT without FROM", path, self._sql(sel))
        return distinct is not None

    def _ordered_query(self, sel: exp.Select, output: Node, exprs: list[Node], order_items: list[exp.Expression],
                       positions: list[int | Node], path: str) -> Node:
        """The statement's ``OrderedQuery``: ORDER BY keys as output positions, LIMIT and OFFSET."""
        keys = []
        for o, position in zip(order_items, positions):
            if isinstance(position, Node):
                matches = [i for i, e in enumerate(exprs) if e == position]
                if not matches:
                    raise Refusal("hidden_order_key", "ORDER BY key is not an output column", f"{path}/order", self._sql(o))
                position = matches[0]
            desc = bool(o.args.get("desc"))
            nulls_first = o.args.get("nulls_first")
            # PostgreSQL defaults: ASC NULLS LAST, DESC NULLS FIRST.
            nulls_first = desc if nulls_first is None else bool(nulls_first)
            keys.append(Node("OrderKey", col=position, desc=desc, nulls_first=nulls_first))
        limit = self._row_count(sel.args.get("limit"), "LIMIT", path)
        offset = self._row_count(sel.args.get("offset"), "OFFSET", path)
        return Node("OrderedQuery", body=output, keys=tuple(keys), limit=limit, offset=0 if offset is None else offset)

    def _row_count(self, node: exp.Expression | None, what: str, path: str) -> int | None:
        """The literal of LIMIT / OFFSET (``what``), None when absent."""
        if node is None:
            return None
        check_args(node, {"expression"}, path)
        v = node.args.get("expression")
        if isinstance(v, exp.Parameter):
            raise Refusal("parameter_position", f"a placeholder in {what}", path, self._sql(node))
        if not (isinstance(v, exp.Literal) and not v.is_string and v.this.isdigit()):
            raise Refusal("non_literal_limit", f"{what} must be a non-negative integer literal", path, self._sql(node))
        return int(v.this)

    # -- FROM ----------------------------------------------------------------------------------

    def _from(self, sel: exp.Select, parent: Level | None, ctx_len: int, path: str) -> tuple[Node, Frame]:
        """The FROM clause: comma-separated items as a left-deep ``Product`` of join trees."""
        from_ = sel.args["from"]
        check_args(from_, {"this"}, path)
        groups: list[tuple[Node, Frame]] = [self._from_item(from_.this, parent, ctx_len, path)]
        for j in sel.args.get("joins") or []:
            side, kind = self._check_join(j, path)
            right = self._from_item(j.this, parent, ctx_len, path)
            if j.args.get("on") is None and not side and not kind:
                groups.append(right)  # comma: a new FROM item (JOIN binds tighter)
            else:
                groups[-1] = self._join(groups[-1], right, j, side, kind, parent, ctx_len, path)
        query, frame = groups[0]
        for q, f in groups[1:]:
            query, frame = Node("Product", query.ann + q.ann, left=query, right=q), frame.concat(f)
        names = [i.name for i in frame.items if i.name is not None]
        for n in names:
            if names.count(n) > 1:
                raise Refusal("duplicate_alias", f"table name {n!r} specified more than once", f"{path}/from")
        return query, frame

    def _check_join(self, j: exp.Join, path: str) -> tuple[str, str]:
        """(side, kind) of a join in the fragment: comma, [INNER] JOIN ... ON, CROSS JOIN, LEFT [OUTER] JOIN ... ON."""
        side = (j.args.get("side") or "").upper()
        kind = (j.args.get("kind") or "").upper()
        if isinstance(j.this, exp.Lateral) or kind == "LATERAL":
            raise Refusal("lateral", "LATERAL is outside the fragment", f"{path}/from", self._sql(j))
        if j.args.get("using") or j.args.get("method"):
            raise Refusal("using_or_natural_join", "JOIN USING / NATURAL", f"{path}/from", self._sql(j))
        if side in ("RIGHT", "FULL") or kind == "OUTER" and side != "LEFT":
            raise Refusal("full_or_right_join", f"{side or kind} JOIN", f"{path}/from", self._sql(j))
        check_args(j, {"this", "on", "side", "kind"}, f"{path}/from")
        if kind not in ("", "INNER", "CROSS", "OUTER"):
            raise Refusal("unsupported_syntax", f"{kind} JOIN", f"{path}/from", self._sql(j))
        return side, kind

    def _join(self, left: tuple[Node, Frame], right: tuple[Node, Frame], j: exp.Join, side: str, kind: str,
              parent: Level | None, ctx_len: int, path: str) -> tuple[Node, Frame]:
        """``left JOIN right`` as a query over the concatenated row."""
        (left_q, left_f), (right_q, right_f) = left, right
        on = j.args.get("on")
        if kind == "CROSS":
            if on is not None:
                raise Refusal("unsupported_syntax", "CROSS JOIN with ON", f"{path}/from", self._sql(j))
            return Node("Product", left_q.ann + right_q.ann, left=left_q, right=right_q), left_f.concat(right_f)
        if on is None:
            raise Refusal("join_without_condition", "JOIN without ON", f"{path}/from", self._sql(j))
        joined = left_f.concat(right_f)
        p = self.binder.pred(on, ExprScope(Level(parent, ctx_len, joined), "JOIN ON"), f"{path}/on")
        if side == "LEFT":
            ann = left_q.ann + tuple(t.with_nullable(True) for t in right_q.ann)
            return (Node("LeftJoin", ann, left=left_q, right=right_q, on=p),
                    left_f.concat(right_f, right_nullable=True))
        product = Node("Product", left_q.ann + right_q.ann, left=left_q, right=right_q)
        return Node("Filter", product.ann, pred=p, input=product), joined

    def _from_item(self, node: exp.Expression, parent: Level | None, ctx_len: int, path: str) -> tuple[Node, Frame]:
        """A table, WITH item or derived table, with its alias and column aliases."""
        alias = node.args.get("alias")
        if isinstance(node, exp.Table) and (d := self._visible_cte(node)) is not None:
            check_args(node, {"this", "alias"}, f"{path}/from")
            query, out_names = self.lower_cte(d, ctx_len, path)
            name = d.name
            columns = list(zip(out_names, query.ann))
        elif isinstance(node, exp.Table):
            check_args(node, {"this", "alias"}, f"{path}/from")
            if not isinstance(node.this, exp.Identifier):
                raise Refusal("unsupported_syntax", "table function in FROM", f"{path}/from", self._sql(node))
            name = ident(node.this)
            tid = self.schema.table_id(name)
            if tid is None:
                raise Refusal("unknown_table", f"relation {name!r} does not exist", f"{path}/from", self._sql(node))
            columns = [(c.name, c.ty) for c in self.schema.tables[tid].columns]
            query = Node("Table", tuple(t for _, t in columns), table=tid)
        elif isinstance(node, exp.Subquery):
            check_args(node, {"this", "alias"}, f"{path}/from")
            # A derived table is not lateral: it sees the enclosing query's context, not its siblings.
            query, out_names = self.select(self.subquery_select(node.this, path), parent, ctx_len, f"{path}/derived",
                                           top=False)
            name = None
            columns = list(zip(out_names, query.ann))
        else:
            raise Refusal("lateral" if isinstance(node, exp.Lateral) else "unsupported_syntax",
                          f"FROM item {type(node).__name__}", f"{path}/from", self._sql(node))
        if alias is not None:
            check_args(alias, {"this", "columns"}, f"{path}/from")
            if alias.this is not None:
                name = ident(alias.this)
            renames = [ident(c) for c in alias.args.get("columns") or []]
            if len(renames) > len(columns):
                raise Refusal("unknown_column", f"{name!r} has {len(columns)} columns but {len(renames)} aliases",
                              f"{path}/from", self._sql(node))
            columns = [(renames[i] if i < len(renames) else n, t) for i, (n, t) in enumerate(columns)]
        return query, Frame((RangeItem(name, tuple(columns), 0),))

    def _visible_cte(self, node: exp.Table) -> cte.CteDef | None:
        """The innermost visible WITH item an unqualified table name refers to."""
        if not isinstance(node.this, exp.Identifier) or node.args.get("db") or node.args.get("catalog"):
            return None
        name = ident(node.this)
        return next((d for d in reversed(self.ctes) if d.name == name), None)

    # -- select list, GROUP BY, ORDER BY ---------------------------------------------------------

    def _select_items(self, sel: exp.Select, level: Level, path: str) -> list[SelectItem]:
        """The select list with stars expanded and output names (alias or PostgreSQL's implied name)."""
        items: list[SelectItem] = []
        for e in sel.expressions:
            star_of = None
            if isinstance(e, exp.Star):
                check_args(e, set(), path)
                star_of = level.frame.items
            elif isinstance(e, exp.Column) and isinstance(e.this, exp.Star):
                check_args(e, {"this", "table"}, path)
                check_args(e.this, set(), path)
                qualifier = ident(e.args["table"])
                star_of = tuple(i for i in level.frame.items if i.name == qualifier)
                if not star_of:
                    raise Refusal("unknown_table", f"missing FROM-clause entry for table {qualifier!r}", f"{path}/select", self._sql(e))
            if star_of is not None:
                for item in star_of:
                    for j, (n, t) in enumerate(item.columns):
                        items.append(SelectItem(n, None, col(level.ctx_len + item.offset + j, t)))
            elif isinstance(e, exp.Alias):
                check_args(e, {"this", "alias"}, path)
                items.append(SelectItem(ident(e.args["alias"]), e.this))
            else:
                items.append(SelectItem(implied_name(e), e))
        return items

    def _group_keys(self, group: exp.Group, items: list[SelectItem], level: Level, path: str) -> list[Node]:
        check_args(group, {"expressions"}, f"{path}/group")
        sc = ExprScope(level, "GROUP BY")
        keys: list[Node] = []
        for g in group.expressions:
            target = self._select_reference(g, items, path, prefer_input=level)
            if target is not None:
                key = target.bound if target.bound is not None else self.binder.expr(target.source, sc, f"{path}/group")
            else:
                key = self.binder.expr(g, sc, f"{path}/group")
            if key not in keys:  # PostgreSQL drops repeated grouping expressions
                keys.append(key)
        return keys

    def _select_reference(self, node: exp.Expression, items: list[SelectItem], path: str,
                          prefer_input: Level | None = None) -> SelectItem | None:
        """An ordinal or a bare output-column name in GROUP BY / ORDER BY.

        GROUP BY prefers an input column of the same name (``prefer_input``); ORDER BY prefers output names
        (PostgreSQL's findTargetlistEntrySQL92)."""
        if isinstance(node, exp.Literal) and not node.is_string and node.this.isdigit():
            n = int(node.this)
            if not 1 <= n <= len(items):
                raise Refusal("invalid_ordinal", f"position {n} is not in select list", path, self._sql(node))
            return items[n - 1]
        if isinstance(node, exp.Column) and node.args.get("table") is None and isinstance(node.this, exp.Identifier):
            name = ident(node.this)
            if prefer_input is not None and prefer_input.has_local_column(name):
                return None
            hits = [i for i in items if i.name == name]
            # Several output columns of that name are ambiguous unless they are the same expression.
            if len({h.source.sql(self.dialect) if h.source is not None else repr(h.bound) for h in hits}) > 1:
                raise Refusal("ambiguous_order_key", f"{name!r} matches several output columns", path, self._sql(node))
            return hits[0] if hits else None
        return None

    def _order_position(self, o: exp.Expression, items: list[SelectItem], sc: ExprScope, path: str) -> int | Node:
        """An output position, or a bound expression to match against the output after grouping."""
        if not isinstance(o, exp.Ordered):
            raise Refusal("unsupported_syntax", "ORDER BY item", f"{path}/order", self._sql(o))
        check_args(o, {"this", "desc", "nulls_first"}, f"{path}/order")
        target = self._select_reference(o.this, items, f"{path}/order")
        if target is not None:
            return items.index(target)
        return default_type(self.binder.value(o.this, ExprScope(sc.level, "ORDER BY", sc.aggs), f"{path}/order"), path)


class Regroup:
    """Maps pre-group expressions (over ``ctx ++ from_row``) to post-group ones (over ``ctx ++ keys ++ aggs``)."""

    def __init__(self, level: Level, keys: list[Node], collector: AggCollector, path: str):
        self.level = level
        self.path = path
        self.keys = keys
        self.collector = collector
        self.key_index = {k: i for i, k in enumerate(keys)}  # keys are distinct (``_group_keys``)
        self.from_width = level.frame.width
        # Positions past the FROM row (subquery rows) shift by the change of the row width.
        self.width_change = len(keys) + len(collector.aggs) - self.from_width

    def grouped_query(self, where: Node, has_group_by: bool) -> Node:
        aggs = tuple(self.collector.aggs)
        if has_group_by:
            ann = tuple(k.ann for k in self.keys) + tuple(self.collector.types)
            return Node("GroupBy", ann, keys=tuple(self.keys), aggs=aggs, input=where)
        return Node("Aggregate", tuple(self.collector.types), aggs=aggs, input=where)

    def apply(self, node: Node) -> Node:
        ctx = self.level.ctx_len
        if node.sort == "expr" and node in self.key_index:
            k = self.key_index[node]
            return col(ctx + k, self.keys[k].ann)
        if node.tag == "AggSlot":
            return col(ctx + len(self.keys) + node.slot, node.ann)
        if node.tag == "Col":
            i = node.index
            if i < ctx:
                return node
            if i < ctx + self.from_width:
                raise Refusal("ungrouped_column",
                              f"column {self.level.column_name(i)} must appear in GROUP BY or be used in an aggregate",
                              f"{self.path}/select", self.level.column_name(i))
            return node.replace(index=i + self.width_change)
        return node.map_children(self.apply)


def _project(body: Node, exprs: list[Node], ctx_len: int) -> Node:
    """``Project(exprs, body)``; a select list that is exactly the input row (e.g. SUM(x) over Aggregate, or * over
    one table) needs no Project: the input already is the result."""
    identity = [col(ctx_len + i, t) for i, t in enumerate(body.ann)]
    if exprs == identity:
        return body
    return Node("Project", tuple(e.ann for e in exprs), exprs=tuple(exprs), input=body)


def _cannot_fail(e: Node) -> bool:
    """Expressions without an error case: column references (including grouped keys and aggregate results),
    literals and the exact widening casts."""
    if e.tag == "Cast":
        return e.cast in ("Int4ToInt8", "IntToNumeric") and _cannot_fail(e.arg)
    return e.tag in ("Col", "Lit")


def _has_local_aggregate(node: exp.Expression) -> bool:
    """An aggregate call of this query level (not inside a subquery)."""
    return any(isinstance(n, exp.AggFunc)
               for n in node.walk(prune=lambda n: n is not node and isinstance(n, (exp.Select, exp.Subquery))))


def implied_name(node: exp.Expression) -> str:
    """PostgreSQL's FigureColname for the supported expressions."""
    name, _ = _figure_name(node)
    return name or "?column?"


_CAST_NAMES = {"INT": "int4", "BIGINT": "int8", "DECIMAL": "numeric", "DATE": "date", "TIMESTAMP": "timestamp",
               "TEXT": "text", "VARCHAR": "varchar", "CHAR": "bpchar", "BOOLEAN": "bool"}


def _figure_name(node: exp.Expression) -> tuple[str | None, int]:
    """(name, strength) as in PostgreSQL: column names (2) beat type names of casts (1)."""
    if isinstance(node, exp.Paren):
        return _figure_name(node.this)
    if isinstance(node, exp.Column) and isinstance(node.this, exp.Identifier):
        return ident(node.this), 2
    if isinstance(node, exp.Cast):
        name, strength = _figure_name(node.this)
        if strength <= 1:
            return _CAST_NAMES.get(node.args["to"].this.name), 1
        return name, strength
    if isinstance(node, (exp.Count, exp.Sum, exp.Avg, exp.Min, exp.Max)):
        return type(node).__name__.lower(), 2
    if isinstance(node, exp.Case):
        # PostgreSQL: the ELSE result's name if it is a strong one, else "case".
        default = node.args.get("default")
        name, strength = _figure_name(default) if default is not None else (None, 0)
        return (name, strength) if strength > 1 else ("case", 1)
    if isinstance(node, (exp.Coalesce, exp.Nullif, exp.Extract, exp.Substring)):
        return type(node).__name__.lower(), 2
    if isinstance(node, exp.Exists):
        return "exists", 2
    if isinstance(node, exp.Boolean):
        return "bool", 1
    if isinstance(node, exp.Subquery) and isinstance(node.this, exp.Select) and node.this.expressions:
        first = node.this.expressions[0]
        return (ident(first.args["alias"]), 2) if isinstance(first, exp.Alias) else _figure_name(first)
    return None, 0
