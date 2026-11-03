"""Parsing with the pinned sqlglot, plus the syntax checks sqlglot cannot make for us.

sqlglot is a permissive multi-dialect parser: it normalizes or accepts some text that PostgreSQL rejects.  The
resolver therefore never trusts a node it does not know: ``check_args`` refuses every argument a handler does not
consume, so a construct sqlglot keeps on an otherwise supported node (TABLESAMPLE, locking clauses, FILTER, ...) is
a named refusal rather than a silent drop.
"""

from __future__ import annotations

import sqlglot
from sqlglot import exp
from sqlglot.errors import ParseError, TokenError
from sqlglot.tokens import TokenType

from .refusal import Refusal


def ident(node: exp.Identifier) -> str:
    """PostgreSQL identifier folding: unquoted names fold to lower case, quoted ones are kept."""
    return node.this if node.quoted else node.this.lower()


def check_args(node: exp.Expression, allowed: set[str], path: str, dialect: str = "postgres") -> None:
    """Refuse every argument of ``node`` that the caller does not handle."""
    for key, value in node.args.items():
        if key in allowed or value is None or value is False or value == [] or value == "":
            continue
        raise Refusal("unsupported_syntax", f"{type(node).__name__} with {key!r} is outside the fragment",
                      path, node.sql(dialect)[:200])


def parse_statements(text: str, dialect: str, what: str) -> list[exp.Expression]:
    try:
        return [s for s in sqlglot.parse(text, dialect=dialect) if s is not None]
    except (ParseError, TokenError) as e:
        raise Refusal("parse_error", f"{what}: {str(e).splitlines()[0]}") from None


def parse_query(sql: str, dialect: str) -> exp.Select:
    """The one SELECT statement of ``sql`` (or of the view script, see ``view_script_as_with``)."""
    statements = parse_statements(sql, dialect, "query")
    if len(statements) == 3 and isinstance(statements[0], exp.Create):
        statements = [view_script_as_with(statements, dialect)]
    if len(statements) != 1:
        raise Refusal("multiple_statements", f"{len(statements)} statements in the query text")
    stmt = statements[0]
    if isinstance(stmt, (exp.Union, exp.Intersect, exp.Except)):
        raise Refusal("set_operation", "set operations are outside the fragment", "query", stmt.sql(dialect))
    if not isinstance(stmt, exp.Select):
        raise Refusal("not_select", f"statement is {type(stmt).__name__}", "query", stmt.sql(dialect)[:200])
    _check_join_keywords(sql, stmt, dialect)
    return stmt


def _check_join_keywords(sql: str, stmt: exp.Expression, dialect: str) -> None:
    """sqlglot reads ``a JOIN b`` (no ON; a PostgreSQL syntax error) as the comma join ``a, b``.

    Every JOIN keyword token must belong to a join that carries ON, USING, CROSS, NATURAL or LATERAL; comma joins
    have no JOIN token.
    """
    tokens = sqlglot.Dialect.get_or_raise(dialect).tokenize(sql)
    keywords = sum(1 for t in tokens if t.token_type == TokenType.JOIN)
    qualified = sum(1 for j in stmt.find_all(exp.Join)
                    if j.args.get("on") is not None or j.args.get("using") or j.args.get("method")
                    or (j.args.get("kind") or "").upper() == "CROSS" or isinstance(j.this, exp.Lateral))
    if keywords > qualified:
        raise Refusal("join_without_condition", "a JOIN keyword has no ON / USING clause", "from")


def view_script_as_with(statements: list[exp.Expression], dialect: str) -> exp.Select:
    """The TPC-H view script ``CREATE VIEW v [(cols)] AS q; SELECT ...; DROP VIEW [IF EXISTS] v;`` (exactly these
    three statements) as the query ``WITH v [(cols)] AS (q) SELECT ...`` (``features/cte.py`` gives WITH its
    meaning)."""
    create, body, drop = statements
    shape = (isinstance(create, exp.Create) and str(create.args.get("kind") or "").upper() == "VIEW"
             and isinstance(body, exp.Select) and isinstance(drop, exp.Drop)
             and str(drop.args.get("kind") or "").upper() == "VIEW")
    if not shape:
        raise Refusal("view_script", "expected CREATE VIEW v AS q; SELECT ...; DROP VIEW v;")
    for key, value in create.args.items():
        if key not in ("this", "kind", "expression") and value not in (None, False, [], ""):
            raise Refusal("view_script", f"CREATE VIEW with {key!r}", "query", create.sql(dialect)[:200])
    for key, value in drop.args.items():
        if key not in ("this", "kind", "exists") and value not in (None, False, [], ""):
            raise Refusal("view_script", f"DROP VIEW with {key!r}", "query", drop.sql(dialect)[:200])
    target = create.this
    columns = []
    if isinstance(target, exp.Schema):
        columns = list(target.expressions)
        target = target.this
    if (not isinstance(target, exp.Table) or not isinstance(drop.this, exp.Table)
            or target.args.get("db") or drop.this.args.get("db")
            or ident(target.this) != ident(drop.this.this)):
        raise Refusal("view_script", "the dropped view is not the created one", "query")
    name = ident(target.this)
    body = body.copy()
    with_ = body.args.get("with")
    items = list(with_.expressions) if with_ is not None else []
    if any(ident(i.args["alias"].this) == name for i in items):
        raise Refusal("view_script", f"the query redefines the view name {name!r} in its WITH", "query")
    view = exp.CTE(this=create.args.get("expression").copy(),
                   alias=exp.TableAlias(this=exp.to_identifier(name, quoted=target.this.quoted),
                                        columns=[c.copy() for c in columns]))
    recursive = with_.args.get("recursive") if with_ is not None else None
    body.set("with", exp.With(expressions=[view, *items], recursive=recursive))
    return body
