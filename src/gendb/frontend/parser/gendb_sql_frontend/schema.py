"""Schema DDL (``CREATE TABLE`` statements, then ``ALTER TABLE ... ADD`` table constraints) to the typed schema.

Table ids are DDL order.  Unquoted identifiers fold to lower case, quoted ones are kept.  NOT NULL is the column's
nullability; PRIMARY KEY columns are NOT NULL (as in PostgreSQL).  PRIMARY KEY, UNIQUE, FOREIGN KEY and CHECK are
declared constraints of the table (``features/constraints.py``; meaning: Verus ``spec::constraints``), recorded in the
document and checked by the verified evaluator; a constraint form without a represented meaning is a named refusal.

After the last ``CREATE TABLE``, each ``ALTER TABLE name ADD [CONSTRAINT n] <table constraint>`` appends exactly one
constraint to that table, resolved against every created table (so a FOREIGN KEY may reference a table created
later) and the constraints added before it, as PostgreSQL resolves the same script.  It never changes a column: a
PRIMARY KEY over a nullable column (PostgreSQL would make the column NOT NULL) and NOT VALID (PostgreSQL would not
check existing rows) are named refusals, as is any other ALTER form or a CREATE TABLE after an ALTER TABLE.  A DDL
without ALTER TABLE gives the same schema as before this path existed.
"""

from __future__ import annotations

from dataclasses import dataclass, replace

from sqlglot import exp

from .features import constraints
from .parse import check_args, ident, parse_statements
from .refusal import Refusal
from .sqltypes import ColTy, SqlType, column_type, sql_type


@dataclass(frozen=True)
class Column:
    name: str
    ty: ColTy


@dataclass(frozen=True)
class Table:
    name: str
    columns: tuple[Column, ...]
    constraints: tuple[constraints.Constraint, ...] = ()  # declaration order

    def to_json(self) -> dict:
        return {"name": self.name,
                "columns": [{"name": c.name, "type": c.ty.ty.to_json(), "nullable": c.ty.nullable}
                            for c in self.columns],
                "constraints": [k.to_json() for k in self.constraints]}


@dataclass(frozen=True)
class Schema:
    tables: tuple[Table, ...]

    def table_id(self, name: str) -> int | None:
        for i, t in enumerate(self.tables):
            if t.name == name:
                return i
        return None

    def to_json(self) -> dict:
        return {"tables": [t.to_json() for t in self.tables]}


def load_schema(ddl: str, dialect: str) -> Schema:
    tables: list[Table] = []
    altered = False
    for stmt in parse_statements(ddl, dialect, "schema"):
        if isinstance(stmt, exp.Alter) or (isinstance(stmt, exp.Command) and str(stmt.this).upper() == "ALTER"):
            altered = True
            t, added = _alter_table_add(stmt, dialect, tables)
            tables[t] = replace(tables[t], constraints=tables[t].constraints + (added,))
            continue
        if altered:
            raise Refusal("invalid_schema", "CREATE TABLE after ALTER TABLE: every table is created before constraints "
                          "are added", "schema", stmt.sql(dialect)[:200])
        if not (isinstance(stmt, exp.Create) and (stmt.args.get("kind") or "").upper() == "TABLE"
                and isinstance(stmt.this, exp.Schema) and isinstance(stmt.this.this, exp.Table)):
            raise Refusal("invalid_schema", "only CREATE TABLE name (...) statements are accepted", "schema",
                          stmt.sql(dialect)[:200])
        check_args(stmt, {"this", "kind"}, "schema")
        table = _table(stmt.this, dialect, tables)
        if any(t.name == table.name for t in tables):
            raise Refusal("duplicate_table", f"table {table.name!r} defined twice", "schema")
        tables.append(table)
    if not tables:
        raise Refusal("invalid_schema", "no CREATE TABLE statement", "schema")
    return Schema(tuple(tables))


def _alter_table_add(stmt: exp.Alter | exp.Command, dialect: str,
                     tables: list[Table]) -> tuple[int, constraints.Constraint]:
    """One ``ALTER TABLE name ADD [CONSTRAINT n] <table constraint>``: the table id and its added constraint."""
    if isinstance(stmt, exp.Command):
        # sqlglot 27 keeps an ALTER it cannot parse as an opaque command, e.g. an unnamed ADD CHECK (the named
        # ``ADD CONSTRAINT n CHECK (...)`` parses) or several comma-separated actions.
        raise Refusal("parse_error", "schema: sqlglot parses this ALTER statement only as an opaque command (an "
                      "unnamed ADD CHECK needs CONSTRAINT <name>; one ADD <table constraint> per statement)",
                      "schema", stmt.sql(dialect)[:200])
    sql = stmt.sql(dialect)[:200]
    if stmt.args.get("not_valid"):
        raise Refusal("constraint_not_valid", "ADD ... NOT VALID", "schema", sql)
    check_args(stmt, {"this", "kind", "actions"}, "schema")
    actions = stmt.args.get("actions") or []
    if ((stmt.args.get("kind") or "").upper() != "TABLE" or len(actions) != 1
            or not isinstance(actions[0], exp.AddConstraint) or len(actions[0].expressions) != 1):
        raise Refusal("invalid_schema", "only ALTER TABLE name ADD <one table constraint> is accepted", "schema", sql)
    check_args(actions[0], {"expressions"}, "schema")
    check_args(stmt.this, {"this"}, "schema")
    name = ident(stmt.this.this)
    t = next((i for i, table in enumerate(tables) if table.name == name), None)
    if t is None:
        raise Refusal("unknown_table", f"ALTER TABLE names table {name!r}, which is not created before it", "schema",
                      sql)
    where = f"schema/{name}"
    raw = constraints.table_constraint(actions[0].expressions[0], where, dialect)
    if raw is None:
        raise Refusal("unsupported_constraint", f"table element {sql}", where, sql)
    return t, constraints.resolve_added(raw, t, tables, dialect, where)


@dataclass(frozen=True)
class _ColumnDecl:
    """A column definition as declared: its NULL / NOT NULL clauses (before PRIMARY KEY makes it NOT NULL)."""
    name: str
    ty: SqlType
    not_null: bool
    explicit_null: bool


def _table(node: exp.Schema, dialect: str, earlier: list[Table]) -> Table:
    """One CREATE TABLE body; ``earlier`` are the tables defined before it (foreign-key targets)."""
    check_args(node.this, {"this"}, "schema")
    name = ident(node.this.this)
    where = f"schema/{name}"
    decls: list[_ColumnDecl] = []
    raw: list[constraints.RawConstraint] = []  # declaration order
    for item in node.expressions:
        if isinstance(item, exp.ColumnDef):
            decls.append(_column_definition(item, dialect, where, raw))
        else:
            declared = constraints.table_constraint(item, where, dialect)
            if declared is None:
                raise Refusal("unsupported_constraint", f"table element {item.sql(dialect)[:120]}", where)
            raw.append(declared)
    names = [d.name for d in decls]
    for n in names:
        if names.count(n) > 1:
            raise Refusal("duplicate_column", f"column {n!r} defined twice", where)
    keys = constraints.key_positions(raw, names, where)
    primary_key_columns = {i for k, positions in keys.items() if raw[k].primary for i in positions}
    for i in primary_key_columns:
        if decls[i].explicit_null:
            raise Refusal("invalid_schema", f"PRIMARY KEY column {names[i]!r} is declared NULL", where)
    columns = tuple(Column(d.name, column_type(d.ty, not (d.not_null or i in primary_key_columns)))
                    for i, d in enumerate(decls))
    return Table(name, columns, constraints.resolve(name, list(columns), raw, keys, earlier, dialect, where))


def _column_definition(item: exp.ColumnDef, dialect: str, where: str,
                       raw: list[constraints.RawConstraint]) -> _ColumnDecl:
    """A column definition; appends its PRIMARY KEY / UNIQUE / REFERENCES / CHECK clauses to ``raw``."""
    check_args(item, {"this", "kind", "constraints"}, where)
    name = ident(item.this)
    column_where = f"{where}/{name}"
    ty = sql_type(item.kind, column_where)
    not_null = explicit_null = False
    for c in item.args.get("constraints") or []:
        check_args(c, {"this", "kind"}, column_where)
        kind = c.args.get("kind")
        if isinstance(kind, exp.NotNullColumnConstraint):
            check_args(kind, {"allow_null"}, column_where)
            if kind.args.get("allow_null"):
                explicit_null = True
            else:
                not_null = True
            continue
        constraint_name = ident(c.this) if isinstance(c.this, exp.Identifier) else None
        declared = constraints.column_constraint(kind, constraint_name, name, column_where, c.sql(dialect)[:200])
        if declared is None:
            raise Refusal("unsupported_constraint", f"column constraint {c.sql(dialect)}", column_where)
        raw.append(declared)
    if explicit_null and not_null:
        raise Refusal("invalid_schema", f"conflicting NULL/NOT NULL declarations for column {name!r}", column_where)
    return _ColumnDecl(name, ty, not_null, explicit_null)
