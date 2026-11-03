"""Integrity constraints of the schema DDL.

Every PRIMARY KEY, UNIQUE, FOREIGN KEY and CHECK of a ``CREATE TABLE`` becomes a declared constraint of the schema
document, with the meaning of Verus ``spec::constraints`` (checked by the verified evaluator before any query runs);
NOT NULL stays the column's nullability.  A form whose meaning is not represented is a named refusal, never dropped:

* PRIMARY KEY / UNIQUE, column or table level, composite, named or not: the column positions, ``primary``,
  ``nulls_distinct`` (``UNIQUE NULLS NOT DISTINCT`` is ``False``; the explicit ``NULLS DISTINCT`` does not parse in
  sqlglot 27 and is a ``parse_error``).  PRIMARY KEY makes its columns NOT NULL (as PostgreSQL).
* FOREIGN KEY / REFERENCES: the referencing columns, the referenced table (an earlier table or the table itself;
  PostgreSQL requires it to exist) and columns (default: its primary key), which must be exactly the column set of a
  declared non-deferrable key of that table (any order; PostgreSQL 55000 otherwise), MATCH SIMPLE (default) or FULL.
  Referential actions and DEFERRABLE / INITIALLY DEFERRED only affect when PostgreSQL checks a modification: they
  are recorded as metadata and do not change the committed-database predicate.
* CHECK: bound by the query binder over the table's own row (columns by name, optionally qualified by the table
  name), with no subquery and no aggregate; the verified typing re-checks it over an empty schema.

Named refusals cover MATCH PARTIAL, NOT ENFORCED, index options, foreign-key type pairs whose PostgreSQL equality
differs from the semantics' value equality, and DDL that PostgreSQL itself rejects.  Constraint names are metadata
only.

Reading one table has two phases: ``column_constraint`` / ``table_constraint`` collect raw declarations (column
names unresolved) while the columns are read; ``key_positions`` and ``resolve`` then resolve them against the final
columns and the tables defined before.  A constraint added by ``ALTER TABLE ... ADD`` (``schema.py``) is one raw
table constraint resolved by ``resolve_added`` against the table's columns and constraints so far, with every created
table a possible FOREIGN KEY target.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import TYPE_CHECKING

from sqlglot import exp

from ..ast import Node, encode_arena
from ..bind import Binder, ExprScope
from ..parse import check_args, ident
from ..refusal import Refusal
from ..scope import Frame, Level, RangeItem
from ..sqltypes import SqlType

if TYPE_CHECKING:
    from ..schema import Column, Table

ACTIONS = {"NO ACTION": "no_action", "RESTRICT": "restrict", "CASCADE": "cascade", "SET NULL": "set_null",
           "SET DEFAULT": "set_default"}


@dataclass(frozen=True)
class Timing:
    deferrable: bool = False
    initially_deferred: bool = False


@dataclass(frozen=True)
class Key:
    name: str | None
    primary: bool
    columns: tuple[int, ...]
    nulls_distinct: bool
    timing: Timing

    def to_json(self) -> dict:
        return {"kind": "key", "name": self.name, "primary": self.primary, "columns": list(self.columns),
                "nulls_distinct": self.nulls_distinct, "deferrable": self.timing.deferrable,
                "initially_deferred": self.timing.initially_deferred}


@dataclass(frozen=True)
class ForeignKey:
    name: str | None
    columns: tuple[int, ...]
    table: int
    ref_columns: tuple[int, ...]
    match_full: bool
    on_delete: str
    on_update: str
    timing: Timing

    def to_json(self) -> dict:
        return {"kind": "foreign_key", "name": self.name, "columns": list(self.columns), "table": self.table,
                "ref_columns": list(self.ref_columns), "match_full": self.match_full, "on_delete": self.on_delete,
                "on_update": self.on_update, "deferrable": self.timing.deferrable,
                "initially_deferred": self.timing.initially_deferred}


@dataclass(frozen=True)
class Check:
    name: str | None
    pred: Node  # sort pred, over the table's row

    def to_json(self) -> dict:
        nodes, root = encode_arena(self.pred)
        return {"kind": "check", "name": self.name, "root": root, "nodes": nodes}


Constraint = Key | ForeignKey | Check


# ------------------------------------------------------------------------------------------------------------
# Raw declarations collected while reading one CREATE TABLE (names still unresolved).

@dataclass(frozen=True)
class RawKey:
    name: str | None
    primary: bool
    columns: tuple[str, ...]
    nulls_distinct: bool
    timing: Timing
    sql: str


@dataclass(frozen=True)
class RawForeignKey:
    name: str | None
    columns: tuple[str, ...]
    table: str
    ref_columns: tuple[str, ...] | None  # None: the referenced table's primary key
    match_full: bool
    on_delete: str
    on_update: str
    timing: Timing
    sql: str


@dataclass(frozen=True)
class RawCheck:
    name: str | None
    expr: exp.Expression
    sql: str


RawConstraint = RawKey | RawForeignKey | RawCheck


def column_constraint(kind: exp.Expression, name: str | None, column: str, where: str,
                      sql: str) -> RawConstraint | None:
    """A column-level PRIMARY KEY / UNIQUE / REFERENCES / CHECK as a raw declaration, or None if ``kind`` is not
    one of them."""
    if isinstance(kind, exp.PrimaryKeyColumnConstraint):
        check_args(kind, {"options"}, where)
        return RawKey(name, True, (column,), True, _timing(kind.args.get("options"), where, sql), sql)
    if isinstance(kind, exp.UniqueColumnConstraint):
        if kind.this is not None:
            raise Refusal("unsupported_constraint", "a column list on a column-level UNIQUE", where, sql)
        nulls_distinct = _unique_nulls_distinct(kind, where)
        return RawKey(name, False, (column,), nulls_distinct, _timing(kind.args.get("options"), where, sql), sql)
    if isinstance(kind, exp.Reference):
        return _raw_foreign_key(name, (column,), kind, [], where, sql)
    if isinstance(kind, exp.CheckColumnConstraint):
        return _raw_check(kind, name, where, sql)
    return None


def table_constraint(item: exp.Expression, where: str, dialect: str) -> RawConstraint | None:
    """A table-level constraint element as a raw declaration, or None if ``item`` is not one."""
    name = None
    sql = item.sql(dialect)[:200]
    if isinstance(item, exp.Constraint):
        check_args(item, {"this", "expressions"}, where)
        if len(item.expressions) != 1:
            raise Refusal("unsupported_constraint", "a named constraint with several parts", where, sql)
        name = ident(item.this)
        item = item.expressions[0]
    if isinstance(item, exp.PrimaryKey):
        check_args(item, {"expressions", "options"}, where)
        return RawKey(name, True, _column_names(item.expressions, where, sql), True,
                      _timing(item.args.get("options"), where, sql), sql)
    if isinstance(item, exp.UniqueColumnConstraint):
        if not isinstance(item.this, exp.Schema) or item.this.this is not None:
            raise Refusal("unsupported_constraint", "table-level UNIQUE needs a column list", where, sql)
        nulls_distinct = _unique_nulls_distinct(item, where)
        return RawKey(name, False, _column_names(item.this.expressions, where, sql), nulls_distinct,
                      _timing(item.args.get("options"), where, sql), sql)
    if isinstance(item, exp.ForeignKey):
        check_args(item, {"expressions", "reference", "options"}, where)
        if not isinstance(item.args.get("reference"), exp.Reference):
            raise Refusal("unsupported_constraint", "FOREIGN KEY without REFERENCES", where, sql)
        columns = _column_names(item.expressions, where, sql)
        return _raw_foreign_key(name, columns, item.args["reference"], item.args.get("options"), where, sql)
    if isinstance(item, exp.CheckColumnConstraint):
        return _raw_check(item, name, where, sql)
    if name is not None:
        raise Refusal("unsupported_constraint", f"named table element {sql}", where, sql)
    return None


def _column_names(items: list, where: str, sql: str) -> tuple[str, ...]:
    """A parenthesized column-name list (identifiers; key lists may arrive as ``Ordered(Column)``)."""
    names = []
    for e in items:
        column = e
        if isinstance(e, exp.Ordered):
            if e.sql("postgres") != e.this.sql("postgres"):
                raise Refusal("unsupported_constraint", "ordering or NULLS placement in a key column list", where, sql)
            column = e.this
        if isinstance(column, exp.Column) and not column.args.get("table") and isinstance(column.this, exp.Identifier):
            column = column.this
        if not isinstance(column, exp.Identifier):
            raise Refusal("unsupported_constraint", f"key column {e.sql('postgres')!r} is not a column name", where, sql)
        names.append(ident(column))
    if not names:
        raise Refusal("invalid_schema", "empty column list", where, sql)
    return tuple(names)


def _option_text(option: object) -> str | None:
    """A keyword option as normalized upper-case text (sqlglot keeps them as strings), else None."""
    return " ".join(str(option).upper().split()) if isinstance(option, str) else None


def _timing(options: list | None, where: str, sql: str) -> Timing:
    deferrable = initially_deferred = not_deferrable = False
    for o in options or []:
        text = _option_text(o)
        if text == "DEFERRABLE":
            deferrable = True
        elif text == "NOT DEFERRABLE":
            not_deferrable = True
        elif text == "INITIALLY DEFERRED":
            initially_deferred = True
        elif text in ("INITIALLY IMMEDIATE", "ENFORCED"):
            pass
        elif text == "NOT ENFORCED":
            raise Refusal("constraint_not_enforced", "NOT ENFORCED constraint", where, sql)
        else:
            raise Refusal("constraint_option", f"constraint option {o!s}", where, sql)
    if not_deferrable and (deferrable or initially_deferred):
        raise Refusal("invalid_schema", "conflicting constraint deferrability clauses (PostgreSQL 42601)", where, sql)
    return Timing(deferrable or initially_deferred, initially_deferred)


def _raw_foreign_key(name: str | None, columns: tuple[str, ...], ref: exp.Reference, extra_options: list | None,
                     where: str, sql: str) -> RawForeignKey:
    """A FOREIGN KEY / REFERENCES declaration: ``ref`` is its REFERENCES clause, ``extra_options`` the options
    sqlglot attaches to a table-level FOREIGN KEY instead of the clause."""
    check_args(ref, {"this", "expressions", "options"}, where)
    target = ref.this
    ref_columns: tuple[str, ...] | None = None
    if isinstance(target, exp.Schema):
        check_args(target, {"this", "expressions"}, where)
        ref_columns = _column_names(target.expressions, where, sql)
        target = target.this
    if not isinstance(target, exp.Table):
        raise Refusal("unsupported_constraint", "REFERENCES target is not a table name", where, sql)
    check_args(target, {"this"}, where)
    match_full = False
    on_delete = on_update = "no_action"
    timing_options = []
    for o in list(ref.args.get("options") or []) + list(extra_options or []):
        text = _option_text(o) or ""
        if text in ("MATCH FULL", "MATCH SIMPLE"):
            match_full = text == "MATCH FULL"
        elif text == "MATCH PARTIAL":
            raise Refusal("fk_match_partial", "MATCH PARTIAL is not implemented by PostgreSQL", where, sql)
        elif text.startswith("ON DELETE ") and text[10:] in ACTIONS:
            on_delete = ACTIONS[text[10:]]
        elif text.startswith("ON UPDATE ") and text[10:] in ACTIONS:
            on_update = ACTIONS[text[10:]]
        else:
            timing_options.append(o)
    return RawForeignKey(name, columns, ident(target.this), ref_columns, match_full, on_delete, on_update,
                         _timing(timing_options, where, sql), sql)


def _unique_nulls_distinct(u: exp.UniqueColumnConstraint, where: str) -> bool:
    check_args(u, {"this", "nulls", "options"}, where)
    return not u.args.get("nulls")


def _raw_check(node: exp.CheckColumnConstraint, name: str | None, where: str, sql: str) -> RawCheck:
    check_args(node, {"this", "enforced"}, where)
    if node.args.get("enforced") not in (None, True):
        raise Refusal("constraint_not_enforced", "NOT ENFORCED CHECK", where, sql)
    return RawCheck(name, node.this, sql)


# ------------------------------------------------------------------------------------------------------------
# Resolution (after all columns of the table are known).

def key_positions(raw: list[RawConstraint], column_names: list[str], where: str) -> dict[int, tuple[int, ...]]:
    """The column positions of every raw key, by its index in ``raw``."""
    primaries = [r for r in raw if isinstance(r, RawKey) and r.primary]
    if len(primaries) > 1:
        raise Refusal("multiple_primary_keys", "more than one PRIMARY KEY", where, primaries[1].sql)
    positions = {}
    for i, r in enumerate(raw):
        if isinstance(r, RawKey):
            if len(set(r.columns)) != len(r.columns):
                raise Refusal("duplicate_key_column", "a column appears twice in the key", where, r.sql)
            positions[i] = _positions(r.columns, column_names, where, r.sql)
    return positions


def resolve(table_name: str, columns: list[Column], raw: list[RawConstraint], keys: dict[int, tuple[int, ...]],
            earlier: list[Table], dialect: str, where: str) -> tuple[Constraint, ...]:
    """The constraints of one table in declaration order.

    ``columns``: the table's columns (nullability final); ``keys``: the ``key_positions`` of ``raw``; ``earlier``:
    the tables defined before it."""
    column_names = [c.name for c in columns]
    own_keys = [(raw[i].primary, pos, raw[i].timing.deferrable) for i, pos in keys.items()]
    out: list[Constraint] = []
    for i, r in enumerate(raw):
        if isinstance(r, RawKey):
            out.append(Key(r.name, r.primary, keys[i], r.nulls_distinct, r.timing))
        elif isinstance(r, RawForeignKey):
            out.append(_foreign_key(r, table_name, len(earlier), columns, column_names, own_keys, earlier, where))
        else:
            out.append(Check(r.name, _bind_check(r, table_name, columns, dialect, where)))
    return tuple(out)


def resolve_added(r: RawConstraint, t: int, tables: list[Table], dialect: str, where: str) -> Constraint:
    """The constraint ``r`` that ``ALTER TABLE ... ADD`` adds to table ``t`` of ``tables`` (every created table).

    The table's columns are final and stay unchanged: a PRIMARY KEY over a nullable column is a named refusal (PostgreSQL
    would make the column NOT NULL).  Keys and the single PRIMARY KEY are checked against the constraints the table
    has so far; a FOREIGN KEY may reference any table, itself included, through a key that table has so far."""
    table = tables[t]
    columns = list(table.columns)
    column_names = [c.name for c in columns]
    own_keys = [(k.primary, k.columns, k.timing.deferrable) for k in table.constraints if isinstance(k, Key)]
    if isinstance(r, RawKey):
        if r.primary and any(primary for primary, _, _ in own_keys):
            raise Refusal("multiple_primary_keys", "more than one PRIMARY KEY", where, r.sql)
        positions = key_positions([r], column_names, where)[0]
        nullable = [column_names[i] for i in positions if columns[i].ty.nullable]
        if r.primary and nullable:
            raise Refusal("alter_primary_key_nullable_column", f"PRIMARY KEY over nullable column(s) {nullable}", where,
                          r.sql)
        return Key(r.name, r.primary, positions, r.nulls_distinct, r.timing)
    if isinstance(r, RawForeignKey):
        return _foreign_key(r, table.name, t, columns, column_names, own_keys, tables, where)
    return Check(r.name, _bind_check(r, table.name, columns, dialect, where))


def _positions(names: tuple[str, ...], column_names: list[str], where: str, sql: str) -> tuple[int, ...]:
    positions = []
    for n in names:
        if n not in column_names:
            raise Refusal("unknown_column", f"column {n!r} named in a constraint does not exist", where, sql)
        positions.append(column_names.index(n))
    return tuple(positions)


def _foreign_key(r: RawForeignKey, table_name: str, self_id: int, columns: list[Column], column_names: list[str],
                 own_keys: list[tuple[bool, tuple[int, ...], bool]], earlier: list[Table], where: str) -> ForeignKey:
    """A FOREIGN KEY of table ``table_name`` (id ``self_id``, its ``columns`` and ``own_keys``) referencing itself or
    one of the tables ``earlier`` (the tables a CREATE TABLE may reference, or every table for ALTER TABLE)."""
    cols = _positions(r.columns, column_names, where, r.sql)
    if r.table == table_name:
        tid, target_columns, target_keys = self_id, columns, own_keys
    else:
        hit = [i for i, t in enumerate(earlier) if t.name == r.table]
        if not hit:
            raise Refusal("fk_unknown_table", f"referenced table {r.table!r} is not defined before {table_name!r}", where, r.sql)
        tid = hit[0]
        target = earlier[tid]
        target_columns = list(target.columns)
        target_keys = [(k.primary, k.columns, k.timing.deferrable) for k in target.constraints if isinstance(k, Key)]
    target_names = [c.name for c in target_columns]
    # PostgreSQL references only an immediate (non-deferrable) key: 55000 when the only matching key is deferrable.
    if r.ref_columns is None:
        primary_keys = [(pos, deferrable) for primary, pos, deferrable in target_keys if primary]
        if not primary_keys:
            raise Refusal("fk_no_matching_key", f"there is no primary key for referenced table {r.table!r}", where, r.sql)
        if primary_keys[0][1]:
            raise Refusal("fk_deferrable_key", f"cannot use a deferrable primary key for referenced table {r.table!r}", where, r.sql)
        ref = primary_keys[0][0]
    else:
        ref = _positions(r.ref_columns, target_names, where, r.sql)
    if len(ref) != len(cols):
        raise Refusal("fk_arity", "number of referencing and referenced columns for foreign key disagree", where, r.sql)
    matching = [deferrable for _, pos, deferrable in target_keys if len(pos) == len(ref) and set(pos) == set(ref)]
    if len(set(ref)) != len(ref) or not matching:
        raise Refusal("fk_no_matching_key", f"no unique constraint of {r.table!r} matches the referenced columns", where, r.sql)
    if all(matching):
        raise Refusal("fk_deferrable_key", f"cannot use a deferrable unique constraint for referenced table {r.table!r}", where, r.sql)
    for c, p in zip(cols, ref):
        reason = _fk_type_refusal(columns[c].ty.ty, target_columns[p].ty.ty)
        if reason is not None:
            raise Refusal(reason, f"{column_names[c]} ({columns[c].ty.ty.pg_name()}) references {r.table}.{target_names[p]} "
                                  f"({target_columns[p].ty.ty.pg_name()})", where, r.sql)
    return ForeignKey(r.name, cols, tid, ref, r.match_full, r.on_delete, r.on_update, r.timing)


def _fk_type_refusal(child: SqlType, parent: SqlType) -> str | None:
    """None if PostgreSQL's FK equality on this pair is the semantics' value equality, else the refusal reason
    (mirrors Verus ``spec::constraints::fk_col_types_ok``)."""
    c, p = child.kind, parent.kind
    if c == "bool":
        return None if p == "bool" else "fk_type_mismatch"
    if c in ("int4", "int8"):
        return None if p in ("int4", "int8", "numeric") else "fk_type_mismatch"
    if c == "numeric":
        return None if p == "numeric" else "fk_type_mismatch"
    if c in ("date", "timestamp"):
        return None if p in ("date", "timestamp") else "fk_type_mismatch"
    if c in ("text", "varchar"):
        if p == "bpchar":
            return "fk_bpchar_coercion"
        return None if p in ("text", "varchar") else "fk_type_mismatch"
    if c == "bpchar":
        return None if p in ("text", "varchar", "bpchar") else "fk_type_mismatch"
    return "fk_type_mismatch"


def _bind_check(r: RawCheck, table_name: str, columns: list[Column], dialect: str, where: str) -> Node:
    """The CHECK condition as a resolved ``pred`` over the table's row (environment = the row)."""
    def refuse_subquery(node: exp.Expression, level: Level, path: str):
        raise Refusal("check_subquery", "cannot use subquery in check constraint", path, node.sql(dialect)[:200])

    binder = Binder(dialect, refuse_subquery, refuse_subquery)
    level = Level(None, 0, Frame((RangeItem(table_name, tuple((c.name, c.ty) for c in columns), 0),)))
    return binder.pred(r.expr, ExprScope(level, "CHECK"), f"{where}/check")
