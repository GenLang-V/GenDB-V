"""Names and scopes: FROM items, levels, and the flat environment ``ctx ++ row``.

A column reference resolves to an absolute position in the environment of the expression that contains it.  The
environment of a query level is the environment of the enclosing level (``ctx``, length ``ctx_len``) followed by the
level's own row, so an outer reference keeps the same position at every depth (the LeanSQL mechanism).
"""

from __future__ import annotations

from dataclasses import dataclass

from .refusal import Refusal
from .sqltypes import ColTy


@dataclass(frozen=True)
class RangeItem:
    """A FROM item: its visible name (None for an unnamed derived table) and columns."""
    name: str | None
    columns: tuple[tuple[str, ColTy], ...]
    offset: int  # first position of its columns inside the frame row


@dataclass(frozen=True)
class Frame:
    """A row of one or more FROM items (a join tree, or the whole FROM clause)."""
    items: tuple[RangeItem, ...]

    @property
    def width(self) -> int:
        return sum(len(i.columns) for i in self.items)

    def concat(self, right: "Frame", right_nullable: bool = False) -> "Frame":
        shift = self.width
        moved = tuple(RangeItem(i.name, tuple((n, t.with_nullable(True) if right_nullable else t) for n, t in i.columns),
                                i.offset + shift) for i in right.items)
        return Frame(self.items + moved)


@dataclass
class Level:
    """One query level: the outer level, the length of its context, and the visible frame."""
    parent: "Level | None"
    ctx_len: int
    frame: Frame

    @property
    def env_len(self) -> int:
        return self.ctx_len + self.frame.width

    def column_name(self, index: int) -> str:
        """``item.column`` of environment position ``index`` (for diagnostics)."""
        level: Level | None = self
        while level is not None:
            if index >= level.ctx_len:
                rel = index - level.ctx_len
                for item in level.frame.items:
                    if item.offset <= rel < item.offset + len(item.columns):
                        col = item.columns[rel - item.offset][0]
                        return f"{item.name}.{col}" if item.name else col
                return f"#{index}"
            level = level.parent
        return f"#{index}"

    def resolve(self, qualifier: str | None, name: str, path: str, sql: str) -> tuple[int, ColTy]:
        """PostgreSQL column resolution: innermost level first; ambiguity is an error at that level."""
        level: Level | None = self
        while level is not None:
            if qualifier is not None:
                item = next((i for i in level.frame.items if i.name == qualifier), None)
                if item is not None:
                    hits = [(j, t) for j, (n, t) in enumerate(item.columns) if n == name]
                    if not hits:
                        raise Refusal("unknown_column", f"column {qualifier}.{name} does not exist", path, sql)
                    if len(hits) > 1:
                        raise Refusal("ambiguous_column", f"column reference {qualifier}.{name} is ambiguous", path, sql)
                    j, t = hits[0]
                    return level.ctx_len + item.offset + j, t
            else:
                hits = [(i.offset + j, t) for i in level.frame.items for j, (n, t) in enumerate(i.columns) if n == name]
                if len(hits) > 1:
                    raise Refusal("ambiguous_column", f"column reference {name!r} is ambiguous", path, sql)
                if hits:
                    rel, t = hits[0]
                    return level.ctx_len + rel, t
            level = level.parent
        if qualifier is not None:
            raise Refusal("unknown_table", f"missing FROM-clause entry for table {qualifier!r}", path, sql)
        raise Refusal("unknown_column", f"column {name!r} does not exist", path, sql)

    def has_local_column(self, name: str) -> bool:
        return any(n == name for i in self.frame.items for n, _ in i.columns)
