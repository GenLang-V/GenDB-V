"""The resolved typed SQL AST and its arena JSON encoding (``gendb-sql-ast-v1``).

Node tags, fields and field kinds come from the one AST encoding schema, ``frontend/ast/ast_schema.json``, which
mirrors the Verus AST constructor for constructor and is shared with the Rust host (the ``gendb-frontend`` crate).
A ``Node`` is checked against the schema when it is built; ``decode_arena`` re-validates every structural rule of a
JSON arena (tags, fields, value ranges, child sorts, post-order tree, literal validity) without recursion, so
arbitrarily deep ASTs decode.  The node discriminator is ``tag`` because ``kind`` is a Verus field name
(``Literal::Int { v, kind }``).
"""

from __future__ import annotations

import json
import re
from typing import Any, Callable, Iterator

from .sqltypes import INT4_MAX, INT4_MIN, INT8_MAX, INT8_MIN, ColTy, ScalarTy, SqlType
from .toolchain import PARSER_DIR

SCHEMA_FILE = PARSER_DIR.parent / "ast" / "ast_schema.json"
SCHEMA: dict = json.loads(SCHEMA_FILE.read_text(encoding="utf-8"))
FORMAT: str = SCHEMA["format"]
# Internal tags exist only inside the resolver and are never encoded.  AggSlot stands for
# "the value of the slot-th aggregate of this level" until grouping maps it to a column.
INTERNAL_KINDS: dict[str, dict] = {"AggSlot": {"sort": "expr", "form": "tuple", "fields": [["slot", "nat:usize"]]}}
KINDS: dict[str, dict] = {**SCHEMA["kinds"], **INTERNAL_KINDS}
ENUMS: dict[str, list[str]] = SCHEMA["enums"]
ANNOTATIONS: dict[str, str] = SCHEMA["annotations"]
# JSON key of each annotation kind: expr nodes carry ``type``, query nodes ``columns``.
ANNOTATION_KEYS = {"coltype": "type", "coltypes": "columns"}
FIELD_NAMES: dict[str, tuple[str, ...]] = {k: tuple(f for f, _ in v["fields"]) for k, v in KINDS.items()}
MACHINE_INT_RANGES = {"i32": (INT4_MIN, INT4_MAX), "i64": (INT8_MIN, INT8_MAX)}
NUMERIC_DSCALE_MAX = 16383  # PostgreSQL NUMERIC_DSCALE_MAX (verus spec::limits)
NUMERIC_INT_DIGITS_MAX = 131072  # PostgreSQL numeric format limit (verus spec::limits)
_CANONICAL_INT_TEXT = re.compile(r"-?(0|[1-9][0-9]*)\Z")


class AstError(ValueError):
    """A structural violation of the AST encoding."""


def sort_of(tag: str) -> str:
    return KINDS[tag]["sort"]


def child_sort(fkind: str) -> str | None:
    """The child sort of a ref:/box:/seq: field kind, else None."""
    head, _, sort = fkind.partition(":")
    return sort if head in ("ref", "box", "seq") else None


class Node:
    """One AST node: a tag, its field values in schema order, and the static-type annotation.

    Fields are attributes (``node.op``, ``node.kind``, ...)."""

    __slots__ = ("tag", "values", "ann")

    def __init__(self, tag: str, ann: Any = None, /, **fields: Any):
        if tag not in KINDS:
            raise AstError(f"unknown node tag {tag!r}")
        names = FIELD_NAMES[tag]
        if set(fields) != set(names):
            raise AstError(f"{tag}: fields {sorted(fields)} != schema {list(names)}")
        for name, fkind in KINDS[tag]["fields"]:
            _check_value(f"{tag}.{name}", fkind, fields[name])
        _check_annotation(tag, ann)
        self.tag = tag
        self.values = tuple(fields[n] for n in names)
        self.ann = ann

    @property
    def sort(self) -> str:
        return sort_of(self.tag)

    def __getattr__(self, name: str) -> Any:
        try:
            return self.values[FIELD_NAMES[object.__getattribute__(self, "tag")].index(name)]
        except ValueError:
            raise AttributeError(name) from None

    def replace(self, **changes: Any) -> "Node":
        fields = dict(zip(FIELD_NAMES[self.tag], self.values))
        ann = changes.pop("ann", self.ann)
        fields.update(changes)
        return Node(self.tag, ann, **fields)

    def children(self) -> Iterator["Node"]:
        for (_, fkind), value in zip(KINDS[self.tag]["fields"], self.values):
            if fkind.startswith("seq:"):
                yield from value
            elif child_sort(fkind):
                yield value

    def map_children(self, f: Callable[["Node"], "Node"]) -> "Node":
        changes = {}
        for (name, fkind), value in zip(KINDS[self.tag]["fields"], self.values):
            if fkind.startswith("seq:"):
                changes[name] = tuple(f(v) for v in value)
            elif child_sort(fkind):
                changes[name] = f(value)
        return self.replace(**changes) if changes else self

    def _key(self):
        return (self.tag, self.values, self.ann)

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Node) and self._key() == other._key()

    def __hash__(self) -> int:
        return hash(self._key())

    def __repr__(self) -> str:
        return render(self)


def _is_int(v: Any) -> bool:
    return isinstance(v, int) and not isinstance(v, bool)


def _check_value(where: str, fkind: str, v: Any) -> None:
    head = fkind.split(":", 1)[0]
    if head in ("ref", "box"):
        ok = isinstance(v, Node) and v.sort == child_sort(fkind)
    elif head == "seq":
        ok = isinstance(v, tuple) and all(isinstance(c, Node) and c.sort == child_sort(fkind) for c in v)
    elif head == "int":
        ok = _is_int(v)
    elif head == "nat":
        ok = _is_int(v) and v >= 0
    elif head == "opt_nat":
        ok = v is None or (_is_int(v) and v >= 0)
    elif head in MACHINE_INT_RANGES:
        lo, hi = MACHINE_INT_RANGES[head]
        ok = _is_int(v) and lo <= v <= hi
    elif head == "bool":
        ok = isinstance(v, bool)
    elif head == "bytes":
        ok = isinstance(v, str) and "\x00" not in v
    elif head == "scalar_ty":
        ok = isinstance(v, ScalarTy)
    elif head == "enum":
        ok = v in ENUMS[fkind[5:]]
    else:
        raise AstError(f"{where}: unknown field kind {fkind!r} in schema")
    if not ok:
        raise AstError(f"{where}: {v!r} is not a valid {fkind}")


def _check_annotation(tag: str, ann: Any) -> None:
    want = ANNOTATIONS.get(sort_of(tag))
    if want is None:
        ok = ann is None
    elif want == "coltype":
        ok = isinstance(ann, ColTy)
    else:
        ok = isinstance(ann, tuple) and all(isinstance(c, ColTy) for c in ann)
    if not ok:
        raise AstError(f"{tag}: annotation {ann!r} is not a {want}")


def check_literal(node: Node) -> None:
    """Literal validity as in the Verus typing (``type_lit``); the rest of typing is Verus-checked."""
    if node.tag == "Int":
        lo, hi = (INT4_MIN, INT4_MAX) if node.kind == "Int4" else (INT8_MIN, INT8_MAX)
        if not lo <= node.v <= hi:
            raise AstError(f"Int {node.v} outside {node.kind}")
    elif node.tag == "Num":
        if node.scale > NUMERIC_DSCALE_MAX or len(str(abs(node.coeff))) - node.scale > NUMERIC_INT_DIGITS_MAX:
            raise AstError(f"Num {node.coeff}e-{node.scale} outside PostgreSQL's numeric format")
    elif node.tag == "Date":
        if not valid_ymd(node.y, node.m, node.d):
            raise AstError(f"Date {node.y}-{node.m}-{node.d} is not a calendar date")


def valid_ymd(y: int, m: int, d: int) -> bool:
    """Proleptic Gregorian calendar validity (a predicate, no date arithmetic)."""
    if not 1 <= m <= 12 or d < 1:
        return False
    leap = y % 4 == 0 and (y % 100 != 0 or y % 400 == 0)
    return d <= [31, 29 if leap else 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31][m - 1]


# ---------------------------------------------------------------------------------------------
# Arena encoding.

def encode_arena(root: Node) -> tuple[list[dict], int]:
    """Post-order arena: children before parents, ids = array positions (iterative)."""
    nodes: list[dict] = []
    stack: list[tuple[Node, bool]] = [(root, False)]
    done: list[int] = []  # ids of finished nodes not yet consumed by their parent
    while stack:
        node, expanded = stack.pop()
        if not expanded:
            stack.append((node, True))
            stack.extend((c, False) for c in reversed(list(node.children())))
            continue
        if node.tag in INTERNAL_KINDS:
            raise AstError(f"internal node {node.tag} cannot be encoded")
        n = sum(1 for _ in node.children())
        ids = iter(done[len(done) - n:])
        del done[len(done) - n:]
        obj: dict[str, Any] = {"id": len(nodes), "tag": node.tag}
        for (name, fkind), value in zip(KINDS[node.tag]["fields"], node.values):
            if fkind.startswith("seq:"):
                obj[name] = [next(ids) for _ in value]
            elif child_sort(fkind):
                obj[name] = next(ids)
            elif fkind.startswith("int:"):
                obj[name] = str(value)
            elif fkind == "scalar_ty":
                obj[name] = value.to_json()
            else:
                obj[name] = value
        ann_key = ANNOTATION_KEYS.get(ANNOTATIONS.get(node.sort))
        if ann_key == "type":
            obj["type"] = node.ann.to_json()
        elif ann_key == "columns":
            obj["columns"] = [c.to_json() for c in node.ann]
        done.append(len(nodes))
        nodes.append(obj)
    return nodes, done[0]


def decode_arena(nodes: Any, root: Any) -> Node:
    """Validate a JSON arena and rebuild the tree (iteratively; no depth limit)."""
    if not isinstance(nodes, list) or not nodes:
        raise AstError("nodes must be a non-empty list")
    built: list[Node] = []
    has_parent = [False] * len(nodes)
    for i, obj in enumerate(nodes):
        built.append(_decode_node(i, obj, built, has_parent))
    if root != len(nodes) - 1:
        raise AstError("root must be the last node")
    if built[root].sort != SCHEMA["root_sort"]:
        raise AstError(f"root is a {built[root].sort}, expected {SCHEMA['root_sort']}")
    orphans = [i for i in range(len(nodes) - 1) if not has_parent[i]]
    if orphans:
        raise AstError(f"nodes {orphans} have no parent")
    return built[root]


def _decode_node(i: int, obj: Any, built: list[Node], has_parent: list[bool]) -> Node:
    """Node ``i`` of an arena whose earlier nodes are ``built``; claims its children in ``has_parent``."""
    if not isinstance(obj, dict) or obj.get("id") != i:
        raise AstError(f"node {i}: id must equal its position")
    tag = obj.get("tag")
    if tag not in SCHEMA["kinds"]:
        raise AstError(f"node {i}: unknown tag {tag!r}")
    ann_key = ANNOTATION_KEYS.get(ANNOTATIONS.get(sort_of(tag)))
    expected = {"id", "tag", *FIELD_NAMES[tag]} | ({ann_key} if ann_key else set())
    if set(obj) != expected:
        raise AstError(f"node {i} ({tag}): keys {sorted(obj)} != {sorted(expected)}")

    def child(ref: Any, sort: str) -> Node:
        if not _is_int(ref) or not 0 <= ref < i:
            raise AstError(f"node {i} ({tag}): child {ref!r} must be an earlier node id")
        if has_parent[ref]:
            raise AstError(f"node {i} ({tag}): node {ref} already has a parent")
        if built[ref].sort != sort:
            raise AstError(f"node {i} ({tag}): child {ref} is a {built[ref].sort}, expected {sort}")
        has_parent[ref] = True
        return built[ref]

    fields: dict[str, Any] = {}
    for name, fkind in KINDS[tag]["fields"]:
        raw = obj[name]
        if fkind.startswith("seq:"):
            if not isinstance(raw, list):
                raise AstError(f"node {i} ({tag}).{name}: expected a list of ids")
            fields[name] = tuple(child(r, child_sort(fkind)) for r in raw)
        elif child_sort(fkind):
            fields[name] = child(raw, child_sort(fkind))
        elif fkind.startswith("int:"):
            if not isinstance(raw, str) or not _CANONICAL_INT_TEXT.match(raw):
                raise AstError(f"node {i} ({tag}).{name}: expected a canonical decimal string")
            fields[name] = int(raw)
        elif fkind == "scalar_ty":
            fields[name] = decode_scalar_ty(raw, f"node {i} ({tag}).{name}")
        else:
            fields[name] = raw
    ann = None
    if ann_key == "type":
        ann = decode_coltype(obj["type"], f"node {i} type")
    elif ann_key == "columns":
        if not isinstance(obj["columns"], list):
            raise AstError(f"node {i}: columns must be a list")
        ann = tuple(decode_coltype(c, f"node {i} columns") for c in obj["columns"])
    try:
        node = Node(tag, ann, **fields)
        if node.sort == "literal":
            check_literal(node)
    except AstError as e:
        raise AstError(f"node {i}: {e}") from None
    return node


def decode_scalar_ty(obj: Any, where: str) -> ScalarTy:
    params = SCHEMA["scalar_types"].get(obj.get("kind")) if isinstance(obj, dict) else None
    if params is None or set(obj) != {"kind", *params}:
        raise AstError(f"{where}: invalid scalar type {obj!r}")
    if params and not (_is_int(obj["scale"]) and 0 <= obj["scale"] <= NUMERIC_DSCALE_MAX):
        raise AstError(f"{where}: invalid numeric scale")
    return ScalarTy(obj["kind"], obj.get("scale"))


def decode_type(obj: Any, where: str) -> SqlType:
    types = SCHEMA["sql_types"]
    if not isinstance(obj, dict) or obj.get("kind") not in types:
        raise AstError(f"{where}: invalid type {obj!r}")
    params = types[obj["kind"]]
    if set(obj) != {"kind", *params}:
        raise AstError(f"{where}: type keys {sorted(obj)}")
    for name, pkind in params.items():
        v = obj[name]
        if pkind == "opt_nat" and not (v is None or (_is_int(v) and v > 0)):
            raise AstError(f"{where}: {name} must be null or a positive integer")
        if pkind == "opt_typmod" and v is not None:
            if (not isinstance(v, dict) or set(v) != {"precision", "scale"} or not _is_int(v["precision"])
                    or not _is_int(v["scale"]) or not 1 <= v["precision"] <= 1000 or not 0 <= v["scale"] <= v["precision"]):
                raise AstError(f"{where}: invalid numeric typmod {v!r}")
    return SqlType.from_json(obj)


def decode_coltype(obj: Any, where: str) -> ColTy:
    if (not isinstance(obj, dict) or not {"type", "nullable", "dscale"} <= set(obj)
            or not set(obj) <= {"type", "nullable", "dscale", "dscale_exact"}):
        raise AstError(f"{where}: invalid column type {obj!r}")
    ty = decode_type(obj["type"], where)
    if not isinstance(obj["nullable"], bool):
        raise AstError(f"{where}: nullable must be a bool")
    dscale = obj["dscale"]
    if (dscale is None) != (ty.kind != "numeric") or (dscale is not None and not (_is_int(dscale) and dscale >= 0)):
        raise AstError(f"{where}: dscale is required for numeric (static scale) and absent otherwise")
    # Canonical: the key is present only as ``false`` on a numeric (absent = exact).
    if "dscale_exact" in obj and (obj["dscale_exact"] is not False or dscale is None):
        raise AstError(f"{where}: dscale_exact is only written as false on a numeric")
    return ColTy(ty, obj["nullable"], dscale, "dscale_exact" not in obj)


def render(node: Node) -> str:
    """Compact S-expression view for reading and diagnostics (not an interchange format)."""
    parts = []
    for (name, fkind), value in zip(KINDS[node.tag]["fields"], node.values):
        if fkind.startswith("seq:"):
            parts.append("[" + " ".join(render(v) for v in value) + "]")
        elif child_sort(fkind):
            parts.append(render(value))
        elif fkind == "scalar_ty":
            parts.append(value.kind if value.scale is None else f"{value.kind}({value.scale})")
        elif fkind == "bool" or fkind.startswith("opt_nat"):
            parts.append(f"{name}={value!r}")
        else:
            parts.append(repr(value) if fkind == "bytes" else str(value))
    return f"({node.tag}{''.join(' ' + p for p in parts)})"
