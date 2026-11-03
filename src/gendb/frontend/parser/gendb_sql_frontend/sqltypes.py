"""SQL types of the fragment and static column types.

``SqlType`` is a PostgreSQL type with its type modifier; ``ColTy`` adds nullability and the statically known numeric
display scale (``dscale``), as in the Verus typing (``ColTy { ty, nullable, dscale }``).  ``sql_type`` reads the
fragment's type names from DDL columns, CAST targets and parameter declarations.
"""

from __future__ import annotations

from dataclasses import dataclass

from sqlglot import exp

from .parse import check_args
from .refusal import Refusal

INT4_MIN, INT4_MAX = -(2**31), 2**31 - 1
INT8_MIN, INT8_MAX = -(2**63), 2**63 - 1
VARLENA_MAX_CHARS = 10485760  # PostgreSQL's limit for char(n) / varchar(n)

# Comparison families: PostgreSQL has exact cross-type comparison operators (or exact implicit casts) inside a
# family and none across families.
FAMILY = {"bool": "bool", "int4": "number", "int8": "number", "numeric": "number",
          "date": "datetime", "timestamp": "datetime",
          "text": "text", "varchar": "text", "bpchar": "text"}


@dataclass(frozen=True)
class SqlType:
    kind: str
    precision: int | None = None  # numeric(p, s)
    scale: int | None = None
    length: int | None = None  # varchar(n) max characters / char(n) width

    def __post_init__(self):
        if self.kind not in FAMILY:
            raise ValueError(f"unknown SQL type kind {self.kind!r}")

    @property
    def family(self) -> str:
        return FAMILY[self.kind]

    @property
    def is_int(self) -> bool:
        return self.kind in ("int4", "int8")

    def to_json(self) -> dict:
        if self.kind == "numeric":
            typmod = None if self.precision is None else {"precision": self.precision, "scale": self.scale}
            return {"kind": "numeric", "typmod": typmod}
        if self.kind == "varchar":
            return {"kind": "varchar", "max_chars": self.length}
        if self.kind == "bpchar":
            return {"kind": "bpchar", "n": self.length}
        return {"kind": self.kind}

    @staticmethod
    def from_json(obj: dict) -> "SqlType":
        kind = obj["kind"]
        if kind == "numeric":
            typmod = obj["typmod"]
            return numeric() if typmod is None else numeric(typmod["precision"], typmod["scale"])
        if kind == "varchar":
            return SqlType("varchar", length=obj["max_chars"])
        if kind == "bpchar":
            return SqlType("bpchar", length=obj["n"])
        return SqlType(kind)

    def pg_name(self) -> str:
        """The name PostgreSQL's ``format_type`` (and ``\\gdesc``) prints."""
        if self.kind == "numeric":
            return "numeric" if self.precision is None else f"numeric({self.precision},{self.scale})"
        if self.kind == "varchar":
            return "character varying" if self.length is None else f"character varying({self.length})"
        if self.kind == "bpchar":
            return "bpchar" if self.length is None else f"character({self.length})"
        return {"bool": "boolean", "int4": "integer", "int8": "bigint", "date": "date",
                "timestamp": "timestamp without time zone", "text": "text"}[self.kind]


BOOL, INT4, INT8, DATE, TIMESTAMP, TEXT = (SqlType(k) for k in ("bool", "int4", "int8", "date", "timestamp", "text"))


def numeric(precision: int | None = None, scale: int | None = None) -> SqlType:
    return SqlType("numeric", precision, scale)


@dataclass(frozen=True)
class ScalarTy:
    """The Verus AST's static value type (``spec::types::ScalarTy``): text, varchar and char are one comparison
    family ``Text``; numeric carries an upper bound on the display scale of its values (exact for columns, literals
    and the core operators; division and AVG results get the bound 1000 with a value-dependent actual scale)."""
    kind: str  # Bool | Int4 | Int8 | Numeric | Date | Timestamp | Text
    scale: int | None = None

    def to_json(self) -> dict:
        return {"kind": self.kind, "scale": self.scale} if self.kind == "Numeric" else {"kind": self.kind}


@dataclass(frozen=True)
class ColTy:
    ty: SqlType
    nullable: bool
    # Numeric display scale: the Verus ``ScalarTy::Numeric { scale }``, an upper bound on every value's dscale.
    # ``dscale_exact`` (PostgreSQL-level annotation only, not part of the Verus AST) says whether every value has
    # exactly that scale (columns, literals and the core operators on exact inputs) or a value-dependent one
    # (division, AVG, CASE of different scales). Encoded as ``"dscale_exact": false`` only when not exact.
    dscale: int | None = None
    dscale_exact: bool = True

    def to_json(self) -> dict:
        out = {"type": self.ty.to_json(), "nullable": self.nullable, "dscale": self.dscale}
        if not self.dscale_exact:
            out["dscale_exact"] = False
        return out

    @staticmethod
    def from_json(obj: dict) -> "ColTy":
        return ColTy(SqlType.from_json(obj["type"]), obj["nullable"], obj["dscale"], obj.get("dscale_exact", True))

    def with_nullable(self, nullable: bool) -> "ColTy":
        return ColTy(self.ty, nullable, self.dscale, self.dscale_exact)

    def scalar(self) -> ScalarTy:
        """Projection onto the Verus AST's ``ScalarTy``."""
        if self.ty.kind == "numeric":
            return ScalarTy("Numeric", self.dscale)
        return ScalarTy({"bool": "Bool", "int4": "Int4", "int8": "Int8", "date": "Date",
                         "timestamp": "Timestamp"}.get(self.ty.kind, "Text"))


def numeric_bound(nullable: bool, scale: int = 1000) -> ColTy:
    """An unconstrained ``numeric`` whose values have a value-dependent display scale ``<= scale`` (division and
    AVG results: PostgreSQL's ``select_div_scale`` is at most ``NUMERIC_MAX_DISPLAY_SCALE`` = 1000)."""
    return ColTy(numeric(), nullable, scale, dscale_exact=False)


def column_type(ty: SqlType, nullable: bool) -> ColTy:
    """The static type of a stored column: numeric(p, s) has static scale s."""
    return ColTy(ty, nullable, ty.scale if ty.kind == "numeric" else None)


def sql_type(dt: exp.DataType, where: str) -> SqlType:
    """A sqlglot type (DDL column, CAST target or parameter declaration) as a fragment type."""
    T = exp.DataType.Type
    t = dt.this
    nparams = len(dt.expressions)
    check_args(dt, {"this", "expressions", "nested"}, where)
    if t in (T.INT, T.BIGINT, T.BOOLEAN, T.DATE, T.TIMESTAMP, T.TEXT) and nparams == 0:
        return {T.INT: INT4, T.BIGINT: INT8, T.BOOLEAN: BOOL, T.DATE: DATE, T.TIMESTAMP: TIMESTAMP, T.TEXT: TEXT}[t]
    if t == T.DECIMAL and 1 <= nparams <= 2:  # unconstrained numeric has no static scale
        precision = _type_parameter(dt, 0)
        scale = _type_parameter(dt, 1) if nparams == 2 else 0
        if not 1 <= precision <= 1000 or scale > precision:
            raise Refusal("unsupported_type", f"numeric({precision},{scale}) (supported: 1 <= p <= 1000, 0 <= s <= p)", where)
        return numeric(precision, scale)
    if (t == T.CHAR and nparams <= 1) or (t == T.VARCHAR and nparams == 1):
        n = _type_parameter(dt, 0) if nparams == 1 else 1  # char = char(1)
        if not 1 <= n <= VARLENA_MAX_CHARS:
            raise Refusal("unsupported_type", f"length {n} outside 1..{VARLENA_MAX_CHARS}", where)
        return SqlType("bpchar" if t == T.CHAR else "varchar", length=n)
    raise Refusal("unsupported_type", f"type {dt.sql('postgres')}", where, dt.sql("postgres"))


def _type_parameter(dt: exp.DataType, i: int) -> int:
    p = dt.expressions[i]
    lit = p.this if isinstance(p, exp.DataTypeParam) else p
    if not (isinstance(lit, exp.Literal) and not lit.is_string and lit.this.isdigit()):
        raise Refusal("unsupported_type", f"type parameter {p.sql('postgres')!r} is not an integer", "schema")
    return int(lit.this)
