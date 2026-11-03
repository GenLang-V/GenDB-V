"""GenDB SQL frontend: PostgreSQL SQL + schema -> resolved typed SQL AST (``gendb-sql-ast-v1``).

Pipeline: parse (pinned sqlglot, ``parse.py``) -> schema (DDL, ``schema.py``) -> scope/bind (names, PostgreSQL types
and casts; ``scope.py``, ``bind.py``, ``values.py``, ``features/``) -> lower (relational constructors, ``lower.py``)
-> ast (arena JSON, ``ast.py``).  Anything outside the fragment is a named refusal (``refusal.REASONS``).  The
toolchain pin and deployment policy are in ``toolchain.py``.
"""

from .api import IDENTITY, document, dumps, load_document, translate
from .refusal import REASONS, Refusal

__all__ = ["IDENTITY", "REASONS", "Refusal", "document", "dumps", "load_document", "translate"]
