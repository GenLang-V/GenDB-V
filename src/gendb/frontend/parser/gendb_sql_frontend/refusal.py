"""Named refusals: the only way the frontend declines a query.

Every refusal carries a reason from ``REASONS`` (a stable name plus a one-line meaning), a detail sentence, the clause
path where it arose and the offending SQL fragment.  Refusals cover both SQL the fragment does not support and SQL
that PostgreSQL itself rejects (unknown names, type errors): in both cases no AST is produced, so nothing
unsupported reaches compilation.  Nothing is ever defaulted to NULL or silently dropped.

``REASONS`` is the one catalog of reason names.  The reason name is the stable, machine-read code; the meaning is a
short human-facing description.  Both appear in refusal documents, but only the reason is part of the frontend's
translation contract: correcting a meaning's wording does not change what any query translates to, so it does not
move the frontend identity (``api.IDENTITY``).

The Rust host refuses two more reasons after parsing (``gendb_frontend::constants``, which holds their meanings):
``constant_expression_error`` (a literal-only constant subexpression whose SQLSpec evaluation raises an SQL error,
which PostgreSQL raises while planning) and ``constant_expression_capacity`` (its evaluation leaves the machine domain
of SQLSpec's executable interpreter).
"""

from __future__ import annotations

REASONS: dict[str, str] = {
    # Input and toolchain.
    "toolchain_mismatch": "the interpreter or sqlglot version differs from the parser's toolchain.json",
    "unsupported_dialect": "only the explicit dialect 'postgres' is supported",
    "parse_error": "sqlglot could not parse the text",
    "multiple_statements": "exactly one statement is required",
    "not_select": "the statement is not a SELECT query",
    "view_script": "a multi-statement text other than CREATE VIEW v AS q; SELECT ...; DROP VIEW v;",
    "frontend_resource_limit": "the parser or resolver exceeded the Python recursion limit (engineering limit, not a semantic cap)",
    # Schema DDL (schema.py).
    "invalid_schema": "the schema DDL is not a list of CREATE TABLE statements with named, typed columns",
    "duplicate_table": "the schema defines a table twice",
    "duplicate_column": "a table defines a column twice",
    "unsupported_type": "a type outside bool/int4/int8/numeric(p,s)/date/timestamp/text/varchar(n)/char(n)",
    "unsupported_constraint": "a column or table constraint other than NOT NULL, NULL, PRIMARY KEY, UNIQUE, FOREIGN KEY / REFERENCES or CHECK (e.g. DEFAULT, COLLATE, GENERATED, EXCLUDE)",
    # Integrity constraints (features/constraints.py).
    "fk_match_partial": "FOREIGN KEY ... MATCH PARTIAL (PostgreSQL 0A000: not implemented)",
    "constraint_not_enforced": "a NOT ENFORCED constraint (its instance predicate need not hold, so it is no proof hypothesis)",
    "constraint_option": "a constraint option outside the supported DEFERRABLE / INITIALLY / MATCH / ON DELETE / ON UPDATE forms (e.g. index parameters, USING INDEX, INCLUDE)",
    "fk_unknown_table": "a FOREIGN KEY names a table that is not defined before it (PostgreSQL 42P01)",
    "fk_no_matching_key": "the referenced columns are not exactly the columns of a PRIMARY KEY or UNIQUE constraint of the referenced table (PostgreSQL 42830 / 42704)",
    "fk_deferrable_key": "the only PRIMARY KEY or UNIQUE constraint of the referenced table on the referenced columns is DEFERRABLE (PostgreSQL 55000)",
    "fk_arity": "the referencing and referenced column lists differ in length (PostgreSQL 42830)",
    "fk_type_mismatch": "a FOREIGN KEY column pair PostgreSQL cannot compare (another comparison family, or numeric referencing an integer; PostgreSQL 42804)",
    "fk_bpchar_coercion": "a text/varchar column referencing a char(n) column: PostgreSQL compares it blank-insensitively as bpchar, which the semantics' value equality does not represent",
    "duplicate_key_column": "a column listed twice in a PRIMARY KEY or UNIQUE constraint (PostgreSQL 42701)",
    "multiple_primary_keys": "more than one PRIMARY KEY for a table (PostgreSQL 42P16)",
    "check_subquery": "a subquery (EXISTS, IN, scalar) inside a CHECK constraint (PostgreSQL 0A000)",
    "constraint_not_valid": "ALTER TABLE ... ADD ... NOT VALID (PostgreSQL does not check existing rows, so it is no proof hypothesis)",
    "alter_primary_key_nullable_column": "ALTER TABLE ... ADD PRIMARY KEY over a nullable column (PostgreSQL would make the column NOT NULL, changing the column schema)",
    # Statement parameters (features/params.py).
    "invalid_parameter_declaration": "the parameter declaration is not a list of {index >= 1, type} with distinct indices",
    "unsupported_parameter_type": "a parameter type outside integer, bigint, numeric(p, s) with p <= 38, date, text",
    "undeclared_parameter": "a placeholder $n without a declaration",
    "unused_parameter": "a declared parameter that the statement does not use",
    "parameter_position": "a placeholder where the AST needs a constant (LIMIT / OFFSET)",
    # Syntax outside the fragment.
    "unsupported_syntax": "a SQL construct outside the supported fragment",
    "join_without_condition": "JOIN without ON (PostgreSQL rejects it; sqlglot would read it as a comma join)",
    "using_or_natural_join": "JOIN USING or NATURAL JOIN (not supported)",
    "full_or_right_join": "a RIGHT or FULL join (not supported)",
    "lateral": "LATERAL is not supported",
    "set_operation": "a UNION, INTERSECT or EXCEPT set operation (not supported)",
    "recursive_cte": "WITH RECURSIVE is not supported",
    "distinct_on": "SELECT DISTINCT ON (...) is not supported",
    "subquery_order_or_limit": "ORDER BY / LIMIT / OFFSET inside a subquery",
    "hidden_order_key": "an ORDER BY key that is not an output column",
    "non_literal_limit": "LIMIT / OFFSET must be non-negative integer literals",
    "row_subquery": "a row-valued comparison with a subquery ((a, b) IN (SELECT ...))",
    "quantified_array": "ANY / SOME / ALL over an array rather than a subquery",
    "boolean_value": "a condition used as a value (e.g. in the select list), which is not supported",
    "exists_select_list": "an aggregated EXISTS subquery whose select list can raise an error (evaluated by PostgreSQL for a plan-dependent row)",
    # Functions, operators, casts and literals outside the fragment.
    "unsupported_aggregate": "an unsupported aggregate function or aggregate call form",
    "unsupported_function": "a function call outside the fragment",
    "unsupported_operator": "an unsupported operator",
    "unsupported_cast": "a cast that is not an exact, supported conversion",
    "unsupported_literal": "a literal form outside the fragment (e.g. exponent notation, non-ISO dates)",
    "invalid_literal": "a literal that PostgreSQL rejects (e.g. an impossible date)",
    "unsupported_interval": "an interval that is not an integer number of years, months or days used with + or -",
    "interval_negation_range": "date/timestamp - INTERVAL whose negated field is outside int32 (PostgreSQL raises 22008 when it evaluates a row)",
    "unsupported_extract_field": "an EXTRACT field other than YEAR, MONTH or DAY",
    "substring_regex": "SUBSTRING with a text pattern (the regular-expression / SIMILAR form)",
    "numeric_scale_limit": "a numeric scale above PostgreSQL's display-scale limit 16383",
    # Blank-insensitive char(n) comparisons the core cannot represent (it has no rtrim cast).
    "bpchar_varchar_comparison": "char(n) compared with varchar: PostgreSQL uses the blank-insensitive bpchar operator, and the core has no rtrim cast",
    "in_list_bpchar_coercion": "an IN list whose PostgreSQL common type is bpchar has a text/varchar item (coerced blank-insensitively; the core has no rtrim cast)",
    "case_bpchar_coercion": "a CASE / COALESCE whose common type is bpchar has a text/varchar result (coerced blank-insensitively; the core has no rtrim cast)",
    "like_bpchar_without_length": "LIKE on a char value without a declared length (PostgreSQL pads to the typmod)",
    # PostgreSQL resolution errors (PostgreSQL rejects these queries).
    "unknown_table": "a FROM item or qualifier names no visible table",
    "unknown_column": "a column name resolves to no visible column",
    "ambiguous_column": "a column name resolves to more than one column at the innermost level that has it",
    "duplicate_alias": "a FROM clause uses the same name twice",
    "duplicate_cte": "a WITH query name is specified more than once in one WITH clause",
    "cte_columns": "a WITH query has more column aliases than columns",
    "subquery_columns": "a scalar or IN / ANY / ALL subquery must return exactly one column (PostgreSQL rejects it)",
    "type_mismatch": "operand types have no PostgreSQL operator or coercion in the fragment",
    "ungrouped_column": "a column is used outside an aggregate but is not a GROUP BY key",
    "aggregate_misplaced": "an aggregate in WHERE, ON, GROUP BY or inside another aggregate",
    "outer_level_aggregate": "an aggregate whose arguments reference only outer queries",
    "invalid_ordinal": "a GROUP BY / ORDER BY position outside the select list",
    "ambiguous_order_key": "an ORDER BY name that matches several output columns",
}


class Refusal(Exception):
    """A named refusal with a clause path and the offending SQL fragment."""

    def __init__(self, reason: str, detail: str, path: str = "", sql: str = ""):
        if reason not in REASONS:
            raise ValueError(f"unregistered refusal reason {reason!r}")
        super().__init__(f"{reason}: {detail}")
        self.reason = reason
        self.detail = detail
        self.path = path
        self.sql = sql

    def to_json(self) -> dict:
        return {"reason": self.reason, "meaning": REASONS[self.reason], "detail": self.detail,
                "path": self.path, "sql": self.sql}
