//! Integrity constraints (`spec::types::Constraint`) as verified hypotheses of the evaluator's theorems.
//!
//! - `constraints_wf(schema)`: which declarations are well-formed (part of `schema_wf`). Recursive over finite
//!   sequences (no quantifier), so `by (compute)` decides it for an emitted schema.
//! - `constraints_hold(db)`: the instance predicate every committed database must satisfy (PRIMARY KEY, UNIQUE,
//!   FOREIGN KEY MATCH SIMPLE / FULL, CHECK). NOT NULL is the column-domain rule of `db_wf`
//!   (`spec::typing::value_in_column`), and a primary key's columns must be declared NOT NULL.
//!
//! The checked entry point (`exec::relational::entry::evaluate`) decides both with verified code
//! (`exec::relational::constraints`); its executable domain `fits_constraints` (CHECK evaluation) is defined there
//! (`fits_pred` is in `exec::relational::domain`), because it is an exec notion. Nothing here depends on `exec` or `bridge`.
//!
//! Meaning of the instance predicate (PostgreSQL 18 probe):
//! - Key (PRIMARY KEY / UNIQUE): no two rows (positions `i < j`) have not-distinct key tuples
//!   (`spec::equality::row_not_distinct`: SQL value equality, numerics by value). With `nulls_distinct` (the SQL
//!   default) a key tuple containing NULL never collides; `UNIQUE NULLS NOT DISTINCT` compares NULL as equal to
//!   NULL. A primary key additionally has no NULL cell (also implied by its NOT NULL columns).
//! - ForeignKey: a referencing tuple with no NULL cell must equal (`compare == Some(0)` column by column, in the
//!   declared column mapping) the referenced columns of some row of the referenced table (the row itself for a
//!   self reference). MATCH SIMPLE exempts every tuple with a NULL cell; MATCH FULL exempts only the all-NULL
//!   tuple and rejects a partly NULL one. A referenced NULL never matches.
//! - Check(p): for every row, `p` evaluated with the row as its environment (the semantics' `eval_pred`) is `True`
//!   or `Unknown`; `False` and a SQL error are violations.
//!   Deviation (strict AND/OR, design D1, extended to CHECK validity): `eval_pred` evaluates both operands of
//!   `AND`/`OR` and returns the first error, while PostgreSQL may skip an operand. So a row PostgreSQL stores can
//!   violate the semantics' CHECK: `CHECK (b = 0 OR a / b > 1)` with row `(5, 0)` is stored by PostgreSQL 18.3 but
//!   gives 22012 here, hence `ConstraintViolation`. `ConstraintViolation` therefore means "violates this CHECK
//!   meaning", not "PostgreSQL would reject the row". A lazy `CASE` form of the same condition agrees. The
//!   direction is a refusal only: `Done` still implies the constraints hold.
//! Referential actions (ON DELETE / ON UPDATE) and DEFERRABLE / INITIALLY DEFERRED only change when PostgreSQL
//! checks a modification; a committed database satisfies the same instance predicate, so they are frontend metadata
//! only (recorded in the AST document, never silently dropped).
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::scalar::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::typing::*;
use crate::spec::equality::*;

verus! {

// ------------------------------------------------------------------ declared-schema well-formedness

/// `x` occurs in `s`.
pub open spec fn nat_in(s: Seq<nat>, x: nat) -> bool
    decreases s.len(),
{
    s.len() > 0 && (s.last() == x || nat_in(s.drop_last(), x))
}

/// Every column position is `< n`.
pub open spec fn cols_in_range(cols: Seq<nat>, n: nat) -> bool
    decreases cols.len(),
{
    cols.len() == 0 || (cols.last() < n && cols_in_range(cols.drop_last(), n))
}

/// No column position repeats (PostgreSQL 42701 for a key; a referenced column list must match a key).
pub open spec fn cols_distinct(cols: Seq<nat>) -> bool
    decreases cols.len(),
{
    cols.len() == 0 || (!nat_in(cols.drop_last(), cols.last()) && cols_distinct(cols.drop_last()))
}

/// Every column of `cols` is declared NOT NULL.
pub open spec fn cols_not_null(cols: Seq<nat>, columns: Seq<Column>) -> bool
    decreases cols.len(),
{
    cols.len() == 0 || (cols.last() < columns.len() && !columns[cols.last() as int].nullable
        && cols_not_null(cols.drop_last(), columns))
}

/// Every position of `a` occurs in `b`.
pub open spec fn cols_subset(a: Seq<nat>, b: Seq<nat>) -> bool
    decreases a.len(),
{
    a.len() == 0 || (nat_in(b, a.last()) && cols_subset(a.drop_last(), b))
}

/// Some Key (PRIMARY KEY or UNIQUE, either NULLS mode) of `cs` is declared on exactly the column set of the
/// repetition-free list `ref_cols`, in any order (PostgreSQL `transformFkeyCheckAttrs`; 42830 otherwise).
pub open spec fn has_key_on(cs: Seq<Constraint>, ref_cols: Seq<nat>) -> bool
    decreases cs.len(),
{
    cs.len() > 0 && (match cs.last() {
        Constraint::Key { cols, .. } => cols.len() == ref_cols.len() && cols_subset(cols, ref_cols),
        _ => false,
    } || has_key_on(cs.drop_last(), ref_cols))
}

/// Number of primary keys declared in `cs` (PostgreSQL 42P16 for more than one).
pub open spec fn primary_keys(cs: Seq<Constraint>) -> nat
    decreases cs.len(),
{
    if cs.len() == 0 {
        0
    } else {
        primary_keys(cs.drop_last()) + match cs.last() {
            Constraint::Key { primary, .. } => if primary { 1nat } else { 0nat },
            _ => 0nat,
        }
    }
}

/// Column type pairs (referencing, referenced) of a foreign key whose PostgreSQL equality is exactly
/// `compare == Some(0)` on this fragment's values (PostgreSQL 18.3 probe):
/// - int4/int8 -> int4/int8/numeric and numeric -> numeric: exact value equality (numeric -> int4/int8 is
///   rejected by PostgreSQL, 42804);
/// - date/timestamp -> date/timestamp: exact, dates at midnight;
/// - text/varchar -> text/varchar: bytes; char(n) -> text/varchar/char(m): the referencing value is cast with
///   PostgreSQL's rtrim, which is exactly the canonical stored char(n) value, so bytes again;
/// - bool -> bool.
/// Refused: every cross-family pair (PostgreSQL 42804) and text/varchar -> char(n), where PostgreSQL compares
/// blank-insensitively (`'ab '` references `'ab'`), which byte equality would misjudge.
pub open spec fn fk_col_types_ok(c: SqlType, p: SqlType) -> bool {
    match c {
        SqlType::Bool => p is Bool,
        SqlType::Int4 | SqlType::Int8 => p is Int4 || p is Int8 || p is Numeric,
        SqlType::Numeric { .. } => p is Numeric,
        SqlType::Date | SqlType::Timestamp => p is Date || p is Timestamp,
        SqlType::Text | SqlType::Varchar { .. } => p is Text || p is Varchar,
        SqlType::Bpchar { .. } => p is Text || p is Varchar || p is Bpchar,
    }
}

/// Pairwise column types of a foreign key (lists of equal length; positions in range).
pub open spec fn fk_types_ok(child: Seq<Column>, cols: Seq<nat>, parent: Seq<Column>, ref_cols: Seq<nat>) -> bool
    decreases cols.len(),
{
    if cols.len() == 0 || ref_cols.len() == 0 {
        true
    } else {
        cols.last() < child.len() && ref_cols.last() < parent.len()
            && fk_col_types_ok(child[cols.last() as int].ty, parent[ref_cols.last() as int].ty)
            && fk_types_ok(child, cols.drop_last(), parent, ref_cols.drop_last())
    }
}

/// One declared constraint of table `t` in `schema`.
/// - Key: at least one column, positions in range and not repeated; a primary key's columns are NOT NULL.
/// - ForeignKey: an existing referenced table; one or more referencing columns (they may repeat, as PostgreSQL
///   accepts), in range; referenced columns in range, not repeated, exactly the column set of a Key of the
///   referenced table; equal arity and supported type pairs (`fk_col_types_ok`).
/// - Check(p): `p` is typed over the table's row with **no table in scope** (the empty schema). Every query
///   bottoms out in a `Table` leaf, which is ill-typed there, so a well-formed CHECK contains no subquery
///   (`Subquery`, `Exists`, `AnyCmp`; PostgreSQL 0A000) and reads only its row. Aggregates are not predicates or
///   expressions, so they cannot occur (PostgreSQL 42803). Every scalar function of the fragment is immutable.
pub open spec fn constraint_wf(schema: Schema, t: TableSchema, c: Constraint) -> bool {
    match c {
        Constraint::Key { cols, primary, nulls_distinct } =>
            cols.len() > 0 && cols_in_range(cols, t.columns.len()) && cols_distinct(cols)
                && (primary ==> cols_not_null(cols, t.columns)),
        Constraint::ForeignKey { cols, table, ref_cols, match_full } =>
            table < schema.len() && cols.len() > 0 && cols.len() == ref_cols.len()
                && cols_in_range(cols, t.columns.len())
                && cols_in_range(ref_cols, schema[table as int].columns.len()) && cols_distinct(ref_cols)
                && has_key_on(schema[table as int].constraints, ref_cols)
                && fk_types_ok(t.columns, cols, schema[table as int].columns, ref_cols),
        Constraint::Check(p) => type_pred(Seq::empty(), table_tys(t), p),
    }
}

/// Every constraint of `cs` (declared on table `t`) is well-formed.
pub open spec fn table_constraints_wf(schema: Schema, t: TableSchema, cs: Seq<Constraint>) -> bool
    decreases cs.len(),
{
    cs.len() == 0 || (constraint_wf(schema, t, cs.last()) && table_constraints_wf(schema, t, cs.drop_last()))
}

/// Every table of `ts` has well-formed constraints and at most one primary key (`schema` resolves references).
pub open spec fn tables_constraints_wf(schema: Schema, ts: Seq<TableSchema>) -> bool
    decreases ts.len(),
{
    ts.len() == 0 || (table_constraints_wf(schema, ts.last(), ts.last().constraints)
        && primary_keys(ts.last().constraints) <= 1 && tables_constraints_wf(schema, ts.drop_last()))
}

/// Well-formed declared constraints of a schema (part of `spec::types::schema_wf`). Not circular: CHECK typing
/// (`type_pred`) never consults `schema_wf` or `constraints_wf`.
pub open spec fn constraints_wf(schema: Schema) -> bool {
    tables_constraints_wf(schema, schema)
}

// ------------------------------------------------------------------ instance predicate

/// The key tuple of row `r` on columns `cols` (in the listed order).
pub open spec fn key_of(r: Row, cols: Seq<nat>) -> Row {
    cols.map_values(|c: nat| r[c as int])
}

pub open spec fn has_null(k: Row) -> bool {
    exists|i: int| 0 <= i < k.len() && (#[trigger] k[i]) is Null
}

pub open spec fn all_null(k: Row) -> bool {
    forall|i: int| 0 <= i < k.len() ==> (#[trigger] k[i]) is Null
}

/// Rows `r` and `s` collide on a key: not-distinct key tuples, except that with `nulls_distinct` a tuple with a
/// NULL cell collides with nothing.
pub open spec fn key_collides(r: Row, s: Row, cols: Seq<nat>, nulls_distinct: bool) -> bool {
    row_not_distinct(key_of(r, cols), key_of(s, cols)) && !(nulls_distinct && has_null(key_of(r, cols)))
}

/// PRIMARY KEY / UNIQUE on `rows`.
pub open spec fn key_holds(rows: Relation, cols: Seq<nat>, primary: bool, nulls_distinct: bool) -> bool {
    &&& primary ==> forall|i: int| 0 <= i < rows.len() ==> !has_null(key_of(#[trigger] rows[i], cols))
    &&& forall|i: int, j: int| 0 <= i < j < rows.len() ==> !key_collides(#[trigger] rows[i], #[trigger] rows[j], cols, nulls_distinct)
}

/// A referencing tuple equals a referenced tuple (SQL `=` on every column pair; NULL never matches).
pub open spec fn key_matches(k: Row, m: Row) -> bool {
    k.len() == m.len() && forall|i: int| 0 <= i < k.len() ==> compare(#[trigger] k[i], m[i]) == Some(0int)
}

/// One referencing row of a foreign key (MATCH SIMPLE unless `match_full`).
pub open spec fn fk_row_holds(r: Row, cols: Seq<nat>, target: Relation, ref_cols: Seq<nat>, match_full: bool) -> bool {
    let k = key_of(r, cols);
    if has_null(k) {
        !match_full || all_null(k)
    } else {
        exists|j: int| 0 <= j < target.len() && key_matches(k, key_of(#[trigger] target[j], ref_cols))
    }
}

pub open spec fn fk_holds(rows: Relation, cols: Seq<nat>, target: Relation, ref_cols: Seq<nat>, match_full: bool) -> bool {
    forall|i: int| 0 <= i < rows.len() ==> fk_row_holds(#[trigger] rows[i], cols, target, ref_cols, match_full)
}

/// CHECK accepts `True` and `Unknown`; `False` and any SQL error reject the row.
pub open spec fn check_row_holds(db: Database, r: Row, p: Pred) -> bool {
    match eval_pred(db, r, p) {
        Ok(Truth::False) => false,
        Ok(_) => true,
        Err(_) => false,
    }
}

pub open spec fn check_holds(db: Database, rows: Relation, p: Pred) -> bool {
    forall|i: int| 0 <= i < rows.len() ==> check_row_holds(db, #[trigger] rows[i], p)
}

/// Constraint `c` of table `t` holds on `db`.
pub open spec fn constraint_holds(db: Database, t: int, c: Constraint) -> bool {
    match c {
        Constraint::Key { cols, primary, nulls_distinct } => key_holds(db.tables[t], cols, primary, nulls_distinct),
        Constraint::ForeignKey { cols, table, ref_cols, match_full } =>
            table < db.tables.len() && fk_holds(db.tables[t], cols, db.tables[table as int], ref_cols, match_full),
        Constraint::Check(p) => check_holds(db, db.tables[t], p),
    }
}

/// Every declared constraint of every table holds.
pub open spec fn constraints_hold(db: Database) -> bool {
    forall|t: int, k: int| 0 <= t < db.schema.len() && t < db.tables.len() && 0 <= k < db.schema[t].constraints.len()
        ==> constraint_holds(db, t, #[trigger] db.schema[t].constraints[k])
}

} // verus!
