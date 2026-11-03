//! Integrity constraints as proof hypotheses. `exec::relational::entry::evaluate` returns `Done` only when the
//! verified checker established `constraints_hold(db)` (and `db_wf(db)`), so a theorem about a `Done` result may
//! use these consequences of one declared constraint, with no trusted assumption about the data:
//! - a primary key identifies its row (`lemma_primary_key_identifies`);
//! - a UNIQUE key has no two rows with not-distinct key tuples, except NULL-containing ones under NULLS DISTINCT
//!   (`lemma_unique_key`);
//! - a referencing tuple without NULL has a referenced row with equal values (`lemma_foreign_key_target`), and
//!   under MATCH FULL a tuple with a NULL is all NULL (`lemma_foreign_key_full`);
//! - a CHECK is `True` or `Unknown` on every row (`lemma_check_row`).
//! Each lemma first instantiates the constraint (`lemma_constraint_at`), then reads its definition in
//! `spec::constraints`.
use vstd::prelude::*;
use crate::spec::types::*;
use crate::spec::value::*;
use crate::spec::ast::*;
use crate::spec::eval::*;
use crate::spec::equality::*;
use crate::spec::constraints::*;
use crate::bridge::equality::*;

verus! {

/// Constraint `k` of table `t` of a database satisfying its constraints holds.
pub proof fn lemma_constraint_at(db: Database, t: int, k: int)
    requires
        constraints_hold(db), 0 <= t < db.schema.len(), t < db.tables.len(), 0 <= k < db.schema[t].constraints.len(),
    ensures constraint_holds(db, t, db.schema[t].constraints[k]),
{
}

/// Not-distinct key tuples have NULLs in the same positions, so one has a NULL iff the other has.
pub proof fn lemma_not_distinct_has_null(a: Row, b: Row)
    requires row_not_distinct(a, b),
    ensures has_null(a) == has_null(b),
{
    if has_null(a) {
        let i = choose|i: int| 0 <= i < a.len() && (#[trigger] a[i]) is Null;
        assert(val_not_distinct(a[i], b[i]));
        assert(b[i] is Null);
    }
    if has_null(b) {
        let i = choose|i: int| 0 <= i < b.len() && (#[trigger] b[i]) is Null;
        assert(val_not_distinct(a[i], b[i]));
        assert(a[i] is Null);
    }
}

/// Two different rows of a table have distinct key tuples on a declared PRIMARY KEY or UNIQUE key, unless the
/// key is NULLS DISTINCT and the tuple has a NULL cell.
pub proof fn lemma_unique_key(db: Database, t: int, k: int, cols: Seq<nat>, primary: bool, nulls_distinct: bool,
    i: int, j: int)
    requires
        constraints_hold(db), 0 <= t < db.schema.len(), t < db.tables.len(), 0 <= k < db.schema[t].constraints.len(),
        db.schema[t].constraints[k] == (Constraint::Key { cols, primary, nulls_distinct }),
        0 <= i < db.tables[t].len(), 0 <= j < db.tables[t].len(), i != j,
        !(nulls_distinct && has_null(key_of(db.tables[t][i], cols))),
    ensures !row_not_distinct(key_of(db.tables[t][i], cols), key_of(db.tables[t][j], cols)),
{
    lemma_constraint_at(db, t, k);
    let rows = db.tables[t];
    let (ki, kj) = (key_of(rows[i], cols), key_of(rows[j], cols));
    if row_not_distinct(ki, kj) {
        if i < j {
            assert(!key_collides(rows[i], rows[j], cols, nulls_distinct));
        } else {
            lemma_row_not_distinct_symm(ki, kj);
            lemma_not_distinct_has_null(ki, kj);
            assert(!key_collides(rows[j], rows[i], cols, nulls_distinct));
        }
    }
}

/// A declared PRIMARY KEY identifies its row: its tuple has no NULL, and equal (not-distinct) tuples are the
/// same row position.
pub proof fn lemma_primary_key_identifies(db: Database, t: int, k: int, cols: Seq<nat>, nulls_distinct: bool,
    i: int, j: int)
    requires
        constraints_hold(db), 0 <= t < db.schema.len(), t < db.tables.len(), 0 <= k < db.schema[t].constraints.len(),
        db.schema[t].constraints[k] == (Constraint::Key { cols, primary: true, nulls_distinct }),
        0 <= i < db.tables[t].len(), 0 <= j < db.tables[t].len(),
        row_not_distinct(key_of(db.tables[t][i], cols), key_of(db.tables[t][j], cols)),
    ensures i == j, !has_null(key_of(db.tables[t][i], cols)),
{
    lemma_constraint_at(db, t, k);
    assert(!has_null(key_of(db.tables[t][i], cols)));
    if i != j {
        lemma_unique_key(db, t, k, cols, true, nulls_distinct, i, j);
    }
}

/// A referencing tuple without NULL cells equals the referenced columns of some row of the referenced table.
pub proof fn lemma_foreign_key_target(db: Database, t: int, k: int, cols: Seq<nat>, table: nat, ref_cols: Seq<nat>,
    match_full: bool, i: int)
    requires
        constraints_hold(db), 0 <= t < db.schema.len(), t < db.tables.len(), 0 <= k < db.schema[t].constraints.len(),
        db.schema[t].constraints[k] == (Constraint::ForeignKey { cols, table, ref_cols, match_full }),
        0 <= i < db.tables[t].len(), !has_null(key_of(db.tables[t][i], cols)),
    ensures
        table < db.tables.len(),
        exists|j: int| 0 <= j < db.tables[table as int].len()
            && key_matches(key_of(db.tables[t][i], cols), key_of(#[trigger] db.tables[table as int][j], ref_cols)),
{
    lemma_constraint_at(db, t, k);
    assert(fk_row_holds(db.tables[t][i], cols, db.tables[table as int], ref_cols, match_full));
}

/// MATCH FULL: a referencing tuple with a NULL cell is entirely NULL.
pub proof fn lemma_foreign_key_full(db: Database, t: int, k: int, cols: Seq<nat>, table: nat, ref_cols: Seq<nat>, i: int)
    requires
        constraints_hold(db), 0 <= t < db.schema.len(), t < db.tables.len(), 0 <= k < db.schema[t].constraints.len(),
        db.schema[t].constraints[k] == (Constraint::ForeignKey { cols, table, ref_cols, match_full: true }),
        0 <= i < db.tables[t].len(), has_null(key_of(db.tables[t][i], cols)),
    ensures all_null(key_of(db.tables[t][i], cols)),
{
    lemma_constraint_at(db, t, k);
    assert(fk_row_holds(db.tables[t][i], cols, db.tables[table as int], ref_cols, true));
}

/// A CHECK evaluates to `True` or `Unknown` (never `False`, never an error) on every row of its table.
pub proof fn lemma_check_row(db: Database, t: int, k: int, p: Pred, i: int)
    requires
        constraints_hold(db), 0 <= t < db.schema.len(), t < db.tables.len(), 0 <= k < db.schema[t].constraints.len(),
        db.schema[t].constraints[k] == Constraint::Check(p), 0 <= i < db.tables[t].len(),
    ensures eval_pred(db, db.tables[t][i], p) == Ok::<Truth, SqlError>(Truth::True)
        || eval_pred(db, db.tables[t][i], p) == Ok::<Truth, SqlError>(Truth::Unknown),
{
    lemma_constraint_at(db, t, k);
    assert(check_row_holds(db, db.tables[t][i], p));
}

} // verus!
