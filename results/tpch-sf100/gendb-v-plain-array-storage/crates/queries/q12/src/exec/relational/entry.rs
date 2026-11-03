//! Top-level statement evaluation. `exec_ordered` evaluates a statement: the canonical body rows, sorted and
//! sliced (`spec::order::denote_top`). `evaluate` is the checked entry point the host integration calls: it
//! validates the database, the statement and the declared constraints, then evaluates; its postcondition is the
//! end-to-end theorem of the evaluator.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::order::*;
use crate::spec::typing::*;
use crate::spec::constraints::*;
use crate::exec::value::*;
use crate::exec::ast::*;
use crate::exec::relational::schema::*;
use crate::exec::relational::domain::*;
use crate::exec::relational::ops::*;
use crate::exec::relational::eval::*;
use crate::exec::relational::order::*;
use crate::exec::relational::check::*;
use crate::exec::relational::constraints::*;
use crate::bridge::order::*;

verus! {

/// Outcome of a checked evaluation. `BadDatabase` / `IllTyped` / `ConstraintViolation` / `Capacity` are
/// refusals, never SQL results; `Done` carries the SQL result (rows or a SQL error).
pub enum EvalResult {
    /// The database violates `db_wf` (schema, column types, NULLs, value ranges).
    BadDatabase,
    /// The statement violates `wf_ordered` for the database's schema.
    IllTyped,
    /// The rows violate a declared integrity constraint (`constraints_hold` fails).
    ConstraintViolation,
    /// A concrete intermediate of checking the constraints (`fits_constraints`) or of the canonical evaluation
    /// (`fits_query`) is not machine-representable.
    Capacity,
    Done(Result<Vec<ERow>, SqlError>),
}

/// End-to-end theorem: on a well-formed database that satisfies its declared constraints and a checked
/// statement, a `Done` result is the canonical denotation `denote_top` and is allowed by `ordered_ok` (sorted
/// permutation of the body's bag, sliced; any tie order); `Capacity` is returned only when checking the
/// constraints or evaluating leaves the executable domain, and otherwise the result is `ConstraintViolation`
/// exactly when a constraint fails, else `Done`.
pub fn evaluate(db: &EDatabase, oq: &EOrderedQuery) -> (r: EvalResult)
    ensures
        (r is BadDatabase) == !db_wf(db@),
        (r is IllTyped) == (db_wf(db@) && !wf_ordered(db@.schema, view_ordered(*oq))),
        (r is ConstraintViolation) == (db_wf(db@) && wf_ordered(db@.schema, view_ordered(*oq))
            && fits_constraints(db@) && !constraints_hold(db@)),
        (r is Capacity) == (db_wf(db@) && wf_ordered(db@.schema, view_ordered(*oq))
            && (!fits_constraints(db@)
                || (constraints_hold(db@) && !fits_query(db@, Seq::empty(), view_ordered(*oq).body)))),
        r matches EvalResult::Done(res) ==> db_wf(db@) && constraints_hold(db@)
            && wf_ordered(db@.schema, view_ordered(*oq))
            && fits_query(db@, Seq::empty(), view_ordered(*oq).body)
            && view_rel(res) == denote_top(db@, view_ordered(*oq))
            && ordered_ok(db@, view_ordered(*oq), view_rel(res)),
{
    if !check_db(db) {
        return EvalResult::BadDatabase;
    }
    if !check_ordered(&db.schema, oq) {
        return EvalResult::IllTyped;
    }
    match check_constraints_exec(db) {
        Err(_) => return EvalResult::Capacity,
        Ok(false) => return EvalResult::ConstraintViolation,
        Ok(true) => {},
    }
    proof { lemma_db_wf_ts_ok(db@); }
    match exec_ordered(db, oq) {
        Err(_) => EvalResult::Capacity,
        Ok(res) => {
            proof { lemma_denote_top_ok(db@, view_ordered(*oq)); }
            EvalResult::Done(res)
        },
    }
}

/// A top-level statement: `spec::order::denote_top` (the body under the empty context, then ORDER BY, OFFSET and
/// LIMIT). `Capacity` exactly when the body leaves the executable domain (sorting and slicing never do).
pub fn exec_ordered(db: &EDatabase, oq: &EOrderedQuery) -> (r: Outcome<Vec<ERow>>)
    requires db_ts_ok(db@),
    ensures
        match r {
            Ok(res) => fits_query(db@, Seq::empty(), view_ordered(*oq).body)
                && rel_outcome_ok(res, denote_top(db@, view_ordered(*oq))),
            Err(_) => !fits_query(db@, Seq::empty(), view_ordered(*oq).body),
        },
{
    let ctx: ERow = Vec::new();
    proof { assert(view_row(ctx@) =~= Seq::<Val>::empty()); }
    let rows = match exec_query(db, &ctx, &oq.body) {
        Err(c) => return Err(c),
        Ok(Err(e)) => return Ok(Err(e)),
        Ok(Ok(rows)) => rows,
    };
    let ghost body = view_rows(rows@);
    let sorted = sort_rows_exec(&oq.keys, rows);
    let out = slice_rows_exec(&sorted, oq.offset, oq.limit);
    proof {
        assert(view_ordered(*oq).keys == view_keys(oq.keys@));
        lemma_sort_rows_ts_ok(view_keys(oq.keys@), body);
        lemma_slice_ts_ok(view_rows(sorted@), oq.offset as nat, view_ordered(*oq).limit);
    }
    Ok(Ok(out))
}

} // verus!
