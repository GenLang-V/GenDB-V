//! FRAMEWORK FILE: verified entry points of a reference evaluator crate (`gendb_sqlspec::evaluator`).
//!
//! Copied unchanged into every evaluator crate as `crate::abi`, next to the translated statement `crate::query`
//! (`gendb_frontend::translator`: `schema_spec`, `query_spec`, `query_exec`, `lemma_query_wf`) and the generated
//! executable schema `crate::query_schema` (`schema_exec`). Checked by Verus with `--no-cheating` together with the
//! whole crate; the trusted `crate::shim` only decodes/encodes bytes around these two functions.
//!
//! - `abi_run`: the supplied table rows are interpreted with the schema the SQL was resolved against
//!   (`schema_exec`, proved equal to `schema_spec`); the verified interpreter `evaluate` checks the database
//!   (`db_wf`, `constraints_hold`) and the query (`wf_ordered`) itself, so nothing about host data is assumed.
//! - `abi_echo`: the executable AST, proved equal to the spec AST; the host compares its text with the
//!   translated AST document (translation validation of the emitter).
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::typing::*;
use crate::spec::order::*;
use crate::spec::constraints::*;
use crate::exec::relational::constraints::*;
use crate::exec::value::*;
use crate::exec::ast::*;
use crate::exec::relational::schema::*;
use crate::exec::relational::domain::*;
use crate::exec::relational::ops::*;
use crate::exec::relational::entry::*;
use crate::query::*;
use crate::query_schema::schema_exec;

verus! {

/// The database a call evaluates: the query's schema and the supplied rows (table id = position).
pub open spec fn abi_db(tables: Seq<Vec<ERow>>) -> Database {
    Database { schema: schema_spec(), tables: tables.map_values(|rel: Vec<ERow>| view_rows(rel@)) }
}

/// Contract of `abi_run` on the supplied rows (T3 `evaluate` specialised to the query's own schema and AST;
/// `IllTyped` is excluded by `lemma_query_wf`).
pub open spec fn abi_run_meets(tables: Seq<Vec<ERow>>, r: EvalResult) -> bool {
    let db = abi_db(tables);
    let q = query_spec();
    &&& (r is BadDatabase) == !db_wf(db)
    &&& !(r is IllTyped)
    &&& (r is ConstraintViolation) == (db_wf(db) && fits_constraints(db) && !constraints_hold(db))
    &&& (r is Capacity) == (db_wf(db)
            && (!fits_constraints(db) || (constraints_hold(db) && !fits_query(db, Seq::empty(), q.body))))
    &&& r matches EvalResult::Done(res) ==> db_wf(db) && constraints_hold(db) && fits_query(db, Seq::empty(), q.body)
            && view_rel(res) == denote_top(db, q) && ordered_ok(db, q, view_rel(res))
}

pub fn abi_run(tables: Vec<Vec<ERow>>) -> (r: EvalResult)
    ensures abi_run_meets(tables@, r),
{
    let ghost g = tables@;
    let db = EDatabase { schema: schema_exec(), tables };
    assert(db@ == abi_db(g));
    let q = query_exec();
    proof { lemma_query_wf(); }
    evaluate(&db, &q)
}

pub fn abi_echo() -> (q: EOrderedQuery)
    ensures q@ == query_spec(),
{
    query_exec()
}

} // verus!
