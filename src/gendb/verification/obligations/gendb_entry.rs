// FRAMEWORK FILE: the fixed entry v3 of every GenDB Verus candidate (identity `gendb-verus-entry-v3`;
// source `verification/obligations/gendb_entry.rs`, assembled by `gendb_verification::obligations`).
//
// Copied unchanged into every candidate crate as `crate::gendb_entry`; only its child `binder.rs` and the
// sibling modules `crate::gendb_source` and `crate::gendb_params` are generated per query, from data only (the
// source declaration and the parameter declaration: no predicate, aggregate, ordering, capacity or bridge
// logic). Authors cannot edit any of them. The entry is checked by Verus with `--no-cheating` in the same crate
// as the author's code (`crate::agent`), the SQLSpec library (`crate::spec`, `crate::exec`, `crate::bridge`,
// `crate::link`) and the emitted statement (`crate::query`). The claim is stated with `spec` definitions and
// with the fixed source/answer definitions of `link::query` and `link::source` (`view_rows`, `proj_all`, the
// text column views); those are part of the fixed meaning, not optional toolkit items.
//
// The claim is stated directly in SQL terms. For the emitted statement `query_spec_at(ps)` at a parameter
// binding `ps` in the declared domain `crate::query::param_domain`, and for every database `db` of the emitted
// schema in the semantics' input domain (`db_wf`) whose source tables the delivered columns are
// (`bound_db`), the served status means:
// - `Ok(rows)`: `ordered_ok(db, oq, Ok(rows))`, an allowed output of the statement (ORDER BY ties allowed);
// - `SqlError(e)`: `ordered_ok(db, oq, Err(e))`, i.e. the statement's meaning is EXACTLY the SQL error `e`;
// - `Capacity`: `db` is outside the generic capacity domain `capacity_domain(db, oq)` (the canonical
//   evaluation `exec::relational::domain::fits_query`, SUM/AVG bounded by absolute mass);
// - `WorkerFailed`: a joined worker thread failed (only with the runtime's private token); permitted without
//   a condition on the input, and excluded by the trusted assumption `worker_failure`;
// - `ParamRefused`: exactly when the arguments are not a binding in the declared domain (verified
//   `gendb_params::bind_params`, before any author code); `Refused`: worker count outside 1..=MAX_WORKERS.
// Nothing else (the build statuses are those of `build_meets`). The theorems state what each status means
// (partial correctness). Verus's termination checks add that, under the trusted assumptions, every call of
// `abi_build` and `abi_query` ends with exactly one status its contract permits (the proved property
// `termination`, `verification/src/obligations/claim.rs`): total correctness relative to these contracts. A
// process abort (allocation failure, stack exhaustion, failed thread creation, or an unwind on the calling
// thread, which the shim turns into an abort) ends a call with no status; only the trusted assumption
// `calling_thread_progress` excludes it.
//
// Sources. The statement reads N distinct source tables (N >= 1). The delivered columns of every table arrive
// as one ABI column list; the generated binder decides `gendb_source::source_wf` exactly and yields the source
// view `v`; `gendb_source::tables(v)` are the source relations, one per distinct table, each the projection of
// its database table onto the declared columns (`gendb_source::source_columns_are_tables`). The entry decides
// the declared column domain `gendb_source::in_domain` (verified `gendb_source::source_in_domain`) before the
// author's builder runs.
//
// Data path. `abi_build` runs the author's builder; on `Ok` the returned parts decode, under the author's
// `crate::agent::decode`, to exactly `tables(v)` (`built_from`). `abi_query` requires `stored_asset`: the parts
// are a builder output of this crate for some source. That precondition is the trusted assumption at the FFI
// boundary (storage round trip + per-table source-version key + same build); it is not re-checked on the hot
// path. `theorem_end_to_end` composes build, storage round trip, argument binding and query.
//
// `WorkerFailed` has no author-constructible form: it needs a `runtime::WorkerFailure` token, whose field is
// private to `runtime` and which only `runtime::join_worker` (called only by `parallel::fork_join` on a failed
// join of a `no_unwind` worker) creates.
use vstd::prelude::*;
use crate::gendb_abi::{AbiStatus, BuildReturn, Column, DispatchEvidence, ParamArg, Part, QueryReturn};
use crate::gendb_source::{in_domain, lemma_source_in_domain, source_columns_are_tables, source_in_domain, source_wf, tables, SourceView};
use crate::gendb_params::{bind_params, param_source, Params};
use crate::query::{lemma_query_wf_at, param_domain, param_typed, query_spec_at, schema_spec};
use crate::exec::value::EVal;
use crate::exec::relational::domain::fits_query;
use crate::link::query::view_rows;
use crate::spec::value::{Database, Relation, Row, SqlError};
use crate::spec::ast::{Literal, OrderedQuery};
use crate::spec::order::{denote_body, ordered_ok};
use crate::spec::typing::{db_wf, wf_ordered};

pub mod binder;
pub mod layout;
pub mod parallel;
pub mod runtime;
pub mod source_check;
pub mod work;

use binder::{bind_source, column_source};
use layout::{owned_parts_view, parts_view, PartView};
use parallel::{Dispatch, MAX_WORKERS};
use runtime::QueryError;

verus! {

/// The author's query answer. Its meaning is fixed by `outcome_ok`; the author proves it.
pub enum Answer {
    /// Result rows (an allowed output of the statement).
    Rows(Vec<Vec<EVal>>),
    /// The statement's meaning is exactly this SQL error.
    SqlError(SqlError),
    /// The database is outside the capacity domain.
    Capacity,
}

/// The generic capacity domain of a statement on a database: every intermediate of the canonical evaluation
/// (`spec::eval`, in its order, up to its first SQL error) is machine representable, with SUM/AVG bounded by
/// the absolute mass of each group (`exec::relational::domain`). Trusted definition, not generated.
pub open spec fn capacity_domain(db: Database, oq: OrderedQuery) -> bool {
    fits_query(db, Seq::empty(), oq.body)
}

/// `db` is a database of the emitted schema, in the semantics' input domain, whose source tables the delivered
/// columns `v` are (each table projected onto its declared columns).
pub open spec fn bound_db(v: SourceView, db: Database) -> bool {
    &&& db.schema == schema_spec()
    &&& db_wf(db)
    &&& source_columns_are_tables(v, db)
}

/// The fixed meaning of an author answer for one database and one statement instance.
pub open spec fn outcome_ok(db: Database, oq: OrderedQuery, r: Result<Answer, QueryError>) -> bool {
    match r {
        Ok(Answer::Rows(out)) => ordered_ok(db, oq, Ok::<Relation, SqlError>(view_rows(out@))),
        Ok(Answer::SqlError(e)) => ordered_ok(db, oq, Err::<Relation, SqlError>(e)),
        Ok(Answer::Capacity) => !capacity_domain(db, oq),
        Err(QueryError::WorkerFailed(_)) => true,
        Err(_) => false,
    }
}

/// The author's query obligation for source `v` and binding `ps`: the answer is correct for EVERY database
/// bound to `v`.
pub open spec fn answer_meets(v: SourceView, ps: Seq<Literal>, r: Result<Answer, QueryError>) -> bool {
    forall|db: Database| #[trigger] bound_db(v, db) ==> outcome_ok(db, query_spec_at(ps), r)
}

/// `parts` is a valid representation of source `v` under the author's `decode`: they decode to exactly the
/// source tables `tables(v)` (a verified builder output for `v`, and `v` is inside the declared column domain).
pub open spec fn built_from(v: SourceView, parts: Seq<PartView>) -> bool {
    &&& source_wf(v)
    &&& in_domain(tables(v))
    &&& crate::agent::decode(parts) == Some(tables(v))
}

/// Precondition of the query: the parts were built from some source.
pub open spec fn stored_asset(parts: Seq<PartView>) -> bool {
    exists|v: SourceView| #[trigger] built_from(v, parts)
}

pub open spec fn workers_ok(workers: usize) -> bool {
    1 <= workers <= MAX_WORKERS
}

/// Fixed builder contract. Shape or worker-count mismatch: `Refused`. Otherwise, for the bound source `v`:
/// `Ok` exactly with a valid representation of `v`; `InvalidInput` only for input outside the declared column
/// domain; `WorkerFailed` only from a failed join of a `no_unwind` worker.
pub open spec fn build_meets(columns: Seq<Column>, workers: usize, r: BuildReturn) -> bool {
    if !workers_ok(workers) || column_source(columns) is None {
        r.status is Refused
    } else {
        let v = column_source(columns)->Some_0;
        match r.status {
            AbiStatus::Ok => built_from(v, owned_parts_view(r.parts@)),
            AbiStatus::InvalidInput => !in_domain(tables(v)),
            AbiStatus::WorkerFailed => true,
            _ => false,
        }
    }
}

/// The fixed meaning of a served status and rows for one database and one statement instance.
pub open spec fn served(db: Database, oq: OrderedQuery, r: QueryReturn) -> bool {
    match r.status {
        AbiStatus::Ok => ordered_ok(db, oq, Ok::<Relation, SqlError>(view_rows(r.rows@))),
        AbiStatus::SqlError(e) => ordered_ok(db, oq, Err::<Relation, SqlError>(e)),
        AbiStatus::Capacity => !capacity_domain(db, oq),
        AbiStatus::WorkerFailed => true,
        _ => false,
    }
}

/// Fixed query contract: worker-count mismatch `Refused`; arguments that are not a binding in the declared
/// domain `ParamRefused`; otherwise, for every source the parts were built from and every database bound to it,
/// the result is served for the statement at the bound parameters.
pub open spec fn query_meets(parts: Seq<PartView>, args: Seq<ParamArg>, workers: usize, r: QueryReturn) -> bool {
    if !workers_ok(workers) {
        r.status is Refused
    } else if param_source(args) is None {
        r.status is ParamRefused
    } else {
        let ps = param_source(args)->Some_0;
        forall|v: SourceView| #[trigger] built_from(v, parts) ==>
            forall|db: Database| #[trigger] bound_db(v, db) ==> served(db, query_spec_at(ps), r)
    }
}

fn evidence(d: Dispatch) -> DispatchEvidence {
    let (spawned, joined, ranges) = d.into_parts();
    DispatchEvidence { spawned, joined, ranges }
}

/// Builder entry (offline asset build). Called by the trusted shim.
pub fn abi_build(columns: &[Column], workers: usize) -> (r: BuildReturn)
    ensures build_meets(columns@, workers, r),
{
    let mut dispatch = Dispatch::new();
    let src = match bind_source(columns) {
        Some(s) => s,
        None => return BuildReturn { status: AbiStatus::Refused, parts: Vec::new(), dispatch: evidence(dispatch) },
    };
    if workers < 1 || workers > MAX_WORKERS {
        return BuildReturn { status: AbiStatus::Refused, parts: Vec::new(), dispatch: evidence(dispatch) };
    }
    if !source_in_domain(&src) {
        return BuildReturn { status: AbiStatus::InvalidInput, parts: Vec::new(), dispatch: evidence(dispatch) };
    }
    let (status, parts) = match crate::agent::build(&src, workers, &mut dispatch) {
        Ok(p) => (AbiStatus::Ok, p),
        Err(QueryError::InvalidInput) => (AbiStatus::InvalidInput, Vec::new()),
        Err(QueryError::Malformed) => (AbiStatus::Malformed, Vec::new()),
        Err(QueryError::WorkerFailed(_)) => (AbiStatus::WorkerFailed, Vec::new()),
    };
    BuildReturn { status, parts, dispatch: evidence(dispatch) }
}

/// Query entry (serving the stored representation at one argument list). Called by the trusted shim, which is
/// trusted to meet `stored_asset` (see the file header).
pub fn abi_query(parts: &[Part], args: &[ParamArg], workers: usize) -> (r: QueryReturn)
    requires stored_asset(parts_view(parts@)),
    ensures query_meets(parts_view(parts@), args@, workers, r),
{
    let mut dispatch = Dispatch::new();
    if workers < 1 || workers > MAX_WORKERS {
        return QueryReturn { status: AbiStatus::Refused, rows: Vec::new(), dispatch: evidence(dispatch) };
    }
    let params = match bind_params(args) {
        Some(p) => p,
        None => return QueryReturn { status: AbiStatus::ParamRefused, rows: Vec::new(), dispatch: evidence(dispatch) },
    };
    let answer = crate::agent::query(parts, &params, workers, &mut dispatch);
    let (status, rows) = match answer {
        Ok(Answer::Rows(rows)) => (AbiStatus::Ok, rows),
        Ok(Answer::SqlError(e)) => (AbiStatus::SqlError(e), Vec::new()),
        Ok(Answer::Capacity) => (AbiStatus::Capacity, Vec::new()),
        Err(QueryError::InvalidInput) => (AbiStatus::InvalidInput, Vec::new()),
        Err(QueryError::Malformed) => (AbiStatus::Malformed, Vec::new()),
        Err(QueryError::WorkerFailed(_)) => (AbiStatus::WorkerFailed, Vec::new()),
    };
    QueryReturn { status, rows, dispatch: evidence(dispatch) }
}

/// The source bound by the verified binder (meaningful when `column_source(columns) is Some`).
pub open spec fn bound_source(columns: Seq<Column>) -> SourceView {
    column_source(columns)->Some_0
}

/// The data path: a successful build, stored and read back unchanged (the trusted round trip
/// `parts_view(stored) == owned_parts_view(built.parts@)`), discharges the query precondition, and the parts
/// the query reads were built from the bound source.
pub proof fn theorem_build_then_query(columns: Seq<Column>, build_workers: usize, built: BuildReturn, stored: Seq<Part>)
    requires
        build_meets(columns, build_workers, built),
        built.status is Ok,
        parts_view(stored) == owned_parts_view(built.parts@),
    ensures
        column_source(columns) is Some,
        built_from(bound_source(columns), parts_view(stored)),
        stored_asset(parts_view(stored)),
{
    let v = bound_source(columns);
    assert(built_from(v, parts_view(stored)));
}

/// The end-to-end theorem in VERUS_SQL terms, over the executed entry (`abi_build`, `abi_query`: their
/// checked postconditions are the premises `build_meets` and `query_meets`) and its argument decoding.
/// `db` is any database of the emitted schema in the semantics' input domain whose source tables the delivered
/// columns are (`bound_db`: the trusted capture binding). For the asset built from those columns, stored and
/// served with arguments `args` at `query_workers` workers:
/// - `ParamRefused` exactly when `args` is not a binding in the declared domain;
/// - otherwise, with `ps` the bound values (in `param_domain`, the statement well-typed at `ps`) and
///   `oq = query_spec_at(ps)`: `Ok` rows are an allowed output of `oq` on `db`; `SqlError(e)` means the meaning
///   of `oq` on `db` is exactly the error `e`; `Capacity` means `db` is outside `capacity_domain`; no other
///   status except a real worker failure.
pub proof fn theorem_end_to_end(
    db: Database,
    columns: Seq<Column>,
    build_workers: usize,
    built: BuildReturn,
    stored: Seq<Part>,
    args: Seq<ParamArg>,
    query_workers: usize,
    result: QueryReturn,
)
    requires
        build_meets(columns, build_workers, built),
        built.status is Ok,
        parts_view(stored) == owned_parts_view(built.parts@),
        query_meets(parts_view(stored), args, query_workers, result),
        workers_ok(query_workers),
        bound_db(bound_source(columns), db),
    ensures
        stored_asset(parts_view(stored)),
        (result.status is ParamRefused) <==> param_source(args) is None,
        param_source(args) matches Some(ps) ==> {
            let oq = query_spec_at(ps);
            &&& param_domain(ps)
            &&& wf_ordered(schema_spec(), oq)
            &&& (result.status is Ok ==> ordered_ok(db, oq, Ok::<Relation, SqlError>(view_rows(result.rows@))))
            &&& (result.status matches AbiStatus::SqlError(e) ==> ordered_ok(db, oq, Err::<Relation, SqlError>(e))
                    && denote_body(db, oq) == Err::<Relation, SqlError>(e))
            &&& (result.status is Capacity ==> !capacity_domain(db, oq))
            &&& (result.status is Ok || result.status is SqlError || result.status is Capacity || result.status is WorkerFailed)
        },
{
    theorem_build_then_query(columns, build_workers, built, stored);
    let v = bound_source(columns);
    if param_source(args) is Some {
        let ps = param_source(args)->Some_0;
        lemma_query_wf_at(ps);
        assert(served(db, query_spec_at(ps), result));
    }
}

/// Inside the capacity domain and without a worker failure, the status is decided by the SQL meaning: `Ok` when
/// the statement has a value on `db`, `SqlError(e)` exactly when its meaning is the error `e`.
pub proof fn corollary_inside_capacity(
    db: Database,
    columns: Seq<Column>,
    build_workers: usize,
    built: BuildReturn,
    stored: Seq<Part>,
    args: Seq<ParamArg>,
    query_workers: usize,
    result: QueryReturn,
    ps: Seq<Literal>,
)
    requires
        build_meets(columns, build_workers, built),
        built.status is Ok,
        parts_view(stored) == owned_parts_view(built.parts@),
        query_meets(parts_view(stored), args, query_workers, result),
        workers_ok(query_workers),
        bound_db(bound_source(columns), db),
        param_source(args) == Some(ps),
        capacity_domain(db, query_spec_at(ps)),
        !(result.status is WorkerFailed),
    ensures
        denote_body(db, query_spec_at(ps)) is Ok ==> result.status is Ok,
        denote_body(db, query_spec_at(ps)) matches Err(e) ==> result.status == AbiStatus::SqlError(e),
{
    theorem_end_to_end(db, columns, build_workers, built, stored, args, query_workers, result);
    let oq = query_spec_at(ps);
    if result.status is Ok {
        assert(ordered_ok(db, oq, Ok::<Relation, SqlError>(view_rows(result.rows@))));
    }
}

/// On the real source tables, the builder never reports `InvalidInput`: the delivered columns of a `db_wf`
/// database are in the declared column domain (generated `gendb_source::lemma_source_in_domain`).
pub proof fn theorem_build_total(db: Database, columns: Seq<Column>, build_workers: usize, built: BuildReturn)
    requires
        build_meets(columns, build_workers, built),
        workers_ok(build_workers),
        column_source(columns) is Some,
        bound_db(bound_source(columns), db),
    ensures
        built.status is Ok || built.status is WorkerFailed,
{
    lemma_source_in_domain(db, bound_source(columns));
}

} // verus!
