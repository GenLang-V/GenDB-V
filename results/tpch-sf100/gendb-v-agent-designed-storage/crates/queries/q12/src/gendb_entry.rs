// FRAMEWORK FILE: the fixed query entry v5 of every GenDB query crate whose request declares integrity constraints
// (identity `gendb-verus-entry-v5`; source `verification/obligations/query_entry_v5.rs`, assembled as
// `crate::gendb_entry` by `gendb_verification::obligations`).
//
// It is the query entry v4 (`verification/obligations/query_entry.rs`) with one more hypothesis and nothing else:
// `bound_db` also requires `constraints_hold(declared_db(db))`, the request's declared constraints in SQLSpec's meaning
// for the whole database `db` (every table, every declared column). `crate::gendb_constraints` is generated from the
// request's declarations only (`declared_schema`: the column schema with the declared constraints; `declared_db(db)`:
// `db`'s tables under it; `lemma_declared_schema`); the claim's SQL meaning is still evaluated on `db`, whose schema
// is the column schema `crate::schema::schema_spec()`. Every other item, the claim (`outcome_ok`, `served`,
// `capacity_domain`, `theorem_end_to_end`, `corollary_inside_capacity`) and the composition with storage builds are
// the v4 text; a drift test compares both files outside this header, the import and `bound_db`.
//
// The declarations are the user's assumption about the actual database (trusted assumption
// `declared_integrity_constraints`, trust `user_declared`): never checked against the data. The host's link at
// `abi_query` (`stores_ready`: some database is bound to the parts) therefore includes that the actual database
// satisfies them. If it does not, the claim says nothing about that data.
//
// Copied unchanged into every constrained query crate; checked by Verus with `--no-cheating` in the same crate as the
// author's code (`crate::agent`), the SQLSpec library, `crate::gendb_constraints` and the storages' interfaces.
use vstd::prelude::*;
use crate::gendb_abi::{AbiStatus, DispatchEvidence, Part, QueryReturn};
use crate::gendb_arguments::QueryArg;
use crate::gendb_params::{bind_params, param_source};
use crate::query::{lemma_query_wf_at, param_domain, query_spec_at};
use crate::schema::schema_spec;
use crate::gendb_constraints::declared_db;
use crate::spec::constraints::constraints_hold;
use crate::exec::value::EVal;
use crate::exec::relational::domain::fits_query;
use crate::link::query::view_rows;
use crate::spec::value::{Database, Relation, SqlError};
use crate::spec::ast::{Literal, OrderedQuery};
use crate::spec::order::{denote_body, ordered_ok};
use crate::spec::typing::{db_wf, wf_ordered};

pub mod layout;
pub mod parallel;
pub mod results;
pub mod runtime;
pub mod source_check;
pub mod stored;
pub mod stores;
pub mod work;

use parallel::{Dispatch, MAX_WORKERS};
use results::{columns_view, columns_wf, ResultColumns};
use runtime::QueryError;
use stored::RequestCounts;
use stores::{open_stores, request_counts, stored_ok, uses_view, Stores, StoresView, STORAGE_USES};

verus! {

/// The author's query answer. Its meaning is fixed by `outcome_ok`; the author proves it.
pub enum Answer {
    /// Result rows (an allowed output of the statement).
    Rows(Vec<Vec<EVal>>),
    /// The same in columnar form (`results::columns_view`; no allocation per row): an allowed output of the statement
    /// whose columns are well formed (`results::columns_wf`).
    Columns(ResultColumns),
    /// The statement's meaning is exactly this SQL error.
    SqlError(SqlError),
    /// The database is outside the capacity domain.
    Capacity,
}

/// The generic capacity domain of a statement on a database: every intermediate of the canonical evaluation
/// (`spec::eval`, in its order, up to its first SQL error) is machine representable, with SUM/AVG bounded by the
/// absolute mass of each group (`exec::relational::domain`). Trusted definition, not generated.
pub open spec fn capacity_domain(db: Database, oq: OrderedQuery) -> bool {
    fits_query(db, Seq::empty(), oq.body)
}

/// `db` is a database of the schema, in the semantics' input domain, satisfying the declared integrity constraints
/// (`constraints_hold(declared_db(db))`: over all of `db`'s tables and columns), whose stored relations the parts of
/// every storage use represent.
pub open spec fn bound_db(sv: StoresView, db: Database) -> bool {
    &&& db.schema == schema_spec()
    &&& db_wf(db)
    &&& constraints_hold(declared_db(db))
    &&& stored_ok(sv, db)
}

/// The fixed meaning of an author answer for one database and one statement instance.
pub open spec fn outcome_ok(db: Database, oq: OrderedQuery, r: Result<Answer, QueryError>) -> bool {
    match r {
        Ok(Answer::Rows(out)) => ordered_ok(db, oq, Ok::<Relation, SqlError>(view_rows(out@))),
        Ok(Answer::Columns(c)) => columns_wf(c) && ordered_ok(db, oq, Ok::<Relation, SqlError>(columns_view(c))),
        Ok(Answer::SqlError(e)) => ordered_ok(db, oq, Err::<Relation, SqlError>(e)),
        Ok(Answer::Capacity) => !capacity_domain(db, oq),
        Err(QueryError::WorkerFailed(_)) => true,
        Err(_) => false,
    }
}

/// The author's query obligation for stored parts `sv` and binding `ps`: the answer is correct for EVERY database
/// bound to the parts.
pub open spec fn answer_meets(sv: StoresView, ps: Seq<Literal>, r: Result<Answer, QueryError>) -> bool {
    forall|db: Database| #[trigger] bound_db(sv, db) ==> outcome_ok(db, query_spec_at(ps), r)
}

/// Precondition of the query: some database is bound to the stored parts (the trusted FFI assumption; discharged
/// by the storage builds' `theorem_storage_built` for the actual database).
pub open spec fn stores_ready(sv: StoresView) -> bool {
    exists|db: Database| #[trigger] bound_db(sv, db)
}

pub open spec fn workers_ok(workers: usize) -> bool {
    1 <= workers <= MAX_WORKERS
}

/// The result rows a call delivers: its columnar answer's rows when it has one, else its row answer's rows.
pub open spec fn delivered_rows(r: StoredQueryReturn) -> Relation {
    match r.columns {
        Some(c) => columns_view(c),
        None => view_rows(r.result.rows@),
    }
}

/// A delivered columnar answer is well formed (the shim relies on it when encoding the rows).
pub open spec fn delivered_wf(r: StoredQueryReturn) -> bool {
    r.columns matches Some(c) ==> columns_wf(c)
}

/// The fixed meaning of a served status and rows for one database and one statement instance.
pub open spec fn served(db: Database, oq: OrderedQuery, r: StoredQueryReturn) -> bool {
    match r.result.status {
        AbiStatus::Ok => delivered_wf(r) && ordered_ok(db, oq, Ok::<Relation, SqlError>(delivered_rows(r))),
        AbiStatus::SqlError(e) => ordered_ok(db, oq, Err::<Relation, SqlError>(e)),
        AbiStatus::Capacity => !capacity_domain(db, oq),
        AbiStatus::WorkerFailed => true,
        _ => false,
    }
}

/// Fixed query contract: worker-count mismatch `Refused`; arguments that are not a binding in the declared domain
/// `ParamRefused`; otherwise, for every database bound to the stored parts, the result is served for the statement
/// at the bound parameters.
pub open spec fn query_meets(sv: StoresView, args: Seq<QueryArg>, workers: usize, r: StoredQueryReturn) -> bool {
    if !workers_ok(workers) {
        r.result.status is Refused
    } else if param_source(args) is None {
        r.result.status is ParamRefused
    } else {
        let ps = param_source(args)->Some_0;
        forall|db: Database| #[trigger] bound_db(sv, db) ==> served(db, query_spec_at(ps), r)
    }
}

/// A query call's result, its columnar answer (`Some` exactly for an `Ok` columnar answer, whose `result.rows` is
/// then empty) and the request counts of every storage use (in use order).
pub struct StoredQueryReturn {
    pub result: QueryReturn,
    pub columns: Option<ResultColumns>,
    pub requests: Vec<RequestCounts>,
}

fn evidence(d: Dispatch) -> DispatchEvidence {
    let (spawned, joined, ranges) = d.into_parts();
    DispatchEvidence { spawned, joined, ranges }
}

fn finish(stores: &Stores, status: AbiStatus, rows: Vec<Vec<EVal>>, dispatch: Dispatch) -> (r: StoredQueryReturn)
    ensures r.result.status == status, r.result.rows == rows, r.columns is None,
{
    StoredQueryReturn { result: QueryReturn { status, rows, dispatch: evidence(dispatch) }, columns: None, requests: request_counts(stores) }
}

fn finish_columns(stores: &Stores, columns: ResultColumns, dispatch: Dispatch) -> (r: StoredQueryReturn)
    ensures r.result.status is Ok, r.columns == Some(columns),
{
    StoredQueryReturn {
        result: QueryReturn { status: AbiStatus::Ok, rows: Vec::new(), dispatch: evidence(dispatch) },
        columns: Some(columns),
        requests: request_counts(stores),
    }
}

/// Query entry (serving stored parts at one argument list). `uses` holds the parts of every storage use, in the use
/// order of `stores::Stores`. Called by the trusted shim, which is trusted to meet `stores_ready` (file header).
pub fn abi_query(uses: Vec<Vec<Part>>, args: &[QueryArg], workers: usize) -> (r: StoredQueryReturn)
    requires
        uses.len() == STORAGE_USES,
        stores_ready(uses_view(uses@)),
    ensures
        query_meets(uses_view(uses@), args@, workers, r),
{
    let ghost sv = uses_view(uses@);
    let mut stores = open_stores(uses);
    let mut dispatch = Dispatch::new();
    if workers < 1 || workers > MAX_WORKERS {
        return finish(&stores, AbiStatus::Refused, Vec::new(), dispatch);
    }
    let params = match bind_params(args) {
        Some(p) => p,
        None => return finish(&stores, AbiStatus::ParamRefused, Vec::new(), dispatch),
    };
    let answer = crate::agent::query(&mut stores, &params, workers, &mut dispatch);
    match answer {
        Ok(Answer::Rows(rows)) => finish(&stores, AbiStatus::Ok, rows, dispatch),
        Ok(Answer::Columns(columns)) => finish_columns(&stores, columns, dispatch),
        Ok(Answer::SqlError(e)) => finish(&stores, AbiStatus::SqlError(e), Vec::new(), dispatch),
        Ok(Answer::Capacity) => finish(&stores, AbiStatus::Capacity, Vec::new(), dispatch),
        Err(QueryError::InvalidInput) => finish(&stores, AbiStatus::InvalidInput, Vec::new(), dispatch),
        Err(QueryError::Malformed) => finish(&stores, AbiStatus::Malformed, Vec::new(), dispatch),
        Err(QueryError::WorkerFailed(_)) => finish(&stores, AbiStatus::WorkerFailed, Vec::new(), dispatch),
    }
}

/// The end-to-end theorem in SQL terms, over the executed entry (`abi_query`: its checked postcondition is the
/// premise `query_meets`) and its argument decoding. `db` is any database of the schema in the semantics' input
/// domain whose stored relations the parts represent (`bound_db`: for the actual database, the conjunction of the
/// storage builds' `theorem_storage_built` conclusions). Served with arguments `args` at `workers` workers:
/// - `ParamRefused` exactly when `args` is not a binding in the declared domain;
/// - otherwise, with `ps` the bound values (in `param_domain`, the statement well-typed at `ps`) and
///   `oq = query_spec_at(ps)`: `Ok` rows are an allowed output of `oq` on `db`; `SqlError(e)` means the meaning of
///   `oq` on `db` is exactly the error `e`; `Capacity` means `db` is outside `capacity_domain`; no other status
///   except a real worker failure.
pub proof fn theorem_end_to_end(db: Database, sv: StoresView, args: Seq<QueryArg>, workers: usize, result: StoredQueryReturn)
    requires
        query_meets(sv, args, workers, result),
        workers_ok(workers),
        bound_db(sv, db),
    ensures
        stores_ready(sv),
        (result.result.status is ParamRefused) <==> param_source(args) is None,
        param_source(args) matches Some(ps) ==> {
            let oq = query_spec_at(ps);
            let status = result.result.status;
            &&& param_domain(ps)
            &&& wf_ordered(schema_spec(), oq)
            &&& (status is Ok ==> delivered_wf(result) && ordered_ok(db, oq, Ok::<Relation, SqlError>(delivered_rows(result))))
            &&& (status matches AbiStatus::SqlError(e) ==> ordered_ok(db, oq, Err::<Relation, SqlError>(e))
                    && denote_body(db, oq) == Err::<Relation, SqlError>(e))
            &&& (status is Capacity ==> !capacity_domain(db, oq))
            &&& (status is Ok || status is SqlError || status is Capacity || status is WorkerFailed)
        },
{
    if param_source(args) is Some {
        let ps = param_source(args)->Some_0;
        lemma_query_wf_at(ps);
        assert(served(db, query_spec_at(ps), result));
    }
}

/// Inside the capacity domain and without a worker failure, the status is decided by the SQL meaning: `Ok` when the
/// statement has a value on `db`, `SqlError(e)` exactly when its meaning is the error `e`.
pub proof fn corollary_inside_capacity(
    db: Database,
    sv: StoresView,
    args: Seq<QueryArg>,
    workers: usize,
    result: StoredQueryReturn,
    ps: Seq<Literal>,
)
    requires
        query_meets(sv, args, workers, result),
        workers_ok(workers),
        bound_db(sv, db),
        param_source(args) == Some(ps),
        capacity_domain(db, query_spec_at(ps)),
        !(result.result.status is WorkerFailed),
    ensures
        denote_body(db, query_spec_at(ps)) is Ok ==> result.result.status is Ok,
        denote_body(db, query_spec_at(ps)) matches Err(e) ==> result.result.status == AbiStatus::SqlError(e),
{
    theorem_end_to_end(db, sv, args, workers, result);
    let oq = query_spec_at(ps);
    if result.result.status is Ok {
        assert(ordered_ok(db, oq, Ok::<Relation, SqlError>(delivered_rows(result))));
    }
}

} // verus!
