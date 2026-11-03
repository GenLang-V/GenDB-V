// FRAMEWORK FILE: the fixed query entry v4 of every GenDB query crate over stored data (identity
// `gendb-verus-entry-v4`; source `verification/obligations/query_entry.rs`, assembled as `crate::gendb_entry` by
// `gendb_verification::obligations`).
//
// Copied unchanged into every query crate; only its child `stores.rs` and the sibling modules `crate::schema`,
// `crate::query`, `crate::gendb_params` and `crate::stores::S::{mod, declaration}` are generated, from data only (the
// dataset schema, the statement, its parameter declaration and the declarations of the storages the query reads).
// Statement arguments are `crate::gendb_arguments::QueryArg` (query crates only: the shared `gendb_abi::ParamArg`
// plus `text`; `gendb_abi.rs` stays unchanged because it is part of every storage's dependency closure).
// Each storage's interface (`crate::stores::S::interface`: the author's relation `represents` and readers) is copied
// byte for byte from that storage's checked build and read-only here. Authors cannot edit any of these files. The
// entry is checked by Verus with `--no-cheating` in the same crate as the query author's code (`crate::agent`), the
// SQLSpec library and those interfaces.
//
// The claim is stated in SQL terms, exactly as in the entry v3 (`outcome_ok`, `served`, `capacity_domain`, the
// parameter rules). For the emitted statement `query_spec_at(ps)` at a binding `ps` in the declared domain
// `crate::query::param_domain`, and for EVERY database `db` of the schema in the semantics' input domain (`db_wf`)
// whose stored relations the stored parts of every storage use represent (`bound_db`), the served status means:
// - `Ok(rows)`: `ordered_ok(db, oq, Ok(rows))`, an allowed output of the statement (ORDER BY ties allowed);
//   the rows are delivered either as `Vec<EVal>` rows or in columnar form (`results::ResultColumns`, viewed by the
//   fixed `results::columns_view`; the claim then also states `columns_wf`), see `delivered_rows`;
// - `SqlError(e)`: the statement's meaning is EXACTLY the SQL error `e`;
// - `Capacity`: `db` is outside the generic capacity domain `capacity_domain(db, oq)`;
// - `WorkerFailed`: a joined worker thread failed (only with the runtime's private token); permitted without a
//   condition on the input, and excluded by the trusted assumption `worker_failure`;
// - `ParamRefused`: exactly when the arguments are not a binding in the declared domain (verified `bind_params`,
//   before any author code); `Refused`: worker count outside 1..=MAX_WORKERS.
// Nothing else. The theorems state what each status means (partial correctness). Verus's termination checks add that,
// under the trusted assumptions, every call ends with exactly one of these statuses (the proved property
// `termination`, `verification/src/obligations/claim.rs`): total correctness relative to this contract. A process
// abort (allocation failure, stack exhaustion, failed thread creation, or an unwind on the calling thread, which the
// shim turns into an abort) ends a call with no status; only the trusted assumption `calling_thread_progress`
// excludes it.
//
// Composition with storage builds. For a storage `S`, `stores::stored_ok` requires `S::interface::represents(parts,
// S::declaration::stored_relations(db))`, which is literally the conclusion of `S`'s checked
// `theorem_storage_built` (storage entry) for the actual database, provided both crates carry the same `stores/S/**`,
// schema, SQLSpec library and fixed files at the same paths under the same toolchain, and every author file of both
// crates passes the author-source rules (implementation ownership, supported macros only), without which equal text
// could resolve differently (checked by admission: `storage_spec_identity`, `obligations::check_storage_composition`).
// `stored_relations(db)` are projections of `db`'s own tables (equalities only: no value
// restriction), so `bound_db` adds no hypothesis about the SQL data beyond what the storage builds proved for it.
//
// Data path. `abi_query` requires `stores_ready`: some database is bound to the parts. That precondition is the
// trusted assumption at the FFI boundary (every storage use's parts are the parts its admitted build returned for the
// same source capture, unchanged); it is not re-checked on the hot path. Author code reads the parts only through
// `stored::StoredParts` extents; the request counts of every use are returned with the answer (descriptive only).
//
// `WorkerFailed` has no author-constructible form: it needs a `runtime::WorkerFailure` token, whose field is private
// to `runtime` and which only `runtime::join_worker` (called only by `parallel::fork_join` on a failed join of a
// `no_unwind` worker) creates.
use vstd::prelude::*;
use crate::gendb_abi::{AbiStatus, DispatchEvidence, Part, QueryReturn};
use crate::gendb_arguments::QueryArg;
use crate::gendb_params::{bind_params, param_source};
use crate::query::{lemma_query_wf_at, param_domain, query_spec_at};
use crate::schema::schema_spec;
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

/// `db` is a database of the schema, in the semantics' input domain, whose stored relations the parts of every
/// storage use represent.
pub open spec fn bound_db(sv: StoresView, db: Database) -> bool {
    &&& db.schema == schema_spec()
    &&& db_wf(db)
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
