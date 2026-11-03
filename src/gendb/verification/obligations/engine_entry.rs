// FRAMEWORK FILE: the fixed engine entry of every GenDB engine crate (identity `gendb-verus-engine-entry-v1`; source
// `verification/obligations/engine_entry.rs`, assembled as `crate::gendb_entry` by
// `gendb_verification::obligations::engine_crate_files`).
//
// An engine crate is one verified engine for a whole schema: its author code (`crate::agent::engine`) answers ANY
// supported statement, given as AST bytes at call time, over the stored parts of the storages it reads. Nothing in the
// crate is per statement. Copied unchanged into every engine crate; only its children `stores.rs` and `schema_exec.rs`
// are generated, from data only (the storage uses and the column schema). Checked by Verus with `--no-cheating` in
// the same crate as the author's code, the SQLSpec library, the AST codec (`crate::gendb_ast_codec`), the declared
// constraints (`crate::gendb_constraints`) and the storages' interfaces.
//
// The claim (`engine_meets`, `theorem_engine_end_to_end`), for the statement `decode_spec(ast)` the bytes mean (the
// codec's fixed definition) and EVERY database `db` of the schema in the semantics' input domain that satisfies the
// request's declared integrity constraints and whose stored relations the parts of every storage use represent
// (`bound_db`, the query entry v5's form):
// - `Refused`: exactly when the worker count is outside 1..=MAX_WORKERS;
// - `Malformed`: exactly when the bytes decode to no statement (`decode_spec(ast) is None`);
// - `ParamRefused`: exactly when the decoded statement is not supported, `!supported(oq)`, i.e. not well typed for the
//   schema (`wf_ordered(schema_spec(), oq)`; decided by the verified checker `check_ordered` before any author code);
// - otherwise the outcome is `served` exactly as in the query entries: `Ok(rows)` an allowed output (`ordered_ok`, ORDER
//   BY ties and the LIMIT boundary in any allowed way); `SqlError(e)` only when the statement's meaning on `db` is
//   exactly `e`; `Capacity` only outside `capacity_domain(db, oq)`; `WorkerFailed` only from a failed join.
// Nothing else. The set of supported statements is this fixed predicate; the engine author cannot narrow it.
// Statement parameters are not part of the claim: the host substitutes a binding's typed literals into the AST before
// encoding it (`gendb_frontend::engine_encode`), and the echo (`abi_engine_echo`) lets the host compare the decoded
// statement with its own document (trusted items `host_ast_encoding` and `engine_echo`).
//
// Composition with storage builds is the query entry's: `stores::stored_ok` is literally the conclusion of every
// storage's `theorem_storage_built`, under the closure identity checked at admission (`storage_spec_identity`).
// `abi_engine_query` requires `stores_ready` (some database is bound to the parts), the trusted assumption at the FFI
// boundary (`stored_parts_round_trip`), which includes that the actual database satisfies the declared constraints
// (`declared_integrity_constraints`). If it does not, the claim says nothing about that data.
//
// `WorkerFailed` has no author-constructible form (the `runtime::WorkerFailure` token is private to the runtime).
use vstd::prelude::*;
use crate::gendb_abi::{AbiStatus, DispatchEvidence, Part, QueryReturn};
use crate::gendb_ast_codec::{decode_query, decode_spec, render_query, render_spec};
use crate::schema::schema_spec;
use crate::gendb_constraints::declared_db;
use crate::spec::constraints::constraints_hold;
use crate::exec::ast::{view_ordered, EOrderedQuery};
use crate::exec::relational::check::check_ordered;
use crate::exec::relational::schema::view_schema;
use crate::exec::value::EVal;
use crate::exec::relational::domain::fits_query;
use crate::link::query::view_rows;
use crate::spec::value::{Database, Relation, SqlError};
use crate::spec::ast::OrderedQuery;
use crate::spec::order::{denote_body, ordered_ok};
use crate::spec::typing::{db_wf, wf_ordered};

pub mod layout;
pub mod parallel;
pub mod results;
pub mod runtime;
pub mod schema_exec;
pub mod source_check;
pub mod stored;
pub mod stores;
pub mod work;

use parallel::{Dispatch, MAX_WORKERS};
use results::{columns_view, columns_wf, ResultColumns};
use runtime::QueryError;
use schema_exec::schema_exec;
use stored::RequestCounts;
use stores::{open_stores, request_counts, stored_ok, uses_view, Stores, StoresView, STORAGE_USES};

verus! {

/// The engine author's answer for one statement. Its meaning is fixed by `outcome_ok`; the author proves it.
pub enum Answer {
    /// Result rows (an allowed output of the statement).
    Rows(Vec<Vec<EVal>>),
    /// The same in columnar form (`results::columns_view`); its columns are well formed (`results::columns_wf`).
    Columns(ResultColumns),
    /// The statement's meaning is exactly this SQL error.
    SqlError(SqlError),
    /// The database is outside the capacity domain.
    Capacity,
}

/// The supported statements: those well typed for the schema (a well-formed schema, a typed body and ORDER BY keys
/// that name output columns). Fixed by GenDB; it covers every constructor of the SQLSpec fragment, nested to any depth.
pub open spec fn supported(oq: OrderedQuery) -> bool {
    wf_ordered(schema_spec(), oq)
}

/// The generic capacity domain of a statement on a database (as in the query entries): every intermediate of the
/// canonical evaluation is machine representable, with SUM/AVG bounded by the absolute mass of each group.
pub open spec fn capacity_domain(db: Database, oq: OrderedQuery) -> bool {
    fits_query(db, Seq::empty(), oq.body)
}

/// `db` is a database of the schema, in the semantics' input domain, satisfying the declared integrity constraints
/// (over all of `db`'s tables and columns), whose stored relations the parts of every storage use represent.
pub open spec fn bound_db(sv: StoresView, db: Database) -> bool {
    &&& db.schema == schema_spec()
    &&& db_wf(db)
    &&& constraints_hold(declared_db(db))
    &&& stored_ok(sv, db)
}

/// The fixed meaning of an author answer for one database and one statement.
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

/// The engine author's obligation for stored parts `sv` and statement `oq`: the answer is correct for EVERY database
/// bound to the parts.
pub open spec fn answer_meets(sv: StoresView, oq: OrderedQuery, r: Result<Answer, QueryError>) -> bool {
    forall|db: Database| #[trigger] bound_db(sv, db) ==> outcome_ok(db, oq, r)
}

/// Precondition of an engine call: some database is bound to the stored parts (the trusted FFI assumption; discharged
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

/// The fixed meaning of a served status and rows for one database and one statement.
pub open spec fn served(db: Database, oq: OrderedQuery, r: StoredQueryReturn) -> bool {
    match r.result.status {
        AbiStatus::Ok => delivered_wf(r) && ordered_ok(db, oq, Ok::<Relation, SqlError>(delivered_rows(r))),
        AbiStatus::SqlError(e) => ordered_ok(db, oq, Err::<Relation, SqlError>(e)),
        AbiStatus::Capacity => !capacity_domain(db, oq),
        AbiStatus::WorkerFailed => true,
        _ => false,
    }
}

/// THE FIXED ENGINE CONTRACT: worker count outside the bound `Refused`; bytes that decode to no statement
/// `Malformed`; a decoded statement that is not supported `ParamRefused`; otherwise, for every database bound to the
/// stored parts, the result is served for the decoded statement.
pub open spec fn engine_meets(sv: StoresView, ast: Seq<u8>, workers: usize, r: StoredQueryReturn) -> bool {
    if !workers_ok(workers) {
        r.result.status is Refused
    } else {
        match decode_spec(ast) {
            None => r.result.status is Malformed,
            Some(oq) => if !supported(oq) {
                r.result.status is ParamRefused
            } else {
                forall|db: Database| #[trigger] bound_db(sv, db) ==> served(db, oq, r)
            },
        }
    }
}

/// An engine call's result, its columnar answer (`Some` exactly for an `Ok` columnar answer, whose `result.rows` is
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

/// Engine entry (one statement, given as AST bytes, over stored parts). `uses` holds the parts of every storage use, in
/// the use order of `stores::Stores`. Called by the trusted shim, which is trusted to meet `stores_ready`.
pub fn abi_engine_query(uses: Vec<Vec<Part>>, ast: &[u8], workers: usize) -> (r: StoredQueryReturn)
    requires
        uses.len() == STORAGE_USES,
        stores_ready(uses_view(uses@)),
    ensures
        engine_meets(uses_view(uses@), ast@, workers, r),
{
    let mut stores = open_stores(uses);
    let mut dispatch = Dispatch::new();
    if workers < 1 || workers > MAX_WORKERS {
        return finish(&stores, AbiStatus::Refused, Vec::new(), dispatch);
    }
    let q = match decode_query(ast) {
        Some(q) => q,
        None => return finish(&stores, AbiStatus::Malformed, Vec::new(), dispatch),
    };
    let schema = schema_exec();
    if !check_ordered(&schema, &q) {
        return finish(&stores, AbiStatus::ParamRefused, Vec::new(), dispatch);
    }
    proof {
        assert(view_schema(schema@) == schema_spec());
    }
    let answer = crate::agent::engine(&mut stores, &q, workers, &mut dispatch);
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

/// Echo entry: the echo text of the statement the bytes decode to (`(Malformed)` for none), in the evaluator's echo
/// grammar. The host compares it with its own rendering of the AST document it encoded (translation validation of the
/// host encoder). Reads no stored data.
pub fn abi_engine_echo(ast: &[u8]) -> (r: Vec<u8>)
    ensures
        r@ == render_spec(decode_spec(ast@)),
{
    let q = decode_query(ast);
    render_query(&q)
}

/// The end-to-end theorem in SQL terms, over the executed entry (`abi_engine_query`: its checked postcondition is the
/// premise `engine_meets`). `db` is any database of the schema in the semantics' input domain that satisfies the
/// declared constraints and whose stored relations the parts represent (`bound_db`). Called with bytes `ast` at
/// `workers` workers:
/// - `Malformed` exactly when the bytes decode to no statement;
/// - otherwise, with `oq` the decoded statement: `ParamRefused` exactly when it is not supported; `Ok` rows are an
///   allowed output of `oq` on `db`; `SqlError(e)` means the meaning of `oq` on `db` is exactly the error `e`;
///   `Capacity` means `db` is outside `capacity_domain`; no other status except a real worker failure.
pub proof fn theorem_engine_end_to_end(db: Database, sv: StoresView, ast: Seq<u8>, workers: usize, r: StoredQueryReturn)
    requires
        engine_meets(sv, ast, workers, r),
        workers_ok(workers),
        bound_db(sv, db),
    ensures
        stores_ready(sv),
        (r.result.status is Malformed) <==> decode_spec(ast) is None,
        decode_spec(ast) matches Some(oq) ==> {
            let s = r.result.status;
            &&& (s is ParamRefused <==> !supported(oq))
            &&& (s is Ok ==> delivered_wf(r) && ordered_ok(db, oq, Ok::<Relation, SqlError>(delivered_rows(r))))
            &&& (s matches AbiStatus::SqlError(e) ==> ordered_ok(db, oq, Err::<Relation, SqlError>(e))
                    && denote_body(db, oq) == Err::<Relation, SqlError>(e))
            &&& (s is Capacity ==> !capacity_domain(db, oq))
            &&& (s is Ok || s is SqlError || s is Capacity || s is WorkerFailed || s is ParamRefused)
        },
{
    if decode_spec(ast) is Some {
        let oq = decode_spec(ast)->Some_0;
        if supported(oq) {
            assert(served(db, oq, r));
        }
    }
}

/// Inside the capacity domain and without a worker failure, the status of a supported statement is decided by the SQL
/// meaning: `Ok` when the statement has a value on `db`, `SqlError(e)` exactly when its meaning is the error `e`.
pub proof fn corollary_inside_capacity(
    db: Database,
    sv: StoresView,
    ast: Seq<u8>,
    workers: usize,
    r: StoredQueryReturn,
    oq: OrderedQuery,
)
    requires
        engine_meets(sv, ast, workers, r),
        workers_ok(workers),
        bound_db(sv, db),
        decode_spec(ast) == Some(oq),
        supported(oq),
        capacity_domain(db, oq),
        !(r.result.status is WorkerFailed),
    ensures
        denote_body(db, oq) is Ok ==> r.result.status is Ok,
        denote_body(db, oq) matches Err(e) ==> r.result.status == AbiStatus::SqlError(e),
{
    theorem_engine_end_to_end(db, sv, ast, workers, r);
    if r.result.status is Ok {
        assert(ordered_ok(db, oq, Ok::<Relation, SqlError>(delivered_rows(r))));
    }
}

} // verus!
