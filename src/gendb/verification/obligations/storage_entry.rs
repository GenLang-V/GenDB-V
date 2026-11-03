// FRAMEWORK FILE: the fixed storage entry of every GenDB storage crate (identity `gendb-verus-storage-entry-v1`;
// source `verification/obligations/storage_entry.rs`, assembled as `crate::gendb_entry` by
// `gendb_verification::obligations`).
//
// A storage crate checks one storage `S`: the author's representation relation and readers
// (`crate::stores::S::interface`, copied byte for byte into every query crate that reads `S`) and builder
// (`crate::builder`, in this crate only). Generated from data only: the dataset schema (`crate::schema`), the storage
// declaration (`crate::stores::S::declaration`: which columns of which tables `S` stores), the delivered source
// (`crate::gendb_source`, `gendb_entry/binder.rs`) and the binding `gendb_entry/storage.rs`. Authors cannot edit
// any of them. Checked by Verus with `--no-cheating` with the SQLSpec library; no `assume`, `admit` or `external_body`.
//
// The claim. The builder receives the delivered columns of the declared tables (`gendb_source::tables(v)`, one
// relation per table, in canonical row order) inside the declared column domain, which this entry decides before the
// builder runs. On `Ok` its parts represent exactly those relations under the author's relation `represents`
// (`storage_build_meets`). For every database `db` of the schema in the semantics' input domain whose tables the
// delivered columns are (the trusted source binding), the stored parts, read back unchanged (the trusted storage
// round trip), represent `stored_relations(db)`: the declared columns of `db`'s tables (`theorem_storage_built`).
// That conclusion is, per storage use, exactly the premise `stored_ok` of the query entry v4 (a conjunct of its
// `bound_db`). On such a database the builder never reports `InvalidInput` (`theorem_storage_build_total`), so the
// relation must be satisfiable by the real data: an unsatisfiable `represents` makes the builder unprovable, never an
// asset.
//
// Statuses: `Refused` (worker count outside 1..=MAX_WORKERS or columns the binder does not accept), `InvalidInput`
// exactly outside the declared column domain, `WorkerFailed` only with the runtime's private token (a failed join of
// a `no_unwind` worker; excluded by the trusted assumption `worker_failure`), `Ok`. Nothing else. The theorems state
// what a returned status means (partial correctness). Verus's termination checks add that, under the trusted
// assumptions, every call ends with exactly one of these statuses (the proved property `termination`,
// `verification/src/obligations/claim.rs`): total correctness relative to this contract. A process abort (allocation
// failure, stack exhaustion, failed thread creation, or an unwind on the calling thread, which the shim turns into an
// abort) ends a call with no status; only the trusted assumption `calling_thread_progress` excludes it.
use vstd::prelude::*;
use crate::gendb_abi::{AbiStatus, BuildReturn, Column, DispatchEvidence, Part};
use crate::gendb_source::{in_domain, lemma_source_in_domain, source_columns_are_tables, source_in_domain, tables, SourceView};
use crate::schema::schema_spec;
use crate::spec::value::Database;
use crate::spec::typing::db_wf;

pub mod binder;
pub mod layout;
pub mod parallel;
pub mod runtime;
pub mod source_check;
pub mod storage;
pub mod stored;
pub mod work;

use binder::{bind_source, column_source};
use layout::{owned_parts_view, parts_view};
use parallel::{Dispatch, MAX_WORKERS};
use runtime::QueryError;
use storage::{lemma_source_is_stored, represents, stored_relations};

verus! {

/// Worker counts a build accepts.
pub open spec fn build_workers_ok(workers: usize) -> bool {
    1 <= workers <= MAX_WORKERS
}

/// The source view the binder reads from `columns` (meaningful when `column_source(columns) is Some`).
pub open spec fn delivered_source(columns: Seq<Column>) -> SourceView {
    column_source(columns)->Some_0
}

/// Fixed builder contract. Shape or worker-count mismatch: `Refused`. Otherwise, for the delivered source `v`: `Ok`
/// exactly with parts that represent `tables(v)`; `InvalidInput` only outside the declared column domain;
/// `WorkerFailed` only from a failed join of a `no_unwind` worker.
pub open spec fn storage_build_meets(columns: Seq<Column>, workers: usize, r: BuildReturn) -> bool {
    if !build_workers_ok(workers) || column_source(columns) is None {
        r.status is Refused
    } else {
        let v = delivered_source(columns);
        match r.status {
            AbiStatus::Ok => represents(owned_parts_view(r.parts@), tables(v)),
            AbiStatus::InvalidInput => !in_domain(tables(v)),
            AbiStatus::WorkerFailed => true,
            _ => false,
        }
    }
}

fn evidence(d: Dispatch) -> DispatchEvidence {
    let (spawned, joined, ranges) = d.into_parts();
    DispatchEvidence { spawned, joined, ranges }
}

/// Storage build entry (offline, once per source capture). Called by the trusted shim.
pub fn abi_build_storage(columns: &[Column], workers: usize) -> (r: BuildReturn)
    ensures storage_build_meets(columns@, workers, r),
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
    let (status, parts) = match crate::builder::build(&src, workers, &mut dispatch) {
        Ok(p) => (AbiStatus::Ok, p),
        Err(QueryError::InvalidInput) => (AbiStatus::InvalidInput, Vec::new()),
        Err(QueryError::Malformed) => (AbiStatus::Malformed, Vec::new()),
        Err(QueryError::WorkerFailed(_)) => (AbiStatus::WorkerFailed, Vec::new()),
    };
    BuildReturn { status, parts, dispatch: evidence(dispatch) }
}

/// A successful build, stored and read back unchanged (the trusted round trip `parts_view(stored) ==
/// owned_parts_view(built.parts@)`), represents the stored relations of every database of the schema in the input
/// domain whose tables the delivered columns are (the trusted source binding).
pub proof fn theorem_storage_built(db: Database, columns: Seq<Column>, workers: usize, built: BuildReturn, stored: Seq<Part>)
    requires
        storage_build_meets(columns, workers, built),
        built.status is Ok,
        parts_view(stored) == owned_parts_view(built.parts@),
        db.schema == schema_spec(),
        db_wf(db),
        source_columns_are_tables(delivered_source(columns), db),
    ensures
        represents(parts_view(stored), stored_relations(db)),
{
    lemma_source_is_stored(delivered_source(columns), db);
}

/// On the real source tables the build never reports `InvalidInput`: the delivered columns of a `db_wf` database are
/// in the declared column domain.
pub proof fn theorem_storage_build_total(db: Database, columns: Seq<Column>, workers: usize, built: BuildReturn)
    requires
        storage_build_meets(columns, workers, built),
        build_workers_ok(workers),
        column_source(columns) is Some,
        db.schema == schema_spec(),
        db_wf(db),
        source_columns_are_tables(delivered_source(columns), db),
    ensures
        built.status is Ok || built.status is WorkerFailed,
{
    lemma_source_in_domain(db, delivered_source(columns));
}

} // verus!
