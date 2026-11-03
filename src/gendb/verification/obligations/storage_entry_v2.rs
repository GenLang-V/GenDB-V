// FRAMEWORK FILE: the fixed storage entry v2 of a GenDB storage crate whose builder assumes the declared integrity
// constraints (identity `gendb-verus-storage-entry-v2`; source `verification/obligations/storage_entry_v2.rs`, assembled
// as `crate::gendb_entry` by `gendb_verification::obligations` for a storage manifest that opts in with
// `uses_declared_constraints` in a run that declares constraints).
//
// The storage entry v1 with exactly one more hypothesis, everything else unchanged: the delivered source comes from a
// full database of the schema that satisfies the run's declared constraints (`source_witnessed`; the declarations are
// the generated `crate::gendb_constraints`, never the author's). `abi_build_storage` requires it, so the builder may
// require it too; the builder may use the constraints only through that full witness (`choose`), transferring facts
// to the delivered columns by row position and stored column. No constraint is stated about the projection itself.
// The output relation, the statuses and the claim `storage_build_meets` are those of v1, and the theorems take the
// declared constraints of `db` as one more premise, so the dependence is visible where they are composed: the host
// asserts that the actual database is that witness (trusted assumption `declared_integrity_constraints`, the user's
// declaration, never checked against the data). A package of this entry records the exact declaration set and is
// built, offered and composed only under it.
//
// The rest as in v1: a storage crate checks one storage `S`: the author's representation relation and readers
// (`crate::stores::S::interface`, copied byte for byte into every query crate that reads `S`) and builder
// (`crate::builder`, in this crate only). Generated from data only: the dataset schema (`crate::schema`), the declared
// constraints (`crate::gendb_constraints`), the storage declaration (`crate::stores::S::declaration`: which columns of
// which tables `S` stores), the delivered source (`crate::gendb_source`, `gendb_entry/binder.rs`) and the binding
// `gendb_entry/storage.rs`. Authors cannot edit any of them. Checked by Verus with `--no-cheating` with the SQLSpec
// library; no `assume`, `admit` or `external_body`.
//
// The claim. The builder receives the delivered columns of the declared tables (`gendb_source::tables(v)`, one
// relation per table, in canonical row order) inside the declared column domain, which this entry decides before the
// builder runs, delivered from a database satisfying the declared constraints. On `Ok` its parts represent exactly
// those relations under the author's relation `represents` (`storage_build_meets`). For every database `db` of the
// schema in the semantics' input domain satisfying the declared constraints whose tables the delivered columns are (the
// trusted source binding), the stored parts, read back unchanged (the trusted storage round trip), represent
// `stored_relations(db)`: the declared columns of `db`'s tables (`theorem_storage_built`). That conclusion is, per
// storage use, exactly the premise `stored_ok` of the query entry v5 (whose `bound_db` assumes the same declarations).
// On such a database the builder never reports `InvalidInput` (`theorem_storage_build_total`), so the relation must be
// satisfiable by the real data: an unsatisfiable `represents` makes the builder unprovable, never an asset.
//
// Statuses: `Refused` (worker count outside 1..=MAX_WORKERS or columns the binder does not accept), `InvalidInput`
// exactly outside the declared column domain, `WorkerFailed` only with the runtime's private token (a failed join of
// a `no_unwind` worker; excluded by the trusted assumption `worker_failure`), `Ok`. Nothing else. The theorems state
// what a returned status means (partial correctness). Verus's termination checks add that, under the trusted
// assumptions, every call ends with exactly one of these statuses (the proved property `termination`,
// `verification/src/obligations/claim.rs`): total correctness relative to this contract. A process abort (allocation
// failure, stack exhaustion, failed thread creation, or an unwind on the calling thread, which the shim turns into an
// abort) ends a call with no status; only the trusted assumption `calling_thread_progress` excludes it. If the
// declared constraints do not hold on the actual data, nothing is claimed for it.
use vstd::prelude::*;
use crate::gendb_abi::{AbiStatus, BuildReturn, Column, DispatchEvidence, Part};
use crate::gendb_source::{in_domain, lemma_source_in_domain, source_columns_are_tables, source_in_domain, tables, SourceView};
use crate::schema::schema_spec;
use crate::spec::value::Database;
use crate::spec::typing::db_wf;
use crate::gendb_constraints::declared_db;
use crate::spec::constraints::constraints_hold;

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

/// Some full database of the schema, in the semantics' input domain and satisfying the declared integrity constraints
/// (`constraints_hold(declared_db(db))`: over all of its tables and columns), delivers `v` under the source binding.
/// The builder may use the constraints only through such a witness, by row position and delivered column.
pub open spec fn source_witnessed(v: SourceView) -> bool {
    exists|db: Database|
        db.schema == schema_spec() && db_wf(db) && constraints_hold(declared_db(db)) && #[trigger] source_columns_are_tables(v, db)
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
    requires column_source(columns@) is Some ==> source_witnessed(delivered_source(columns@)),
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
/// domain satisfying the declared constraints whose tables the delivered columns are (the trusted source binding).
pub proof fn theorem_storage_built(db: Database, columns: Seq<Column>, workers: usize, built: BuildReturn, stored: Seq<Part>)
    requires
        storage_build_meets(columns, workers, built),
        built.status is Ok,
        parts_view(stored) == owned_parts_view(built.parts@),
        db.schema == schema_spec(),
        db_wf(db),
        constraints_hold(declared_db(db)),
        source_columns_are_tables(delivered_source(columns), db),
    ensures
        represents(parts_view(stored), stored_relations(db)),
{
    lemma_source_is_stored(delivered_source(columns), db);
}

/// On the real source tables the build never reports `InvalidInput`: the delivered columns of a `db_wf` database
/// satisfying the declared constraints are in the declared column domain.
pub proof fn theorem_storage_build_total(db: Database, columns: Seq<Column>, workers: usize, built: BuildReturn)
    requires
        storage_build_meets(columns, workers, built),
        build_workers_ok(workers),
        column_source(columns) is Some,
        db.schema == schema_spec(),
        db_wf(db),
        constraints_hold(declared_db(db)),
        source_columns_are_tables(delivered_source(columns), db),
    ensures
        built.status is Ok || built.status is WorkerFailed,
{
    lemma_source_in_domain(db, delivered_source(columns));
}

} // verus!
