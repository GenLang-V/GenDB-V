// FRAMEWORK FILE: the fixed storage entry of a GenDB storage crate built from admitted storages (identity
// `gendb-verus-storage-entry-derived-v1`; source `verification/obligations/storage_entry_derived.rs`, assembled as
// `crate::gendb_entry` by `gendb_verification::obligations` for a storage manifest with `built_from`).
//
// A derived storage crate checks one new storage `S` whose builder reads ADMITTED storages (its sources) instead of
// source columns: their stored parts, through their own interfaces' readers (`crate::stores::<source>::interface`,
// copied byte for byte from each source's checked build, read-only here). Generated from data only: the dataset schema
// (`crate::schema`), the declarations of `S` and of every source (`crate::stores::*::declaration`), the source handles
// (`gendb_entry/sources.rs`, generated as the query crates' `gendb_entry/stores.rs`), the binding to `S` (`gendb_entry/storage.rs`) and the derivation
// (`gendb_entry/derivation.rs`: the parts `S` inherits unchanged from one source, and whether the builder assumes the
// run's declared integrity constraints). Authors cannot edit any of them. Checked by Verus with `--no-cheating`.
//
// The claim. For EVERY database `db` of the schema in the semantics' input domain whose stored relations the parts of
// every source represent (`sources_bound`; under the opt-in also satisfying the declared constraints), the parts of `S` -
// the inherited parts followed by the builder's parts - represent `S`'s stored relations of `db`
// (`derived_build_meets`, `theorem_storage_built`). The proof chains: for the actual database, each source's admitted
// `theorem_storage_built` gives `stored_ok` (the old `represents` of every source), the builder's proof gives the new
// `represents`; `S`'s conclusion is then, per storage use, exactly the premise of the query entries, as for every
// storage. No source column is read, so a derived storage can be built after the original input is deleted.
//
// Data path. `abi_build_derived_storage` requires `sources_ready`: some database is bound to the source parts. That
// precondition is the trusted assumption at the FFI boundary (every source's parts are the parts its admitted build
// returned for the same capture, unchanged), as for query calls. The host writes the inherited parts as the source's
// own part files, unchanged (hard links), before the builder's parts (trusted storage round trip).
//
// Names. Every public name of this entry root and of `sources.rs` differs from the query entry's (`sources_bound`, not
// `bound_db`; `gendb_entry::sources`, not `gendb_entry::stores`), so the new storage's interface, which query crates
// carry byte for byte, cannot name an item that would resolve to another definition there: such a name fails to
// compile in one of the two crates (the closure basis of `obligations::closure`).
//
// Statuses: `Refused` (worker count outside 1..=MAX_WORKERS), `WorkerFailed` only with the runtime's private token,
// `Ok`. Nothing else: on bound sources the builder never fails otherwise. Partial correctness: an unwind on the
// calling thread aborts the process in the shim.
use vstd::prelude::*;
use crate::gendb_abi::{AbiStatus, BuildReturn, DispatchEvidence, Part};
use crate::schema::schema_spec;
use crate::spec::value::Database;
use crate::spec::typing::db_wf;

pub mod derivation;
pub mod layout;
pub mod parallel;
pub mod runtime;
pub mod source_check;
pub mod storage;
pub mod stored;
pub mod sources;
pub mod work;

use derivation::{assumed, inherited};
use layout::{owned_parts_view, parts_view, PartView};
use parallel::{Dispatch, MAX_WORKERS};
use runtime::QueryError;
use storage::{represents, stored_relations};
use sources::{open_stores, stored_ok, uses_view, StoresView, STORAGE_USES};

verus! {

/// Worker counts a build accepts.
pub open spec fn build_workers_ok(workers: usize) -> bool {
    1 <= workers <= MAX_WORKERS
}

/// `db` is a database of the schema, in the semantics' input domain (and, under the opt-in, satisfying the declared
/// constraints), whose stored relations the parts of every source storage represent.
pub open spec fn sources_bound(sv: StoresView, db: Database) -> bool {
    &&& db.schema == schema_spec()
    &&& db_wf(db)
    &&& assumed(db)
    &&& stored_ok(sv, db)
}

/// Precondition of the build: some database is bound to the source parts (the trusted FFI assumption, discharged by
/// the sources' admitted builds for the actual database).
pub open spec fn sources_ready(sv: StoresView) -> bool {
    exists|db: Database| #[trigger] sources_bound(sv, db)
}

/// The parts of the new storage: the inherited parts of the sources (`derivation::inherited`), then `built`.
pub open spec fn storage_parts(sv: StoresView, built: Seq<PartView>) -> Seq<PartView> {
    inherited(sv) + built
}

/// Fixed builder contract. Worker-count mismatch: `Refused`. Otherwise `Ok` exactly with parts such that, for every
/// database bound to the sources, the new storage's parts represent its stored relations; `WorkerFailed` only from a
/// failed join of a `no_unwind` worker; nothing else.
pub open spec fn derived_build_meets(sv: StoresView, workers: usize, r: BuildReturn) -> bool {
    if !build_workers_ok(workers) {
        r.status is Refused
    } else {
        match r.status {
            AbiStatus::Ok => forall|db: Database| #[trigger] sources_bound(sv, db) ==> represents(storage_parts(sv, owned_parts_view(r.parts@)), stored_relations(db)),
            AbiStatus::WorkerFailed => true,
            _ => false,
        }
    }
}

fn evidence(d: Dispatch) -> DispatchEvidence {
    let (spawned, joined, ranges) = d.into_parts();
    DispatchEvidence { spawned, joined, ranges }
}

/// Derived storage build entry (offline, once per source capture). `uses` holds the parts of every source, in the
/// use order of `sources::Stores`. Called by the trusted shim, which is trusted to meet `sources_ready`.
pub fn abi_build_derived_storage(uses: Vec<Vec<Part>>, workers: usize) -> (r: BuildReturn)
    requires
        uses.len() == STORAGE_USES,
        sources_ready(uses_view(uses@)),
    ensures
        derived_build_meets(uses_view(uses@), workers, r),
{
    let mut stores = open_stores(uses);
    let mut dispatch = Dispatch::new();
    if workers < 1 || workers > MAX_WORKERS {
        return BuildReturn { status: AbiStatus::Refused, parts: Vec::new(), dispatch: evidence(dispatch) };
    }
    let (status, parts) = match crate::builder::build(&mut stores, workers, &mut dispatch) {
        Ok(p) => (AbiStatus::Ok, p),
        Err(QueryError::InvalidInput) => (AbiStatus::InvalidInput, Vec::new()),
        Err(QueryError::Malformed) => (AbiStatus::Malformed, Vec::new()),
        Err(QueryError::WorkerFailed(_)) => (AbiStatus::WorkerFailed, Vec::new()),
    };
    BuildReturn { status, parts, dispatch: evidence(dispatch) }
}

/// A successful build, stored after the inherited parts and read back unchanged (the trusted round trip
/// `parts_view(stored) == storage_parts(sv, owned_parts_view(built.parts@))`), represents the stored relations of every
/// database bound to the sources: for the actual database, the conjunction of the sources' `theorem_storage_built`.
pub proof fn theorem_storage_built(db: Database, sv: StoresView, workers: usize, built: BuildReturn, stored: Seq<Part>)
    requires
        derived_build_meets(sv, workers, built),
        built.status is Ok,
        parts_view(stored) == storage_parts(sv, owned_parts_view(built.parts@)),
        sources_bound(sv, db),
    ensures
        represents(parts_view(stored), stored_relations(db)),
{
}

/// On bound sources the build reports only `Ok` or a real worker failure.
pub proof fn theorem_storage_build_total(sv: StoresView, workers: usize, built: BuildReturn)
    requires
        derived_build_meets(sv, workers, built),
        build_workers_ok(workers),
    ensures
        built.status is Ok || built.status is WorkerFailed,
{
}

} // verus!
