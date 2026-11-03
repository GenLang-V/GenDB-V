// Framework test fixture (redesign S1; hand-written framework test input, not an author output, not a TPC-H storage):
// the builder of storage `sensor_copy`, built from the admitted storage `sensor_days` (derived storage entry) and
// extending it: every part of `sensor_days` is inherited unchanged, and the builder adds no part. Its interface is
// `sensor_days`'s text (the same parts, the same relation over the same declared columns), so the proof is the chain
// "old represents + unchanged parts => new represents".
use vstd::prelude::*;
use crate::spec::value::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{owned_parts_view, PartView};
use crate::gendb_entry::parallel::Dispatch;
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::Stores;
use crate::gendb_entry::{sources_bound, storage_parts};

verus! {

pub fn build(stores: &mut Stores, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    ensures
        r is Ok,
        r matches Ok(p) ==> forall|db: Database| #[trigger] sources_bound(old(stores)@, db) ==> crate::stores::sensor_copy::interface::represents(
            storage_parts(old(stores)@, owned_parts_view(p@)),
            crate::stores::sensor_copy::declaration::stored_relations(db),
        ),
{
    let parts: Vec<OwnedPart> = Vec::new();
    proof {
        let sv = old(stores)@;
        assert(owned_parts_view(parts@) =~= Seq::<PartView>::empty());
        assert forall|db: Database| #[trigger] sources_bound(sv, db) implies crate::stores::sensor_copy::interface::represents(
            storage_parts(sv, owned_parts_view(parts@)),
            crate::stores::sensor_copy::declaration::stored_relations(db),
        ) by {
            assert(storage_parts(sv, owned_parts_view(parts@)) =~= sv.sensor_days);
            assert(crate::stores::sensor_copy::declaration::stored_relations(db) =~= crate::stores::sensor_days::declaration::stored_relations(db));
        }
    }
    Ok(parts)
}

} // verus!
