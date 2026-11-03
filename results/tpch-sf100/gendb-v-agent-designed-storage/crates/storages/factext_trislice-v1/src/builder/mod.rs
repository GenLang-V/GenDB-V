//! Builder of storage `factext_trislice`: the 13 parts of `factext_trisig` are inherited unchanged; this builder adds
//! two U64 parts, signature words 0 and 1 of every orders row (part `ORDERS_SIG` of `factext_trisig`, read through
//! a StoredParts extent) bit-sliced into 64 planes each (`slices::slice_half`).
//!
//! Proof: for every database bound to the source, `factext_trisig`'s `represents` holds for the inherited parts; the
//! same definitions, restated in this storage's interface (`base_represents`, `sigs_ok`), follow by unfolding
//! (`equiv`), and each plane bit is the row's signature bit (`slice_half`).
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{PartView, owned_parts_view};
use crate::gendb_entry::parallel::Dispatch;
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::gendb_entry::storage::{represents, stored_relations};
use crate::spec::value::Database;
use crate::stores::factext_trislice::interface::common::colfmt::u64s;
use crate::stores::factext_trislice::interface::{slices_ok, slice_half_ok, sigs_ok, ORDERS_SIG, ORDERS_SLICES0,
    FACTEXT_PARTS, FACTEXT_TRISIG_PARTS};

pub mod equiv;
pub mod slices;

verus! {

/// Build the two slice parts (the inherited parts of `factext_trisig` come first, unchanged).
pub fn build(stores: &mut Stores, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        sources_ready(old(stores)@),
        1 <= workers <= crate::gendb_entry::parallel::MAX_WORKERS,
    ensures
        match r {
            Ok(p) => forall|db: Database| #[trigger] sources_bound(old(stores)@, db)
                ==> represents(storage_parts(old(stores)@, owned_parts_view(p@)), stored_relations(db)),
            Err(QueryError::WorkerFailed(_)) => true,
            Err(_) => false,
        },
{
    let ghost sv = stores@;
    let ghost db0 = choose|db: Database| #[trigger] sources_bound(sv, db);
    proof {
        equiv::lemma_base_copy(sv, db0);
    }
    let sig_len = stores.factext_trisig.part_len(ORDERS_SIG);
    let sig = stores.factext_trisig.extent_u64(ORDERS_SIG, 0, sig_len);
    proof {
        assert(sig@ =~= u64s(sv.factext_trisig[ORDERS_SIG as int]));
    }
    let n = sig_len / 2;
    assert(sig@.len() == 2 * n) by {
        assert(sig@.len() == 2 * stored_relations(db0)[1].len());
    }
    let s0 = slices::slice_half(sig, sig_len, n, 0);
    let s1 = slices::slice_half(sig, sig_len, n, 1);
    let mut out: Vec<OwnedPart> = Vec::new();
    out.push(OwnedPart::U64(s0));
    out.push(OwnedPart::U64(s1));
    proof {
        let built = owned_parts_view(out@);
        assert(built.len() == 2);
        assert(built[0] == PartView::U64(s0@));
        assert(built[1] == PartView::U64(s1@));
        assert forall|db: Database| #[trigger] sources_bound(sv, db)
            implies represents(storage_parts(sv, built), stored_relations(db)) by {
            equiv::lemma_base_copy(sv, db);
            let rels = stored_relations(db);
            let parts = storage_parts(sv, built);
            assert(parts =~= sv.factext_trisig.push(PartView::U64(s0@)).push(PartView::U64(s1@)));
            assert(parts.subrange(0, FACTEXT_PARTS as int) =~= sv.factext_trisig.subrange(0, FACTEXT_PARTS as int));
            assert(rels[1].len() == n) by {
                assert(u64s(sv.factext_trisig[ORDERS_SIG as int]).len() == 2 * rels[1].len());
            }
            assert(parts[ORDERS_SIG as int] == sv.factext_trisig[ORDERS_SIG as int]);
            assert(parts[10] == sv.factext_trisig[10]);
            assert(parts[11] == sv.factext_trisig[11]);
            assert(sigs_ok(parts, rels[1].len() as int));
            assert(parts[ORDERS_SLICES0 as int] == PartView::U64(s0@));
            assert(parts[ORDERS_SLICES0 as int + 1] == PartView::U64(s1@));
            assert(slice_half_ok(parts, n as int, 0));
            assert(slice_half_ok(parts, n as int, 1));
            assert(slices_ok(parts, rels[1].len() as int));
        }
    }
    Ok(out)
}

} // verus!
