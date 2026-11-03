//! Builder of storage `factext_trisig`: the parts of `factext` are inherited unchanged; this builder adds one U64
//! part, the trigram signature (`trisig::sig_of`) of o_comment of every canonical orders row, computed from the
//! o_comment offsets and bytes parts of `factext` (read through StoredParts extents).
//!
//! Proof: for every database bound to the source, `factext`'s `represents` holds for the inherited parts; the same
//! definitions, restated in this storage's interface (`base_represents`), follow by unfolding (`equiv`), and each
//! computed signature is `sig_of` of the row's text (`sig_of_exec`).
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::layout::{PartView, owned_parts_view};
use crate::gendb_entry::parallel::Dispatch;
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::sources::{Stores, stored_ok, StoresView};
use crate::gendb_entry::derivation::inherited;
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::gendb_entry::storage::{represents, stored_relations};
use crate::spec::value::Database;
use crate::stores::factext_trisig::interface::trisig::*;
use crate::stores::factext_trisig::interface::common::colfmt::{text_of, text_range_ok, text_parts_wf, u64s, u8s};
use crate::stores::factext_trisig::interface::{comment_at, sigs_ok, O_COMMENT_OFFS_PART, O_COMMENT_BYTES_PART,
    ORDERS_SIG, FACTEXT_PARTS, FACTEXT_TRISIG_PARTS};

pub mod equiv;

verus! {

/// Both words of `sig_of(bytes[lo..hi])`.
pub fn sig_of_exec(bytes: &[u8], lo: usize, hi: usize) -> (r: (u64, u64))
    requires
        lo <= hi <= bytes@.len(),
    ensures
        r.0 == sig_of(bytes@.subrange(lo as int, hi as int), 0),
        r.1 == sig_of(bytes@.subrange(lo as int, hi as int), 1),
{
    let ghost t = bytes@.subrange(lo as int, hi as int);
    let len = hi - lo;
    let cnt: usize = if len >= 3 { len - 2 } else { 0 };
    assert(cnt as int == tri_count(t));
    let mut acc0: u64 = 0;
    let mut acc1: u64 = 0;
    let mut k: usize = 0;
    while k < cnt
        invariant
            lo <= hi <= bytes@.len(),
            t == bytes@.subrange(lo as int, hi as int),
            len == hi - lo,
            cnt as int == tri_count(t),
            k <= cnt,
            acc0 == sig_upto(t, k as int, 0),
            acc1 == sig_upto(t, k as int, 1),
        decreases cnt - k,
    {
        assert(t[k as int] == bytes@[lo + k]);
        assert(t[k as int + 1] == bytes@[lo + k + 1]);
        assert(t[k as int + 2] == bytes@[lo + k + 2]);
        let (b0, b1) = tri_bits_exec(bytes[lo + k], bytes[lo + k + 1], bytes[lo + k + 2]);
        acc0 = acc0 | b0;
        acc1 = acc1 | b1;
        k = k + 1;
    }
    (acc0, acc1)
}

/// The signatures of every orders row of the source (`offs`: `n + 1` offsets, `bytes`: the o_comment bytes), two
/// words per row.
fn all_sigs(offs: &[u64], bytes: &[u8], n: usize) -> (v: Vec<u64>)
    requires
        offs@.len() == n + 1,
        text_parts_wf(offs@, bytes@, n as int),
    ensures
        v@.len() == 2 * n,
        forall|r: int| 0 <= r < n ==> {
            &&& #[trigger] v@[2 * r] == sig_of(text_of(offs@, bytes@, r), 0)
            &&& v@[2 * r + 1] == sig_of(text_of(offs@, bytes@, r), 1)
        },
{
    let mut v: Vec<u64> = Vec::new();
    let blen = bytes.len();
    let mut r: usize = 0;
    while r < n
        invariant
            offs@.len() == n + 1,
            text_parts_wf(offs@, bytes@, n as int),
            r <= n,
            blen == bytes@.len(),
            v@.len() == 2 * r,
            forall|q: int| 0 <= q < r ==> {
                &&& #[trigger] v@[2 * q] == sig_of(text_of(offs@, bytes@, q), 0)
                &&& v@[2 * q + 1] == sig_of(text_of(offs@, bytes@, q), 1)
            },
        decreases n - r,
    {
        assert(text_range_ok(offs@, bytes@, r as int));
        assert(offs@[r as int] <= offs@[r as int + 1] <= blen);
        let lo = offs[r] as usize;
        let hi = offs[r + 1] as usize;
        assert(lo as int == offs@[r as int] && hi as int == offs@[r as int + 1]);
        let (s0, s1) = sig_of_exec(bytes, lo, hi);
        let ghost old_v = v@;
        v.push(s0);
        v.push(s1);
        proof {
            assert(v@[2 * r] == sig_of(text_of(offs@, bytes@, r as int), 0));
            assert(v@[2 * r + 1] == sig_of(text_of(offs@, bytes@, r as int), 1));
            assert forall|q: int| 0 <= q < r + 1 implies {
                &&& #[trigger] v@[2 * q] == sig_of(text_of(offs@, bytes@, q), 0)
                &&& v@[2 * q + 1] == sig_of(text_of(offs@, bytes@, q), 1)
            } by {
                if q < r {
                    assert(v@[2 * q] == old_v[2 * q]);
                    assert(v@[2 * q + 1] == old_v[2 * q + 1]);
                }
            }
        }
        r = r + 1;
    }
    v
}

/// Build the signature part (the inherited parts of `factext` come first, unchanged).
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
        equiv::lemma_source_facts(sv, db0);
    }
    let offs_len = stores.factext.part_len(O_COMMENT_OFFS_PART);
    let bytes_len = stores.factext.part_len(O_COMMENT_BYTES_PART);
    let offs = stores.factext.extent_u64(O_COMMENT_OFFS_PART, 0, offs_len);
    let bytes = stores.factext.extent_u8(O_COMMENT_BYTES_PART, 0, bytes_len);
    proof {
        assert(offs@ =~= u64s(sv.factext[O_COMMENT_OFFS_PART as int]));
        assert(bytes@ =~= u8s(sv.factext[O_COMMENT_BYTES_PART as int]));
    }
    let n = offs_len - 1;
    let sigs = all_sigs(offs, bytes, n);
    let mut out: Vec<OwnedPart> = Vec::new();
    out.push(OwnedPart::U64(sigs));
    proof {
        let built = owned_parts_view(out@);
        assert(built.len() == 1);
        assert(built[0] == PartView::U64(sigs@));
        assert forall|db: Database| #[trigger] sources_bound(sv, db)
            implies represents(storage_parts(sv, built), stored_relations(db)) by {
            equiv::lemma_source_facts(sv, db);
            let parts = storage_parts(sv, built);
            assert(parts =~= sv.factext.push(PartView::U64(sigs@)));
            assert(parts.subrange(0, FACTEXT_PARTS as int) =~= sv.factext);
            equiv::lemma_base_copy(sv, db);
            assert forall|r: int| 0 <= r < stored_relations(db)[1].len() implies {
                &&& #[trigger] u64s(parts[ORDERS_SIG as int])[2 * r] == sig_of(comment_at(parts, r), 0)
                &&& u64s(parts[ORDERS_SIG as int])[2 * r + 1] == sig_of(comment_at(parts, r), 1)
            } by {
                assert(parts[O_COMMENT_OFFS_PART as int] == sv.factext[O_COMMENT_OFFS_PART as int]);
                assert(parts[O_COMMENT_BYTES_PART as int] == sv.factext[O_COMMENT_BYTES_PART as int]);
                assert(u64s(parts[ORDERS_SIG as int]) == sigs@);
                assert(comment_at(parts, r) == text_of(offs@, bytes@, r));
                assert(sigs@[2 * r] == sig_of(text_of(offs@, bytes@, r), 0));
            }
            assert(u64s(parts[ORDERS_SIG as int]) == sigs@);
            assert(sigs@.len() == 2 * stored_relations(db)[1].len());
            assert(sigs_ok(parts, stored_relations(db)[1].len() as int));
        }
    }
    Ok(out)
}

} // verus!
