//! Builder of storage `sub_sic`: keeps the 46 parts of storage `sub_fy` (inherited, linked unchanged) and adds one
//! part, `sic_order`: the row positions sorted by `(sic word, cik word, 0, row)` (`interface::sic_key`).
//! One `Key4` per row is read from sub_fy's `sic`, `sic` validity and `cik` parts, the keys are sorted by a parallel
//! merge sort, and the rows of the sorted keys form the permutation. The proof: the keys' rows are `0..n` (so the
//! sorted rows are a permutation), and each sorted key is the key of its row (so the permutation is sorted by
//! `sic_key`); the inherited parts carry sub_fy's `represents` over to `sub_sic`'s.
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::layout::{owned_parts_view, PartView};
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::spec::value::Database;
use crate::stores::sub_fy::interface as src;
use crate::stores::sub_sic::interface as dst;
use crate::stores::sub_sic::interface::common::perm::{ident, is_permutation, lemma_multiset_map};
pub mod common;
use common::sort::{par_sort, Key4, KeyOrder, SortOrder, sorted_by, all_ok};

verus! {

broadcast use {vstd::seq_lib::group_to_multiset_ensures, vstd::multiset::group_multiset_axioms};

/// The sort key of row `i` of the (inherited) parts `sp`, as a `Key4`.
pub open spec fn key_of(sp: Seq<PartView>, i: int) -> Key4 {
    let k = dst::sic_key(sp, i);
    Key4 { k0: k.0, k1: k.1, k2: k.2, k3: k.3 }
}

/// The row of a key.
pub open spec fn key_row(e: Key4) -> u64 {
    e.k3
}

/// Some database is bound to the source: sub_fy's layout holds.
proof fn lemma_source_layout(sv: StoresView)
    requires sources_ready(sv),
    ensures src::sub_layout_ok(sv.sub_fy),
{
    let db = choose|db: Database| #[trigger] sources_bound(sv, db);
}

/// The rows of the sorted keys are a permutation of `0..n`, sorted by `sic_key`.
proof fn lemma_order_ok(sp: Seq<PartView>, kv: Seq<Key4>, s: Seq<Key4>, ord: Seq<u64>, n: nat)
    requires
        n <= u64::MAX,
        kv.len() == n,
        forall|k: int| 0 <= k < n ==> #[trigger] kv[k] == key_of(sp, k),
        sorted_by(KeyOrder {}, s),
        s.to_multiset() == kv.to_multiset(),
        ord == s.map_values(|e: Key4| key_row(e)),
    ensures
        ord.len() == n,
        is_permutation(ord, n),
        forall|a: int, b: int| 0 <= a < b < n
            ==> dst::key_le(dst::sic_key(sp, #[trigger] ord[a] as int), dst::sic_key(sp, #[trigger] ord[b] as int)),
{
    assert(s.len() == s.to_multiset().len());
    assert(kv.len() == kv.to_multiset().len());
    assert(kv.map_values(|e: Key4| key_row(e)) =~= ident(n));
    lemma_multiset_map(s, kv, |e: Key4| key_row(e));
    // Every sorted key is the key of its own row.
    assert forall|a: int| 0 <= a < n implies #[trigger] s[a] == key_of(sp, ord[a] as int) && ord[a] < n by {
        assert(s.contains(s[a]));
        assert(s.to_multiset().count(s[a]) > 0);
        assert(kv.to_multiset().count(s[a]) > 0);
        assert(kv.contains(s[a]));
        let k = choose|k: int| 0 <= k < kv.len() && kv[k] == s[a];
        assert(kv[k] == key_of(sp, k));
        assert(ord[a] == s[a].k3);
        assert(k as u64 == s[a].k3);
    }
    assert forall|a: int, b: int| 0 <= a < b < n implies
        dst::key_le(dst::sic_key(sp, #[trigger] ord[a] as int), dst::sic_key(sp, #[trigger] ord[b] as int)) by {
        assert(s[a] == key_of(sp, ord[a] as int));
        assert(s[b] == key_of(sp, ord[b] as int));
        assert(KeyOrder {}.le(s[a], s[b]));
    }
}

/// The inherited parts followed by `sic_order` represent sub_sic's relations of every database bound to the source.
proof fn lemma_represents(sv: StoresView, db: Database, ord: Seq<u64>)
    requires
        sources_bound(sv, db),
        is_permutation(ord, src::row_count(sv.sub_fy) as nat),
        forall|a: int, b: int| 0 <= a < b < src::row_count(sv.sub_fy)
            ==> dst::key_le(dst::sic_key(sv.sub_fy, #[trigger] ord[a] as int), dst::sic_key(sv.sub_fy, #[trigger] ord[b] as int)),
    ensures
        dst::represents(sv.sub_fy + seq![PartView::U64(ord)], crate::stores::sub_sic::declaration::stored_relations(db)),
{
    let sp = sv.sub_fy;
    let parts = sp + seq![PartView::U64(ord)];
    let rels = crate::stores::sub_fy::declaration::stored_relations(db);
    assert(crate::stores::sub_sic::declaration::stored_relations(db) == rels);
    assert(src::represents(sp, rels));
    let n = src::row_count(sp);
    assert(sp.len() == 46);
    assert forall|k: int| 0 <= k < 46 implies #[trigger] parts[k] == sp[k] by {}
    assert(parts[dst::P_SIC_ORDER as int] == PartView::U64(ord));
    assert(dst::adsh_order(parts) == src::adsh_order(sp));
    assert(dst::fy_order(parts) == src::fy_order(sp));
    assert(dst::adsh_rank(parts) == src::adsh_rank(sp));
    assert(dst::sic_order(parts) == ord);
    assert(dst::row_count(parts) == n);
    assert forall|i: int| #[trigger] dst::row_key(parts, i) == src::row_key(sp, i) by {}
    assert forall|i: int| #[trigger] dst::sic_key(parts, i) == dst::sic_key(sp, i) by {}
    assert forall|a: int, b: int| 0 <= a < b < n implies dst::key_le(dst::row_key(parts, #[trigger] dst::fy_order(parts)[a] as int),
        dst::row_key(parts, #[trigger] dst::fy_order(parts)[b] as int)) by {
        assert(src::key_le(src::row_key(sp, src::fy_order(sp)[a] as int), src::row_key(sp, src::fy_order(sp)[b] as int)));
    }
    assert forall|a: int, b: int| 0 <= a < b < n implies dst::key_le(dst::sic_key(parts, #[trigger] dst::sic_order(parts)[a] as int),
        dst::sic_key(parts, #[trigger] dst::sic_order(parts)[b] as int)) by {
        assert(dst::key_le(dst::sic_key(sp, ord[a] as int), dst::sic_key(sp, ord[b] as int)));
    }
    assert forall|a: int, b: int| 0 <= a < b < n implies crate::spec::text::lex_cmp(
        dst::adsh_bytes(parts, #[trigger] dst::adsh_order(parts)[a] as int),
        dst::adsh_bytes(parts, #[trigger] dst::adsh_order(parts)[b] as int)) <= 0 by {
        assert(crate::spec::text::lex_cmp(src::adsh_bytes(sp, src::adsh_order(sp)[a] as int),
            src::adsh_bytes(sp, src::adsh_order(sp)[b] as int)) <= 0);
    }
    assert forall|q: int| 0 <= q < n implies dst::adsh_rank(parts)[#[trigger] dst::adsh_order(parts)[q] as int] == q by {
        assert(src::adsh_rank(sp)[src::adsh_order(sp)[q] as int] == q);
    }
    // The two interfaces' permutation predicates agree (their `ident` sequences are extensionally equal).
    assert(src::common::perm::ident(n as nat) =~= ident(n as nat));
    assert(is_permutation(dst::adsh_order(parts), n as nat));
    assert(is_permutation(dst::fy_order(parts), n as nat));
    let (doff, dbytes) = (src::common::text::u64_part(sp[src::P_NAME_DICT_OFF as int]),
        src::common::text::u8_part(sp[src::P_NAME_DICT_BYTES as int]));
    let dcount = src::common::cols::text_count(sp, src::P_NAME_DICT_OFF as int);
    assert forall|a: int, b: int| 0 <= a < b < dcount implies crate::spec::text::lex_cmp(
        #[trigger] dst::common::text::text_entry(doff, dbytes, a), #[trigger] dst::common::text::text_entry(doff, dbytes, b)) < 0 by {
        assert(crate::spec::text::lex_cmp(src::common::text::text_entry(doff, dbytes, a),
            src::common::text::text_entry(doff, dbytes, b)) < 0);
    }
    assert(dst::common::text::text_strictly_sorted(dst::common::text::u64_part(parts[dst::P_NAME_DICT_OFF as int]),
        dst::common::text::u8_part(parts[dst::P_NAME_DICT_BYTES as int]),
        dst::common::cols::text_count(parts, dst::P_NAME_DICT_OFF as int)));
    assert(dst::sub_layout_ok(parts));
    assert forall|i: int| 0 <= i < n implies dst::sub_row_ok(parts, #[trigger] rels[0][i], i) by {
        assert(src::sub_row_ok(sp, rels[0][i], i));
    }
}

pub fn build(stores: &mut Stores, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        sources_ready(old(stores)@),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(p) ==> forall|db: Database| #[trigger] sources_bound(old(stores)@, db)
            ==> dst::represents(storage_parts(old(stores)@, owned_parts_view(p@)),
                crate::stores::sub_sic::declaration::stored_relations(db)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost sv = stores@;
    let ghost sp = sv.sub_fy;
    proof { lemma_source_layout(sv); }
    let n = stores.sub_fy.part_len(src::P_CIK);
    let sic = stores.sub_fy.extent_i32(src::P_SIC, 0, n);
    let sic_valid = stores.sub_fy.extent_u8(src::P_SIC_VALID, 0, n);
    let cik = stores.sub_fy.extent_i32(src::P_CIK, 0, n);
    // ---- one key per row
    let mut keys: Vec<Key4> = Vec::with_capacity(n);
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n, n == src::row_count(sp), src::sub_layout_ok(sp),
            sic@ == src::common::cols::i32_part(sp[src::P_SIC as int]),
            sic_valid@ == src::common::text::u8_part(sp[src::P_SIC_VALID as int]),
            cik@ == src::common::cols::i32_part(sp[src::P_CIK as int]),
            keys@.len() == i,
            forall|k: int| 0 <= k < i ==> #[trigger] keys@[k] == key_of(sp, k),
        decreases n - i,
    {
        let sw: u64 = if sic_valid[i] == 0 { 0 } else { (sic[i] as i64 + 0x8000_0001) as u64 };
        let cw: u64 = (cik[i] as i64 + 0x8000_0000) as u64;
        keys.push(Key4 { k0: sw, k1: cw, k2: 0, k3: i as u64 });
        i = i + 1;
    }
    let ghost kv = keys@;
    proof {
        assert forall|k: int| 0 <= k < kv.len() implies KeyOrder {}.ok(#[trigger] kv[k]) by {}
    }
    // ---- sorted keys, then their rows
    let sorted = par_sort(KeyOrder {}, keys, workers, dispatch)?;
    proof {
        assert(sorted@.len() == sorted@.to_multiset().len());
        assert(kv.len() == kv.to_multiset().len());
    }
    let mut order: Vec<u64> = Vec::with_capacity(n);
    let mut q: usize = 0;
    while q < n
        invariant
            q <= n, sorted@.len() == n,
            order@ == sorted@.subrange(0, q as int).map_values(|e: Key4| key_row(e)),
        decreases n - q,
    {
        order.push(sorted[q].k3);
        q = q + 1;
        proof {
            assert(order@ =~= sorted@.subrange(0, q as int).map_values(|e: Key4| key_row(e)));
        }
    }
    let ghost ord = order@;
    proof {
        assert(sorted@.subrange(0, n as int) =~= sorted@);
        lemma_order_ok(sp, kv, sorted@, ord, n as nat);
    }
    let mut parts: Vec<OwnedPart> = Vec::new();
    parts.push(OwnedPart::U64(order));
    proof {
        assert(owned_parts_view(parts@) =~= seq![PartView::U64(ord)]);
        assert forall|db: Database| #[trigger] sources_bound(sv, db) implies dst::represents(
            storage_parts(sv, owned_parts_view(parts@)), crate::stores::sub_sic::declaration::stored_relations(db)) by {
            lemma_represents(sv, db, ord);
        }
    }
    Ok(parts)
}

} // verus!
