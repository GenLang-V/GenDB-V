//! Builder of storage `tag_tv`: keeps the 28 parts of storage `tag` (inherited, linked unchanged) and adds the key
//! index of its `tv_order`: `tag_first` (per tag code, the first `tv_order` position whose row has that tag code or a
//! larger one; one forward scan over the positions, whose tag codes are nondecreasing) and `tv_version` (the version
//! code of the row at each position; one gather pass). The proof: the scan's cut is exact because the tag codes along
//! `tv_order` are nondecreasing; the inherited parts carry tag's `represents` over to `tag_tv`'s.
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_entry::parallel::{Dispatch, MAX_WORKERS};
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::layout::{owned_parts_view, PartView};
use crate::gendb_entry::sources::{Stores, StoresView};
use crate::gendb_entry::{sources_bound, sources_ready, storage_parts};
use crate::spec::value::Database;
use crate::stores::tag::interface as src;
use crate::stores::tag_tv::interface as dst;

verus! {

/// Some database is bound to the source: tag's layout holds.
proof fn lemma_source_layout(sv: StoresView)
    requires sources_ready(sv),
    ensures src::tag_layout_ok(sv.tag),
{
    let db = choose|db: Database| #[trigger] sources_bound(sv, db);
}

/// Tag code of the row at `tv_order` position `k` of the source parts.
pub open spec fn src_tv_tag(sp: Seq<PartView>, k: int) -> u64 {
    src::common::cols::u64s(sp, src::P_TAG_CODES)[src::common::cols::u64s(sp, src::P_TV_ORDER)[k] as int]
}

/// Along `tv_order` the tag codes are nondecreasing.
proof fn lemma_tv_tag_mono(sp: Seq<PartView>, a: int, b: int)
    requires src::tag_layout_ok(sp), 0 <= a <= b < src::row_count(sp),
    ensures src_tv_tag(sp, a) <= src_tv_tag(sp, b),
{
    if a < b {
        let order = src::common::cols::u64s(sp, src::P_TV_ORDER);
        let tc = src::common::cols::u64s(sp, src::P_TAG_CODES);
        let vc = src::common::cols::u64s(sp, src::P_VERSION_CODES);
        assert(src::pair_le(tc[order[a] as int], vc[order[a] as int], tc[order[b] as int], vc[order[b] as int]));
    }
}

/// The inherited parts followed by `tag_first` and `tv_version` represent tag_tv's relations of every database bound
/// to the source.
proof fn lemma_represents(sv: StoresView, db: Database, first: Seq<u64>, tvv: Seq<u64>)
    requires
        sources_bound(sv, db),
        first.len() == src::common::cols::text_count(sv.tag, src::P_TAG_OFF as int) + 1,
        forall|c: int| 0 <= c < first.len() ==> #[trigger] first[c] <= src::row_count(sv.tag),
        forall|c: int, k: int| 0 <= c < first.len() && 0 <= k < src::row_count(sv.tag)
            ==> (k < #[trigger] first[c] <==> #[trigger] src_tv_tag(sv.tag, k) < c),
        tvv.len() == src::row_count(sv.tag),
        forall|k: int| 0 <= k < src::row_count(sv.tag) ==> #[trigger] tvv[k]
            == src::common::cols::u64s(sv.tag, src::P_VERSION_CODES)[src::common::cols::u64s(sv.tag, src::P_TV_ORDER)[k] as int],
    ensures
        dst::represents(sv.tag + seq![PartView::U64(first), PartView::U64(tvv)],
            crate::stores::tag_tv::declaration::stored_relations(db)),
{
    let sp = sv.tag;
    let parts = sp + seq![PartView::U64(first), PartView::U64(tvv)];
    let rels = crate::stores::tag::declaration::stored_relations(db);
    assert(crate::stores::tag_tv::declaration::stored_relations(db) == rels);
    assert(src::represents(sp, rels));
    let n = src::row_count(sp);
    assert(sp.len() == 28);
    assert forall|k: int| 0 <= k < 28 implies #[trigger] parts[k] == sp[k] by {}
    assert(parts[dst::P_TAG_FIRST as int] == PartView::U64(first));
    assert(parts[dst::P_TV_VERSION as int] == PartView::U64(tvv));
    assert(dst::row_count(parts) == n);
    let order = dst::common::cols::u64s(parts, dst::P_TV_ORDER);
    let tc = dst::common::cols::u64s(parts, dst::P_TAG_CODES);
    let vc = dst::common::cols::u64s(parts, dst::P_VERSION_CODES);
    assert(order == src::common::cols::u64s(sp, src::P_TV_ORDER));
    assert(tc == src::common::cols::u64s(sp, src::P_TAG_CODES));
    assert(vc == src::common::cols::u64s(sp, src::P_VERSION_CODES));
    // The two interfaces' permutation predicates agree (their `ident` sequences are extensionally equal).
    assert(src::common::perm::ident(n as nat) =~= dst::common::perm::ident(n as nat));
    assert(dst::common::perm::is_permutation(order, n as nat));
    assert forall|a: int, b: int| 0 <= a < b < n implies dst::pair_le(tc[#[trigger] order[a] as int], vc[order[a] as int],
        tc[#[trigger] order[b] as int], vc[order[b] as int]) by {
        assert(src::pair_le(tc[order[a] as int], vc[order[a] as int], tc[order[b] as int], vc[order[b] as int]));
    }
    // Dictionaries and coded columns: the same parts, so the same facts.
    assert forall|po: usize| po < 28 && #[trigger] src::common::cols::sorted_list_ok(sp, po)
        implies dst::common::cols::sorted_list_ok(parts, po) by {
        let (off, bytes) = (src::common::text::u64_part(sp[po as int]), src::common::text::u8_part(sp[po + 1]));
        let cnt = src::common::cols::text_count(sp, po as int);
        assert(parts[po as int] == sp[po as int] && parts[po + 1] == sp[po + 1]);
        assert forall|a: int, b: int| 0 <= a < b < cnt implies crate::spec::text::lex_cmp(
            #[trigger] dst::common::text::text_entry(off, bytes, a), #[trigger] dst::common::text::text_entry(off, bytes, b)) < 0 by {
            assert(crate::spec::text::lex_cmp(src::common::text::text_entry(off, bytes, a),
                src::common::text::text_entry(off, bytes, b)) < 0);
        }
    }
    assert(src::common::cols::sorted_list_ok(sp, src::P_TAG_OFF));
    assert(src::common::cols::sorted_list_ok(sp, src::P_VERSION_OFF));
    assert(src::common::cols::sorted_list_ok(sp, src::P_DATATYPE_OFF));
    assert(src::common::cols::sorted_list_ok(sp, src::P_IORD_OFF));
    assert(src::common::cols::sorted_list_ok(sp, src::P_CRDR_OFF));
    assert(src::common::cols::sorted_list_ok(sp, src::P_TLABEL_OFF));
    assert(src::common::cols::sorted_list_ok(sp, src::P_DOC_OFF));
    assert(dst::tag_first_ok(parts)) by {
        assert forall|c: int, k: int| 0 <= c <= dst::common::cols::text_count(parts, dst::P_TAG_OFF as int) && 0 <= k < n
            implies (k < #[trigger] dst::common::cols::u64s(parts, dst::P_TAG_FIRST)[c] <==> #[trigger] dst::tv_tag(parts, k) < c) by {
            assert(dst::tv_tag(parts, k) == src_tv_tag(sp, k));
        }
    }
    assert(dst::tv_version_ok(parts));
    assert(dst::tag_layout_ok(parts));
    assert forall|i: int| 0 <= i < n implies dst::tag_row_ok(parts, #[trigger] rels[0][i], i) by {
        assert(src::tag_row_ok(sp, rels[0][i], i));
    }
}

pub fn build(stores: &mut Stores, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires
        sources_ready(old(stores)@),
        1 <= workers <= MAX_WORKERS,
    ensures
        r matches Ok(p) ==> forall|db: Database| #[trigger] sources_bound(old(stores)@, db)
            ==> dst::represents(storage_parts(old(stores)@, owned_parts_view(p@)),
                crate::stores::tag_tv::declaration::stored_relations(db)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost sv = stores@;
    let ghost sp = sv.tag;
    proof { lemma_source_layout(sv); }
    let n = stores.tag.part_len(src::P_CUSTOM);
    let tc = stores.tag.extent_u64(src::P_TAG_CODES, 0, n);
    let vc = stores.tag.extent_u64(src::P_VERSION_CODES, 0, n);
    proof { src::common::perm::lemma_permutation_facts(src::common::cols::u64s(sp, src::P_TV_ORDER), n as nat); }
    let order = stores.tag.extent_u64(src::P_TV_ORDER, 0, n);
    let nto = stores.tag.part_len(src::P_TAG_OFF);
    let ghost nt = src::common::cols::text_count(sp, src::P_TAG_OFF as int);
    proof {
        src::common::perm::lemma_permutation_facts(src::common::cols::u64s(sp, src::P_TV_ORDER), n as nat);
        assert(tc@ =~= src::common::cols::u64s(sp, src::P_TAG_CODES));
        assert(vc@ =~= src::common::cols::u64s(sp, src::P_VERSION_CODES));
        assert(order@ =~= src::common::cols::u64s(sp, src::P_TV_ORDER));
        assert(nto as int == nt + 1);
    }
    // ---- tv_version: the version code behind each position
    let mut tvv: Vec<u64> = Vec::with_capacity(n);
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n, n == src::row_count(sp), src::tag_layout_ok(sp),
            tc@ == src::common::cols::u64s(sp, src::P_TAG_CODES), vc@ == src::common::cols::u64s(sp, src::P_VERSION_CODES),
            order@ == src::common::cols::u64s(sp, src::P_TV_ORDER),
            order@.len() == n, tc@.len() == n, vc@.len() == n,
            forall|i: int| 0 <= i < n ==> #[trigger] order@[i] < n,
            tvv@.len() == k,
            forall|i: int| 0 <= i < k ==> #[trigger] tvv@[i] == vc@[order@[i] as int],
        decreases n - k,
    {
        let r = order[k] as usize;
        tvv.push(vc[r]);
        k = k + 1;
    }
    // ---- tag_first: one forward scan, cutting where the tag code reaches `c`
    let mut first: Vec<u64> = Vec::with_capacity(nto);
    let mut k: usize = 0;
    let mut c: usize = 0;
    while c < nto
        invariant
            c <= nto, nto == nt + 1, k <= n, n == src::row_count(sp), src::tag_layout_ok(sp),
            tc@ == src::common::cols::u64s(sp, src::P_TAG_CODES), order@ == src::common::cols::u64s(sp, src::P_TV_ORDER),
            order@.len() == n, tc@.len() == n,
            forall|i: int| 0 <= i < n ==> #[trigger] order@[i] < n,
            // Every position before `k` has a tag code below `c` (or below the last cut when `c` is 0: none).
            forall|i: int| 0 <= i < k ==> #[trigger] src_tv_tag(sp, i) < c,
            first@.len() == c,
            forall|cc: int| 0 <= cc < c ==> #[trigger] first@[cc] <= k,
            forall|cc: int, i: int| 0 <= cc < c && 0 <= i < n ==> (i < #[trigger] first@[cc] <==> #[trigger] src_tv_tag(sp, i) < cc),
        decreases nto - c,
    {
        while k < n && tc[order[k] as usize] < c as u64
            invariant
                k <= n, n == src::row_count(sp), src::tag_layout_ok(sp),
                tc@ == src::common::cols::u64s(sp, src::P_TAG_CODES), order@ == src::common::cols::u64s(sp, src::P_TV_ORDER),
                order@.len() == n, tc@.len() == n,
                forall|i: int| 0 <= i < n ==> #[trigger] order@[i] < n,
                forall|i: int| 0 <= i < k ==> #[trigger] src_tv_tag(sp, i) < c,
                first@.len() == c,
                forall|cc: int| 0 <= cc < c ==> #[trigger] first@[cc] <= k,
            decreases n - k,
        {
            k = k + 1;
        }
        proof {
            // From `k` on every tag code is at least `c` (the codes along tv_order are nondecreasing).
            assert forall|i: int| 0 <= i < n implies (i < k <==> #[trigger] src_tv_tag(sp, i) < c) by {
                if i >= k {
                    assert(src_tv_tag(sp, k as int) >= c);
                    lemma_tv_tag_mono(sp, k as int, i);
                }
            }
        }
        let ghost prev = first@;
        first.push(k as u64);
        proof {
            assert forall|cc: int, i: int| 0 <= cc < c + 1 && 0 <= i < n
                implies (i < #[trigger] first@[cc] <==> #[trigger] src_tv_tag(sp, i) < cc) by {
                if cc < c {
                    assert(first@[cc] == prev[cc]);
                }
            }
        }
        c = c + 1;
    }
    let ghost fv = first@;
    let ghost tv = tvv@;
    let mut parts: Vec<OwnedPart> = Vec::new();
    parts.push(OwnedPart::U64(first));
    parts.push(OwnedPart::U64(tvv));
    proof {
        assert(owned_parts_view(parts@) =~= seq![PartView::U64(fv), PartView::U64(tv)]);
        assert forall|db: Database| #[trigger] sources_bound(sv, db) implies dst::represents(
            storage_parts(sv, owned_parts_view(parts@)), crate::stores::tag_tv::declaration::stored_relations(db)) by {
            lemma_represents(sv, db, fv, tv);
        }
    }
    Ok(parts)
}

} // verus!
