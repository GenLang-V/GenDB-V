//! Builder of storage `tag`: a sorted dictionary and per-row codes for every text column (parallel sorts of row ids
//! by value; validity copied for nullable columns), custom and abstract copied, and `tv_order`: the row positions
//! sorted by (tag code, version code). Canonical row order throughout. Parts in `P_*` order.
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_source::*;
use crate::gendb_entry::parallel::Dispatch;
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::layout::{owned_parts_view, PartView};
use crate::link::query::{text_at, text_wf, TextView};
use crate::spec::value::{Row, Val};
use crate::stores::tag::interface::*;
use crate::stores::tag::interface::common::text::{text_entry, text_parts_wf, text_strictly_sorted, u64_part, u8_part};
use crate::stores::tag::interface::common::cols::{i32_part, text_count, u64s, list_entry, sorted_list_ok, coded_text_at, coded_col_ok};
use crate::stores::tag::interface::common::perm::{is_permutation, lemma_permutation_facts};
pub mod common;
use common::sort::{TextOrder, SortOrder, Key4, KeyOrder, key4_le, sorted_by};
use common::dict::{build_text_dict, emit_text_list, lemma_emitted_sorted, dict_ids_ok, codes_ok, row_in};
use common::keys::{sort_row_keys, rows_of_keys, row_keys, key_rows, lemma_sorted_keys};

verus! {

/// The text order of a delivered text column of `rows` rows.
fn text_order(c: &TextCol, rows: usize) -> (o: TextOrder)
    requires text_wf(c@, rows as int), rows < usize::MAX,
    ensures o.wf(), o.rows == rows, o.text() == c@,
{
    TextOrder { offsets: c.offsets, bytes: c.bytes, rows: rows as u64 }
}

/// A sorted dictionary of a text column: representative rows, per-row codes, and its text parts.
pub struct BuiltDict {
    pub ids: Vec<u64>,
    pub codes: Vec<u64>,
    pub off: Vec<u64>,
    pub bytes: Vec<u8>,
}

/// The facts a dictionary of column `o` gives (NULL rows have no code).
spec fn built_dict_ok(o: TextOrder, valid: Seq<u8>, nullable: bool, d: BuiltDict) -> bool {
    &&& dict_ids_ok(o, d.ids@)
    &&& d.ids@.len() <= o.rows
    &&& d.codes@.len() == o.rows
    &&& forall|i: int| 0 <= i < o.rows && row_in(valid, nullable, i) ==> (#[trigger] d.codes@[i]) < d.ids@.len()
        && o.value(d.ids@[d.codes@[i] as int]) == o.value(i as u64)
    &&& d.off@.len() == d.ids@.len() + 1
    &&& text_parts_wf(d.off@, d.bytes@, d.ids@.len() as int)
    &&& text_strictly_sorted(d.off@, d.bytes@, d.ids@.len() as int)
    &&& forall|k: int| 0 <= k < d.ids@.len() ==> #[trigger] text_entry(d.off@, d.bytes@, k) == o.value(d.ids@[k])
}

/// Dictionary of a text column (of its non-NULL rows when `nullable`).
fn dictionary(o: TextOrder, valid: &'static [u8], nullable: bool, workers: usize, dispatch: &mut Dispatch)
    -> (r: Result<BuiltDict, QueryError>)
    requires o.wf(), nullable ==> valid@.len() == o.rows, 1 <= workers <= 64,
    ensures
        r matches Ok(d) ==> built_dict_ok(o, valid@, nullable, d),
        r matches Err(e) ==> e is WorkerFailed,
{
    let d = build_text_dict(o, valid, nullable, workers, dispatch)?;
    let (off, bytes) = emit_text_list(&o, &d.ids);
    proof {
        lemma_emitted_sorted(o, d.ids@, off@, bytes@);
    }
    Ok(BuiltDict { ids: d.ids, codes: d.codes, off, bytes })
}

/// A dictionary column in canonical order satisfies `coded_col_ok`, and its value at row `i` is the column's.
proof fn lemma_coded(pv: Seq<PartView>, pc: usize, pvalid: int, po: usize, o: TextOrder, valid: Seq<u8>,
    nullable: bool, d: BuiltDict, n: int)
    requires
        built_dict_ok(o, valid, nullable, d),
        o.rows == n, nullable ==> valid.len() == n,
        nullable <==> pvalid >= 0,
        0 <= pc < pv.len(), po + 1 < pv.len(), pvalid < pv.len(),
        pv[pc as int] == PartView::U64(d.codes@),
        pvalid >= 0 ==> pv[pvalid] == PartView::U8(valid),
        pv[po as int] == PartView::U64(d.off@) && pv[po + 1] == PartView::U8(d.bytes@),
    ensures
        coded_col_ok(pv, pc, pvalid, po, n),
        forall|i: int| 0 <= i < n ==> #[trigger] coded_text_at(pv, pc, pvalid, po, i)
            == crate::gendb_source::or_null(if nullable { valid[i] } else { 1u8 }, Val::Text(o.value(i as u64))),
{
    assert(text_count(pv, po as int) == d.ids@.len());
    assert forall|i: int| 0 <= i < n && !(pvalid >= 0 && u8_part(pv[pvalid])[i] == 0)
        implies #[trigger] u64s(pv, pc)[i] < text_count(pv, po as int) by {
        assert(row_in(valid, nullable, i));
    }
    assert forall|i: int| 0 <= i < n implies #[trigger] coded_text_at(pv, pc, pvalid, po, i)
        == crate::gendb_source::or_null(if nullable { valid[i] } else { 1u8 }, Val::Text(o.value(i as u64))) by {
        if row_in(valid, nullable, i) {
            assert(d.codes@[i] < d.ids@.len());
            assert(list_entry(pv, po, d.codes@[i] as int) == text_entry(d.off@, d.bytes@, d.codes@[i] as int));
        }
    }
}

pub fn build(src: &SourceRef, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires source_wf(src@), in_domain(tables(src@)), 1 <= workers <= 64,
    ensures
        r matches Ok(p) ==> represents(owned_parts_view(p@), tables(src@)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost v = src@;
    let n = src.t0_f0.offsets.len() - 1;
    let tag = text_order(&src.t0_f0, n);
    let version = text_order(&src.t0_f1, n);
    let datatype = text_order(&src.t0_f4, n);
    let iord = text_order(&src.t0_f5, n);
    let crdr = text_order(&src.t0_f6, n);
    let tlabel = text_order(&src.t0_f7, n);
    let doc = text_order(&src.t0_f8, n);
    let tag_d = dictionary(tag, src.t0_v4, false, workers, dispatch)?;
    let version_d = dictionary(version, src.t0_v4, false, workers, dispatch)?;
    let datatype_d = dictionary(datatype, src.t0_v4, true, workers, dispatch)?;
    let iord_d = dictionary(iord, src.t0_v4, false, workers, dispatch)?;
    let crdr_d = dictionary(crdr, src.t0_v6, true, workers, dispatch)?;
    let tlabel_d = dictionary(tlabel, src.t0_v7, true, workers, dispatch)?;
    let doc_d = dictionary(doc, src.t0_v8, true, workers, dispatch)?;
    let zeros: Vec<u64> = vec![0u64; n];
    let s = sort_row_keys(&tag_d.codes, &version_d.codes, &zeros, workers, dispatch)?;
    proof {
        lemma_sorted_keys(s@, tag_d.codes@, version_d.codes@, zeros@);
        lemma_permutation_facts(key_rows(s@), n as nat);
    }
    let order = rows_of_keys(&s);
    let ghost order_v = order@;
    let ghost tc = tag_d.codes@;
    let ghost vc = version_d.codes@;
    proof {
        assert forall|a: int, b: int| 0 <= a < b < n implies pair_le(tc[#[trigger] order_v[a] as int], vc[order_v[a] as int],
            tc[#[trigger] order_v[b] as int], vc[order_v[b] as int]) by {
            assert(key4_le(s@[a], s@[b]));
            assert(order_v[a] == s@[a].k3 && order_v[b] == s@[b].k3);
            assert(s@[a] == row_keys(tc, vc, zeros@)[s@[a].k3 as int]);
            assert(s@[b] == row_keys(tc, vc, zeros@)[s@[b].k3 as int]);
        }
    }
    let ghost views = seq![
        PartView::U64(tag_d.codes@), PartView::U64(tag_d.off@), PartView::U8(tag_d.bytes@),
        PartView::U64(version_d.codes@), PartView::U64(version_d.off@), PartView::U8(version_d.bytes@),
        PartView::U64(order@),
        PartView::I32(v.t0_f2), PartView::I32(v.t0_f3),
        PartView::U64(datatype_d.codes@), PartView::U8(v.t0_v4), PartView::U64(datatype_d.off@), PartView::U8(datatype_d.bytes@),
        PartView::U64(iord_d.codes@), PartView::U64(iord_d.off@), PartView::U8(iord_d.bytes@),
        PartView::U64(crdr_d.codes@), PartView::U8(v.t0_v6), PartView::U64(crdr_d.off@), PartView::U8(crdr_d.bytes@),
        PartView::U64(tlabel_d.codes@), PartView::U8(v.t0_v7), PartView::U64(tlabel_d.off@), PartView::U8(tlabel_d.bytes@),
        PartView::U64(doc_d.codes@), PartView::U8(v.t0_v8), PartView::U64(doc_d.off@), PartView::U8(doc_d.bytes@)
    ];
    let ghost g = (tag_d, version_d, datatype_d, iord_d, crdr_d, tlabel_d, doc_d);
    let mut parts: Vec<OwnedPart> = Vec::new();
    parts.push(OwnedPart::U64(tag_d.codes));
    parts.push(OwnedPart::U64(tag_d.off));
    parts.push(OwnedPart::U8(tag_d.bytes));
    parts.push(OwnedPart::U64(version_d.codes));
    parts.push(OwnedPart::U64(version_d.off));
    parts.push(OwnedPart::U8(version_d.bytes));
    parts.push(OwnedPart::U64(order));
    parts.push(OwnedPart::I32(vstd::slice::slice_to_vec(src.t0_f2)));
    parts.push(OwnedPart::I32(vstd::slice::slice_to_vec(src.t0_f3)));
    parts.push(OwnedPart::U64(datatype_d.codes));
    parts.push(OwnedPart::U8(vstd::slice::slice_to_vec(src.t0_v4)));
    parts.push(OwnedPart::U64(datatype_d.off));
    parts.push(OwnedPart::U8(datatype_d.bytes));
    parts.push(OwnedPart::U64(iord_d.codes));
    parts.push(OwnedPart::U64(iord_d.off));
    parts.push(OwnedPart::U8(iord_d.bytes));
    parts.push(OwnedPart::U64(crdr_d.codes));
    parts.push(OwnedPart::U8(vstd::slice::slice_to_vec(src.t0_v6)));
    parts.push(OwnedPart::U64(crdr_d.off));
    parts.push(OwnedPart::U8(crdr_d.bytes));
    parts.push(OwnedPart::U64(tlabel_d.codes));
    parts.push(OwnedPart::U8(vstd::slice::slice_to_vec(src.t0_v7)));
    parts.push(OwnedPart::U64(tlabel_d.off));
    parts.push(OwnedPart::U8(tlabel_d.bytes));
    parts.push(OwnedPart::U64(doc_d.codes));
    parts.push(OwnedPart::U8(vstd::slice::slice_to_vec(src.t0_v8)));
    parts.push(OwnedPart::U64(doc_d.off));
    parts.push(OwnedPart::U8(doc_d.bytes));
    proof {
        assert(owned_parts_view(parts@) =~= views);
        let pv = views;
        lemma_coded(pv, P_TAG_CODES, -1, P_TAG_OFF, tag, v.t0_v4, false, g.0, n as int);
        lemma_coded(pv, P_VERSION_CODES, -1, P_VERSION_OFF, version, v.t0_v4, false, g.1, n as int);
        lemma_coded(pv, P_DATATYPE_CODES, P_DATATYPE_VALID as int, P_DATATYPE_OFF, datatype, v.t0_v4, true, g.2, n as int);
        lemma_coded(pv, P_IORD_CODES, -1, P_IORD_OFF, iord, v.t0_v4, false, g.3, n as int);
        lemma_coded(pv, P_CRDR_CODES, P_CRDR_VALID as int, P_CRDR_OFF, crdr, v.t0_v6, true, g.4, n as int);
        lemma_coded(pv, P_TLABEL_CODES, P_TLABEL_VALID as int, P_TLABEL_OFF, tlabel, v.t0_v7, true, g.5, n as int);
        lemma_coded(pv, P_DOC_CODES, P_DOC_VALID as int, P_DOC_OFF, doc, v.t0_v8, true, g.6, n as int);
        assert(row_count(pv) == n);
        assert(u64s(pv, P_TV_ORDER) == order_v);
        assert(u64s(pv, P_TAG_CODES) == tc && u64s(pv, P_VERSION_CODES) == vc);
        assert(tag_layout_ok(pv));
        let rows = table_t0(v);
        assert forall|i: int| 0 <= i < n implies tag_row_ok(pv, #[trigger] tables(v)[0][i], i) by {
            assert(tables(v)[0] == rows);
        }
    }
    Ok(parts)
}

} // verus!
