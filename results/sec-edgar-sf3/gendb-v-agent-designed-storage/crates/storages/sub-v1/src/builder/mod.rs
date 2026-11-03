//! Builder of storage `sub`: copies every column in canonical row order (int4 and validity parts as delivered,
//! text columns as flat text lists), dictionary-encodes `name` (sorted distinct names + one code per row) and sorts
//! the row positions by `adsh` (`adsh_order`). Parts in the order of the interface's `P_*` constants.
use vstd::prelude::*;
use crate::gendb_abi::OwnedPart;
use crate::gendb_source::*;
use crate::gendb_entry::parallel::Dispatch;
use crate::gendb_entry::runtime::QueryError;
use crate::gendb_entry::layout::{owned_parts_view, PartView};
use crate::link::query::{text_at, text_wf, TextView};
use crate::spec::value::Val;
use crate::stores::sub::interface::*;
use crate::stores::sub::interface::common::text::{text_entry, text_parts_wf, u64_part, u8_part};
use crate::stores::sub::interface::common::cols::*;
pub mod common;
use common::sort::{TextOrder, SortOrder};
use common::dict::{build_text_dict, emit_text_list, lemma_emitted_sorted};
use common::columns::{copy_text, sort_permutation};

verus! {

/// The text order of a delivered text column of `rows` rows.
fn text_order(c: &TextCol, rows: usize) -> (o: TextOrder)
    requires text_wf(c@, rows as int), rows < usize::MAX,
    ensures o.wf(), o.rows == rows, o.text() == c@,
{
    TextOrder { offsets: c.offsets, bytes: c.bytes, rows: rows as u64 }
}

/// A flat copy of a delivered text column: its parts' values are the column's values.
fn flat_text(c: &TextCol, rows: usize) -> (r: (Vec<u64>, Vec<u8>))
    requires text_wf(c@, rows as int), rows < usize::MAX,
    ensures
        text_parts_wf(r.0@, r.1@, rows as int),
        forall|i: int| 0 <= i < rows ==> #[trigger] text_entry(r.0@, r.1@, i) == text_at(c@, i),
{
    let o = text_order(c, rows);
    copy_text(&o)
}

pub fn build(src: &SourceRef, workers: usize, dispatch: &mut Dispatch) -> (r: Result<Vec<OwnedPart>, QueryError>)
    requires source_wf(src@), in_domain(tables(src@)), 1 <= workers <= 64,
    ensures
        r matches Ok(p) ==> represents(owned_parts_view(p@), tables(src@)),
        r matches Err(e) ==> e is WorkerFailed,
{
    let ghost v = src@;
    let n = src.t0_f0.offsets.len() - 1;
    let adsh = text_order(&src.t0_f0, n);
    let (adsh_off, adsh_bytes) = copy_text(&adsh);
    let adsh_order = sort_permutation(adsh, workers, dispatch)?;
    let ghost adsh_order_v = adsh_order@;
    let name = text_order(&src.t0_f2, n);
    let name_dict = build_text_dict(name, src.t0_v3, false, workers, dispatch)?;
    let (name_off, name_bytes) = emit_text_list(&name, &name_dict.ids);
    proof {
        lemma_emitted_sorted(name, name_dict.ids@, name_off@, name_bytes@);
    }
    let (countryba_off, countryba_bytes) = flat_text(&src.t0_f4, n);
    let (stprba_off, stprba_bytes) = flat_text(&src.t0_f5, n);
    let (cityba_off, cityba_bytes) = flat_text(&src.t0_f6, n);
    let (countryinc_off, countryinc_bytes) = flat_text(&src.t0_f7, n);
    let (form_off, form_bytes) = flat_text(&src.t0_f8, n);
    let (fp_off, fp_bytes) = flat_text(&src.t0_f11, n);
    let (accepted_off, accepted_bytes) = flat_text(&src.t0_f13, n);
    let (afs_off, afs_bytes) = flat_text(&src.t0_f16, n);
    let (fye_off, fye_bytes) = flat_text(&src.t0_f18, n);
    let (instance_off, instance_bytes) = flat_text(&src.t0_f19, n);
    let ghost name_codes_v = name_dict.codes@;
    let ghost views = seq![
        PartView::U64(adsh_off@), PartView::U8(adsh_bytes@), PartView::U64(adsh_order@),
        PartView::I32(v.t0_f1),
        PartView::U64(name_dict.codes@), PartView::U64(name_off@), PartView::U8(name_bytes@),
        PartView::I32(v.t0_f3), PartView::U8(v.t0_v3),
        PartView::U64(countryba_off@), PartView::U8(countryba_bytes@), PartView::U8(v.t0_v4),
        PartView::U64(stprba_off@), PartView::U8(stprba_bytes@), PartView::U8(v.t0_v5),
        PartView::U64(cityba_off@), PartView::U8(cityba_bytes@), PartView::U8(v.t0_v6),
        PartView::U64(countryinc_off@), PartView::U8(countryinc_bytes@), PartView::U8(v.t0_v7),
        PartView::U64(form_off@), PartView::U8(form_bytes@),
        PartView::I32(v.t0_f9), PartView::U8(v.t0_v9),
        PartView::I32(v.t0_f10), PartView::U8(v.t0_v10),
        PartView::U64(fp_off@), PartView::U8(fp_bytes@), PartView::U8(v.t0_v11),
        PartView::I32(v.t0_f12),
        PartView::U64(accepted_off@), PartView::U8(accepted_bytes@),
        PartView::I32(v.t0_f14),
        PartView::I32(v.t0_f15),
        PartView::U64(afs_off@), PartView::U8(afs_bytes@), PartView::U8(v.t0_v16),
        PartView::I32(v.t0_f17),
        PartView::U64(fye_off@), PartView::U8(fye_bytes@), PartView::U8(v.t0_v18),
        PartView::U64(instance_off@), PartView::U8(instance_bytes@)
    ];
    let mut parts: Vec<OwnedPart> = Vec::new();
    parts.push(OwnedPart::U64(adsh_off));
    parts.push(OwnedPart::U8(adsh_bytes));
    parts.push(OwnedPart::U64(adsh_order));
    parts.push(OwnedPart::I32(vstd::slice::slice_to_vec(src.t0_f1)));
    parts.push(OwnedPart::U64(name_dict.codes));
    parts.push(OwnedPart::U64(name_off));
    parts.push(OwnedPart::U8(name_bytes));
    parts.push(OwnedPart::I32(vstd::slice::slice_to_vec(src.t0_f3)));
    parts.push(OwnedPart::U8(vstd::slice::slice_to_vec(src.t0_v3)));
    parts.push(OwnedPart::U64(countryba_off));
    parts.push(OwnedPart::U8(countryba_bytes));
    parts.push(OwnedPart::U8(vstd::slice::slice_to_vec(src.t0_v4)));
    parts.push(OwnedPart::U64(stprba_off));
    parts.push(OwnedPart::U8(stprba_bytes));
    parts.push(OwnedPart::U8(vstd::slice::slice_to_vec(src.t0_v5)));
    parts.push(OwnedPart::U64(cityba_off));
    parts.push(OwnedPart::U8(cityba_bytes));
    parts.push(OwnedPart::U8(vstd::slice::slice_to_vec(src.t0_v6)));
    parts.push(OwnedPart::U64(countryinc_off));
    parts.push(OwnedPart::U8(countryinc_bytes));
    parts.push(OwnedPart::U8(vstd::slice::slice_to_vec(src.t0_v7)));
    parts.push(OwnedPart::U64(form_off));
    parts.push(OwnedPart::U8(form_bytes));
    parts.push(OwnedPart::I32(vstd::slice::slice_to_vec(src.t0_f9)));
    parts.push(OwnedPart::U8(vstd::slice::slice_to_vec(src.t0_v9)));
    parts.push(OwnedPart::I32(vstd::slice::slice_to_vec(src.t0_f10)));
    parts.push(OwnedPart::U8(vstd::slice::slice_to_vec(src.t0_v10)));
    parts.push(OwnedPart::U64(fp_off));
    parts.push(OwnedPart::U8(fp_bytes));
    parts.push(OwnedPart::U8(vstd::slice::slice_to_vec(src.t0_v11)));
    parts.push(OwnedPart::I32(vstd::slice::slice_to_vec(src.t0_f12)));
    parts.push(OwnedPart::U64(accepted_off));
    parts.push(OwnedPart::U8(accepted_bytes));
    parts.push(OwnedPart::I32(vstd::slice::slice_to_vec(src.t0_f14)));
    parts.push(OwnedPart::I32(vstd::slice::slice_to_vec(src.t0_f15)));
    parts.push(OwnedPart::U64(afs_off));
    parts.push(OwnedPart::U8(afs_bytes));
    parts.push(OwnedPart::U8(vstd::slice::slice_to_vec(src.t0_v16)));
    parts.push(OwnedPart::I32(vstd::slice::slice_to_vec(src.t0_f17)));
    parts.push(OwnedPart::U64(fye_off));
    parts.push(OwnedPart::U8(fye_bytes));
    parts.push(OwnedPart::U8(vstd::slice::slice_to_vec(src.t0_v18)));
    parts.push(OwnedPart::U64(instance_off));
    parts.push(OwnedPart::U8(instance_bytes));
    proof {
        assert(owned_parts_view(parts@) =~= views);
        let order = u64_part(views[P_ADSH_ORDER as int]);
        assert(order == adsh_order_v);
        crate::stores::sub::interface::common::perm::lemma_permutation_facts(adsh_order_v, n as nat);
        assert forall|a: int, b: int| 0 <= a < b < n implies crate::spec::text::lex_cmp(
            text_at(v.t0_f0, #[trigger] order[a] as int), text_at(v.t0_f0, #[trigger] order[b] as int)) <= 0 by {
            assert(crate::spec::text::lex_cmp(adsh.value(adsh_order_v[a]), adsh.value(adsh_order_v[b])) <= 0);
        }
        lemma_sub_represents(v, views, name);
    }
    Ok(parts)
}

/// The assembled part views represent the delivered `sub` relation.
proof fn lemma_sub_represents(v: SourceView, pv: Seq<PartView>, name: TextOrder)
    requires
        source_wf(v),
        pv.len() == PART_COUNT,
        name.text() == v.t0_f2, name.wf(), name.rows == source_rows_t0(v),
        // the parts as the builder assembled them
        flat_parts(pv, P_ADSH_OFF as int, P_ADSH_BYTES as int, v.t0_f0, source_rows_t0(v)),
        pv[P_ADSH_ORDER as int] is U64,
        crate::stores::sub::interface::common::perm::is_permutation(u64_part(pv[P_ADSH_ORDER as int]), source_rows_t0(v) as nat),
        forall|a: int, b: int| 0 <= a < b < source_rows_t0(v) ==> crate::spec::text::lex_cmp(
            text_at(v.t0_f0, #[trigger] u64_part(pv[P_ADSH_ORDER as int])[a] as int),
            text_at(v.t0_f0, #[trigger] u64_part(pv[P_ADSH_ORDER as int])[b] as int)) <= 0,
        pv[P_CIK as int] == PartView::I32(v.t0_f1),
        name_parts(pv, v, name),
        pv[P_SIC as int] == PartView::I32(v.t0_f3), pv[P_SIC_VALID as int] == PartView::U8(v.t0_v3),
        flat_parts(pv, P_COUNTRYBA_OFF as int, P_COUNTRYBA_BYTES as int, v.t0_f4, source_rows_t0(v)),
        pv[P_COUNTRYBA_VALID as int] == PartView::U8(v.t0_v4),
        flat_parts(pv, P_STPRBA_OFF as int, P_STPRBA_BYTES as int, v.t0_f5, source_rows_t0(v)),
        pv[P_STPRBA_VALID as int] == PartView::U8(v.t0_v5),
        flat_parts(pv, P_CITYBA_OFF as int, P_CITYBA_BYTES as int, v.t0_f6, source_rows_t0(v)),
        pv[P_CITYBA_VALID as int] == PartView::U8(v.t0_v6),
        flat_parts(pv, P_COUNTRYINC_OFF as int, P_COUNTRYINC_BYTES as int, v.t0_f7, source_rows_t0(v)),
        pv[P_COUNTRYINC_VALID as int] == PartView::U8(v.t0_v7),
        flat_parts(pv, P_FORM_OFF as int, P_FORM_BYTES as int, v.t0_f8, source_rows_t0(v)),
        pv[P_PERIOD as int] == PartView::I32(v.t0_f9), pv[P_PERIOD_VALID as int] == PartView::U8(v.t0_v9),
        pv[P_FY as int] == PartView::I32(v.t0_f10), pv[P_FY_VALID as int] == PartView::U8(v.t0_v10),
        flat_parts(pv, P_FP_OFF as int, P_FP_BYTES as int, v.t0_f11, source_rows_t0(v)),
        pv[P_FP_VALID as int] == PartView::U8(v.t0_v11),
        pv[P_FILED as int] == PartView::I32(v.t0_f12),
        flat_parts(pv, P_ACCEPTED_OFF as int, P_ACCEPTED_BYTES as int, v.t0_f13, source_rows_t0(v)),
        pv[P_PREVRPT as int] == PartView::I32(v.t0_f14),
        pv[P_NCIKS as int] == PartView::I32(v.t0_f15),
        flat_parts(pv, P_AFS_OFF as int, P_AFS_BYTES as int, v.t0_f16, source_rows_t0(v)),
        pv[P_AFS_VALID as int] == PartView::U8(v.t0_v16),
        pv[P_WKSI as int] == PartView::I32(v.t0_f17),
        flat_parts(pv, P_FYE_OFF as int, P_FYE_BYTES as int, v.t0_f18, source_rows_t0(v)),
        pv[P_FYE_VALID as int] == PartView::U8(v.t0_v18),
        flat_parts(pv, P_INSTANCE_OFF as int, P_INSTANCE_BYTES as int, v.t0_f19, source_rows_t0(v)),
    ensures
        represents(pv, tables(v)),
{
    let n = source_rows_t0(v);
    assert(row_count(pv) == n);
    assert forall|a: int, b: int| 0 <= a < b < n implies crate::spec::text::lex_cmp(
        adsh_bytes(pv, #[trigger] adsh_order(pv)[a] as int), adsh_bytes(pv, #[trigger] adsh_order(pv)[b] as int)) <= 0 by {
        crate::stores::sub::interface::common::perm::lemma_permutation_facts(adsh_order(pv), n as nat);
        assert(adsh_order(pv)[a] < n && adsh_order(pv)[b] < n);
    }
    assert(sub_layout_ok(pv));
    let rows = table_t0(v);
    assert forall|i: int| 0 <= i < n implies sub_row_ok(pv, #[trigger] tables(v)[0][i], i) by {
        assert(tables(v)[0] == rows);
        assert(rows[i][0] == flat_text_at(pv, P_ADSH_OFF as int, P_ADSH_BYTES as int, i));
        assert(rows[i][2] == dict_text_at(pv, P_NAME_CODES as int, P_NAME_DICT_OFF as int, P_NAME_DICT_BYTES as int, i));
        assert(rows[i][4] == or_null_at(pv, P_COUNTRYBA_VALID as int, i, flat_text_at(pv, P_COUNTRYBA_OFF as int, P_COUNTRYBA_BYTES as int, i)));
        assert(rows[i][5] == or_null_at(pv, P_STPRBA_VALID as int, i, flat_text_at(pv, P_STPRBA_OFF as int, P_STPRBA_BYTES as int, i)));
        assert(rows[i][6] == or_null_at(pv, P_CITYBA_VALID as int, i, flat_text_at(pv, P_CITYBA_OFF as int, P_CITYBA_BYTES as int, i)));
        assert(rows[i][7] == or_null_at(pv, P_COUNTRYINC_VALID as int, i, flat_text_at(pv, P_COUNTRYINC_OFF as int, P_COUNTRYINC_BYTES as int, i)));
        assert(rows[i][8] == flat_text_at(pv, P_FORM_OFF as int, P_FORM_BYTES as int, i));
        assert(rows[i][11] == or_null_at(pv, P_FP_VALID as int, i, flat_text_at(pv, P_FP_OFF as int, P_FP_BYTES as int, i)));
        assert(rows[i][13] == flat_text_at(pv, P_ACCEPTED_OFF as int, P_ACCEPTED_BYTES as int, i));
        assert(rows[i][16] == or_null_at(pv, P_AFS_VALID as int, i, flat_text_at(pv, P_AFS_OFF as int, P_AFS_BYTES as int, i)));
        assert(rows[i][18] == or_null_at(pv, P_FYE_VALID as int, i, flat_text_at(pv, P_FYE_OFF as int, P_FYE_BYTES as int, i)));
        assert(rows[i][19] == flat_text_at(pv, P_INSTANCE_OFF as int, P_INSTANCE_BYTES as int, i));
    }
}

/// Parts `po`, `pb` are a flat copy of text column `c` (`n` rows).
pub open spec fn flat_parts(pv: Seq<PartView>, po: int, pb: int, c: TextView, n: int) -> bool {
    &&& pv[po] is U64
    &&& pv[pb] is U8
    &&& text_parts_wf(u64_part(pv[po]), u8_part(pv[pb]), n)
    &&& forall|i: int| 0 <= i < n ==> #[trigger] text_entry(u64_part(pv[po]), u8_part(pv[pb]), i) == text_at(c, i)
}

/// The `name` parts: codes per row into the emitted sorted dictionary of `name`'s values.
pub open spec fn name_parts(pv: Seq<PartView>, v: SourceView, name: TextOrder) -> bool {
    let codes = u64_part(pv[P_NAME_CODES as int]);
    let off = u64_part(pv[P_NAME_DICT_OFF as int]);
    let bytes = u8_part(pv[P_NAME_DICT_BYTES as int]);
    &&& pv[P_NAME_CODES as int] is U64
    &&& pv[P_NAME_DICT_OFF as int] is U64
    &&& pv[P_NAME_DICT_BYTES as int] is U8
    &&& codes.len() == source_rows_t0(v)
    &&& off.len() >= 1
    &&& text_parts_wf(off, bytes, off.len() - 1)
    &&& crate::stores::sub::interface::common::text::text_strictly_sorted(off, bytes, off.len() - 1)
    &&& forall|i: int| 0 <= i < source_rows_t0(v) ==> #[trigger] codes[i] < off.len() - 1
        && text_entry(off, bytes, codes[i] as int) == text_at(v.t0_f2, i)
}

} // verus!
