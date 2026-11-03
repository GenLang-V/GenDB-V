//! Reading the parts on the calling thread: every column the query reads as one whole-part extent, as the scan
//! model's slices (`Cols` of storage `facts`, `SCols` of storage `suppliers`), with the o_orderstatus dictionary
//! and the co-clustering flag.
use vstd::prelude::*;
use crate::gendb_entry::stored::StoredParts;
use crate::stores::facts::interface::*;
use crate::stores::facts::interface::common::colfmt::*;
use crate::stores::li_ordruns::interface::{facts_parts, run_lens, RUN_LENS};
use crate::stores::suppliers::interface::{SUPPLIER_FIRST, SU_LAYOUT, SU_SUPPKEY_CODES, SU_SUPPKEY_BASE,
    SU_NAME_OFFS, SU_NAME_BYTES, SU_NATIONKEY_CODES, SU_NATIONKEY_BASE, NATION_FIRST, NA_LAYOUT, NA_NATIONKEY_CODES,
    NA_NATIONKEY_BASE, NA_NAME_OFFS, NA_NAME_BYTES};
use super::model::*;
use super::side::*;
use super::bind::*;

verus! {

/// A group size for the model that decodes like the stored one on `n` rows (`bind::bs_ok`).
pub fn model_bs(stored: u64, n: usize) -> (b: usize)
    requires stored >= 1,
    ensures bs_ok(b as int, stored as int, n as int),
{
    if stored <= n as u64 {
        stored as usize
    } else if n > 0 {
        n
    } else {
        1
    }
}

/// The scan model's columns as whole parts of storage `facts`, with the o_orderstatus dictionary (offsets, bytes)
/// and the co-clustering flag.
pub fn open_facts(st: &mut StoredParts, Ghost(db): Ghost<crate::spec::value::Database>) -> (r: (Cols, &'static [u64], &'static [u8], u64))
    requires fbound(db, facts_parts(old(st)@)), old(st)@.len() == crate::stores::li_ordruns::interface::LI_ORDRUNS_PARTS,
        old(st)@[RUN_LENS as int] is U8,
    ensures
        final(st)@ == old(st)@,
        cols_from_parts(r.0, facts_parts(old(st)@)),
        r.0.rl@ == run_lens(old(st)@),
        facts_parts(old(st)@)[p_oso()] == crate::gendb_entry::layout::PartView::U64(r.1@),
        facts_parts(old(st)@)[p_osy()] == crate::gendb_entry::layout::PartView::U8(r.2@),
        r.3 == u64s(facts_parts(old(st)@)[p_flag()])[0],
{
    let ghost parts = facts_parts(st@);
    proof {
        lemma_parts_shape(db, parts);
    }
    let olay = st.extent_u64(ORDERS_FIRST + OR_LAYOUT, 0, 2);
    let llay = st.extent_u64(LINEITEM_FIRST + LI_LAYOUT, 0, 2);
    let n_o = st.part_len(ORDERS_FIRST + OR_ORDERKEY_CODES);
    let n_l = st.part_len(LINEITEM_FIRST + LI_ORDERKEY_CODES);
    let ng_o = st.part_len(ORDERS_FIRST + OR_ORDERKEY_BASE);
    let ng_l = st.part_len(LINEITEM_FIRST + LI_ORDERKEY_BASE);
    proof {
        assert(olay@ =~= u64s(parts[p_ol()]));
        assert(llay@ =~= u64s(parts[p_ll()]));
    }
    let bs_o = model_bs(olay[1], n_o);
    let bs_l = model_bs(llay[1], n_l);
    let ok_codes = st.extent_u32(ORDERS_FIRST + OR_ORDERKEY_CODES, 0, n_o);
    let ok_bases = st.extent_i64(ORDERS_FIRST + OR_ORDERKEY_BASE, 0, ng_o);
    let os_codes = st.extent_u8(ORDERS_FIRST + OR_ORDERSTATUS_CODES, 0, n_o);
    let os_bases = st.extent_u64(ORDERS_FIRST + OR_ORDERSTATUS_BASE, 0, ng_o);
    let oic_len = st.part_len(ORDERS_FIRST + OR_KEYIDX_CODES);
    let oi_codes = st.extent_u32(ORDERS_FIRST + OR_KEYIDX_CODES, 0, oic_len);
    let oib_len = st.part_len(ORDERS_FIRST + OR_KEYIDX_BASE);
    let oi_bases = st.extent_u64(ORDERS_FIRST + OR_KEYIDX_BASE, 0, oib_len);
    let oi_kind = st.extent_u64(ORDERS_FIRST + OR_KEYIDX_KIND, 0, 1)[0];
    let lk_codes = st.extent_u32(LINEITEM_FIRST + LI_ORDERKEY_CODES, 0, n_l);
    let lk_bases = st.extent_i64(LINEITEM_FIRST + LI_ORDERKEY_BASE, 0, ng_l);
    let ls_codes = st.extent_u32(LINEITEM_FIRST + LI_SUPPKEY_CODES, 0, n_l);
    let ls_bases = st.extent_i64(LINEITEM_FIRST + LI_SUPPKEY_BASE, 0, ng_l);
    let lc_codes = st.extent_u16(LINEITEM_FIRST + LI_COMMITDATE_CODES, 0, n_l);
    let lc_bases = st.extent_i64(LINEITEM_FIRST + LI_COMMITDATE_BASE, 0, ng_l);
    let lr_codes = st.extent_u16(LINEITEM_FIRST + LI_RECEIPTDATE_CODES, 0, n_l);
    let lr_bases = st.extent_i64(LINEITEM_FIRST + LI_RECEIPTDATE_BASE, 0, ng_l);
    let dlen = st.part_len(ORDERS_FIRST + OR_ORDERSTATUS_DICT_OFFS);
    let doffs = st.extent_u64(ORDERS_FIRST + OR_ORDERSTATUS_DICT_OFFS, 0, dlen);
    let dblen = st.part_len(ORDERS_FIRST + OR_ORDERSTATUS_DICT_BYTES);
    let dbytes = st.extent_u8(ORDERS_FIRST + OR_ORDERSTATUS_DICT_BYTES, 0, dblen);
    let flag = st.extent_u64(FACTS_CLUSTER, 0, 1)[0];
    let n_r = st.part_len(RUN_LENS);
    let rl = st.extent_u8(RUN_LENS, 0, n_r);
    let c = Cols {
        ok_codes, ok_bases, os_codes, os_bases, oi_codes, oi_bases, oi_kind, n_o, bs_o,
        lk_codes, lk_bases, ls_codes, ls_bases, lc_codes, lc_bases, lr_codes, lr_bases, n_l, bs_l, rl,
    };
    proof {
        assert(ok_codes@ =~= u32s(parts[p_okc()]));
        assert(ok_bases@ =~= i64s(parts[p_okb()]));
        assert(os_codes@ =~= u8s(parts[p_osc()]));
        assert(os_bases@ =~= u64s(parts[p_osb()]));
        assert(oi_codes@ =~= u32s(parts[p_oic()]));
        assert(oi_bases@ =~= u64s(parts[p_oib()]));
        assert(lk_codes@ =~= u32s(parts[p_lkc()]));
        assert(lk_bases@ =~= i64s(parts[p_lkb()]));
        assert(ls_codes@ =~= u32s(parts[p_lsc()]));
        assert(ls_bases@ =~= i64s(parts[p_lsb()]));
        assert(lc_codes@ =~= u16s(parts[p_lcc()]));
        assert(lc_bases@ =~= i64s(parts[p_lcb()]));
        assert(lr_codes@ =~= u16s(parts[p_lrc()]));
        assert(lr_bases@ =~= i64s(parts[p_lrb()]));
        assert(doffs@ =~= u64s(parts[p_oso()]));
        assert(dbytes@ =~= u8s(parts[p_osy()]));
        assert(rl@ =~= run_lens(st@));
    }
    (c, doffs, dbytes, flag)
}

/// The supplier and nation columns as whole parts of storage `suppliers`.
pub fn open_suppliers(st: &mut StoredParts, Ghost(db): Ghost<crate::spec::value::Database>) -> (c: SCols)
    requires sbound(db, old(st)@),
    ensures
        final(st)@ == old(st)@,
        scols_from_parts(c, old(st)@),
{
    let ghost parts = st@;
    proof {
        lemma_sparts_shape(db, parts);
    }
    let slay = st.extent_u64(SUPPLIER_FIRST + SU_LAYOUT, 0, 2);
    let nlay = st.extent_u64(NATION_FIRST + NA_LAYOUT, 0, 2);
    let n_s = st.part_len(SUPPLIER_FIRST + SU_SUPPKEY_CODES);
    let n_n = st.part_len(NATION_FIRST + NA_NATIONKEY_CODES);
    let ng_s = st.part_len(SUPPLIER_FIRST + SU_SUPPKEY_BASE);
    let ng_n = st.part_len(NATION_FIRST + NA_NATIONKEY_BASE);
    proof {
        assert(slay@ =~= u64s(parts[p_sl()]));
        assert(nlay@ =~= u64s(parts[p_nl()]));
    }
    let bs_s = model_bs(slay[1], n_s);
    let bs_n = model_bs(nlay[1], n_n);
    let sk_codes = st.extent_u32(SUPPLIER_FIRST + SU_SUPPKEY_CODES, 0, n_s);
    let sk_bases = st.extent_i64(SUPPLIER_FIRST + SU_SUPPKEY_BASE, 0, ng_s);
    let sn_codes = st.extent_u8(SUPPLIER_FIRST + SU_NATIONKEY_CODES, 0, n_s);
    let sn_bases = st.extent_i64(SUPPLIER_FIRST + SU_NATIONKEY_BASE, 0, ng_s);
    let smo_len = st.part_len(SUPPLIER_FIRST + SU_NAME_OFFS);
    let sm_offs = st.extent_u64(SUPPLIER_FIRST + SU_NAME_OFFS, 0, smo_len);
    let smb_len = st.part_len(SUPPLIER_FIRST + SU_NAME_BYTES);
    let sm_bytes = st.extent_u8(SUPPLIER_FIRST + SU_NAME_BYTES, 0, smb_len);
    let nk_codes = st.extent_u8(NATION_FIRST + NA_NATIONKEY_CODES, 0, n_n);
    let nk_bases = st.extent_i64(NATION_FIRST + NA_NATIONKEY_BASE, 0, ng_n);
    let nmo_len = st.part_len(NATION_FIRST + NA_NAME_OFFS);
    let nm_offs = st.extent_u64(NATION_FIRST + NA_NAME_OFFS, 0, nmo_len);
    let nmb_len = st.part_len(NATION_FIRST + NA_NAME_BYTES);
    let nm_bytes = st.extent_u8(NATION_FIRST + NA_NAME_BYTES, 0, nmb_len);
    let c = SCols { sk_codes, sk_bases, sn_codes, sn_bases, sm_offs, sm_bytes, n_s, bs_s, nk_codes, nk_bases, nm_offs, nm_bytes, n_n, bs_n };
    proof {
        assert(sk_codes@ =~= u32s(parts[p_skc()]));
        assert(sk_bases@ =~= i64s(parts[p_skb()]));
        assert(sn_codes@ =~= u8s(parts[p_snc()]));
        assert(sn_bases@ =~= i64s(parts[p_snb()]));
        assert(sm_offs@ =~= u64s(parts[p_smo()]));
        assert(sm_bytes@ =~= u8s(parts[p_smy()]));
        assert(nk_codes@ =~= u8s(parts[p_nkc()]));
        assert(nk_bases@ =~= i64s(parts[p_nkb()]));
        assert(nm_offs@ =~= u64s(parts[p_nmo()]));
        assert(nm_bytes@ =~= u8s(parts[p_nmy()]));
    }
    c
}

} // verus!
