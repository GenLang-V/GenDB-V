//! Opening the scan's slices: whole parts of the storages (`whole_*`, one extent request each), the model group
//! sizes (`model_bs`), and the part kinds and lengths the requests need (`*_kinds`, from each storage's
//! `represents`). Lineitem and orders are read from storage `li_okruns`: facts' 75 parts (`fpv`) and the run
//! starts of l_orderkey after them (`runs_kind`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::{StoredParts, part_len};
use crate::gendb_entry::stores::{Stores, StoresView};
use crate::spec::value::*;
use crate::spec::typing::db_wf;
use crate::stores::facts::interface::*;
use crate::stores::facts::interface::common::colfmt::*;
use crate::stores::suppliers::interface::{SUPPLIER_FIRST, SU_LAYOUT, SU_GROUPS, SU_SUPPKEY_CODES, SU_SUPPKEY_BASE,
    SU_NATIONKEY_CODES, SU_NATIONKEY_BASE, SU_KEYIDX_KIND, supplier_ok, NATION_FIRST, NA_LAYOUT, NA_GROUPS,
    NA_NATIONKEY_CODES, NA_NATIONKEY_BASE, NA_NAME_OFFS, NA_NAME_BYTES, nation_ok};
use crate::stores::custpart::interface::{CUSTOMER_FIRST, CU_LAYOUT, CU_GROUPS, CU_CUSTKEY_CODES, CU_CUSTKEY_BASE,
    CU_NATIONKEY_CODES, CU_NATIONKEY_BASE, CU_KEYIDX_KIND, customer_ok};
use crate::stores::suppliers::interface::common::colfmt as scf;
use crate::stores::custpart::interface::common::colfmt as ccf;
use super::model::*;
use super::bind::*;

verus! {

// ------------------------------------------------------------------------------------------------ whole parts

pub fn whole_u8(st: &mut StoredParts, p: usize) -> (r: &'static [u8])
    requires p < old(st)@.len(), old(st)@[p as int] is U8,
    ensures final(st)@ == old(st)@, PartView::U8(r@) == old(st)@[p as int],
{
    let n = st.part_len(p);
    let r = st.extent_u8(p, 0, n);
    proof {
        assert(r@ =~= old(st)@[p as int]->U8_0);
    }
    r
}

pub fn whole_u16(st: &mut StoredParts, p: usize) -> (r: &'static [u16])
    requires p < old(st)@.len(), old(st)@[p as int] is U16,
    ensures final(st)@ == old(st)@, PartView::U16(r@) == old(st)@[p as int],
{
    let n = st.part_len(p);
    let r = st.extent_u16(p, 0, n);
    proof {
        assert(r@ =~= old(st)@[p as int]->U16_0);
    }
    r
}

pub fn whole_u32(st: &mut StoredParts, p: usize) -> (r: &'static [u32])
    requires p < old(st)@.len(), old(st)@[p as int] is U32,
    ensures final(st)@ == old(st)@, PartView::U32(r@) == old(st)@[p as int],
{
    let n = st.part_len(p);
    let r = st.extent_u32(p, 0, n);
    proof {
        assert(r@ =~= old(st)@[p as int]->U32_0);
    }
    r
}

pub fn whole_u64(st: &mut StoredParts, p: usize) -> (r: &'static [u64])
    requires p < old(st)@.len(), old(st)@[p as int] is U64,
    ensures final(st)@ == old(st)@, PartView::U64(r@) == old(st)@[p as int],
{
    let n = st.part_len(p);
    let r = st.extent_u64(p, 0, n);
    proof {
        assert(r@ =~= old(st)@[p as int]->U64_0);
    }
    r
}

pub fn whole_i64(st: &mut StoredParts, p: usize) -> (r: &'static [i64])
    requires p < old(st)@.len(), old(st)@[p as int] is I64,
    ensures final(st)@ == old(st)@, PartView::I64(r@) == old(st)@[p as int],
{
    let n = st.part_len(p);
    let r = st.extent_i64(p, 0, n);
    proof {
        assert(r@ =~= old(st)@[p as int]->I64_0);
    }
    r
}

/// A model group size: the stored one when it does not exceed the rows, else the rows (or 1 without rows).
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

// ------------------------------------------------------------------------------------------------ kinds

/// Kinds and sizes of the lineitem parts the scan opens.
pub open spec fn li_kinds(p: Seq<PartView>) -> bool {
    &&& p.len() == FACTS_PARTS
    &&& p[LI_LAYOUT as int] is U64 && u64s(p[LI_LAYOUT as int]).len() == 2 && u64s(p[LI_LAYOUT as int])[1] >= 1
    &&& p[LI_SHIPDATE_CODES as int] is U16 && part_len(p[LI_SHIPDATE_CODES as int]) == u64s(p[LI_LAYOUT as int])[0]
    &&& p[LI_SHIPDATE_BASE as int] is I64 && p[LI_SHIPDATE_ZMAX as int] is I64
    &&& p[LI_SUPPKEY_CODES as int] is U32 && p[LI_SUPPKEY_BASE as int] is I64
    &&& p[LI_LINENUMBER_CODES as int] is U8 && p[LI_LINENUMBER_BASE as int] is I64
    &&& p[LI_ORDERKEY_CODES as int] is U32 && p[LI_ORDERKEY_BASE as int] is I64
    &&& p[LI_EXTENDEDPRICE_CODES as int] is U32 && p[LI_EXTENDEDPRICE_BASE as int] is I64
    &&& p[LI_DISCOUNT_CODES as int] is U8 && p[LI_DISCOUNT_BASE as int] is I64
}

/// Kinds and sizes of the orders parts the scan opens.
pub open spec fn ord_kinds(p: Seq<PartView>) -> bool {
    &&& p.len() == FACTS_PARTS
    &&& p[ORDERS_FIRST + OR_LAYOUT] is U64 && u64s(p[ORDERS_FIRST + OR_LAYOUT]).len() == 2
    &&& u64s(p[ORDERS_FIRST + OR_LAYOUT])[1] >= 1
    &&& p[ORDERS_FIRST + OR_ORDERKEY_CODES] is U32
    &&& part_len(p[ORDERS_FIRST + OR_ORDERKEY_CODES]) == u64s(p[ORDERS_FIRST + OR_LAYOUT])[0]
    &&& p[ORDERS_FIRST + OR_ORDERKEY_BASE] is I64
    &&& p[ORDERS_FIRST + OR_KEYIDX_CODES] is U32 && p[ORDERS_FIRST + OR_KEYIDX_BASE] is U64
    &&& p[ORDERS_FIRST + OR_KEYIDX_KIND] is U64 && u64s(p[ORDERS_FIRST + OR_KEYIDX_KIND]).len() == 1
    &&& p[ORDERS_FIRST + OR_CUSTKEY_CODES] is U32 && p[ORDERS_FIRST + OR_CUSTKEY_BASE] is I64
}

/// Kinds and sizes of the supplier parts.
pub open spec fn sup_kinds(p: Seq<PartView>) -> bool {
    &&& p.len() == crate::stores::suppliers::interface::SUPPLIERS_PARTS
    &&& p[SUPPLIER_FIRST + SU_LAYOUT] is U64 && scf::u64s(p[SUPPLIER_FIRST + SU_LAYOUT]).len() == 2
    &&& scf::u64s(p[SUPPLIER_FIRST + SU_LAYOUT])[1] >= 1
    &&& p[SUPPLIER_FIRST + SU_SUPPKEY_CODES] is U32
    &&& part_len(p[SUPPLIER_FIRST + SU_SUPPKEY_CODES]) == scf::u64s(p[SUPPLIER_FIRST + SU_LAYOUT])[0]
    &&& p[SUPPLIER_FIRST + SU_SUPPKEY_BASE] is I64
    &&& p[SUPPLIER_FIRST + SU_NATIONKEY_CODES] is U8 && p[SUPPLIER_FIRST + SU_NATIONKEY_BASE] is I64
    &&& p[SUPPLIER_FIRST + SU_KEYIDX_KIND] is U64 && scf::u64s(p[SUPPLIER_FIRST + SU_KEYIDX_KIND]).len() == 1
}

/// Kinds and sizes of the customer parts.
pub open spec fn cus_kinds(p: Seq<PartView>) -> bool {
    &&& p.len() == crate::stores::custpart::interface::CUSTPART_PARTS
    &&& p[CUSTOMER_FIRST + CU_LAYOUT] is U64 && ccf::u64s(p[CUSTOMER_FIRST + CU_LAYOUT]).len() == 2
    &&& ccf::u64s(p[CUSTOMER_FIRST + CU_LAYOUT])[1] >= 1
    &&& p[CUSTOMER_FIRST + CU_CUSTKEY_CODES] is U32
    &&& part_len(p[CUSTOMER_FIRST + CU_CUSTKEY_CODES]) == ccf::u64s(p[CUSTOMER_FIRST + CU_LAYOUT])[0]
    &&& p[CUSTOMER_FIRST + CU_CUSTKEY_BASE] is I64
    &&& p[CUSTOMER_FIRST + CU_NATIONKEY_CODES] is U8 && p[CUSTOMER_FIRST + CU_NATIONKEY_BASE] is I64
    &&& p[CUSTOMER_FIRST + CU_KEYIDX_KIND] is U64 && ccf::u64s(p[CUSTOMER_FIRST + CU_KEYIDX_KIND]).len() == 1
}

pub proof fn lemma_li_kinds(db: Database, p: Seq<PartView>)
    requires represents(p, crate::stores::facts::declaration::stored_relations(db)),
    ensures li_kinds(p),
{
    let t = ltp(p);
    let rel = lrel(db);
    assert(lineitem_ok(t, rel));
    let rows = lineitem_rows(t, rel);
    assert(lineitem_cols_ok(t, rows));
    assert forall|k: int| 0 <= k < 48 implies t[k] == p[k] by {}
    lemma_uniform_groups(t[LI_GROUPS as int], rel.len() as int, u64s(t[LI_LAYOUT as int])[1] as int);
}

pub proof fn lemma_ord_kinds(db: Database, p: Seq<PartView>)
    requires represents(p, crate::stores::facts::declaration::stored_relations(db)),
    ensures ord_kinds(p),
{
    let t = otp(p);
    let rel = orel(db);
    assert(orders_ok(t, rel));
    let rows = orders_rows(t, rel);
    assert(orders_cols_ok(t, rows));
    assert forall|k: int| 0 <= k < 26 implies t[k] == p[48 + k] by {}
}

pub proof fn lemma_sup_kinds(db: Database, p: Seq<PartView>)
    requires crate::stores::suppliers::interface::represents(p, crate::stores::suppliers::declaration::stored_relations(db)),
    ensures sup_kinds(p),
{
    let t = stp(p);
    let rel = srel(db);
    assert(supplier_ok(t, rel));
    assert forall|k: int| 0 <= k < 17 implies t[k] == p[13 + k] by {}
}

pub proof fn lemma_cus_kinds(db: Database, p: Seq<PartView>)
    requires crate::stores::custpart::interface::represents(p, crate::stores::custpart::declaration::stored_relations(db)),
    ensures cus_kinds(p),
{
    let t = ctp(p);
    let rel = crel(db);
    assert(customer_ok(t, rel));
    assert forall|k: int| 0 <= k < 21 implies t[k] == p[k] by {}
}

/// Kind and size of the co-clustering flag part.
pub open spec fn clus_kind(p: Seq<PartView>) -> bool {
    &&& p.len() == FACTS_PARTS
    &&& p[FACTS_CLUSTER as int] is U64 && u64s(p[FACTS_CLUSTER as int]).len() == 1
}

pub proof fn lemma_clus_kind(db: Database, p: Seq<PartView>)
    requires represents(p, crate::stores::facts::declaration::stored_relations(db)),
    ensures clus_kind(p),
{
}

/// The run starts part of storage `li_okruns`, after facts' parts.
pub open spec fn runs_kind(sv: StoresView) -> bool {
    &&& sv.li_okruns.len() == crate::stores::li_okruns::interface::LI_OKRUNS_PARTS
    &&& sv.li_okruns[crate::stores::li_okruns::interface::RUN_STARTS as int] is U32
}

/// The co-clustering flag of facts' parts in storage `li_okruns` (1: the stored lines follow the stored orders).
pub fn open_clus(stores: &mut Stores) -> (r: u64)
    requires clus_kind(fpv(old(stores)@)), runs_kind(old(stores)@),
    ensures
        final(stores)@ == old(stores)@,
        u64s(fpv(old(stores)@)[FACTS_CLUSTER as int])[0] == r,
{
    let ghost sv = stores@;
    let f = whole_u64(&mut stores.li_okruns, FACTS_CLUSTER);
    proof {
        assert(fpv(sv)[FACTS_CLUSTER as int] == sv.li_okruns[FACTS_CLUSTER as int]);
    }
    f[0]
}

// ------------------------------------------------------------------------------------------------ the slices

/// Open the lineitem, orders, supplier and customer slices of the scan.
pub fn open_cols(stores: &mut Stores) -> (r: (Cols, u64, u64))
    requires
        li_kinds(fpv(old(stores)@)),
        ord_kinds(fpv(old(stores)@)),
        runs_kind(old(stores)@),
        sup_kinds(old(stores)@.suppliers),
        cus_kinds(old(stores)@.custpart),
    ensures
        final(stores)@ == old(stores)@,
        li_from_parts(r.0, fpv(old(stores)@)),
        ord_from_parts(r.0, fpv(old(stores)@)),
        PartView::U32(r.0.l_st@) == old(stores)@.li_okruns[crate::stores::li_okruns::interface::RUN_STARTS as int],
        r.0.n_st == r.0.l_st@.len(),
        sup_from_parts_kind(r.0, old(stores)@.suppliers, r.1),
        cus_from_parts_kind(r.0, old(stores)@.custpart, r.2),
{
    let ghost sv = stores@;
    proof {
        assert forall|k: int| 0 <= k < FACTS_PARTS implies #[trigger] fpv(sv)[k] == sv.li_okruns[k] by {}
    }
    let fs = &mut stores.li_okruns;
    let llay = whole_u64(fs, LINEITEM_FIRST + LI_LAYOUT);
    let ls_codes = whole_u16(fs, LINEITEM_FIRST + LI_SHIPDATE_CODES);
    let n_l = ls_codes.len();
    let bs_l = model_bs(llay[1], n_l);
    let ls_bases = whole_i64(fs, LINEITEM_FIRST + LI_SHIPDATE_BASE);
    let ls_zmax = whole_i64(fs, LINEITEM_FIRST + LI_SHIPDATE_ZMAX);
    let lsk_codes = whole_u32(fs, LINEITEM_FIRST + LI_SUPPKEY_CODES);
    let lsk_bases = whole_i64(fs, LINEITEM_FIRST + LI_SUPPKEY_BASE);
    let lln_codes = whole_u8(fs, LINEITEM_FIRST + LI_LINENUMBER_CODES);
    let lln_bases = whole_i64(fs, LINEITEM_FIRST + LI_LINENUMBER_BASE);
    let lok_codes = whole_u32(fs, LINEITEM_FIRST + LI_ORDERKEY_CODES);
    let lok_bases = whole_i64(fs, LINEITEM_FIRST + LI_ORDERKEY_BASE);
    let lp_codes = whole_u32(fs, LINEITEM_FIRST + LI_EXTENDEDPRICE_CODES);
    let lp_bases = whole_i64(fs, LINEITEM_FIRST + LI_EXTENDEDPRICE_BASE);
    let ld_codes = whole_u8(fs, LINEITEM_FIRST + LI_DISCOUNT_CODES);
    let ld_bases = whole_i64(fs, LINEITEM_FIRST + LI_DISCOUNT_BASE);
    let olay = whole_u64(fs, ORDERS_FIRST + OR_LAYOUT);
    let ok_codes = whole_u32(fs, ORDERS_FIRST + OR_ORDERKEY_CODES);
    let n_o = ok_codes.len();
    let bs_o = model_bs(olay[1], n_o);
    let ok_bases = whole_i64(fs, ORDERS_FIRST + OR_ORDERKEY_BASE);
    let oi_codes = whole_u32(fs, ORDERS_FIRST + OR_KEYIDX_CODES);
    let oi_bases = whole_u64(fs, ORDERS_FIRST + OR_KEYIDX_BASE);
    let oi_kind = whole_u64(fs, ORDERS_FIRST + OR_KEYIDX_KIND)[0];
    let oc_codes = whole_u32(fs, ORDERS_FIRST + OR_CUSTKEY_CODES);
    let oc_bases = whole_i64(fs, ORDERS_FIRST + OR_CUSTKEY_BASE);
    let no_codes = fs.extent_u32(ORDERS_FIRST + OR_KEYIDX_CODES, 0, 0);
    let no_bases = fs.extent_u64(ORDERS_FIRST + OR_KEYIDX_BASE, 0, 0);
    let l_st = whole_u32(fs, crate::stores::li_okruns::interface::RUN_STARTS);
    let ss = &mut stores.suppliers;
    let slay = whole_u64(ss, SUPPLIER_FIRST + SU_LAYOUT);
    let sk_codes = whole_u32(ss, SUPPLIER_FIRST + SU_SUPPKEY_CODES);
    let n_s = sk_codes.len();
    let bs_s = model_bs(slay[1], n_s);
    let sk_bases = whole_i64(ss, SUPPLIER_FIRST + SU_SUPPKEY_BASE);
    let sn_codes = whole_u8(ss, SUPPLIER_FIRST + SU_NATIONKEY_CODES);
    let sn_bases = whole_i64(ss, SUPPLIER_FIRST + SU_NATIONKEY_BASE);
    let s_stored = whole_u64(ss, SUPPLIER_FIRST + SU_KEYIDX_KIND)[0];
    let cs = &mut stores.custpart;
    let clay = whole_u64(cs, CUSTOMER_FIRST + CU_LAYOUT);
    let ck_codes = whole_u32(cs, CUSTOMER_FIRST + CU_CUSTKEY_CODES);
    let n_c = ck_codes.len();
    let bs_c = model_bs(clay[1], n_c);
    let ck_bases = whole_i64(cs, CUSTOMER_FIRST + CU_CUSTKEY_BASE);
    let cn_codes = whole_u8(cs, CUSTOMER_FIRST + CU_NATIONKEY_CODES);
    let cn_bases = whole_i64(cs, CUSTOMER_FIRST + CU_NATIONKEY_BASE);
    let c_stored = whole_u64(cs, CUSTOMER_FIRST + CU_KEYIDX_KIND)[0];
    let c = Cols {
        ls_codes, ls_bases, ls_zmax, lsk_codes, lsk_bases, lln_codes, lln_bases, lok_codes, lok_bases,
        lp_codes, lp_bases, ld_codes, ld_bases, n_l, bs_l,
        ok_codes, ok_bases, oi_codes, oi_bases, oi_kind, oc_codes, oc_bases, n_o, bs_o,
        sk_codes, sk_bases, sn_codes, sn_bases, s_kind: if s_stored == 1 { 1 } else { 0 }, n_s, bs_s,
        ck_codes, ck_bases, cn_codes, cn_bases, c_kind: if c_stored == 1 { 1 } else { 0 }, n_c, bs_c,
        no_codes, no_bases, l_st, n_st: l_st.len(),
    };
    proof {
        let (fp, sp, cp) = (fpv(sv), sv.suppliers, sv.custpart);
        assert forall|k: int| 0 <= k < 48 implies ltp(fp)[k] == fp[k] by {}
        assert forall|k: int| 0 <= k < 26 implies otp(fp)[k] == fp[48 + k] by {}
        assert forall|k: int| 0 <= k < 17 implies stp(sp)[k] == sp[13 + k] by {}
        assert forall|k: int| 0 <= k < 21 implies ctp(cp)[k] == cp[k] by {}
        assert(no_codes@ =~= Seq::<u32>::empty());
        assert(no_bases@ =~= Seq::<u64>::empty());
    }
    (c, s_stored, c_stored)
}

} // verus!
