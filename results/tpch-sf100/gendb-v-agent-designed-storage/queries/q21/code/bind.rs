//! Part positions and shapes of the two storages the query reads, and what a database bound to them gives the
//! models: `fbound` (storage `facts`: lineitem and orders) and `sbound` (storage `suppliers`: supplier and nation),
//! the slices of the models as whole parts (`cols_from_parts`, `scols_from_parts`) and the kinds and lengths the
//! extent requests need (`parts_shape`, `sparts_shape`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::*;
use crate::spec::typing::*;
use crate::spec::constraints::*;
use crate::schema::schema_spec;
use crate::gendb_constraints::declared_db;
use crate::stores::facts::interface::*;
use crate::stores::facts::interface::common::colfmt::*;
use crate::stores::suppliers::interface as si;
use super::model::*;
use super::side::*;

verus! {

pub open spec fn u16s(p: PartView) -> Seq<u16> {
    match p {
        PartView::U16(s) => s,
        _ => Seq::empty(),
    }
}

/// The database facts every link needs.
pub open spec fn db_ok(db: Database) -> bool {
    db.schema == schema_spec() && db_wf(db)
}

// ------------------------------------------------------------------------------------------------ storage facts

/// Absolute part positions of storage `facts` the query reads.
pub open spec fn p_ol() -> int { (ORDERS_FIRST + OR_LAYOUT) as int }
pub open spec fn p_og() -> int { (ORDERS_FIRST + OR_GROUPS) as int }
pub open spec fn p_okc() -> int { (ORDERS_FIRST + OR_ORDERKEY_CODES) as int }
pub open spec fn p_okb() -> int { (ORDERS_FIRST + OR_ORDERKEY_BASE) as int }
pub open spec fn p_osc() -> int { (ORDERS_FIRST + OR_ORDERSTATUS_CODES) as int }
pub open spec fn p_osb() -> int { (ORDERS_FIRST + OR_ORDERSTATUS_BASE) as int }
pub open spec fn p_oso() -> int { (ORDERS_FIRST + OR_ORDERSTATUS_DICT_OFFS) as int }
pub open spec fn p_osy() -> int { (ORDERS_FIRST + OR_ORDERSTATUS_DICT_BYTES) as int }
pub open spec fn p_oic() -> int { (ORDERS_FIRST + OR_KEYIDX_CODES) as int }
pub open spec fn p_oib() -> int { (ORDERS_FIRST + OR_KEYIDX_BASE) as int }
pub open spec fn p_oik() -> int { (ORDERS_FIRST + OR_KEYIDX_KIND) as int }
pub open spec fn p_ll() -> int { (LINEITEM_FIRST + LI_LAYOUT) as int }
pub open spec fn p_lg() -> int { (LINEITEM_FIRST + LI_GROUPS) as int }
pub open spec fn p_lkc() -> int { (LINEITEM_FIRST + LI_ORDERKEY_CODES) as int }
pub open spec fn p_lkb() -> int { (LINEITEM_FIRST + LI_ORDERKEY_BASE) as int }
pub open spec fn p_lsc() -> int { (LINEITEM_FIRST + LI_SUPPKEY_CODES) as int }
pub open spec fn p_lsb() -> int { (LINEITEM_FIRST + LI_SUPPKEY_BASE) as int }
pub open spec fn p_lcc() -> int { (LINEITEM_FIRST + LI_COMMITDATE_CODES) as int }
pub open spec fn p_lcb() -> int { (LINEITEM_FIRST + LI_COMMITDATE_BASE) as int }
pub open spec fn p_lrc() -> int { (LINEITEM_FIRST + LI_RECEIPTDATE_CODES) as int }
pub open spec fn p_lrb() -> int { (LINEITEM_FIRST + LI_RECEIPTDATE_BASE) as int }
pub open spec fn p_flag() -> int { FACTS_CLUSTER as int }

/// The orders parts and the lineitem parts.
pub open spec fn otp(parts: Seq<PartView>) -> Seq<PartView> {
    parts.subrange(ORDERS_FIRST as int, (ORDERS_FIRST + OR_PARTS) as int)
}

pub open spec fn ltp(parts: Seq<PartView>) -> Seq<PartView> {
    parts.subrange(LINEITEM_FIRST as int, (LINEITEM_FIRST + LI_PARTS) as int)
}

/// The stored relations of lineitem and orders.
pub open spec fn lrel_of(db: Database) -> Seq<Row> {
    crate::stores::facts::declaration::stored_relations(db)[0]
}

pub open spec fn orel_of(db: Database) -> Seq<Row> {
    crate::stores::facts::declaration::stored_relations(db)[1]
}

/// The stored orders rows and stored lineitem rows of `db` in storage order.
pub open spec fn orows(parts: Seq<PartView>, db: Database) -> Seq<Row> {
    orders_rows(otp(parts), orel_of(db))
}

pub open spec fn lrows(parts: Seq<PartView>, db: Database) -> Seq<Row> {
    lineitem_rows(ltp(parts), lrel_of(db))
}

/// Number of row groups of orders and of lineitem.
pub open spec fn ng_o(parts: Seq<PartView>) -> int {
    u64s(parts[p_og()]).len() - 1
}

pub open spec fn ng_l(parts: Seq<PartView>) -> int {
    u64s(parts[p_lg()]).len() - 1
}

/// Kinds and lengths of every part of `facts` the query reads (what the extent requests need).
pub open spec fn parts_shape(parts: Seq<PartView>) -> bool {
    &&& parts.len() == FACTS_PARTS
    &&& parts[p_ol()] is U64 && u64s(parts[p_ol()]).len() == 2 && u64s(parts[p_ol()])[1] >= 1
    &&& parts[p_og()] is U64 && u64s(parts[p_og()]).len() >= 1
    &&& parts[p_okc()] is U32 && u32s(parts[p_okc()]).len() == u64s(parts[p_ol()])[0]
    &&& parts[p_okb()] is I64 && i64s(parts[p_okb()]).len() == ng_o(parts)
    &&& parts[p_osc()] is U8 && u8s(parts[p_osc()]).len() == u64s(parts[p_ol()])[0]
    &&& parts[p_osb()] is U64 && u64s(parts[p_osb()]).len() == ng_o(parts)
    &&& parts[p_oso()] is U64 && u64s(parts[p_oso()]).len() >= 1
    &&& parts[p_osy()] is U8
    &&& parts[p_oic()] is U32
    &&& parts[p_oib()] is U64
    &&& parts[p_oik()] is U64 && u64s(parts[p_oik()]).len() == 1
    &&& parts[p_ll()] is U64 && u64s(parts[p_ll()]).len() == 2 && u64s(parts[p_ll()])[1] >= 1
    &&& parts[p_lg()] is U64 && u64s(parts[p_lg()]).len() >= 1
    &&& parts[p_lkc()] is U32 && u32s(parts[p_lkc()]).len() == u64s(parts[p_ll()])[0]
    &&& parts[p_lkb()] is I64 && i64s(parts[p_lkb()]).len() == ng_l(parts)
    &&& parts[p_lsc()] is U32 && u32s(parts[p_lsc()]).len() == u64s(parts[p_ll()])[0]
    &&& parts[p_lsb()] is I64 && i64s(parts[p_lsb()]).len() == ng_l(parts)
    &&& parts[p_lcc()] is U16 && u16s(parts[p_lcc()]).len() == u64s(parts[p_ll()])[0]
    &&& parts[p_lcb()] is I64 && i64s(parts[p_lcb()]).len() == ng_l(parts)
    &&& parts[p_lrc()] is U16 && u16s(parts[p_lrc()]).len() == u64s(parts[p_ll()])[0]
    &&& parts[p_lrb()] is I64 && i64s(parts[p_lrb()]).len() == ng_l(parts)
    &&& parts[p_flag()] is U64 && u64s(parts[p_flag()]).len() == 1
}

/// The model's group size `b` decodes like the stored group size `stored_bs` on rows below `n`: equal, or both at least
/// `n` (every row then lies in group 0).
pub open spec fn bs_ok(b: int, stored_bs: int, n: int) -> bool {
    b >= 1 && (b == stored_bs || (b >= n && stored_bs >= n))
}

/// The model's slices are whole parts of storage `facts`.
pub open spec fn cols_from_parts(c: Cols, parts: Seq<PartView>) -> bool {
    &&& parts_shape(parts)
    &&& c.n_o as int == u64s(parts[p_ol()])[0]
    &&& bs_ok(c.bs_o as int, u64s(parts[p_ol()])[1] as int, c.n_o as int)
    &&& parts[p_okc()] == PartView::U32(c.ok_codes@)
    &&& parts[p_okb()] == PartView::I64(c.ok_bases@)
    &&& parts[p_osc()] == PartView::U8(c.os_codes@)
    &&& parts[p_osb()] == PartView::U64(c.os_bases@)
    &&& parts[p_oic()] == PartView::U32(c.oi_codes@)
    &&& parts[p_oib()] == PartView::U64(c.oi_bases@)
    &&& u64s(parts[p_oik()])[0] == c.oi_kind
    &&& c.n_l as int == u64s(parts[p_ll()])[0]
    &&& bs_ok(c.bs_l as int, u64s(parts[p_ll()])[1] as int, c.n_l as int)
    &&& parts[p_lkc()] == PartView::U32(c.lk_codes@)
    &&& parts[p_lkb()] == PartView::I64(c.lk_bases@)
    &&& parts[p_lsc()] == PartView::U32(c.ls_codes@)
    &&& parts[p_lsb()] == PartView::I64(c.ls_bases@)
    &&& parts[p_lcc()] == PartView::U16(c.lc_codes@)
    &&& parts[p_lcb()] == PartView::I64(c.lc_bases@)
    &&& parts[p_lrc()] == PartView::U16(c.lr_codes@)
    &&& parts[p_lrb()] == PartView::I64(c.lr_bases@)
}

/// A database bound to the parts of storage `facts`.
pub open spec fn fbound(db: Database, parts: Seq<PartView>) -> bool {
    &&& db_ok(db)
    &&& constraints_hold(declared_db(db))
    &&& represents(parts, crate::stores::facts::declaration::stored_relations(db))
}

/// A database bound to the parts `lp` of storage `li_ordruns` (facts' parts first, then the run lengths).
pub open spec fn lo_bound(db: Database, lp: Seq<PartView>) -> bool {
    &&& db_ok(db)
    &&& constraints_hold(declared_db(db))
    &&& crate::stores::li_ordruns::interface::represents(lp, crate::stores::li_ordruns::declaration::stored_relations(db))
}

/// li_ordruns represents facts' relations in its inherited parts, and the run lengths of the stored lineitem rows.
pub proof fn lemma_lo_bound(db: Database, lp: Seq<PartView>)
    requires lo_bound(db, lp),
    ensures
        fbound(db, crate::stores::li_ordruns::interface::facts_parts(lp)),
        lp.len() == crate::stores::li_ordruns::interface::LI_ORDRUNS_PARTS,
        lp[crate::stores::li_ordruns::interface::RUN_LENS as int] is U8,
        crate::stores::li_ordruns::interface::runs_ok(lrows(crate::stores::li_ordruns::interface::facts_parts(lp), db),
            crate::stores::li_ordruns::interface::run_lens(lp)),
{
    assert(crate::stores::li_ordruns::declaration::stored_relations(db)
        =~= crate::stores::facts::declaration::stored_relations(db));
    assert(crate::stores::li_ordruns::interface::stored_lines(lp, crate::stores::li_ordruns::declaration::stored_relations(db))
        == lrows(crate::stores::li_ordruns::interface::facts_parts(lp), db));
}

/// The parts the query reads have the kinds and lengths `parts_shape` lists.
pub proof fn lemma_parts_shape(db: Database, parts: Seq<PartView>)
    requires fbound(db, parts),
    ensures
        parts_shape(parts),
        u64s(parts[p_ol()])[0] == orel_of(db).len(),
        u64s(parts[p_ll()])[0] == lrel_of(db).len(),
{
    let o = otp(parts);
    let l = ltp(parts);
    let orel = orel_of(db);
    let lrel = lrel_of(db);
    assert(orders_ok(o, orel));
    assert(lineitem_ok(l, lrel));
    let (no, nl) = (orel.len() as int, lrel.len() as int);
    let orows = orders_rows(o, orel);
    let lrows = lineitem_rows(l, lrel);
    assert(orows.len() == no);
    assert(lrows.len() == nl);
    assert(o[OR_LAYOUT as int] == parts[p_ol()]);
    assert(o[OR_GROUPS as int] == parts[p_og()]);
    assert(o[OR_ORDERKEY_CODES as int] == parts[p_okc()]);
    assert(o[OR_ORDERKEY_BASE as int] == parts[p_okb()]);
    assert(o[OR_ORDERSTATUS_CODES as int] == parts[p_osc()]);
    assert(o[OR_ORDERSTATUS_BASE as int] == parts[p_osb()]);
    assert(o[OR_ORDERSTATUS_DICT_OFFS as int] == parts[p_oso()]);
    assert(o[OR_ORDERSTATUS_DICT_BYTES as int] == parts[p_osy()]);
    assert(o[OR_KEYIDX_CODES as int] == parts[p_oic()]);
    assert(o[OR_KEYIDX_BASE as int] == parts[p_oib()]);
    assert(o[OR_KEYIDX_KIND as int] == parts[p_oik()]);
    assert(l[LI_LAYOUT as int] == parts[p_ll()]);
    assert(l[LI_GROUPS as int] == parts[p_lg()]);
    assert(l[LI_ORDERKEY_CODES as int] == parts[p_lkc()]);
    assert(l[LI_ORDERKEY_BASE as int] == parts[p_lkb()]);
    assert(l[LI_SUPPKEY_CODES as int] == parts[p_lsc()]);
    assert(l[LI_SUPPKEY_BASE as int] == parts[p_lsb()]);
    assert(l[LI_COMMITDATE_CODES as int] == parts[p_lcc()]);
    assert(l[LI_COMMITDATE_BASE as int] == parts[p_lcb()]);
    assert(l[LI_RECEIPTDATE_CODES as int] == parts[p_lrc()]);
    assert(l[LI_RECEIPTDATE_BASE as int] == parts[p_lrb()]);
    lemma_uniform_groups(parts[p_og()], no, u64s(parts[p_ol()])[1] as int);
    lemma_uniform_groups(parts[p_lg()], nl, u64s(parts[p_ll()])[1] as int);
}

// ------------------------------------------------------------------------------------------------ storage suppliers

/// Absolute part positions of storage `suppliers` the query reads.
pub open spec fn p_sl() -> int { (si::SUPPLIER_FIRST + si::SU_LAYOUT) as int }
pub open spec fn p_sg() -> int { (si::SUPPLIER_FIRST + si::SU_GROUPS) as int }
pub open spec fn p_skc() -> int { (si::SUPPLIER_FIRST + si::SU_SUPPKEY_CODES) as int }
pub open spec fn p_skb() -> int { (si::SUPPLIER_FIRST + si::SU_SUPPKEY_BASE) as int }
pub open spec fn p_snc() -> int { (si::SUPPLIER_FIRST + si::SU_NATIONKEY_CODES) as int }
pub open spec fn p_snb() -> int { (si::SUPPLIER_FIRST + si::SU_NATIONKEY_BASE) as int }
pub open spec fn p_smo() -> int { (si::SUPPLIER_FIRST + si::SU_NAME_OFFS) as int }
pub open spec fn p_smy() -> int { (si::SUPPLIER_FIRST + si::SU_NAME_BYTES) as int }
pub open spec fn p_nl() -> int { (si::NATION_FIRST + si::NA_LAYOUT) as int }
pub open spec fn p_ng() -> int { (si::NATION_FIRST + si::NA_GROUPS) as int }
pub open spec fn p_nkc() -> int { (si::NATION_FIRST + si::NA_NATIONKEY_CODES) as int }
pub open spec fn p_nkb() -> int { (si::NATION_FIRST + si::NA_NATIONKEY_BASE) as int }
pub open spec fn p_nmo() -> int { (si::NATION_FIRST + si::NA_NAME_OFFS) as int }
pub open spec fn p_nmy() -> int { (si::NATION_FIRST + si::NA_NAME_BYTES) as int }

/// The supplier parts and the nation parts.
pub open spec fn stp(parts: Seq<PartView>) -> Seq<PartView> {
    parts.subrange(si::SUPPLIER_FIRST as int, (si::SUPPLIER_FIRST + si::SU_PARTS) as int)
}

pub open spec fn ntp(parts: Seq<PartView>) -> Seq<PartView> {
    parts.subrange(si::NATION_FIRST as int, (si::NATION_FIRST + si::NA_PARTS) as int)
}

/// The stored relations of supplier and nation.
pub open spec fn srel_of(db: Database) -> Seq<Row> {
    crate::stores::suppliers::declaration::stored_relations(db)[1]
}

pub open spec fn nrel_of(db: Database) -> Seq<Row> {
    crate::stores::suppliers::declaration::stored_relations(db)[2]
}

pub open spec fn ng_s(parts: Seq<PartView>) -> int {
    u64s(parts[p_sg()]).len() - 1
}

pub open spec fn ng_n(parts: Seq<PartView>) -> int {
    u64s(parts[p_ng()]).len() - 1
}

/// Kinds and lengths of every part of `suppliers` the query reads.
pub open spec fn sparts_shape(parts: Seq<PartView>) -> bool {
    &&& parts.len() == si::SUPPLIERS_PARTS
    &&& parts[p_sl()] is U64 && u64s(parts[p_sl()]).len() == 2 && u64s(parts[p_sl()])[1] >= 1
    &&& parts[p_sg()] is U64 && u64s(parts[p_sg()]).len() >= 1
    &&& parts[p_skc()] is U32 && u32s(parts[p_skc()]).len() == u64s(parts[p_sl()])[0]
    &&& parts[p_skb()] is I64 && i64s(parts[p_skb()]).len() == ng_s(parts)
    &&& parts[p_snc()] is U8 && u8s(parts[p_snc()]).len() == u64s(parts[p_sl()])[0]
    &&& parts[p_snb()] is I64 && i64s(parts[p_snb()]).len() == ng_s(parts)
    &&& parts[p_smo()] is U64
    &&& parts[p_smy()] is U8
    &&& parts[p_nl()] is U64 && u64s(parts[p_nl()]).len() == 2 && u64s(parts[p_nl()])[1] >= 1
    &&& parts[p_ng()] is U64 && u64s(parts[p_ng()]).len() >= 1
    &&& parts[p_nkc()] is U8 && u8s(parts[p_nkc()]).len() == u64s(parts[p_nl()])[0]
    &&& parts[p_nkb()] is I64 && i64s(parts[p_nkb()]).len() == ng_n(parts)
    &&& parts[p_nmo()] is U64
    &&& parts[p_nmy()] is U8
}

/// The supplier-side slices are whole parts of storage `suppliers`.
pub open spec fn scols_from_parts(c: SCols, parts: Seq<PartView>) -> bool {
    &&& sparts_shape(parts)
    &&& c.n_s as int == u64s(parts[p_sl()])[0]
    &&& bs_ok(c.bs_s as int, u64s(parts[p_sl()])[1] as int, c.n_s as int)
    &&& parts[p_skc()] == PartView::U32(c.sk_codes@)
    &&& parts[p_skb()] == PartView::I64(c.sk_bases@)
    &&& parts[p_snc()] == PartView::U8(c.sn_codes@)
    &&& parts[p_snb()] == PartView::I64(c.sn_bases@)
    &&& parts[p_smo()] == PartView::U64(c.sm_offs@)
    &&& parts[p_smy()] == PartView::U8(c.sm_bytes@)
    &&& c.n_n as int == u64s(parts[p_nl()])[0]
    &&& bs_ok(c.bs_n as int, u64s(parts[p_nl()])[1] as int, c.n_n as int)
    &&& parts[p_nkc()] == PartView::U8(c.nk_codes@)
    &&& parts[p_nkb()] == PartView::I64(c.nk_bases@)
    &&& parts[p_nmo()] == PartView::U64(c.nm_offs@)
    &&& parts[p_nmy()] == PartView::U8(c.nm_bytes@)
}

/// A database bound to the parts of storage `suppliers`.
pub open spec fn sbound(db: Database, parts: Seq<PartView>) -> bool {
    &&& db_ok(db)
    &&& constraints_hold(declared_db(db))
    &&& si::represents(parts, crate::stores::suppliers::declaration::stored_relations(db))
}

/// The parts the query reads have the kinds and lengths `sparts_shape` lists.
pub proof fn lemma_sparts_shape(db: Database, parts: Seq<PartView>)
    requires sbound(db, parts),
    ensures
        sparts_shape(parts),
        u64s(parts[p_sl()])[0] == srel_of(db).len(),
        u64s(parts[p_nl()])[0] == nrel_of(db).len(),
{
    let s = stp(parts);
    let n = ntp(parts);
    let srel = srel_of(db);
    let nrel = nrel_of(db);
    assert(si::supplier_ok(s, srel));
    assert(si::nation_ok(n, nrel));
    let (ns, nn) = (srel.len() as int, nrel.len() as int);
    assert(s[si::SU_LAYOUT as int] == parts[p_sl()]);
    assert(s[si::SU_GROUPS as int] == parts[p_sg()]);
    assert(s[si::SU_SUPPKEY_CODES as int] == parts[p_skc()]);
    assert(s[si::SU_SUPPKEY_BASE as int] == parts[p_skb()]);
    assert(s[si::SU_NATIONKEY_CODES as int] == parts[p_snc()]);
    assert(s[si::SU_NATIONKEY_BASE as int] == parts[p_snb()]);
    assert(s[si::SU_NAME_OFFS as int] == parts[p_smo()]);
    assert(s[si::SU_NAME_BYTES as int] == parts[p_smy()]);
    assert(n[si::NA_LAYOUT as int] == parts[p_nl()]);
    assert(n[si::NA_GROUPS as int] == parts[p_ng()]);
    assert(n[si::NA_NATIONKEY_CODES as int] == parts[p_nkc()]);
    assert(n[si::NA_NATIONKEY_BASE as int] == parts[p_nkb()]);
    assert(n[si::NA_NAME_OFFS as int] == parts[p_nmo()]);
    assert(n[si::NA_NAME_BYTES as int] == parts[p_nmy()]);
    crate::stores::suppliers::interface::common::colfmt::lemma_uniform_groups(parts[p_sg()], ns, u64s(parts[p_sl()])[1] as int);
    crate::stores::suppliers::interface::common::colfmt::lemma_uniform_groups(parts[p_ng()], nn, u64s(parts[p_nl()])[1] as int);
}

} // verus!
