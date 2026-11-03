//! Binding of the scan model (`super::model::Cols`) to storage `facts`: when the model's slices are whole parts of
//! the storage (`cols_from_parts`) and the parts represent a database's stored relations, the model's decoded
//! columns are the stored rows' values (orders rows `orows`, lineitem rows `lrows`, each a permutation of its stored
//! relation), the model's facts hold (`cols_ok`, `keys_distinct` from the orders primary key, `lines_clustered`
//! from the storage's checked co-clustering flag), and the model's counts are the normal form's group counts
//! (`lemma_count_gcount`, `lemma_keys_complete`).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::gendb_entry::stored::part_len;
use crate::spec::value::*;
use crate::spec::typing::*;
use crate::spec::types::*;
use crate::spec::constraints::*;
use crate::spec::equality::*;
use crate::link::query::*;
use crate::link::join::{lemma_acc_sum_of, lemma_sum_of_perm, count_term};
use crate::link::source::rows_in_columns;
use crate::gendb_constraints::{declared_db, declared_schema};
use crate::stores::facts::declaration::*;
use crate::stores::facts::interface::*;
use crate::stores::facts::interface::common::colfmt::*;
use crate::stores::facts::interface::common::read::lemma_for_row;
use crate::stores::facts::interface::cluster::*;
use crate::stores::li_ordruns::interface as LO;
use crate::stores::li_ordruns::declaration as LD;
use super::model::*;
use super::sql::*;

verus! {

// ------------------------------------------------------------------------------------------------ part positions

pub open spec fn u16s(p: PartView) -> Seq<u16> {
    match p {
        PartView::U16(s) => s,
        _ => Seq::empty(),
    }
}

/// Absolute part positions of storage `facts` the query reads.
pub open spec fn p_ol() -> int { (ORDERS_FIRST + OR_LAYOUT) as int }
pub open spec fn p_og() -> int { (ORDERS_FIRST + OR_GROUPS) as int }
pub open spec fn p_okc() -> int { (ORDERS_FIRST + OR_ORDERKEY_CODES) as int }
pub open spec fn p_okb() -> int { (ORDERS_FIRST + OR_ORDERKEY_BASE) as int }
pub open spec fn p_odc() -> int { (ORDERS_FIRST + OR_ORDERDATE_CODES) as int }
pub open spec fn p_odb() -> int { (ORDERS_FIRST + OR_ORDERDATE_BASE) as int }
pub open spec fn p_odz() -> int { (ORDERS_FIRST + OR_ORDERDATE_ZMAX) as int }
pub open spec fn p_opc() -> int { (ORDERS_FIRST + OR_ORDERPRIORITY_CODES) as int }
pub open spec fn p_opb() -> int { (ORDERS_FIRST + OR_ORDERPRIORITY_BASE) as int }
pub open spec fn p_odo() -> int { (ORDERS_FIRST + OR_ORDERPRIORITY_DICT_OFFS) as int }
pub open spec fn p_ody() -> int { (ORDERS_FIRST + OR_ORDERPRIORITY_DICT_BYTES) as int }
pub open spec fn p_oic() -> int { (ORDERS_FIRST + OR_KEYIDX_CODES) as int }
pub open spec fn p_oib() -> int { (ORDERS_FIRST + OR_KEYIDX_BASE) as int }
pub open spec fn p_oik() -> int { (ORDERS_FIRST + OR_KEYIDX_KIND) as int }
pub open spec fn p_ll() -> int { (LINEITEM_FIRST + LI_LAYOUT) as int }
pub open spec fn p_lg() -> int { (LINEITEM_FIRST + LI_GROUPS) as int }
pub open spec fn p_lkc() -> int { (LINEITEM_FIRST + LI_ORDERKEY_CODES) as int }
pub open spec fn p_lkb() -> int { (LINEITEM_FIRST + LI_ORDERKEY_BASE) as int }
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

/// Kinds and lengths of every part the query reads (what the extent requests need).
pub open spec fn parts_shape(parts: Seq<PartView>) -> bool {
    &&& parts.len() == FACTS_PARTS
    &&& parts[p_ol()] is U64 && u64s(parts[p_ol()]).len() == 2 && u64s(parts[p_ol()])[1] >= 1
    &&& parts[p_og()] is U64 && u64s(parts[p_og()]).len() >= 1
    &&& parts[p_okc()] is U32 && u32s(parts[p_okc()]).len() == u64s(parts[p_ol()])[0]
    &&& parts[p_okb()] is I64 && i64s(parts[p_okb()]).len() == ng_o(parts)
    &&& parts[p_odc()] is U16 && u16s(parts[p_odc()]).len() == u64s(parts[p_ol()])[0]
    &&& parts[p_odb()] is I64 && i64s(parts[p_odb()]).len() == ng_o(parts)
    &&& parts[p_odz()] is I64 && i64s(parts[p_odz()]).len() == ng_o(parts)
    &&& parts[p_opc()] is U8 && u8s(parts[p_opc()]).len() == u64s(parts[p_ol()])[0]
    &&& parts[p_opb()] is U64 && u64s(parts[p_opb()]).len() == ng_o(parts)
    &&& parts[p_odo()] is U64 && u64s(parts[p_odo()]).len() >= 1
    &&& parts[p_ody()] is U8
    &&& parts[p_oic()] is U32
    &&& parts[p_oib()] is U64
    &&& parts[p_oik()] is U64 && u64s(parts[p_oik()]).len() == 1
    &&& parts[p_ll()] is U64 && u64s(parts[p_ll()]).len() == 2 && u64s(parts[p_ll()])[1] >= 1
    &&& parts[p_lg()] is U64 && u64s(parts[p_lg()]).len() >= 1
    &&& parts[p_lkc()] is U32 && u32s(parts[p_lkc()]).len() == u64s(parts[p_ll()])[0]
    &&& parts[p_lkb()] is I64 && i64s(parts[p_lkb()]).len() == ng_l(parts)
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
    &&& parts[p_odc()] == PartView::U16(c.od_codes@)
    &&& parts[p_odb()] == PartView::I64(c.od_bases@)
    &&& parts[p_opc()] == PartView::U8(c.op_codes@)
    &&& parts[p_opb()] == PartView::U64(c.op_bases@)
    &&& parts[p_oic()] == PartView::U32(c.oi_codes@)
    &&& parts[p_oib()] == PartView::U64(c.oi_bases@)
    &&& u64s(parts[p_oik()])[0] == c.oi_kind
    &&& c.n_l as int == u64s(parts[p_ll()])[0]
    &&& bs_ok(c.bs_l as int, u64s(parts[p_ll()])[1] as int, c.n_l as int)
    &&& parts[p_lkc()] == PartView::U32(c.lk_codes@)
    &&& parts[p_lkb()] == PartView::I64(c.lk_bases@)
    &&& parts[p_lcc()] == PartView::U16(c.lc_codes@)
    &&& parts[p_lcb()] == PartView::I64(c.lc_bases@)
    &&& parts[p_lrc()] == PartView::U16(c.lr_codes@)
    &&& parts[p_lrb()] == PartView::I64(c.lr_bases@)
}

/// A database bound to the parts (the query entry's `bound_db` for storage `facts`).
pub open spec fn bound(db: Database, parts: Seq<PartView>) -> bool {
    &&& db_ok(db)
    &&& constraints_hold(declared_db(db))
    &&& represents(parts, stored_relations(db))
}

/// A database bound to the parts `lp` of storage `li_ordruns` (facts' parts first, then the run lengths).
pub open spec fn bound2(db: Database, lp: Seq<PartView>) -> bool {
    &&& db_ok(db)
    &&& constraints_hold(declared_db(db))
    &&& LO::represents(lp, LD::stored_relations(db))
}

/// li_ordruns represents facts' relations in its inherited parts, and the run lengths of the stored lineitem rows.
pub proof fn lemma_bound2(db: Database, lp: Seq<PartView>)
    requires bound2(db, lp),
    ensures
        bound(db, LO::facts_parts(lp)),
        lp.len() == LO::LI_ORDRUNS_PARTS,
        lp[LO::RUN_LENS as int] is U8,
        LO::runs_ok(lrows(LO::facts_parts(lp), db), LO::run_lens(lp)),
{
    assert(LD::stored_relations(db) =~= stored_relations(db));
    assert(LO::stored_lines(lp, LD::stored_relations(db)) == lrows(LO::facts_parts(lp), db));
}

/// The model's run lengths are the maximal runs of l_orderkey (one per stored orders row).
pub proof fn lemma_runs_model(db: Database, lp: Seq<PartView>, c: Cols)
    requires
        bound2(db, lp),
        cols_from_parts(c, LO::facts_parts(lp)),
        c.rl@ == LO::run_lens(lp),
        c.rl@.len() == c.n_o,
        c.n_o > 0,
    ensures
        runs_model(c),
{
    let fp = LO::facts_parts(lp);
    lemma_bound2(db, lp);
    lemma_lineitem_cols(db, fp, c);
    let l = lrows(fp, db);
    let rl = c.rl@;
    assert(LO::runs_ok(l, rl));
    assert(l.len() == c.n_l);
    assert forall|r: int, i: int| 0 <= r < c.n_o && 0 <= i < c.rl@[r] implies #[trigger] lsame(c, r, i) by {
        assert(LO::run_same(l, rl, r, i));
        LO::lemma_run_start_mono(rl, r + 1, rl.len() as int);
        LO::lemma_run_start_next(rl, r);
        LO::lemma_run_start_mono(rl, 0, r);
        let j = rstart(c, r);
        assert(0 <= j + i < c.n_l);
        assert(l[j + i][0] == Val::Int(lkey(c, j + i)));
        assert(l[j][0] == Val::Int(lkey(c, j)));
    }
    assert forall|r: int| 0 < r < c.n_o implies #[trigger] lsplit(c, r) by {
        assert(LO::run_split(l, rl, r));
        LO::lemma_run_start_mono(rl, r, rl.len() as int);
        LO::lemma_run_start_mono(rl, 0, r);
        let j = rstart(c, r);
        assert(1 <= j < c.n_l);
        assert(l[j][0] == Val::Int(lkey(c, j)));
        assert(l[j - 1][0] == Val::Int(lkey(c, j - 1)));
    }
}

/// Dictionary entry `d` of o_orderpriority as a group key.
pub open spec fn key_d(doffs: Seq<u64>, dbytes: Seq<u8>, d: int) -> Row {
    seq![Val::Text(text_of(doffs, dbytes, d))]
}

// ------------------------------------------------------------------------------------------------ shapes

/// The parts the query reads have the kinds and lengths `parts_shape` lists.
pub proof fn lemma_parts_shape(db: Database, parts: Seq<PartView>)
    requires bound(db, parts),
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
    assert(o[OR_ORDERDATE_CODES as int] == parts[p_odc()]);
    assert(o[OR_ORDERDATE_BASE as int] == parts[p_odb()]);
    assert(o[OR_ORDERDATE_ZMAX as int] == parts[p_odz()]);
    assert(o[OR_ORDERPRIORITY_CODES as int] == parts[p_opc()]);
    assert(o[OR_ORDERPRIORITY_BASE as int] == parts[p_opb()]);
    assert(o[OR_ORDERPRIORITY_DICT_OFFS as int] == parts[p_odo()]);
    assert(o[OR_ORDERPRIORITY_DICT_BYTES as int] == parts[p_ody()]);
    assert(o[OR_KEYIDX_CODES as int] == parts[p_oic()]);
    assert(o[OR_KEYIDX_BASE as int] == parts[p_oib()]);
    assert(o[OR_KEYIDX_KIND as int] == parts[p_oik()]);
    assert(l[LI_LAYOUT as int] == parts[p_ll()]);
    assert(l[LI_GROUPS as int] == parts[p_lg()]);
    assert(l[LI_ORDERKEY_CODES as int] == parts[p_lkc()]);
    assert(l[LI_ORDERKEY_BASE as int] == parts[p_lkb()]);
    assert(l[LI_COMMITDATE_CODES as int] == parts[p_lcc()]);
    assert(l[LI_COMMITDATE_BASE as int] == parts[p_lcb()]);
    assert(l[LI_RECEIPTDATE_CODES as int] == parts[p_lrc()]);
    assert(l[LI_RECEIPTDATE_BASE as int] == parts[p_lrb()]);
    lemma_uniform_groups(parts[p_og()], no, u64s(parts[p_ol()])[1] as int);
    lemma_uniform_groups(parts[p_lg()], nl, u64s(parts[p_ll()])[1] as int);
}

// ------------------------------------------------------------------------------------------------ decoding

/// Within uniform groups, a model group size `b` (`bs_ok`) finds the same group as the stored one.
pub proof fn lemma_bs_group(b: int, stored_bs: int, n: int, j: int)
    requires bs_ok(b, stored_bs, n), stored_bs >= 1, 0 <= j < n,
    ensures j / b == j / stored_bs,
{
    if b != stored_bs {
        vstd::arithmetic::div_mod::lemma_basic_div(j, b);
        vstd::arithmetic::div_mod::lemma_basic_div(j, stored_bs);
    }
}

/// The model's orders columns are the stored orders rows' values.
pub proof fn lemma_orders_cols(db: Database, parts: Seq<PartView>, c: Cols, doffs: Seq<u64>, dbytes: Seq<u8>)
    requires
        bound(db, parts),
        cols_from_parts(c, parts),
        parts[p_odo()] == PartView::U64(doffs),
        parts[p_ody()] == PartView::U8(dbytes),
    ensures ({
        let o = orows(parts, db);
        let k = doffs.len() - 1;
        let zmax = i64s(parts[p_odz()]);
        &&& o.len() == c.n_o
        &&& doffs.len() >= 1
        &&& text_parts_wf(doffs, dbytes, k)
        &&& dict_sorted(doffs, dbytes, k)
        &&& forall|p: int| 0 <= p < c.n_o ==> {
            &&& (#[trigger] o[p])[0] == Val::Int(okey(c, p))
            &&& o[p][4] == Val::Date(odate(c, p))
            &&& 0 <= oprio(c, p) < k
            &&& o[p][5] == Val::Text(text_of(doffs, dbytes, oprio(c, p)))
            &&& odate(c, p) <= zmax[p / c.bs_o as int]
        }
    }),
{
    let tp = otp(parts);
    let orel = orel_of(db);
    let o = orows(parts, db);
    let n = orel.len() as int;
    let stored_bs = u64s(tp[OR_LAYOUT as int])[1] as int;
    let gp = tp[OR_GROUPS as int];
    let gs = u64s(gp);
    lemma_parts_shape(db, parts);
    assert(orders_ok(tp, orel));
    assert(orders_cols_ok(tp, o));
    assert(tp[OR_LAYOUT as int] == parts[p_ol()]);
    assert(tp[OR_ORDERKEY_CODES as int] == parts[p_okc()]);
    assert(tp[OR_ORDERKEY_BASE as int] == parts[p_okb()]);
    assert(tp[OR_ORDERDATE_CODES as int] == parts[p_odc()]);
    assert(tp[OR_ORDERDATE_BASE as int] == parts[p_odb()]);
    assert(tp[OR_ORDERDATE_ZMAX as int] == parts[p_odz()]);
    assert(tp[OR_ORDERPRIORITY_CODES as int] == parts[p_opc()]);
    assert(tp[OR_ORDERPRIORITY_BASE as int] == parts[p_opb()]);
    assert(tp[OR_ORDERPRIORITY_DICT_OFFS as int] == parts[p_odo()]);
    assert(tp[OR_ORDERPRIORITY_DICT_BYTES as int] == parts[p_ody()]);
    assert(o.len() == n);
    assert forall|p: int| 0 <= p < c.n_o implies {
        &&& (#[trigger] o[p])[0] == Val::Int(okey(c, p))
        &&& o[p][4] == Val::Date(odate(c, p))
        &&& 0 <= oprio(c, p) < doffs.len() - 1
        &&& o[p][5] == Val::Text(text_of(doffs, dbytes, oprio(c, p)))
        &&& odate(c, p) <= i64s(parts[p_odz()])[p / c.bs_o as int]
    } by {
        lemma_bs_group(c.bs_o as int, stored_bs, n, p);
        lemma_for_row(gp, n, stored_bs, tp[OR_ORDERKEY_BASE as int], tp[OR_ORDERKEY_CODES as int], p);
        lemma_for_row(gp, n, stored_bs, tp[OR_ORDERDATE_BASE as int], tp[OR_ORDERDATE_CODES as int], p);
        lemma_for_row(gp, n, stored_bs, tp[OR_ORDERPRIORITY_BASE as int], tp[OR_ORDERPRIORITY_CODES as int], p);
        assert(int_col(o, 0, gs, tp[OR_ORDERKEY_BASE as int], tp[OR_ORDERKEY_CODES as int]));
        assert(date_col(o, 4, gs, tp[OR_ORDERDATE_BASE as int], tp[OR_ORDERDATE_CODES as int]));
        assert(dict_col(o, 5, gs, tp[OR_ORDERPRIORITY_BASE as int], tp[OR_ORDERPRIORITY_CODES as int], doffs, dbytes));
        assert(zone_max_ok(gs, tp[OR_ORDERDATE_BASE as int], tp[OR_ORDERDATE_CODES as int], i64s(tp[OR_ORDERDATE_ZMAX as int])));
        assert(in_group(gs, p / stored_bs, p));
    }
}

/// The model's lineitem columns are the stored lineitem rows' values.
pub proof fn lemma_lineitem_cols(db: Database, parts: Seq<PartView>, c: Cols)
    requires
        bound(db, parts),
        cols_from_parts(c, parts),
    ensures ({
        let l = lrows(parts, db);
        &&& l.len() == c.n_l
        &&& forall|j: int| 0 <= j < c.n_l ==> {
            &&& (#[trigger] l[j])[0] == Val::Int(lkey(c, j))
            &&& l[j][11] == Val::Date(lcmt(c, j))
            &&& l[j][12] == Val::Date(lrcp(c, j))
        }
    }),
{
    let tp = ltp(parts);
    let lrel = lrel_of(db);
    let l = lrows(parts, db);
    let n = lrel.len() as int;
    let stored_bs = u64s(tp[LI_LAYOUT as int])[1] as int;
    let gp = tp[LI_GROUPS as int];
    let gs = u64s(gp);
    lemma_parts_shape(db, parts);
    assert(lineitem_ok(tp, lrel));
    assert(lineitem_cols_ok(tp, l));
    assert(tp[LI_LAYOUT as int] == parts[p_ll()]);
    assert(tp[LI_ORDERKEY_CODES as int] == parts[p_lkc()]);
    assert(tp[LI_ORDERKEY_BASE as int] == parts[p_lkb()]);
    assert(tp[LI_COMMITDATE_CODES as int] == parts[p_lcc()]);
    assert(tp[LI_COMMITDATE_BASE as int] == parts[p_lcb()]);
    assert(tp[LI_RECEIPTDATE_CODES as int] == parts[p_lrc()]);
    assert(tp[LI_RECEIPTDATE_BASE as int] == parts[p_lrb()]);
    assert(l.len() == n);
    assert forall|j: int| 0 <= j < c.n_l implies {
        &&& (#[trigger] l[j])[0] == Val::Int(lkey(c, j))
        &&& l[j][11] == Val::Date(lcmt(c, j))
        &&& l[j][12] == Val::Date(lrcp(c, j))
    } by {
        lemma_bs_group(c.bs_l as int, stored_bs, n, j);
        lemma_for_row(gp, n, stored_bs, tp[LI_ORDERKEY_BASE as int], tp[LI_ORDERKEY_CODES as int], j);
        lemma_for_row(gp, n, stored_bs, tp[LI_COMMITDATE_BASE as int], tp[LI_COMMITDATE_CODES as int], j);
        lemma_for_row(gp, n, stored_bs, tp[LI_RECEIPTDATE_BASE as int], tp[LI_RECEIPTDATE_CODES as int], j);
        assert(int_col(l, 0, gs, tp[LI_ORDERKEY_BASE as int], tp[LI_ORDERKEY_CODES as int]));
        assert(date_col(l, 11, gs, tp[LI_COMMITDATE_BASE as int], tp[LI_COMMITDATE_CODES as int]));
        assert(date_col(l, 12, gs, tp[LI_RECEIPTDATE_BASE as int], tp[LI_RECEIPTDATE_CODES as int]));
    }
}

/// The stored rows are the stored relation's rows under a bijection.
pub proof fn lemma_row_maps(db: Database, parts: Seq<PartView>)
    requires bound(db, parts),
    ensures
        is_perm(orders_map(otp(parts), orel_of(db).len() as int), orel_of(db).len() as int),
        orows(parts, db) == stored_rows(orel_of(db), orders_map(otp(parts), orel_of(db).len() as int)),
        is_perm(lineitem_map(ltp(parts), lrel_of(db).len() as int), lrel_of(db).len() as int),
        lrows(parts, db) == stored_rows(lrel_of(db), lineitem_map(ltp(parts), lrel_of(db).len() as int)),
{
    assert(orders_ok(otp(parts), orel_of(db)));
    assert(lineitem_ok(ltp(parts), lrel_of(db)));
}

/// Values of the stored relations lie in their declared columns.
pub proof fn lemma_rel_values(db: Database)
    requires db_ok(db),
    ensures
        forall|i: int| 0 <= i < orel_of(db).len() ==> {
            &&& (#[trigger] orel_of(db)[i])[0] is Int
            &&& in_i64(orel_of(db)[i][0]->Int_0)
            &&& orel_of(db)[i][4] is Date
            &&& in_i64(orel_of(db)[i][4]->Date_0)
        },
        forall|j: int| 0 <= j < lrel_of(db).len() ==> {
            &&& (#[trigger] lrel_of(db)[j])[0] is Int
            &&& in_i64(lrel_of(db)[j][0]->Int_0)
            &&& lrel_of(db)[j][11] is Date
            &&& in_i64(lrel_of(db)[j][11]->Date_0)
            &&& lrel_of(db)[j][12] is Date
            &&& in_i64(lrel_of(db)[j][12]->Date_0)
        },
{
    lemma_stored_relations(db);
    let (oc, lc) = (stored_columns_t1(), stored_columns_t0());
    assert(oc[0] == Column { ty: SqlType::Int8, nullable: false });
    assert(oc[4] == Column { ty: SqlType::Date, nullable: false });
    assert(lc[0] == Column { ty: SqlType::Int8, nullable: false });
    assert(lc[11] == Column { ty: SqlType::Date, nullable: false });
    assert(lc[12] == Column { ty: SqlType::Date, nullable: false });
    assert(oc.len() == 7 && lc.len() == 15);
    assert forall|i: int| 0 <= i < orel_of(db).len() implies {
        &&& (#[trigger] orel_of(db)[i])[0] is Int
        &&& in_i64(orel_of(db)[i][0]->Int_0)
        &&& orel_of(db)[i][4] is Date
        &&& in_i64(orel_of(db)[i][4]->Date_0)
    } by {
        assert(value_in_column(orel_of(db)[i][0], oc[0]));
        assert(value_in_column(orel_of(db)[i][4], oc[4]));
    }
    assert forall|j: int| 0 <= j < lrel_of(db).len() implies {
        &&& (#[trigger] lrel_of(db)[j])[0] is Int
        &&& in_i64(lrel_of(db)[j][0]->Int_0)
        &&& lrel_of(db)[j][11] is Date
        &&& in_i64(lrel_of(db)[j][11]->Date_0)
        &&& lrel_of(db)[j][12] is Date
        &&& in_i64(lrel_of(db)[j][12]->Date_0)
    } by {
        assert(value_in_column(lrel_of(db)[j][0], lc[0]));
        assert(value_in_column(lrel_of(db)[j][11], lc[11]));
        assert(value_in_column(lrel_of(db)[j][12], lc[12]));
    }
}

/// The model's facts: shapes, value ranges and dictionary indices.
pub proof fn lemma_cols_ok(db: Database, parts: Seq<PartView>, c: Cols, doffs: Seq<u64>, dbytes: Seq<u8>)
    requires
        bound(db, parts),
        cols_from_parts(c, parts),
        parts[p_odo()] == PartView::U64(doffs),
        parts[p_ody()] == PartView::U8(dbytes),
    ensures
        cols_ok(c, doffs.len() - 1),
{
    let k = doffs.len() - 1;
    let tp = otp(parts);
    let n_o = c.n_o as int;
    let n_l = c.n_l as int;
    lemma_parts_shape(db, parts);
    lemma_orders_cols(db, parts, c, doffs, dbytes);
    lemma_lineitem_cols(db, parts, c);
    lemma_row_maps(db, parts);
    lemma_rel_values(db);
    let (o, l) = (orows(parts, db), lrows(parts, db));
    let omap = orders_map(tp, n_o);
    let lmap = lineitem_map(ltp(parts), n_l);
    // Group-base lengths cover the rows.
    let sbs_o = u64s(parts[p_ol()])[1] as int;
    let sbs_l = u64s(parts[p_ll()])[1] as int;
    assert(orders_ok(tp, orel_of(db)));
    assert(lineitem_ok(ltp(parts), lrel_of(db)));
    assert(tp[OR_GROUPS as int] == parts[p_og()]);
    assert(ltp(parts)[LI_GROUPS as int] == parts[p_lg()]);
    lemma_uniform_groups(parts[p_og()], n_o, sbs_o);
    lemma_uniform_groups(parts[p_lg()], n_l, sbs_l);
    lemma_nblocks(n_o, sbs_o);
    lemma_nblocks(n_l, sbs_l);
    assert(c.ok_bases@.len() * c.bs_o >= c.n_o) by {
        if c.bs_o as int != sbs_o && n_o > 0 {
            assert(nblocks_of(n_o, sbs_o) >= 1);
            assert(c.ok_bases@.len() * c.bs_o >= c.bs_o) by (nonlinear_arith)
                requires c.ok_bases@.len() >= 1, c.bs_o >= 1;
        }
    }
    assert(c.lk_bases@.len() * c.bs_l >= c.n_l) by {
        if c.bs_l as int != sbs_l && n_l > 0 {
            assert(nblocks_of(n_l, sbs_l) >= 1);
            assert(c.lk_bases@.len() * c.bs_l >= c.bs_l) by (nonlinear_arith)
                requires c.lk_bases@.len() >= 1, c.bs_l >= 1;
        }
    }
    // Key index.
    assert(tp[OR_ORDERKEY_CODES as int] == parts[p_okc()]);
    assert(tp[OR_ORDERKEY_BASE as int] == parts[p_okb()]);
    assert(tp[OR_KEYIDX_CODES as int] == parts[p_oic()]);
    assert(tp[OR_KEYIDX_BASE as int] == parts[p_oib()]);
    assert(tp[OR_KEYIDX_KIND as int] == parts[p_oik()]);
    assert(tp[OR_LAYOUT as int] == parts[p_ol()]);
    assert(orders_cols_ok(tp, o));
    assert(crate::stores::facts::interface::common::keyidx::keyidx_ok(c.ok_codes@, c.ok_bases@, c.oi_codes@, c.oi_bases@,
        sbs_o, c.oi_kind, n_o));
    assert(crate::stores::facts::interface::common::keyidx::keyidx_ok(c.ok_codes@, c.ok_bases@, c.oi_codes@, c.oi_bases@,
        c.bs_o as int, c.oi_kind, n_o)) by {
        if c.bs_o as int != sbs_o {
            lemma_keyidx_bs(c, sbs_o, n_o);
        }
    }
    // Value ranges through the row maps.
    assert forall|p: int| 0 <= p < c.n_o implies in_i64(#[trigger] okey(c, p)) && in_i64(odate(c, p)) by {
        assert(0 <= omap[p] < n_o);
        assert(o[p] == orel_of(db)[omap[p]]);
    }
    assert forall|p: int| 0 <= p < c.n_o implies in_i64(#[trigger] odate(c, p)) by {
        assert(0 <= omap[p] < n_o);
        assert(o[p] == orel_of(db)[omap[p]]);
    }
    assert forall|p: int| 0 <= p < c.n_o implies 0 <= #[trigger] oprio(c, p) < k by {
        assert(o[p][0] == Val::Int(okey(c, p)));
    }
    assert forall|j: int| 0 <= j < c.n_l implies in_i64(#[trigger] lkey(c, j)) && in_i64(lcmt(c, j)) && in_i64(lrcp(c, j)) by {
        assert(0 <= lmap[j] < n_l);
        assert(l[j] == lrel_of(db)[lmap[j]]);
    }
    assert forall|j: int| 0 <= j < c.n_l implies in_i64(#[trigger] lcmt(c, j)) by {
        assert(0 <= lmap[j] < n_l);
        assert(l[j] == lrel_of(db)[lmap[j]]);
    }
    assert forall|j: int| 0 <= j < c.n_l implies in_i64(#[trigger] lrcp(c, j)) by {
        assert(0 <= lmap[j] < n_l);
        assert(l[j] == lrel_of(db)[lmap[j]]);
    }
}

/// The key index stays valid under a model group size that finds the same groups (`bs_ok` with sizes >= `n`).
pub proof fn lemma_keyidx_bs(c: Cols, stored_bs: int, n: int)
    requires
        crate::stores::facts::interface::common::keyidx::keyidx_ok(c.ok_codes@, c.ok_bases@, c.oi_codes@, c.oi_bases@,
            stored_bs, c.oi_kind, n),
        c.bs_o >= n, stored_bs >= n, c.bs_o >= 1, stored_bs >= 1,
        c.ok_bases@.len() * c.bs_o >= n,
    ensures
        crate::stores::facts::interface::common::keyidx::keyidx_ok(c.ok_codes@, c.ok_bases@, c.oi_codes@, c.oi_bases@,
            c.bs_o as int, c.oi_kind, n),
{
    use crate::stores::facts::interface::common::keyidx::*;
    let b = c.bs_o as int;
    assert forall|r: int| 0 <= r < n implies #[trigger] fidx(c.oi_codes@, c.oi_bases@, b, r) == fidx(c.oi_codes@, c.oi_bases@, stored_bs, r) by {
        vstd::arithmetic::div_mod::lemma_basic_div(r, b);
        vstd::arithmetic::div_mod::lemma_basic_div(r, stored_bs);
    }
    assert forall|r: int| 0 <= r < n implies #[trigger] fkey(c.ok_codes@, c.ok_bases@, b, r) == fkey(c.ok_codes@, c.ok_bases@, stored_bs, r) by {
        vstd::arithmetic::div_mod::lemma_basic_div(r, b);
        vstd::arithmetic::div_mod::lemma_basic_div(r, stored_bs);
    }
    if c.oi_kind == 2 {
        assert(idx_map(c.oi_codes@, c.oi_bases@, b, n) =~= idx_map(c.oi_codes@, c.oi_bases@, stored_bs, n));
        assert(c.oi_bases@.len() * stored_bs >= n);
        if n > 0 {
            assert(c.oi_bases@.len() >= 1) by (nonlinear_arith) requires c.oi_bases@.len() * stored_bs >= n, n > 0, stored_bs >= 1;
            assert(c.oi_bases@.len() * b >= b) by (nonlinear_arith) requires c.oi_bases@.len() >= 1, b >= 1;
        }
    }
    if c.oi_kind >= 1 {
        assert forall|r: int| 0 <= r < n - 1 implies #[trigger] sorted_at(c.ok_codes@, c.ok_bases@, c.oi_codes@, c.oi_bases@, b, c.oi_kind, r) by {
            assert(sorted_at(c.ok_codes@, c.ok_bases@, c.oi_codes@, c.oi_bases@, stored_bs, c.oi_kind, r));
            lemma_irow_bound(c.ok_codes@, c.ok_bases@, c.oi_codes@, c.oi_bases@, stored_bs, c.oi_kind, n, r);
            lemma_irow_bound(c.ok_codes@, c.ok_bases@, c.oi_codes@, c.oi_bases@, stored_bs, c.oi_kind, n, r + 1);
        }
    }
}

// ------------------------------------------------------------------------------------------------ keys and clustering

/// Under the orders primary key, o_orderkey is distinct over the stored orders rows.
pub proof fn lemma_keys_distinct(db: Database, parts: Seq<PartView>, c: Cols, doffs: Seq<u64>, dbytes: Seq<u8>)
    requires
        bound(db, parts),
        cols_from_parts(c, parts),
        parts[p_odo()] == PartView::U64(doffs),
        parts[p_ody()] == PartView::U8(dbytes),
    ensures keys_distinct(c),
{
    let n = c.n_o as int;
    lemma_orders_cols(db, parts, c, doffs, dbytes);
    lemma_row_maps(db, parts);
    lemma_stored_positions(db);
    lemma_rows_typed(db);
    let o = orows(parts, db);
    let omap = orders_map(otp(parts), n);
    let ddb = declared_db(db);
    crate::gendb_constraints::lemma_declared_schema();
    assert(ddb.schema[1].constraints[0] == Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true });
    assert forall|a: int, b: int| 0 <= a < c.n_o && 0 <= b < c.n_o && a != b implies #[trigger] okey(c, a) != #[trigger] okey(c, b) by {
        if okey(c, a) == okey(c, b) {
            let (ma, mb) = (omap[a], omap[b]);
            assert(o[a] == orel_of(db)[ma] && o[b] == orel_of(db)[mb]);
            assert(ma != mb);
            let (ra, rb) = (db.tables[1][ma], db.tables[1][mb]);
            assert(ra[0] == rb[0]);
            let ka = key_of(ra, seq![0nat]);
            let kb = key_of(rb, seq![0nat]);
            assert(ka =~= kb);
            crate::bridge::equality::lemma_row_not_distinct_refl(ka);
            crate::bridge::constraints::lemma_primary_key_identifies(ddb, 1, 0, seq![0nat], true, ma, mb);
        }
    }
}

proof fn lemma_first_key_rpos(o: Seq<Row>, c: Cols, k: int, i: int)
    requires
        o.len() == c.n_o,
        forall|p: int| 0 <= p < c.n_o ==> (#[trigger] o[p])[0] == Val::Int(okey(c, p)),
        0 <= i,
    ensures first_key_from(o, Val::Int(k), i) == rpos_from(c, k, i),
    decreases c.n_o - i,
{
    if i < c.n_o {
        assert(o[i][0] == Val::Int(okey(c, i)));
        if okey(c, i) != k {
            lemma_first_key_rpos(o, c, k, i + 1);
        }
    }
}

/// With the storage's co-clustering flag set, the model's lineitem rows follow the orders order.
pub proof fn lemma_clustered(db: Database, parts: Seq<PartView>, c: Cols, doffs: Seq<u64>, dbytes: Seq<u8>)
    requires
        bound(db, parts),
        cols_from_parts(c, parts),
        parts[p_odo()] == PartView::U64(doffs),
        parts[p_ody()] == PartView::U8(dbytes),
        u64s(parts[p_flag()])[0] == 1,
    ensures lines_clustered(c),
{
    lemma_orders_cols(db, parts, c, doffs, dbytes);
    lemma_lineitem_cols(db, parts, c);
    let (o, l) = (orows(parts, db), lrows(parts, db));
    assert(clustered(l, o));
    assert forall|j: int| 0 <= j < c.n_l - 1 implies #[trigger] lstep(c, j) by {
        assert(cluster_step(l, o, j));
        lemma_first_key_rpos(o, c, lkey(c, j), 0);
        lemma_first_key_rpos(o, c, lkey(c, j + 1), 0);
        assert(l[j][0] == Val::Int(lkey(c, j)));
        assert(l[j + 1][0] == Val::Int(lkey(c, j + 1)));
    }
}

// ------------------------------------------------------------------------------------------------ counts

/// EXISTS over the stored lineitem relation is the model's scan condition.
pub proof fn lemma_has_line(db: Database, parts: Seq<PartView>, c: Cols, k: int)
    requires
        bound(db, parts),
        cols_from_parts(c, parts),
    ensures has_line(lrel_of(db), Val::Int(k)) == has_line_raw(c, k),
{
    lemma_lineitem_cols(db, parts, c);
    lemma_row_maps(db, parts);
    let lrel = lrel_of(db);
    let l = lrows(parts, db);
    let n = lrel.len() as int;
    let lmap = lineitem_map(ltp(parts), n);
    if has_line(lrel, Val::Int(k)) {
        let i = choose|i: int| 0 <= i < lrel.len() && #[trigger] line_hit(lrel[i], Val::Int(k));
        assert(covered(lmap, i));
        let j = choose|j: int| 0 <= j < lmap.len() && lmap[j] == i;
        assert(l[j] == lrel[i]);
        assert(lmatch(c, j, k));
    }
    if has_line_raw(c, k) {
        let j = choose|j: int| 0 <= j < c.n_l && #[trigger] lmatch(c, j, k);
        let i = lmap[j];
        assert(0 <= i < n);
        assert(l[j] == lrel[i]);
        assert(line_hit(lrel[i], Val::Int(k)));
    }
}

/// Stored orders row `p` is in group `key_d(d)` of the normal form exactly when the model counts it for `d`.
pub proof fn lemma_hit_row(db: Database, parts: Seq<PartView>, c: Cols, doffs: Seq<u64>, dbytes: Seq<u8>,
    lo: int, hi: int, d: int, p: int)
    requires
        bound(db, parts),
        cols_from_parts(c, parts),
        parts[p_odo()] == PartView::U64(doffs),
        parts[p_ody()] == PartView::U8(dbytes),
        0 <= d < doffs.len() - 1,
        0 <= p < c.n_o,
    ensures
        hit(qspec(lrel_of(db), lo, hi), orows(parts, db)[p], key_d(doffs, dbytes, d))
            == (qual_raw(c, lo, hi, p) && oprio(c, p) == d),
{
    lemma_orders_cols(db, parts, c, doffs, dbytes);
    let o = orows(parts, db);
    let x = o[p];
    lemma_has_line(db, parts, c, okey(c, p));
    let k = doffs.len() - 1;
    if oprio(c, p) != d {
        lemma_dict_distinct(doffs, dbytes, k, oprio(c, p), d);
        assert(seq![x[5]][0] != key_d(doffs, dbytes, d)[0]);
    } else {
        assert(seq![x[5]] =~= key_d(doffs, dbytes, d));
    }
}

/// The model's count for dictionary entry `d` over every stored orders row is the normal form's count of group
/// `key_d(d)`.
pub proof fn lemma_count_gcount(db: Database, parts: Seq<PartView>, c: Cols, doffs: Seq<u64>, dbytes: Seq<u8>,
    lo: int, hi: int, d: int)
    requires
        bound(db, parts),
        cols_from_parts(c, parts),
        parts[p_odo()] == PartView::U64(doffs),
        parts[p_ody()] == PartView::U8(dbytes),
        0 <= d < doffs.len() - 1,
    ensures
        count_raw(c, lo, hi, d, 0, c.n_o as int) == gcount(qspec(lrel_of(db), lo, hi), orel_of(db), key_d(doffs, dbytes, d)),
{
    let g = qspec(lrel_of(db), lo, hi);
    let kd = key_d(doffs, dbytes, d);
    let o = orows(parts, db);
    let orel = orel_of(db);
    lemma_orders_cols(db, parts, c, doffs, dbytes);
    lemma_count_prefix(db, parts, c, doffs, dbytes, lo, hi, d, c.n_o as int);
    lemma_full_range(o);
    // The stored rows are a permutation of the relation: the same count.
    lemma_row_maps(db, parts);
    lemma_stored_rows_multiset(orel, orders_map(otp(parts), orel.len() as int));
    lemma_acc_sum_of(g, o, kd, 0);
    lemma_acc_sum_of(g, orel, kd, 0);
    lemma_sum_of_perm(o, orel, count_term(g, kd));
}

proof fn lemma_count_prefix(db: Database, parts: Seq<PartView>, c: Cols, doffs: Seq<u64>, dbytes: Seq<u8>,
    lo: int, hi: int, d: int, p: int)
    requires
        bound(db, parts),
        cols_from_parts(c, parts),
        parts[p_odo()] == PartView::U64(doffs),
        parts[p_ody()] == PartView::U8(dbytes),
        0 <= d < doffs.len() - 1,
        0 <= p <= c.n_o,
        orows(parts, db).len() == c.n_o,
    ensures
        count_raw(c, lo, hi, d, 0, p)
            == gcount(qspec(lrel_of(db), lo, hi), orows(parts, db).subrange(0, p), key_d(doffs, dbytes, d)),
    decreases p,
{
    let g = qspec(lrel_of(db), lo, hi);
    let kd = key_d(doffs, dbytes, d);
    let o = orows(parts, db);
    if p == 0 {
        lemma_empty(g, o, 0, kd, 0);
    } else {
        lemma_count_prefix(db, parts, c, doffs, dbytes, lo, hi, d, p - 1);
        lemma_range_step(g, o, 0, p - 1, kd, 0);
        lemma_hit_row(db, parts, c, doffs, dbytes, lo, hi, d, p - 1);
    }
}

/// Every non-empty group of the normal form is some dictionary entry's group.
pub proof fn lemma_keys_complete(db: Database, parts: Seq<PartView>, c: Cols, doffs: Seq<u64>, dbytes: Seq<u8>,
    lo: int, hi: int, kr: Row)
    requires
        bound(db, parts),
        cols_from_parts(c, parts),
        parts[p_odo()] == PartView::U64(doffs),
        parts[p_ody()] == PartView::U8(dbytes),
        gcount(qspec(lrel_of(db), lo, hi), orel_of(db), kr) > 0,
    ensures
        exists|d: int| 0 <= d < doffs.len() - 1 && kr == key_d(doffs, dbytes, d),
{
    let g = qspec(lrel_of(db), lo, hi);
    let orel = orel_of(db);
    let n = orel.len() as int;
    lemma_orders_cols(db, parts, c, doffs, dbytes);
    lemma_row_maps(db, parts);
    lemma_count_witness(g, orel, kr);
    let m = choose|m: int| 0 <= m < orel.len() && #[trigger] hit(g, orel[m], kr);
    let omap = orders_map(otp(parts), n);
    assert(covered(omap, m));
    let p = choose|p: int| 0 <= p < omap.len() && omap[p] == m;
    let o = orows(parts, db);
    assert(o[p] == orel[m]);
    let d = oprio(c, p);
    assert(kr =~= key_d(doffs, dbytes, d));
}

// ------------------------------------------------------------------------------------------------ summary

/// Everything the scan needs about the model, from one bound database.
pub proof fn lemma_model_facts(db: Database, parts: Seq<PartView>, c: Cols, doffs: Seq<u64>, dbytes: Seq<u8>, zmax: Seq<i64>)
    requires
        bound(db, parts),
        cols_from_parts(c, parts),
        parts[p_odo()] == PartView::U64(doffs),
        parts[p_ody()] == PartView::U8(dbytes),
        zmax == i64s(parts[p_odz()]),
    ensures
        doffs.len() >= 1,
        cols_ok(c, doffs.len() - 1),
        keys_distinct(c),
        u64s(parts[p_flag()])[0] == 1 ==> lines_clustered(c),
        text_parts_wf(doffs, dbytes, doffs.len() - 1),
        zmax.len() == c.od_bases@.len(),
        forall|p: int| 0 <= p < c.n_o ==> #[trigger] odate(c, p) <= zmax[p / c.bs_o as int],
{
    lemma_parts_shape(db, parts);
    lemma_cols_ok(db, parts, c, doffs, dbytes);
    lemma_keys_distinct(db, parts, c, doffs, dbytes);
    lemma_orders_cols(db, parts, c, doffs, dbytes);
    if u64s(parts[p_flag()])[0] == 1 {
        lemma_clustered(db, parts, c, doffs, dbytes);
    }
    let o = orows(parts, db);
    assert forall|p: int| 0 <= p < c.n_o implies #[trigger] odate(c, p) <= zmax[p / c.bs_o as int] by {
        assert(o[p][4] == Val::Date(odate(c, p)));
    }
}

} // verus!
