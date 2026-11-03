//! The stored lineitem relation of storage `facts` and the integer model (`model::Model`): from the storage's
//! `represents` (`lineitem_ok` over the table's parts `tp`), the model of the parts is well formed, every stored
//! row's Q1 columns are the model's decoded values, the normal form's group accumulators of a key are the
//! model's key sums (`ksum`, `kabs`), keys outside the dictionaries have no qualifying row, and the stored order
//! (a permutation of the canonical rows) gives the same accumulators as the canonical order.
use vstd::prelude::*;
use crate::spec::value::*;
use crate::spec::numeric::abs;
use crate::gendb_entry::layout::PartView;
use crate::link::query::*;
use crate::link::join::{lemma_acc_sum_of, lemma_sum_of_perm};
use crate::link::expr::ival;
use crate::stores::facts::interface::*;
use crate::stores::facts::interface::common::colfmt::*;
use crate::stores::facts::interface::common::read::lemma_for_row;
use super::spec::*;
use super::model::*;

verus! {

/// The values of a U16 part (empty for another kind).
pub open spec fn u16s(p: PartView) -> Seq<u16> {
    match p {
        PartView::U16(s) => s,
        _ => Seq::empty(),
    }
}

/// The model of the lineitem parts `tp`.
pub open spec fn tp_model(tp: Seq<PartView>) -> Model {
    let lay = u64s(tp[LI_LAYOUT as int]);
    Model {
        qty: u16s(tp[LI_QUANTITY_CODES as int]),
        qty_b: i64s(tp[LI_QUANTITY_BASE as int]),
        price: u32s(tp[LI_EXTENDEDPRICE_CODES as int]),
        price_b: i64s(tp[LI_EXTENDEDPRICE_BASE as int]),
        disc: u8s(tp[LI_DISCOUNT_CODES as int]),
        disc_b: i64s(tp[LI_DISCOUNT_BASE as int]),
        tax: u8s(tp[LI_TAX_CODES as int]),
        tax_b: i64s(tp[LI_TAX_BASE as int]),
        rf: u8s(tp[LI_RETURNFLAG_CODES as int]),
        rf_b: u64s(tp[LI_RETURNFLAG_BASE as int]),
        ls: u8s(tp[LI_LINESTATUS_CODES as int]),
        ls_b: u64s(tp[LI_LINESTATUS_BASE as int]),
        ship: u16s(tp[LI_SHIPDATE_CODES as int]),
        ship_b: i64s(tp[LI_SHIPDATE_BASE as int]),
        ship_z: i64s(tp[LI_SHIPDATE_ZMAX as int]),
        n: lay[0] as int,
        bsize: lay[1] as int,
        nb: i64s(tp[LI_QUANTITY_BASE as int]).len() as int,
        nrf: u64s(tp[LI_RETURNFLAG_DICT_OFFS as int]).len() - 1,
        nls: u64s(tp[LI_LINESTATUS_DICT_OFFS as int]).len() - 1,
    }
}

/// The dictionary entries of l_returnflag and l_linestatus.
pub open spec fn rf_text(tp: Seq<PartView>, a: int) -> Seq<u8> {
    text_of(u64s(tp[LI_RETURNFLAG_DICT_OFFS as int]), u8s(tp[LI_RETURNFLAG_DICT_BYTES as int]), a)
}

pub open spec fn ls_text(tp: Seq<PartView>, b: int) -> Seq<u8> {
    text_of(u64s(tp[LI_LINESTATUS_DICT_OFFS as int]), u8s(tp[LI_LINESTATUS_DICT_BYTES as int]), b)
}

/// The group key of dictionary indices `(a, b)`.
pub open spec fn dkey(tp: Seq<PartView>, a: int, b: int) -> Row {
    seq![Val::Text(rf_text(tp, a)), Val::Text(ls_text(tp, b))]
}

/// The value kind of aggregate `jj < 7` of the normal form.
pub open spec fn wmap(jj: int) -> int {
    if jj == 0 || jj == 4 { 0 } else if jj == 1 || jj == 5 { 1 } else if jj == 2 { 2 } else if jj == 3 { 3 } else { 4 }
}

/// The shape facts of the parts beyond `model_wf` that the scans use.
pub open spec fn tp_shape(tp: Seq<PartView>) -> bool {
    let m = tp_model(tp);
    &&& m.nb * m.bsize < m.n + m.bsize
    &&& m.n + m.bsize <= u64::MAX
    &&& tp[LI_LAYOUT as int] is U64 && u64s(tp[LI_LAYOUT as int]).len() == 2
    &&& tp[LI_QUANTITY_CODES as int] is U16 && tp[LI_QUANTITY_BASE as int] is I64
    &&& tp[LI_EXTENDEDPRICE_CODES as int] is U32 && tp[LI_EXTENDEDPRICE_BASE as int] is I64
    &&& tp[LI_DISCOUNT_CODES as int] is U8 && tp[LI_DISCOUNT_BASE as int] is I64
    &&& tp[LI_TAX_CODES as int] is U8 && tp[LI_TAX_BASE as int] is I64
    &&& tp[LI_RETURNFLAG_CODES as int] is U8 && tp[LI_RETURNFLAG_BASE as int] is U64
    &&& tp[LI_LINESTATUS_CODES as int] is U8 && tp[LI_LINESTATUS_BASE as int] is U64
    &&& tp[LI_SHIPDATE_CODES as int] is U16 && tp[LI_SHIPDATE_BASE as int] is I64 && tp[LI_SHIPDATE_ZMAX as int] is I64
    &&& tp[LI_RETURNFLAG_DICT_OFFS as int] is U64 && tp[LI_RETURNFLAG_DICT_BYTES as int] is U8
    &&& tp[LI_LINESTATUS_DICT_OFFS as int] is U64 && tp[LI_LINESTATUS_DICT_BYTES as int] is U8
    &&& u64s(tp[LI_RETURNFLAG_DICT_OFFS as int]).len() >= 1 && u64s(tp[LI_LINESTATUS_DICT_OFFS as int]).len() >= 1
    &&& text_parts_wf(u64s(tp[LI_RETURNFLAG_DICT_OFFS as int]), u8s(tp[LI_RETURNFLAG_DICT_BYTES as int]), m.nrf)
    &&& text_parts_wf(u64s(tp[LI_LINESTATUS_DICT_OFFS as int]), u8s(tp[LI_LINESTATUS_DICT_BYTES as int]), m.nls)
    &&& dict_sorted(u64s(tp[LI_RETURNFLAG_DICT_OFFS as int]), u8s(tp[LI_RETURNFLAG_DICT_BYTES as int]), m.nrf)
    &&& dict_sorted(u64s(tp[LI_LINESTATUS_DICT_OFFS as int]), u8s(tp[LI_LINESTATUS_DICT_BYTES as int]), m.nls)
}

/// The facts every stored row of the relation has: its Q1 columns are the model's values.
pub open spec fn row_facts(tp: Seq<PartView>, srows: Seq<Row>, j: int) -> bool {
    let m = tp_model(tp);
    &&& srows[j][4] == (Val::Num { coeff: qv(m, j), scale: 2 })
    &&& srows[j][5] == (Val::Num { coeff: pv(m, j), scale: 2 })
    &&& srows[j][6] == (Val::Num { coeff: dv(m, j), scale: 2 })
    &&& srows[j][7] == (Val::Num { coeff: tv(m, j), scale: 2 })
    &&& srows[j][8] == Val::Text(rf_text(tp, rfi(m, j)))
    &&& srows[j][9] == Val::Text(ls_text(tp, lsi(m, j)))
    &&& srows[j][10] == Val::Date(shv(m, j))
}

/// The groups of the parts: well formed, `bsize >= 1`.
proof fn lemma_groups(tp: Seq<PartView>, n: int)
    requires table_layout_ok(tp, n),
    ensures ({
        let m = tp_model(tp);
        &&& m.bsize >= 1 && m.n == n && n >= 0
        &&& gs_at(tp, LI_GROUPS as int).len() == nblocks_of(n, m.bsize) + 1
        &&& nblocks_of(n, m.bsize) * m.bsize >= n
        &&& nblocks_of(n, m.bsize) * m.bsize < n + m.bsize
        &&& n + m.bsize <= u64::MAX
    }),
{
    let m = tp_model(tp);
    lemma_uniform_groups(tp[LI_GROUPS as int], n, m.bsize);
    lemma_nblocks(n, m.bsize);
    let nb = nblocks_of(n, m.bsize);
    if nb > 0 {
        assert(nb * m.bsize == (nb - 1) * m.bsize + m.bsize) by (nonlinear_arith);
    } else {
        assert(nb * m.bsize == 0) by (nonlinear_arith) requires nb == 0;
    }
}

/// From `lineitem_ok`: the part kinds, sequence lengths and block arithmetic of the model.
pub proof fn lemma_tp_lengths(tp: Seq<PartView>, rel: Seq<Row>)
    requires lineitem_ok(tp, rel),
    ensures ({
        let m = tp_model(tp);
        &&& tp_shape(tp)
        &&& m.n == rel.len() && m.n >= 0 && m.bsize >= 1 && m.nb >= 0 && m.nb * m.bsize >= m.n
        &&& m.qty.len() == m.n && m.price.len() == m.n && m.disc.len() == m.n && m.tax.len() == m.n
        &&& m.rf.len() == m.n && m.ls.len() == m.n && m.ship.len() == m.n
        &&& m.qty_b.len() == m.nb && m.price_b.len() == m.nb && m.disc_b.len() == m.nb && m.tax_b.len() == m.nb
        &&& m.rf_b.len() == m.nb && m.ls_b.len() == m.nb && m.ship_b.len() == m.nb && m.ship_z.len() == m.nb
        &&& m.nrf >= 0 && m.nls >= 0
    }),
{
    let m = tp_model(tp);
    let n = rel.len() as int;
    lemma_groups(tp, n);
    let srows = lineitem_rows(tp, rel);
    assert(lineitem_cols_ok(tp, srows));
}

/// From `lineitem_ok`: the zone maxima bound the shipdates and dictionary indices lie in their dictionaries.
pub proof fn lemma_tp_bounds(tp: Seq<PartView>, rel: Seq<Row>)
    requires lineitem_ok(tp, rel),
    ensures ({
        let m = tp_model(tp);
        &&& forall|j: int| 0 <= j < m.n ==> #[trigger] shv(m, j) <= m.ship_z[blk(m, j)]
        &&& forall|j: int| 0 <= j < m.n ==> 0 <= #[trigger] rfi(m, j) < m.nrf
        &&& forall|j: int| 0 <= j < m.n ==> 0 <= #[trigger] lsi(m, j) < m.nls
    }),
{
    let m = tp_model(tp);
    let n = rel.len() as int;
    let srows = lineitem_rows(tp, rel);
    let gs = gs_at(tp, LI_GROUPS as int);
    lemma_groups(tp, n);
    let bs = m.bsize;
    assert(lineitem_cols_ok(tp, srows));
    assert forall|j: int| 0 <= j < n implies #[trigger] shv(m, j) <= m.ship_z[blk(m, j)] by {
        lemma_for_row(tp[LI_GROUPS as int], n, bs, tp[LI_SHIPDATE_BASE as int], tp[LI_SHIPDATE_CODES as int], j);
        assert(in_group(gs, j / bs, j));
    }
    assert forall|j: int| 0 <= j < n implies 0 <= #[trigger] rfi(m, j) < m.nrf by {
        lemma_for_row(tp[LI_GROUPS as int], n, bs, tp[LI_RETURNFLAG_BASE as int], tp[LI_RETURNFLAG_CODES as int], j);
        assert(srows.len() == n);
        assert(srows[j][8] == Val::Text(text_of(u64s(tp[LI_RETURNFLAG_DICT_OFFS as int]), u8s(tp[LI_RETURNFLAG_DICT_BYTES as int]),
            for_at(gs, tp[LI_RETURNFLAG_BASE as int], tp[LI_RETURNFLAG_CODES as int], j))));
    }
    assert forall|j: int| 0 <= j < n implies 0 <= #[trigger] lsi(m, j) < m.nls by {
        lemma_for_row(tp[LI_GROUPS as int], n, bs, tp[LI_LINESTATUS_BASE as int], tp[LI_LINESTATUS_CODES as int], j);
        assert(srows.len() == n);
        assert(srows[j][9] == Val::Text(text_of(u64s(tp[LI_LINESTATUS_DICT_OFFS as int]), u8s(tp[LI_LINESTATUS_DICT_BYTES as int]),
            for_at(gs, tp[LI_LINESTATUS_BASE as int], tp[LI_LINESTATUS_CODES as int], j))));
    }
}

/// From `lineitem_ok`: every stored row has the row facts.
proof fn lemma_tp_rows(tp: Seq<PartView>, rel: Seq<Row>)
    requires lineitem_ok(tp, rel),
    ensures
        lineitem_rows(tp, rel).len() == rel.len(),
        forall|j: int| 0 <= j < rel.len() ==> #[trigger] row_facts(tp, lineitem_rows(tp, rel), j),
{
    let m = tp_model(tp);
    let n = rel.len() as int;
    let srows = lineitem_rows(tp, rel);
    lemma_groups(tp, n);
    let bs = m.bsize;
    assert(lineitem_cols_ok(tp, srows));
    assert(srows.len() == n);
    assert forall|j: int| 0 <= j < n implies #[trigger] row_facts(tp, srows, j) by {
        lemma_for_row(tp[LI_GROUPS as int], n, bs, tp[LI_QUANTITY_BASE as int], tp[LI_QUANTITY_CODES as int], j);
        lemma_for_row(tp[LI_GROUPS as int], n, bs, tp[LI_EXTENDEDPRICE_BASE as int], tp[LI_EXTENDEDPRICE_CODES as int], j);
        lemma_for_row(tp[LI_GROUPS as int], n, bs, tp[LI_DISCOUNT_BASE as int], tp[LI_DISCOUNT_CODES as int], j);
        lemma_for_row(tp[LI_GROUPS as int], n, bs, tp[LI_TAX_BASE as int], tp[LI_TAX_CODES as int], j);
        lemma_for_row(tp[LI_GROUPS as int], n, bs, tp[LI_RETURNFLAG_BASE as int], tp[LI_RETURNFLAG_CODES as int], j);
        lemma_for_row(tp[LI_GROUPS as int], n, bs, tp[LI_LINESTATUS_BASE as int], tp[LI_LINESTATUS_CODES as int], j);
        lemma_for_row(tp[LI_GROUPS as int], n, bs, tp[LI_SHIPDATE_BASE as int], tp[LI_SHIPDATE_CODES as int], j);
    }
}

/// From `lineitem_ok` (with a non-empty l_linestatus dictionary): the model is well formed and every stored row
/// has the row facts.
pub proof fn lemma_tp_model(tp: Seq<PartView>, rel: Seq<Row>)
    requires lineitem_ok(tp, rel), u64s(tp[LI_LINESTATUS_DICT_OFFS as int]).len() >= 2,
    ensures ({
        let m = tp_model(tp);
        let srows = lineitem_rows(tp, rel);
        &&& model_wf(m)
        &&& tp_shape(tp)
        &&& m.n == rel.len() && srows.len() == rel.len()
        &&& forall|j: int| 0 <= j < m.n ==> #[trigger] row_facts(tp, srows, j)
    }),
{
    lemma_tp_lengths(tp, rel);
    lemma_tp_bounds(tp, rel);
    lemma_tp_rows(tp, rel);
}

/// Distinct dictionary indices give distinct texts, so a row's key is `dkey(a, b)` exactly for its indices.
pub proof fn lemma_dkey_eq(tp: Seq<PartView>, a1: int, b1: int, a2: int, b2: int)
    requires
        tp_shape(tp),
        0 <= a1 < tp_model(tp).nrf, 0 <= a2 < tp_model(tp).nrf,
        0 <= b1 < tp_model(tp).nls, 0 <= b2 < tp_model(tp).nls,
    ensures (dkey(tp, a1, b1) == dkey(tp, a2, b2)) == (a1 == a2 && b1 == b2),
{
    let m = tp_model(tp);
    if a1 != a2 {
        lemma_dict_distinct(u64s(tp[LI_RETURNFLAG_DICT_OFFS as int]), u8s(tp[LI_RETURNFLAG_DICT_BYTES as int]), m.nrf, a1, a2);
        assert(dkey(tp, a1, b1)[0] != dkey(tp, a2, b2)[0]);
    }
    if b1 != b2 {
        lemma_dict_distinct(u64s(tp[LI_LINESTATUS_DICT_OFFS as int]), u8s(tp[LI_LINESTATUS_DICT_BYTES as int]), m.nls, b1, b2);
        assert(dkey(tp, a1, b1)[1] != dkey(tp, a2, b2)[1]);
    }
}

/// One stored row: its qualification and key under the normal form, and its aggregate arguments.
pub proof fn lemma_row_q1(tp: Seq<PartView>, srows: Seq<Row>, p: int, j: int)
    requires row_facts(tp, srows, j),
    ensures
        q1_qual(p, srows[j]) == (shv(tp_model(tp), j) <= p),
        q1_key(srows[j]) == dkey(tp, rfi(tp_model(tp), j), lsi(tp_model(tp), j)),
        forall|jj: int| 0 <= jj < 7 ==> #[trigger] q1_arg(jj, srows[j]) == mval(tp_model(tp), wmap(jj), j),
{
    let m = tp_model(tp);
    assert(q1_key(srows[j]) =~= dkey(tp, rfi(m, j), lsi(m, j)));
    assert forall|jj: int| 0 <= jj < 7 implies #[trigger] q1_arg(jj, srows[j]) == mval(m, wmap(jj), j) by {
        assert(ival(srows[j][4]) == qv(m, j) && ival(srows[j][5]) == pv(m, j));
        assert(ival(srows[j][6]) == dv(m, j) && ival(srows[j][7]) == tv(m, j));
    }
}

/// The normal form's accumulators of key `dkey(a, b)` over the stored rows `0 .. hi` are the model's key sums.
pub proof fn lemma_acc_ksum(tp: Seq<PartView>, srows: Seq<Row>, p: int, a: int, b: int, jj: int, hi: int)
    requires
        tp_shape(tp), model_wf(tp_model(tp)),
        0 <= hi <= tp_model(tp).n, hi <= srows.len(),
        forall|j: int| 0 <= j < tp_model(tp).n ==> #[trigger] row_facts(tp, srows, j),
        0 <= a < tp_model(tp).nrf, 0 <= b < tp_model(tp).nls, 0 <= jj < 7,
    ensures
        gcount(q1_spec(p), srows.subrange(0, hi), dkey(tp, a, b)) == ksum(tp_model(tp), p, a, b, 5, 0, hi),
        gsum(q1_spec(p), srows.subrange(0, hi), dkey(tp, a, b), jj) == ksum(tp_model(tp), p, a, b, wmap(jj), 0, hi),
        gabs(q1_spec(p), srows.subrange(0, hi), dkey(tp, a, b), jj) == kabs(tp_model(tp), p, a, b, wmap(jj), 0, hi),
    decreases hi,
{
    let g = q1_spec(p);
    let m = tp_model(tp);
    let k = dkey(tp, a, b);
    if hi == 0 {
        lemma_empty(g, srows, 0, k, jj);
    } else {
        lemma_acc_ksum(tp, srows, p, a, b, jj, hi - 1);
        let j = hi - 1;
        lemma_range_step(g, srows, 0, j, k, jj);
        lemma_row_q1(tp, srows, p, j);
        assert(0 <= rfi(m, j) < m.nrf && 0 <= lsi(m, j) < m.nls);
        lemma_dkey_eq(tp, rfi(m, j), lsi(m, j), a, b);
        assert(hit(g, srows[j], k) == ksel(m, p, a, b, j));
        assert(abs((g.arg)(jj, srows[j])) == abs_int(mval(m, wmap(jj), j)));
    }
}

/// A key that is no `dkey(a, b)` of dictionary indices has no qualifying stored row.
pub proof fn lemma_other_key(tp: Seq<PartView>, srows: Seq<Row>, p: int, k: Row, hi: int)
    requires
        tp_shape(tp), model_wf(tp_model(tp)),
        0 <= hi <= tp_model(tp).n, hi <= srows.len(),
        forall|j: int| 0 <= j < tp_model(tp).n ==> #[trigger] row_facts(tp, srows, j),
        forall|a: int, b: int| 0 <= a < tp_model(tp).nrf && 0 <= b < tp_model(tp).nls ==> #[trigger] dkey(tp, a, b) != k,
    ensures gcount(q1_spec(p), srows.subrange(0, hi), k) == 0,
    decreases hi,
{
    let g = q1_spec(p);
    let m = tp_model(tp);
    if hi == 0 {
        lemma_empty(g, srows, 0, k, 0);
    } else {
        lemma_other_key(tp, srows, p, k, hi - 1);
        let j = hi - 1;
        lemma_range_step(g, srows, 0, j, k, 0);
        lemma_row_q1(tp, srows, p, j);
        assert(0 <= rfi(m, j) < m.nrf && 0 <= lsi(m, j) < m.nls);
        assert(dkey(tp, rfi(m, j), lsi(m, j)) != k);
    }
}

/// The stored rows are a permutation of the relation: the same accumulators for every key.
pub proof fn lemma_perm_acc(tp: Seq<PartView>, rel: Seq<Row>, p: int, k: Row, jj: int)
    requires lineitem_ok(tp, rel),
    ensures
        gcount(q1_spec(p), rel, k) == gcount(q1_spec(p), lineitem_rows(tp, rel), k),
        gsum(q1_spec(p), rel, k, jj) == gsum(q1_spec(p), lineitem_rows(tp, rel), k, jj),
        gabs(q1_spec(p), rel, k, jj) == gabs(q1_spec(p), lineitem_rows(tp, rel), k, jj),
{
    let g = q1_spec(p);
    let srows = lineitem_rows(tp, rel);
    let n = rel.len() as int;
    lemma_stored_rows_multiset(rel, lineitem_map(tp, n));
    lemma_acc_sum_of(g, rel, k, jj);
    lemma_acc_sum_of(g, srows, k, jj);
    lemma_sum_of_perm(srows, rel, crate::link::join::count_term(g, k));
    lemma_sum_of_perm(srows, rel, crate::link::join::sum_term(g, k, jj));
    lemma_sum_of_perm(srows, rel, crate::link::join::abs_term(g, k, jj));
}

} // verus!
