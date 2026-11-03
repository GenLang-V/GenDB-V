//! The models' columns are the stored rows' values, for a database bound to the parts. Storage `facts`: the stored
//! orders rows (`bind::orows`, a permutation of the orders relation) hold `okey` / the o_orderstatus dictionary entry
//! of `ostat`, the stored lineitem rows (`bind::lrows`) `lkey`, `lsupp`, `lcmt`, `lrcp` (`lemma_orders_cols`,
//! `lemma_lineitem_cols`); the model's facts hold (`lemma_cols_ok`), o_orderkey is distinct (the orders primary
//! key, `lemma_keys_distinct`) and the lines follow the orders under the co-clustering flag (`lemma_clustered`).
//! Storage `suppliers` (canonical order): supplier row `r` holds `skey`, `sname`, `snat`, nation row `n` `nkey`,
//! `nname` (`lemma_supplier_cols`, `lemma_nation_cols`, `lemma_scols_ok`); both keys are distinct (primary keys).
use vstd::prelude::*;
use crate::gendb_entry::layout::PartView;
use crate::spec::value::*;
use crate::spec::typing::*;
use crate::spec::types::*;
use crate::spec::constraints::*;
use crate::spec::equality::*;
use crate::gendb_constraints::{declared_db, declared_schema};
use crate::stores::facts::declaration::*;
use crate::stores::facts::interface::*;
use crate::stores::facts::interface::common::colfmt::*;
use crate::stores::facts::interface::common::read::lemma_for_row;
use crate::stores::facts::interface::cluster::*;
use crate::stores::suppliers::interface as si;
use super::model::*;
use super::side::*;
use super::bind::*;

verus! {

// ------------------------------------------------------------------------------------------------ storage facts

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
        fbound(db, parts),
        cols_from_parts(c, parts),
        parts[p_oso()] == PartView::U64(doffs),
        parts[p_osy()] == PartView::U8(dbytes),
    ensures ({
        let o = orows(parts, db);
        let k = doffs.len() - 1;
        &&& o.len() == c.n_o
        &&& doffs.len() >= 1
        &&& text_parts_wf(doffs, dbytes, k)
        &&& dict_sorted(doffs, dbytes, k)
        &&& forall|p: int| 0 <= p < c.n_o ==> {
            &&& (#[trigger] o[p])[0] == Val::Int(okey(c, p))
            &&& 0 <= ostat(c, p) < k
            &&& o[p][2] == Val::Text(text_of(doffs, dbytes, ostat(c, p)))
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
    assert(tp[OR_ORDERSTATUS_CODES as int] == parts[p_osc()]);
    assert(tp[OR_ORDERSTATUS_BASE as int] == parts[p_osb()]);
    assert(tp[OR_ORDERSTATUS_DICT_OFFS as int] == parts[p_oso()]);
    assert(tp[OR_ORDERSTATUS_DICT_BYTES as int] == parts[p_osy()]);
    assert(o.len() == n);
    assert forall|p: int| 0 <= p < c.n_o implies {
        &&& (#[trigger] o[p])[0] == Val::Int(okey(c, p))
        &&& 0 <= ostat(c, p) < doffs.len() - 1
        &&& o[p][2] == Val::Text(text_of(doffs, dbytes, ostat(c, p)))
    } by {
        lemma_bs_group(c.bs_o as int, stored_bs, n, p);
        lemma_for_row(gp, n, stored_bs, tp[OR_ORDERKEY_BASE as int], tp[OR_ORDERKEY_CODES as int], p);
        lemma_for_row(gp, n, stored_bs, tp[OR_ORDERSTATUS_BASE as int], tp[OR_ORDERSTATUS_CODES as int], p);
        assert(int_col(o, 0, gs, tp[OR_ORDERKEY_BASE as int], tp[OR_ORDERKEY_CODES as int]));
        assert(dict_col(o, 2, gs, tp[OR_ORDERSTATUS_BASE as int], tp[OR_ORDERSTATUS_CODES as int], doffs, dbytes));
    }
}

/// The model's lineitem columns are the stored lineitem rows' values.
pub proof fn lemma_lineitem_cols(db: Database, parts: Seq<PartView>, c: Cols)
    requires
        fbound(db, parts),
        cols_from_parts(c, parts),
    ensures ({
        let l = lrows(parts, db);
        &&& l.len() == c.n_l
        &&& forall|j: int| 0 <= j < c.n_l ==> {
            &&& (#[trigger] l[j])[0] == Val::Int(lkey(c, j))
            &&& l[j][2] == Val::Int(lsupp(c, j))
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
    assert(tp[LI_SUPPKEY_CODES as int] == parts[p_lsc()]);
    assert(tp[LI_SUPPKEY_BASE as int] == parts[p_lsb()]);
    assert(tp[LI_COMMITDATE_CODES as int] == parts[p_lcc()]);
    assert(tp[LI_COMMITDATE_BASE as int] == parts[p_lcb()]);
    assert(tp[LI_RECEIPTDATE_CODES as int] == parts[p_lrc()]);
    assert(tp[LI_RECEIPTDATE_BASE as int] == parts[p_lrb()]);
    assert(l.len() == n);
    assert forall|j: int| 0 <= j < c.n_l implies {
        &&& (#[trigger] l[j])[0] == Val::Int(lkey(c, j))
        &&& l[j][2] == Val::Int(lsupp(c, j))
        &&& l[j][11] == Val::Date(lcmt(c, j))
        &&& l[j][12] == Val::Date(lrcp(c, j))
    } by {
        lemma_bs_group(c.bs_l as int, stored_bs, n, j);
        lemma_for_row(gp, n, stored_bs, tp[LI_ORDERKEY_BASE as int], tp[LI_ORDERKEY_CODES as int], j);
        lemma_for_row(gp, n, stored_bs, tp[LI_SUPPKEY_BASE as int], tp[LI_SUPPKEY_CODES as int], j);
        lemma_for_row(gp, n, stored_bs, tp[LI_COMMITDATE_BASE as int], tp[LI_COMMITDATE_CODES as int], j);
        lemma_for_row(gp, n, stored_bs, tp[LI_RECEIPTDATE_BASE as int], tp[LI_RECEIPTDATE_CODES as int], j);
        assert(int_col(l, 0, gs, tp[LI_ORDERKEY_BASE as int], tp[LI_ORDERKEY_CODES as int]));
        assert(int_col(l, 2, gs, tp[LI_SUPPKEY_BASE as int], tp[LI_SUPPKEY_CODES as int]));
        assert(date_col(l, 11, gs, tp[LI_COMMITDATE_BASE as int], tp[LI_COMMITDATE_CODES as int]));
        assert(date_col(l, 12, gs, tp[LI_RECEIPTDATE_BASE as int], tp[LI_RECEIPTDATE_CODES as int]));
    }
}

/// The stored rows are the stored relation's rows under a bijection.
pub proof fn lemma_row_maps(db: Database, parts: Seq<PartView>)
    requires fbound(db, parts),
    ensures
        is_perm(orders_map(otp(parts), orel_of(db).len() as int), orel_of(db).len() as int),
        orows(parts, db) == stored_rows(orel_of(db), orders_map(otp(parts), orel_of(db).len() as int)),
        is_perm(lineitem_map(ltp(parts), lrel_of(db).len() as int), lrel_of(db).len() as int),
        lrows(parts, db) == stored_rows(lrel_of(db), lineitem_map(ltp(parts), lrel_of(db).len() as int)),
{
    assert(orders_ok(otp(parts), orel_of(db)));
    assert(lineitem_ok(ltp(parts), lrel_of(db)));
}

/// The stored relations are the tables' rows on their stored columns; the values Q21 reads are typed.
pub proof fn lemma_rel_values(db: Database)
    requires db_ok(db),
    ensures
        orel_of(db).len() == db.tables[1].len(),
        lrel_of(db).len() == db.tables[0].len(),
        forall|i: int| 0 <= i < orel_of(db).len() ==> {
            &&& (#[trigger] orel_of(db)[i])[0] == db.tables[1][i][0]
            &&& orel_of(db)[i][2] == db.tables[1][i][2]
            &&& orel_of(db)[i][0] is Int
            &&& i64::MIN <= orel_of(db)[i][0]->Int_0 <= i64::MAX
        },
        forall|j: int| 0 <= j < lrel_of(db).len() ==> {
            &&& (#[trigger] lrel_of(db)[j])[0] == db.tables[0][j][0]
            &&& lrel_of(db)[j][2] == db.tables[0][j][2]
            &&& lrel_of(db)[j][11] == db.tables[0][j][11]
            &&& lrel_of(db)[j][12] == db.tables[0][j][12]
            &&& lrel_of(db)[j][0] is Int && i64::MIN <= lrel_of(db)[j][0]->Int_0 <= i64::MAX
            &&& lrel_of(db)[j][2] is Int && i64::MIN <= lrel_of(db)[j][2]->Int_0 <= i64::MAX
            &&& lrel_of(db)[j][11] is Date && i64::MIN <= lrel_of(db)[j][11]->Date_0 <= i64::MAX
            &&& lrel_of(db)[j][12] is Date && i64::MIN <= lrel_of(db)[j][12]->Date_0 <= i64::MAX
        },
{
    lemma_stored_relations(db);
    crate::link::source::lemma_proj_all_index(db.tables[1], stored_cols_t1());
    crate::link::source::lemma_proj_all_index(db.tables[0], stored_cols_t0());
    let (oc, lc) = (stored_columns_t1(), stored_columns_t0());
    assert(oc[0] == Column { ty: SqlType::Int8, nullable: false });
    assert(lc[0] == Column { ty: SqlType::Int8, nullable: false });
    assert(lc[2] == Column { ty: SqlType::Int8, nullable: false });
    assert(lc[11] == Column { ty: SqlType::Date, nullable: false });
    assert(lc[12] == Column { ty: SqlType::Date, nullable: false });
    assert(oc.len() == 7 && lc.len() == 15);
    assert forall|i: int| 0 <= i < orel_of(db).len() implies {
        &&& (#[trigger] orel_of(db)[i])[0] == db.tables[1][i][0]
        &&& orel_of(db)[i][2] == db.tables[1][i][2]
        &&& orel_of(db)[i][0] is Int
        &&& i64::MIN <= orel_of(db)[i][0]->Int_0 <= i64::MAX
    } by {
        assert(orel_of(db)[i] == crate::link::query::proj(db.tables[1][i], stored_cols_t1()));
        assert(value_in_column(orel_of(db)[i][0], oc[0]));
    }
    assert forall|j: int| 0 <= j < lrel_of(db).len() implies {
        &&& (#[trigger] lrel_of(db)[j])[0] == db.tables[0][j][0]
        &&& lrel_of(db)[j][2] == db.tables[0][j][2]
        &&& lrel_of(db)[j][11] == db.tables[0][j][11]
        &&& lrel_of(db)[j][12] == db.tables[0][j][12]
        &&& lrel_of(db)[j][0] is Int && i64::MIN <= lrel_of(db)[j][0]->Int_0 <= i64::MAX
        &&& lrel_of(db)[j][2] is Int && i64::MIN <= lrel_of(db)[j][2]->Int_0 <= i64::MAX
        &&& lrel_of(db)[j][11] is Date && i64::MIN <= lrel_of(db)[j][11]->Date_0 <= i64::MAX
        &&& lrel_of(db)[j][12] is Date && i64::MIN <= lrel_of(db)[j][12]->Date_0 <= i64::MAX
    } by {
        assert(lrel_of(db)[j] == crate::link::query::proj(db.tables[0][j], stored_cols_t0()));
        assert(value_in_column(lrel_of(db)[j][0], lc[0]));
        assert(value_in_column(lrel_of(db)[j][2], lc[2]));
        assert(value_in_column(lrel_of(db)[j][11], lc[11]));
        assert(value_in_column(lrel_of(db)[j][12], lc[12]));
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

/// The model's facts: shapes, value ranges and dictionary indices.
pub proof fn lemma_cols_ok(db: Database, parts: Seq<PartView>, c: Cols, doffs: Seq<u64>, dbytes: Seq<u8>)
    requires
        fbound(db, parts),
        cols_from_parts(c, parts),
        parts[p_oso()] == PartView::U64(doffs),
        parts[p_osy()] == PartView::U8(dbytes),
        doffs.len() - 1 <= u64::MAX,
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
    assert forall|p: int| 0 <= p < c.n_o implies in_i64(#[trigger] okey(c, p)) by {
        assert(0 <= omap[p] < n_o);
        assert(o[p] == orel_of(db)[omap[p]]);
    }
    assert forall|p: int| 0 <= p < c.n_o implies 0 <= #[trigger] ostat(c, p) < k by {
        assert(o[p][0] == Val::Int(okey(c, p)));
    }
    assert forall|j: int| 0 <= j < c.n_l implies in_i64(#[trigger] lkey(c, j)) && in_i64(lsupp(c, j)) && in_i64(lcmt(c, j)) && in_i64(lrcp(c, j)) by {
        assert(0 <= lmap[j] < n_l);
        assert(l[j] == lrel_of(db)[lmap[j]]);
    }
    assert forall|j: int| 0 <= j < c.n_l implies in_i64(#[trigger] lsupp(c, j)) by {
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

/// The first column of rows `a`, `b` of table `t` (whose first declared constraint is the primary key on column 0)
/// differs when the rows differ.
pub proof fn lemma_pk0(db: Database, t: int, a: int, b: int)
    requires
        db_ok(db),
        constraints_hold(declared_db(db)),
        t == 1 || t == 5 || t == 6,
        0 <= a < db.tables[t].len(), 0 <= b < db.tables[t].len(),
        a != b,
    ensures db.tables[t][a][0] != db.tables[t][b][0],
{
    let ddb = declared_db(db);
    crate::gendb_constraints::lemma_declared_schema();
    assert(ddb.schema[t].constraints[0] == Constraint::Key { cols: seq![0nat], primary: true, nulls_distinct: true });
    if db.tables[t][a][0] == db.tables[t][b][0] {
        let (ra, rb) = (db.tables[t][a], db.tables[t][b]);
        let ka = key_of(ra, seq![0nat]);
        let kb = key_of(rb, seq![0nat]);
        assert(ka =~= kb);
        crate::bridge::equality::lemma_row_not_distinct_refl(ka);
        crate::bridge::constraints::lemma_primary_key_identifies(ddb, t, 0, seq![0nat], true, a, b);
    }
}

/// Under the orders primary key, o_orderkey is distinct over the stored orders rows.
pub proof fn lemma_keys_distinct(db: Database, parts: Seq<PartView>, c: Cols, doffs: Seq<u64>, dbytes: Seq<u8>)
    requires
        fbound(db, parts),
        cols_from_parts(c, parts),
        parts[p_oso()] == PartView::U64(doffs),
        parts[p_osy()] == PartView::U8(dbytes),
    ensures keys_distinct(c),
{
    let n = c.n_o as int;
    lemma_orders_cols(db, parts, c, doffs, dbytes);
    lemma_row_maps(db, parts);
    lemma_rel_values(db);
    let o = orows(parts, db);
    let omap = orders_map(otp(parts), n);
    assert forall|a: int, b: int| 0 <= a < c.n_o && 0 <= b < c.n_o && a != b implies #[trigger] okey(c, a) != #[trigger] okey(c, b) by {
        if okey(c, a) == okey(c, b) {
            let (ma, mb) = (omap[a], omap[b]);
            assert(o[a] == orel_of(db)[ma] && o[b] == orel_of(db)[mb]);
            assert(ma != mb);
            lemma_pk0(db, 1, ma, mb);
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
        fbound(db, parts),
        cols_from_parts(c, parts),
        parts[p_oso()] == PartView::U64(doffs),
        parts[p_osy()] == PartView::U8(dbytes),
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

// ------------------------------------------------------------------------------------------------ storage suppliers

/// The supplier and nation stored relations are their tables' rows (every column stored, canonical order).
pub proof fn lemma_srels(db: Database)
    requires db_ok(db),
    ensures
        srel_of(db).len() == db.tables[5].len(),
        nrel_of(db).len() == db.tables[6].len(),
        forall|r: int| 0 <= r < srel_of(db).len() ==> (#[trigger] srel_of(db)[r])[0] == db.tables[5][r][0]
            && srel_of(db)[r][1] == db.tables[5][r][1] && srel_of(db)[r][3] == db.tables[5][r][3],
        forall|n: int| 0 <= n < nrel_of(db).len() ==> (#[trigger] nrel_of(db)[n])[0] == db.tables[6][n][0]
            && nrel_of(db)[n][1] == db.tables[6][n][1],
{
    crate::stores::suppliers::declaration::lemma_stored_relations(db);
    use crate::stores::suppliers::declaration::{stored_cols_t1, stored_cols_t2};
    crate::link::source::lemma_proj_all_index(db.tables[5], stored_cols_t1());
    crate::link::source::lemma_proj_all_index(db.tables[6], stored_cols_t2());
    assert forall|r: int| 0 <= r < srel_of(db).len() implies (#[trigger] srel_of(db)[r])[0] == db.tables[5][r][0]
        && srel_of(db)[r][1] == db.tables[5][r][1] && srel_of(db)[r][3] == db.tables[5][r][3] by {
        assert(srel_of(db)[r] == crate::link::query::proj(db.tables[5][r], stored_cols_t1()));
    }
    assert forall|n: int| 0 <= n < nrel_of(db).len() implies (#[trigger] nrel_of(db)[n])[0] == db.tables[6][n][0]
        && nrel_of(db)[n][1] == db.tables[6][n][1] by {
        assert(nrel_of(db)[n] == crate::link::query::proj(db.tables[6][n], stored_cols_t2()));
    }
}

/// The supplier model's columns are the supplier rows' values; the nation model's the nation rows'.
pub proof fn lemma_supplier_cols(db: Database, parts: Seq<PartView>, sc: SCols)
    requires
        sbound(db, parts),
        scols_from_parts(sc, parts),
    ensures
        srel_of(db).len() == sc.n_s,
        nrel_of(db).len() == sc.n_n,
        forall|r: int| 0 <= r < sc.n_s ==> {
            &&& (#[trigger] srel_of(db)[r])[0] == Val::Int(skey(sc, r))
            &&& srel_of(db)[r][1] == Val::Text(sname(sc, r))
            &&& srel_of(db)[r][3] == Val::Int(snat(sc, r))
        },
        forall|n: int| 0 <= n < sc.n_n ==> {
            &&& (#[trigger] nrel_of(db)[n])[0] == Val::Int(nkey(sc, n))
            &&& nrel_of(db)[n][1] == Val::Text(nname(sc, n))
        },
{
    use crate::stores::suppliers::interface::common::colfmt as sf;
    let st = stp(parts);
    let nt = ntp(parts);
    let srel = srel_of(db);
    let nrel = nrel_of(db);
    lemma_sparts_shape(db, parts);
    assert(si::supplier_ok(st, srel));
    assert(si::nation_ok(nt, nrel));
    let (ns, nn) = (srel.len() as int, nrel.len() as int);
    let sbs = sf::u64s(st[si::SU_LAYOUT as int])[1] as int;
    let nbs = sf::u64s(nt[si::NA_LAYOUT as int])[1] as int;
    assert(st[si::SU_LAYOUT as int] == parts[p_sl()]);
    assert(st[si::SU_SUPPKEY_CODES as int] == parts[p_skc()]);
    assert(st[si::SU_SUPPKEY_BASE as int] == parts[p_skb()]);
    assert(st[si::SU_NATIONKEY_CODES as int] == parts[p_snc()]);
    assert(st[si::SU_NATIONKEY_BASE as int] == parts[p_snb()]);
    assert(st[si::SU_NAME_OFFS as int] == parts[p_smo()]);
    assert(st[si::SU_NAME_BYTES as int] == parts[p_smy()]);
    assert(nt[si::NA_LAYOUT as int] == parts[p_nl()]);
    assert(nt[si::NA_NATIONKEY_CODES as int] == parts[p_nkc()]);
    assert(nt[si::NA_NATIONKEY_BASE as int] == parts[p_nkb()]);
    assert(nt[si::NA_NAME_OFFS as int] == parts[p_nmo()]);
    assert(nt[si::NA_NAME_BYTES as int] == parts[p_nmy()]);
    let sgp = st[si::SU_GROUPS as int];
    let ngp = nt[si::NA_GROUPS as int];
    assert forall|r: int| 0 <= r < sc.n_s implies {
        &&& (#[trigger] srel_of(db)[r])[0] == Val::Int(skey(sc, r))
        &&& srel_of(db)[r][1] == Val::Text(sname(sc, r))
        &&& srel_of(db)[r][3] == Val::Int(snat(sc, r))
    } by {
        lemma_bs_group(sc.bs_s as int, sbs, ns, r);
        crate::stores::suppliers::interface::common::read::lemma_for_row(sgp, ns, sbs, st[si::SU_SUPPKEY_BASE as int], st[si::SU_SUPPKEY_CODES as int], r);
        crate::stores::suppliers::interface::common::read::lemma_for_row(sgp, ns, sbs, st[si::SU_NATIONKEY_BASE as int], st[si::SU_NATIONKEY_CODES as int], r);
        assert(sf::int_col(srel, 0, sf::gs_at(st, si::SU_GROUPS as int), st[si::SU_SUPPKEY_BASE as int], st[si::SU_SUPPKEY_CODES as int]));
        assert(sf::int_col(srel, 3, sf::gs_at(st, si::SU_GROUPS as int), st[si::SU_NATIONKEY_BASE as int], st[si::SU_NATIONKEY_CODES as int]));
        assert(sf::text_col(srel, 1, sf::u64s(st[si::SU_NAME_OFFS as int]), sf::u8s(st[si::SU_NAME_BYTES as int])));
    }
    assert forall|n: int| 0 <= n < sc.n_n implies {
        &&& (#[trigger] nrel_of(db)[n])[0] == Val::Int(nkey(sc, n))
        &&& nrel_of(db)[n][1] == Val::Text(nname(sc, n))
    } by {
        lemma_bs_group(sc.bs_n as int, nbs, nn, n);
        crate::stores::suppliers::interface::common::read::lemma_for_row(ngp, nn, nbs, nt[si::NA_NATIONKEY_BASE as int], nt[si::NA_NATIONKEY_CODES as int], n);
        assert(sf::int_col(nrel, 0, sf::gs_at(nt, si::NA_GROUPS as int), nt[si::NA_NATIONKEY_BASE as int], nt[si::NA_NATIONKEY_CODES as int]));
        assert(sf::text_col(nrel, 1, sf::u64s(nt[si::NA_NAME_OFFS as int]), sf::u8s(nt[si::NA_NAME_BYTES as int])));
    }
}


/// The model's run lengths are the maximal runs of l_orderkey (one per stored orders row).
pub proof fn lemma_runs_model(db: Database, lp: Seq<PartView>, c: Cols)
    requires
        lo_bound(db, lp),
        cols_from_parts(c, crate::stores::li_ordruns::interface::facts_parts(lp)),
        c.rl@ == crate::stores::li_ordruns::interface::run_lens(lp),
        c.rl@.len() == c.n_o,
        c.n_o > 0,
    ensures
        super::runs::runs_model(c),
{
    use crate::stores::li_ordruns::interface as LO;
    use super::runs::*;
    let fp = LO::facts_parts(lp);
    lemma_lo_bound(db, lp);
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

} // verus!
